use crate::budget;
use crate::laws::{self, Breach, Kind};
use crate::model::Facts;
use crate::trace::{Answered, Event, Run, Tag, CALLER, CLOCK, DATA, MATH, OUT, SIZE, STORE, VALUE};
use crate::world::{self, Addr, Msg, World, ACTOR, ALLY, OWNER, SUBJECT, USER};
use evmdec::abi;
use evmdec::decompile::Contract;
use evmdec::function::{FnKind, Mutability};
use evmdec::opcode as op;
use evmdec::U256;
use std::collections::HashSet;

pub const UNIT: U256 = U256([1_000_000_000_000_000_000, 0, 0, 0]);
// What an account is taken to hold in a ledger the contract keeps: a thousand units.
const STAKE: U256 = U256([0x35c9_adc5_dea0_0000, 0x36, 0, 0]);

const MAX_ENTRIES: usize = 80;
const MAX_STATES: usize = 96;
const ROUNDS: usize = 5;
const MAX_TRIES: usize = 10;
const MAX_HOOKS: usize = 4;
const ACTOR_DEPTH: usize = 3;
const UNUSED_SELECTOR: u32 = 0xfeed_c0de;
const TEN_YEARS: u64 = 315_360_000;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Word {
    Address,
    Flag,
    Small,
    Amount,
    // Points at where a list or a byte string starts. Never changed.
    Offset,
    // How many items a list holds.
    Count,
    Other,
}

#[derive(Clone, Debug)]
pub struct Entry {
    pub function: usize,
    pub selector: Option<u32>,
    pub name: String,
    template: Vec<u8>,
    words: Vec<Word>,
    // The same call with two elements in each list, and what each of its words holds.
    pair: Option<(Vec<u8>, Vec<Word>)>,
    pub view: bool,
    pub payable: bool,
}

#[derive(Clone, Debug)]
pub enum Step {
    Call {
        entry: usize,
        msg: Msg,
    },
    Wait {
        until: U256,
    },
    Told {
        to: Addr,
        selector: u32,
        answer: Vec<u8>,
    },
    // The contract holds ether and assets that were sent to it.
    Funded,
}

#[derive(Clone)]
pub struct State {
    pub world: World,
    pub steps: Vec<Step>,
    pub acted: usize,
    // What the account with no role has given up of its own recorded claims so far.
    pub spent: U256,
}

#[derive(Clone, Debug)]
pub struct Violation {
    pub breach: Breach,
    pub entry: usize,
    pub steps: Vec<Step>,
    pub run: Run,
    pub via_hook: bool,
    // The last call was a user's own, made after the account had acted.
    pub by_user: bool,
}

type Told = (Addr, u32, Vec<u8>);
type TryKey = (Vec<u8>, U256, Option<U256>, Vec<Told>);

// One call to make, with what the world is taken to be when it is made.
#[derive(Clone, Debug)]
struct Try {
    msg: Msg,
    answers: Vec<(Addr, u32, Vec<u8>)>,
    time: Option<U256>,
}

impl Try {
    fn of(msg: Msg) -> Try {
        Try {
            msg,
            answers: Vec::new(),
            time: None,
        }
    }
}

pub struct Explorer<'a> {
    pub c: &'a Contract,
    pub subject: Addr,
    pub entries: Vec<Entry>,
    pub states: Vec<State>,
    pub facts: Facts,
    pub found: Vec<Violation>,
    pub assumed: Vec<String>,
    pub runs: u64,
    trace: bool,
    edges: HashSet<u32>,
    outside: Vec<Addr>,
    known: Vec<Addr>,
    staked: HashSet<crate::trace::Place>,
    unspendable: HashSet<(crate::trace::Place, usize)>,
    // For each entry, how far its furthest failed call got and what stopped it.
    pub stopped: Vec<Option<(usize, String)>>,
    // For each entry, a call of the owner's that ended in the starting world.
    good: Vec<Option<Try>>,
}

fn outside(n: usize) -> Addr {
    world::account(0xa5, n as u64 + 1)
}

fn kind_of(ty: &str) -> Word {
    let bits = |t: &str| {
        t.trim_start_matches("uint")
            .trim_start_matches("int")
            .parse::<u32>()
    };
    match ty {
        t if t.contains(['[', '(']) || t == "bytes" || t == "string" => Word::Other,
        t if t.starts_with("address") => Word::Address,
        "bool" => Word::Flag,
        t if t.starts_with("uint") || t.starts_with("int") => match bits(t) {
            Ok(n) if n < 64 => Word::Small,
            _ => Word::Amount,
        },
        _ => Word::Amount,
    }
}

fn entries(c: &Contract) -> Vec<Entry> {
    let reached =
        |kind: FnKind| matches!(kind, FnKind::External | FnKind::Fallback | FnKind::Receive);
    let all = c.functions.iter().enumerate();
    let mut out = Vec::new();
    for (function, f) in all.filter(|(_, f)| reached(f.kind)).take(MAX_ENTRIES) {
        let hex = f.selector.as_deref().map(|s| s.trim_start_matches("0x"));
        let selector = hex.and_then(|s| u32::from_str_radix(s, 16).ok());
        let types: Vec<String> = f.params.iter().map(|p| p.ty.clone()).collect();
        let shaped = |elements: usize| {
            let layout = abi::layout_with(selector, &types, elements);
            let template = match f.kind {
                FnKind::Receive => Vec::new(),
                FnKind::Fallback => UNUSED_SELECTOR.to_be_bytes().to_vec(),
                _ => layout.calldata,
            };
            let count = template.len().saturating_sub(4) / 32;
            let mut words = vec![Word::Other; count];
            // Heads sit one word apart only until the first parameter that takes several.
            let plain = |ty: &str| !ty.contains('(') && !(ty.contains('[') && !ty.ends_with("[]"));
            for fixed in layout.fixed.iter().filter(|i| **i < count) {
                words[*fixed] = Word::Offset;
            }
            for (i, ty) in types
                .iter()
                .take_while(|t| plain(t))
                .enumerate()
                .take(count)
            {
                if !layout.fixed.contains(&i) {
                    words[i] = kind_of(ty);
                    continue;
                }
                words[i] = Word::Offset;
                // A list of one-word items sits where its head points: a length, then the items.
                let item = ty
                    .strip_suffix("[]")
                    .filter(|item| kind_of(item) != Word::Other);
                let at = U256::from_be_bytes(&template[4 + 32 * i..36 + 32 * i]).as_usize();
                if let (Some(item), Some(at)) = (item, at.map(|at| at / 32)) {
                    if let Some(word) = words.get_mut(at) {
                        *word = Word::Count;
                    }
                    for k in 1..=elements {
                        if let Some(word) = words.get_mut(at + k) {
                            *word = kind_of(item);
                        }
                    }
                }
            }
            (template, words)
        };
        let (template, words) = shaped(1);
        let lists = types.iter().any(|t| t.ends_with("[]"));
        out.push(Entry {
            function,
            selector,
            name: f.name.clone(),
            template,
            words,
            pair: lists.then(|| shaped(2)),
            view: matches!(f.mutability, Mutability::Pure | Mutability::View),
            payable: f.mutability == Mutability::Payable,
        });
    }
    out
}

// What a failed call was refused for, as far as the run shows it.
fn obstacle(run: &Run) -> String {
    let said = run
        .output
        .get(68..)
        .filter(|_| run.output.starts_with(&[0x08, 0xc3, 0x79, 0xa0]));
    if let Some(text) = said {
        let text: String = text
            .iter()
            .filter(|b| b.is_ascii_graphic() || **b == b' ')
            .map(|b| *b as char)
            .collect();
        return format!("refused: {}", text.trim());
    }
    if run.output.starts_with(&[0x4e, 0x48, 0x7b, 0x71]) {
        let code = run.output.get(35).copied().unwrap_or(0);
        return format!("a built-in check failed (code {code:#04x})");
    }
    if run.halt == crate::trace::Halt::Steps {
        return "ran past the step limit".to_string();
    }
    let failed_call = run.calls.iter().rev().find(|c| !c.ok);
    let last = run.events.iter().rev().find_map(|e| match e {
        Event::Branch { tag, .. } => Some(*tag),
        _ => None,
    });
    let mut on: Vec<&str> = Vec::new();
    if let Some(tag) = last {
        for (bit, name) in [
            (CALLER, "the caller"),
            (DATA, "the call data"),
            (VALUE, "the ether sent"),
            (STORE, "storage"),
            (OUT, "an outside answer"),
            (CLOCK, "the time"),
            (SIZE, "a length"),
        ] {
            if tag.has(bit) {
                on.push(name);
            }
        }
    }
    match (failed_call, on.is_empty()) {
        (Some(call), _)
            if run
                .events
                .iter()
                .rev()
                .take(6)
                .any(|e| matches!(e, Event::Returned(_))) =>
        {
            format!("a call out to {} failed", call.to.to_hex())
        }
        (_, false) => format!("a test on {} failed", on.join(" and ")),
        _ => format!("stopped with no test in sight ({:?})", run.halt),
    }
}

fn set_word(data: &mut Vec<u8>, index: usize, value: U256) {
    let at = 4 + 32 * index;
    if data.len() < at + 32 {
        data.resize(at + 32, 0);
    }
    data[at..at + 32].copy_from_slice(&value.to_be_bytes());
}

fn better(new: &Run, old: &Run) -> bool {
    match (new.ok, old.ok) {
        (true, false) => true,
        (false, true) => false,
        _ => (new.edges.len(), new.steps) > (old.edges.len(), old.steps),
    }
}

fn low_address(value: U256) -> Addr {
    value & ((U256::ONE << 160) - U256::ONE)
}

impl<'a> Explorer<'a> {
    #[must_use]
    pub fn new(c: &'a Contract) -> Explorer<'a> {
        let named = c.address.as_deref().and_then(U256::from_hex_str);
        let subject = named.unwrap_or(SUBJECT);
        let mut world = World::new();
        world.subject = subject;
        world.place(subject, &c.info.runtime);
        // The code behind a proxy runs in the proxy's storage, from the slot that names it.
        let behind = c.parts.iter().skip(1).filter_map(|part| {
            let at = U256::from_hex_str(&part.address)?;
            world.place(at, &part.runtime);
            Some(at)
        });
        let behind: Vec<Addr> = behind.collect();
        if let [implementation] = behind[..] {
            for slot in c
                .delegatecall_slots
                .iter()
                .filter_map(|s| U256::from_hex_str(s))
            {
                world.seed(subject, slot, implementation);
            }
        }
        for (slot, held) in &c.stored_targets {
            if let (Some(slot), Some(held)) = (U256::from_hex_str(slot), U256::from_hex_str(held)) {
                world.seed(subject, slot, held);
            }
        }
        let entries = entries(c);
        let start = State {
            world,
            steps: Vec::new(),
            acted: 0,
            spent: U256::ZERO,
        };
        Explorer {
            c,
            subject,
            facts: Facts::new(entries.len()),
            entries,
            states: vec![start],
            found: Vec::new(),
            assumed: Vec::new(),
            runs: 0,
            trace: std::env::var("EVMDEC_AUDIT_TRACE").is_ok(),
            edges: HashSet::new(),
            outside: Vec::new(),
            known: vec![OWNER, USER, ACTOR, ALLY, subject],
            staked: HashSet::new(),
            unspendable: HashSet::new(),
            stopped: Vec::new(),
            good: Vec::new(),
        }
    }

    fn seed(&self, entry: usize, who: Addr, address: Addr, amount: U256, value: U256) -> Msg {
        let e = &self.entries[entry];
        self.fill(entry, &e.template, &e.words, who, address, amount, value)
    }

    #[allow(clippy::too_many_arguments)]
    fn fill(
        &self,
        entry: usize,
        template: &[u8],
        words: &[Word],
        who: Addr,
        address: Addr,
        amount: U256,
        value: U256,
    ) -> Msg {
        let mut data = template.to_vec();
        let targets = &self.facts.entries[entry].target_words;
        for (i, word) in words.iter().enumerate() {
            let fill = match word {
                Word::Address if targets.contains(&i) => outside(0),
                Word::Address => address,
                Word::Flag => U256::ONE,
                Word::Small => U256::ZERO,
                Word::Amount => amount,
                Word::Offset | Word::Count | Word::Other => continue,
            };
            set_word(&mut data, i, fill);
        }
        Msg {
            from: who,
            to: self.subject,
            data,
            value,
            hook: None,
        }
    }

    fn honest(&self, entry: usize, who: Addr) -> Vec<Msg> {
        let plain = self.seed(entry, who, who, UNIT, U256::ZERO);
        // A function that takes ether is first used the way it is meant to be, with some.
        let mut seeds = match self.entries[entry].payable {
            true => vec![self.seed(entry, who, who, UNIT, UNIT), plain],
            false => vec![plain],
        };
        // What an owner registers under an address is as often a contract as itself.
        if who == OWNER && self.entries[entry].words.contains(&Word::Address) {
            seeds.push(self.seed(entry, who, outside(0), UNIT, U256::ZERO));
        }
        seeds
    }

    // What an account with no role tries: itself everywhere, then another account in each place.
    fn hostile(&self, entry: usize) -> Vec<Msg> {
        let e = &self.entries[entry];
        let mut seeds = vec![self.seed(entry, ACTOR, ACTOR, UNIT, U256::ZERO)];
        if e.payable {
            seeds.insert(0, self.seed(entry, ACTOR, ACTOR, UNIT, UNIT));
        }
        let addresses: Vec<usize> = (0..e.words.len())
            .filter(|i| e.words[*i] == Word::Address)
            .collect();
        for at in addresses.iter().take(3) {
            for other in [USER, OWNER] {
                let mut msg = self.seed(entry, ACTOR, ACTOR, UNIT, U256::ZERO);
                set_word(&mut msg.data, *at, other);
                seeds.push(msg);
            }
        }
        if !addresses.is_empty() {
            seeds.push(self.seed(entry, ACTOR, ALLY, UNIT, U256::ZERO));
        }
        if e.words.contains(&Word::Amount) {
            seeds.push(self.seed(entry, ACTOR, ACTOR, U256::MAX, U256::ZERO));
            seeds.push(self.seed(entry, ACTOR, ACTOR, U256::ZERO, U256::ZERO));
        }
        // Two items of half the range each add up to nothing where a sum is not checked.
        if let Some((template, words)) = &e.pair {
            let half = U256::ONE << 255;
            seeds.push(self.fill(entry, template, words, ACTOR, ACTOR, half, U256::ZERO));
            seeds.push(self.fill(entry, template, words, ACTOR, ACTOR, UNIT, U256::ZERO));
        }
        seeds
    }

    fn attempt_in(&mut self, mut world: World, entry: usize, t: &Try) -> (World, Run) {
        for (to, selector, answer) in &t.answers {
            world.answer_with(*to, *selector, answer.clone());
        }
        if let Some(time) = t.time.filter(|time| *time > world.time) {
            let blocks = (time - world.time).low_u64() / 12;
            world.number = world.number + U256::from_u64(blocks);
            world.time = time;
        }
        let honest = t.msg.from == OWNER || t.msg.from == USER;
        let held_before: Vec<(Option<Addr>, U256)> = match honest {
            true => {
                let mut kinds = vec![(None, world.ether_of(self.subject))];
                let assets = world.assets().into_iter();
                kinds.extend(assets.map(|a| (Some(a), world.asset_of(a, self.subject))));
                kinds
            }
            false => Vec::new(),
        };
        let run = world.send(&t.msg);
        self.runs += 1;
        if run.ok && honest {
            let mut kinds: Vec<Option<Addr>> = vec![None];
            kinds.extend(world.assets().into_iter().map(Some));
            for kind in kinds {
                let was = held_before
                    .iter()
                    .find(|(k, _)| *k == kind)
                    .map_or(U256::ZERO, |(_, v)| *v);
                let now = match kind {
                    Some(asset) => world.asset_of(asset, self.subject),
                    None => world.ether_of(self.subject),
                };
                if now > was {
                    self.facts.keeps.insert(kind);
                }
            }
        }
        if self.trace {
            let from = t.msg.from.to_hex();
            let data = evmdec::hex::encode(&t.msg.data[..t.msg.data.len().min(100)]);
            let name = &self.entries[entry].name;
            eprintln!(
                "run {from:.6} {name} {data} value={} ok={} halt={:?} steps={} edges={} calls={}",
                t.msg.value.to_hex(),
                run.ok,
                run.halt,
                run.steps,
                run.edges.len(),
                run.calls.len()
            );
            if std::env::var("EVMDEC_AUDIT_TRACE").is_ok_and(|v| v == "2") {
                for event in run
                    .events
                    .iter()
                    .filter(|e| !matches!(e, Event::Load { .. }))
                {
                    eprintln!("    {event:?}");
                }
            }
        }
        self.facts
            .observe(entry, &t.msg, &run, self.subject, &self.known);
        if self.stopped.len() < self.entries.len() {
            self.stopped.resize(self.entries.len(), None);
        }
        let further = self.stopped[entry]
            .as_ref()
            .is_none_or(|(edges, _)| run.edges.len() > *edges);
        if !run.ok && further && t.msg.from == OWNER {
            self.stopped[entry] = Some((run.edges.len(), obstacle(&run)));
        }
        (world, run)
    }

    fn attempt(&mut self, state: usize, entry: usize, t: &Try) -> (World, Run) {
        let world = self.states[state].world.clone();
        self.attempt_in(world, entry, t)
    }

    /* What to change so that the comparison a failed run stopped at comes out the
    other way: a word of the call data, the value sent, the length of the call data
    or of an outside answer, or the time. */
    #[allow(clippy::too_many_lines)]
    fn mutations(&self, t: &Try, run: &Run, entry: usize, now: U256) -> Vec<Try> {
        let e = &self.entries[entry];
        let free = |w: usize| e.words.get(w).is_none_or(|k| *k != Word::Offset);
        let count = |w: usize| e.words.get(w) == Some(&Word::Count);
        let mut out: Vec<Try> = Vec::new();
        let mut seen: HashSet<TryKey> = HashSet::new();
        let mut push = |out: &mut Vec<Try>, next: Try| {
            let key = (
                next.msg.data.clone(),
                next.msg.value,
                next.time,
                next.answers.clone(),
            );
            let differs = next.msg.data != t.msg.data
                || next.msg.value != t.msg.value
                || next.time != t.time
                || next.answers != t.answers;
            if differs && out.len() < MAX_TRIES && seen.insert(key) {
                out.push(next);
            }
        };
        for call in &run.calls {
            /* The contract passes on a call for its caller: the address called and the
            bytes sent both come from the call data. What such a call can do is what the
            contract itself may do, so it is tried with the two messages that move an asset. */
            let passed_on =
                call.kind == op::CALL && call.to_tag.has(DATA) && call.input_from.has(DATA);
            let places = (
                call.to_tag.word(),
                call.input_from.word().filter(|w| *w >= 1),
            );
            if let (true, (Some(target), Some(at))) = (passed_on, places) {
                let moves = [
                    world::transfer_from_call(USER, ALLY, UNIT),
                    world::transfer_call(ALLY, UNIT),
                ];
                for payload in moves {
                    let mut next = t.clone();
                    set_word(&mut next.msg.data, target, outside(0));
                    set_word(&mut next.msg.data, at - 1, U256::from(payload.len()));
                    let start = 4 + 32 * at;
                    let end = start + payload.len().div_ceil(32) * 32;
                    if next.msg.data.len() < end {
                        next.msg.data.resize(end, 0);
                    }
                    next.msg.data[start..start + payload.len()].copy_from_slice(&payload);
                    push(&mut out, next);
                }
            }
            // An answer the contract goes on to call has to be the address of a contract.
            let asked = call.to_tag.call().filter(|_| call.to_tag.has(OUT));
            let source = asked.and_then(|k| run.calls.get(k));
            if let Some(source) =
                source.filter(|s| matches!(s.by, Answered::Blank | Answered::Taken))
            {
                if let Some(selector) = world::selector(&source.input) {
                    let mut next = t.clone();
                    next.answers
                        .push((source.to, selector, outside(0).to_be_bytes().to_vec()));
                    push(&mut out, next);
                }
            }
            let unanswered = !call.input.is_empty()
                && call.by == Answered::Blank
                && (call.to.is_zero() || self.known.contains(&call.to));
            if let Some(word) = call
                .to_tag
                .word()
                .filter(|w| unanswered && call.to_tag.has(DATA) && free(*w))
            {
                let mut next = t.clone();
                set_word(&mut next.msg.data, word, outside(0));
                push(&mut out, next);
            }
        }
        let cmps = run.events.iter().rev().filter_map(|ev| match ev {
            Event::Cmp {
                op: o,
                a,
                b,
                ta,
                tb,
                ..
            } => Some((*o, *a, *b, *ta, *tb)),
            _ => None,
        });
        for (o, a, b, ta, tb) in cmps.take(12) {
            for (tag, other) in [(ta, b), (tb, a)] {
                let near = [
                    other,
                    other.wrapping_add(U256::ONE),
                    other.wrapping_sub(U256::ONE),
                ];
                let values: &[U256] = match o {
                    op::EQ => &near[..1],
                    _ => &near,
                };
                if let Some(word) = tag.word().filter(|w| tag.has(DATA) && free(*w)) {
                    for value in values {
                        let mut next = t.clone();
                        set_word(&mut next.msg.data, word, *value);
                        // A longer list needs its items: each new one is a copy of the first.
                        let items = value
                            .as_usize()
                            .filter(|n| count(word) && (1..=8).contains(n));
                        for k in 1..items.unwrap_or(0) {
                            let first =
                                U256::from_be_bytes(&next.msg.data[4 + 32 * (word + 1)..][..32]);
                            if next.msg.data.len() < 4 + 32 * (word + 2 + k) {
                                set_word(&mut next.msg.data, word + 1 + k, first);
                            }
                        }
                        push(&mut out, next);
                    }
                }
                // An outside answer the code compares with something is tried as that thing.
                let asked = tag.call().filter(|_| tag.has(OUT) && !tag.has(DATA));
                let source = asked.and_then(|k| run.calls.get(k));
                if let Some(source) =
                    source.filter(|s| matches!(s.by, Answered::Blank | Answered::Taken))
                {
                    if let Some(selector) = world::selector(&source.input) {
                        for value in values {
                            let mut answer = source.output.clone();
                            answer.resize(answer.len().max(32), 0);
                            answer[..32].copy_from_slice(&value.to_be_bytes());
                            let mut next = t.clone();
                            next.answers
                                .retain(|(to, s, _)| !(*to == source.to && *s == selector));
                            next.answers.push((source.to, selector, answer));
                            push(&mut out, next);
                        }
                    }
                }
                if tag.only(VALUE) || tag.only(VALUE | MATH) {
                    for value in values {
                        let mut next = t.clone();
                        next.msg.value = *value;
                        push(&mut out, next);
                    }
                }
                let length = other.as_usize().filter(|n| *n <= 2_048);
                if let (true, Some(len)) = (tag.has(SIZE), length) {
                    match tag.call().and_then(|k| run.calls.get(k)) {
                        None => {
                            for len in [len, len + 4] {
                                let mut next = t.clone();
                                if next.msg.data.len() < len {
                                    next.msg.data.resize(len, 0);
                                    push(&mut out, next);
                                }
                            }
                        }
                        Some(call) if call.by == Answered::Blank || call.by == Answered::Taken => {
                            if let Some(selector) = world::selector(&call.input) {
                                let mut answer = Vec::new();
                                while answer.len() < len.max(32) {
                                    answer.extend_from_slice(&U256::ONE.to_be_bytes());
                                }
                                let mut next = t.clone();
                                next.answers.push((call.to, selector, answer));
                                push(&mut out, next);
                            }
                        }
                        Some(_) => {}
                    }
                }
                let ahead = other > now
                    && (other - now).bits() <= 64
                    && (other - now).low_u64() < TEN_YEARS;
                if tag.has(CLOCK) && !tag.has(DATA) && ahead {
                    let mut next = t.clone();
                    next.time = Some(other.wrapping_add(U256::ONE));
                    push(&mut out, next);
                }
            }
        }
        out
    }

    // The input, and the world it leaves, under which a call to the entry ends.
    fn solve(&mut self, state: usize, entry: usize, seed: Try) -> (Try, World, Run) {
        let (world, run) = self.attempt(state, entry, &seed);
        let mut best = (seed, world, run);
        for _ in 0..ROUNDS {
            if best.2.ok || budget::spent() {
                break;
            }
            let now = self.states[state].world.time;
            let tries = self.mutations(&best.0, &best.2, entry, now);
            let mut improved = false;
            for t in tries {
                if budget::spent() {
                    break;
                }
                let (world, run) = self.attempt(state, entry, &t);
                if better(&run, &best.2) {
                    let ended = run.ok;
                    best = (t, world, run);
                    improved = true;
                    if ended {
                        break;
                    }
                }
            }
            if !improved {
                break;
            }
        }
        best
    }

    fn novel(&mut self, run: &Run) -> bool {
        let before = self.edges.len();
        self.edges.extend(run.edges.iter().copied());
        self.edges.len() > before
    }

    fn keep(&mut self, from: usize, entry: usize, t: &Try, world: World, actor: bool) -> usize {
        let parent = &self.states[from];
        let mut steps = parent.steps.clone();
        if let Some(until) = t.time.filter(|time| *time > parent.world.time) {
            steps.push(Step::Wait { until });
        }
        for (to, selector, answer) in &t.answers {
            steps.push(Step::Told {
                to: *to,
                selector: *selector,
                answer: answer.clone(),
            });
        }
        steps.push(Step::Call {
            entry,
            msg: t.msg.clone(),
        });
        let spent = parent.spent;
        self.states.push(State {
            world,
            steps,
            acted: parent.acted + usize::from(actor),
            spent,
        });
        self.states.len() - 1
    }

    /* A contract in use has an owner, knows the contracts it calls, and has its
    switches set. Runtime code does not say any of that, so each is taken to hold when
    the owner's own call is refused for the lack of it and goes further with it. */
    fn settle(&mut self) {
        for _ in 0..4 {
            let mut changed = false;
            self.good = vec![None; self.entries.len()];
            let mut refused: Vec<(usize, Try, Run)> = Vec::new();
            // What works as things are is found first, so that no setting is taken that shuts it.
            for entry in 0..self.entries.len() {
                for who in [OWNER, USER, ACTOR] {
                    let plain = Try::of(self.seed(entry, who, who, UNIT, U256::ZERO));
                    let (_, run) = self.attempt(0, entry, &plain);
                    changed |= self.assume_stake(&plain, &run, entry, who);
                }
                for seed in self.honest(entry, OWNER) {
                    if budget::spent() {
                        return;
                    }
                    let (best, _, run) = self.solve(0, entry, Try::of(seed));
                    changed |= self.assume_targets(&run);
                    changed |= self.assume_owner(&best, &run, entry);
                    if run.ok {
                        self.good[entry] = Some(best);
                        break;
                    }
                    refused.push((entry, best, run));
                }
            }
            for (entry, t, run) in refused {
                if self.good[entry].is_none() {
                    changed |= self.assume_from(&t, &run, entry);
                }
            }
            changed |= self.set_up();
            if !changed {
                break;
            }
        }
    }

    /* A call the owner can make once and not again, and that fills cells it found
    empty, is the contract's set-up. A contract in use has been through it, so the
    world every other call starts from has too. */
    fn set_up(&mut self) -> bool {
        for entry in 0..self.entries.len() {
            if self.entries[entry].view {
                continue;
            }
            let own = [
                self.seed(entry, OWNER, OWNER, UNIT, U256::ZERO),
                self.seed(entry, OWNER, OWNER, UNIT, UNIT),
            ];
            let seeds = if self.entries[entry].payable { 2 } else { 1 };
            for seed in own.into_iter().take(seeds) {
                if budget::spent() {
                    return false;
                }
                let (t, world, run) = self.solve(0, entry, Try::of(seed));
                let subject = self.subject;
                let fills = run.stores().any(|(c, old, new, _, _)| {
                    c.account == subject && old.is_zero() && !new.is_zero()
                });
                if !run.ok || !fills {
                    continue;
                }
                let (_, again) = self.attempt_in(world.clone(), entry, &t);
                if again.ok {
                    continue;
                }
                self.novel(&run);
                self.states[0].world = world;
                self.states[0].steps.push(Step::Call { entry, msg: t.msg });
                return true;
            }
        }
        false
    }

    /* A ledger in use has holders. Where a call is refused because the caller's own
    entry does not cover the amount asked for, the caller is taken to hold a stake
    there. All three accounts get one, so none starts ahead of the others. */
    fn assume_stake(&mut self, t: &Try, run: &Run, entry: usize, who: Addr) -> bool {
        let subject = self.subject;
        let mut slots: Vec<(U256, crate::trace::Place)> = Vec::new();
        for event in &run.events {
            let Event::Cmp {
                op: o,
                a,
                b,
                ta,
                tb,
                ..
            } = event
            else {
                continue;
            };
            if !matches!(*o, op::LT | op::GT | op::SLT | op::SGT) {
                continue;
            }
            for (tag, value, other) in [(ta, a, tb), (tb, b, ta)] {
                let own = tag.has(STORE) && !tag.has(DATA | VALUE);
                let cell = run.cell_of(*tag).filter(|c| c.account == subject);
                let (true, true, Some(cell)) =
                    (own && value.is_zero(), other.has(DATA | VALUE), cell)
                else {
                    continue;
                };
                let by_caller = cell
                    .keys
                    .iter()
                    .any(|k| k.tag.only(CALLER) && k.value == who);
                if by_caller && self.states[0].world.stored(subject, cell.slot).is_zero() {
                    slots.push((cell.slot, cell.place()));
                }
            }
        }
        let mut changed = false;
        for (slot, place) in slots {
            let mut world = self.states[0].world.clone();
            world.seed(subject, slot, STAKE);
            let (_, next) = self.attempt_in(world, entry, t);
            if !better(&next, run) {
                continue;
            }
            self.states[0].world.seed(subject, slot, STAKE);
            if self.staked.insert(place) {
                self.assumed.push(format!(
                    "each account holds a thousand units in the ledger at slot {}, since a call is refused when the caller's entry there does not cover the amount",
                    place.root.to_hex()
                ));
            }
            changed = true;
        }
        changed
    }

    fn assume_targets(&mut self, run: &Run) -> bool {
        let mut changed = false;
        for call in &run.calls {
            let from_store = call.to_tag.has(STORE) && !call.to_tag.has(DATA | MATH);
            let cell = run
                .cell_of(call.to_tag)
                .filter(|c| c.account == self.subject);
            // A person does not answer a call. A cell the set-up filled with the owner's address
            // and that the code then calls is the address of a contract.
            let nobody = call.to.is_zero() || (call.to == OWNER && !call.input.is_empty());
            let (true, true, Some(cell)) = (nobody, from_store, cell) else {
                continue;
            };
            let held = self.states[0].world.stored(self.subject, cell.slot);
            if low_address(held) != call.to {
                continue;
            }
            let fresh = outside(self.outside.len() + 1);
            self.outside.push(fresh);
            self.known.push(fresh);
            let rest = held & !((U256::ONE << 160) - U256::ONE);
            self.states[0]
                .world
                .seed(self.subject, cell.slot, rest | fresh);
            self.assumed.push(format!(
                "slot {} holds the address of another contract, since the code calls what it reads there",
                cell.slot.to_hex()
            ));
            if let Some(place) = self.facts.places.get_mut(&cell.place()) {
                place.assumed = true;
            }
            changed = true;
        }
        changed
    }

    /* Old code does not refuse a caller it does not know. It skips the body and ends.
    So a cell the caller is compared with is taken to name the owner whether or not the
    call failed for the lack of it. */
    fn assume_owner(&mut self, t: &Try, run: &Run, entry: usize) -> bool {
        let subject = self.subject;
        let mut empty: Vec<(usize, U256)> = Vec::new();
        for event in &run.events {
            let Event::Cmp {
                pc,
                op: op::EQ,
                a,
                b,
                ta,
                tb,
            } = event
            else {
                continue;
            };
            for (caller, value, other, named) in [(ta, a, tb, b), (tb, b, ta, a)] {
                let stored = other.has(STORE) && !other.has(DATA);
                let cell = run.cell_of(*other).filter(|c| c.account == subject);
                let by_owner = caller.only(CALLER) && *value == OWNER;
                if let (true, true, true, Some(cell)) = (by_owner, stored, named.is_zero(), cell) {
                    empty.push((*pc, cell.slot));
                }
            }
        }
        let mut changed = false;
        for (at, slot) in empty {
            let held = self.states[0].world.stored(subject, slot);
            // The address may sit above other fields packed into the same slot.
            for shift in 0..12u32 {
                let mut world = self.states[0].world.clone();
                let named = held | (OWNER << (8 * shift));
                world.seed(subject, slot, named);
                let (_, again) = self.attempt_in(world, entry, t);
                let matched = again.events.iter().any(|e| {
                    matches!(e, Event::Cmp { pc, op: op::EQ, a, b, .. } if *pc == at && a == b && *a == OWNER)
                });
                if !matched {
                    continue;
                }
                self.states[0].world.seed(subject, slot, named);
                self.assumed.push(format!(
                    "slot {} names the owner, since the code compares the caller with it",
                    slot.to_hex()
                ));
                changed = true;
                break;
            }
        }
        changed
    }

    /* The tests a failed call of the owner's last made on storage. A role the owner
    lacks is given to it. A plain slot that reads as nothing is tried with what the
    code compared it with, then with a total that matches the three stakes, then with a
    plain amount. An entry under a key is left for the calls that fill it. */
    fn assume_from(&mut self, t: &Try, run: &Run, entry: usize) -> bool {
        let subject = self.subject;
        let base = &self.states[0].world;
        let mut options: Vec<(U256, U256, String)> = Vec::new();
        let tests = run.events.iter().rev().filter_map(|e| match e {
            Event::Branch { tag, .. } if tag.has(STORE) && !tag.has(DATA | VALUE) => Some(*tag),
            _ => None,
        });
        for tag in tests.take(3) {
            let unset = run.events.iter().filter_map(|e| match e {
                Event::Load { cell, value } if value.is_zero() => Some(*cell),
                _ => None,
            });
            let cells: Vec<usize> = match tag.cell() {
                Some(cell) => vec![cell],
                None => unset
                    .filter(|c| run.cells[*c].keys.is_empty())
                    .take(4)
                    .collect(),
            };
            for index in cells {
                let cell = &run.cells[index];
                if cell.account != subject {
                    continue;
                }
                let held = base.stored(subject, cell.slot);
                let by_caller = cell
                    .keys
                    .iter()
                    .any(|k| k.tag.only(CALLER) && k.value == OWNER);
                if by_caller && held.is_zero() && !tag.has(MATH) {
                    let why = format!(
                        "the owner holds the role kept at slot {}, since the code tests the caller's entry there",
                        cell.root.to_hex()
                    );
                    options.push((cell.slot, U256::ONE, why));
                }
                if !cell.keys.is_empty() || tag.has(CALLER) {
                    continue;
                }
                let this = u16::try_from(index + 1).unwrap_or(u16::MAX);
                let compared = run.events.iter().filter_map(|ev| match ev {
                    Event::Cmp { b, ta, tb, .. } if ta.cell == this && !tb.has(STORE) => Some(*b),
                    Event::Cmp { a, ta, tb, .. } if tb.cell == this && !ta.has(STORE) => Some(*a),
                    _ => None,
                });
                let mut values: Vec<U256> = compared
                    .flat_map(|v| [v, v.wrapping_add(U256::ONE), v.wrapping_sub(U256::ONE)])
                    .take(3)
                    .collect();
                if held.is_zero() {
                    values.extend([STAKE + STAKE + STAKE, UNIT, U256::ONE]);
                }
                let why = format!(
                    "slot {} is set, since the owner's call needs it",
                    cell.slot.to_hex()
                );
                options.extend(values.into_iter().map(|v| (cell.slot, v, why.clone())));
            }
        }
        for (slot, value, why) in options.into_iter().take(12) {
            if budget::spent() {
                return false;
            }
            let mut world = self.states[0].world.clone();
            if world.stored(subject, slot) == value {
                continue;
            }
            world.seed(subject, slot, value);
            let (_, next) = self.attempt_in(world.clone(), entry, t);
            if better(&next, run) && !self.breaks_others(&world, entry) {
                self.states[0].world.seed(subject, slot, value);
                self.assumed.push(why);
                return true;
            }
        }
        false
    }

    // A setting one call needs must not shut the calls that worked without it.
    fn breaks_others(&mut self, world: &World, but: usize) -> bool {
        let worked: Vec<(usize, Try)> = self
            .good
            .iter()
            .enumerate()
            .filter(|(entry, _)| *entry != but)
            .filter_map(|(entry, t)| Some((entry, t.clone()?)))
            .collect();
        for (entry, t) in worked {
            let (_, run) = self.attempt_in(world.clone(), entry, &t);
            if !run.ok {
                return true;
            }
        }
        false
    }

    fn used_by(&mut self, who: Addr, depth: usize) {
        let mut frontier: Vec<usize> = (0..self.states.len()).collect();
        for _ in 0..depth {
            let mut next = Vec::new();
            for from in frontier {
                for entry in 0..self.entries.len() {
                    if self.entries[entry].view {
                        continue;
                    }
                    let mut kept = false;
                    for seed in self.honest(entry, who) {
                        if budget::spent() || self.states.len() >= MAX_STATES / 2 {
                            return;
                        }
                        let (t, world, run) = self.solve(from, entry, Try::of(seed));
                        // The owner's second way of filling in an address leads somewhere else
                        // even where it runs the same code.
                        let other_way = who == OWNER && kept && run.stores().next().is_some();
                        if run.ok && (self.novel(&run) || other_way) {
                            next.push(self.keep(from, entry, &t, world, false));
                            if who != OWNER {
                                break;
                            }
                            kept = true;
                        }
                    }
                }
            }
            frontier = next;
        }
    }

    fn report(
        &mut self,
        breaches: Vec<Breach>,
        entry: usize,
        steps: &[Step],
        run: &Run,
        how: (bool, bool),
    ) {
        let (via_hook, by_user) = how;
        for breach in breaches {
            let about_value = matches!(
                breach.kind,
                Kind::Gain | Kind::Loss | Kind::Credit | Kind::Debit
            );
            if about_value && !self.survives(&breach, steps, run) {
                continue;
            }
            let place = breach.cell.as_ref().map(crate::trace::Cell::place);
            let (kind, asset) = (breach.kind, breach.asset);
            let same = |v: &Violation| {
                v.breach.kind == kind
                    && v.entry == entry
                    && v.breach.asset == asset
                    && v.breach.cell.as_ref().map(crate::trace::Cell::place) == place
            };
            let fresh = Violation {
                breach,
                entry,
                steps: steps.to_vec(),
                run: run.clone(),
                via_hook,
                by_user,
            };
            match self.found.iter_mut().find(|v| same(v)) {
                Some(known) if known.steps.len() <= steps.len() => {}
                Some(known) => *known = fresh,
                None => self.found.push(fresh),
            }
        }
    }

    /* A number the code multiplies or compares with, kept in a slot nobody but the
    owner writes, read as zero only because this world never saw it set. A price or a
    rate of nothing makes everything free. The same calls are made again with such
    slots holding a plain amount, and a finding has to show then too. */
    fn survives(&mut self, breach: &Breach, steps: &[Step], run: &Run) -> bool {
        let subject = self.subject;
        let zero_loads = run.events.iter().filter_map(|e| match e {
            Event::Load { cell, value } if value.is_zero() => Some(*cell),
            _ => None,
        });
        let unset: Vec<(usize, U256)> = zero_loads
            .filter(|i| {
                let cell = &run.cells[*i];
                let place = self.facts.places.get(&cell.place());
                let open = place.is_some_and(|p| !p.open_writers.is_empty());
                cell.account == subject && cell.keys.is_empty() && !open
            })
            .map(|i| (i, run.cells[i].slot))
            .collect();
        let tags = run.events.iter().flat_map(|e| match e {
            Event::Cmp { ta, tb, .. } => vec![*ta, *tb],
            Event::Store { tag, .. } | Event::Branch { tag, .. } => vec![*tag],
            Event::Pay { amount_tag, .. } => vec![*amount_tag],
            _ => Vec::new(),
        });
        let worked: Vec<Tag> = tags.filter(|t| t.has(MATH) && t.has(STORE)).collect();
        let used = |i: usize| worked.iter().any(|t| t.cell().is_none_or(|c| c == i));
        let mut doubtful: Vec<U256> = unset
            .into_iter()
            .filter(|(i, _)| used(*i))
            .map(|(_, slot)| slot)
            .collect();
        doubtful.sort();
        doubtful.dedup();
        if doubtful.is_empty() {
            return true;
        }
        let prefix = self.states[0].steps.len();
        let mut world = self.states[0].world.clone();
        for slot in doubtful {
            world.seed(subject, slot, UNIT);
        }
        let Some((Step::Call { msg, .. }, earlier)) =
            steps.get(prefix..).and_then(|s| s.split_last())
        else {
            return true;
        };
        let mut base = world.clone();
        let mut spent = U256::ZERO;
        for step in earlier {
            match step {
                Step::Wait { until } => world.time = *until,
                Step::Told {
                    to,
                    selector,
                    answer,
                } => world.answer_with(*to, *selector, answer.clone()),
                Step::Funded => {
                    for kind in self.facts.keeps.clone() {
                        world.enrich(subject, kind);
                    }
                    base = world.clone();
                }
                Step::Call { msg, .. } => {
                    self.runs += 1;
                    let made = world.send(msg);
                    if !made.ok {
                        return false;
                    }
                    if Facts::same_party(msg.from, ACTOR) {
                        spent = spent.wrapping_add(laws::claims_lowered(&made, subject));
                    }
                }
            }
        }
        let before = world.clone();
        self.runs += 1;
        let again = world.send(msg);
        let found = laws::check(&base, &before, &world, &again, &self.facts, spent);
        again.ok && found.iter().any(|b| b.kind == breach.kind)
    }

    /* A record that rose is worth something only if more can now be done with it. The
    account tries to pass on, or be paid, all that the record now holds. That has to
    work after the call and not before it. A slot that packs a flag beside an amount
    rises when the flag is set, and no more can be spent for that. */
    fn spendable(
        &mut self,
        before: &World,
        after: &World,
        breach: &Breach,
        made_by: usize,
    ) -> bool {
        let Some(place) = breach.cell.as_ref().map(crate::trace::Cell::place) else {
            return false;
        };
        if self.unspendable.contains(&(place, made_by)) {
            return false;
        }
        let spends = |world: &World, run: &Run, from: &World| {
            let in_place = |c: &crate::trace::Cell| c.place() == place;
            let passed = run.stores().any(|(c, old, new, _, _)| {
                in_place(c) && c.keyed_by(USER) && !c.keyed_by(ACTOR) && new > old
            });
            let lowered = run
                .stores()
                .any(|(c, old, new, _, _)| in_place(c) && c.keyed_by(ACTOR) && new < old);
            let assets = world.assets();
            let paid = world.ether_of(ACTOR) > from.ether_of(ACTOR)
                || assets
                    .iter()
                    .any(|a| world.asset_of(*a, ACTOR) > from.asset_of(*a, ACTOR));
            run.ok && lowered && (passed || paid)
        };
        self.states.push(State {
            world: after.clone(),
            steps: Vec::new(),
            acted: 0,
            spent: U256::ZERO,
        });
        let at = self.states.len() - 1;
        let mut spent = false;
        for entry in 0..self.entries.len() {
            if self.entries[entry].view || budget::spent() {
                continue;
            }
            let seed = self.seed(entry, ACTOR, USER, breach.total, U256::ZERO);
            let (t, world, run) = self.solve(at, entry, Try::of(seed));
            let whole = breach.total.to_be_bytes();
            let asks_all = t.msg.data.len() >= 36 && t.msg.data[4..].chunks(32).any(|w| w == whole);
            if !asks_all || !spends(&world, &run, after) {
                continue;
            }
            let (earlier, could) = self.attempt_in(before.clone(), entry, &t);
            if !spends(&earlier, &could, before) {
                spent = true;
                break;
            }
        }
        self.states.truncate(at);
        if !spent {
            self.unspendable.insert((place, made_by));
        }
        spent
    }

    /* The mirror of the test above. An account whose record fell has lost something only
    if it can now do less: what it could pass on before the call, it no longer can. */
    fn withheld(&mut self, before: &World, after: &World, breach: &Breach) -> bool {
        let (Some(place), Some(victim)) = (
            breach.cell.as_ref().map(crate::trace::Cell::place),
            breach.victim,
        ) else {
            return false;
        };
        let spends = |run: &Run| {
            let lowered = run
                .stores()
                .any(|(c, old, new, _, _)| c.place() == place && c.keyed_by(victim) && new < old);
            run.ok && lowered
        };
        self.states.push(State {
            world: before.clone(),
            steps: Vec::new(),
            acted: 0,
            spent: U256::ZERO,
        });
        let at = self.states.len() - 1;
        let mut lost = false;
        for entry in 0..self.entries.len() {
            if self.entries[entry].view || budget::spent() {
                continue;
            }
            for amount in [breach.total, STAKE] {
                let other = if victim == OWNER { USER } else { OWNER };
                let seed = self.seed(entry, victim, other, amount, U256::ZERO);
                let (t, _, run) = self.solve(at, entry, Try::of(seed));
                let whole = amount.to_be_bytes();
                let asks_all =
                    t.msg.data.len() >= 36 && t.msg.data[4..].chunks(32).any(|w| w == whole);
                if !asks_all || !spends(&run) {
                    continue;
                }
                let (_, now) = self.attempt_in(after.clone(), entry, &t);
                lost |= !spends(&now);
            }
            if lost {
                break;
            }
        }
        self.states.truncate(at);
        lost
    }

    fn history(&self, from: usize, entry: usize, msg: &Msg) -> Vec<Step> {
        let mut steps = self.states[from].steps.clone();
        steps.push(Step::Call {
            entry,
            msg: msg.clone(),
        });
        steps
    }

    /* A cell that names nobody yet says nothing about whether the call that fills it is
    the contract's set-up or a way to take it over. The same call is made again with the
    owner named there, and only a change that survives that is reported. */
    fn takes_from_owner(&mut self, from: usize, entry: usize, t: &Try, run: &Run) {
        let filled: Vec<U256> = run
            .stores()
            .filter(|(cell, old, new, _, _)| {
                let place = self.facts.places.get(&cell.place());
                let identity = place.is_some_and(|p| p.identity);
                // An entry under a key the caller supplies is the caller's own to fill.
                let plain = cell.keys.iter().all(|k| k.tag.is_none());
                let empty = low_address(*old).is_zero() && !new.is_zero();
                cell.account == self.subject && identity && plain && empty
            })
            .map(|(cell, ..)| cell.slot)
            .collect();
        for slot in filled {
            let before = {
                let mut world = self.states[from].world.clone();
                world.seed(self.subject, slot, OWNER);
                world
            };
            let (after, again) = self.attempt_in(before.clone(), entry, t);
            if !again.ok {
                continue;
            }
            let base = self.states[0].world.clone();
            let spent = self.states[from].spent;
            let breaches = laws::check(&base, &before, &after, &again, &self.facts, spent);
            let takeovers: Vec<Breach> = breaches
                .into_iter()
                .filter(|b| matches!(b.kind, Kind::Takeover | Kind::RoleCleared))
                .collect();
            let steps = self.history(from, entry, &t.msg);
            self.report(takeovers, entry, &steps, &again, (false, false));
        }
    }

    fn reenter(&mut self, from: usize, entry: usize, t: &Try, plain: &[Breach]) {
        let mut hooks: Vec<(usize, Msg)> = vec![(entry, t.msg.clone())];
        let paying: Vec<usize> = (0..self.entries.len())
            .filter(|e| *e != entry && self.facts.entries[*e].pays_out)
            .collect();
        for other in paying.into_iter().take(MAX_HOOKS - 1) {
            hooks.push((other, self.seed(other, ACTOR, ACTOR, UNIT, U256::ZERO)));
        }
        for (_, hook) in hooks {
            if budget::spent() {
                return;
            }
            let mut again = t.clone();
            again.msg.hook = Some(Box::new(Msg { hook: None, ..hook }));
            let before = self.states[from].world.clone();
            let (after, run) = self.attempt(from, entry, &again);
            if !run.ok || !run.hooked {
                continue;
            }
            let base = self.states[0].world.clone();
            let spent = self.states[from].spent;
            let breaches = laws::check(&base, &before, &after, &run, &self.facts, spent);
            let fresh: Vec<Breach> = breaches
                .into_iter()
                .filter(|b| !plain.iter().any(|p| p.kind == b.kind && p.asset == b.asset))
                .collect();
            let steps = self.history(from, entry, &again.msg);
            self.report(fresh, entry, &steps, &run, (true, false));
        }
    }

    /* A contract in use holds ether and assets: what users paid in, and what was sent
    to it. A single call by an account that has paid nothing and holds no claim must not
    take any of it out. Only one call is tried from here. Over several calls an account
    that staked and waited is paid by design. */
    fn sweep(&mut self) {
        let starts = self.states.len().min(MAX_STATES / 8);
        for start in 0..starts {
            // Only what the contract was seen to take in and keep. A contract that passes
            // everything on holds nothing, and what strays into it is anyone's by design.
            if self.facts.keeps.is_empty() {
                return;
            }
            let mut world = self.states[start].world.clone();
            for kind in self.facts.keeps.clone() {
                world.enrich(self.subject, kind);
            }
            let mut steps = self.states[start].steps.clone();
            steps.push(Step::Funded);
            self.states.push(State {
                world,
                steps,
                acted: 0,
                spent: U256::ZERO,
            });
            let at = self.states.len() - 1;
            for entry in 0..self.entries.len() {
                if self.entries[entry].view {
                    continue;
                }
                for seed in self.hostile(entry) {
                    if budget::spent() {
                        break;
                    }
                    let before = self.states[at].world.clone();
                    let (t, world, run) = self.solve(at, entry, Try::of(seed));
                    if !run.ok {
                        continue;
                    }
                    let found =
                        laws::check(&before, &before, &world, &run, &self.facts, U256::ZERO);
                    let gains: Vec<Breach> =
                        found.into_iter().filter(|b| b.kind == Kind::Gain).collect();
                    let steps = self.history(at, entry, &t.msg);
                    self.report(gains, entry, &steps, &run, (false, false));
                }
            }
            self.states.truncate(at);
        }
    }

    /* After the account has acted, a user goes on using the contract as before. A
    user's own call that now pays the account does so because of what the account
    changed, and the finding is placed at the call that changed it. */
    fn used_after(&mut self) {
        let acted: Vec<usize> = (0..self.states.len())
            .filter(|s| self.states[*s].acted > 0)
            .collect();
        for from in acted.into_iter().take(MAX_STATES / 4) {
            let blamed = self.states[from].steps.iter().rev().find_map(|s| match s {
                Step::Call { entry, msg } if msg.from == ACTOR => Some(*entry),
                _ => None,
            });
            let Some(blamed) = blamed else {
                continue;
            };
            for entry in 0..self.entries.len() {
                if self.entries[entry].view {
                    continue;
                }
                for seed in self.honest(entry, USER) {
                    if budget::spent() {
                        return;
                    }
                    let before = self.states[from].world.clone();
                    let (t, world, run) = self.solve(from, entry, Try::of(seed));
                    if !run.ok {
                        continue;
                    }
                    if let Some(breach) = laws::diverted(&before, &world) {
                        let steps = self.history(from, entry, &t.msg);
                        self.report(vec![breach], blamed, &steps, &run, (false, true));
                    }
                    break;
                }
            }
        }
    }

    fn attack(&mut self) {
        let mut frontier: Vec<usize> = (0..self.states.len()).collect();
        for _ in 0..ACTOR_DEPTH {
            let mut next = Vec::new();
            for from in frontier {
                for entry in 0..self.entries.len() {
                    if self.entries[entry].view {
                        continue;
                    }
                    let mut kept = false;
                    for seed in self.hostile(entry) {
                        if budget::spent() {
                            return;
                        }
                        let before = self.states[from].world.clone();
                        let (t, world, run) = self.solve(from, entry, Try::of(seed));
                        let handed = run.calls.iter().any(|c| c.by == Answered::Taken);
                        let mut plain = Vec::new();
                        if run.ok {
                            let base = self.states[0].world.clone();
                            let spent = self.states[from].spent;
                            plain = laws::check(&base, &before, &world, &run, &self.facts, spent);
                            plain.retain(|b| {
                                b.kind != Kind::Credit || self.spendable(&before, &world, b, entry)
                            });
                            plain.retain(|b| {
                                b.kind != Kind::Debit || self.withheld(&before, &world, b)
                            });
                            let steps = self.history(from, entry, &t.msg);
                            self.report(plain.clone(), entry, &steps, &run, (false, false));
                            self.takes_from_owner(from, entry, &t, &run);
                        }
                        if handed {
                            self.reenter(from, entry, &t, &plain);
                        }
                        if run.ok && self.novel(&run) && !kept && self.states.len() < MAX_STATES {
                            let at = self.keep(from, entry, &t, world, true);
                            let lowered = laws::claims_lowered(&run, self.subject);
                            self.states[at].spent = self.states[at].spent.wrapping_add(lowered);
                            next.push(at);
                            kept = true;
                        }
                    }
                }
            }
            frontier = next;
        }
    }

    pub fn explore(&mut self, work: u64) {
        budget::within(work / 5, || self.settle());
        budget::within(work / 10, || self.used_by(OWNER, 1));
        budget::within(work / 5, || self.used_by(USER, 2));
        budget::within(work / 10, || self.sweep());
        budget::within(work / 3, || self.attack());
        budget::within(work / 10, || self.used_after());
    }
}

// The tag of a call data word, for tests and reports that build their own messages.
#[must_use]
pub fn data_word(index: usize) -> Tag {
    Tag::data(4 + 32 * index)
}
