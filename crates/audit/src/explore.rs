use crate::budget;
use crate::laws::{self, Breach, Kind};
use crate::model::Facts;
use crate::trace::{Answered, Event, Run, Tag, CALLER, CLOCK, DATA, MATH, SIZE, STORE, VALUE};
use crate::world::{self, Addr, Msg, World, ACTOR, ALLY, OWNER, SUBJECT, USER};
use evmdec::abi;
use evmdec::decompile::Contract;
use evmdec::function::{FnKind, Mutability};
use evmdec::opcode as op;
use evmdec::U256;
use std::collections::HashSet;

pub const UNIT: U256 = U256([1_000_000_000_000_000_000, 0, 0, 0]);

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
    Call { entry: usize, msg: Msg },
    Wait { until: U256 },
    Told { to: Addr, selector: u32, len: usize },
}

#[derive(Clone)]
pub struct State {
    pub world: World,
    pub steps: Vec<Step>,
    pub acted: usize,
}

#[derive(Clone, Debug)]
pub struct Violation {
    pub breach: Breach,
    pub entry: usize,
    pub steps: Vec<Step>,
    pub run: Run,
    pub via_hook: bool,
}

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
                // A list of one-word items sits where its head points: a length, then the items.
                let item = ty
                    .strip_suffix("[]")
                    .filter(|item| kind_of(item) != Word::Other);
                let at = U256::from_be_bytes(&template[4 + 32 * i..36 + 32 * i]).as_usize();
                if let (Some(item), Some(at)) = (item, at.map(|at| at / 32)) {
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
                Word::Other => continue,
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
        match self.entries[entry].payable {
            true => vec![self.seed(entry, who, who, UNIT, UNIT), plain],
            false => vec![plain],
        }
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
        let run = world.send(&t.msg);
        self.runs += 1;
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
        let free =
            |w: usize| e.words.get(w).is_none_or(|k| *k != Word::Other) || w >= e.words.len();
        let mut out: Vec<Try> = Vec::new();
        let mut seen: HashSet<(Vec<u8>, U256, Option<U256>, usize)> = HashSet::new();
        let mut push = |out: &mut Vec<Try>, next: Try| {
            let key = (
                next.msg.data.clone(),
                next.msg.value,
                next.time,
                next.answers.len(),
            );
            let differs = next.msg.data != t.msg.data
                || next.msg.value != t.msg.value
                || next.time != t.time
                || next.answers.len() != t.answers.len();
            if differs && out.len() < MAX_TRIES && seen.insert(key) {
                out.push(next);
            }
        };
        for call in &run.calls {
            let unanswered =
                call.by == Answered::Blank && (call.to.is_zero() || self.known.contains(&call.to));
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
                        push(&mut out, next);
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
                len: answer.len(),
            });
        }
        steps.push(Step::Call {
            entry,
            msg: t.msg.clone(),
        });
        self.states.push(State {
            world,
            steps,
            acted: parent.acted + usize::from(actor),
        });
        self.states.len() - 1
    }

    /* A contract in use has an owner, knows the contracts it calls, and has its
    switches set. Runtime code does not say any of that, so each is taken to hold when
    the owner's own call is refused for the lack of it and goes further with it. */
    fn settle(&mut self) {
        for _ in 0..4 {
            let mut changed = false;
            for entry in 0..self.entries.len() {
                for seed in self.honest(entry, OWNER) {
                    if budget::spent() {
                        return;
                    }
                    let (best, _, run) = self.solve(0, entry, Try::of(seed));
                    changed |= self.assume_targets(&run);
                    changed |= self.assume_owner(&run);
                    if run.ok {
                        break;
                    }
                    changed |= self.assume_from(&best, &run, entry);
                }
            }
            if !changed {
                break;
            }
        }
    }

    fn assume_targets(&mut self, run: &Run) -> bool {
        let mut changed = false;
        for call in &run.calls {
            let from_store = call.to_tag.has(STORE) && !call.to_tag.has(DATA | MATH);
            let cell = run
                .cell_of(call.to_tag)
                .filter(|c| c.account == self.subject);
            let (true, true, Some(cell)) = (call.to.is_zero(), from_store, cell) else {
                continue;
            };
            let held = self.states[0].world.stored(self.subject, cell.slot);
            if !low_address(held).is_zero() {
                continue;
            }
            let fresh = outside(self.outside.len() + 1);
            self.outside.push(fresh);
            self.known.push(fresh);
            self.states[0]
                .world
                .seed(self.subject, cell.slot, held | fresh);
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
    fn assume_owner(&mut self, run: &Run) -> bool {
        let mut changed = false;
        for event in &run.events {
            let Event::Cmp {
                op: op::EQ,
                a,
                b,
                ta,
                tb,
                ..
            } = event
            else {
                continue;
            };
            for (caller, value, other) in [(ta, a, tb), (tb, b, ta)] {
                let stored = other.has(STORE) && !other.has(DATA);
                let cell = run.cell_of(*other).filter(|c| c.account == self.subject);
                let (true, true, Some(cell)) =
                    (caller.only(CALLER) && *value == OWNER, stored, cell)
                else {
                    continue;
                };
                let held = self.states[0].world.stored(self.subject, cell.slot);
                if !low_address(held).is_zero() {
                    continue;
                }
                self.states[0]
                    .world
                    .seed(self.subject, cell.slot, held | OWNER);
                self.assumed.push(format!(
                    "slot {} names the owner, since the code compares the caller with it",
                    cell.slot.to_hex()
                ));
                if let Some(place) = self.facts.places.get_mut(&cell.place()) {
                    place.assumed = true;
                }
                changed = true;
            }
        }
        changed
    }

    fn assume_from(&mut self, t: &Try, run: &Run, entry: usize) -> bool {
        let subject = self.subject;
        let base = &self.states[0].world;
        let mut options: Vec<(U256, U256, String)> = Vec::new();
        for event in run.events.iter().rev() {
            match event {
                Event::Branch { tag, .. } if tag.has(STORE) && !tag.has(DATA | VALUE | MATH) => {
                    let Some(cell) = run.cell_of(*tag).filter(|c| c.account == subject) else {
                        continue;
                    };
                    let held = base.stored(subject, cell.slot);
                    let by_caller = cell
                        .keys
                        .iter()
                        .any(|k| k.tag.only(CALLER) && k.value == OWNER);
                    if by_caller && held.is_zero() {
                        let why = format!(
                            "the owner holds the role kept at slot {}, since the code tests the caller's entry there",
                            cell.root.to_hex()
                        );
                        options.push((cell.slot, U256::ONE, why));
                        continue;
                    }
                    let written = self
                        .facts
                        .places
                        .get(&cell.place())
                        .is_some_and(|p| !p.writers.is_empty());
                    if by_caller || written || tag.has(CALLER) || options.len() >= 8 {
                        continue;
                    }
                    let why = format!(
                        "slot {} is set, since the owner's call needs it",
                        cell.slot.to_hex()
                    );
                    let compared = run.events.iter().filter_map(|ev| match ev {
                        Event::Cmp { a, b, ta, tb, .. }
                            if ta.cell == tag.cell && !tb.has(STORE) =>
                        {
                            Some(*b)
                        }
                        Event::Cmp { a, b, ta, tb, .. }
                            if tb.cell == tag.cell && !ta.has(STORE) =>
                        {
                            Some(*a)
                        }
                        _ => None,
                    });
                    let mut values: Vec<U256> = compared
                        .flat_map(|v| [v, v.wrapping_add(U256::ONE), v.wrapping_sub(U256::ONE)])
                        .collect();
                    values.push(U256::ONE);
                    for value in values.into_iter().take(4) {
                        options.push((cell.slot, value, why.clone()));
                    }
                }
                _ => {}
            }
        }
        for (slot, value, why) in options.into_iter().take(10) {
            if budget::spent() {
                return false;
            }
            let mut world = self.states[0].world.clone();
            if world.stored(subject, slot) == value {
                continue;
            }
            world.seed(subject, slot, value);
            let (_, next) = self.attempt_in(world, entry, t);
            if better(&next, run) {
                self.states[0].world.seed(subject, slot, value);
                self.assumed.push(why);
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
                    for seed in self.honest(entry, who) {
                        if budget::spent() || self.states.len() >= MAX_STATES / 2 {
                            return;
                        }
                        let (t, world, run) = self.solve(from, entry, Try::of(seed));
                        if run.ok && self.novel(&run) {
                            next.push(self.keep(from, entry, &t, world, false));
                            break;
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
        steps: Vec<Step>,
        run: &Run,
        via_hook: bool,
    ) {
        for breach in breaches {
            let place = breach.cell.as_ref().map(crate::trace::Cell::place);
            let same = |v: &Violation| {
                v.breach.kind == breach.kind
                    && v.entry == entry
                    && v.breach.asset == breach.asset
                    && v.breach.cell.as_ref().map(crate::trace::Cell::place) == place
            };
            match self.found.iter_mut().find(|v| same(v)) {
                Some(known) if known.steps.len() <= steps.len() => {}
                Some(known) => {
                    *known = Violation {
                        breach,
                        entry,
                        steps: steps.clone(),
                        run: run.clone(),
                        via_hook,
                    };
                }
                None => self.found.push(Violation {
                    breach,
                    entry,
                    steps: steps.clone(),
                    run: run.clone(),
                    via_hook,
                }),
            }
        }
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
                let identity = self
                    .facts
                    .places
                    .get(&cell.place())
                    .is_some_and(|p| p.identity);
                cell.account == self.subject
                    && identity
                    && low_address(*old).is_zero()
                    && !new.is_zero()
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
            let breaches = laws::check(&base, &before, &after, &again, &self.facts);
            let takeovers: Vec<Breach> = breaches
                .into_iter()
                .filter(|b| matches!(b.kind, Kind::Takeover | Kind::RoleCleared))
                .collect();
            let steps = self.history(from, entry, &t.msg);
            self.report(takeovers, entry, steps, &again, false);
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
            let breaches = laws::check(&base, &before, &after, &run, &self.facts);
            let fresh: Vec<Breach> = breaches
                .into_iter()
                .filter(|b| !plain.iter().any(|p| p.kind == b.kind && p.asset == b.asset))
                .collect();
            let steps = self.history(from, entry, &again.msg);
            self.report(fresh, entry, steps, &run, true);
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
                            plain = laws::check(&base, &before, &world, &run, &self.facts);
                            let steps = self.history(from, entry, &t.msg);
                            self.report(plain.clone(), entry, steps, &run, false);
                            self.takes_from_owner(from, entry, &t, &run);
                        }
                        if handed {
                            self.reenter(from, entry, &t, &plain);
                        }
                        if run.ok && self.novel(&run) && !kept && self.states.len() < MAX_STATES {
                            next.push(self.keep(from, entry, &t, world, true));
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
        budget::within(work / 2, || self.attack());
    }
}

// The tag of a call data word, for tests and reports that build their own messages.
#[must_use]
pub fn data_word(index: usize) -> Tag {
    Tag::data(4 + 32 * index)
}
