use crate::abi::{self, SEL_BALANCE_OF, SEL_TRANSFER, SEL_TRANSFER_FROM};
use crate::analyze::{display_name, push, Confidence, Finding, Severity};
use crate::decompile::{Contract, Function};
use crate::deploy;
use crate::exec;
use crate::function::FnKind;
use crate::hex;
use crate::interp::Rng;
use crate::path::{self, Explorers, Limits, Path};
use crate::solve::{Free, Inputs};
use crate::u256::U256;
use crate::world::{Call, Holdings, World, PURSE};
use std::cmp::Ordering;
use std::collections::{BTreeSet, HashSet};

pub const WORK: u64 = 4 * exec::WORK_PER_SECOND;

// The account whose gain is looked for. It holds no role and has paid nothing in.
const ACTOR: U256 = exec::CALLER;
// The account that uses the contract first, so that there is something in it.
const OTHER: U256 = U256::from_u64(0xbbbb_bbbb_bbbb_bbbb);
const SEED: u64 = 0x5ea2_c4ed;
const WORDS: usize = 6;
const MAX_ENTRIES: usize = 96;
const MAX_DEPTH: usize = 6;
const MAX_KEPT: usize = 240;
const MAX_ROUNDS: usize = 60_000;
// Rounds that reach no new code before the search is taken to have learnt what it can.
const STALE_ROUNDS: usize = 3_000;
// A contract whose calls are long gets through few rounds. It is stale by work done.
const STALE_WORK: u64 = WORK / 8;
const SEEDS_PER_ENTRY: usize = 4;
const MAX_READS: usize = 1_024;
const MAX_POSITIONS: usize = 96;
const MAX_SET_SLOTS: usize = 64;
const SEED_LIMITS: Limits = Limits { paths: 6, runs: 18 };
const FIRST_VALUE: u64 = 0x1001;
const WAITS: [u64; 4] = [3_600, 86_400, 30 * 86_400, 365 * 86_400];
const UNUSED_SELECTOR: u32 = 0xffff_ffff;

struct Entry<'a> {
    function: &'a Function,
    at: usize,
    shape: Vec<u8>,
    fixed: Vec<usize>,
    addresses: Vec<usize>,
    seeds: Vec<(Vec<u8>, U256)>,
    reads: BTreeSet<U256>,
    helped: HashSet<usize>,
}

#[derive(Clone)]
struct Step {
    entry: usize,
    call: Call,
}

// A sequence of calls that ended, with the world it left behind.
#[derive(Clone)]
struct Kept {
    world: World,
    steps: Vec<Step>,
    written: BTreeSet<U256>,
    amounts: Vec<U256>,
    // What the actor held just before its first call. Everything the other account did
    // before that is the state the actor found, not something the actor gained.
    base: Option<Holdings>,
    // Whether a call that brought the other account's value in also wrote storage.
    // Value that came in with nothing written is value the contract keeps no record of.
    recorded: bool,
    // Whether a call by the actor moved an asset out of the other account.
    taken: bool,
    reentered: bool,
    other: Holdings,
}

struct Broken {
    steps: Vec<Step>,
    base: Holdings,
    now: Holdings,
    waited: bool,
    recorded: bool,
    taken: bool,
    // Whether the gain needs the account to call in again while it is being paid.
    reentered: bool,
}

// One call by the actor after which the other account has less.
struct Less {
    steps: Vec<Step>,
    before: Holdings,
    now: Holdings,
    waited: bool,
}

// Which way each holding of the two accounts went, and which slots are set.
type Place = (Vec<(U256, Ordering)>, BTreeSet<U256>);

struct Search<'a> {
    c: &'a Contract,
    entries: Vec<Entry<'a>>,
    kept: Vec<Kept>,
    covered: HashSet<(usize, usize, bool)>,
    positions: HashSet<Place>,
    explorers: Explorers,
    rng: Rng,
    helps_left: usize,
    best: Option<Broken>,
    less: Option<Less>,
}

fn shape(f: &Function) -> (Vec<u8>, Vec<usize>) {
    let selector = exec::selector_of(f);
    let types: Vec<String> = f.params.iter().map(|p| p.ty.clone()).collect();
    let shaped = abi::layout(selector, &types);
    match f.kind {
        FnKind::Receive => (Vec::new(), Vec::new()),
        FnKind::Fallback => {
            let unused = Some(UNUSED_SELECTOR);
            (path::inputs_for(unused, WORDS).calldata, Vec::new())
        }
        _ if shaped.fixed.is_empty() => (path::inputs_for(selector, WORDS).calldata, Vec::new()),
        _ => (shaped.calldata, shaped.fixed),
    }
}

// More of something, and less of nothing. An account that paid ether for what it got
// did not gain, whatever the price.
// The words of the call that hold an address, as far as the types found say. The
// count stops at the first parameter that takes more than one word.
fn address_words(f: &Function) -> Vec<usize> {
    let one_word = |ty: &str| !ty.contains(['[', '(']) && ty != "bytes" && ty != "string";
    let heads = f.params.iter().take_while(|p| one_word(&p.ty));
    let address = |(_, p): &(usize, &crate::function::Param)| p.ty.starts_with("address");
    heads.enumerate().filter(address).map(|(i, _)| i).collect()
}

fn gained(base: &Holdings, now: &Holdings) -> bool {
    let mut pairs = vec![(base.ether, now.ether)];
    // An asset the account has not touched is one it still holds its whole purse of.
    let of = |h: &Holdings, asset: &U256| h.assets.get(asset).copied().unwrap_or(PURSE);
    for asset in base.assets.keys().chain(now.assets.keys()) {
        pairs.push((of(base, asset), of(now, asset)));
    }
    if let (Some(before), Some(after)) = (base.reported, now.reported) {
        pairs.push((before, after));
    }
    pairs.iter().all(|(a, b)| b >= a) && pairs.iter().any(|(a, b)| b > a)
}

// Which way each of an account's holdings went. A state where the two accounts'
// holdings went a way not seen before is a new place to continue from, whatever code
// ran to reach it.
fn position(base: &Holdings, now: &Holdings) -> Vec<(U256, Ordering)> {
    let of = |h: &Holdings, asset: &U256| h.assets.get(asset).copied().unwrap_or(PURSE);
    let assets = now
        .assets
        .keys()
        .map(|a| (*a, of(now, a).cmp(&of(base, a))));
    let own = (U256::MAX, now.reported.cmp(&base.reported));
    let ether = (U256::ZERO, now.ether.cmp(&base.ether));
    [ether, own].into_iter().chain(assets).collect()
}

impl Broken {
    fn outside(&self) -> bool {
        let rose = |(asset, held): (&U256, &U256)| {
            *held > self.base.assets.get(asset).copied().unwrap_or(PURSE)
        };
        self.now.ether > self.base.ether || self.now.assets.iter().any(rose)
    }

    // Ether and outside assets in the contract are what the two accounts paid in, so a
    // gain in them is the other account's money whenever it is taken. It is only known
    // to be owed to that account when the contract wrote something as it came in. A
    // balance in the contract's own ledger can also be a reward that accrues with time.
    fn severity(&self) -> Severity {
        match (self.outside(), self.recorded || self.taken, self.waited) {
            (true, true, _) | (false, _, false) => Severity::High,
            _ => Severity::Medium,
        }
    }

    fn better_than(&self, other: &Broken) -> bool {
        // The most severe level sorts first.
        let rank = |b: &Broken| (b.severity(), b.reentered, b.steps.len());
        rank(self) < rank(other)
    }
}

impl Less {
    fn own(&self) -> bool {
        matches!((self.before.reported, self.now.reported), (Some(a), Some(b)) if b < a)
    }

    // A balance the contract itself keeps for an account is that account's. An asset
    // that left under a standing approval may have been credited where a balance
    // function does not show it.
    fn severity(&self) -> Severity {
        match self.own() && !self.waited {
            true => Severity::High,
            false => Severity::Medium,
        }
    }

    fn better_than(&self, other: &Less) -> bool {
        let rank = |l: &Less| (l.severity(), l.steps.len());
        rank(self) < rank(other)
    }
}

impl<'a> Search<'a> {
    fn new(c: &'a Contract) -> Search<'a> {
        let reached = |f: &&Function| {
            matches!(
                f.kind,
                FnKind::External | FnKind::Fallback | FnKind::Receive
            )
        };
        let entries = c.functions.iter().enumerate();
        let entries = entries.filter(|(_, f)| reached(f)).take(MAX_ENTRIES);
        let entries: Vec<Entry<'a>> = entries
            .map(|(at, function)| {
                let (shape, fixed) = shape(function);
                Entry {
                    function,
                    at,
                    shape,
                    fixed,
                    addresses: address_words(function),
                    seeds: Vec::new(),
                    reads: BTreeSet::new(),
                    helped: HashSet::new(),
                }
            })
            .collect();
        let world = World::of(c, &[ACTOR, OTHER]);
        let start = Kept {
            other: world.holdings(OTHER),
            world,
            steps: Vec::new(),
            written: BTreeSet::new(),
            amounts: Vec::new(),
            base: None,
            recorded: false,
            taken: false,
            reentered: false,
        };
        Search {
            c,
            helps_left: 3 * entries.len(),
            entries,
            kept: vec![start],
            covered: HashSet::new(),
            positions: HashSet::new(),
            explorers: Explorers::default(),
            rng: Rng::new(SEED),
            best: None,
            less: None,
        }
    }

    fn pick(&mut self, n: usize) -> usize {
        (self.rng.next_u64() % n.max(1) as u64) as usize
    }

    // Inputs under which the function ends from this state, found by solving its own
    // checks. Random words do not pass a test of an amount against a balance.
    fn solved(&mut self, index: usize, who: U256, from: usize) -> Vec<(Vec<u8>, U256)> {
        let entry = &self.entries[index];
        let world = &self.kept[from].world;
        let (timestamp, number) = world.time();
        let one = U256::ONE.to_be_bytes().to_vec();
        let start = Inputs {
            calldata: path::fill_words(&entry.shape, &entry.fixed, path::varied_word),
            caller: who,
            callvalue: U256::from_u64(FIRST_VALUE),
            storage: world.slots(exec::SELF),
            timestamp,
            number,
            returned: one.clone(),
            replies: vec![
                (SEL_TRANSFER, one.clone()),
                (SEL_TRANSFER_FROM, one),
                (
                    SEL_BALANCE_OF,
                    U256::from_u64(FIRST_VALUE).to_be_bytes().to_vec(),
                ),
            ],
            ..path::inputs_for(None, 0)
        };
        let free = Free {
            words: start.calldata.len() / 32,
            value: true,
            fixed: entry.fixed.clone(),
            ..Free::default()
        };
        let code = self.c.code_of(entry.function);
        let found = self.explorers.of(code).explore(&start, &free, SEED_LIMITS);
        let ended = found.into_iter().filter(Path::succeeded);
        let inputs = ended.map(|p| (p.inputs.calldata, p.inputs.callvalue));
        inputs.take(SEEDS_PER_ENTRY).collect()
    }

    fn input(&mut self, index: usize, who: U256, from: usize) -> Call {
        let seeds = self.entries[index].seeds.len();
        let (mut data, mut value) = match seeds {
            0 => {
                let entry = &self.entries[index];
                let shape = path::fill_words(&entry.shape, &entry.fixed, path::varied_word);
                (shape, U256::ZERO)
            }
            _ => {
                let chosen = self.pick(seeds);
                self.entries[index].seeds[chosen].clone()
            }
        };
        let mut pool = vec![
            U256::ZERO,
            U256::ONE,
            U256::from_u64(FIRST_VALUE),
            U256::MAX,
            who,
        ];
        pool.extend(self.kept[from].amounts.iter().copied());
        if who == ACTOR {
            pool.push(OTHER);
        }
        let words = data.len().saturating_sub(4) / 32;
        // Without a solved input the plain shape is all there is, and it was tried.
        let changes = match seeds {
            0 => 1 + self.pick(2),
            _ => self.pick(3),
        };
        for _ in 0..changes {
            let at = self.pick(words);
            if words == 0 || self.entries[index].fixed.contains(&at) {
                continue;
            }
            let with = pool[self.pick(pool.len())];
            data[4 + 32 * at..36 + 32 * at].copy_from_slice(&with.to_be_bytes());
        }
        // An address a call names is one of the few that mean something here. The
        // other account never names the actor: an account it names has been given
        // something, and is no longer one with no role.
        let parties: &[U256] = match who == ACTOR {
            true => &[ACTOR, OTHER, exec::SELF],
            false => &[OTHER, exec::SELF],
        };
        for at in self.entries[index].addresses.clone() {
            if at < words && self.pick(2) == 0 {
                let with = parties[self.pick(parties.len())];
                data[4 + 32 * at..36 + 32 * at].copy_from_slice(&with.to_be_bytes());
            }
        }
        if self.pick(4) == 0 {
            value = pool[self.pick(3)];
        }
        let seconds_later = match self.pick(8) {
            0 => WAITS[self.pick(WAITS.len())],
            _ => 0,
        };
        // An account that is code can make a call of its own when it is paid.
        let back = match who == ACTOR && self.pick(6) == 0 {
            true => Some((data.clone(), U256::ZERO)),
            false => None,
        };
        Call {
            who,
            data,
            value,
            seconds_later,
            back,
        }
    }

    // A function that reads what the sequence so far has written is the one whose
    // behaviour that sequence changed.
    fn follows(&mut self, from: usize) -> usize {
        let written = &self.kept[from].written;
        let reads = |e: &Entry| e.reads.iter().any(|key| written.contains(key));
        let related: Vec<usize> = (0..self.entries.len())
            .filter(|i| reads(&self.entries[*i]))
            .collect();
        match (related.is_empty(), self.pick(4)) {
            (false, 1..) => related[self.pick(related.len())],
            _ => self.pick(self.entries.len()),
        }
    }

    fn round(&mut self) {
        let recent = self.kept.len().min(24);
        let from = match self.pick(2) {
            0 => self.kept.len() - 1 - self.pick(recent),
            _ => self.pick(self.kept.len()),
        };
        if self.kept[from].steps.len() >= MAX_DEPTH {
            return;
        }
        let index = self.follows(from);
        let acted = self.kept[from].base.is_some();
        let who = match (acted, self.pick(2)) {
            (false, 0) => OTHER,
            _ => ACTOR,
        };
        let call = self.input(index, who, from);
        self.attempt(from, index, call);
    }

    fn attempt(&mut self, from: usize, index: usize, call: Call) -> bool {
        let at = self.entries[index].at;
        let mut world = self.kept[from].world.clone();
        let mut call = call;
        let mut done = world.call(at, &call);
        // The same call with nothing made from inside it is the plainer account of
        // whatever it shows.
        if done.ended && !done.called_back && call.back.take().is_some() {
            world = self.kept[from].world.clone();
            done = world.call(at, &call);
        }
        let known = &mut self.entries[index].reads;
        if known.len() < MAX_READS {
            known.extend(done.read.iter().copied());
        }
        if !done.ended {
            return false;
        }
        // The starting state stands for a contract in use. A call that sets a slot it
        // found empty and cannot be made again is the contract's set-up. The other
        // account may make it, which is how the state a later call needs comes to be.
        // The account whose gain is looked for may not: its gain would be the set-up's.
        let zero = |world: &World, key: &U256| world.stored(exec::SELF, *key).is_zero();
        let before = &self.kept[from].world;
        let arms = |key: &U256| done.read.contains(key) && zero(before, key) && !zero(&world, key);
        if call.who == ACTOR
            && done.written.iter().any(arms)
            && !world.clone().call(at, &call).ended
        {
            return false;
        }
        let mut novel = false;
        for branch in &done.branches {
            novel |= self.covered.insert(*branch);
        }
        let parent = &self.kept[from];
        let base = match (call.who == ACTOR, &parent.base) {
            (true, None) => Some(parent.world.holdings(ACTOR)),
            (_, base) => base.clone(),
        };
        let mut steps = parent.steps.clone();
        let mut written = parent.written.clone();
        let mut amounts = parent.amounts.clone();
        if written.len() < MAX_READS {
            written.extend(done.written.iter().copied());
        }
        if !call.value.is_zero() && !amounts.contains(&call.value) {
            amounts.push(call.value);
        }
        let brought = call.who == OTHER && done.crossed && !done.written.is_empty();
        let recorded = parent.recorded || brought;
        let by_actor = call.who == ACTOR;
        let reentered = parent.reentered || done.called_back;
        steps.push(Step { entry: index, call });
        let changed = !done.written.is_empty() || done.moved;
        let other = match changed {
            true => world.holdings(OTHER),
            false => parent.other.clone(),
        };
        let waited = steps
            .iter()
            .any(|s| s.call.who == ACTOR && s.call.seconds_later > 0);
        let fell = by_actor && gained(&other, &parent.other);
        let taken = parent.taken || (fell && other.assets != parent.other.assets);
        if fell {
            let found = Less {
                steps: steps.clone(),
                before: parent.other.clone(),
                now: other.clone(),
                waited,
            };
            if self.less.as_ref().is_none_or(|l| found.better_than(l)) {
                self.less = Some(found);
            }
        }
        if let (Some(base), true) = (&base, changed) {
            let now = world.holdings(ACTOR);
            let mut place = position(base, &now);
            place.extend(position(&self.kept[0].other, &other));
            // Which slots are set tells apart states the holdings alone do not. A
            // contract that sets a new slot on every call would never stop being new.
            let set = world.set_slots(exec::SELF);
            let room = self.positions.len() < MAX_POSITIONS && set.len() <= MAX_SET_SLOTS;
            novel |= room && self.positions.insert((place, set));
            if gained(base, &now) {
                let mut found = Broken {
                    steps: steps.clone(),
                    base: base.clone(),
                    now,
                    waited,
                    recorded,
                    taken,
                    reentered,
                };
                // A gain the call leaves on its own is not owed to calling in again.
                if let (true, Some(last)) = (done.called_back, found.steps.last_mut()) {
                    let mut plain = parent.world.clone();
                    last.call.back = None;
                    let alone = plain.call(at, &last.call).ended;
                    let same = alone && gained(base, &plain.holdings(ACTOR));
                    match same {
                        true => found.reentered = parent.reentered,
                        false => last.call.back = steps.last().and_then(|s| s.call.back.clone()),
                    }
                }
                if self.best.as_ref().is_none_or(|b| found.better_than(b)) {
                    self.best = Some(found);
                }
            }
        }
        if novel && self.kept.len() < MAX_KEPT {
            self.kept.push(Kept {
                world,
                steps,
                written,
                amounts,
                base,
                recorded,
                taken,
                reentered,
                other,
            });
        }
        true
    }

    fn help(&mut self, from: usize, index: usize, who: U256) {
        if self.helps_left == 0 || !self.entries[index].helped.insert(from) {
            return;
        }
        self.helps_left -= 1;
        let mut found = self.solved(index, who, from);
        // The solver sends a payment in case the function wants one. A function that
        // ends without it is also called without it.
        let unpaid = found.iter().filter(|(_, value)| !value.is_zero());
        let unpaid: Vec<_> = unpaid.map(|(data, _)| (data.clone(), U256::ZERO)).collect();
        found.extend(unpaid);
        for (data, value) in found {
            let call = Call {
                who,
                data: data.clone(),
                value,
                ..Call::default()
            };
            if self.attempt(from, index, call) && self.entries[index].seeds.len() < 16 {
                self.entries[index].seeds.push((data, value));
            }
        }
    }

    fn run(&mut self) {
        for index in 0..self.entries.len() {
            if exec::spent() {
                return;
            }
            self.help(0, index, OTHER);
        }
        let mut rounds = 0;
        let learnt = self.covered.len() + self.positions.len();
        let (mut reached, mut fresh, mut fresh_at) = (learnt, 0, exec::work());
        let stale = |rounds: usize, fresh: usize, fresh_at: u64| {
            rounds - fresh >= STALE_ROUNDS || exec::work() - fresh_at >= STALE_WORK
        };
        while !exec::spent() && rounds < MAX_ROUNDS && !stale(rounds, fresh, fresh_at) {
            rounds += 1;
            self.round();
            let learnt = self.covered.len() + self.positions.len();
            if learnt > reached {
                (reached, fresh, fresh_at) = (learnt, rounds, exec::work());
            }
            // A state the search just reached may be the one a stuck function was
            // waiting for. Its own checks are solved again from there.
            if rounds % 64 == 0 && self.kept.len() > 1 {
                let from = self.kept.len() - 1;
                let index = self.follows(from);
                let who = match self.kept[from].base {
                    Some(_) => ACTOR,
                    None => OTHER,
                };
                self.help(from, index, who);
                self.help(from, index, ACTOR);
            }
        }
        if crate::debug::on("EVMDEC_DEBUG_SEARCH") {
            let seeded = self.entries.iter().filter(|e| !e.seeds.is_empty()).count();
            let holding = self
                .kept
                .iter()
                .filter(|k| k.world.holds_value(exec::SELF))
                .count();
            eprintln!(
                "[search] work={} entries={} seeded={seeded} rounds={rounds} kept={} holding={holding} covered={} broken={}",
                exec::work(),
                self.entries.len(),
                self.kept.len(),
                self.covered.len(),
                self.best.is_some()
            );
        }
    }
}

fn shown(steps: &[Step]) -> Vec<String> {
    let line = |s: &Step| {
        let waited = match s.call.seconds_later {
            0 => String::new(),
            seconds => format!(", {seconds} seconds after the call before it"),
        };
        format!(
            "{} with value {} from {}{waited}",
            hex::encode(&s.call.data),
            s.call.value.to_hex(),
            s.call.who.to_hex()
        )
    };
    steps.iter().map(line).collect()
}

fn report(c: &Contract, search: &Search, broken: &Broken, out: &mut Vec<Finding>) {
    let Some((last, earlier)) = broken.steps.split_last() else {
        return;
    };
    let function = search.entries[last.entry].function;
    let (base, now) = (&broken.base, &broken.now);
    let mut rose = Vec::new();
    if now.ether > base.ether {
        rose.push(format!("{} more ether", (now.ether - base.ether).to_hex()));
    }
    for (asset, held) in &now.assets {
        let before = base.assets.get(asset).copied().unwrap_or(PURSE);
        if *held > before {
            rose.push(format!(
                "{} more of the asset at {}",
                (*held - before).to_hex(),
                asset.to_hex()
            ));
        }
    }
    let own = matches!((base.reported, now.reported), (Some(a), Some(b)) if b > a);
    if let (true, Some(before), Some(after)) = (own, base.reported, now.reported) {
        rose.push(format!(
            "a balance in the contract's own ledger of {} where it had {}",
            after.to_hex(),
            before.to_hex()
        ));
    }
    let outside = broken.outside();
    let source = match (outside, broken.taken) {
        (true, true) => "An asset left the other account during these calls, under the approval that account gave the contract when it paid in.",
        (true, false) => "The contract held nothing at the start and received only what the two accounts paid in, so what the account gained is the other account's payment.",
        (false, _) => "Nothing was paid for that balance, in ether or in any asset.",
    };
    let severity = broken.severity();
    let timing = match (severity, outside) {
        (Severity::High, _) => "",
        (_, true) => {
            " No call that brought that payment in wrote anything to storage, so the contract keeps no record of whose it is. A contract that only passes value on within one transaction leaves what stays behind open in this way."
        }
        (_, false) => {
            " The gain needs time to pass between the calls, as a reward that accrues would. Whether that reward is meant to be open to an account that paid nothing is for a reader to judge."
        }
    };
    if broken.reentered {
        let note = format!(
            " Confirmed by running it: after the attached earlier call(s), the attached call is made by an account whose code makes the same call again when it is paid. Every call ends normally and the account ends with {} and with no less of anything else. The same call with nothing made from inside it leaves no gain.",
            rose.join(" and "),
        );
        let name = display_name(function);
        let known = |f: &&mut Finding| {
            f.id.starts_with("reentrancy") && f.function.as_deref() == Some(name.as_str())
        };
        if out.iter_mut().find(known).is_none() {
            push(
                out,
                "reentered-call-pays-again",
                "A call made again from inside its own payment is paid twice",
                Severity::High,
                Confidence::High,
                Some(function),
                None,
                format!(
                    "`{}` pays its caller before it has finished recording the payment.",
                    function.name
                ),
                Vec::new(),
                "Finish every storage update before the payment, or hold a lock across it.",
            );
        }
        if let Some(f) = out.iter_mut().find(known) {
            f.description.push_str(&note);
            f.confidence = Confidence::High;
            f.setup = shown(earlier);
            f.confirmed = true;
            f.witness = Some(hex::encode(&last.call.data));
            f.observed = vec![format!("sent by {}", last.call.who.to_hex())];
        }
        return;
    }
    let own_calls = broken.steps.iter().filter(|s| s.call.who == ACTOR).count();
    push(
        out,
        "calls-leave-account-with-gain",
        "A sequence of calls leaves an account with more than it started with",
        severity,
        Confidence::High,
        Some(function),
        None,
        format!(
            "Starting from {}, {} call(s) were made, {} of them by an account with no role, the last to `{}`. Every call ended normally. That account ends with {} and with no less of anything else. {source}{timing} The assets the contract calls keep honest books in these runs: a transfer the sender cannot cover fails, and the contract is told it holds exactly what was sent to it.",
            deploy::started_from(c),
            broken.steps.len(),
            own_calls,
            function.name,
            rose.join(" and "),
        ),
        Vec::new(),
        "Bound what an account can take out, or be credited, by what it paid in or is recorded as owed.",
    );
    if let Some(finding) = out.last_mut() {
        finding.setup = shown(earlier);
        finding.confirmed = true;
        finding.witness = Some(hex::encode(&last.call.data));
        finding.observed = vec![
            format!("sent by {}", last.call.who.to_hex()),
            format!(
                "ether held by that account: {} becomes {}",
                base.ether.to_hex(),
                now.ether.to_hex()
            ),
        ];
    }
}

fn report_less(c: &Contract, search: &Search, less: &Less, out: &mut Vec<Finding>) {
    let Some((last, earlier)) = less.steps.split_last() else {
        return;
    };
    let function = search.entries[last.entry].function;
    let (before, now) = (&less.before, &less.now);
    let mut fell = Vec::new();
    for (asset, held) in &now.assets {
        let had = before.assets.get(asset).copied().unwrap_or(PURSE);
        if *held < had {
            fell.push(format!(
                "{} less of the asset at {}",
                (had - *held).to_hex(),
                asset.to_hex()
            ));
        }
    }
    if let (true, Some(had), Some(has)) = (less.own(), before.reported, now.reported) {
        fell.push(format!(
            "a balance in the contract's own ledger of {} where it had {}",
            has.to_hex(),
            had.to_hex()
        ));
    }
    let note = match (less.own(), less.waited) {
        (true, false) => "",
        (true, true) => " Time passed between the calls, and a balance that runs down with time would fall in the same way.",
        (false, _) => " The asset left under the approval that account gave the contract when it paid in. It went to the contract or to a third account, and a credit for it that no balance function shows cannot be seen from outside.",
    };
    push(
        out,
        "call-leaves-another-account-with-less",
        "A call leaves an account that took no part in it with less",
        less.severity(),
        Confidence::High,
        Some(function),
        None,
        format!(
            "Starting from {}, {} call(s) were made. The last, to `{}`, was made by an account with no role and ended normally. The other account made no call after its own and is left with {} and with no more of anything else.{note}",
            deploy::started_from(c),
            less.steps.len(),
            function.name,
            fell.join(" and "),
        ),
        Vec::new(),
        "Let a call lower only what its caller holds, or what an account agreed to in that call.",
    );
    if let Some(finding) = out.last_mut() {
        finding.setup = shown(earlier);
        finding.confirmed = true;
        finding.witness = Some(hex::encode(&last.call.data));
        finding.observed = vec![format!("sent by {}", last.call.who.to_hex())];
    }
}

// One search over sequences of calls. It keeps every sequence that reached code no
// earlier one reached, extends those, and checks after each call whether an account
// with no role now holds more than before its first call, and whether the other
// account holds less than before that call.
pub fn findings(c: &Contract, out: &mut Vec<Finding>) {
    if std::env::var("EVMDEC_NO_CONFIRM").is_ok() || c.info.runtime.is_empty() {
        return;
    }
    let mut search = Search::new(c);
    if search.entries.is_empty() {
        return;
    }
    search.run();
    let taken = search.best.as_ref().is_some_and(|b| b.taken);
    if let Some(broken) = search.best.take() {
        report(c, &search, &broken, out);
    }
    // A gain that came out of the other account already says what that account lost.
    if let (Some(less), false) = (search.less.take(), taken) {
        report_less(c, &search, &less, out);
    }
}
