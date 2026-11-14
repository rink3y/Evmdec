use crate::abi::{self, SEL_BALANCE_OF, SEL_TRANSFER, SEL_TRANSFER_FROM};
use crate::analyze::{display_name, push, Confidence, Finding, Severity};
use crate::decompile::{Contract, Function};
use crate::deploy;
use crate::exec;
use crate::function::FnKind;
use crate::hex;
use crate::interp::Rng;
use crate::path::{self, Explorers, Limits, Path};
use crate::solve::{word, Free, Inputs};
use crate::u256::U256;
use crate::world::{Call, Done, Holdings, Swung, World, PURSE};
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
const STALE_ROUNDS: usize = 10_000;
// A contract whose calls are long gets through few rounds. It is stale by work done.
const STALE_WORK: u64 = WORK / 8;
const SEEDS_PER_ENTRY: usize = 4;
const MAX_READS: usize = 1_024;
const MAX_POSITIONS: usize = 96;
const MAX_SET_SLOTS: usize = 64;
const SEED_LIMITS: Limits = Limits { paths: 6, runs: 18 };
const FIRST_VALUE: u64 = 0x1001;
const SIZES: [u32; 4] = [0, 1, 2, 4];
const WAITS: [u64; 4] = [3_600, 86_400, 30 * 86_400, 365 * 86_400];
const UNUSED_SELECTOR: u32 = 0xffff_ffff;

struct Entry<'a> {
    function: &'a Function,
    at: usize,
    shape: Vec<u8>,
    fixed: Vec<usize>,
    addresses: Vec<usize>,
    // How many leading words of the call are parameters, as far as the types say.
    params: usize,
    seeds: Vec<(Vec<u8>, U256)>,
    reads: BTreeSet<U256>,
    helped: HashSet<usize>,
}

#[derive(Clone)]
enum Step {
    Call(usize, Call),
    // Value sent straight to the contract, outside any of its functions.
    Gift(U256, Option<U256>, U256),
}

impl Step {
    fn waited_by_actor(&self) -> bool {
        matches!(self, Step::Call(_, call) if call.who == ACTOR && call.seconds_later > 0)
    }

    fn by_actor(&self) -> bool {
        match self {
            Step::Call(_, call) => call.who == ACTOR,
            Step::Gift(who, ..) => *who == ACTOR,
        }
    }
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
    // The one answer a call of this sequence saw differently, and whether the call
    // data named the contract that gave it.
    swung: Option<(Swung, bool)>,
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
    swung: Option<(Swung, bool)>,
}

// One call by the actor after which the other account has less.
struct Less {
    steps: Vec<Step>,
    before: Holdings,
    now: Holdings,
    waited: bool,
}

// Which way each holding of the two accounts went, which slots are set, whether value
// the contract has no record of was sent to it, and whether a call saw an answer
// differently.
type Place = (Vec<(U256, Ordering)>, BTreeSet<U256>, bool, bool);

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
    // What the solver had outside contracts answer. Every world is told the same.
    readings: Vec<((U256, u32), Vec<u8>)>,
}

fn names(data: &[u8], who: U256) -> bool {
    let words = data.len().saturating_sub(4) / 32;
    (0..words).any(|i| word(data, 4 + 32 * i) == who)
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
        // An answer the caller can move is one it will move. Any other may be out of
        // its reach.
        match self.swung {
            Some((swung, named)) if swung.balance || named => return Severity::High,
            Some(_) => return Severity::Medium,
            None => {}
        }
        match (self.outside(), self.recorded || self.taken, self.waited) {
            (true, true, _) | (false, _, false) => Severity::High,
            _ => Severity::Medium,
        }
    }

    fn better_than(&self, other: &Broken) -> bool {
        // The most severe level sorts first.
        let rank = |b: &Broken| (b.swung.is_some(), b.severity(), b.reentered, b.steps.len());
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
                    params: match function.params.len() {
                        0 => WORDS,
                        n => n,
                    },
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
            swung: None,
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
            readings: Vec::new(),
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
            answers: true,
            fixed: entry.fixed.clone(),
            ..Free::default()
        };
        let code = self.c.code_of(entry.function);
        let found = self.explorers.of(code).explore(&start, &free, SEED_LIMITS);
        let ended: Vec<Path> = found.into_iter().filter(Path::succeeded).collect();
        for p in ended.iter().take(SEEDS_PER_ENTRY) {
            for (at, answer) in &p.inputs.answers {
                let Some(asked) = p.run.calls.get(*at) else {
                    continue;
                };
                let first = asked.input.get(..4).map(|b| [b[0], b[1], b[2], b[3]]);
                let (address, selector) = (asked.addr, first.map_or(0, u32::from_be_bytes));
                if !self.readings.iter().any(|(k, _)| *k == (address, selector)) {
                    self.readings.push(((address, selector), answer.clone()));
                }
            }
        }
        let inputs = ended
            .into_iter()
            .map(|p| (p.inputs.calldata, p.inputs.callvalue));
        inputs.take(SEEDS_PER_ENTRY).collect()
    }

    // An amount to send: nothing, a little, or a few times what this sequence has
    // already seen sent. What a contract pays out is often sized by what was paid in.
    fn size(&mut self, from: usize) -> U256 {
        let seen = &self.kept[from].amounts;
        let mut sizes = match seen.is_empty() {
            true => vec![U256::ZERO, U256::ONE, U256::from_u64(FIRST_VALUE)],
            false => vec![U256::ZERO],
        };
        sizes.extend(seen.iter().copied());
        let chosen = sizes[self.pick(sizes.len())];
        match chosen < PURSE {
            true => chosen << SIZES[self.pick(SIZES.len())],
            false => chosen,
        }
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
        // What was paid, and twice that: a credit is often a multiple of the payment.
        // What the contract holds is the most there is to ask for.
        let seen = self.kept[from].amounts.iter().filter(|a| **a < PURSE);
        pool.extend(seen.flat_map(|a| [*a, *a << 1]));
        pool.extend(self.kept[from].world.held(exec::SELF));
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
            let at = self.pick(words.min(self.entries[index].params));
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
        // A function that was solved with a payment is one whose payment matters, and
        // what it pays back is often sized by what was paid.
        let resized = match value.is_zero() {
            true => self.pick(8) == 0,
            false => self.pick(2) == 0,
        };
        if resized {
            value = self.size(from);
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
        // One answer from outside reads differently for this call, as it would when
        // someone moves what it reports for the length of one transaction.
        let swing = match who == ACTOR && self.kept[from].swung.is_none() && self.pick(8) == 0 {
            true => Some((self.pick(3), self.pick(4), self.pick(2) == 0)),
            false => None,
        };
        Call {
            who,
            data,
            value,
            seconds_later,
            back,
            swing,
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
        // Value sent to a contract nobody has a stake in is nobody's to lose. The other
        // account sends it only while the contract holds a payment it recorded.
        let parent = &self.kept[from];
        let stake = who == ACTOR || (parent.recorded && parent.world.holds_value(exec::SELF));
        if stake && self.pick(16) == 0 {
            self.gift(false, from, who);
            return;
        }
        let call = self.input(index, who, from);
        self.attempt(from, index, call);
    }

    fn gift(&mut self, keep: bool, from: usize, who: U256) -> Option<usize> {
        let mut world = self.kept[from].world.clone();
        let assets: Vec<U256> = world.assets().into_iter().collect();
        let asset = match self.pick(assets.len() + 1) {
            0 => None,
            n => Some(assets[n - 1]),
        };
        // Several times the largest payment seen, so that it is not lost in what the
        // contract holds.
        let seen = self.kept[from].amounts.iter().max().copied();
        let amount = seen.unwrap_or(U256::from_u64(FIRST_VALUE));
        let amount = match amount < PURSE {
            true => amount << 2,
            false => amount,
        };
        if !world.give(asset, who, exec::SELF, amount) {
            return None;
        }
        let done = Done {
            ended: true,
            moved: true,
            ..Done::default()
        };
        self.settle(keep, from, world, Step::Gift(who, asset, amount), &done)
    }

    fn attempt(&mut self, from: usize, index: usize, call: Call) -> bool {
        self.attempt_and(false, from, index, call).is_some()
    }

    // The state a call leaves when it ends and that state is kept. With `keep` it is
    // kept whether or not it is somewhere new.
    fn attempt_and(&mut self, keep: bool, from: usize, index: usize, call: Call) -> Option<usize> {
        let at = self.entries[index].at;
        let mut before = self.kept[from].world.clone();
        for ((address, selector), answer) in &self.readings {
            before.tell(*address, *selector, answer);
        }
        let mut world = before.clone();
        let mut call = call;
        let mut done = world.call(at, &call);
        // The same call with nothing made from inside it is the plainer account of
        // whatever it shows.
        if done.ended && !done.called_back && call.back.take().is_some() {
            world = before;
            done = world.call(at, &call);
        }
        if done.swung.is_none() {
            call.swing = None;
        }
        let known = &mut self.entries[index].reads;
        if known.len() < MAX_READS {
            known.extend(done.read.iter().copied());
        }
        if !done.ended {
            return None;
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
            return None;
        }
        let kept = self.settle(keep, from, world, Step::Call(index, call), &done);
        Some(kept.unwrap_or(from))
    }

    // The world the same steps leave from the start with every answer as first given.
    fn replayed(&self, steps: &[Step]) -> Option<World> {
        let mut world = self.kept[0].world.clone();
        for ((address, selector), answer) in &self.readings {
            world.tell(*address, *selector, answer);
        }
        for step in steps {
            let ended = match step {
                Step::Call(index, call) => {
                    let plain = Call {
                        swing: None,
                        ..call.clone()
                    };
                    world.call(self.entries[*index].at, &plain).ended
                }
                Step::Gift(who, asset, amount) => world.give(*asset, *who, exec::SELF, *amount),
            };
            if !ended {
                return None;
            }
        }
        Some(world)
    }

    // What a step that ended leaves: the properties are checked on it, and it is kept
    // to continue from when it is somewhere new.
    fn settle(
        &mut self,
        keep: bool,
        from: usize,
        world: World,
        step: Step,
        done: &Done,
    ) -> Option<usize> {
        let mut novel = keep;
        for branch in &done.branches {
            novel |= self.covered.insert(*branch);
        }
        let parent = &self.kept[from];
        let by_actor = step.by_actor();
        let base = match (by_actor, &parent.base) {
            (true, None) => Some(parent.world.holdings(ACTOR)),
            (_, base) => base.clone(),
        };
        let mut steps = parent.steps.clone();
        let mut written = parent.written.clone();
        let mut amounts = parent.amounts.clone();
        if written.len() < MAX_READS {
            written.extend(done.written.iter().copied());
        }
        let sent = match &step {
            Step::Call(_, call) => call.value,
            Step::Gift(_, _, amount) => *amount,
        };
        if !sent.is_zero() && !amounts.contains(&sent) {
            amounts.push(sent);
        }
        let brought = !by_actor && done.crossed && !done.written.is_empty();
        let recorded = parent.recorded || brought;
        let reentered = parent.reentered || done.called_back;
        let swung = match (&step, done.swung) {
            (Step::Call(_, call), Some(swung)) => Some((swung, names(&call.data, swung.address))),
            _ => parent.swung,
        };
        steps.push(step);
        let changed = !done.written.is_empty() || done.moved;
        let other = match changed {
            true => world.holdings(OTHER),
            false => parent.other.clone(),
        };
        let waited = steps.iter().any(Step::waited_by_actor);
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
        let now = match (&base, changed) {
            (Some(_), true) => Some(world.holdings(ACTOR)),
            _ => None,
        };
        if changed {
            let mut place = match (&base, &now) {
                (Some(base), Some(now)) => position(base, now),
                _ => Vec::new(),
            };
            place.extend(position(&self.kept[0].other, &other));
            // Which slots are set tells apart states the holdings alone do not. A
            // contract that sets a new slot on every call would never stop being new.
            let set = world.set_slots(exec::SELF);
            let room = self.positions.len() < MAX_POSITIONS && set.len() <= MAX_SET_SLOTS;
            let unrecorded = steps.iter().any(|s| matches!(s, Step::Gift(..)));
            let place = (place, set, unrecorded, swung.is_some());
            novel |= room && self.positions.insert(place);
        }
        if let (Some(base), Some(now)) = (&base, now) {
            if gained(base, &now) {
                let mut found = Broken {
                    steps: steps.clone(),
                    base: base.clone(),
                    now,
                    waited,
                    recorded,
                    taken,
                    reentered,
                    swung,
                };
                // A gain the same calls leave with every answer as first given is not
                // owed to the answer that differed.
                if swung.is_some()
                    && self
                        .replayed(&steps)
                        .is_some_and(|w| gained(base, &w.holdings(ACTOR)))
                {
                    found.swung = None;
                }
                // A gain the call leaves on its own is not owed to calling in again.
                if let (true, Some(Step::Call(index, call))) = (done.called_back, steps.last()) {
                    let mut plain = parent.world.clone();
                    let alone = Call {
                        back: None,
                        ..call.clone()
                    };
                    let ended = plain.call(self.entries[*index].at, &alone).ended;
                    if ended && gained(base, &plain.holdings(ACTOR)) {
                        found.reentered = parent.reentered;
                        found.steps.pop();
                        found.steps.push(Step::Call(*index, alone));
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
                swung,
                other,
            });
            return Some(self.kept.len() - 1);
        }
        None
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

    // What a contract pays back is often sized by what was paid, and random sizes
    // seldom meet the pair that matters. For each function that needs a payment: the
    // other account pays, value the contract has no record of arrives, and the actor
    // pays twice at each pair of a few sizes. Every state reached is kept, so that the
    // rounds after it try every way out from there.
    fn opening(&mut self, index: usize) {
        // A function that also ends without a payment does not size anything by it.
        let seeds = &self.entries[index].seeds;
        if seeds.iter().any(|(_, value)| value.is_zero()) {
            return;
        }
        let Some((data, value)) = seeds.iter().find(|(_, v)| *v < PURSE).cloned() else {
            return;
        };
        let pays = |who: U256, value: U256| Call {
            who,
            data: data.clone(),
            value,
            ..Call::default()
        };
        let Some(paid_in) = self.attempt_and(true, 0, index, pays(OTHER, value)) else {
            return;
        };
        let Some(given) = self.gift(true, paid_in, OTHER) else {
            return;
        };
        for first in SIZES {
            let call = pays(ACTOR, value << first);
            let Some(once) = self.attempt_and(true, given, index, call) else {
                continue;
            };
            for second in SIZES {
                self.attempt_and(true, once, index, pays(ACTOR, value << second));
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
        for index in 0..self.entries.len() {
            if exec::spent() {
                return;
            }
            self.opening(index);
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
    let line = |s: &Step| match s {
        Step::Call(_, call) => {
            let waited = match call.seconds_later {
                0 => String::new(),
                seconds => format!(", {seconds} seconds after the call before it"),
            };
            format!(
                "{} with value {} from {}{waited}",
                hex::encode(&call.data),
                call.value.to_hex(),
                call.who.to_hex()
            )
        }
        Step::Gift(who, asset, amount) => {
            let what = match asset {
                Some(asset) => format!("the asset at {}", asset.to_hex()),
                None => "ether".to_string(),
            };
            format!(
                "{} of {what} sent straight to the contract by {}, outside its functions",
                amount.to_hex(),
                who.to_hex()
            )
        }
    };
    steps.iter().map(line).collect()
}

fn report(c: &Contract, search: &Search, broken: &Broken, out: &mut Vec<Finding>) {
    let Some((Step::Call(entry, last), earlier)) = broken.steps.split_last() else {
        return;
    };
    let function = search.entries[*entry].function;
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
    let source = match (outside, broken.taken, c.linked.is_empty()) {
        (true, true, _) => "An asset left the other account during these calls, under the approval that account gave the contract when it paid in.",
        (true, false, true) => "The contract held nothing at the start and received only what the two accounts paid in, so what the account gained is the other account's payment.",
        (true, false, false) => "The contract held nothing at the start, so what the account gained is the other account's payment or was held by a contract this one calls, whose code ran as it is.",
        (false, ..) => "Nothing was paid for that balance, in ether or in any asset.",
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
    if let Some((swung, named)) = broken.swung {
        let how = match (swung.balance, named) {
            (true, _) => "That answer is an asset's count of what another account holds, which follows any transfer to that account, so whoever calls can move it.",
            (false, true) => "That answer comes from a contract the call data names, so whoever calls chooses what gives it.",
            (false, false) => "Whether a caller can move that answer is not known from this contract alone.",
        };
        push(
            out,
            "one-call-reading-leaves-a-gain",
            "A reading that differs for one call leaves the caller with a gain that stays",
            severity,
            Confidence::High,
            Some(function),
            None,
            format!(
                "Starting from {}, {} call(s) were made, the last to `{}`. With every outside answer as first given, the same calls leave the account with no gain. When one word of an answer from {} is {} instead of {} for that one call, and as first given for every other call, the account ends with {} and with no less of anything else. The contract held nothing at the start, so the difference comes out of what the other account paid in. {how}",
                deploy::started_from(c),
                broken.steps.len(),
                function.name,
                swung.address.to_hex(),
                swung.now.to_hex(),
                swung.was.to_hex(),
                rose.join(" and "),
            ),
            Vec::new(),
            "Do not let an amount that is credited or paid follow a quantity read at the moment of the call. Use the contract's own records, or a value that one transaction cannot move, and bound what an account takes out by what is recorded for it.",
        );
        if let Some(finding) = out.last_mut() {
            finding.setup = shown(earlier);
            finding.confirmed = true;
            finding.witness = Some(hex::encode(&last.data));
            finding.observed = vec![format!("sent by {}", last.who.to_hex())];
        }
        return;
    }
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
            f.witness = Some(hex::encode(&last.data));
            f.observed = vec![format!("sent by {}", last.who.to_hex())];
        }
        return;
    }
    let own_calls = broken.steps.iter().filter(|s| s.by_actor()).count();
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
        finding.witness = Some(hex::encode(&last.data));
        finding.observed = vec![
            format!("sent by {}", last.who.to_hex()),
            format!(
                "ether held by that account: {} becomes {}",
                base.ether.to_hex(),
                now.ether.to_hex()
            ),
        ];
    }
}

fn report_less(c: &Contract, search: &Search, less: &Less, out: &mut Vec<Finding>) {
    let Some((Step::Call(entry, last), earlier)) = less.steps.split_last() else {
        return;
    };
    let function = search.entries[*entry].function;
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
        finding.witness = Some(hex::encode(&last.data));
        finding.observed = vec![format!("sent by {}", last.who.to_hex())];
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
