use crate::abi::{self, SEL_BALANCE_OF, SEL_TRANSFER, SEL_TRANSFER_FROM};
use crate::analyze::{display_name, push, Confidence, Finding, Severity};
use crate::confirm;
use crate::decompile::{Contract, Function};
use crate::deploy;
use crate::exec;
use crate::expr::{self, ExprId, Node};
use crate::function::FnKind;
use crate::hex;
use crate::interp::Rng;
use crate::lift::{Stmt, Term};
use crate::opcode as op;
use crate::path::{self, Explorers, Limits, Path};
use crate::solve::{word, Free, Inputs};
use crate::u256::U256;
use crate::world::{Call, Done, Holdings, Made, Swung, World, PURSE};
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

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
const MAX_SPLITS: usize = 24;
const MAX_FRESH_STARTS: usize = 48;
const MAX_ROLE_TRIES: usize = 16;
const MAX_SITES: usize = 256;
const SEED_LIMITS: Limits = Limits { paths: 6, runs: 18 };
const FIRST_VALUE: u64 = 0x1001;
const STAKE: U256 = U256([0, 1 << 16, 0, 0]);
const SIZES: [u32; 4] = [0, 1, 2, 4];
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

// The slots whose stored address some check compares the caller with. Holding one is
// what lets an account past that check.
fn role_slots(c: &Contract) -> BTreeSet<U256> {
    let bare = |e: ExprId| match expr::node(e) {
        Node::Op(op::AND, v) if expr::as_const(v[1]) == Some(expr::mask_bits(160)) => v[0],
        _ => e,
    };
    let caller = |e: ExprId| matches!(expr::node(bare(e)), Node::Env(op::CALLER, _));
    let slot = |e: ExprId| match expr::node(bare(e)) {
        Node::SLoad(k, false, _) => expr::as_const(k),
        _ => None,
    };
    let mut out = BTreeSet::new();
    let graphs = c.functions.iter().filter_map(|f| f.lifted.as_ref());
    for nd in graphs.flat_map(|l| l.nodes.iter()) {
        let required = nd.stmts.iter().filter_map(|s| match s {
            Stmt::Require { cond, .. } => Some(*cond),
            _ => None,
        });
        let branched = match &nd.term {
            Term::Branch { cond, .. } => Some(*cond),
            _ => None,
        };
        let mut stack: Vec<ExprId> = required.chain(branched).collect();
        let mut seen = HashSet::new();
        while let Some(e) = stack.pop() {
            if !seen.insert(e) || seen.len() > MAX_READS {
                continue;
            }
            if let Node::Op(op::EQ | op::SUB | op::XOR, v) = expr::node(e) {
                let pairs = [(v[0], v[1]), (v[1], v[0])];
                let named = pairs.iter().filter(|(a, _)| caller(*a));
                out.extend(named.filter_map(|(_, b)| slot(*b)));
            }
            stack.extend(expr::children(e));
        }
    }
    out
}

// What a call by the account with no role did to a slot that names who a check lets
// through.
struct Chosen<K> {
    steps: Vec<Step>,
    at: usize,
    first: K,
    then: K,
}

struct Role {
    steps: Vec<Step>,
    slot: U256,
    taken: bool,
}

#[derive(Clone)]
enum Step {
    Call(usize, Call),
    // Value sent straight to the contract, outside any of its functions.
    Gift(U256, Option<U256>, U256),
}

impl Step {
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
    // A call by which the other account takes out from here, and what it then holds.
    exit: Option<(usize, Call, Holdings)>,
    other: Holdings,
}

struct Broken {
    steps: Vec<Step>,
    base: Holdings,
    now: Holdings,
    recorded: bool,
    taken: bool,
    // Whether the gain needs the account to call in again while it is being paid.
    reentered: bool,
    swung: Option<(Swung, bool)>,
}

// A call by the actor that moves no value and after which the other account's way out
// pays it less.
struct Lowered {
    steps: Vec<Step>,
    exit: (usize, Call),
    before: Holdings,
    after: Holdings,
}

// A take-out that costs less in two parts than in one.
struct Rounded {
    steps: Vec<Step>,
    word: usize,
    whole: U256,
    parts: (U256, U256),
}

// One call by the actor after which the other account has less.
struct Less {
    steps: Vec<Step>,
    before: Holdings,
    now: Holdings,
}

// Which way each holding of the two accounts went, which slots are set, whether value
// the contract has no record of was sent to it, and whether a call saw an answer
// higher or lower.
type Place = (
    Vec<(U256, Ordering)>,
    BTreeSet<U256>,
    bool,
    Option<Ordering>,
);

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
    lowered: Option<Lowered>,
    // States from which a way out was just found, still to be probed.
    exits: Vec<usize>,
    renamed: Vec<(usize, Call)>,
    rounded: Option<Rounded>,
    roles: BTreeSet<U256>,
    role: Option<Role>,
    role_tries: usize,
    // For each place the contract called out from, the first call that got there.
    sites: BTreeMap<usize, (usize, usize, Call)>,
    // How often each function has been tried in two parts.
    splits: HashMap<usize, usize>,
    // Whether both accounts were given some of the contract's own token to start with.
    staked: bool,
}

// A token nobody holds shows nothing of what its code does to a holder. Both accounts
// start with an amount in the slot the contract's own balance function reads for each
// of them. A balance function that reads anything else is left alone.
fn stake(world: &mut World, balance_of: usize) -> bool {
    let slot = |who: U256| {
        let call = Call {
            who,
            data: exec::calldata(Some(SEL_BALANCE_OF), &[who]),
            ..Call::default()
        };
        let done = world.clone().call(balance_of, &call);
        let zero = done.ended && done.returned.len() >= 32 && word(&done.returned, 0).is_zero();
        match (zero, done.read.len()) {
            (true, 1) => done.read.first().copied(),
            _ => None,
        }
    };
    let (Some(actor), Some(other)) = (slot(ACTOR), slot(OTHER)) else {
        return false;
    };
    let mut held = world.clone();
    held.seed(exec::SELF, actor, STAKE);
    held.seed(exec::SELF, other, STAKE);
    let holds = |who: U256| held.holdings(who).reported == Some(STAKE);
    if actor == other || !holds(ACTOR) || !holds(OTHER) {
        return false;
    }
    *world = held;
    true
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
        _ if shaped.fixed.is_empty() => {
            let words = WORDS.max(f.params.len());
            (path::inputs_for(selector, words).calldata, Vec::new())
        }
        _ => (shaped.calldata, shaped.fixed),
    }
}

// The words of the call that hold an address, as far as the types found say. The
// count stops at the first parameter that takes more than one word.
fn address_words(f: &Function) -> Vec<usize> {
    let one_word = |ty: &str| !ty.contains(['[', '(']) && ty != "bytes" && ty != "string";
    let heads = f.params.iter().take_while(|p| one_word(&p.ty));
    let address = |(_, p): &(usize, &crate::function::Param)| p.ty.starts_with("address");
    heads.enumerate().filter(address).map(|(i, _)| i).collect()
}

// More of something, and less of nothing. An account that paid ether for what it got
// did not gain, whatever the price.
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
        match self.outside() && !self.recorded && !self.taken {
            true => Severity::Medium,
            false => Severity::High,
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
        match self.own() {
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
        let mut world = World::of(c, &[ACTOR, OTHER]);
        let balance_of = |e: &&Entry| exec::selector_of(e.function) == Some(SEL_BALANCE_OF);
        let balance_of = entries.iter().find(balance_of).map(|e| e.at);
        let staked = balance_of.is_some_and(|at| stake(&mut world, at));
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
            exit: None,
        };
        Search {
            c,
            helps_left: 6 * entries.len(),
            entries,
            kept: vec![start],
            covered: HashSet::new(),
            positions: HashSet::new(),
            explorers: Explorers::default(),
            rng: Rng::new(SEED),
            best: None,
            less: None,
            lowered: None,
            exits: Vec::new(),
            renamed: Vec::new(),
            rounded: None,
            roles: role_slots(c),
            role: None,
            role_tries: 0,
            sites: BTreeMap::new(),
            splits: HashMap::new(),
            staked,
        }
    }

    fn started_from(&self) -> String {
        let storage = deploy::started_from(self.c);
        match self.staked {
            true => format!(
                "{storage}, with {} of the contract's own token written for each of the two accounts in the slot its balance function reads",
                STAKE.to_hex()
            ),
            false => storage.to_string(),
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
        let ended: Vec<Path> = found.into_iter().filter(Path::succeeded).collect();
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
        // Once the actor holds a stake, value sent in by the other account is a present
        // to it and shows nothing.
        let parent = &self.kept[from];
        let held = !acted && parent.recorded && parent.world.holds_value(exec::SELF);
        let stake = who == ACTOR || held;
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
        let before = self.kept[from].world.clone();
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
        for made in &done.made {
            if self.sites.len() < MAX_SITES {
                let first = (from, index, call.clone());
                self.sites.entry(made.at).or_insert(first);
            }
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

    // Empty storage cannot tell a first set-up from a takeover. The last step is run
    // again with the role held by another account.
    fn takes_from_holder(&self, steps: &[Step], slot: U256) -> Option<bool> {
        let (Step::Call(index, call), earlier) = steps.split_last()? else {
            return None;
        };
        let mut world = self.replayed(earlier)?;
        let mask = expr::mask_bits(160);
        let held = world.stored(exec::SELF, slot);
        world.seed(exec::SELF, slot, (held & !mask) | OTHER);
        let plain = Call {
            swing: None,
            ..call.clone()
        };
        let done = world.call(self.entries[*index].at, &plain);
        let now = world.stored(exec::SELF, slot) & mask;
        match done.ended && !done.asked {
            true if now == ACTOR => Some(true),
            true if now.is_zero() => Some(false),
            _ => None,
        }
    }

    // Whether what the contract calls follows the call data, asked from a state that a
    // sequence of calls reached. `seen` reads the part in question off a call made: its
    // first four bytes, or the address called. The call data is changed four bytes at a
    // time. `Some(None)` is a part no change moved.
    fn tracks<K: PartialEq + Copy>(
        &self,
        site: &std::ops::Range<usize>,
        seen: impl Fn(&Made) -> Option<K>,
    ) -> Option<Option<Chosen<K>>> {
        let (pc, (from, index, call)) = self.sites.range(site.clone()).next()?;
        let at_site = |done: &Done| done.made.iter().find(|m| m.at == *pc).and_then(&seen);
        let entry = self.entries[*index].at;
        let run = |call: &Call| self.kept[*from].world.clone().call(entry, call);
        let first = at_site(&run(call))?;
        let chunks = (call.data.len().saturating_sub(4) / 4).min(confirm::MAX_CHUNKS);
        let mut trials = 0;
        for chunk in 0..chunks {
            if exec::spent() {
                return None;
            }
            let at = 4 + 4 * chunk;
            let mut changed = call.clone();
            for (byte, flip) in changed.data[at..at + 4].iter_mut().zip(confirm::FLIP) {
                *byte ^= flip;
            }
            let Some(then) = at_site(&run(&changed)) else {
                continue;
            };
            trials += 1;
            if then != first {
                let mut steps = self.kept[*from].steps.clone();
                steps.push(Step::Call(*index, call.clone()));
                return Some(Some(Chosen {
                    steps,
                    at,
                    first,
                    then,
                }));
            }
        }
        (trials >= confirm::MIN_TRIALS).then_some(None)
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
        let took_out = !by_actor && gained(&parent.other, &other);
        let exit = match (steps.last(), took_out && parent.base.is_none()) {
            (Some(Step::Call(index, call)), true) => Some((*index, call.clone(), other.clone())),
            _ => None,
        };
        // An answer that read differently for one call belongs to the gain it may leave
        // and to nothing else. Read lower, a refusal can look like a permission.
        let plain = swung.is_none();
        if let (Some(Step::Call(index, call)), true) = (steps.last(), by_actor && plain) {
            let quiet = !done.moved && !done.written.is_empty();
            let found = match (quiet, &parent.exit) {
                (true, Some(exit)) => self.lowers(parent, &world, exit, &steps),
                _ => None,
            };
            let shorter = |l: &Lowered| {
                self.lowered
                    .as_ref()
                    .is_none_or(|k| l.steps.len() < k.steps.len())
            };
            if let Some(found) = found.filter(shorter) {
                self.lowered = Some(found);
            }
            // Only a call that lowered a record has a cost that two parts could beat.
            let costs = done.writes.iter().any(|w| w.after < w.before);
            let tries = self.splits.get(index).copied().unwrap_or(0);
            if done.crossed && costs && self.rounded.is_none() && tries < MAX_SPLITS {
                self.splits.insert(*index, tries + 1);
                self.rounded = self.split(parent, &world, *index, call, &steps);
            }
        }
        let unpaid = match steps.last() {
            Some(Step::Call(_, call)) => call.value.is_zero(),
            _ => false,
        };
        // An account let past a check by what it paid has bought its place. A call
        // that went through because an unknown contract said yes shows nothing.
        if by_actor && plain && unpaid && !done.asked && self.role_tries < MAX_ROLE_TRIES {
            let low = |v: U256| v & expr::mask_bits(160);
            let named = |w: &&crate::world::Write| {
                let role = w.address == exec::SELF && self.roles.contains(&w.slot);
                role && (low(w.after) == ACTOR || low(w.after).is_zero())
            };
            let slots: BTreeSet<U256> = done.writes.iter().filter(named).map(|w| w.slot).collect();
            for slot in slots {
                self.role_tries += 1;
                let taken = self.takes_from_holder(&steps, slot);
                let better = self
                    .role
                    .as_ref()
                    .is_none_or(|r| taken == Some(true) && !r.taken);
                if let (Some(taken), true) = (taken, better) {
                    self.role = Some(Role {
                        steps: steps.clone(),
                        slot,
                        taken,
                    });
                }
            }
        }
        let fell = by_actor && plain && gained(&other, &parent.other);
        let taken = parent.taken || (fell && other.assets != parent.other.assets);
        if fell {
            let found = Less {
                steps: steps.clone(),
                before: parent.other.clone(),
                now: other.clone(),
            };
            if self.less.as_ref().is_none_or(|l| found.better_than(l)) {
                self.less = Some(found);
                // What left the other account went where the call named. The same call
                // naming the caller in each of those places is tried next, and not left
                // to the chance of the caller's address being drawn there.
                if let Some(Step::Call(index, call)) = steps.last() {
                    for word in &self.entries[*index].addresses {
                        let at = 4 + 32 * word;
                        let mut named = call.clone();
                        if named.data.len() >= at + 32 {
                            named.data[at..at + 32].copy_from_slice(&ACTOR.to_be_bytes());
                            self.renamed.push((*index, named));
                        }
                    }
                }
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
            let seen = swung.map(|(swung, _)| swung.now.cmp(&swung.was));
            let place = (place, set, unrecorded, seen);
            novel |= room && self.positions.insert(place);
        }
        if let (Some(base), Some(now)) = (&base, now) {
            if gained(base, &now) {
                let mut found = Broken {
                    steps: steps.clone(),
                    base: base.clone(),
                    now,
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
        if let (Some(exit), None) = (exit, &self.kept[from].exit) {
            self.kept[from].exit = Some(exit);
            self.exits.push(from);
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
                exit: None,
                other,
            });
            return Some(self.kept.len() - 1);
        }
        None
    }

    // Whether the other account's way out pays it less after the actor's call, with no
    // argument of that way out able to refuse the lower amount.
    fn lowers(
        &self,
        parent: &Kept,
        now: &World,
        exit: &(usize, Call, Holdings),
        steps: &[Step],
    ) -> Option<Lowered> {
        let (index, call, before) = exit;
        let at = self.entries[*index].at;
        let mut after = now.clone();
        if !after.call(at, call).ended {
            return None;
        }
        let after = after.holdings(OTHER);
        if !gained(&after, before) {
            return None;
        }
        // The amount the way out paid before is what a floor would be set to.
        let of = |h: &Holdings, asset: &U256| h.assets.get(asset).copied().unwrap_or(PURSE);
        let assets = before.assets.keys();
        let rises = assets.map(|a| (of(&parent.other, a), of(before, a)));
        // What the way out paid in ether is what its caller gained and what it sent.
        let paid = before.ether.checked_add(call.value).unwrap_or(before.ether);
        let rises = rises.chain([(parent.other.ether, paid)]);
        let amount = rises
            .filter(|(had, has)| has > had)
            .map(|(had, has)| has - had)
            .max()?;
        let words = call.data.len().saturating_sub(4) / 32;
        let floors = (0..words.min(self.entries[*index].params)).any(|word_at| {
            let mut with = call.clone();
            with.data[4 + 32 * word_at..36 + 32 * word_at].copy_from_slice(&amount.to_be_bytes());
            parent.world.clone().call(at, &with).ended && !now.clone().call(at, &with).ended
        });
        (!floors).then(|| Lowered {
            steps: steps.to_vec(),
            exit: (*index, call.clone()),
            before: before.clone(),
            after,
        })
    }

    // Whether the last call, made in two parts, leaves the actor holding the same and
    // some record it lowered less lowered. What a call takes from a record should round
    // up, and then parts never cost less than the whole.
    fn split(
        &self,
        parent: &Kept,
        whole: &World,
        index: usize,
        call: &Call,
        steps: &[Step],
    ) -> Option<Rounded> {
        let entry = &self.entries[index];
        let words = call.data.len().saturating_sub(4) / 32;
        let amount = |at: &usize| word(&call.data, 4 + 32 * at);
        let sized = |at: &usize| amount(at) >= U256::from_u64(2) && amount(at) < PURSE;
        let free = |at: &usize| !entry.fixed.contains(at) && !entry.addresses.contains(at);
        let word_at = (0..words.min(entry.params)).find(|at| free(at) && sized(at))?;
        let (at, all) = (entry.at, amount(&word_at));
        let with = |part: U256| {
            let mut data = call.data.clone();
            data[4 + 32 * word_at..36 + 32 * word_at].copy_from_slice(&part.to_be_bytes());
            Call {
                data,
                back: None,
                swing: None,
                ..call.clone()
            }
        };
        let held = whole.holdings(ACTOR);
        let before = &parent.world;
        for first in [U256::ONE, all >> 1, all >> 2] {
            let second = all - first;
            let mut parts = before.clone();
            let ended = !first.is_zero()
                && parts.call(at, &with(first)).ended
                && parts.call(at, &with(second)).ended;
            if !ended || parts.holdings(ACTOR) != held {
                continue;
            }
            let lowered = whole.slots(exec::SELF);
            let lowered = lowered
                .iter()
                .filter(|(slot, value)| **value < before.stored(exec::SELF, **slot));
            let mut less_taken = false;
            let mut more_taken = false;
            for (slot, value) in lowered {
                let kept = parts.stored(exec::SELF, *slot);
                less_taken |= kept > *value;
                more_taken |= kept < *value;
            }
            if less_taken && !more_taken {
                return Some(Rounded {
                    steps: steps.to_vec(),
                    word: word_at,
                    whole: all,
                    parts: (first, second),
                });
            }
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

    // Two shapes a random round seldom meets are tried outright for each function the
    // other account can pay into. What a contract pays back is often sized by what was
    // paid, and random sizes seldom meet the pair that matters. For a function that
    // needs a payment: the other account pays, value the contract has no record of arrives, and the actor
    // pays twice at each pair of a few sizes. Every state reached is kept, so that the
    // rounds after it try every way out from there.
    fn opening(&mut self, index: usize) {
        let seeds = &self.entries[index].seeds;
        let paid = |(_, value): &&(Vec<u8>, U256)| !value.is_zero() && *value < PURSE;
        let Some((data, value)) = seeds.iter().find(paid).cloned() else {
            return;
        };
        // A function that also ends without a payment does not size anything by it.
        let needs_payment = !seeds.iter().any(|(_, value)| value.is_zero());
        let pays = |who: U256, value: U256| Call {
            who,
            data: data.clone(),
            value,
            ..Call::default()
        };
        let Some(paid_in) = self.attempt_and(true, 0, index, pays(OTHER, value)) else {
            return;
        };
        if !needs_payment && !self.kept[paid_in].recorded {
            return;
        }
        // The actor pays in while one outside answer reads higher or lower, and then
        // asks each function for all the contract holds.
        for (nth, up) in [(0, true), (0, false), (1, true), (1, false)] {
            let call = Call {
                swing: Some((nth, 0, up)),
                ..pays(ACTOR, value)
            };
            let swung = self.attempt_and(true, paid_in, index, call);
            if let Some(swung) = swung.filter(|at| self.kept[*at].swung.is_some()) {
                self.drain(swung);
            }
        }
        if !needs_payment {
            return;
        }
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

    // Every function is asked once, by the actor, for each amount the contract holds.
    fn drain(&mut self, from: usize) {
        let held = self.kept[from].world.held(exec::SELF);
        for index in 0..self.entries.len() {
            let entry = &self.entries[index];
            let Some((data, _)) = entry.seeds.first().cloned() else {
                continue;
            };
            let words = data.len().saturating_sub(4) / 32;
            let free = |at: &usize| !entry.fixed.contains(at) && !entry.addresses.contains(at);
            let Some(at) = (0..words.min(entry.params)).find(free) else {
                continue;
            };
            for amount in &held {
                let mut data = data.clone();
                data[4 + 32 * at..36 + 32 * at].copy_from_slice(&amount.to_be_bytes());
                let call = Call {
                    who: ACTOR,
                    data,
                    ..Call::default()
                };
                self.attempt(from, index, call);
            }
        }
    }

    // From a state the other account can take out of, every function is called once by
    // the actor with no payment. A random round seldom makes the one quiet call that
    // changes what the way out pays.
    fn probe(&mut self, from: usize) {
        for index in 0..self.entries.len() {
            let seeds: Vec<Vec<u8>> = self.entries[index]
                .seeds
                .iter()
                .map(|(data, _)| data.clone())
                .collect();
            for data in seeds {
                let call = Call {
                    who: ACTOR,
                    data,
                    ..Call::default()
                };
                self.attempt(from, index, call);
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
        let mut solved_up_to = self.kept.len();
        let learnt = self.covered.len() + self.positions.len();
        let (mut reached, mut fresh, mut fresh_at) = (learnt, 0, exec::work());
        let stale = |rounds: usize, fresh: usize, fresh_at: u64| {
            rounds - fresh >= STALE_ROUNDS || exec::work() - fresh_at >= STALE_WORK
        };
        while !exec::spent() && rounds < MAX_ROUNDS && !stale(rounds, fresh, fresh_at) {
            rounds += 1;
            self.round();
            // A caller that paid anything before has not gained, so these start where
            // it has not acted yet.
            while let Some((index, call)) = self.renamed.pop() {
                let fresh = |k: &usize| self.kept[*k].base.is_none();
                let starts: Vec<usize> = (0..self.kept.len()).filter(fresh).collect();
                for from in starts.into_iter().take(MAX_FRESH_STARTS) {
                    self.attempt(from, index, call.clone());
                }
            }
            while let Some(from) = self.exits.pop() {
                self.probe(from);
            }
            let learnt = self.covered.len() + self.positions.len();
            if learnt > reached {
                (reached, fresh, fresh_at) = (learnt, rounds, exec::work());
            }
            // A function with no working input is often waiting for state. When a new
            // state wrote a slot such a function reads, its checks are solved from there.
            for from in solved_up_to..self.kept.len() {
                let who = match self.kept[from].base {
                    Some(_) => ACTOR,
                    None => OTHER,
                };
                let wrote = &self.kept[from].written;
                let waits =
                    |e: &Entry| e.seeds.is_empty() && e.reads.iter().any(|k| wrote.contains(k));
                let waiting: Vec<usize> = (0..self.entries.len())
                    .filter(|i| waits(&self.entries[*i]))
                    .collect();
                for index in waiting {
                    self.help(from, index, who);
                }
            }
            solved_up_to = self.kept.len();
        }
    }
}

fn shown(steps: &[Step]) -> Vec<String> {
    let line = |s: &Step| match s {
        Step::Call(_, call) => {
            format!(
                "{} with value {} from {}",
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

fn report(search: &Search, broken: &Broken, out: &mut Vec<Finding>) {
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
    let source = match (outside, broken.taken) {
        (true, true) => "An asset left the other account during these calls, under the approval that account gave the contract when it paid in.",
        (true, false) => "The contract held nothing at the start and received only what the two accounts paid in, so what the account gained is the other account's payment.",
        (false, _) => "Nothing was paid for that balance, in ether or in any asset.",
    };
    let severity = broken.severity();
    let timing = match severity {
        Severity::Medium => " No call that brought that payment in wrote anything to storage, so the contract keeps no record of whose it is. A contract that only passes value on within one transaction leaves what stays behind open in this way.",
        _ => "",
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
                search.started_from(),
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
            search.started_from(),
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

fn report_less(search: &Search, less: &Less, out: &mut Vec<Finding>) {
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
    let note = match less.own() {
        true => "",
        false => " The asset left under the approval that account gave the contract when it paid in. It went to the contract or to a third account, and a credit for it that no balance function shows cannot be seen from outside.",
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
            search.started_from(),
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

fn report_role(search: &Search, role: &Role, out: &mut Vec<Finding>) {
    let Some((Step::Call(entry, last), earlier)) = role.steps.split_last() else {
        return;
    };
    let function = search.entries[*entry].function;
    let (id, title, severity, now, advice) = match role.taken {
        true => (
            "caller-gives-itself-a-role",
            "An account with no role makes itself the one a check lets through",
            Severity::High,
            "was first given to another account, and after the last call it holds the caller's address, so the caller passes a check it did not pass before",
            "Let only the account the slot already names, or one it has agreed to, change who it names.",
        ),
        false => (
            "caller-clears-a-role",
            "An account with no role removes the one a check lets through",
            Severity::Medium,
            "was first given to another account, and after the last call it holds none, so no account passes that check any more",
            "Let only the account the slot names give the role up.",
        ),
    };
    push(
        out,
        id,
        title,
        severity,
        Confidence::High,
        Some(function),
        None,
        format!(
            "Starting from {}, {} call(s) were made, the last to `{}` by an account with no role, sending no ether and asking no outside contract anything. Every call ended normally. Some function compares its caller with the address in slot {} and lets only that one through. That slot {now}.",
            search.started_from(),
            role.steps.len(),
            function.name,
            role.slot.to_hex(),
        ),
        Vec::new(),
        advice,
    );
    if let Some(finding) = out.last_mut() {
        attach(finding, earlier, last);
    }
}

const TARGET_IDS: [&str; 2] = ["arbitrary-call", "arbitrary-delegatecall"];
// A finding that says the caller picks what is called is judged from the states the
// search reached: the call data is changed and the call either follows it or does not.
// One that follows is shown with the run. One that does not is not there to report.
fn settle_calls(search: &mut Search, c: &Contract, out: &mut Vec<Finding>) -> Vec<String> {
    let mut fixed = Vec::new();
    for (index, finding) in out.iter_mut().enumerate() {
        let selector = finding.id == confirm::SELECTOR_ID;
        if finding.confirmed || !(selector || TARGET_IDS.contains(&finding.id.as_str())) {
            continue;
        }
        let (Some(pc), Some(name)) = (finding.pc, finding.function.as_deref()) else {
            continue;
        };
        let external = |f: &&Function| f.kind == FnKind::External && display_name(f) == name;
        let Some(f) = c.functions.iter().find(external) else {
            continue;
        };
        let site = search
            .explorers
            .of(c.code_of(f))
            .rest_of_block(c.local_pc(f, pc));
        let reached = "from a state that earlier calls left";
        let shown = match selector {
            true => search.tracks(&site, |m| m.first).map(|chosen| {
                chosen.map(|c| {
                    let note = confirm::chosen_note(reached, c.first, c.at, c.then);
                    (c.steps, note)
                })
            }),
            false => search.tracks(&site, |m| Some(m.to)).map(|chosen| {
                chosen.map(|c| {
                    let note = format!(
                        " Confirmed by running it, {reached}: the call goes to {}, and with bytes {} to {} of the call data changed it goes to {}. The caller decides which address is called.",
                        c.first.to_hex(),
                        c.at,
                        c.at + 3,
                        c.then.to_hex(),
                    );
                    (c.steps, note)
                })
            }),
        };
        match shown {
            None => {}
            Some(None) => fixed.push(index),
            Some(Some((steps, note))) => {
                let Some((Step::Call(_, last), earlier)) = steps.split_last() else {
                    continue;
                };
                finding.description.push_str(&note);
                if selector {
                    finding.confidence = Confidence::Medium;
                }
                attach(finding, earlier, last);
            }
        }
    }
    let mut withdrawn = Vec::new();
    for index in fixed.into_iter().rev() {
        let gone = out.remove(index);
        let part = match gone.id == confirm::SELECTOR_ID {
            true => "the function called",
            false => "the address called",
        };
        withdrawn.push(confirm::withdrawn(&gone, part));
    }
    withdrawn.reverse();
    withdrawn
}

fn attach(finding: &mut Finding, earlier: &[Step], last: &Call) {
    finding.setup = shown(earlier);
    finding.confirmed = true;
    finding.witness = Some(hex::encode(&last.data));
    finding.observed = vec![format!("sent by {}", last.who.to_hex())];
}

fn report_lowered(search: &Search, lowered: &Lowered, out: &mut Vec<Finding>) {
    let Some(Step::Call(by, _)) = lowered.steps.last() else {
        return;
    };
    let (index, call) = &lowered.exit;
    let (function, earlier) = (
        search.entries[*index].function,
        search.entries[*by].function,
    );
    let (before, after) = (&lowered.before, &lowered.after);
    let of = |h: &Holdings, asset: &U256| h.assets.get(asset).copied().unwrap_or(PURSE);
    let mut fell = Vec::new();
    if after.ether < before.ether {
        fell.push(format!(
            "{} less ether",
            (before.ether - after.ether).to_hex()
        ));
    }
    for asset in before
        .assets
        .keys()
        .filter(|a| of(after, a) < of(before, a))
    {
        let less = of(before, asset) - of(after, asset);
        fell.push(format!(
            "{} less of the asset at {}",
            less.to_hex(),
            asset.to_hex()
        ));
    }
    if matches!((before.reported, after.reported), (Some(a), Some(b)) if b < a) {
        fell.push("a lower balance in the contract's own ledger".to_string());
    }
    push(
        out,
        "earlier-call-lowers-payout",
        "Another account's call just before lowers what this call pays, and nothing in the call refuses it",
        Severity::Medium,
        Confidence::High,
        Some(function),
        None,
        format!(
            "Starting from {}, after the attached earlier call(s) an account calls `{}` and is paid. When an account holding no role first calls `{}`, which moves no value in or out, the same call to `{}` still ends normally and leaves its caller with {} than without that call, and with no more of anything. No argument word set to the amount paid before made the lower run fail, so the caller cannot set a floor.",
            search.started_from(),
            function.name,
            earlier.name,
            function.name,
            fell.join(" and "),
        ),
        Vec::new(),
        "Take a minimum amount as an argument and fail when the payout is below it.",
    );
    if let Some(finding) = out.last_mut() {
        attach(finding, &lowered.steps, call);
    }
}

fn report_rounded(search: &Search, rounded: &Rounded, out: &mut Vec<Finding>) {
    let Some((Step::Call(entry, last), earlier)) = rounded.steps.split_last() else {
        return;
    };
    let function = search.entries[*entry].function;
    push(
        out,
        "rounding-favours-caller",
        "A division rounds in the caller's favour",
        Severity::Medium,
        Confidence::High,
        Some(function),
        None,
        format!(
            "Starting from {}, after the attached earlier call(s), `{}` was called once with argument word {} set to {}, and from the same state twice with {} and then {}. The caller ends holding the same either way, and a record the single call lowered is lowered less by the two. What a call takes from a record should round up, and then parts never cost less than the whole. Here they do, so asking in small parts keeps the difference each time.",
            search.started_from(),
            function.name,
            rounded.word,
            rounded.whole.to_hex(),
            rounded.parts.0.to_hex(),
            rounded.parts.1.to_hex(),
        ),
        Vec::new(),
        "Round what the contract hands out down and what it takes up.",
    );
    if let Some(finding) = out.last_mut() {
        attach(finding, earlier, last);
    }
}

// One search over sequences of calls. It keeps every sequence that reached code no
// earlier one reached, extends those, and checks after each call whether an account
// with no role now holds more than before its first call, and whether the other
// account holds less than before that call.
// Returns what it tested and withdrew, one line for each finding.
pub fn findings(c: &Contract, out: &mut Vec<Finding>) -> Vec<String> {
    if std::env::var("EVMDEC_NO_CONFIRM").is_ok() || c.info.runtime.is_empty() {
        return Vec::new();
    }
    let mut search = Search::new(c);
    if search.entries.is_empty() {
        return Vec::new();
    }
    search.run();
    let last = |steps: &[Step]| match steps.last() {
        Some(Step::Call(entry, _)) => Some(*entry),
        _ => None,
    };
    let gain_at = search.best.as_ref().and_then(|b| last(&b.steps));
    if let Some(broken) = search.best.take() {
        report(&search, &broken, out);
    }
    // A gain through the same function already says what that function lets happen.
    if let Some(less) = search.less.take().filter(|l| last(&l.steps) != gain_at) {
        report_less(&search, &less, out);
    }
    if let Some(role) = search.role.take() {
        report_role(&search, &role, out);
    }
    let withdrawn = settle_calls(&mut search, c, out);
    if let Some(lowered) = search.lowered.take() {
        report_lowered(&search, &lowered, out);
    }
    if let Some(rounded) = search.rounded.take() {
        report_rounded(&search, &rounded, out);
    }
    withdrawn
}
