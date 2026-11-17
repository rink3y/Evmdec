use crate::budget;
use crate::laws::{self, Breach, Kind};
use crate::model::Facts;
use crate::shape::{Holds, Laid, Node, Role, Shape};
use crate::trace::{
    Answered, Event, Place, Run, Tag, CALLER, CLOCK, DATA, EXT, MATH, OUT, SIZE, STORE, VALUE,
};
use crate::world::{self, Addr, Msg, Source, World, ACTOR, ALLY, OWNER, SUBJECT, USER};
use evmdec::decompile::Contract;
use evmdec::function::{FnKind, Mutability};
use evmdec::opcode as op;
use evmdec::U256;
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::rc::Rc;

pub const UNIT: U256 = U256([1_000_000_000_000_000_000, 0, 0, 0]);
// What an account is taken to hold in a ledger the contract keeps: a thousand units.
const STAKE: U256 = U256([0x35c9_adc5_dea0_0000, 0x36, 0, 0]);

const MAX_ENTRIES: usize = 80;
const MAX_STATES: usize = 96;
const ROUNDS: usize = 5;
const MAX_TRIES: usize = 10;
const MAX_HOOKS: usize = 4;
const ACTOR_DEPTH: usize = 3;
const MAX_OUTSIDE: usize = 3;
const OUTSIDE_ENTRIES: usize = 6;
const SWAYED_A_STATE: usize = 3;
const SWAYED_AN_ENTRY: usize = 3;
const MAX_SENDS: usize = 4;
const MAX_READ: usize = 8;
const UNUSED_SELECTOR: u32 = 0xfeed_c0de;
const TEN_YEARS: u64 = 315_360_000;

#[derive(Clone, Debug)]
pub struct Entry {
    pub function: usize,
    pub selector: Option<u32>,
    pub name: String,
    shape: Shape,
    pub view: bool,
    pub payable: bool,
    pub to: Addr,
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
    // The account with no role holds some of the contract's own ledger, written there or sent by a holder.
    Holds {
        from: Option<Addr>,
    },
    Sent {
        asset: Option<Addr>,
        to: Addr,
        amount: U256,
    },
}

#[derive(Clone)]
pub struct State {
    pub world: World,
    pub steps: Vec<Step>,
    pub acted: usize,
    // What the account with no role has given up of its own recorded claims so far.
    pub spent: U256,
    /* The account got here by making a call that can be made only once by anyone. On a
    contract in use that call has been made, so nothing found from here is reported. */
    pub raced: bool,
    /* An honest call left value in the contract and the contract wrote nothing down
    about it. Nobody has a claim on such value, and a contract that passes value on holds
    none of it between calls. A gain picked up from here is not taken from anyone. */
    pub stray: bool,
    /* The account with no role was handed a holding here. What it then draws on that
    holding is not taken from anyone, so only what happens to others is reported. */
    pub granted: bool,
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
type TryKey = (Addr, Vec<u8>, U256, Option<U256>, Vec<Told>);

// One call to make, with what the world is taken to be when it is made.
#[derive(Clone, Debug)]
struct Try {
    msg: Msg,
    shape: Shape,
    answers: Vec<(Addr, u32, Vec<u8>)>,
    time: Option<U256>,
}

impl Try {
    fn of(from: Addr, to: Addr, shape: Shape, value: U256) -> Try {
        let msg = Msg {
            from,
            to,
            data: shape.encode(),
            value,
            hook: None,
        };
        Try {
            msg,
            shape,
            answers: Vec::new(),
            time: None,
        }
    }

    fn sent(msg: Msg) -> Try {
        Try {
            shape: Shape::raw(&msg.data),
            msg,
            answers: Vec::new(),
            time: None,
        }
    }

    fn reshaped(&self, change: &dyn Fn(&mut Shape) -> bool) -> Option<Try> {
        let mut next = self.clone();
        change(&mut next.shape).then(|| {
            next.msg.data = next.shape.encode();
            next
        })
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
    // Each slot filled as a setting, with the variable it belongs to and what it held.
    settings: Vec<(Place, U256, U256)>,
    raised: std::collections::BTreeMap<U256, std::collections::BTreeSet<U256>>,
    /* What an owner's call tried to pay out of the contract and could not, for the lack
    of it, with the function that tried. */
    owed: HashSet<(usize, Option<Addr>)>,
    pub runs: u64,
    trace: bool,
    edges: HashSet<u32>,
    outside: Vec<Addr>,
    known: Vec<Addr>,
    shapes: HashSet<u64>,
    staked: HashSet<crate::trace::Place>,
    unspendable: HashSet<(crate::trace::Place, usize)>,
    // For each entry, how far its furthest failed call got and what stopped it.
    pub stopped: Vec<Option<(usize, String)>>,
    // For each entry, how far the call went whose call data the entry's shape was taken from.
    reach: Vec<(bool, usize)>,
    // For each entry, a call of the owner's that ended in the starting world.
    good: Vec<Option<Try>>,
    // The set-up calls the starting world has been through.
    setups: Vec<(usize, Try)>,
    on_chain: bool,
    // Set while a call is made in a world that is only being tried. Such a call says
    // nothing of what the contract does in the world the report is about.
    trial: bool,
    // Set while every function of a state is given one short try before any gets a long one.
    shallow: bool,
    // The contracts the chain's state names, and the addresses looked at to find them.
    contracts: Vec<Addr>,
    checked: HashSet<Addr>,
    // Entries from here on are other contracts'. No finding may end in one.
    pub own: usize,
    // A contract behind a proxy is read from the code it delegates to.
    talked: BTreeMap<Addr, (usize, Option<Addr>)>,
    read_out: HashSet<(Addr, U256, bool)>,
    named_out: BTreeMap<Addr, usize>,
    aims: Vec<Addr>,
    room: usize,
    paid: Vec<(usize, usize, Try, laws::Moved)>,
}

fn outside(n: usize) -> Addr {
    world::account(0xa5, n as u64 + 1)
}

fn entries(c: &Contract, to: Addr) -> Vec<Entry> {
    let reached =
        |kind: FnKind| matches!(kind, FnKind::External | FnKind::Fallback | FnKind::Receive);
    let all = c.functions.iter().enumerate();
    let mut out = Vec::new();
    for (function, f) in all.filter(|(_, f)| reached(f.kind)).take(MAX_ENTRIES) {
        let hex = f.selector.as_deref().map(|s| s.trim_start_matches("0x"));
        let selector = hex.and_then(|s| u32::from_str_radix(s, 16).ok());
        let types: Vec<String> = f.params.iter().map(|p| p.ty.clone()).collect();
        let shape = match f.kind {
            FnKind::Receive => Shape::default(),
            FnKind::Fallback => Shape::raw(&UNUSED_SELECTOR.to_be_bytes()),
            _ => Shape::of(selector, &types),
        };
        out.push(Entry {
            function,
            selector,
            name: f.name.clone(),
            shape,
            view: matches!(f.mutability, Mutability::Pure | Mutability::View),
            payable: f.mutability == Mutability::Payable,
            to,
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

fn better(new: &Run, old: &Run) -> bool {
    // A call that runs until the step limit got nowhere, however many steps it took.
    let endless = new.halt == crate::trace::Halt::Steps;
    match (new.ok, old.ok) {
        (true, false) => true,
        (false, true) => false,
        _ => !endless && (new.edges.len(), new.steps) > (old.edges.len(), old.steps),
    }
}

fn low_address(value: U256) -> Addr {
    value & ((U256::ONE << 160) - U256::ONE)
}

fn marked(cell: &crate::trace::Cell) -> (Addr, U256, bool) {
    (cell.account, cell.slot, !cell.keys.is_empty())
}

fn sent(asset: Option<Addr>, to: Addr, amount: U256) -> Msg {
    let from = ACTOR;
    match asset {
        Some(asset) => Msg {
            from,
            to: asset,
            data: world::transfer_call(to, amount),
            ..Msg::default()
        },
        None => Msg {
            from,
            to,
            value: amount,
            ..Msg::default()
        },
    }
}

fn alike(a: &Breach, b: &Breach) -> bool {
    let place = |b: &Breach| b.cell.as_ref().map(crate::trace::Cell::place);
    a.kind == b.kind && a.asset == b.asset && a.victim == b.victim && place(a) == place(b)
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
        Self::starting_from(c, subject, world)
    }

    #[must_use]
    pub fn on_chain(
        c: &'a Contract,
        source: Rc<dyn Source>,
        number: u64,
        time: u64,
    ) -> Explorer<'a> {
        let named = c.address.as_deref().and_then(U256::from_hex_str);
        let subject = named.unwrap_or(SUBJECT);
        let mut world = World::new();
        world.subject = subject;
        world.place(subject, &c.info.runtime);
        world.read_from(source);
        (world.number, world.time) = (U256::from_u64(number), U256::from_u64(time));
        let mut explorer = Self::starting_from(c, subject, world);
        explorer.on_chain = true;
        explorer
    }

    fn starting_from(c: &'a Contract, subject: Addr, world: World) -> Explorer<'a> {
        let entries = entries(c, subject);
        let own = entries.len();
        let start = State {
            world,
            steps: Vec::new(),
            acted: 0,
            spent: U256::ZERO,
            raced: false,
            stray: false,
            granted: false,
        };
        Explorer {
            c,
            subject,
            facts: Facts::new(entries.len()),
            entries,
            states: vec![start],
            found: Vec::new(),
            assumed: Vec::new(),
            settings: Vec::new(),
            raised: crate::model::raised_within_a_call(c),
            owed: HashSet::new(),
            runs: 0,
            trace: std::env::var("EVMDEC_AUDIT_TRACE").is_ok(),
            edges: HashSet::new(),
            outside: Vec::new(),
            known: vec![OWNER, USER, ACTOR, ALLY, subject],
            shapes: HashSet::new(),
            staked: HashSet::new(),
            unspendable: HashSet::new(),
            stopped: Vec::new(),
            reach: Vec::new(),
            good: Vec::new(),
            setups: Vec::new(),
            on_chain: false,
            trial: false,
            shallow: false,
            contracts: Vec::new(),
            checked: HashSet::new(),
            own,
            talked: BTreeMap::new(),
            read_out: HashSet::new(),
            named_out: BTreeMap::new(),
            aims: Vec::new(),
            room: MAX_STATES,
            paid: Vec::new(),
        }
    }

    fn seed(&self, entry: usize, who: Addr, address: Addr, amount: U256, value: U256) -> Try {
        self.fill(
            entry,
            &self.entries[entry].shape,
            who,
            address,
            amount,
            value,
        )
    }

    fn fill(
        &self,
        entry: usize,
        shape: &Shape,
        who: Addr,
        address: Addr,
        amount: U256,
        value: U256,
    ) -> Try {
        let mut shape = shape.clone();
        shape.each_word(&mut |kind, held| {
            *held = match kind {
                Holds::Callee => outside(0),
                Holds::Address => address,
                Holds::Flag => U256::ONE,
                Holds::Small => U256::ZERO,
                Holds::Amount => amount,
                Holds::Other => return,
            };
        });
        Try::of(who, self.entries[entry].to, shape, value)
    }

    fn honest(&self, entry: usize, who: Addr) -> Vec<Try> {
        let plain = self.seed(entry, who, who, UNIT, U256::ZERO);
        // A function that takes ether is first used the way it is meant to be, with some.
        let mut seeds = match self.entries[entry].payable {
            true => vec![self.seed(entry, who, who, UNIT, UNIT), plain],
            false => vec![plain],
        };
        // What an owner registers under an address is as often a contract as itself. On the
        // chain what it registered is there to be read, and a made-up contract in its place
        // undoes the set-up the run is meant to start from.
        let kinds = self.entries[entry].shape.kinds();
        let named = kinds
            .iter()
            .any(|k| matches!(k, Holds::Address | Holds::Callee));
        if who == OWNER && !self.on_chain && named {
            seeds.push(self.seed(entry, who, outside(0), UNIT, U256::ZERO));
        }
        seeds.extend(self.bare_payment(entry, who));
        seeds.extend(self.naming_contracts(entry, who));
        seeds
    }

    /* Old code has one function for a call it does not know and for ether sent with no
    message at all. The second is how most ether reaches a contract. */
    fn bare_payment(&self, entry: usize, who: Addr) -> Option<Try> {
        let e = &self.entries[entry];
        let catch_all = e.selector.is_none() && e.shape != Shape::default();
        catch_all.then(|| Try::of(who, e.to, Shape::default(), UNIT))
    }

    // What an account with no role tries: itself everywhere, then another account in each place.
    fn hostile(&self, entry: usize) -> Vec<Try> {
        let e = &self.entries[entry];
        let mut seeds = vec![self.seed(entry, ACTOR, ACTOR, UNIT, U256::ZERO)];
        if e.payable {
            seeds.insert(0, self.seed(entry, ACTOR, ACTOR, UNIT, UNIT));
        }
        seeds.extend(self.bare_payment(entry, ACTOR));
        seeds.extend(self.naming_contracts(entry, ACTOR));
        let kinds = e.shape.kinds();
        let addresses: Vec<usize> = (0..kinds.len())
            .filter(|i| matches!(kinds[*i], Holds::Address | Holds::Callee))
            .collect();
        for at in addresses.iter().take(3) {
            for other in [USER, OWNER] {
                let plain = self.seed(entry, ACTOR, ACTOR, UNIT, U256::ZERO);
                seeds.extend(plain.reshaped(&|shape| shape.put(*at, other)));
            }
        }
        if !addresses.is_empty() {
            seeds.push(self.seed(entry, ACTOR, ALLY, UNIT, U256::ZERO));
        }
        // A contract the code is told to call may be the account itself, or one it wrote.
        for own in [ACTOR, ALLY] {
            let plain = self.seed(entry, ACTOR, ACTOR, UNIT, U256::ZERO);
            let called = kinds.contains(&Holds::Callee);
            seeds.extend(plain.reshaped(&|shape| {
                shape.each_word(&mut |holds, held| {
                    if *holds == Holds::Callee {
                        *held = own;
                    }
                });
                called
            }));
        }
        if kinds.contains(&Holds::Amount) {
            seeds.push(self.seed(entry, ACTOR, ACTOR, U256::MAX, U256::ZERO));
            seeds.push(self.seed(entry, ACTOR, ACTOR, U256::ZERO, U256::ZERO));
        }
        // Two items of half the range each add up to nothing where a sum is not checked.
        if let Some(pair) = e.shape.paired() {
            let half = U256::ONE << 255;
            seeds.push(self.fill(entry, &pair, ACTOR, ACTOR, half, U256::ZERO));
            seeds.push(self.fill(entry, &pair, ACTOR, ACTOR, UNIT, U256::ZERO));
        }
        seeds
    }

    fn set_for(world: &mut World, t: &Try) {
        for (to, selector, answer) in &t.answers {
            world.answer_with(*to, *selector, answer.clone());
        }
        if let Some(time) = t.time.filter(|time| *time > world.time) {
            let blocks = (time - world.time).low_u64() / 12;
            world.number = world.number + U256::from_u64(blocks);
            world.time = time;
        }
    }

    fn attempt_in(&mut self, mut world: World, entry: usize, t: &Try) -> (World, Run) {
        Self::set_for(&mut world, t);
        let run = world.send(&t.msg);
        self.runs += 1;
        if t.msg.from == OWNER {
            let subject = self.subject;
            let lacked = run.calls.iter().filter(|c| c.from == subject && !c.ok);
            let lacked = lacked.filter_map(|c| match (c.value.is_zero(), c.by) {
                (false, _) if c.kind == op::CALL => Some(None),
                (true, Answered::Books) => Some(Some(c.to)),
                _ => None,
            });
            let lacked: Vec<Option<Addr>> = lacked.collect();
            self.owed
                .extend(lacked.into_iter().map(|kind| (entry, kind)));
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
                for call in &run.calls {
                    let (input, output) = (&call.input, &call.output);
                    eprintln!(
                        "    call to {:.8} in {} out {} by {:?} args {:?}",
                        call.to.to_hex(),
                        evmdec::hex::encode(&input[..input.len().min(100)]),
                        evmdec::hex::encode(&output[..output.len().min(32)]),
                        call.by,
                        call.arg_tags.iter().map(|t| t.bits).collect::<Vec<_>>()
                    );
                }
            }
        }
        if self.trial {
            return (world, run);
        }
        if entry < self.own {
            self.facts
                .observe(entry, &t.msg, &run, self.subject, &self.known);
            if self.on_chain {
                self.note_outside(&run);
            }
        } else if run.ok
            && run
                .stores()
                .any(|(c, ..)| self.read_out.contains(&marked(c)))
        {
            self.facts.entries[entry].ended.insert(t.msg.from);
        }
        self.learn(entry, t, &run);
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

    /* What a run shows of a word of the call data. One the contract calls is the address
    of a contract, one it pays is an address, and what it pays is an amount. */
    fn learn(&mut self, entry: usize, t: &Try, run: &Run) {
        let mut shown = Vec::new();
        for call in &run.calls {
            let holds = match call.input.is_empty() {
                true => Holds::Address,
                false => Holds::Callee,
            };
            shown.push((call.to_tag, call.to, holds));
            shown.push((call.value_tag, call.value, Holds::Amount));
            let named = world::accounts_named(&call.input);
            for (at, tag) in call.arg_tags.iter().enumerate() {
                let seen = call.input.get(4 + 32 * at..36 + 32 * at);
                let holds = match named.contains(&at) {
                    true => Holds::Address,
                    false => Holds::Amount,
                };
                if let (Answered::Books, Some(seen)) = (call.by, seen) {
                    shown.push((*tag, U256::from_be_bytes(seen), holds));
                }
            }
        }
        for event in &run.events {
            if let Event::Pay {
                to,
                amount,
                to_tag,
                amount_tag,
                ..
            } = event
            {
                shown.push((*to_tag, *to, Holds::Address));
                shown.push((*amount_tag, *amount, Holds::Amount));
            }
        }
        shown.retain(|(tag, ..)| tag.has(DATA));
        if shown.is_empty() {
            return;
        }
        let laid = t.shape.layout();
        for (tag, seen, holds) in shown {
            // An amount worked out from several words is worked out from amounts.
            let spots = match holds {
                Holds::Amount => laid.behind(tag),
                _ => laid.about(tag, seen).into_iter().collect(),
            };
            for spot in spots.into_iter().filter(|s| s.role == Role::Value) {
                match (self.entries[entry].shape.node_mut(&spot.path), holds) {
                    (Some(Node::Word(kind, _)), Holds::Callee) => *kind = holds,
                    (Some(Node::Word(kind @ Holds::Other, _)), _) => *kind = holds,
                    _ => {}
                }
            }
        }
    }

    fn attempt(&mut self, state: usize, entry: usize, t: &Try) -> (World, Run) {
        let world = self.states[state].world.clone();
        self.attempt_in(world, entry, t)
    }

    /* The contract passes on a call for its caller: the address called and the bytes
    sent both come from the call data. What such a call can do is what the contract
    itself may do, so it is tried with the two messages that move an asset. */
    fn passed_on(t: &Try, run: &Run, laid: &Laid) -> Vec<Try> {
        let mut out = Vec::new();
        for call in &run.calls {
            let passed_on =
                call.kind == op::CALL && call.to_tag.has(DATA) && call.input_from.has(DATA);
            let target = laid.about(call.to_tag, call.to);
            let target = target.filter(|s| s.role == Role::Value);
            let sent = call.input_from.word().filter(|w| *w >= 1);
            let length = sent.and_then(|w| laid.spot_at(w - 1));
            let length = length.filter(|s| s.role == Role::Length);
            let (true, Some(target), Some(length)) = (passed_on, target, length) else {
                continue;
            };
            // A contract that measures what its caller received has to see it arrive there.
            for to in [ALLY, t.msg.from] {
                let moves = [
                    world::transfer_from_call(USER, to, UNIT),
                    world::transfer_call(to, UNIT),
                ];
                // An asset is told to move with no ether sent along.
                let value = laid.about(call.value_tag, call.value);
                for payload in moves {
                    out.extend(t.reshaped(&|shape| {
                        value.is_none_or(|spot| shape.set(spot, U256::ZERO))
                            && shape.set(target, outside(0))
                            && shape.put_bytes(&length.path, &payload)
                    }));
                }
            }
        }
        out
    }

    /* What to change so that the comparison a failed run stopped at comes out the
    other way: a part of the call data, the value sent, the length of the call data
    or of an outside answer, or the time. */
    #[allow(clippy::too_many_lines)]
    fn mutations(&self, t: &Try, run: &Run, now: U256, tests: usize) -> Vec<Try> {
        let laid = t.shape.layout();
        let mut out: Vec<Try> = Vec::new();
        let mut seen: HashSet<TryKey> = HashSet::new();
        let mut push = |out: &mut Vec<Try>, next: Try| {
            let key = (
                next.msg.from,
                next.msg.data.clone(),
                next.msg.value,
                next.time,
                next.answers.clone(),
            );
            let differs = next.msg.from != t.msg.from
                || next.msg.data != t.msg.data
                || next.msg.value != t.msg.value
                || next.time != t.time
                || next.answers != t.answers;
            if differs && out.len() < MAX_TRIES.max(tests) && seen.insert(key) {
                out.push(next);
            }
        };
        // Only the account with no role sends what a contract holds or may take to itself.
        if Facts::same_party(t.msg.from, ACTOR) {
            out.extend(Self::passed_on(t, run, &laid).into_iter().take(MAX_TRIES));
        }
        for call in &run.calls {
            let target = laid.about(call.to_tag, call.to);
            let target = target.filter(|s| s.role == Role::Value);
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
            if let Some(target) = target.filter(|_| unanswered) {
                let next = t.reshaped(&|shape| shape.set(target, outside(0)));
                next.into_iter().for_each(|next| push(&mut out, next));
            }
        }
        /* A test of whether an address has code, failed. Whatever named the address is
        made to name a contract: one that keeps honest books, or one the account wrote. */
        let hostile = Facts::same_party(t.msg.from, ACTOR);
        let last = run.events.iter().rev().filter_map(|ev| match ev {
            Event::Branch { tag, .. } => Some(*tag),
            _ => None,
        });
        for tag in last.take(3).filter(|tag| tag.has(EXT)) {
            let contracts = [outside(0), ALLY];
            for contract in contracts.into_iter().take(1 + usize::from(hostile)) {
                if let Some(spot) = laid.about(tag, U256::MAX) {
                    let next = t.reshaped(&|shape| shape.set(spot, contract));
                    next.into_iter().for_each(|next| push(&mut out, next));
                }
                let source = tag.call().filter(|_| tag.has(OUT));
                let source = source.and_then(|k| run.calls.get(k));
                let source = source.filter(|s| matches!(s.by, Answered::Blank | Answered::Taken));
                // What a contract answers is the account's to write only where the contract is its own.
                let own = |s: &&crate::trace::CallOut| Facts::same_party(s.to, ACTOR);
                let source = source.filter(|s| contract != ALLY || own(s));
                if let Some((source, selector)) =
                    source.and_then(|s| Some((s, world::selector(&s.input)?)))
                {
                    let mut next = t.clone();
                    next.answers
                        .retain(|(to, s, _)| !(*to == source.to && *s == selector));
                    next.answers
                        .push((source.to, selector, contract.to_be_bytes().to_vec()));
                    push(&mut out, next);
                }
            }
            // The caller has to be a contract. Where it named itself it names its contract.
            let spot = laid.about(tag, U256::MAX);
            let own = tag.has(CALLER) || spot.is_some_and(|spot| laid.held(spot) == ACTOR);
            if own && t.msg.from == ACTOR {
                let renamed = t.reshaped(&|shape| {
                    shape.each_word(&mut |_, held| {
                        if *held == ACTOR {
                            *held = ALLY;
                        }
                    });
                    true
                });
                if let Some(mut next) = renamed {
                    next.msg.from = ALLY;
                    push(&mut out, next);
                }
            }
        }
        /* A length tested after an answer came back is that answer's, also where the
        place it was copied to was worked out from an earlier answer's length. */
        let mut returned = None;
        let mut cmps: Vec<(u8, U256, U256, Tag, Tag, Option<usize>)> = Vec::new();
        for ev in &run.events {
            match ev {
                Event::Returned(call) => returned = Some(*call),
                Event::Cmp {
                    op: o,
                    a,
                    b,
                    ta,
                    tb,
                    ..
                } => cmps.push((*o, *a, *b, *ta, *tb, returned)),
                _ => {}
            }
        }
        for (nth, (o, a, b, ta, tb, returned)) in cmps.into_iter().rev().take(tests).enumerate() {
            for (tag, was, other) in [(ta, a, b), (tb, b, a)] {
                let near = [
                    other,
                    other.wrapping_add(U256::ONE),
                    other.wrapping_sub(U256::ONE),
                ];
                let values: &[U256] = match o {
                    op::EQ => &near[..1],
                    _ => &near,
                };
                if let Some(spot) = laid.about(tag, was) {
                    let mut wanted = values.to_vec();
                    // A word worked on before the test lacks what the test lacks.
                    if laid.held(spot) != was {
                        wanted.insert(0, laid.held(spot).wrapping_add(other.wrapping_sub(was)));
                    }
                    for value in wanted {
                        let next = t.reshaped(&|shape| shape.set(spot, value));
                        next.into_iter().for_each(|next| push(&mut out, next));
                    }
                }
                // An outside answer the code compares with something is tried as that thing.
                // Only the owner is whoever an outside contract names when asked who may act.
                let names_caller = values.contains(&t.msg.from) && t.msg.from != OWNER;
                let asked = tag
                    .call()
                    .filter(|_| tag.has(OUT) && !tag.has(DATA) && !names_caller);
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
                    let latest = returned.filter(|_| tag.of_several_calls());
                    match tag.call().or(latest).and_then(|k| run.calls.get(k)) {
                        None => {
                            for len in [len, len + 4] {
                                let lacks = len.saturating_sub(laid.data.len());
                                let next = t.reshaped(&|shape| {
                                    shape.spare.resize(shape.spare.len() + lacks, 0);
                                    lacks > 0
                                });
                                next.into_iter().for_each(|next| push(&mut out, next));
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
                /* A time measured from a stored one is short by what the test lacks. The
                code may count it in a larger unit than seconds. Only the test the run
                stopped at is waited out, or the waits crowd out every other repair. */
                let lacks = Some(other.wrapping_sub(was)).filter(|d| other > was && d.bits() <= 32);
                let measured = nth == 0 && tag.has(CLOCK) && tag.has(MATH);
                if let (true, Some(lacks)) = (measured, lacks) {
                    for unit in [1, 3_600, 86_400, 604_800] {
                        let wait = (lacks.low_u64() + 1).saturating_mul(unit);
                        if !tag.has(DATA) && wait < TEN_YEARS {
                            let mut next = t.clone();
                            next.time = Some(now.wrapping_add(U256::from_u64(wait)));
                            push(&mut out, next);
                        }
                    }
                }
            }
        }
        out
    }

    // The input, and the world it leaves, under which a call to the entry ends.
    fn solve(&mut self, state: usize, entry: usize, seed: Try) -> (Try, World, Run) {
        let (world, run) = self.attempt(state, entry, &seed);
        let from = seed.shape.frame();
        let plain = from == self.entries[entry].shape.frame();
        if self.reach.len() < self.entries.len() {
            self.reach.resize(self.entries.len(), (false, 0));
        }
        if plain {
            self.reach[entry] = self.reach[entry].max((run.ok, run.edges.len()));
        }
        let mut best = (seed, world, run);
        /* A call that ends because a list was emptied skips what the list is there for.
        It is held back while a repair that keeps the list gets further, and is the
        answer only if none of those ends. */
        let mut hollow: Option<(Try, World, Run)> = None;
        let rounds = match self.shallow {
            true => 1,
            false => ROUNDS,
        };
        for _ in 0..rounds {
            if best.2.ok || budget::spent() {
                break;
            }
            let now = self.states[state].world.time;
            let tries = self.mutations(&best.0, &best.2, now, 12);
            let emptied = best.0.shape.hollow();
            let mut improved = false;
            for t in tries {
                if budget::spent() {
                    break;
                }
                let (world, run) = self.attempt(state, entry, &t);
                if run.ok && t.shape.hollow() > emptied {
                    hollow.get_or_insert((t, world, run));
                } else if better(&run, &best.2) {
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
        if let Some(ended) = hollow.filter(|_| !best.2.ok) {
            best = ended;
        }
        /* A call that got further than any before it with more in its call data than
        the entry's own shape has is what every later call starts from. What the account
        with no role sends is no model for anyone else. */
        let reach = (best.2.ok, best.2.edges.len());
        let plain = plain && !Facts::same_party(best.0.msg.from, ACTOR);
        let grown = best.0.shape.hollow() <= self.entries[entry].shape.hollow();
        if plain && grown && best.0.shape.frame() != from && reach > self.reach[entry] {
            self.reach[entry] = reach;
            self.entries[entry].shape = best.0.shape.clone();
            self.learn(entry, &best.0, &best.2);
        }
        best
    }

    /* A call led somewhere new when it ran code no call ran before, or left the
    contract with a set of filled cells no kept state has. How much a cell holds is
    not part of that, or every amount would be a state of its own. */
    fn novel(&mut self, run: &Run, world: &World) -> bool {
        let before = self.edges.len();
        self.edges.extend(run.edges.iter().copied());
        let filled = world
            .slots(self.subject)
            .into_iter()
            .filter(|(_, v)| !v.is_zero());
        let mut shape = self.subject.low_u64() ^ u64::from(!world.ether_of(self.subject).is_zero());
        for (slot, _) in filled {
            shape = shape.rotate_left(7) ^ slot.low_u64() ^ slot.0[3];
        }
        let reshaped = self.shapes.insert(shape);
        self.edges.len() > before || reshaped
    }

    fn called(now: U256, entry: usize, t: &Try) -> Vec<Step> {
        let mut steps = Vec::new();
        if let Some(until) = t.time.filter(|time| *time > now) {
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
        steps
    }

    fn keep(&mut self, from: usize, entry: usize, t: &Try, world: World, actor: bool) -> usize {
        let parent = &self.states[from];
        let mut steps = parent.steps.clone();
        steps.extend(Self::called(parent.world.time, entry, t));
        let (spent, raced, stray) = (parent.spent, parent.raced, parent.stray);
        let granted = parent.granted;
        self.states.push(State {
            world,
            steps,
            acted: parent.acted + usize::from(actor),
            spent,
            raced,
            stray,
            granted,
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
                    let plain = self.seed(entry, who, who, UNIT, U256::ZERO);
                    let (_, run) = self.attempt(0, entry, &plain);
                    changed |= self.assume_targets(&run);
                    let staked = self.assume_stake(&plain, &run, entry, who);
                    /* A call with a plain amount comes first. The search would get the
                    same function to end by asking for nothing, and a total that was
                    never set would go unseen. */
                    let total = who == OWNER && !staked && !run.ok;
                    changed |= staked || (total && self.assume_from(&plain, &run, entry, true));
                }
                for seed in self.honest(entry, OWNER) {
                    if budget::spent() {
                        return;
                    }
                    let (best, _, run) = self.solve(0, entry, seed);
                    changed |= self.assume_targets(&run);
                    changed |= self.assume_owner(&best, &run, entry);
                    if run.ok {
                        // Remembered only if it can be made again. A call that works once says
                        // nothing about whether what follows it shut the contract.
                        let after = {
                            let mut world = self.states[0].world.clone();
                            world.send(&best.msg);
                            world
                        };
                        let (_, again) = self.attempt_in(after, entry, &best);
                        if again.ok {
                            self.good[entry] = Some(best);
                        }
                        break;
                    }
                    refused.push((entry, best, run));
                }
            }
            // Set-up comes before any setting is taken, so that no setting is taken for the lack of it.
            let mut set_up = false;
            while self.setups.len() < 8 && self.set_up() {
                set_up = true;
            }
            changed |= set_up;
            for (entry, t, run) in refused {
                if self.good[entry].is_none() && !set_up {
                    changed |= self.assume_from(&t, &run, entry, false);
                }
            }
            /* A setting only the constructor wrote can stop a user where it does not
            stop the owner: a sale that is open, a limit on what one call may bring. The
            user's plain call, with ether where the function takes it, is asked too. */
            for entry in 0..self.entries.len() {
                if set_up || self.entries[entry].view || budget::spent() {
                    continue;
                }
                let t = self.honest(entry, USER).remove(0);
                let (_, run) = self.attempt(0, entry, &t);
                if !run.ok {
                    changed |= self.assume_from(&t, &run, entry, false);
                }
            }
            if !changed {
                break;
            }
        }
    }

    /* A world read from the chain is set up already. What is left to learn is who the
    people are in it: the account the code compares its caller with, and what the three
    hold of the assets the calls move. A role kept under the caller's own address
    cannot be read off the chain without knowing who holds it, so that is still taken. */
    fn settle_on_chain(&mut self) {
        let subject = self.subject;
        if self.states[0].world.endow(subject, STAKE) {
            self.assumed.push(
                "the owner and the user each hold a thousand units in the contract's own ledger, written into the cells it answers balances from".to_string(),
            );
        }
        for _ in 0..4 {
            let mut changed = false;
            self.good = vec![None; self.entries.len()];
            let mut refused: Vec<(usize, Try, Run)> = Vec::new();
            let mut named: Vec<(Place, U256, Addr)> = Vec::new();
            for entry in 0..self.entries.len() {
                for who in [OWNER, USER, ACTOR] {
                    let plain = self.seed(entry, who, who, UNIT, U256::ZERO);
                    let (_, run) = self.attempt(0, entry, &plain);
                    named.extend(self.compared_with_caller(&run));
                    self.note_contracts(&run);
                }
                for seed in self.honest(entry, OWNER) {
                    if budget::spent() {
                        return;
                    }
                    let (best, world, run) = self.solve(0, entry, seed);
                    named.extend(self.compared_with_caller(&run));
                    if run.ok {
                        let (_, again) = self.attempt_in(world, entry, &best);
                        if again.ok {
                            self.good[entry] = Some(best);
                        }
                        break;
                    }
                    refused.push((entry, best, run));
                }
            }
            changed |= self.name_owner(named);
            for asset in self.states[0].world.met() {
                if !self.contracts.contains(&asset) {
                    self.contracts.insert(0, asset);
                }
                let endowed = self.states[0].world.endow(asset, world::PURSE);
                let held = match endowed {
                    true => "the owner, the user and the account with no role each hold a purse of the asset at {}, written into the cells it keeps its books in, and let the contract draw on it",
                    false => "nobody here holds any of the asset at {}, since it does not answer what an account holds from a cell of its own",
                };
                self.assumed.push(held.replace("{}", &asset.to_hex()));
                changed |= endowed;
            }
            for (entry, t, run) in refused {
                if self.good[entry].is_none() {
                    changed |= self.assume_from(&t, &run, entry, false);
                }
            }
            if !changed {
                break;
            }
        }
    }

    fn compared_with_caller(&self, run: &Run) -> Vec<(Place, U256, Addr)> {
        let mut named = Vec::new();
        for event in &run.events {
            let (a, b, ta, tb) = match event {
                Event::Cmp {
                    op: op::EQ,
                    a,
                    b,
                    ta,
                    tb,
                    ..
                }
                | Event::Differs { a, b, ta, tb, .. } => (a, b, ta, tb),
                _ => continue,
            };
            for (caller, other, holder) in [(ta, tb, b), (tb, ta, a)] {
                let stored = caller.only(CALLER) && other.has(STORE) && !other.has(DATA);
                let cell = run.cell_of(*other).filter(|c| c.account == self.subject);
                let somebody =
                    !holder.is_zero() && holder.bits() <= 160 && !self.known.contains(holder);
                if let (true, true, Some(cell)) = (stored, somebody, cell) {
                    if cell.keys.iter().all(|k| k.tag.is_none()) {
                        named.push((cell.place(), cell.slot, *holder));
                    }
                }
            }
        }
        named
    }

    /* On the chain the cells the code compares its caller with name somebody already.
    The owner here takes that account's place in each of them, so that what it may do
    is tried. A cell the code also calls names a contract the calls are made to. A cell
    whose account is shut out of what everyone else may call, as the keeper of a proxy
    is, names no owner of the contract behind it. Both are left as they are. */
    fn name_owner(&mut self, mut named: Vec<(Place, U256, Addr)>) -> bool {
        let subject = self.subject;
        let mask = (U256::ONE << 160) - U256::ONE;
        let mut changed = false;
        named.sort();
        named.dedup();
        for (place, slot, holder) in named {
            let called = self.facts.places.get(&place).is_some_and(|p| p.target)
                || self.c.call_target_slots.contains(&slot.to_hex_padded(32));
            let held = self.states[0].world.stored(subject, slot);
            // The address may sit above other fields packed into the same slot.
            let at = (0..12u32)
                .map(|bytes| 8 * bytes)
                .find(|shift| (held >> *shift) & mask == holder);
            let Some(shift) = at.filter(|_| !called) else {
                continue;
            };
            let mut world = self.states[0].world.clone();
            world.seed(subject, slot, (held & !(mask << shift)) | (OWNER << shift));
            if self.breaks_others(&world, usize::MAX) {
                continue;
            }
            self.states[0].world = world;
            self.assumed.push(format!(
                "the owner stands for the account at {}, which slot {} names and the code compares the caller with",
                holder.to_hex(),
                slot.to_hex()
            ));
            changed = true;
        }
        changed
    }

    /* On the chain the addresses a call is given are mostly contracts the contract
    already knows: the assets it moves and whatever its own storage names. A call that
    names a made-up one is refused before it does anything. */
    fn note_contracts(&mut self, run: &Run) {
        for event in &run.events {
            let Event::Load { cell, value } = event else {
                continue;
            };
            let named = low_address(*value);
            let fresh = named.bits() > 96 && self.checked.len() < 24;
            if run.cells[*cell].account != self.subject || !fresh || !self.checked.insert(named) {
                continue;
            }
            if !self.known.contains(&named) && self.states[0].world.runs_code(named) {
                self.contracts.push(named);
            }
        }
    }

    fn naming_contracts(&self, entry: usize, who: Addr) -> Vec<Try> {
        let kinds = self.entries[entry].shape.kinds();
        let places: Vec<usize> = (0..kinds.len())
            .filter(|i| matches!(kinds[*i], Holds::Address | Holds::Callee))
            .collect();
        let known = self.contracts.len().min(3);
        let ways = match (places.len(), known) {
            (0, _) | (_, 0) => 0,
            (_, 1) => 1,
            _ => 2,
        };
        let seeds = (0..ways).filter_map(|way| {
            let plain = self.seed(entry, who, who, UNIT, U256::ZERO);
            plain.reshaped(&|shape| {
                let named = places.iter().enumerate();
                named.fold(true, |all, (k, at)| {
                    shape.put(*at, self.contracts[(way + k) % known]) && all
                })
            })
        });
        seeds.collect()
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
                let (t, world, run) = self.solve(0, entry, seed);
                let subject = self.subject;
                let fills = run.stores().any(|(c, old, new, _, _)| {
                    c.account == subject && old.is_zero() && !new.is_zero()
                });
                if !run.ok || !fills {
                    continue;
                }
                let (_, again) = self.attempt_in(world.clone(), entry, &t);
                // A call that can be made once and shuts what worked before it closes the
                // contract down. Set-up opens it.
                if again.ok || self.breaks_others(&world, entry) {
                    continue;
                }
                self.good[entry] = None;
                self.novel(&run, &world);
                self.states[0].world = world;
                self.setups.push((entry, t.clone()));
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
        let called = run.calls.iter().map(|call| {
            // A person does not answer a call. A cell the set-up filled with the owner's address
            // and that the code then calls is the address of a contract.
            let nobody = call.to.is_zero() || (call.to == OWNER && !call.input.is_empty());
            (call.to_tag, nobody.then_some(call.to))
        });
        /* Newer code asks whether an address has code before it calls it, and stops
        there when it has none. No call is made, and the test says the same thing. */
        let sized = run.events.iter().filter_map(|e| match e {
            Event::Branch { tag, .. } if tag.has(EXT) && !run.ok => Some((*tag, None)),
            _ => None,
        });
        let asked: Vec<(Tag, Option<Addr>)> = called.chain(sized).collect();
        for (tag, to) in asked {
            let from_store = tag.has(STORE) && !tag.has(DATA | MATH);
            let cell = run.cell_of(tag).filter(|c| c.account == self.subject);
            let (true, Some(cell)) = (from_store, cell) else {
                continue;
            };
            let held = self.states[0].world.stored(self.subject, cell.slot);
            let named = low_address(held);
            let nobody = named.is_zero() || named == OWNER;
            if to.map_or(!nobody, |to| named != to) {
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
            let (pc, a, b, ta, tb) = match event {
                Event::Cmp {
                    pc,
                    op: op::EQ,
                    a,
                    b,
                    ta,
                    tb,
                }
                | Event::Differs { pc, a, b, ta, tb } => (pc, a, b, ta, tb),
                _ => continue,
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
                    matches!(e, Event::Cmp { pc, op: op::EQ, a, b, .. } | Event::Differs { pc, a, b, .. } if *pc == at && a == b && *a == OWNER)
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
    fn assume_from(&mut self, t: &Try, run: &Run, entry: usize, totals: bool) -> bool {
        let subject = self.subject;
        let base = &self.states[0].world;
        let mut options: Vec<(U256, U256, String)> = Vec::new();
        let mut at: HashMap<U256, Place> = HashMap::new();
        let mut roles: Vec<U256> = Vec::new();
        let tests = run.events.iter().rev().filter_map(|e| match e {
            Event::Branch { tag, .. } if tag.has(STORE) && !tag.has(VALUE) => Some(*tag),
            _ => None,
        });
        let tests = tests.filter(|tag| tag.has(DATA) || !totals);
        for tag in tests.take(4) {
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
                at.insert(cell.slot, cell.place());
                let by_caller = cell
                    .keys
                    .iter()
                    .any(|k| k.tag.only(CALLER) && k.value == OWNER);
                if by_caller && held.is_zero() && !tag.has(MATH) {
                    let why = format!(
                        "the owner holds the role kept at slot {}, since the code tests the caller's entry there",
                        cell.root.to_hex()
                    );
                    roles.push(cell.slot);
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
                /* A plain slot that reads as nothing and is tested against an amount in the
                call data is a total. The accounts were given their stakes and the total
                has to cover them. */
                let total = tag.has(DATA);
                let mut values: Vec<U256> = compared
                    .flat_map(|v| [v, v.wrapping_add(U256::ONE), v.wrapping_sub(U256::ONE)])
                    .take(if total { 0 } else { 3 })
                    .collect();
                // The least that lets the call go on is taken. A total has to cover the stakes.
                if held.is_zero() && !total {
                    values.extend([U256::ONE, UNIT]);
                }
                if held.is_zero() {
                    values.push(STAKE + STAKE + STAKE);
                }
                let why = format!(
                    "slot {} is set, since the owner's call needs it",
                    cell.slot.to_hex()
                );
                options.extend(values.into_iter().map(|v| (cell.slot, v, why.clone())));
            }
        }
        // The settings a contract read from the chain needs are the ones it has.
        options.retain(|(slot, _, _)| !self.on_chain || roles.contains(slot));
        /* Each value is tried and the one that takes the call furthest is kept. Of two
        that go as far, the smaller is the lesser thing to take for granted. */
        let mut tried: Vec<(bool, usize, U256, U256, String)> = Vec::new();
        for (slot, value, why) in options.into_iter().take(12) {
            if budget::spent() {
                return false;
            }
            let mut world = self.states[0].world.clone();
            let lowered = self
                .raised
                .get(&slot)
                .is_none_or(|rests| rests.contains(&value));
            /* A slot with entries under it holds how many there are. A made-up count
            promises entries that are not there, and every loop over them runs dry. */
            let counts = self
                .facts
                .places
                .keys()
                .any(|p| p.root == slot && p.depth > 0);
            if world.stored(subject, slot) == value || !lowered || counts {
                continue;
            }
            world.seed(subject, slot, value);
            self.trial = true;
            let (_, next) = self.attempt_in(world, entry, t);
            self.trial = false;
            // The caller's own entry is as often a balance as a role. Only a role lets the call end.
            let enough = next.ok || !roles.contains(&slot);
            if enough && better(&next, run) {
                tried.push((next.ok, next.edges.len(), slot, value, why));
            }
        }
        tried.sort_by(|a, b| (b.0, b.1).cmp(&(a.0, a.1)).then(a.3.cmp(&b.3)));
        for (_, _, slot, value, why) in tried {
            let mut world = self.states[0].world.clone();
            world.seed(subject, slot, value);
            if self.breaks_others(&world, entry) {
                continue;
            }
            let held = self.states[0].world.stored(subject, slot);
            self.states[0].world.seed(subject, slot, value);
            self.assumed.push(why);
            self.settings
                .extend(at.get(&slot).map(|place| (*place, slot, held)));
            return true;
        }
        false
    }

    // A setting one call needs must not shut the calls that worked without it.
    fn breaks_others(&mut self, world: &World, but: usize) -> bool {
        let outer = std::mem::replace(&mut self.trial, true);
        let breaks = self.shuts(world, but);
        self.trial = outer;
        breaks
    }

    fn shuts(&mut self, world: &World, but: usize) -> bool {
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
        // Nor may it open again a set-up that can be made only once.
        for (entry, t) in self.setups.clone() {
            let (_, run) = self.attempt_in(world.clone(), entry, &t);
            if run.ok {
                return true;
            }
        }
        /* A value that lets one call go on can stop every other: a lock taken for a
        setting, a switch that admits only testers, a count that sends a loop over
        entries that are not there. No plain call of the owner or of a user may get
        less far with it than without it. */
        let now = self.states[0].world.clone();
        for entry in (0..self.entries.len()).filter(|e| *e != but) {
            if self.entries[entry].view || budget::spent() {
                continue;
            }
            for who in [OWNER, USER] {
                let plain = self.seed(entry, who, who, UNIT, U256::ZERO);
                let (_, before) = self.attempt_in(now.clone(), entry, &plain);
                let (_, after) = self.attempt_in(world.clone(), entry, &plain);
                let endless = after.halt == crate::trace::Halt::Steps
                    && before.halt != crate::trace::Halt::Steps;
                if endless || (after.ok, after.edges.len()) < (before.ok, before.edges.len()) {
                    return true;
                }
            }
        }
        false
    }

    fn left_behind(&self, before: &World, after: &World, run: &Run) -> bool {
        let subject = self.subject;
        let mut kinds: Vec<Option<Addr>> = vec![None];
        kinds.extend(after.assets().into_iter().map(Some));
        let held = |world: &World, kind: Option<Addr>| match kind {
            Some(asset) => world.asset_of(asset, subject),
            None => world.ether_of(subject),
        };
        let more = kinds.iter().any(|k| held(after, *k) > held(before, *k));
        let recorded = run.changes().iter().any(|(c, ..)| c.account == subject);
        more && !recorded
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
                        let (t, world, run) = self.solve(from, entry, seed);
                        // The owner's second way of filling in an address leads somewhere else
                        // even where it runs the same code.
                        let other_way = who == OWNER && kept && run.stores().next().is_some();
                        if run.ok && (self.novel(&run, &world) || other_way) {
                            let stray = self.left_behind(&self.states[from].world, &world, &run);
                            let at = self.keep(from, entry, &t, world, false);
                            self.states[at].stray |= stray;
                            next.push(at);
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
            if !self.survives(&breach, steps, run, about_value) {
                continue;
            }
            let steps = &self.fewest(&breach, steps);
            if self.shown_elsewhere(&breach, steps) {
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
    fn survives(&mut self, breach: &Breach, steps: &[Step], run: &Run, value: bool) -> bool {
        let subject = self.subject;
        /* A flag some call raises and lowers again within itself is down between
        calls. Taking it for a setting leaves it up for good. */
        let scoped = |place: &Place| self.facts.places.get(place).is_some_and(|p| p.scoped);
        let undo: Vec<(U256, U256)> = self
            .settings
            .iter()
            // A lock is one slot for the whole contract. An entry kept per account is no lock.
            .filter(|(place, _, _)| scoped(place) && place.depth == 0)
            .map(|(_, slot, held)| (*slot, *held))
            .collect();
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
            .filter(|(i, _)| value && used(*i) && !self.on_chain)
            .map(|(_, slot)| slot)
            .collect();
        doubtful.sort();
        doubtful.dedup();
        let about_caller = |c: &crate::trace::CallOut| {
            c.by == Answered::Blank && c.arg_tags.iter().any(|a| a.only(CALLER))
        };
        let judged = run.calls.iter().any(about_caller);
        if doubtful.is_empty() && undo.is_empty() && !judged {
            return true;
        }
        let prefix = self.states[0].steps.len();
        let mut world = self.states[0].world.clone();
        world.contrary = judged;
        for slot in doubtful {
            world.seed(subject, slot, UNIT);
        }
        for (slot, held) in undo {
            world.seed(subject, slot, held);
        }
        let kind = breach.kind;
        steps
            .get(prefix..)
            .is_none_or(|steps| self.shows(world, steps, &|b| b.kind == kind))
    }

    // Whether the same steps, made again from this world, end in the consequence asked for.
    fn shows(&mut self, mut world: World, steps: &[Step], same: &dyn Fn(&Breach) -> bool) -> bool {
        let subject = self.subject;
        let Some((Step::Call { msg, .. }, earlier)) = steps.split_last() else {
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
                Step::Holds { from } => {
                    match from {
                        Some(holder) => world.hold_from(*holder, ACTOR),
                        None => world.hold(ACTOR, STAKE),
                    };
                    base = world.clone();
                }
                Step::Sent { asset, to, amount } => {
                    self.runs += 1;
                    if !world.send(&sent(*asset, *to, *amount)).ok {
                        return false;
                    }
                }
                Step::Call { msg, .. } => {
                    self.runs += 1;
                    let made = world.send(msg);
                    if !made.ok {
                        return false;
                    }
                    if Facts::same_party(msg.from, ACTOR) {
                        spent = spent.wrapping_add(laws::claims_lowered(&made, subject, &base));
                    }
                }
            }
        }
        let before = world.clone();
        self.runs += 1;
        let again = world.send(msg);
        let found = laws::check(&base, &before, &world, &again, &self.facts, spent);
        again.ok && found.iter().any(same)
    }

    /* A call the finding shows without is no part of it. Each earlier call is left out
    in turn and the rest made again, and it stays out when the same consequence shows. */
    fn fewest(&mut self, breach: &Breach, steps: &[Step]) -> Vec<Step> {
        let prefix = self.states[0].steps.len().min(steps.len());
        let same = |b: &Breach| alike(b, breach);
        let mut kept = steps.to_vec();
        let mut at = prefix;
        while at + 1 < kept.len() && !budget::spent() {
            let mut without = kept.clone();
            without.remove(at);
            let world = self.states[0].world.clone();
            let call = matches!(kept[at], Step::Call { .. });
            if call && self.shows(world, &without[prefix..], &same) {
                kept = without;
            } else {
                at += 1;
            }
        }
        kept
    }

    /* A finding is the contract's own only where its calls to the contract are needed.
    What the calls to other contracts show by themselves is theirs. */
    fn shown_elsewhere(&mut self, breach: &Breach, steps: &[Step]) -> bool {
        let prefix = self.states[0].steps.len().min(steps.len());
        let subject = self.subject;
        let mut rest: Vec<Step> = steps[prefix..]
            .iter()
            .filter(|s| !matches!(s, Step::Call { msg, .. } if msg.to == subject))
            .cloned()
            .collect();
        while rest.last().is_some_and(|s| !matches!(s, Step::Call { .. })) {
            rest.pop();
        }
        let world = self.states[0].world.clone();
        !rest.is_empty() && self.shows(world, &rest, &|b| alike(b, breach))
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
            raced: false,
            stray: false,
            granted: false,
        });
        let at = self.states.len() - 1;
        let mut spent = false;
        for entry in 0..self.own {
            if self.entries[entry].view || budget::spent() {
                continue;
            }
            let seed = self.seed(entry, ACTOR, USER, breach.total, U256::ZERO);
            let (t, world, run) = self.solve(at, entry, seed);
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
        // Nothing is withheld from an account that could never have spent it.
        if !before.can_act(victim) {
            return false;
        }
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
            raced: false,
            stray: false,
            granted: false,
        });
        let at = self.states.len() - 1;
        let mut lost = false;
        for entry in 0..self.own {
            if self.entries[entry].view || budget::spent() {
                continue;
            }
            for amount in [breach.total, STAKE] {
                let other = if victim == OWNER { USER } else { OWNER };
                let seed = self.seed(entry, victim, other, amount, U256::ZERO);
                let (t, _, run) = self.solve(at, entry, seed);
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

    // The last call is given with the wait and the outside answers it was made under.
    fn history(&self, from: usize, entry: usize, t: &Try) -> Vec<Step> {
        let state = &self.states[from];
        let mut steps = state.steps.clone();
        steps.extend(Self::called(state.world.time, entry, t));
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
            let steps = self.history(from, entry, t);
            self.report(takeovers, entry, &steps, &again, (false, false));
        }
    }

    /* The account calls in again while the contract's call to it is still open. What
    counts is what that nesting adds: a breach the same two calls show when made one
    after the other is not about re-entry and is reported where it belongs. */
    fn reenter(&mut self, from: usize, entry: usize, t: &Try, plain: &[Breach]) {
        let mut hooks: Vec<(usize, Msg)> = vec![(entry, t.msg.clone())];
        let paying: Vec<usize> = (0..self.entries.len())
            .filter(|e| *e != entry && self.facts.entries[*e].pays_out)
            .collect();
        for other in paying.into_iter().take(MAX_HOOKS - 1) {
            hooks.push((other, self.seed(other, ACTOR, ACTOR, UNIT, U256::ZERO).msg));
        }
        let base = self.states[0].world.clone();
        let spent = self.states[from].spent;
        let before = self.states[from].world.clone();
        let (alone, first) = self.attempt(from, entry, t);
        for (inner, hook) in hooks {
            if budget::spent() {
                return;
            }
            let hook = Msg { hook: None, ..hook };
            let mut again = t.clone();
            again.msg.hook = Some(Box::new(hook.clone()));
            let (after, run) = self.attempt(from, entry, &again);
            if !run.ok || !run.hooked {
                continue;
            }
            let mut apart: Vec<Breach> = plain.to_vec();
            if first.ok {
                let (then, second) = self.attempt_in(alone.clone(), inner, &Try::sent(hook));
                if second.ok {
                    apart.extend(laws::check(
                        &base,
                        &alone,
                        &then,
                        &second,
                        &self.facts,
                        spent,
                    ));
                }
            }
            let breaches = laws::check(&base, &before, &after, &run, &self.facts, spent);
            let fresh: Vec<Breach> = breaches
                .into_iter()
                .filter(|b| !apart.iter().any(|p| p.kind == b.kind && p.asset == b.asset))
                .collect();
            let steps = self.history(from, entry, &again);
            self.report(fresh, entry, &steps, &run, (true, false));
        }
    }

    /* A contract may hold value no function here takes in: it was funded when it was
    made, or it is sent what it holds. A door only the owner gets through, that pays an
    asset out of the contract, says the contract is meant to hold that asset. A single
    call by an account that has paid nothing must not take any of it out. What users
    pay in is not added here. The states their calls leave hold it, on the contract's
    own records, and a made-up surplus beside those records is free for the taking in
    many sound contracts. */
    fn sweep(&mut self) {
        for (entry, kind) in self.owed.clone() {
            let facts = &self.facts.entries[entry];
            // A caller compared with a word of the call's own data keeps nobody out.
            let role = |p: &Place| {
                self.facts
                    .places
                    .get(p)
                    .is_some_and(|p| p.identity || p.gate)
            };
            if facts.reads.iter().any(role) && !facts.ended.contains(&ACTOR) {
                self.facts.keeps.insert(kind);
            }
        }
        let starts = self.states.len().min(MAX_STATES / 8);
        for start in 0..starts {
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
                raced: false,
                stray: false,
                granted: false,
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
                    let (t, world, run) = self.solve(at, entry, seed);
                    if !run.ok || self.once_for_all(&world, entry, &t, &run) {
                        continue;
                    }
                    let found =
                        laws::check(&before, &before, &world, &run, &self.facts, U256::ZERO);
                    let gains: Vec<Breach> =
                        found.into_iter().filter(|b| b.kind == Kind::Gain).collect();
                    let steps = self.history(at, entry, &t);
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
        let subject = self.subject;
        let elsewhere = |s: &Step| matches!(s, Step::Call { msg, .. } if msg.to != subject);
        let acted: Vec<usize> = (0..self.states.len())
            .filter(|s| self.states[*s].acted > 0 && !self.states[*s].raced)
            .filter(|s| !self.states[*s].steps.iter().any(elsewhere))
            .collect();
        for from in acted.into_iter().take(MAX_STATES / 4) {
            let blamed = self.states[from].steps.iter().rev().find_map(|s| match s {
                Step::Call { entry, msg } if msg.from == ACTOR => Some(*entry),
                _ => None,
            });
            let Some(blamed) = blamed else {
                continue;
            };
            for entry in 0..self.own {
                if self.entries[entry].view {
                    continue;
                }
                for seed in self.honest(entry, USER) {
                    if budget::spent() {
                        return;
                    }
                    let before = self.states[from].world.clone();
                    let (t, world, run) = self.solve(from, entry, seed);
                    if !run.ok {
                        continue;
                    }
                    let base = &self.states[0].world;
                    if let Some(breach) = laws::diverted(base, &before, &world) {
                        let steps = self.history(from, entry, &t);
                        self.report(vec![breach], blamed, &steps, &run, (false, true));
                    }
                    break;
                }
            }
        }
    }

    /* A call that fills plain cells it found empty and that nobody can make again is a
    step of the contract's set-up or of its closing. Whoever makes it first wins a race
    at deployment. On a contract in use it is not there to be made. */
    fn once_for_all(&mut self, after: &World, entry: usize, t: &Try, run: &Run) -> bool {
        let subject = self.subject;
        let fills = run.stores().any(|(c, old, new, _, _)| {
            c.account == subject && c.keys.is_empty() && old.is_zero() && !new.is_zero()
        });
        if !fills {
            return false;
        }
        [t.msg.from, USER].into_iter().all(|who| {
            let mut again = t.clone();
            again.msg.from = who;
            !self.attempt_in(after.clone(), entry, &again).1.ok
        })
    }

    /* Real state has real rates in it, and two kinds of payment show there that no
    guessed world ever made. An account that put its own value in and is paid more
    once the clock has moved is paid interest. An account paid in a call that also
    raises what the contract records for people unknown here is paid for work done for
    them, as a keeper is. Neither is taken from anyone. */
    fn earned(&self, from: usize, t: &Try, before: &World, run: &Run) -> bool {
        if !self.on_chain {
            return false;
        }
        let base = &self.states[0].world;
        let held = |world: &World, asset: Option<Addr>| {
            let of = |who: Addr| match asset {
                Some(asset) => world.asset_of(asset, who),
                None => world.ether_of(who),
            };
            of(ACTOR).wrapping_add(of(ALLY))
        };
        let mut kinds: Vec<Option<Addr>> = vec![None];
        kinds.extend(before.assets().into_iter().map(Some));
        let paid_in = kinds.iter().any(|k| held(before, *k) < held(base, *k));
        let mut acted = false;
        let mut waited = t.time.is_some_and(|time| time > before.time);
        for step in &self.states[from].steps {
            match step {
                Step::Call { msg, .. } => acted |= Facts::same_party(msg.from, ACTOR),
                Step::Wait { .. } => waited |= acted,
                _ => {}
            }
        }
        let unknown = |k: &crate::trace::Key| {
            let account = (97..=160).contains(&k.value.bits()) && !self.known.contains(&k.value);
            account && !before.runs_code(k.value)
        };
        let serves = run.stores().any(|(cell, old, new, _, _)| {
            cell.account == self.subject && new > old && cell.keys.iter().any(unknown)
        });
        (paid_in && waited) || serves
    }

    /* Anyone can come to hold some of what the contract keeps a ledger of, and some
    functions do nothing for an account that holds none. The chain's state has no
    holding for the account with no role, so one state gives it one. */
    fn as_holder(&mut self) {
        let mut world = self.states[0].world.clone();
        /* A holding sent by one who has some goes through the contract's own transfer,
        which keeps every record it has of a holder. A cell written here keeps one. */
        let from = [USER, OWNER]
            .into_iter()
            .find(|holder| world.hold_from(*holder, ACTOR));
        if from.is_none() && !world.hold(ACTOR, STAKE) {
            return;
        }
        let mut steps = self.states[0].steps.clone();
        steps.push(Step::Holds { from });
        self.states.push(State {
            world,
            steps,
            acted: 0,
            spent: U256::ZERO,
            raced: false,
            stray: false,
            granted: true,
        });
    }

    /* A call that ends may have ended on the quiet side of a test: nothing to burn,
    not the address that is charged, not yet time. The other side of each test on what
    the caller chose is tried once, and what runs code no call ran before is gone into. */
    fn other_sides(&mut self, from: usize, entry: usize, t: &Try, run: &Run) -> Vec<Try> {
        let now = self.states[from].world.time;
        let mut found = Vec::new();
        let mut reached: HashSet<u32> = run.edges.iter().copied().collect();
        for next in self.mutations(t, run, now, 24) {
            if budget::spent() || found.len() >= 4 {
                break;
            }
            let (_, tried) = self.attempt(from, entry, &next);
            let new = |e: &&u32| !self.edges.contains(e) && !reached.contains(e);
            if tried.edges.iter().any(|e| new(&e)) {
                reached.extend(tried.edges.iter().copied());
                found.push(next);
            }
        }
        found
    }

    fn attack(&mut self) {
        let mut frontier: Vec<usize> = (0..self.states.len()).collect();
        /* The state in which the account holds some comes first. It is made last, and
        taken last it is reached only when the states before it leave work over. */
        let holds = |s: &usize| {
            self.states[*s]
                .steps
                .iter()
                .any(|step| matches!(step, Step::Holds { .. }))
        };
        frontier.sort_by_key(|s| !holds(s));
        let holding: Vec<usize> = frontier.iter().copied().filter(holds).collect();
        for _ in 0..ACTOR_DEPTH {
            let mut next = Vec::new();
            for from in frontier {
                /* In the state where the account holds some, every function gets one
                short try before any gets a long one. With long tries only, the first
                functions used the work up and the later ones were never tried. */
                for shallow in [true, false] {
                    if shallow && !holding.contains(&from) {
                        continue;
                    }
                    self.shallow = shallow;
                    for entry in 0..self.own {
                        if !self.entries[entry].view && !self.act(from, entry, &mut next) {
                            self.shallow = false;
                            return;
                        }
                    }
                }
            }
            frontier = next;
        }
    }

    // False once the work is used up.
    fn act(&mut self, from: usize, entry: usize, next: &mut Vec<usize>) -> bool {
        let mut kept = false;
        let mut seeds: VecDeque<Try> = match self.entries[entry].to == self.subject {
            true => self.hostile(entry).into(),
            false => self.aimed(entry).into(),
        };
        let mut passed = false;
        let mut turned = 0;
        while let Some(seed) = seeds.pop_front() {
            if budget::spent() {
                return false;
            }
            let before = self.states[from].world.clone();
            let (t, world, run) = self.solve(from, entry, seed);
            // A call that ends says nothing of what else could have been passed on.
            if run.ok && !passed {
                let more = Self::passed_on(&t, &run, &t.shape.layout());
                passed = !more.is_empty();
                seeds.extend(more);
            }
            if run.ok && turned < 2 {
                let more = self.other_sides(from, entry, &t, &run);
                turned += more.len().max(1);
                seeds.extend(more);
            }
            let handed = run.calls.iter().any(|c| c.by == Answered::Taken);
            // What the call shows by itself, whether or not it was worth reporting.
            let mut alone = Vec::new();
            let race = run.ok && self.once_for_all(&world, entry, &t, &run);
            let open = !race && !self.states[from].raced;
            let own = self.entries[entry].to == self.subject;
            if run.ok && open && own {
                let base = self.states[0].world.clone();
                let spent = self.states[from].spent;
                let mut plain = laws::check(&base, &before, &world, &run, &self.facts, spent);
                alone.clone_from(&plain);
                plain.retain(|b| {
                    b.kind != Kind::Credit || self.spendable(&before, &world, b, entry)
                });
                plain.retain(|b| b.kind != Kind::Debit || self.withheld(&before, &world, b));
                let gains = plain.iter().any(|b| b.kind == Kind::Gain);
                let stray =
                    self.states[from].stray || (gains && self.earned(from, &t, &before, &run));
                let granted = self.states[from].granted;
                let claim = |b: &&Breach| matches!(b.kind, Kind::Gain | Kind::Credit);
                let shown = plain.iter().filter(|b| b.kind != Kind::Gain || !stray);
                let shown: Vec<Breach> = shown.filter(|b| !granted || !claim(b)).cloned().collect();
                let steps = self.history(from, entry, &t);
                self.report(shown, entry, &steps, &run, (false, false));
                if !granted {
                    self.takes_from_owner(from, entry, &t, &run);
                }
                let moved = laws::moved(&run);
                // A call that moves the same things from another state would be weighed the same.
                let seen = |p: &(usize, usize, Try, laws::Moved)| p.1 == entry && p.3 == moved;
                let of_state = self.paid.iter().filter(|p| p.0 == from).count();
                let of_entry = self.paid.iter().filter(|p| p.1 == entry).count();
                let fresh = of_state < SWAYED_A_STATE
                    && of_entry < SWAYED_AN_ENTRY
                    && !self.paid.iter().any(seen);
                if self.on_chain && fresh && !moved.nothing() {
                    self.paid.push((from, entry, t.clone(), moved));
                }
            }
            let apart = self.states[from].stray || self.states[from].granted;
            if handed && open && !apart && own {
                self.reenter(from, entry, &t, &alone);
            }
            if run.ok && self.novel(&run, &world) && !kept && self.states.len() < self.room {
                let at = self.keep(from, entry, &t, world, true);
                let lowered = laws::claims_lowered(&run, self.subject, &self.states[0].world);
                self.states[at].spent = self.states[at].spent.wrapping_add(lowered);
                self.states[at].raced |= race;
                /* What another contract writes down for the account rests on the purse
                this world handed it. What it then draws on that is not taken from anyone. */
                let keyed = |c: &crate::trace::Cell| c.keyed_by(ACTOR) || c.keyed_by(ALLY);
                let credited = |c: &(&crate::trace::Cell, U256, U256, Tag, usize)| {
                    c.0.account != self.subject && keyed(c.0) && c.2 > c.1
                };
                self.states[at].granted |= !own && run.changes().iter().any(credited);
                next.push(at);
                kept = true;
            }
        }
        true
    }

    /* On the chain what the contracts it calls hold is part of what the contract does,
    and anyone may change some of it. Each step stays short so the search stays cheap. */
    fn reach_out(&mut self) {
        self.add_outside();
        // The search below takes whatever work it is given, so the readings get theirs first.
        budget::within(budget::left() / 2, || self.readings());
        if self.entries.len() == self.own {
            return;
        }
        self.room = MAX_STATES + MAX_STATES / 2;
        let mut frontier: Vec<usize> = (0..self.states.len())
            .filter(|s| self.states[*s].acted <= 1 && !self.states[*s].raced)
            .collect();
        frontier.sort_by_key(|s| self.states[*s].acted);
        let mut outside: Vec<usize> = (self.own..self.entries.len()).collect();
        for from in frontier.into_iter().take(MAX_STATES / 8) {
            if !self.reach(from, &outside, 2) {
                return;
            }
            // An entry that changed nothing the contract reads from the first place is dropped.
            outside.retain(|e| self.facts.entries[*e].ended.contains(&ACTOR));
        }
    }

    fn readings(&mut self) {
        let mut paid = std::mem::take(&mut self.paid);
        // The same call is reported once, from the state fewest steps lead to.
        paid.sort_by_key(|(from, ..)| self.states[*from].steps.len());
        for (from, entry, t, _) in paid {
            if budget::spent() {
                return;
            }
            self.sway(from, entry, &t);
        }
    }

    /* A larger payout after the step is tried once more with every reading put back to
    what it was. If it is still larger, something else the step changed sized it, and
    nothing is shown. */
    fn sway(&mut self, from: usize, entry: usize, t: &Try) {
        let mut start = self.states[from].world.clone();
        start.noting = true;
        let (_, first) = self.attempt_in(start.clone(), entry, t);
        let steps = match first.ok && !first.read.is_empty() {
            true => self.steps_elsewhere(&start, &first),
            false => Vec::new(),
        };
        if self.trace {
            let name = &self.entries[entry].name;
            let (read, steps) = (first.read.len(), steps.len());
            eprintln!("sway {name} from state {from}: {read} readings, {steps} steps elsewhere");
        }
        for (world, made, on) in steps {
            if budget::spent() {
                return;
            }
            let (after, second) = self.attempt_in(world.clone(), entry, t);
            let found = laws::swayed(&first, &second, &after, &on);
            if found.is_empty() {
                continue;
            }
            let mut as_before = world;
            as_before.answer_as_before(first.read.clone());
            Self::set_for(&mut as_before, t);
            let third = as_before.send(&t.msg);
            self.runs += 1;
            let still = laws::swayed(&first, &third, &as_before, &on);
            let mut steps = self.states[from].steps.clone();
            steps.extend(made);
            steps.extend(Self::called(start.time, entry, t));
            for breach in found {
                if !third.ok || still.iter().any(|b| alike(b, &breach)) {
                    continue;
                }
                let same = |v: &Violation| v.entry == entry && alike(&v.breach, &breach);
                if self.found.iter().any(same) {
                    continue;
                }
                self.found.push(Violation {
                    breach,
                    entry,
                    steps: steps.clone(),
                    run: second.clone(),
                    via_hook: false,
                    by_user: false,
                });
            }
        }
    }

    /* What a step elsewhere must not do. One that pays the account is a trade of its
    own. One that leaves more in the contract's hands gave it what it then pays out. One
    that costs the account is a payment or a gift, and what the contract pays after it
    may be what was bought or given. A plain send costs too and is let through, since
    where that went is known. */
    fn idle(&self, before: &World, after: &World, run: &Run, send: bool) -> bool {
        let subject = self.subject;
        let mut kinds: Vec<Option<Addr>> = vec![None];
        kinds.extend(after.assets().into_iter().map(Some));
        let held = |world: &World, kind: Option<Addr>, who: Addr| match kind {
            Some(asset) => world.asset_of(asset, who),
            None => world.ether_of(who),
        };
        let own = |world: &World, kind: Option<Addr>| {
            held(world, kind, ACTOR).wrapping_add(held(world, kind, ALLY))
        };
        let fed = |k: &Option<Addr>| held(after, *k, subject) > held(before, *k, subject);
        let paid = kinds
            .iter()
            .any(|k| own(after, *k) > own(before, *k) || fed(k));
        let cost = kinds.iter().any(|k| own(after, *k) < own(before, *k));
        let keyed = |cell: &crate::trace::Cell| cell.keyed_by(ACTOR) || cell.keyed_by(ALLY);
        let changes = run.changes();
        let rose = |c: &(&crate::trace::Cell, U256, U256, Tag, usize)| keyed(c.0) && c.2 > c.1;
        let fell = |c: &(&crate::trace::Cell, U256, U256, Tag, usize)| keyed(c.0) && c.2 < c.1;
        let spent = cost || changes.iter().any(fell);
        !paid && !changes.iter().any(rose) && (send || !spent)
    }

    fn steps_elsewhere(
        &mut self,
        start: &World,
        first: &Run,
    ) -> Vec<(World, Vec<Step>, Vec<Addr>)> {
        let subject = self.subject;
        let read: HashSet<(Addr, U256)> = first
            .loads()
            .filter(|(cell, _)| cell.account != subject)
            .map(|(cell, _)| (cell.account, cell.slot))
            .collect();
        let mut out = Vec::new();
        let mut bases: Vec<(World, Vec<Step>, Option<Addr>)> =
            vec![(start.clone(), Vec::new(), None)];
        for (asset, to, amount) in self.holdings_read(start, first) {
            let mut world = start.clone();
            let run = world.send(&sent(asset, to, amount));
            self.runs += 1;
            let arrived = match asset {
                Some(asset) => run.changes().iter().any(|(cell, old, new, _, _)| {
                    cell.account == asset && cell.keyed_by(to) && new > old
                }),
                None => world.ether_of(to) > start.ether_of(to),
            };
            if !run.ok || !arrived || !self.idle(start, &world, &run, true) {
                continue;
            }
            let step = vec![Step::Sent { asset, to, amount }];
            out.push((world.clone(), step.clone(), vec![to]));
            bases.push((world, step, Some(to)));
        }
        for (base, made, sent_to) in bases {
            for entry in self.own..self.entries.len() {
                let to = self.entries[entry].to;
                if sent_to.is_some_and(|sent_to| sent_to != to) {
                    continue;
                }
                for seed in self.aimed(entry).into_iter().take(2) {
                    if budget::spent() {
                        return out;
                    }
                    let (world, run) = self.attempt_in(base.clone(), entry, &seed);
                    let moved = run
                        .changes()
                        .iter()
                        .any(|(cell, ..)| read.contains(&(cell.account, cell.slot)));
                    if !run.ok || !moved || !self.idle(&base, &world, &run, false) {
                        continue;
                    }
                    let mut steps = made.clone();
                    steps.push(Step::Call {
                        entry,
                        msg: seed.msg,
                    });
                    let on = sent_to.into_iter().chain([to]).collect();
                    out.push((world, steps, on));
                    break;
                }
            }
        }
        out
    }

    /* As much again as is held there is sent. That moves the reading far and needs no
    more than a holder there already has. */
    fn holdings_read(&self, start: &World, first: &Run) -> Vec<(Option<Addr>, Addr, U256)> {
        let subject = self.subject;
        let assets = start.assets();
        let other = |who: &Addr| {
            (97..=160).contains(&who.bits()) && *who != subject && !self.known.contains(who)
        };
        let mut places: Vec<Addr> = Vec::new();
        for (cell, _) in first.loads().filter(|(cell, _)| cell.account != subject) {
            match assets.contains(&cell.account) {
                true => places.extend(cell.keys.iter().map(|k| k.value).filter(other)),
                false => places.extend(Some(cell.account).filter(other)),
            }
        }
        let mut seen = HashSet::new();
        places.retain(|to| seen.insert(*to));
        let mut found: Vec<(Option<Addr>, Addr, U256)> = Vec::new();
        for to in places.into_iter().take(MAX_SENDS) {
            for asset in &assets {
                found.push((Some(*asset), to, start.holding(*asset, to)));
            }
        }
        for read in first.read.iter().filter(|r| r.asked.is_empty()) {
            if other(&read.of) && !found.iter().any(|f| f.0.is_none() && f.1 == read.of) {
                found.push((None, read.of, U256::from_be_bytes(&read.said)));
            }
        }
        for (asset, _, amount) in &mut found {
            let own = match asset {
                Some(asset) => start.asset_of(*asset, ACTOR),
                None => start.ether_of(ACTOR),
            };
            *amount = (*amount).min(own >> 1);
        }
        found.retain(|(_, _, amount)| !amount.is_zero());
        found.truncate(MAX_SENDS);
        found
    }

    // A step elsewhere is followed at once by calls to the contract, so it is not starved of work.
    fn reach(&mut self, from: usize, outside: &[usize], left: usize) -> bool {
        for entry in outside.iter().copied() {
            let mut made = Vec::new();
            if !self.act(from, entry, &mut made) {
                return false;
            }
            for at in made {
                for own in 0..self.own {
                    if !self.entries[own].view && !self.act(at, own, &mut Vec::new()) {
                        return false;
                    }
                }
                if left > 1 && !self.reach(at, outside, left - 1) {
                    return false;
                }
            }
        }
        true
    }

    /* Only entries that write what the contract read there can change what it does.
    An asset the account holds comes last, since it can send that itself and needs no
    entry for it. Each contract looked at is decompiled, so only a few are. */
    fn add_outside(&mut self) {
        let world = self.states[0].world.clone();
        let held = world.assets();
        let cells = |at: Addr| self.read_out.iter().filter(|c| c.0 == at).count();
        let mut talked: Vec<(bool, usize, usize, Addr, Option<Addr>)> = self
            .talked
            .iter()
            .map(|(at, (n, behind))| (!held.contains(at), cells(*at), *n, *at, *behind))
            .collect();
        talked.sort_by(|a, b| (b.0, b.1, b.2).cmp(&(a.0, a.1, a.2)).then(a.3.cmp(&b.3)));
        talked.truncate(MAX_READ);
        let mut named: Vec<(usize, Addr)> =
            self.named_out.iter().map(|(at, n)| (*n, *at)).collect();
        named.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)));
        let mut aims = vec![self.subject];
        aims.extend(
            named
                .into_iter()
                .map(|(_, at)| at)
                .filter(|at| world.runs_code(*at)),
        );
        let mut chosen = 0;
        for (_, _, _, to, behind) in talked {
            if chosen == MAX_OUTSIDE || budget::spent() {
                break;
            }
            let Some(code) = world.code(behind.unwrap_or(to)) else {
                continue;
            };
            let c = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default());
            let keyed = self.read_out.iter().any(|c| c.0 == to && c.2);
            let mut scored: Vec<(usize, Entry)> = Vec::new();
            for e in entries(&c, to).into_iter().filter(|e| !e.view) {
                let done = crate::model::in_code(&c, e.function);
                let read = done.writes.iter().filter_map(|w| U256::from_hex_str(w));
                let read = read
                    .filter(|w| self.read_out.contains(&(to, *w, false)))
                    .count();
                let score = read + usize::from(keyed && done.writes_under_keys);
                if score > 0 && !done.tests_caller {
                    scored.push((score, e));
                }
            }
            scored.sort_by_key(|a| std::cmp::Reverse(a.0));
            if scored.is_empty() {
                continue;
            }
            chosen += 1;
            aims.push(to);
            let picked = scored.into_iter().take(OUTSIDE_ENTRIES).map(|(_, e)| e);
            self.entries.extend(picked);
        }
        let mut seen = HashSet::new();
        aims.retain(|at| seen.insert(*at));
        aims.truncate(4);
        self.aims = aims;
        self.facts
            .entries
            .resize(self.entries.len(), Default::default());
        if self.trace {
            for e in &self.entries[self.own..] {
                eprintln!(
                    "outside {:.10} {} {:?}",
                    e.to.to_hex(),
                    e.name,
                    e.shape.kinds()
                );
            }
            let aims: Vec<String> = self.aims.iter().map(U256::to_hex).collect();
            eprintln!("aims {aims:?} talked {}", self.talked.len());
        }
    }

    /* A call to another contract matters to this one through what it changes there,
    so each account this one reads about there is tried in each place that names one. */
    fn aimed(&self, entry: usize) -> Vec<Try> {
        let kinds = self.entries[entry].shape.kinds();
        let places =
            (0..kinds.len()).filter(|i| matches!(kinds[*i], Holds::Address | Holds::Callee));
        let mut out = vec![self.seed(entry, ACTOR, ACTOR, UNIT, U256::ZERO)];
        for at in places.take(2) {
            for aim in &self.aims {
                let plain = self.seed(entry, ACTOR, ACTOR, UNIT, U256::ZERO);
                out.extend(plain.reshaped(&|shape| shape.put(at, *aim)));
            }
        }
        out
    }

    fn note_outside(&mut self, run: &Run) {
        let subject = self.subject;
        for event in &run.events {
            if let Event::Load { cell, .. } = event {
                let cell = &run.cells[*cell];
                if cell.account != subject {
                    self.read_out.insert(marked(cell));
                    // What is read through another contract is read all the same.
                    if !self.known.contains(&cell.account) {
                        self.talked.entry(cell.account).or_default();
                    }
                }
            }
        }
        for call in &run.calls {
            let direct =
                call.from == subject && !matches!(call.kind, op::DELEGATECALL | op::CALLCODE);
            if direct && !call.to.is_zero() && !self.known.contains(&call.to) {
                self.talked.entry(call.to).or_default().0 += 1;
                let (words, _) = call.input.get(4..).unwrap_or_default().as_chunks::<32>();
                for word in words.iter().map(|w| U256::from_be_bytes(w)) {
                    if (97..=160).contains(&word.bits()) && !self.known.contains(&word) {
                        *self.named_out.entry(word).or_default() += 1;
                    }
                }
            }
            if call.kind == op::DELEGATECALL {
                if let Some(talked) = self.talked.get_mut(&call.from) {
                    talked.1.get_or_insert(call.to);
                }
            }
        }
    }

    pub fn explore(&mut self, work: u64) {
        let started = budget::used();
        budget::within(work / 5, || match self.on_chain {
            true => self.settle_on_chain(),
            false => self.settle(),
        });
        budget::within(work / 10, || self.used_by(OWNER, 1));
        budget::within(work / 5, || self.used_by(USER, 2));
        // What the contract holds on the chain is read from it. Nothing more is taken to be there.
        match self.on_chain {
            true => self.as_holder(),
            false => budget::within(work / 10, || self.sweep()),
        }
        // What the earlier parts left unused goes to the account with no role.
        let left = work.saturating_sub(budget::used() - started);
        budget::within(left.saturating_sub(work / 10).max(work / 3), || {
            // The account's own calls to the contract come first and may not take it all.
            let room = budget::left().saturating_sub(work / 10 * u64::from(self.on_chain));
            budget::within(room, || self.attack());
            if self.on_chain {
                self.reach_out();
            }
        });
        budget::within(work / 10, || self.used_after());
    }
}
