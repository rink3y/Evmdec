use crate::budget;
use crate::trace::{
    join_all, Answered, CallOut, Cell, Event, Halt, Key, Run, Tag, BAL, BLOCK, CALLER, CLOCK, CMP,
    DATA, EXT, HASH, MATH, ORIGIN, OUT, SELF, SIZE, STORE, VALUE,
};
use evmdec::interp::{CallRecord, CreateRecord, Host, Machine, Outcome};
use evmdec::keccak::keccak256;
use evmdec::opcode as op;
use evmdec::U256;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::rc::Rc;

pub type Addr = U256;

#[must_use]
pub const fn account(tag: u64, n: u64) -> Addr {
    U256([n, 0, tag << 24, 0])
}

// Holds every role the contract hands out. Acts only to set the contract up.
pub const OWNER: Addr = account(0xad, 1);
// Uses the contract as it is meant to be used.
pub const USER: Addr = account(0xbb, 2);
// Holds no role. Its gain and other accounts' loss are what is looked for.
pub const ACTOR: Addr = account(0xac, 3);
// A second address of the same party, with code of its own choosing behind it.
pub const ALLY: Addr = account(0xac, 4);
pub const SUBJECT: Addr = account(0x5b, 0x5b);
// What a signature check recovers when nobody signed.
pub const NO_ONE: Addr = account(0xdead, 0xdead);

/* What every person starts with, in ether and in each asset. Large enough to pay for
any call and far enough from the top that sums stay in range. */
pub const PURSE: U256 = U256([0, 0, 1 << 32, 0]);

const STEP_LIMIT: u64 = 300_000;
const MAX_DEPTH: usize = 10;
const MAX_EVENTS: usize = 8_000;
const MAX_CMPS: usize = 600;
const MAX_FIELD: u64 = 12;
const MAX_TAGGED: usize = 4_096;
const FIRST_MADE: u64 = 0xc0de_0000;
const LAST_BUILT_IN: u64 = 0x11;

const SEL_TRANSFER: u32 = 0xa905_9cbb;
const SEL_TRANSFER_FROM: u32 = 0x23b8_72dd;
const SEL_BALANCE_OF: u32 = 0x70a0_8231;
const SEL_APPROVE: u32 = 0x095e_a7b3;
const SEL_ALLOWANCE: u32 = 0xdd62_ed3e;
const SEL_TOTAL_SUPPLY: u32 = 0x1816_0ddd;
const SEL_DECIMALS: u32 = 0x313c_e567;

struct Code {
    bytes: Vec<u8>,
    dests: HashSet<usize>,
    id: u32,
}

fn code_of(bytes: &[u8]) -> Rc<Code> {
    let hash = keccak256(bytes);
    Rc::new(Code {
        bytes: bytes.to_vec(),
        dests: evmdec::disasm::jumpdests(bytes).into_iter().collect(),
        id: u32::from_be_bytes([hash[0], hash[1], hash[2], hash[3]]),
    })
}

#[derive(Clone, Debug, Default)]
pub struct Msg {
    pub from: Addr,
    pub to: Addr,
    pub data: Vec<u8>,
    pub value: U256,
    // What the actor does when the contract hands it control during this message.
    pub hook: Option<Box<Msg>>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Holdings {
    pub ether: U256,
    pub assets: BTreeMap<Addr, U256>,
}

/* A local chain: the code and storage of each contract, who holds how much ether and
how much of each asset, and the time. A message either ends and changes it, or fails
and leaves it as it was. An address with no code that is spoken to in the transfer
interface is an asset and keeps honest books. */
#[derive(Clone, Default)]
pub struct World {
    codes: HashMap<Addr, Rc<Code>>,
    storage: HashMap<Addr, Rc<HashMap<U256, U256>>>,
    transient: HashMap<(Addr, U256), U256>,
    ether: Rc<HashMap<Addr, U256>>,
    assets: Rc<HashMap<(Addr, Addr), U256>>,
    grants: Rc<HashMap<(Addr, Addr, Addr), U256>>,
    // What an outside contract says to a question nobody keeps books for.
    answers: Rc<HashMap<(Addr, u32), Vec<u8>>>,
    // Digests the owner or the user is taken to have signed.
    signed: Rc<HashMap<U256, Addr>>,
    people: Vec<Addr>,
    // Accounts that hold a purse of something without being people. None is ether.
    rich: Vec<(Addr, Option<Addr>)>,
    pub subject: Addr,
    pub time: U256,
    pub number: U256,
    /* An outside contract asked about a caller who is not the owner answers zero. Some
    contracts say yes with a zero, so a finding is tried again with this set and the
    answer a one. */
    pub contrary: bool,
    made: u64,
}

struct Frame {
    account: Addr,
    caller: Addr,
    value: U256,
    data: Vec<u8>,
    data_tags: Vec<Tag>,
    code: Rc<Code>,
    depth: usize,
    fixed: bool,
}

struct Pre {
    bytes: Vec<u8>,
    tags: Vec<Tag>,
}

struct Tx {
    origin: Addr,
    hook: Option<Box<Msg>>,
    run: Run,
    hashes: HashMap<U256, Pre>,
    cell_ids: HashMap<(Addr, U256), usize>,
    edges: HashSet<u32>,
    cmps: usize,
}

#[derive(Default)]
struct Shadow {
    stack: Vec<Tag>,
    mem: Vec<Tag>,
    ret: Vec<Tag>,
}

impl Shadow {
    fn get(&self, off: U256, len: usize) -> Tag {
        let Some(off) = off.as_usize() else {
            return Tag::NONE;
        };
        let end = off.saturating_add(len).min(self.mem.len());
        self.mem.get(off..end).map_or(Tag::NONE, join_all)
    }

    fn slice(&self, off: U256, len: usize) -> Vec<Tag> {
        let len = len.min(MAX_TAGGED);
        let mut out = vec![Tag::NONE; len];
        if let Some(off) = off.as_usize() {
            for (i, slot) in out.iter_mut().enumerate() {
                *slot = self.mem.get(off + i).copied().unwrap_or(Tag::NONE);
            }
        }
        out
    }

    fn put(&mut self, off: U256, tags: &[Tag]) {
        let Some(off) = off.as_usize().filter(|o| *o < (1 << 20)) else {
            return;
        };
        let end = off + tags.len().min(MAX_TAGGED);
        if self.mem.len() < end {
            self.mem.resize(end, Tag::NONE);
        }
        self.mem[off..end].copy_from_slice(&tags[..end - off]);
    }

    fn set(&mut self, off: U256, len: usize, tag: Tag) {
        self.put(off, &vec![tag; len.min(MAX_TAGGED)]);
    }
}

struct Pending {
    to: Tag,
    value: Tag,
    args: Vec<Tag>,
    input: Vec<Tag>,
    out: Vec<Tag>,
    hashed: Option<(Vec<u8>, Vec<Tag>)>,
}

fn word(data: &[u8], at: usize) -> U256 {
    let mut buf = [0u8; 32];
    for (i, b) in buf.iter_mut().enumerate() {
        *b = data.get(at + i).copied().unwrap_or(0);
    }
    U256::from_be_bytes(&buf)
}

pub fn selector(data: &[u8]) -> Option<u32> {
    let b = data.get(..4)?;
    Some(u32::from_be_bytes([b[0], b[1], b[2], b[3]]))
}

// The message that moves an asset, as an account or a contract sends it.
#[must_use]
pub fn transfer_call(to: Addr, amount: U256) -> Vec<u8> {
    let mut data = SEL_TRANSFER.to_be_bytes().to_vec();
    data.extend_from_slice(&to.to_be_bytes());
    data.extend_from_slice(&amount.to_be_bytes());
    data
}

#[must_use]
pub fn transfer_from_call(from: Addr, to: Addr, amount: U256) -> Vec<u8> {
    let mut data = SEL_TRANSFER_FROM.to_be_bytes().to_vec();
    data.extend_from_slice(&from.to_be_bytes());
    data.extend_from_slice(&to.to_be_bytes());
    data.extend_from_slice(&amount.to_be_bytes());
    data
}

fn one_word(value: U256) -> Vec<u8> {
    value.to_be_bytes().to_vec()
}

fn built_in(addr: Addr) -> bool {
    addr.fits_u64() && (1..=LAST_BUILT_IN).contains(&addr.low_u64())
}

fn low_address(value: U256) -> Addr {
    value & ((U256::ONE << 160) - U256::ONE)
}

impl World {
    #[must_use]
    pub fn new() -> World {
        World {
            people: vec![OWNER, USER, ACTOR, ALLY],
            subject: SUBJECT,
            time: U256::from_u64(1_700_000_000),
            number: U256::from_u64(18_000_000),
            ..World::default()
        }
    }

    pub fn place(&mut self, address: Addr, code: &[u8]) {
        self.codes.insert(address, code_of(code));
    }

    #[must_use]
    pub fn has_code(&self, address: Addr) -> bool {
        self.codes.contains_key(&address)
    }

    pub fn seed(&mut self, address: Addr, slot: U256, value: U256) {
        let slots = self.storage.entry(address).or_default();
        Rc::make_mut(slots).insert(slot, value);
    }

    #[must_use]
    pub fn stored(&self, address: Addr, slot: U256) -> U256 {
        let slots = self.storage.get(&address);
        slots
            .and_then(|s| s.get(&slot))
            .copied()
            .unwrap_or(U256::ZERO)
    }

    #[must_use]
    pub fn slots(&self, address: Addr) -> Vec<(U256, U256)> {
        let slots = self.storage.get(&address);
        let mut all: Vec<(U256, U256)> = slots
            .into_iter()
            .flat_map(|s| s.iter().map(|(k, v)| (*k, *v)))
            .collect();
        all.sort();
        all
    }

    pub fn answer_with(&mut self, to: Addr, selector: u32, answer: Vec<u8>) {
        Rc::make_mut(&mut self.answers).insert((to, selector), answer);
    }

    pub fn sign(&mut self, digest: U256, signer: Addr) {
        Rc::make_mut(&mut self.signed).insert(digest, signer);
    }

    #[must_use]
    pub fn is_person(&self, who: Addr) -> bool {
        self.people.contains(&who)
    }

    // A contract in use holds ether and assets that were sent to it.
    pub fn enrich(&mut self, who: Addr, of: Option<Addr>) {
        if !self.rich.contains(&(who, of)) {
            self.rich.push((who, of));
        }
        if let Some(asset) = of {
            let held = self.asset_of(asset, who);
            Rc::make_mut(&mut self.assets).insert((asset, who), held);
        }
    }

    #[must_use]
    pub fn ether_of(&self, who: Addr) -> U256 {
        let start = match self.is_person(who) || self.rich.contains(&(who, None)) {
            true => PURSE,
            false => U256::ZERO,
        };
        self.ether.get(&who).copied().unwrap_or(start)
    }

    #[must_use]
    pub fn asset_of(&self, asset: Addr, who: Addr) -> U256 {
        let start = match self.is_person(who) || self.rich.contains(&(who, Some(asset))) {
            true => PURSE,
            false => U256::ZERO,
        };
        self.assets.get(&(asset, who)).copied().unwrap_or(start)
    }

    #[must_use]
    pub fn assets(&self) -> Vec<Addr> {
        let mut all: Vec<Addr> = self.assets.keys().map(|(asset, _)| *asset).collect();
        all.sort();
        all.dedup();
        all
    }

    #[must_use]
    pub fn holdings(&self, who: Addr) -> Holdings {
        let assets = self.assets().into_iter();
        Holdings {
            ether: self.ether_of(who),
            assets: assets.map(|a| (a, self.asset_of(a, who))).collect(),
        }
    }

    // Puts an asset in an account's hands, as when a person sends it there.
    pub fn give(&mut self, asset: Option<Addr>, from: Addr, to: Addr, amount: U256) -> bool {
        match asset {
            Some(asset) => self.moves(asset, from, to, amount),
            None => self.pays(from, to, amount),
        }
    }

    fn pays(&mut self, from: Addr, to: Addr, amount: U256) -> bool {
        if amount.is_zero() || from == to {
            return true;
        }
        let held = self.ether_of(from);
        if held < amount {
            return false;
        }
        let gets = self.ether_of(to).wrapping_add(amount);
        let ether = Rc::make_mut(&mut self.ether);
        ether.insert(from, held - amount);
        ether.insert(to, gets);
        true
    }

    fn moves(&mut self, asset: Addr, from: Addr, to: Addr, amount: U256) -> bool {
        let held = self.asset_of(asset, from);
        if held < amount {
            return false;
        }
        if from == to {
            Rc::make_mut(&mut self.assets).insert((asset, from), held);
            return true;
        }
        let gets = self.asset_of(asset, to).wrapping_add(amount);
        let assets = Rc::make_mut(&mut self.assets);
        assets.insert((asset, from), held - amount);
        assets.insert((asset, to), gets);
        true
    }

    /* A person leaves the contract under test free to take what its calls ask for, as
    people who use a contract do. Anyone else has to be granted an amount first. */
    fn allowed(&self, asset: Addr, owner: Addr, spender: Addr) -> U256 {
        if owner == spender || (self.is_person(owner) && spender == self.subject) {
            return U256::MAX;
        }
        let granted = self.grants.get(&(asset, owner, spender));
        granted.copied().unwrap_or(U256::ZERO)
    }

    fn size(&self) -> u64 {
        let slots: usize = self.storage.values().map(|s| s.len()).sum();
        (slots / 64 + self.storage.len() + 4) as u64
    }

    pub fn send(&mut self, msg: &Msg) -> Run {
        budget::spend(self.size());
        let before = self.clone();
        self.transient.clear();
        let mut tx = Tx {
            origin: msg.from,
            hook: msg.hook.clone(),
            run: Run {
                ok: false,
                halt: Halt::Fault,
                output: Vec::new(),
                events: Vec::new(),
                cells: Vec::new(),
                calls: Vec::new(),
                edges: Vec::new(),
                steps: 0,
                hooked: false,
            },
            hashes: HashMap::new(),
            cell_ids: HashMap::new(),
            edges: HashSet::new(),
            cmps: 0,
        };
        let paid = self.pays(msg.from, msg.to, msg.value);
        let (ok, output) = match (paid, self.codes.get(&msg.to).cloned()) {
            (false, _) => (false, Vec::new()),
            (true, None) => {
                tx.run.halt = Halt::Done;
                (true, Vec::new())
            }
            (true, Some(code)) => {
                let frame = Frame {
                    account: msg.to,
                    caller: msg.from,
                    value: msg.value,
                    data_tags: (0..msg.data.len()).map(Tag::data).collect(),
                    data: msg.data.clone(),
                    code,
                    depth: 0,
                    fixed: false,
                };
                let (ok, output, _) = self.frame(&frame, &mut tx);
                (ok, output)
            }
        };
        budget::spend(tx.run.steps);
        if !ok {
            *self = before;
        }
        let mut run = tx.run;
        (run.ok, run.output) = (ok, output);
        run.edges = tx.edges.into_iter().collect();
        run.edges.sort_unstable();
        run
    }

    // Runs a frame that may fail, and takes back everything it did when it does.
    fn nested(
        &mut self,
        inner: &Frame,
        tx: &mut Tx,
        payer: Option<Addr>,
    ) -> (bool, Vec<u8>, Vec<Tag>) {
        budget::spend(self.size());
        let saved = self.clone();
        let events = tx.run.events.len();
        let paid = payer.is_none_or(|from| self.pays(from, inner.account, inner.value));
        let (ok, output, tags) = match paid {
            true => self.frame(inner, tx),
            false => (false, Vec::new(), Vec::new()),
        };
        if !ok {
            *self = saved;
            tx.run.events.truncate(events);
        }
        (ok, output, tags)
    }

    fn event(tx: &mut Tx, event: Event) {
        if tx.run.events.len() < MAX_EVENTS {
            tx.run.events.push(event);
        }
    }

    fn unhash(tx: &Tx, slot: U256, depth: usize) -> (U256, Vec<Key>, u64) {
        if depth > 6 {
            return (slot, Vec::new(), 0);
        }
        let rootlike = |w: &U256| w.bits() <= 64 || tx.hashes.contains_key(w);
        for offset in 0..=MAX_FIELD {
            let base = slot.wrapping_sub(U256::from_u64(offset));
            let Some(pre) = tx.hashes.get(&base) else {
                continue;
            };
            let tag = |i: usize| pre.tags.get(i).copied().unwrap_or(Tag::NONE);
            let (key, parent) = match pre.bytes.len() {
                0..=31 => return (slot, Vec::new(), 0),
                32 => {
                    let (root, mut keys, _) = Self::unhash(tx, word(&pre.bytes, 0), depth + 1);
                    keys.push(Key {
                        value: U256::from_u64(offset),
                        tag: Tag::NONE,
                    });
                    return (root, keys, 0);
                }
                64 => {
                    let (first, second) = (word(&pre.bytes, 0), word(&pre.bytes, 32));
                    // Solidity hashes the key before the slot and Vyper the slot before the key.
                    match rootlike(&second) || !rootlike(&first) {
                        true => (
                            Key {
                                value: first,
                                tag: tag(0),
                            },
                            second,
                        ),
                        false => (
                            Key {
                                value: second,
                                tag: tag(1),
                            },
                            first,
                        ),
                    }
                }
                n => {
                    let parent = word(&pre.bytes, n - 32);
                    let head = U256::from_be_bytes(&keccak256(&pre.bytes[..n - 32]));
                    (
                        Key {
                            value: head,
                            tag: tag(0),
                        },
                        parent,
                    )
                }
            };
            let (root, mut keys, _) = Self::unhash(tx, parent, depth + 1);
            keys.push(key);
            return (root, keys, offset);
        }
        (slot, Vec::new(), 0)
    }

    fn cell(tx: &mut Tx, account: Addr, slot: U256) -> usize {
        if let Some(id) = tx.cell_ids.get(&(account, slot)) {
            return *id;
        }
        let (root, keys, offset) = Self::unhash(tx, slot, 0);
        let id = tx.run.cells.len();
        tx.run.cells.push(Cell {
            account,
            slot,
            root,
            keys,
            offset,
        });
        tx.cell_ids.insert((account, slot), id);
        id
    }

    fn code_size(&self, who: Addr) -> U256 {
        if let Some(code) = self.codes.get(&who) {
            return U256::from(code.bytes.len());
        }
        let bare = who.is_zero() || built_in(who) || [OWNER, USER, ACTOR].contains(&who);
        U256::from(!bare)
    }

    #[allow(clippy::too_many_lines)]
    fn frame(&mut self, f: &Frame, tx: &mut Tx) -> (bool, Vec<u8>, Vec<Tag>) {
        let code = f.code.clone();
        let mut host = Host::controlled(f.account, f.caller, f.data.clone(), f.value);
        host.origin = tx.origin;
        host.intercept_calls = true;
        host.timestamp = self.time;
        host.number = self.number;
        let mut m = Machine::new(&code.bytes, &host);
        m.move_limit = Machine::LOOPED_MOVE_LIMIT;
        let mut sh = Shadow::default();
        let fail = |tx: &mut Tx, halt: Halt| {
            if f.depth == 0 {
                tx.run.halt = halt;
            }
            (false, Vec::new(), Vec::new())
        };
        loop {
            tx.run.steps += 1;
            if tx.run.steps > STEP_LIMIT {
                tx.run.halt = Halt::Steps;
                return (false, Vec::new(), Vec::new());
            }
            let pc = m.pc;
            let Some(o) = code.bytes.get(pc).copied() else {
                if f.depth == 0 {
                    tx.run.halt = Halt::Done;
                }
                return (true, Vec::new(), Vec::new());
            };
            let n = m.stack.len();
            let need = op::info(o).map_or(0, |i| i.pops as usize);
            if n < need || sh.stack.len() != n {
                return fail(tx, Halt::Fault);
            }
            // The world answers what the machine cannot know of other accounts.
            let answered = match o {
                op::SLOAD => {
                    let key = m.stack[n - 1];
                    let value = self.stored(f.account, key);
                    let cell = Self::cell(tx, f.account, key);
                    Self::event(tx, Event::Load { cell, value });
                    let tag = Tag {
                        cell: u16::try_from(cell + 1).unwrap_or(u16::MAX),
                        ..Tag::of(STORE)
                    };
                    Some((1, Some((value, tag))))
                }
                op::SSTORE => {
                    if f.fixed {
                        return fail(tx, Halt::Fault);
                    }
                    let (key, new) = (m.stack[n - 1], m.stack[n - 2]);
                    let old = self.stored(f.account, key);
                    let cell = Self::cell(tx, f.account, key);
                    let tag = sh.stack[n - 2];
                    Self::event(
                        tx,
                        Event::Store {
                            cell,
                            old,
                            new,
                            tag,
                            pc,
                        },
                    );
                    self.seed(f.account, key, new);
                    Some((2, None))
                }
                op::TLOAD => {
                    let held = self.transient.get(&(f.account, m.stack[n - 1]));
                    let value = held.copied().unwrap_or(U256::ZERO);
                    Some((1, Some((value, Tag::of(STORE)))))
                }
                op::TSTORE => {
                    if f.fixed {
                        return fail(tx, Halt::Fault);
                    }
                    self.transient
                        .insert((f.account, m.stack[n - 1]), m.stack[n - 2]);
                    Some((2, None))
                }
                op::BALANCE => {
                    let who = low_address(m.stack[n - 1]);
                    Some((1, Some((self.ether_of(who), Tag::of(BAL)))))
                }
                op::SELFBALANCE => Some((0, Some((self.ether_of(f.account), Tag::of(BAL))))),
                op::EXTCODESIZE => {
                    let who = low_address(m.stack[n - 1]);
                    Some((1, Some((self.code_size(who), sh.stack[n - 1].with(EXT)))))
                }
                _ => None,
            };
            if let Some((pops, push)) = answered {
                m.stack.truncate(n - pops);
                sh.stack.truncate(n - pops);
                if let Some((value, tag)) = push {
                    m.stack.push(value);
                    sh.stack.push(tag);
                }
                m.pc = pc + 1;
                continue;
            }
            let pending = self.shadow(o, pc, &m, &mut sh, f, tx);
            let outcome = match m.step() {
                Err(_) => return fail(tx, Halt::Fault),
                Ok(None) => {
                    if let Some((bytes, tags)) = pending.hashed {
                        if let Some(hash) = m.stack.last() {
                            tx.hashes.insert(*hash, Pre { bytes, tags });
                        }
                    }
                    continue;
                }
                Ok(Some(outcome)) => outcome,
            };
            let jump = |t: U256| t.as_usize().filter(|pc| code.dests.contains(pc));
            match outcome {
                Outcome::Jump(t) => match jump(t) {
                    Some(to) => m.pc = to,
                    None => return fail(tx, Halt::Invalid),
                },
                Outcome::JumpI(t, c) => match (c.is_zero(), jump(t)) {
                    (true, _) => m.pc = pc + 1,
                    (false, Some(to)) => m.pc = to,
                    (false, None) => return fail(tx, Halt::Invalid),
                },
                Outcome::Fallthrough => {}
                Outcome::Stop => {
                    if f.depth == 0 {
                        tx.run.halt = Halt::Done;
                    }
                    return (true, Vec::new(), Vec::new());
                }
                Outcome::Return(data) => {
                    if f.depth == 0 {
                        tx.run.halt = Halt::Done;
                    }
                    return (true, data, pending.out);
                }
                Outcome::Revert(data) => {
                    if f.depth == 0 {
                        tx.run.halt = Halt::Reverted;
                    }
                    return (false, data, pending.out);
                }
                Outcome::SelfDestruct(to) => {
                    if f.fixed {
                        return fail(tx, Halt::Fault);
                    }
                    let to = low_address(to);
                    let all = self.ether_of(f.account);
                    self.pays(f.account, to, all);
                    Self::event(
                        tx,
                        Event::Destroy {
                            account: f.account,
                            to,
                            tag: pending.to,
                        },
                    );
                    if f.depth == 0 {
                        tx.run.halt = Halt::Done;
                    }
                    return (true, Vec::new(), Vec::new());
                }
                Outcome::Invalid | Outcome::Exception(_) => return fail(tx, Halt::Invalid),
                Outcome::Call(index) => {
                    let record = m.calls[index].clone();
                    let (ok, data, tags, id) = self.call_out(&record, pc, &pending, f, tx);
                    let result = Tag {
                        call: u16::try_from(id + 1).unwrap_or(u16::MAX),
                        ..Tag::of(OUT)
                    };
                    let copied = record.out_len.as_usize().unwrap_or(0).min(data.len());
                    sh.put(record.out_off, &tags[..copied.min(tags.len())]);
                    sh.ret = tags;
                    if m.resume_after_call(index, ok, data).is_err() {
                        return fail(tx, Halt::Fault);
                    }
                    sh.stack.push(result);
                    m.pc = pc + 1;
                }
                Outcome::Create(index) => {
                    let record = m.creates[index].clone();
                    let made = match f.fixed {
                        true => U256::ZERO,
                        false => self.create(&record, f, tx),
                    };
                    sh.ret = Vec::new();
                    if m.resume_after_create(made).is_err() {
                        return fail(tx, Halt::Fault);
                    }
                    sh.stack.push(Tag::NONE);
                    m.pc = pc + 1;
                }
            }
        }
    }

    /* Moves the tags the way the instruction about to run moves the words. Leaves the
    tag stack as the word stack will be once the instruction is done, except for a
    call or a creation, whose result is pushed when it is known. */
    #[allow(clippy::too_many_lines)]
    fn shadow(
        &mut self,
        o: u8,
        pc: usize,
        m: &Machine,
        sh: &mut Shadow,
        f: &Frame,
        tx: &mut Tx,
    ) -> Pending {
        let n = sh.stack.len();
        let val = |i: usize| m.stack[n - 1 - i];
        let tag = |sh: &Shadow, i: usize| sh.stack[n - 1 - i];
        let len_of = |v: U256| v.as_usize().unwrap_or(0).min(MAX_TAGGED);
        let mut pending = Pending {
            to: Tag::NONE,
            value: Tag::NONE,
            args: Vec::new(),
            input: Vec::new(),
            out: Vec::new(),
            hashed: None,
        };
        let info = op::info(o);
        let (pops, pushes) = info.map_or((0, 0), |i| (i.pops as usize, i.pushes as usize));
        let mut result = join_all(&sh.stack[n - pops..]);
        match o {
            op::DUP1..=op::DUP16 => {
                let k = (o - op::DUP1) as usize;
                sh.stack.push(tag(sh, k));
                return pending;
            }
            op::SWAP1..=op::SWAP16 => {
                let k = (o - op::SWAP1) as usize + 1;
                sh.stack.swap(n - 1, n - 1 - k);
                return pending;
            }
            op::CALLER => result = Tag::of(CALLER),
            op::ORIGIN => result = Tag::of(ORIGIN),
            op::CALLVALUE => result = Tag::of(VALUE),
            op::ADDRESS => result = Tag::of(SELF),
            op::TIMESTAMP | op::NUMBER => result = Tag::of(CLOCK),
            op::COINBASE
            | op::PREVRANDAO
            | op::GASLIMIT
            | op::BASEFEE
            | op::BLOBBASEFEE
            | op::GAS => {
                result = Tag::of(BLOCK);
            }
            op::BLOCKHASH | op::BLOBHASH => result = result.with(BLOCK),
            op::CALLDATASIZE => result = Tag::of(SIZE),
            op::RETURNDATASIZE => {
                result = Tag {
                    call: u16::try_from(tx.run.calls.len()).unwrap_or(u16::MAX),
                    ..Tag::of(SIZE)
                };
            }
            op::EXTCODEHASH => result = result.with(EXT),
            op::CALLDATALOAD => {
                let at = val(0).as_usize().unwrap_or(usize::MAX);
                // A word read from the very start is read for the four bytes that choose the function.
                let end = match at {
                    0 => 4,
                    _ => at.saturating_add(32),
                };
                let read = f
                    .data_tags
                    .get(at..end.min(f.data_tags.len()))
                    .map_or(Tag::NONE, join_all);
                result = result.join(read);
            }
            op::CALLDATACOPY => {
                let (at, len) = (val(1).as_usize().unwrap_or(usize::MAX), len_of(val(2)));
                let tags: Vec<Tag> = (0..len)
                    .map(|i| {
                        f.data_tags
                            .get(at.saturating_add(i))
                            .copied()
                            .unwrap_or(Tag::NONE)
                    })
                    .collect();
                sh.put(val(0), &tags);
            }
            op::CODECOPY => sh.set(val(0), len_of(val(2)), Tag::NONE),
            op::EXTCODECOPY => sh.set(val(1), len_of(val(3)), Tag::of(EXT)),
            op::RETURNDATACOPY => {
                let (at, len) = (val(1).as_usize().unwrap_or(usize::MAX), len_of(val(2)));
                let tags: Vec<Tag> = (0..len)
                    .map(|i| {
                        sh.ret
                            .get(at.saturating_add(i))
                            .copied()
                            .unwrap_or(Tag::NONE)
                    })
                    .collect();
                sh.put(val(0), &tags);
            }
            op::MCOPY => {
                let tags = sh.slice(val(1), len_of(val(2)));
                sh.put(val(0), &tags);
            }
            op::MLOAD => result = sh.get(val(0), 32),
            op::MSTORE => sh.set(val(0), 32, tag(sh, 1)),
            op::MSTORE8 => sh.set(val(0), 1, tag(sh, 1)),
            op::KECCAK256 => {
                let len = val(1).as_usize().unwrap_or(0);
                result = sh.get(val(0), len).with(HASH);
                if (32..=256).contains(&len) {
                    let at = val(0).as_usize().unwrap_or(usize::MAX);
                    let bytes: Vec<u8> = (0..len)
                        .map(|i| m.memory.get(at.saturating_add(i)).copied().unwrap_or(0))
                        .collect();
                    let tags = (0..len / 32)
                        .map(|w| sh.get(val(0).wrapping_add(U256::from(32 * w)), 32))
                        .collect();
                    pending.hashed = Some((bytes, tags));
                }
            }
            op::LT | op::GT | op::SLT | op::SGT | op::EQ => {
                let (ta, tb) = (tag(sh, 0), tag(sh, 1));
                if tx.cmps < MAX_CMPS && !(ta.is_none() && tb.is_none()) {
                    tx.cmps += 1;
                    let (a, b) = (val(0), val(1));
                    Self::event(
                        tx,
                        Event::Cmp {
                            pc,
                            op: o,
                            a,
                            b,
                            ta,
                            tb,
                        },
                    );
                }
                result = result.with(CMP);
            }
            op::ISZERO => {
                // A word of the call data tested against nothing is a comparison with zero.
                let ta = tag(sh, 0);
                if tx.cmps < MAX_CMPS && ta.has(DATA) && !ta.has(CMP) && ta.word().is_some() {
                    tx.cmps += 1;
                    let (a, b, tb) = (val(0), U256::ZERO, Tag::NONE);
                    Self::event(
                        tx,
                        Event::Cmp {
                            pc,
                            op: o,
                            a,
                            b,
                            ta,
                            tb,
                        },
                    );
                }
                result = result.with(CMP);
            }
            op::ADD | op::SUB | op::MUL => {
                let (a, b) = (val(0), val(1));
                let wraps = match o {
                    op::ADD => a.overflowing_add(b).1,
                    op::SUB => a.overflowing_sub(b).1,
                    _ => !a.full_mul(b).1.is_zero(),
                };
                // Compilers subtract and add around the top on purpose to build masks and offsets.
                let meant = a.bits() > 250 || b.bits() > 250;
                if wraps && !meant && !result.is_none() {
                    Self::event(
                        tx,
                        Event::Overflow {
                            pc,
                            op: o,
                            tag: result,
                        },
                    );
                }
                result = result.with(MATH);
            }
            op::DIV | op::SDIV | op::MOD | op::SMOD | op::ADDMOD | op::MULMOD | op::EXP => {
                result = result.with(MATH);
            }
            // A number read as a narrower signed one that comes out negative is no longer the number it was.
            op::SIGNEXTEND => {
                let (width, x) = (val(0), val(1));
                let sign = width.as_usize().filter(|w| *w < 31).map(|w| 8 * w + 7);
                let flips = sign.is_some_and(|bit| x.bits() as usize == bit + 1);
                if flips && !result.is_none() {
                    Self::event(
                        tx,
                        Event::Overflow {
                            pc,
                            op: o,
                            tag: result,
                        },
                    );
                }
            }
            op::JUMPI => {
                let cond = tag(sh, 1);
                let taken = !val(1).is_zero();
                let edge = f
                    .code
                    .id
                    .wrapping_mul(31)
                    .wrapping_add((pc as u32) << 1 | u32::from(taken));
                tx.edges.insert(edge);
                if !cond.is_none() {
                    let depth = f.depth;
                    Self::event(
                        tx,
                        Event::Branch {
                            pc,
                            taken,
                            tag: cond,
                            depth,
                        },
                    );
                }
                if let Some(call) = cond.call() {
                    if let Some(made) = tx.run.calls.get_mut(call) {
                        made.checked = true;
                    }
                }
            }
            op::CALL | op::CALLCODE | op::DELEGATECALL | op::STATICCALL => {
                let valued = o == op::CALL || o == op::CALLCODE;
                let base = if valued { 3 } else { 2 };
                pending.to = tag(sh, 1);
                if valued {
                    pending.value = tag(sh, 2);
                }
                let (at, len) = (val(base), len_of(val(base + 1)));
                pending.input = sh.slice(at, len);
                let words = len.saturating_sub(4) / 32;
                pending.args = (0..words.min(8))
                    .map(|w| join_all(&pending.input[4 + 32 * w..4 + 32 * w + 32]))
                    .collect();
                sh.stack.truncate(n - pops);
                return pending;
            }
            op::CREATE | op::CREATE2 => {
                sh.stack.truncate(n - pops);
                return pending;
            }
            op::RETURN | op::REVERT => pending.out = sh.slice(val(0), len_of(val(1))),
            op::SELFDESTRUCT => pending.to = tag(sh, 0),
            _ => {}
        }
        sh.stack.truncate(n - pops);
        if pushes > 0 {
            let fresh = matches!(
                o,
                op::PUSH0
                    ..=op::PUSH32 | op::PC | op::MSIZE | op::CODESIZE | op::CHAINID | op::GASPRICE
            );
            sh.stack
                .push(if fresh { Tag::NONE } else { result.settled() });
        }
        pending
    }

    fn call_out(
        &mut self,
        record: &CallRecord,
        pc: usize,
        pending: &Pending,
        f: &Frame,
        tx: &mut Tx,
    ) -> (bool, Vec<u8>, Vec<Tag>, usize) {
        let id = tx.run.calls.len();
        let to = low_address(record.addr);
        tx.run.calls.push(CallOut {
            depth: f.depth,
            pc,
            kind: record.kind,
            from: f.account,
            to,
            value: record.value,
            input: record.input.iter().copied().take(4 + 32 * 8).collect(),
            to_tag: pending.to,
            value_tag: pending.value,
            arg_tags: pending.args.clone(),
            input_from: pending.input.first().copied().unwrap_or(Tag::NONE),
            ok: false,
            by: Answered::Blank,
            checked: false,
            output: Vec::new(),
        });
        Self::event(tx, Event::Call(id));
        let fixed = f.fixed || record.kind == op::STATICCALL;
        let (ok, output, tags, by) = self.dispatch(record, to, id, fixed, pending, f, tx);
        let made = &mut tx.run.calls[id];
        (made.ok, made.by) = (ok, by);
        made.output = output.iter().copied().take(96).collect();
        Self::event(tx, Event::Returned(id));
        (ok, output, tags, id)
    }

    #[allow(clippy::too_many_arguments)]
    fn dispatch(
        &mut self,
        record: &CallRecord,
        to: Addr,
        id: usize,
        fixed: bool,
        pending: &Pending,
        f: &Frame,
        tx: &mut Tx,
    ) -> (bool, Vec<u8>, Vec<Tag>, Answered) {
        let out = Tag {
            call: u16::try_from(id + 1).unwrap_or(u16::MAX),
            ..Tag::of(OUT)
        };
        let said = |answer: (bool, Vec<u8>), by: Answered| {
            let tags = vec![out; answer.1.len().min(MAX_TAGGED)];
            (answer.0, answer.1, tags, by)
        };
        let moves_value = record.kind == op::CALL && !record.value.is_zero();
        if moves_value && fixed {
            return said((false, Vec::new()), Answered::Blank);
        }
        if built_in(to) {
            let answer = match to.low_u64() {
                1 => {
                    /* A signature nobody made recovers to some address nobody holds, a
                    different one for each thing signed, as it does on chain. */
                    let digest = word(&record.input, 0);
                    let nobody =
                        low_address(U256::from_be_bytes(&keccak256(&record.input))) | NO_ONE;
                    one_word(self.signed.get(&digest).copied().unwrap_or(nobody))
                }
                4 => record.input.clone(),
                // The other built-in contracts are not run. A digest of the input stands for theirs.
                _ => keccak256(&record.input).to_vec(),
            };
            let tags = vec![join_all(&pending.input).with(HASH); answer.len().min(MAX_TAGGED)];
            return (true, answer, tags, Answered::BuiltIn);
        }
        if let Some(code) = self.codes.get(&to).cloned() {
            if f.depth >= MAX_DEPTH {
                return said((false, Vec::new()), Answered::Code);
            }
            let (account, caller, value) = match record.kind {
                op::DELEGATECALL => (f.account, f.caller, f.value),
                op::CALLCODE => (f.account, f.account, record.value),
                _ => (to, f.account, record.value),
            };
            let inner = Frame {
                account,
                caller,
                value,
                data: record.input.clone(),
                data_tags: pending.input.clone(),
                code,
                depth: f.depth + 1,
                fixed,
            };
            let payer = moves_value.then_some(f.account);
            if payer.is_some() {
                let (to_tag, amount_tag) = (pending.to, pending.value);
                let (from, amount) = (f.account, record.value);
                Self::event(
                    tx,
                    Event::Pay {
                        asset: None,
                        from,
                        to,
                        amount,
                        to_tag,
                        amount_tag,
                    },
                );
            }
            let (ok, output, mut tags) = self.nested(&inner, tx, payer);
            tags.resize(output.len().min(MAX_TAGGED), Tag::NONE);
            return (ok, output, tags, Answered::Code);
        }
        // Code run in the caller's own storage is part of the caller. When it is not
        // here to run, nothing is known of what it would have done.
        if matches!(record.kind, op::DELEGATECALL | op::CALLCODE) {
            return said((true, Vec::new()), Answered::Blank);
        }
        if moves_value {
            if !self.pays(f.account, to, record.value) {
                return said((false, Vec::new()), Answered::Blank);
            }
            let (to_tag, amount_tag) = (pending.to, pending.value);
            let (from, amount) = (f.account, record.value);
            Self::event(
                tx,
                Event::Pay {
                    asset: None,
                    from,
                    to,
                    amount,
                    to_tag,
                    amount_tag,
                },
            );
        }
        if to == ACTOR || to == ALLY {
            if !fixed {
                self.hand_over(f, tx);
            }
            let shaped = selector(&record.input).and_then(|s| self.answers.get(&(to, s)));
            let answer = match (shaped, record.input.is_empty()) {
                (Some(shaped), _) => shaped.clone(),
                (None, true) => Vec::new(),
                (None, false) => one_word(U256::ONE),
            };
            return said((true, answer), Answered::Taken);
        }
        if to.is_zero() || self.is_person(to) {
            return said((true, Vec::new()), Answered::Blank);
        }
        let (answer, by) = self.asked(record, to, fixed, pending, f, tx);
        said(answer, by)
    }

    // The actor was just called by the contract, and calls in again.
    fn hand_over(&mut self, f: &Frame, tx: &mut Tx) {
        let Some(hook) = tx.hook.take() else {
            return;
        };
        let Some(code) = self.codes.get(&hook.to).cloned() else {
            return;
        };
        let inner = Frame {
            account: hook.to,
            caller: hook.from,
            value: hook.value,
            data_tags: (0..hook.data.len()).map(Tag::data).collect(),
            data: hook.data.clone(),
            code,
            depth: f.depth + 1,
            fixed: false,
        };
        let (ok, _, _) = self.nested(&inner, tx, Some(hook.from));
        tx.run.hooked |= ok;
    }

    /* An address with no code. An asset answers from its books. Anything else answers
    what the world was told it answers, or one word that reads as true. */
    fn asked(
        &mut self,
        record: &CallRecord,
        to: Addr,
        fixed: bool,
        pending: &Pending,
        f: &Frame,
        tx: &mut Tx,
    ) -> ((bool, Vec<u8>), Answered) {
        let arg = |i: usize| word(&record.input, 4 + 32 * i);
        let arg_tag = |i: usize| pending.args.get(i).copied().unwrap_or(Tag::NONE);
        let this = f.account;
        let chosen = selector(&record.input);
        let size = record.input.len();
        let books = |answer: (bool, Vec<u8>)| (answer, Answered::Books);
        let yes = one_word(U256::ONE);
        match chosen {
            Some(SEL_TRANSFER) if !fixed && size >= 68 => {
                let (dest, amount) = (low_address(arg(0)), arg(1));
                let moved = self.moves(to, this, dest, amount);
                if moved {
                    let (to_tag, amount_tag) = (arg_tag(0), arg_tag(1));
                    let paid = Event::Pay {
                        asset: Some(to),
                        from: this,
                        to: dest,
                        amount,
                        to_tag,
                        amount_tag,
                    };
                    Self::event(tx, paid);
                }
                books((moved, one_word(U256::from(moved))))
            }
            Some(SEL_TRANSFER_FROM) if !fixed && size >= 100 => {
                let (from, dest, amount) = (low_address(arg(0)), low_address(arg(1)), arg(2));
                let limit = self.allowed(to, from, this);
                let moved = limit >= amount && self.moves(to, from, dest, amount);
                if moved {
                    if limit != U256::MAX {
                        Rc::make_mut(&mut self.grants).insert((to, from, this), limit - amount);
                    }
                    let (to_tag, amount_tag) = (arg_tag(1), arg_tag(2));
                    let paid = Event::Pay {
                        asset: Some(to),
                        from,
                        to: dest,
                        amount,
                        to_tag,
                        amount_tag,
                    };
                    Self::event(tx, paid);
                }
                books((moved, one_word(U256::from(moved))))
            }
            Some(SEL_BALANCE_OF) if size >= 36 => {
                let held = self.asset_of(to, low_address(arg(0)));
                // An asset somebody asked about is one the world keeps books for.
                if !self.assets.contains_key(&(to, this)) {
                    let own = self.asset_of(to, this);
                    Rc::make_mut(&mut self.assets).insert((to, this), own);
                }
                books((true, one_word(held)))
            }
            Some(SEL_APPROVE) if !fixed && size >= 68 => {
                let grant = (to, this, low_address(arg(0)));
                Rc::make_mut(&mut self.grants).insert(grant, arg(1));
                books((true, yes))
            }
            Some(SEL_ALLOWANCE) if size >= 68 => {
                let limit = self.allowed(to, low_address(arg(0)), low_address(arg(1)));
                books((true, one_word(limit)))
            }
            Some(SEL_TOTAL_SUPPLY) => books((true, one_word(PURSE << 3))),
            Some(SEL_DECIMALS) => books((true, one_word(U256::from_u64(18)))),
            other => {
                /* A contract that asks another about its caller is most often asking
                whether the caller may act. The account with no role is the one that may
                not, so it is told no. The owner and a user are known to the other
                contract and get its usual answer. */
                let about = (0..pending.args.len())
                    .find(|i| arg_tag(*i).only(CALLER) || arg_tag(*i).only(ORIGIN));
                let asked_of = about.map(|i| low_address(arg(i)));
                let refused = asked_of.is_some_and(|who| who == ACTOR || who == ALLY);
                let shaped = other.and_then(|s| self.answers.get(&(to, s)));
                let answer = match refused {
                    true => one_word(U256::from(self.contrary)),
                    false => shaped.cloned().unwrap_or(yes),
                };
                ((true, answer), Answered::Blank)
            }
        }
    }

    fn create(&mut self, record: &CreateRecord, f: &Frame, tx: &mut Tx) -> Addr {
        if f.depth >= MAX_DEPTH {
            return U256::ZERO;
        }
        self.made += 1;
        let address = account(FIRST_MADE, self.made);
        let inner = Frame {
            account: address,
            caller: f.account,
            value: record.value,
            data: Vec::new(),
            data_tags: Vec::new(),
            code: code_of(&record.init),
            depth: f.depth + 1,
            fixed: false,
        };
        let (ok, runtime, _) = self.nested(&inner, tx, Some(f.account));
        if !ok {
            return U256::ZERO;
        }
        self.place(address, &runtime);
        address
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::trace::CALLER as FROM_CALLER;

    fn run(code_hex: &str, data: Vec<u8>, from: Addr) -> (World, Run) {
        let mut world = World::new();
        world.place(SUBJECT, &evmdec::hex::decode(code_hex).expect("hex"));
        let msg = Msg {
            from,
            to: SUBJECT,
            data,
            ..Msg::default()
        };
        let run = world.send(&msg);
        (world, run)
    }

    #[test]
    fn a_store_keeps_where_its_value_came_from() {
        // sstore(0, caller); sstore(1, calldataload(4))
        let (world, run) = run("33600055600435600155", vec![0, 0, 0, 0, 7], ACTOR);
        assert!(run.ok);
        assert_eq!(world.stored(SUBJECT, U256::ZERO), ACTOR);
        let stores: Vec<_> = run.stores().collect();
        assert!(stores[0].3.only(FROM_CALLER));
        assert_eq!(stores[1].3.word(), Some(0));
    }

    #[test]
    fn a_mapping_entry_is_read_back_to_its_slot_and_key() {
        // mstore(0, caller); mstore(32, 5); sstore(keccak(0, 64), 1)
        let (_, run) = run("3360005260056020526001604060002055", Vec::new(), USER);
        assert!(run.ok);
        let cell = run.stores().next().expect("one store").0.clone();
        assert_eq!(cell.root, U256::from_u64(5));
        assert_eq!(cell.keys.len(), 1);
        assert_eq!(cell.keys[0].value, USER);
        assert!(cell.keys[0].tag.only(FROM_CALLER));
    }

    #[test]
    fn a_failed_message_leaves_the_world_as_it_was() {
        // sstore(0, 1); revert(0, 0)
        let (world, run) = run("600160005560006000fd", Vec::new(), USER);
        assert!(!run.ok);
        assert_eq!(run.halt, Halt::Reverted);
        assert!(world.stored(SUBJECT, U256::ZERO).is_zero());
    }

    #[test]
    fn an_outside_contract_asked_about_a_stranger_says_no_and_can_be_made_to_say_the_other() {
        // mstore(4, caller); call(gas, asset, 0, 0, 36, 0, 32); return(0, 32)
        let code = "336004526020600060246000600073a50000000000000000000000000000000000000161fffff15060206000f3";
        let answer = |from: Addr, contrary: bool| {
            let mut world = World::new();
            world.place(SUBJECT, &evmdec::hex::decode(code).expect("hex"));
            world.contrary = contrary;
            let msg = Msg {
                from,
                to: SUBJECT,
                ..Msg::default()
            };
            word(&world.send(&msg).output, 0)
        };
        assert_eq!(answer(OWNER, false), U256::ONE);
        assert_eq!(answer(ACTOR, false), U256::ZERO);
        assert_eq!(answer(ACTOR, true), U256::ONE);
    }

    #[test]
    fn an_asset_keeps_honest_books() {
        // call(gas, asset, 0, 0, 68, 0, 32) with transfer(ACTOR, 5) in memory
        let mut data = SEL_TRANSFER.to_be_bytes().to_vec();
        data.extend_from_slice(&ACTOR.to_be_bytes());
        data.extend_from_slice(&U256::from_u64(5).to_be_bytes());
        // calldatacopy(0, 0, 68); call(gas, asset, 0, 0, 68, 0, 32)
        let code = "604460006000376020600060446000600073a50000000000000000000000000000000000000161fffff100";
        let mut world = World::new();
        world.place(SUBJECT, &evmdec::hex::decode(code).expect("hex"));
        let asset = account(0xa5, 1);
        let msg = Msg {
            from: USER,
            to: SUBJECT,
            data,
            ..Msg::default()
        };
        let refused = world.send(&msg);
        assert!(
            refused.ok && !refused.calls[0].ok,
            "the contract holds nothing to send"
        );
        assert!(world.give(Some(asset), USER, SUBJECT, U256::from_u64(9)));
        let run = world.send(&msg);
        assert!(run.calls[0].ok);
        assert_eq!(world.asset_of(asset, SUBJECT), U256::from_u64(4));
        assert_eq!(world.asset_of(asset, ACTOR), PURSE + U256::from_u64(5));
        assert_eq!(run.calls[0].arg_tags[0].word(), Some(0));
    }
}
