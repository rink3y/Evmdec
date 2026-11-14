use crate::abi::{SEL_BALANCE_OF, SEL_TRANSFER, SEL_TRANSFER_FROM};
use crate::decompile::Contract;
use crate::deploy;
use crate::disasm;
use crate::exec;
use crate::function::FnKind;
use crate::interp::{CallRecord, CreateRecord, Host, Machine, Outcome};
use crate::opcode as op;
use crate::solve::word;
use crate::u256::U256;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

const SEL_APPROVE: u32 = 0x095e_a7b3;
const SEL_ALLOWANCE: u32 = 0xdd62_ed3e;
const SEL_TOTAL_SUPPLY: u32 = 0x1816_0ddd;
const SEL_DECIMALS: u32 = 0x313c_e567;
const DECIMALS: u64 = 18;
const IDENTITY: u64 = 4;
const STEPS_PER_CALL: usize = 600_000;
const MAX_DEPTH: usize = 12;
// The slots a call touched say which calls depend on which. A few hundred say it as
// well as thousands, and a set of thousands costs more to keep than the call to run.
const MAX_KEYS: usize = 256;
const MAX_WRITES: usize = 4_096;
const FIRST_MADE: u64 = 0xc0de_0000_0000;
// What every funded account starts with, in ether and in each asset. Large enough to
// pay for any call, and far from the top so that sums stay in range.
pub const PURSE: U256 = U256([0, 0, 1 << 32, 0]);

#[derive(Clone, Debug, Default)]
pub struct Call {
    pub who: U256,
    pub data: Vec<u8>,
    pub value: U256,
    pub seconds_later: u64,
    // A call the sender makes into the same contract when it is paid during this one.
    pub back: Option<(Vec<u8>, U256)>,
}

// What one account holds: ether, each outside asset it touched, and what the contract
// itself reports for it when the contract keeps balances.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Holdings {
    pub ether: U256,
    pub assets: BTreeMap<U256, U256>,
    pub reported: Option<U256>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Write {
    pub address: U256,
    pub slot: U256,
    pub before: U256,
    pub after: U256,
}

#[derive(Clone, Debug, Default)]
pub struct Done {
    pub ended: bool,
    pub returned: Vec<u8>,
    pub branches: BTreeSet<(usize, usize, bool)>,
    pub read: BTreeSet<U256>,
    pub written: BTreeSet<U256>,
    pub crossed: bool,
    // Whether any ether or asset changed hands, between any two accounts.
    pub moved: bool,
    pub called_back: bool,
    pub writes: Vec<Write>,
}

struct Code {
    bytes: Vec<u8>,
    dests: HashSet<usize>,
}

impl Code {
    fn of(bytes: &[u8]) -> Rc<Code> {
        Rc::new(Code {
            bytes: bytes.to_vec(),
            dests: disasm::jumpdests(bytes).into_iter().collect(),
        })
    }
}

type Entry = (FnKind, Option<u32>, Rc<Code>);

// Accounts with everything a call can touch: the code and storage of each contract,
// who holds how much ether, who holds how much of each asset, and what time it is. A
// call either ends and changes the world, or fails and leaves it as it was. A call to
// an address that has code runs that code. An address without code that is spoken to
// in the standard transfer interface is an asset, and keeps honest books: what a
// contract is told it holds is what was really sent to it.
#[derive(Clone, Default)]
pub struct World {
    codes: HashMap<U256, Rc<Code>>,
    // How the contract under test takes a call, one entry for each of its functions.
    entries: Rc<Vec<Entry>>,
    storage: HashMap<U256, HashMap<U256, U256>>,
    ether: HashMap<U256, U256>,
    assets: HashMap<(U256, U256), U256>,
    approved: HashSet<(U256, U256)>,
    funded: Vec<U256>,
    timestamp: U256,
    number: U256,
    made: u64,
}

struct Frame {
    account: U256,
    caller: U256,
    value: U256,
    data: Vec<u8>,
    code: Rc<Code>,
    depth: usize,
}

// One call from outside, with every call it leads to.
struct Run {
    origin: U256,
    target: U256,
    steps: usize,
    back: Option<(Vec<u8>, U256)>,
    done: Done,
}

fn selector(input: &[u8]) -> Option<u32> {
    let b = input.get(..4)?;
    Some(u32::from_be_bytes([b[0], b[1], b[2], b[3]]))
}

fn one_word(value: U256) -> Vec<u8> {
    value.to_be_bytes().to_vec()
}

impl World {
    pub fn new() -> World {
        World {
            timestamp: U256::from_u64(1_700_000_000),
            number: U256::from_u64(18_000_000),
            ..World::default()
        }
    }

    // The contract under test at its own address, from the storage its constructor or
    // its assumed settings leave.
    pub fn of(c: &Contract, accounts: &[U256]) -> World {
        let mut codes: HashMap<usize, Rc<Code>> = HashMap::new();
        let entries = c.functions.iter().map(|f| {
            let bytes = c.code_of(f);
            let code = codes
                .entry(bytes.as_ptr() as usize)
                .or_insert_with(|| Code::of(bytes));
            (f.kind, exec::selector_of(f), code.clone())
        });
        let mut world = World {
            entries: Rc::new(entries.collect()),
            funded: accounts.to_vec(),
            ..World::new()
        };
        world.storage.insert(exec::SELF, deploy::start(c));
        world
    }

    pub fn place(&mut self, address: U256, code: &[u8]) {
        self.codes.insert(address, Code::of(code));
    }

    pub fn fund(&mut self, who: U256) {
        self.funded.push(who);
    }

    pub fn seed(&mut self, address: U256, slot: U256, value: U256) {
        self.storage.entry(address).or_default().insert(slot, value);
    }

    pub fn stored(&self, address: U256, slot: U256) -> U256 {
        let slots = self.storage.get(&address);
        let held = slots.and_then(|s| s.get(&slot));
        held.copied().unwrap_or(U256::ZERO)
    }

    pub fn set_slots(&self, address: U256) -> BTreeSet<U256> {
        let slots = self.storage.get(&address).into_iter().flatten();
        let set = slots.filter(|(_, value)| !value.is_zero());
        set.map(|(slot, _)| *slot).collect()
    }

    pub fn slots(&self, address: U256) -> HashMap<U256, U256> {
        self.storage.get(&address).cloned().unwrap_or_default()
    }

    pub fn was_made(&self, address: U256) -> bool {
        address.fits_u64() && (FIRST_MADE + 1..=FIRST_MADE + self.made).contains(&address.low_u64())
    }

    pub fn time(&self) -> (U256, U256) {
        (self.timestamp, self.number)
    }

    pub fn holds_value(&self, who: U256) -> bool {
        let asset =
            |((_, holder), amount): (&(U256, U256), &U256)| *holder == who && !amount.is_zero();
        !self.ether_of(who).is_zero() || self.assets.iter().any(asset)
    }

    fn purse(&self, who: U256) -> U256 {
        match self.funded.contains(&who) {
            true => PURSE,
            false => U256::ZERO,
        }
    }

    fn ether_of(&self, who: U256) -> U256 {
        self.ether.get(&who).copied().unwrap_or(self.purse(who))
    }

    fn asset_of(&self, asset: U256, who: U256) -> U256 {
        let held = self.assets.get(&(asset, who)).copied();
        held.unwrap_or(self.purse(who))
    }

    fn pays(&mut self, from: U256, to: U256, amount: U256) -> bool {
        let held = self.ether_of(from);
        if held < amount {
            return false;
        }
        self.ether.insert(from, held - amount);
        let had = self.ether_of(to);
        self.ether
            .insert(to, had.checked_add(amount).unwrap_or(U256::MAX));
        true
    }

    fn moves(&mut self, asset: U256, from: U256, to: U256, amount: U256) -> bool {
        let held = self.asset_of(asset, from);
        if held < amount {
            return false;
        }
        self.assets.insert((asset, from), held - amount);
        let had = self.asset_of(asset, to);
        self.assets
            .insert((asset, to), had.checked_add(amount).unwrap_or(U256::MAX));
        true
    }

    // Value sent straight to an account, outside any function of a contract. Ether can
    // be forced on a contract and an asset is moved in the asset's own books, so no
    // contract can refuse either.
    pub fn give(&mut self, asset: Option<U256>, from: U256, to: U256, amount: U256) -> bool {
        match asset {
            Some(asset) => self.moves(asset, from, to, amount),
            None => self.pays(from, to, amount),
        }
    }

    pub fn assets(&self) -> BTreeSet<U256> {
        self.assets.keys().map(|(asset, _)| *asset).collect()
    }

    pub fn holdings(&self, who: U256) -> Holdings {
        let touched = self.assets.keys().filter(|(_, holder)| *holder == who);
        Holdings {
            ether: self.ether_of(who),
            assets: touched
                .map(|(asset, _)| (*asset, self.asset_of(*asset, who)))
                .collect(),
            reported: self.reported(who),
        }
    }

    // What the contract's own balance function says, asked without changing anything.
    fn reported(&self, who: U256) -> Option<U256> {
        let asked = |(kind, selector, _): &Entry| {
            *kind == FnKind::External && *selector == Some(SEL_BALANCE_OF)
        };
        let entry = self.entries.iter().position(asked)?;
        let call = Call {
            who,
            data: exec::calldata(Some(SEL_BALANCE_OF), &[who]),
            ..Call::default()
        };
        let done = self.clone().call(entry, &call);
        (done.ended && done.returned.len() >= 32).then(|| word(&done.returned, 0))
    }

    // A call to one function of the contract under test.
    pub fn call(&mut self, entry: usize, call: &Call) -> Done {
        match self.entries.get(entry) {
            Some((_, _, code)) => self.enter(exec::SELF, code.clone(), call),
            None => Done::default(),
        }
    }

    // A call to whatever code is placed at an address.
    pub fn run(&mut self, address: U256, call: &Call) -> Done {
        match self.codes.get(&address) {
            Some(code) => self.enter(address, code.clone(), call),
            None => Done::default(),
        }
    }

    fn size(&self) -> usize {
        self.storage.values().map(HashMap::len).sum::<usize>() + self.assets.len()
    }

    fn enter(&mut self, account: U256, code: Rc<Code>, call: &Call) -> Done {
        // A world is copied to try a call and copied again by whoever keeps the result.
        // With thousands of stored slots that costs more than running the call.
        exec::spend(2 * self.size() as u64);
        let before = self.clone();
        let later = U256::from_u64(call.seconds_later);
        self.timestamp = self.timestamp.wrapping_add(later);
        self.number = self
            .number
            .wrapping_add(U256::from_u64(call.seconds_later / 12));
        let mut run = Run {
            origin: call.who,
            target: account,
            steps: 0,
            back: call.back.clone(),
            done: Done::default(),
        };
        let frame = Frame {
            account,
            caller: call.who,
            value: call.value,
            data: call.data.clone(),
            code,
            depth: 0,
        };
        let paid = self.pays(call.who, account, call.value);
        let (ended, returned) = match paid {
            true => self.frame(&frame, &mut run),
            false => (false, Vec::new()),
        };
        exec::spend(run.steps as u64);
        let mut done = run.done;
        (done.ended, done.returned) = (ended, returned);
        done.crossed |= !call.value.is_zero();
        done.moved = self.ether != before.ether || self.assets != before.assets;
        if !ended {
            *self = before;
            done.writes.clear();
        }
        done
    }

    fn frame(&mut self, f: &Frame, run: &mut Run) -> (bool, Vec<u8>) {
        let code = f.code.clone();
        let id = Rc::as_ptr(&code) as usize;
        let mut host = Host::controlled(f.account, f.caller, f.data.clone(), f.value);
        host.origin = run.origin;
        host.intercept_calls = true;
        host.spends_balance = true;
        host.selfbalance = self.ether_of(f.account);
        host.timestamp = self.timestamp;
        host.number = self.number;
        let mut m = Machine::new(&code.bytes, &host);
        m.move_limit = Machine::LOOPED_MOVE_LIMIT;
        m.storage = self.storage.remove(&f.account).unwrap_or_default();
        let watched = f.account == run.target;
        let jump = |t: U256| t.as_usize().filter(|pc| code.dests.contains(pc));
        let outcome = loop {
            run.steps += 1;
            if run.steps > STEPS_PER_CALL {
                break Outcome::Exception("step limit".into());
            }
            let at = m.pc;
            let Some(opcode) = code.bytes.get(at).copied() else {
                break Outcome::Stop;
            };
            let done = &mut run.done;
            match (opcode, &m.stack[..]) {
                (op::SLOAD, [.., key]) if watched && done.read.len() < MAX_KEYS => {
                    done.read.insert(*key);
                }
                (op::SSTORE, [.., after, key]) => {
                    if watched && done.written.len() < MAX_KEYS {
                        done.written.insert(*key);
                    }
                    if done.writes.len() < MAX_WRITES {
                        done.writes.push(Write {
                            address: f.account,
                            slot: *key,
                            before: m.sload(*key),
                            after: *after,
                        });
                    }
                }
                _ => {}
            }
            let stepped = match m.step() {
                Ok(stepped) => stepped,
                Err(e) => break Outcome::Exception(e),
            };
            match stepped {
                None => {}
                Some(Outcome::Jump(t)) => match jump(t) {
                    Some(pc) => m.pc = pc,
                    None => break Outcome::Invalid,
                },
                Some(Outcome::JumpI(t, cond)) => {
                    run.done.branches.insert((id, at, !cond.is_zero()));
                    match (cond.is_zero(), jump(t)) {
                        (true, _) => m.pc = at + 1,
                        (false, Some(pc)) => m.pc = pc,
                        (false, None) => break Outcome::Invalid,
                    }
                }
                Some(Outcome::Call(index)) => {
                    let record = m.calls[index].clone();
                    let own = std::mem::take(&mut m.storage);
                    self.storage.insert(f.account, own);
                    let (success, data) = self.outside(&record, f, run);
                    m.storage = self.storage.remove(&f.account).unwrap_or_default();
                    m.balance_is(self.ether_of(f.account));
                    if m.resume_after_call(index, success, data).is_err() {
                        break Outcome::Exception("call result does not fit".into());
                    }
                    m.pc = at + 1;
                }
                Some(Outcome::Create(index)) => {
                    let record = m.creates[index].clone();
                    let own = std::mem::take(&mut m.storage);
                    self.storage.insert(f.account, own);
                    let made = self.create(&record, f, run);
                    m.storage = self.storage.remove(&f.account).unwrap_or_default();
                    if m.resume_after_create(made).is_err() {
                        break Outcome::Exception("stack overflow".into());
                    }
                    m.pc = at + 1;
                }
                Some(other) => break other,
            }
        };
        self.storage.insert(f.account, m.storage);
        match outcome {
            Outcome::Return(data) => (true, data),
            Outcome::Stop | Outcome::SelfDestruct(_) => (true, Vec::new()),
            Outcome::Revert(data) => (false, data),
            _ => (false, Vec::new()),
        }
    }

    fn code_at(&self, address: U256, input: &[u8]) -> Option<Rc<Code>> {
        if address != exec::SELF || self.entries.is_empty() {
            return self.codes.get(&address).cloned();
        }
        let wanted = selector(input);
        let named = |(kind, selector, _): &&Entry| {
            *kind == FnKind::External && wanted.is_some() && *selector == wanted
        };
        let rest = |(kind, _, _): &&Entry| match input.is_empty() {
            true => *kind == FnKind::Receive,
            false => *kind == FnKind::Fallback,
        };
        let found = self.entries.iter().find(named);
        let found = found.or_else(|| self.entries.iter().find(rest));
        found.map(|(_, _, code)| code.clone())
    }

    // Runs a frame that may fail, and takes back everything it did when it does.
    fn nested(&mut self, inner: &Frame, run: &mut Run, payer: Option<U256>) -> (bool, Vec<u8>) {
        exec::spend(self.size() as u64);
        let saved = self.clone();
        let written = run.done.writes.len();
        let paid = payer.is_none_or(|from| self.pays(from, inner.account, inner.value));
        let (success, output) = match paid {
            true => self.frame(inner, run),
            false => (false, Vec::new()),
        };
        if !success {
            *self = saved;
            run.done.writes.truncate(written);
        }
        (success, output)
    }

    fn outside(&mut self, record: &CallRecord, from: &Frame, run: &mut Run) -> (bool, Vec<u8>) {
        if record.addr == U256::from_u64(IDENTITY) {
            return (true, record.input.clone());
        }
        let Some(code) = self.code_at(record.addr, &record.input) else {
            return self.answer(record, from, run);
        };
        if from.depth >= MAX_DEPTH {
            return (true, Vec::new());
        }
        let (account, caller, value) = match record.kind {
            op::DELEGATECALL => (from.account, from.caller, from.value),
            op::CALLCODE => (from.account, from.account, record.value),
            _ => (record.addr, from.account, record.value),
        };
        let inner = Frame {
            account,
            caller,
            value,
            data: record.input.clone(),
            code,
            depth: from.depth + 1,
        };
        let payer = (record.kind == op::CALL).then_some(from.account);
        if record.kind != op::STATICCALL {
            return self.nested(&inner, run, payer);
        }
        let saved = self.clone();
        let written = run.done.writes.len();
        let result = self.frame(&inner, run);
        *self = saved;
        run.done.writes.truncate(written);
        result
    }

    // The account that made the outer call was just paid, and calls in again.
    fn calls_back(&mut self, from: &Frame, run: &mut Run) {
        let Some((data, value)) = run.back.take() else {
            return;
        };
        let Some(code) = self.code_at(run.target, &data) else {
            return;
        };
        let inner = Frame {
            account: run.target,
            caller: run.origin,
            value,
            data,
            code,
            depth: from.depth + 1,
        };
        let (success, _) = self.nested(&inner, run, Some(run.origin));
        run.done.called_back |= success;
    }

    // An address without code. An asset answers from its books. Anything else answers
    // one word that reads as true, which is what a call that went well most often
    // returns.
    fn answer(&mut self, call: &CallRecord, from: &Frame, run: &mut Run) -> (bool, Vec<u8>) {
        let (this, user) = (from.account, run.origin);
        let changes = call.kind == op::CALL;
        if changes && !call.value.is_zero() {
            self.pays(this, call.addr, call.value);
            run.done.crossed |= call.addr == user;
        }
        let arg = |index: usize| word(&call.input, 4 + 32 * index);
        let yes = (true, one_word(U256::ONE));
        let mut delivered = changes && call.addr == user;
        let answer = match selector(&call.input) {
            Some(SEL_TRANSFER) if changes && call.input.len() >= 68 => {
                let moved = self.moves(call.addr, this, arg(0), arg(1));
                run.done.crossed |= moved && arg(0) == user;
                delivered |= moved && arg(0) == user;
                (moved, one_word(U256::from(moved)))
            }
            Some(SEL_TRANSFER_FROM) if changes && call.input.len() >= 100 => {
                // An account lets the contract it calls take what the call asks for, and
                // leaves that approval standing, as accounts that use a contract do.
                let source = (call.addr, arg(0));
                let own = arg(0) == user || arg(0) == this;
                let allowed = own || self.approved.contains(&source);
                let moved = allowed && self.moves(call.addr, arg(0), arg(1), arg(2));
                if moved && arg(0) == user {
                    self.approved.insert(source);
                }
                run.done.crossed |= moved && (arg(0) == user || arg(1) == user);
                delivered |= moved && arg(1) == user;
                (moved, one_word(U256::from(moved)))
            }
            Some(SEL_BALANCE_OF) if call.input.len() >= 36 => {
                (true, one_word(self.asset_of(call.addr, arg(0))))
            }
            Some(SEL_ALLOWANCE) => (true, one_word(U256::MAX)),
            Some(SEL_DECIMALS) => (true, one_word(U256::from_u64(DECIMALS))),
            Some(SEL_TOTAL_SUPPLY) => (true, one_word(PURSE)),
            Some(SEL_APPROVE) => yes,
            _ => yes,
        };
        if delivered {
            self.calls_back(from, run);
        }
        answer
    }

    fn create(&mut self, record: &CreateRecord, from: &Frame, run: &mut Run) -> U256 {
        if from.depth >= MAX_DEPTH {
            return U256::ZERO;
        }
        self.made += 1;
        let address = U256::from_u64(FIRST_MADE + self.made);
        let inner = Frame {
            account: address,
            caller: from.account,
            value: record.value,
            data: Vec::new(),
            code: Code::of(&record.init),
            depth: from.depth + 1,
        };
        let (success, runtime) = self.nested(&inner, run, None);
        if !success {
            return U256::ZERO;
        }
        self.place(address, &runtime);
        address
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const CALLER: U256 = U256::from_u64(0xaaaa);
    const FIRST: U256 = U256::from_u64(0xf1);
    const SECOND: U256 = U256::from_u64(0xf2);

    fn stores_then(end: &[u8]) -> Vec<u8> {
        let mut code = vec![
            op::PUSH1,
            0x01,
            op::PUSH1,
            0x04,
            op::CALLDATALOAD,
            op::SSTORE,
        ];
        code.extend_from_slice(end);
        code
    }

    fn passes_on(kind: u8) -> Vec<u8> {
        let mut code = vec![
            op::CALLDATASIZE,
            op::PUSH1,
            0x00,
            op::PUSH1,
            0x00,
            op::CALLDATACOPY,
            op::PUSH1,
            0x00,
            op::PUSH1,
            0x00,
            op::CALLDATASIZE,
            op::PUSH1,
            0x00,
        ];
        if kind == op::CALL {
            code.extend_from_slice(&[op::PUSH1, 0x00]);
        }
        code.extend_from_slice(&[op::PUSH1, 0xf2, op::GAS, kind, op::STOP]);
        code
    }

    fn naming(slot: u8) -> Call {
        let mut data = vec![0u8; 36];
        data[35] = slot;
        Call {
            who: CALLER,
            data,
            ..Call::default()
        }
    }

    fn world(first: &[u8], second: &[u8]) -> World {
        let mut world = World::new();
        world.place(FIRST, first);
        world.place(SECOND, second);
        world
    }

    #[test]
    fn a_call_writes_the_storage_of_the_contract_it_reaches() {
        let mut world = world(&passes_on(op::CALL), &stores_then(&[op::STOP]));
        let done = world.run(FIRST, &naming(0x42));
        assert!(done.ended);
        assert_eq!(world.stored(SECOND, U256::from_u64(0x42)), U256::ONE);
        assert_eq!(world.stored(FIRST, U256::from_u64(0x42)), U256::ZERO);
        let expected = Write {
            address: SECOND,
            slot: U256::from_u64(0x42),
            before: U256::ZERO,
            after: U256::ONE,
        };
        assert_eq!(done.writes, [expected]);
    }

    #[test]
    fn a_delegated_call_writes_the_storage_of_the_contract_that_made_it() {
        let mut world = world(&passes_on(op::DELEGATECALL), &stores_then(&[op::STOP]));
        assert!(world.run(FIRST, &naming(0x42)).ended);
        assert_eq!(world.stored(FIRST, U256::from_u64(0x42)), U256::ONE);
        assert_eq!(world.stored(SECOND, U256::from_u64(0x42)), U256::ZERO);
    }

    #[test]
    fn a_call_that_fails_or_may_only_read_leaves_nothing_behind() {
        let reverts = [op::PUSH1, 0x00, op::PUSH1, 0x00, op::REVERT];
        let mut failing = world(&passes_on(op::CALL), &stores_then(&reverts));
        let done = failing.run(FIRST, &naming(0x42));
        assert!(done.ended);
        assert_eq!(failing.stored(SECOND, U256::from_u64(0x42)), U256::ZERO);
        assert!(done.writes.is_empty());

        let mut reading = world(&passes_on(op::STATICCALL), &stores_then(&[op::STOP]));
        let done = reading.run(FIRST, &naming(0x42));
        assert!(done.ended);
        assert_eq!(reading.stored(SECOND, U256::from_u64(0x42)), U256::ZERO);
        assert!(done.writes.is_empty());
    }

    #[test]
    fn created_code_is_placed_and_can_be_called() {
        let runtime = stores_then(&[op::STOP]);
        let size = runtime.len() as u8;
        let mut init = vec![
            op::PUSH1,
            size,
            op::PUSH1,
            0x0c,
            op::PUSH1,
            0x00,
            op::CODECOPY,
            op::PUSH1,
            size,
            op::PUSH1,
            0x00,
            op::RETURN,
        ];
        init.extend_from_slice(&runtime);
        let total = init.len() as u8;
        let mut creator = vec![
            op::PUSH1,
            total,
            op::PUSH1,
            0x00,
            op::PUSH1,
            0x00,
            op::CODECOPY,
            op::PUSH1,
            total,
            op::PUSH1,
            0x00,
            op::PUSH1,
            0x00,
            op::CREATE,
            op::STOP,
        ];
        creator[3] = creator.len() as u8;
        creator.extend_from_slice(&init);

        let mut world = World::new();
        world.place(FIRST, &creator);
        assert!(world.run(FIRST, &naming(0)).ended);
        let made = U256::from_u64(FIRST_MADE + 1);
        assert!(world.was_made(made));
        assert!(!world.was_made(FIRST));
        assert!(world.run(made, &naming(0x07)).ended);
        assert_eq!(world.stored(made, U256::from_u64(0x07)), U256::ONE);
    }
}
