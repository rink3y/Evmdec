use crate::disasm;
use crate::interp::{CallRecord, CreateRecord, Host, Machine, Outcome};
use crate::opcode as op;
use crate::u256::U256;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

const BUDGET: usize = 600_000;
const MAX_DEPTH: usize = 12;
const SENT_INPUT: usize = 100;
const FIRST_MADE: u64 = 0xc0de_0000_0000;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Write {
    pub address: U256,
    pub slot: U256,
    pub before: U256,
    pub after: U256,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sent {
    pub from: U256,
    pub to: U256,
    pub value: U256,
    pub input: Vec<u8>,
}

#[derive(Clone, Debug)]
struct Frame {
    account: U256,
    caller: U256,
    value: U256,
    data: Vec<u8>,
}

struct Saved {
    storage: HashMap<U256, HashMap<U256, U256>>,
    codes: HashMap<U256, Rc<Vec<u8>>>,
    writes: usize,
    sent: usize,
}

#[derive(Default)]
pub struct World {
    codes: HashMap<U256, Rc<Vec<u8>>>,
    storage: HashMap<U256, HashMap<U256, U256>>,
    writes: Vec<Write>,
    sent: Vec<Sent>,
    origin: U256,
    budget: usize,
    made: u64,
}

impl World {
    pub fn new() -> World {
        World::default()
    }

    pub fn place(&mut self, address: U256, code: Vec<u8>) {
        self.codes.insert(address, Rc::new(code));
    }

    pub fn seed(&mut self, address: U256, slot: U256, value: U256) {
        self.storage.entry(address).or_default().insert(slot, value);
    }

    pub fn stored(&self, address: U256, slot: U256) -> U256 {
        self.storage
            .get(&address)
            .and_then(|slots| slots.get(&slot))
            .copied()
            .unwrap_or(U256::ZERO)
    }

    pub fn writes(&self) -> &[Write] {
        &self.writes
    }

    pub fn sent(&self) -> &[Sent] {
        &self.sent
    }

    pub fn was_made(&self, address: U256) -> bool {
        address.fits_u64() && (FIRST_MADE + 1..=FIRST_MADE + self.made).contains(&address.low_u64())
    }

    pub fn run(&mut self, address: U256, caller: U256, value: U256, data: Vec<u8>) -> bool {
        self.budget = BUDGET;
        self.writes.clear();
        self.sent.clear();
        self.made = 0;
        self.origin = caller;
        let Some(code) = self.codes.get(&address).cloned() else {
            return false;
        };
        let saved = self.save();
        let frame = Frame {
            account: address,
            caller,
            value,
            data,
        };
        let (success, _) = self.frame(&code, &frame, 0);
        if !success {
            self.restore(saved);
        }
        success
    }

    fn save(&self) -> Saved {
        Saved {
            storage: self.storage.clone(),
            codes: self.codes.clone(),
            writes: self.writes.len(),
            sent: self.sent.len(),
        }
    }

    fn restore(&mut self, saved: Saved) {
        self.storage = saved.storage;
        self.codes = saved.codes;
        self.writes.truncate(saved.writes);
        self.sent.truncate(saved.sent);
    }

    fn frame(&mut self, code: &[u8], frame: &Frame, depth: usize) -> (bool, Vec<u8>) {
        let jumpdests: HashSet<usize> = disasm::jumpdests(code).into_iter().collect();
        let mut host =
            Host::controlled(frame.account, frame.caller, frame.data.clone(), frame.value);
        host.origin = self.origin;
        host.intercept_calls = true;
        let mut m = Machine::new(code, &host);
        m.move_limit = Machine::LOOPED_MOVE_LIMIT;
        m.storage = self
            .storage
            .get(&frame.account)
            .cloned()
            .unwrap_or_default();
        let jump = |t: U256| t.as_usize().filter(|pc| jumpdests.contains(pc));
        let outcome = loop {
            if self.budget == 0 {
                break Outcome::Exception("step budget exhausted".into());
            }
            self.budget -= 1;
            let at = m.pc;
            let Some(opcode) = code.get(at).copied() else {
                break Outcome::Stop;
            };
            if let (op::SSTORE, [.., after, slot]) = (opcode, &m.stack[..]) {
                self.writes.push(Write {
                    address: frame.account,
                    slot: *slot,
                    before: m.sload(*slot),
                    after: *after,
                });
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
                Some(Outcome::JumpI(t, cond)) => match (cond.is_zero(), jump(t)) {
                    (true, _) => m.pc = at + 1,
                    (false, Some(pc)) => m.pc = pc,
                    (false, None) => break Outcome::Invalid,
                },
                Some(Outcome::Call(index)) => {
                    let record = m.calls[index].clone();
                    self.storage.insert(frame.account, m.storage.clone());
                    let (success, data) = self.call(&record, frame, depth);
                    m.storage = self
                        .storage
                        .get(&frame.account)
                        .cloned()
                        .unwrap_or_default();
                    if m.resume_after_call(index, success, data).is_err() {
                        break Outcome::Exception("call result does not fit".into());
                    }
                    m.pc = at + 1;
                }
                Some(Outcome::Create(index)) => {
                    let record = m.creates[index].clone();
                    self.storage.insert(frame.account, m.storage.clone());
                    let made = self.create(&record, frame, depth);
                    m.storage = self
                        .storage
                        .get(&frame.account)
                        .cloned()
                        .unwrap_or_default();
                    if m.resume_after_create(made).is_err() {
                        break Outcome::Exception("stack overflow".into());
                    }
                    m.pc = at + 1;
                }
                Some(other) => break other,
            }
        };
        match outcome {
            Outcome::Return(data) => {
                self.storage.insert(frame.account, m.storage);
                (true, data)
            }
            Outcome::Stop | Outcome::SelfDestruct(_) => {
                self.storage.insert(frame.account, m.storage);
                (true, Vec::new())
            }
            Outcome::Revert(data) => (false, data),
            _ => (false, Vec::new()),
        }
    }

    fn call(&mut self, record: &CallRecord, from: &Frame, depth: usize) -> (bool, Vec<u8>) {
        if record.addr == U256::from_u64(4) {
            return (true, record.input.clone());
        }
        let pays = record.kind == op::CALL;
        let payment = Sent {
            from: from.account,
            to: record.addr,
            value: record.value,
            input: record.input.iter().copied().take(SENT_INPUT).collect(),
        };
        let Some(code) = self.codes.get(&record.addr).cloned() else {
            self.sent.extend(pays.then_some(payment));
            return (true, Vec::new());
        };
        if depth >= MAX_DEPTH {
            return (true, Vec::new());
        }
        let data = record.input.clone();
        let inner = match record.kind {
            op::DELEGATECALL => Frame {
                account: from.account,
                caller: from.caller,
                value: from.value,
                data,
            },
            op::CALLCODE => Frame {
                account: from.account,
                caller: from.account,
                value: record.value,
                data,
            },
            _ => Frame {
                account: record.addr,
                caller: from.account,
                value: record.value,
                data,
            },
        };
        let saved = self.save();
        // Pushed after the save so a callee that fails takes the payment back with it.
        self.sent.extend(pays.then_some(payment));
        let (success, output) = self.frame(&code, &inner, depth + 1);
        if !success || record.kind == op::STATICCALL {
            self.restore(saved);
        }
        (success, output)
    }

    fn create(&mut self, record: &CreateRecord, from: &Frame, depth: usize) -> U256 {
        if depth >= MAX_DEPTH {
            return U256::ZERO;
        }
        let saved = self.save();
        self.made += 1;
        let address = U256::from_u64(FIRST_MADE + self.made);
        let inner = Frame {
            account: address,
            caller: from.account,
            value: record.value,
            data: Vec::new(),
        };
        let (success, runtime) = self.frame(&record.init, &inner, depth + 1);
        if !success {
            self.restore(saved);
            return U256::ZERO;
        }
        self.codes.insert(address, Rc::new(runtime));
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

    fn naming(slot: u8) -> Vec<u8> {
        let mut data = vec![0u8; 36];
        data[35] = slot;
        data
    }

    fn world(first: Vec<u8>, second: Vec<u8>) -> World {
        let mut world = World::new();
        world.place(FIRST, first);
        world.place(SECOND, second);
        world
    }

    #[test]
    fn a_call_writes_the_storage_of_the_contract_it_reaches() {
        let mut world = world(passes_on(op::CALL), stores_then(&[op::STOP]));
        assert!(world.run(FIRST, CALLER, U256::ZERO, naming(0x42)));
        assert_eq!(world.stored(SECOND, U256::from_u64(0x42)), U256::ONE);
        assert_eq!(world.stored(FIRST, U256::from_u64(0x42)), U256::ZERO);
        let expected = Write {
            address: SECOND,
            slot: U256::from_u64(0x42),
            before: U256::ZERO,
            after: U256::ONE,
        };
        assert_eq!(world.writes(), [expected]);
    }

    #[test]
    fn a_delegated_call_writes_the_storage_of_the_contract_that_made_it() {
        let mut world = world(passes_on(op::DELEGATECALL), stores_then(&[op::STOP]));
        assert!(world.run(FIRST, CALLER, U256::ZERO, naming(0x42)));
        assert_eq!(world.stored(FIRST, U256::from_u64(0x42)), U256::ONE);
        assert_eq!(world.stored(SECOND, U256::from_u64(0x42)), U256::ZERO);
    }

    #[test]
    fn a_call_that_fails_or_may_only_read_leaves_nothing_behind() {
        let reverts = [op::PUSH1, 0x00, op::PUSH1, 0x00, op::REVERT];
        let mut failing = world(passes_on(op::CALL), stores_then(&reverts));
        assert!(failing.run(FIRST, CALLER, U256::ZERO, naming(0x42)));
        assert_eq!(failing.stored(SECOND, U256::from_u64(0x42)), U256::ZERO);
        assert!(failing.writes().is_empty());

        let mut reading = world(passes_on(op::STATICCALL), stores_then(&[op::STOP]));
        assert!(reading.run(FIRST, CALLER, U256::ZERO, naming(0x42)));
        assert_eq!(reading.stored(SECOND, U256::from_u64(0x42)), U256::ZERO);
        assert!(reading.writes().is_empty());
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
        world.place(FIRST, creator);
        assert!(world.run(FIRST, CALLER, U256::ZERO, Vec::new()));
        let made = U256::from_u64(FIRST_MADE + 1);
        assert!(world.was_made(made));
        assert!(!world.was_made(FIRST));
        assert!(world.run(made, CALLER, U256::ZERO, naming(0x07)));
        assert_eq!(world.stored(made, U256::from_u64(0x07)), U256::ONE);
    }
}
