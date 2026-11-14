use crate::abi::{SEL_BALANCE_OF, SEL_TRANSFER, SEL_TRANSFER_FROM};
use crate::decompile::{Contract, Function};
use crate::deploy;
use crate::disasm;
use crate::exec;
use crate::interp::{CallRecord, Host, Machine, Outcome};
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
const STEPS_PER_CALL: usize = 200_000;
// The slots a call touched say which calls depend on which. A few hundred say it as
// well as thousands, and a set of thousands costs more to keep than the call to run.
const MAX_KEYS: usize = 256;
// What every account starts with, in ether and in each asset. Large enough to pay for
// any call, and far from the top so that sums stay in range.
pub const PURSE: U256 = U256([0, 0, 1 << 32, 0]);

#[derive(Clone, Debug)]
pub struct Call {
    pub who: U256,
    pub data: Vec<u8>,
    pub value: U256,
    pub seconds_later: u64,
}

// What one account holds: ether, each outside asset it touched, and what the contract
// itself reports for it when the contract keeps balances.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Holdings {
    pub ether: U256,
    pub assets: BTreeMap<U256, U256>,
    pub reported: Option<U256>,
}

#[derive(Clone, Debug, Default)]
pub struct Done {
    pub ended: bool,
    pub branches: BTreeSet<(usize, bool)>,
    pub read: BTreeSet<U256>,
    pub written: BTreeSet<U256>,
    pub crossed: bool,
}

// The contract under test with everything around it that a call can touch: who holds
// how much ether, who holds how much of each asset, and what time it is. A call either
// ends and changes the world, or fails and leaves it as it was. Assets are any address
// the contract speaks the standard transfer interface to. They keep honest books, so
// what the contract is told it holds is what was really sent to it.
#[derive(Clone)]
pub struct World<'a> {
    c: &'a Contract,
    jumpdests: Rc<HashMap<usize, HashSet<usize>>>,
    storage: HashMap<U256, U256>,
    ether: HashMap<U256, U256>,
    assets: HashMap<(U256, U256), U256>,
    accounts: Vec<U256>,
    timestamp: U256,
    number: U256,
}

struct Frame<'w, 'a> {
    world: &'w mut World<'a>,
    caller: U256,
    crossed: bool,
}

fn selector(input: &[u8]) -> Option<u32> {
    let b = input.get(..4)?;
    Some(u32::from_be_bytes([b[0], b[1], b[2], b[3]]))
}

fn one_word(value: U256) -> Vec<u8> {
    value.to_be_bytes().to_vec()
}

impl<'a> World<'a> {
    pub fn new(c: &'a Contract, accounts: &[U256]) -> World<'a> {
        let mut codes: Vec<&[u8]> = c.functions.iter().map(|f| c.code_of(f)).collect();
        codes.dedup_by_key(|code| code.as_ptr());
        let jumpdests = codes
            .into_iter()
            .map(|code| {
                (
                    code.as_ptr() as usize,
                    disasm::jumpdests(code).into_iter().collect(),
                )
            })
            .collect();
        World {
            c,
            jumpdests: Rc::new(jumpdests),
            storage: deploy::start(c),
            ether: HashMap::new(),
            assets: HashMap::new(),
            accounts: accounts.to_vec(),
            timestamp: U256::from_u64(1_700_000_000),
            number: U256::from_u64(18_000_000),
        }
    }

    pub fn storage(&self) -> &HashMap<U256, U256> {
        &self.storage
    }

    pub fn time(&self) -> (U256, U256) {
        (self.timestamp, self.number)
    }

    pub fn holds_value(&self) -> bool {
        let this = exec::SELF;
        let asset =
            |((_, holder), amount): (&(U256, U256), &U256)| *holder == this && !amount.is_zero();
        !self.ether_of(this).is_zero() || self.assets.iter().any(asset)
    }

    fn ether_of(&self, who: U256) -> U256 {
        let start = match self.accounts.contains(&who) {
            true => PURSE,
            false => U256::ZERO,
        };
        self.ether.get(&who).copied().unwrap_or(start)
    }

    fn asset_of(&self, asset: U256, who: U256) -> U256 {
        let start = match self.accounts.contains(&who) {
            true => PURSE,
            false => U256::ZERO,
        };
        self.assets.get(&(asset, who)).copied().unwrap_or(start)
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
        let asked = |f: &&Function| exec::selector_of(f) == Some(SEL_BALANCE_OF);
        let f = self.c.functions.iter().find(asked)?;
        let mut aside = self.clone();
        let call = Call {
            who,
            data: exec::calldata(Some(SEL_BALANCE_OF), &[who]),
            value: U256::ZERO,
            seconds_later: 0,
        };
        let (outcome, _) = aside.frame(f, &call);
        match outcome {
            Outcome::Return(data) if data.len() >= 32 => Some(word(&data, 0)),
            _ => None,
        }
    }

    pub fn call(&mut self, f: &Function, call: &Call) -> Done {
        // A world is copied to try a call and copied again by whoever keeps the result.
        // With thousands of stored slots that costs more than running the call.
        exec::spend(2 * (self.storage.len() + self.assets.len()) as u64);
        let before = self.clone();
        let later = U256::from_u64(call.seconds_later);
        self.timestamp = self.timestamp.wrapping_add(later);
        self.number = self
            .number
            .wrapping_add(U256::from_u64(call.seconds_later / 12));
        let paid = self.ether_of(call.who);
        if paid < call.value {
            *self = before;
            return Done::default();
        }
        self.ether.insert(call.who, paid - call.value);
        let held = self.ether_of(exec::SELF);
        self.ether.insert(
            exec::SELF,
            held.checked_add(call.value).unwrap_or(U256::MAX),
        );
        let (outcome, mut done) = self.frame(f, call);
        done.ended = matches!(outcome, Outcome::Stop | Outcome::Return(_));
        done.crossed |= !call.value.is_zero();
        if !done.ended {
            *self = before;
        }
        done
    }

    fn frame(&mut self, f: &Function, call: &Call) -> (Outcome, Done) {
        let c = self.c;
        let code = c.code_of(f);
        let jumpdests = self.jumpdests.clone();
        let none = HashSet::new();
        let dests = jumpdests.get(&(code.as_ptr() as usize)).unwrap_or(&none);
        let mut host = Host::controlled(exec::SELF, call.who, call.data.clone(), call.value);
        host.intercept_calls = true;
        host.spends_balance = true;
        host.selfbalance = self.ether_of(exec::SELF);
        host.timestamp = self.timestamp;
        host.number = self.number;
        let mut m = Machine::new(code, &host);
        m.move_limit = Machine::LOOPED_MOVE_LIMIT;
        m.storage = std::mem::take(&mut self.storage);
        let mut done = Done::default();
        let mut frame = Frame {
            world: self,
            caller: call.who,
            crossed: false,
        };
        let jump = |t: U256| t.as_usize().filter(|pc| dests.contains(pc));
        let mut steps = 0;
        let outcome = loop {
            steps += 1;
            if steps > STEPS_PER_CALL {
                break Outcome::Exception("step limit".into());
            }
            let at = m.pc;
            let Some(opcode) = code.get(at).copied() else {
                break Outcome::Stop;
            };
            match (opcode, m.stack.last()) {
                (op::SLOAD, Some(key)) if done.read.len() < MAX_KEYS => {
                    done.read.insert(*key);
                }
                (op::SSTORE, Some(key)) if done.written.len() < MAX_KEYS => {
                    done.written.insert(*key);
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
                    done.branches.insert((at, !cond.is_zero()));
                    match (cond.is_zero(), jump(t)) {
                        (true, _) => m.pc = at + 1,
                        (false, Some(pc)) => m.pc = pc,
                        (false, None) => break Outcome::Invalid,
                    }
                }
                Some(Outcome::Call(index)) => {
                    let (success, data) = frame.answer(&m.calls[index]);
                    if m.resume_after_call(index, success, data).is_err() {
                        break Outcome::Exception("call result does not fit".into());
                    }
                    m.pc = at + 1;
                }
                Some(Outcome::Create(_)) => {
                    if m.resume_after_create(U256::ZERO).is_err() {
                        break Outcome::Exception("stack overflow".into());
                    }
                    m.pc = at + 1;
                }
                Some(other) => break other,
            }
        };
        exec::spend(steps as u64);
        done.crossed = frame.crossed;
        self.storage = std::mem::take(&mut m.storage);
        (outcome, done)
    }
}

impl Frame<'_, '_> {
    // An asset answers from its books. Anything else answers one word that reads as
    // true, which is what a call that went well most often returns.
    fn answer(&mut self, call: &CallRecord) -> (bool, Vec<u8>) {
        let this = exec::SELF;
        if call.addr == U256::from_u64(IDENTITY) {
            return (true, call.input.clone());
        }
        if call.kind == op::CALL && !call.value.is_zero() {
            let held = self.world.ether_of(this);
            self.world.ether.insert(this, held.wrapping_sub(call.value));
            let had = self.world.ether_of(call.addr);
            let now = had.checked_add(call.value).unwrap_or(U256::MAX);
            self.world.ether.insert(call.addr, now);
            self.crossed |= call.addr == self.caller;
        }
        let arg = |index: usize| word(&call.input, 4 + 32 * index);
        let changes = call.kind == op::CALL;
        let yes = (true, one_word(U256::ONE));
        match selector(&call.input) {
            Some(SEL_TRANSFER) if changes && call.input.len() >= 68 => {
                let moved = self.world.moves(call.addr, this, arg(0), arg(1));
                self.crossed |= moved && arg(0) == self.caller;
                (moved, one_word(U256::from(moved)))
            }
            Some(SEL_TRANSFER_FROM) if changes && call.input.len() >= 100 => {
                // An account lets the contract it calls take what the call asks for. No
                // account lets it take from another.
                let allowed = arg(0) == self.caller || arg(0) == this;
                let moved = allowed && self.world.moves(call.addr, arg(0), arg(1), arg(2));
                self.crossed |= moved && (arg(0) == self.caller || arg(1) == self.caller);
                (moved, one_word(U256::from(moved)))
            }
            Some(SEL_BALANCE_OF) if call.input.len() >= 36 => {
                (true, one_word(self.world.asset_of(call.addr, arg(0))))
            }
            Some(SEL_ALLOWANCE) => (true, one_word(U256::MAX)),
            Some(SEL_DECIMALS) => (true, one_word(U256::from_u64(DECIMALS))),
            Some(SEL_TOTAL_SUPPLY) => (true, one_word(PURSE)),
            Some(SEL_APPROVE) => yes,
            _ => yes,
        }
    }
}
