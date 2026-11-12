//! Running a transaction across several contracts.
//!
//! [`crate::exec`] runs one frame and answers external calls from a seed, so it can confirm a
//! finding whose whole claim is reachability inside one contract. A composed finding spans a
//! call edge: a function of one contract passes a caller-named account to a function of another
//! that lowers that account's entry. To confirm it, the call has to really run — the callee's
//! own code, in the callee's own storage — so the account the caller chose reaches the store.
//!
//! This module holds a [`World`] of contracts by address and runs a transaction through it,
//! following `CALL` and `STATICCALL` into another contract of the world and executing it as a
//! nested frame against that contract's persistent storage. Calls out of the world, and the
//! other call kinds, fall back to the seed. The confirmation pass ([`crate::analyze`]) runs one
//! function twice, with two different accounts in the forwarded word, and confirms the finding
//! when the store the nested frame makes tracks the account.

use crate::disasm;
use crate::exec;
use crate::interp::{Host, Machine, Outcome};
use crate::u256::U256;
use std::collections::{HashMap, HashSet};

/// Steps one transaction may take across every frame before it is abandoned.
const BUDGET: usize = 400_000;
/// Nested calls deep the driver follows before it stops entering new frames.
const MAX_DEPTH: usize = 6;

/// The contracts a transaction can reach, by address, each with its own persistent storage.
pub struct World {
    /// Runtime code by address.
    codes: HashMap<U256, Vec<u8>>,
    /// Storage by address, carried across the whole transaction.
    storage: HashMap<U256, HashMap<U256, U256>>,
    /// Steps left in the transaction.
    budget: usize,
}

/// What one contract's storage did during a run: every slot written, with its final value.
pub type Writes = HashMap<U256, U256>;

impl World {
    /// An empty world.
    pub fn new() -> World {
        World {
            codes: HashMap::new(),
            storage: HashMap::new(),
            budget: BUDGET,
        }
    }

    /// Place `code` at `address`.
    pub fn place(&mut self, address: U256, code: Vec<u8>) {
        self.codes.insert(address, code);
    }

    /// Write `value` into `address`'s storage at `slot` before the transaction runs.
    pub fn seed(&mut self, address: U256, slot: U256, value: U256) {
        self.storage.entry(address).or_default().insert(slot, value);
    }

    /// The slots `address` holds, as written so far.
    pub fn storage_of(&self, address: U256) -> HashMap<U256, U256> {
        self.storage.get(&address).cloned().unwrap_or_default()
    }

    /// Run a transaction from `caller` to `address` with `calldata` and `callvalue`, following
    /// calls between contracts of the world. Returns whether the outermost frame ended normally.
    pub fn run(&mut self, address: U256, caller: U256, callvalue: U256, calldata: Vec<u8>) -> bool {
        self.budget = BUDGET;
        self.frame(address, caller, callvalue, calldata, 0).0
    }

    /// Run the frame at `address`, called by `caller`. Returns `(success, return data)`.
    fn frame(
        &mut self,
        address: U256,
        caller: U256,
        callvalue: U256,
        calldata: Vec<u8>,
        depth: usize,
    ) -> (bool, Vec<u8>) {
        let Some(code) = self.codes.get(&address).cloned() else {
            return (false, Vec::new());
        };
        let jumpdests: HashSet<usize> = disasm::jumpdests(&code).into_iter().collect();
        let mut host = Host::controlled(address, caller, calldata, callvalue);
        host.intercept_calls = true;
        let mut m = Machine::new(&code, &host);
        m.storage = self.storage_of(address);
        let outcome = loop {
            if self.budget == 0 {
                break Outcome::Exception("budget".into());
            }
            self.budget -= 1;
            if m.pc >= code.len() {
                break Outcome::Stop;
            }
            let at = m.pc;
            match m.step() {
                Ok(None) => {}
                Ok(Some(Outcome::Jump(t))) => match target(t, &jumpdests) {
                    Some(pc) => m.pc = pc,
                    None => break Outcome::Invalid,
                },
                Ok(Some(Outcome::JumpI(t, c))) => {
                    if c.is_zero() {
                        m.pc = at + 1;
                    } else {
                        match target(t, &jumpdests) {
                            Some(pc) => m.pc = pc,
                            None => break Outcome::Invalid,
                        }
                    }
                }
                Ok(Some(Outcome::Call(idx))) => {
                    let (success, data) = self.resolve(&m.calls[idx], address, depth);
                    if m.resume_after_call(idx, success, data).is_err() {
                        break Outcome::Exception("resume".into());
                    }
                    m.pc = at + 1;
                }
                Ok(Some(other)) => break other,
                Err(e) => break Outcome::Exception(e),
            }
        };
        let success = matches!(
            outcome,
            Outcome::Stop | Outcome::Return(_) | Outcome::SelfDestruct(_)
        );
        if success {
            self.storage.insert(address, m.storage);
        }
        let data = match outcome {
            Outcome::Return(d) | Outcome::Revert(d) => d,
            _ => Vec::new(),
        };
        (success, data)
    }

    /// Resolve one call: run the callee across the world for `CALL`/`STATICCALL` into another of
    /// its contracts, otherwise fall back to a seed-derived answer.
    fn resolve(
        &mut self,
        rec: &crate::interp::CallRecord,
        from: U256,
        depth: usize,
    ) -> (bool, Vec<u8>) {
        use crate::opcode as op;
        if rec.addr == U256::from_u64(4) {
            return (true, rec.input.clone());
        }
        let followable = matches!(rec.kind, op::CALL | op::STATICCALL);
        if followable && depth < MAX_DEPTH && self.codes.contains_key(&rec.addr) {
            let saved = (rec.kind == op::STATICCALL).then(|| self.storage_of(rec.addr));
            let out = self.frame(rec.addr, from, rec.value, rec.input.clone(), depth + 1);
            if let Some(saved) = saved {
                self.storage.insert(rec.addr, saved);
            }
            return out;
        }
        (true, Vec::new())
    }
}

impl Default for World {
    fn default() -> World {
        World::new()
    }
}

/// A jump target as a code offset, when it names a `JUMPDEST`.
fn target(t: U256, jumpdests: &HashSet<usize>) -> Option<usize> {
    let pc = t.as_usize()?;
    jumpdests.contains(&pc).then_some(pc)
}

/// Two distinct accounts, neither the role-less caller nor zero, to put in a forwarded word so a
/// store that tracks the account can be told from one that does not.
pub const VICTIMS: [U256; 2] = [
    U256::from_u64(0x1111_2222_3333_4444),
    U256::from_u64(0x5555_6666_7777_8888),
];

/// The calldata `exec::calldata` builds, with `word` overwritten by `account`.
pub fn calldata_naming(selector: Option<u32>, nargs: usize, word: u32, account: U256) -> Vec<u8> {
    let mut args = vec![U256::ZERO; nargs.max(word as usize + 1)];
    args[word as usize] = account;
    exec::calldata(selector, &args)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::opcode as op;

    fn asm(ops: &[u8]) -> Vec<u8> {
        ops.to_vec()
    }

    #[test]
    fn a_call_runs_the_callee_in_its_own_storage() {
        // Callee: store calldata word 0 (the account) as the key of slot and write 1 there.
        // PUSH1 0x01 PUSH1 0x04 CALLDATALOAD SSTORE STOP
        let callee = asm(&[
            op::PUSH1,
            0x01,
            op::PUSH1,
            0x04,
            op::CALLDATALOAD,
            op::SSTORE,
            op::STOP,
        ]);
        // Caller: CALL callee with 36 bytes of our own calldata as input (copy calldata to mem).
        // CALLDATASIZE PUSH1 0 PUSH1 0 CALLDATACOPY  then CALL(gas, callee, 0, 0, size, 0, 0)
        let callee_addr: u64 = 0xbbbb;
        // Copy our calldata to memory 0, then CALL(gas, callee, 0, argsOff=0, argsLen=size,
        // retOff=0, retLen=0). CALL pops gas, addr, value, argsOff, argsLen, retOff, retLen, so
        // they are pushed in reverse (retLen first, gas last).
        let mut code = vec![
            op::CALLDATASIZE,
            op::PUSH1,
            0x00,
            op::PUSH1,
            0x00,
            op::CALLDATACOPY,
        ];
        code.extend_from_slice(&[op::PUSH1, 0x00]); // retLen
        code.extend_from_slice(&[op::PUSH1, 0x00]); // retOff
        code.push(op::CALLDATASIZE); // argsLen
        code.extend_from_slice(&[op::PUSH1, 0x00]); // argsOff
        code.extend_from_slice(&[op::PUSH1, 0x00]); // value
        code.push(op::PUSH1 + 7); // addr
        code.extend_from_slice(&callee_addr.to_be_bytes());
        code.extend_from_slice(&[op::GAS, op::CALL, op::STOP]);

        let mut world = World::new();
        world.place(U256::from_u64(0xaaaa), code);
        world.place(U256::from_u64(callee_addr), callee);
        let mut data = vec![0u8; 36];
        data[35] = 0x42;
        assert!(world.run(U256::from_u64(0xaaaa), U256::from_u64(1), U256::ZERO, data));
        let callee_storage = world.storage_of(U256::from_u64(callee_addr));
        assert_eq!(callee_storage.get(&U256::from_u64(0x42)), Some(&U256::ONE));
    }
}
