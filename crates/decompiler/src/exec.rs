//! Whole-frame concrete execution: run a contract from its entry, following jumps across blocks
//! until it halts or a step budget runs out.
//!
//! The oracle ([`crate::verify`]) runs one block at a time from a random state to check the
//! lifter. This module instead runs the whole frame from a chosen, controlled state
//! ([`Host::controlled`]), so a pass can ask a concrete question: does execution reach this
//! instruction under this input, and what does storage look like when it halts. It is the
//! substrate of the confirmation pass ([`crate::confirm`]) and the invariant checks.

use crate::disasm;
use crate::interp::{CallRecord, Host, LogRecord, Machine, Outcome};
use crate::u256::U256;
use std::collections::{HashMap, HashSet};

/// The result of running one frame to its end (or the budget).
#[derive(Clone, Debug)]
pub struct FrameRun {
    /// How the frame ended.
    pub outcome: Outcome,
    /// Program counters of every instruction executed (capped at the step budget).
    pub visited: HashSet<usize>,
    /// Instructions executed.
    pub steps: usize,
    /// Storage after the frame: keys written during it over the host's initial values.
    pub storage: HashMap<U256, U256>,
    /// Logs emitted, in order.
    pub logs: Vec<LogRecord>,
    /// External calls made, in order.
    pub calls: Vec<CallRecord>,
}

impl FrameRun {
    /// Did the frame execute the instruction at `pc`?
    #[must_use]
    pub fn reached(&self, pc: usize) -> bool {
        self.visited.contains(&pc)
    }

    /// Did the frame end without reverting or faulting?
    #[must_use]
    pub fn succeeded(&self) -> bool {
        matches!(
            self.outcome,
            Outcome::Stop | Outcome::Return(_) | Outcome::SelfDestruct(_)
        )
    }
}

/// Run `code` from offset 0 under `host`, with `init_storage` written before the first
/// instruction, following jumps for at most `budget` steps.
///
/// A jump to a target that is not a `JUMPDEST` halts the frame as the EVM would (`Invalid`); so
/// does running past the step budget (reported as an `Exception`), which bounds loops.
pub fn run_frame(
    code: &[u8],
    host: &Host,
    init_storage: &HashMap<U256, U256>,
    budget: usize,
) -> FrameRun {
    let jumpdests: HashSet<usize> = disasm::jumpdests(code).into_iter().collect();
    let mut m = Machine::new(code, host);
    m.storage = init_storage.clone();
    let mut visited = HashSet::new();
    let mut steps = 0;
    let outcome = loop {
        if steps >= budget {
            break Outcome::Exception("step budget exhausted".into());
        }
        if m.pc >= code.len() {
            break Outcome::Stop;
        }
        visited.insert(m.pc);
        steps += 1;
        let at = m.pc;
        match m.step() {
            Ok(None) => {}
            Ok(Some(Outcome::Jump(t))) => match jump_target(t, &jumpdests) {
                Some(pc) => m.pc = pc,
                None => break Outcome::Invalid,
            },
            Ok(Some(Outcome::JumpI(t, c))) => {
                if c.is_zero() {
                    m.pc = at + 1;
                } else {
                    match jump_target(t, &jumpdests) {
                        Some(pc) => m.pc = pc,
                        None => break Outcome::Invalid,
                    }
                }
            }
            Ok(Some(other)) => break other,
            Err(e) => break Outcome::Exception(e),
        }
    };
    FrameRun {
        outcome,
        visited,
        steps,
        storage: m.storage,
        logs: m.logs,
        calls: m.calls,
    }
}

/// A jump target as a code offset, when it names a `JUMPDEST`.
fn jump_target(t: U256, jumpdests: &HashSet<usize>) -> Option<usize> {
    t.as_usize().filter(|pc| jumpdests.contains(pc))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hex;

    /// `PUSH1 1 PUSH1 0 SSTORE` then a conditional loop and STOP, exercising jumps.
    #[test]
    fn runs_across_jumps_and_records_storage() {
        // slot0 = 1; if calldata[0..32] != 0 { slot1 = 2 } ; stop
        let code = hex::decode("6001600055600035156012576002600155005b00").expect("hex");
        // calldata zero: the branch is not taken, slot1 stays unset.
        let host = Host::controlled(
            U256::from_u64(0xc0),
            U256::from_u64(0xa),
            vec![],
            U256::ZERO,
        );
        let run = run_frame(&code, &host, &HashMap::new(), 10_000);
        assert!(run.succeeded(), "{:?}", run.outcome);
        assert_eq!(run.storage.get(&U256::ZERO), Some(&U256::ONE));
        assert_eq!(run.storage.get(&U256::ONE), None);

        // calldata non-zero: the branch runs, slot1 = 2.
        let host = Host::controlled(
            U256::from_u64(0xc0),
            U256::from_u64(0xa),
            vec![0xff; 32],
            U256::ZERO,
        );
        let run = run_frame(&code, &host, &HashMap::new(), 10_000);
        assert!(run.succeeded(), "{:?}", run.outcome);
        assert_eq!(run.storage.get(&U256::ONE), Some(&U256::from_u64(2)));
    }

    #[test]
    fn a_jump_to_a_non_jumpdest_halts() {
        // PUSH1 0x05 JUMP (0x05 is the data byte of the PUSH, not a JUMPDEST)
        let code = hex::decode("600556").expect("hex");
        let host = Host::controlled(
            U256::from_u64(0xc0),
            U256::from_u64(0xa),
            vec![],
            U256::ZERO,
        );
        let run = run_frame(&code, &host, &HashMap::new(), 10_000);
        assert!(matches!(run.outcome, Outcome::Invalid));
    }

    #[test]
    fn an_infinite_loop_stops_at_the_budget() {
        // JUMPDEST PUSH1 0x00 JUMP  (spins forever)
        let code = hex::decode("5b600056").expect("hex");
        let host = Host::controlled(
            U256::from_u64(0xc0),
            U256::from_u64(0xa),
            vec![],
            U256::ZERO,
        );
        let run = run_frame(&code, &host, &HashMap::new(), 500);
        assert!(matches!(run.outcome, Outcome::Exception(_)));
        assert_eq!(run.steps, 500);
    }
}
