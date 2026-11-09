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
    /// Storage after the frame: `init_storage` plus every key written during it. Keys never
    /// written do not appear (a controlled host reads them as zero).
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
    init_storage: HashMap<U256, U256>,
    budget: usize,
) -> FrameRun {
    let jumpdests: HashSet<usize> = disasm::jumpdests(code).into_iter().collect();
    let mut m = Machine::new(code, host);
    m.storage = init_storage;
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

/// The account whose reach is tested: a non-zero address holding no role in a fresh contract.
pub const CALLER: U256 = U256::from_u64(0xaaaa_aaaa_aaaa_aaaa);
/// The executing contract's own address in a controlled run.
pub const SELF: U256 = U256::from_u64(0xcccc_cccc_cccc_cccc);

/// A controlled host for a run by [`CALLER`] against [`SELF`] with `calldata` and `callvalue`.
pub fn caller_host(calldata: Vec<u8>, callvalue: U256) -> Host {
    Host::controlled(SELF, CALLER, calldata, callvalue)
}

/// Values tried in each calldata argument slot: zero, the caller's own address (for `to` and
/// `owner` parameters), one, a round ether amount and the all-ones word.
pub const CANDIDATES: [U256; 5] = [
    U256::ZERO,
    CALLER,
    U256::ONE,
    U256::from_u64(1_000_000_000_000_000_000),
    U256::MAX,
];

/// The argument vectors tried for a function of `nargs` words, cheapest first: every argument
/// the same candidate, then one argument varied with the rest zero (reaches guards keyed on a
/// single parameter). The order is fixed so a witness is reproducible.
pub fn arg_shapes(nargs: usize) -> Vec<Vec<U256>> {
    let mut shapes: Vec<Vec<U256>> = CANDIDATES.iter().map(|c| vec![*c; nargs]).collect();
    for pos in 0..nargs {
        for cand in CANDIDATES {
            let mut args = vec![U256::ZERO; nargs];
            args[pos] = cand;
            shapes.push(args);
        }
    }
    shapes
}

/// `selector ++ args` as ABI-style calldata, each argument one 32-byte word.
pub fn calldata(selector: Option<u32>, args: &[U256]) -> Vec<u8> {
    let mut data = Vec::with_capacity(4 + 32 * args.len());
    if let Some(sel) = selector {
        data.extend_from_slice(&sel.to_be_bytes());
    }
    for a in args {
        data.extend_from_slice(&a.to_be_bytes());
    }
    data
}

/// The 4-byte selector of `f` as a number, when it has one.
pub fn selector_of(f: &crate::decompile::Function) -> Option<u32> {
    f.selector
        .as_deref()
        .and_then(|s| u32::from_str_radix(s.trim_start_matches("0x"), 16).ok())
}

/// A jump target as a code offset, when it names a `JUMPDEST`.
fn jump_target(t: U256, jumpdests: &HashSet<usize>) -> Option<usize> {
    t.as_usize().filter(|pc| jumpdests.contains(pc))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hex;

    /// A controlled host with `calldata` and no value.
    fn host(calldata: Vec<u8>) -> Host {
        Host::controlled(
            U256::from_u64(0xc0),
            U256::from_u64(0xa),
            calldata,
            U256::ZERO,
        )
    }

    /// `slot0 = 1; if calldata[0..32] != 0 { slot1 = 2 }; stop`: a forward conditional branch.
    #[test]
    fn runs_across_jumps_and_records_storage() {
        let code = hex::decode("6001600055600035156012576002600155005b00").expect("hex");
        let run = run_frame(&code, &host(vec![]), HashMap::new(), 10_000);
        assert!(run.succeeded(), "{:?}", run.outcome);
        assert_eq!(run.storage.get(&U256::ZERO), Some(&U256::ONE));
        assert_eq!(run.storage.get(&U256::ONE), None);

        let run = run_frame(&code, &host(vec![0xff; 32]), HashMap::new(), 10_000);
        assert!(run.succeeded(), "{:?}", run.outcome);
        assert_eq!(run.storage.get(&U256::ONE), Some(&U256::from_u64(2)));
    }

    #[test]
    fn a_jump_to_a_non_jumpdest_halts() {
        let code = hex::decode("600156").expect("hex");
        let run = run_frame(&code, &host(vec![]), HashMap::new(), 10_000);
        assert!(matches!(run.outcome, Outcome::Invalid));
    }

    #[test]
    fn an_infinite_loop_stops_at_the_budget() {
        let code = hex::decode("5b600056").expect("hex");
        let run = run_frame(&code, &host(vec![]), HashMap::new(), 500);
        assert!(matches!(run.outcome, Outcome::Exception(_)));
        assert_eq!(run.steps, 500);
    }
}
