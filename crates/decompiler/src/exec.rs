use crate::disasm;
use crate::interp::{CallRecord, Host, LogRecord, Machine, Outcome};
use crate::u256::U256;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug)]
pub struct FrameRun {
    pub outcome: Outcome,
    pub visited: HashSet<usize>,
    pub steps: usize,
    pub storage: HashMap<U256, U256>,
    pub logs: Vec<LogRecord>,
    pub calls: Vec<CallRecord>,
}

impl FrameRun {
    #[must_use]
    pub fn reached(&self, pc: usize) -> bool {
        self.visited.contains(&pc)
    }

    #[must_use]
    pub fn succeeded(&self) -> bool {
        matches!(
            self.outcome,
            Outcome::Stop | Outcome::Return(_) | Outcome::SelfDestruct(_)
        )
    }
}

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

pub const CALLER: U256 = U256::from_u64(0xaaaa_aaaa_aaaa_aaaa);
pub const SELF: U256 = U256::from_u64(0xcccc_cccc_cccc_cccc);

pub fn caller_host(calldata: Vec<u8>, callvalue: U256) -> Host {
    Host::controlled(SELF, CALLER, calldata, callvalue)
}

pub const CANDIDATES: [U256; 5] = [
    U256::ZERO,
    CALLER,
    U256::ONE,
    U256::from_u64(1_000_000_000_000_000_000),
    U256::MAX,
];

// The order is fixed so a witness is reproducible.
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

pub fn selector_of(f: &crate::decompile::Function) -> Option<u32> {
    f.selector
        .as_deref()
        .and_then(|s| u32::from_str_radix(s.trim_start_matches("0x"), 16).ok())
}

fn jump_target(t: U256, jumpdests: &HashSet<usize>) -> Option<usize> {
    t.as_usize().filter(|pc| jumpdests.contains(pc))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hex;

    fn host(calldata: Vec<u8>) -> Host {
        Host::controlled(
            U256::from_u64(0xc0),
            U256::from_u64(0xa),
            calldata,
            U256::ZERO,
        )
    }

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
