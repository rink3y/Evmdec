use crate::analyze::{display_name, Confidence, Finding};
use crate::decompile::{Contract, Function};
use crate::exec::{self, FrameRun};
use crate::function::FnKind;
use crate::hex;
use crate::interp::{CallRecord, Outcome};
use crate::opcode as op;
use crate::u256::U256;
use std::collections::HashMap;

const SEL_TRANSFER_FROM: u32 = 0x23b8_72dd;

// Only rules whose whole claim is reachability from a fresh state.
// Reentrancy needs a seeded balance and arithmetic is about values.
const CONFIRMABLE: &[&str] = &[
    "unprotected-ether-withdrawal",
    "unprotected-owner-write",
    "unprotected-initializer",
    "unprotected-upgrade",
    "arbitrary-call",
    "arbitrary-delegatecall",
    "delegatecall-user-target",
    "delegatecall-dynamic-target",
    "arbitrary-transferfrom",
    "selfdestruct",
    "silent-auth-failure",
];

const STEP_BUDGET: usize = 120_000;
const MAX_ATTEMPTS: usize = 200;
const SOME_ETHER: U256 = U256::from_u64(100_000_000_000_000_000);

const CONFIRMED_NOTE: &str = concat!(
    " Confirmed: a caller holding no role reaches this sink from a fresh state and the",
    " transaction keeps its effect (a reproducing input is attached)."
);

pub fn confirm(c: &Contract, findings: &mut [Finding]) {
    if std::env::var("EVMDEC_NO_CONFIRM").is_ok() {
        return;
    }
    if c.info.runtime.is_empty() {
        return;
    }
    for finding in findings.iter_mut() {
        if finding.confirmed || !CONFIRMABLE.contains(&finding.id.as_str()) {
            continue;
        }
        let (Some(pc), Some(name)) = (finding.pc, finding.function.as_deref()) else {
            continue;
        };
        let Some(f) = c
            .functions
            .iter()
            .find(|f| f.kind == FnKind::External && display_name(f) == name)
        else {
            continue;
        };
        let witness = reach(c.code_of(f), f, c.local_pc(f, pc), &finding.id);
        if let Some(witness) = witness {
            finding.confirmed = true;
            finding.witness = Some(hex::encode(&witness));
            finding.confidence = Confidence::High;
            finding.description.push_str(CONFIRMED_NOTE);
        }
    }
}

// Entering the sink's block is not enough.
// A guard ahead of the sink or a later revert undoes the effect.
// So the run must end normally and show it.
fn reach(code: &[u8], f: &Function, pc: usize, id: &str) -> Option<Vec<u8>> {
    let selector = exec::selector_of(f);
    let mut attempts = 0;
    for callvalue in [U256::ZERO, SOME_ETHER] {
        for nargs in 0..=6usize {
            for args in exec::arg_shapes(nargs) {
                if attempts >= MAX_ATTEMPTS {
                    return None;
                }
                attempts += 1;
                let data = exec::calldata(selector, &args);
                let host = exec::caller_host(data.clone(), callvalue);
                let run = exec::run_frame(code, &host, HashMap::new(), STEP_BUDGET);
                if run.reached(pc) && run.succeeded() && shows_effect(id, &run) {
                    return Some(data);
                }
            }
        }
    }
    None
}

fn shows_effect(id: &str, run: &FrameRun) -> bool {
    let call_of = |pred: &dyn Fn(&CallRecord) -> bool| run.calls.iter().any(pred);
    match id {
        "selfdestruct" => matches!(run.outcome, Outcome::SelfDestruct(_)),
        "unprotected-ether-withdrawal" => call_of(&|c| c.kind == op::CALL && !c.value.is_zero()),
        "arbitrary-call" => call_of(&|c| matches!(c.kind, op::CALL | op::CALLCODE)),
        "arbitrary-delegatecall" | "delegatecall-user-target" | "delegatecall-dynamic-target" => {
            call_of(&|c| c.kind == op::DELEGATECALL)
        }
        "arbitrary-transferfrom" => {
            call_of(&|c| c.input.starts_with(&SEL_TRANSFER_FROM.to_be_bytes()))
        }
        "unprotected-owner-write" | "unprotected-initializer" | "unprotected-upgrade" => {
            !run.storage.is_empty()
        }
        "silent-auth-failure" => {
            run.storage.is_empty() && run.calls.is_empty() && run.logs.is_empty()
        }
        _ => false,
    }
}
