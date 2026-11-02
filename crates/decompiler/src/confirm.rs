//! Confirming findings by reaching their sink.
//!
//! A static rule says a pattern is present; it cannot say the pattern is reachable. For the
//! findings whose whole claim is "an arbitrary caller reaches this sink" — an unprotected owner
//! write, an unguarded withdrawal, an open `selfdestruct`, an attacker-controlled delegatecall —
//! this pass tries to prove it: it runs the real dispatcher ([`crate::exec`]) from a fresh state
//! with the caller set to an account that holds no role, searching a small space of calldata,
//! and checks whether execution reaches the sink instruction. When it does, the finding carries
//! the calldata that got there and is marked confirmed; when it does not, nothing changes
//! (a bounded search finding no witness is not a proof of safety).

use crate::analyze::{display_name, Confidence, Finding};
use crate::decompile::{Contract, Function};
use crate::exec::{self, FrameRun};
use crate::function::FnKind;
use crate::hex;
use crate::interp::{CallRecord, Outcome};
use crate::opcode as op;
use crate::u256::U256;
use std::collections::HashMap;

/// Selector of `transferFrom(address,address,uint256)`.
const SEL_TRANSFER_FROM: u32 = 0x23b8_72dd;

/// Finding ids whose claim is exactly "an arbitrary caller reaches the sink from a fresh state".
/// For these a reached sink is a confirmation; other rules (reentrancy, which needs a seeded
/// balance; arithmetic, which is about values not reachability) are left untouched.
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

/// Steps a single run may take before it is abandoned (bounds loops).
const STEP_BUDGET: usize = 120_000;
/// Calldata shapes tried per finding before giving up.
const MAX_ATTEMPTS: usize = 200;
/// Ether sent in the second round of attempts, for sinks behind a payment.
const SOME_ETHER: U256 = U256::from_u64(100_000_000_000_000_000);

/// Appended to a confirmed finding's description.
const CONFIRMED_NOTE: &str = concat!(
    " Confirmed: a caller holding no role reaches this sink from a fresh state and the",
    " transaction keeps its effect (a reproducing input is attached)."
);

/// Try to confirm the reachable findings of `c` in place. Setting `EVMDEC_NO_CONFIRM` in the
/// environment skips the pass (the search runs the bytecode and costs time).
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
        // In a composite the function's code is its part's, run in the composite's storage as
        // `DELEGATECALL` would; the finding's pc is translated back into that code.
        let witness = reach(c.code_of(f), f, c.local_pc(f, pc), &finding.id);
        if let Some(witness) = witness {
            finding.confirmed = true;
            finding.witness = Some(hex::encode(&witness));
            finding.confidence = Confidence::High;
            finding.description.push_str(CONFIRMED_NOTE);
        }
    }
}

/// Search a small calldata space for an input under which `f`, called by the role-less account,
/// enters the block at `pc`, ends normally and shows the effect the rule `id` claims. Returns
/// the calldata on the first hit.
///
/// `pc` is an offset into `code` (a composite's finding pcs are translated first).
/// A finding's `pc` is the start of the block holding the sink, so entering it is necessary but
/// not sufficient: the block may still revert on a guard inlined ahead of the sink, and a frame
/// that reverts later undoes the write or the call. The run must therefore end normally and
/// leave the trace the claim is about ([`shows_effect`]).
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

/// Did the run leave the trace that the rule `id` claims a role-less caller can produce?
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
        // The claim is a normal return that did nothing: no write, no call, no event.
        "silent-auth-failure" => {
            run.storage.is_empty() && run.calls.is_empty() && run.logs.is_empty()
        }
        _ => false,
    }
}
