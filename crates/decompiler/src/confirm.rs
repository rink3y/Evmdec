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
use crate::exec;
use crate::function::FnKind;
use crate::hex;
use crate::interp::Host;
use crate::u256::U256;
use std::collections::HashMap;

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
/// Attacker account: a non-zero address that holds no role in a fresh contract.
const ATTACKER: u64 = 0xaaaa_aaaa_aaaa_aaaa;
/// The executing contract's own address.
const SELF: u64 = 0xcccc_cccc_cccc_cccc;

/// Try to confirm the reachable findings of `c` in place.
pub fn confirm(c: &Contract, findings: &mut [Finding]) {
    if std::env::var("EVMDEC_NO_CONFIRM").is_ok() {
        return;
    }
    let code = &c.info.runtime;
    if code.is_empty() {
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
        if let Some(witness) = reach(code, f, pc) {
            finding.confirmed = true;
            finding.witness = Some(hex::encode(&witness));
            finding.confidence = Confidence::High;
            finding
                .description
                .push_str(" Confirmed: an arbitrary caller reaches this sink from a fresh state (a reproducing input is attached).");
        }
    }
}

/// Values tried in each calldata argument slot.
fn candidates() -> [U256; 5] {
    [
        U256::ZERO,
        U256::from_u64(ATTACKER),
        U256::ONE,
        U256::from_u64(1_000_000_000_000_000_000),
        U256::MAX,
    ]
}

/// Search a small calldata space for an input that reaches `pc` in `f`, as the attacker. Returns
/// the calldata on the first hit.
fn reach(code: &[u8], f: &Function, pc: usize) -> Option<Vec<u8>> {
    let selector = f
        .selector
        .as_deref()
        .and_then(|s| u32::from_str_radix(s.trim_start_matches("0x"), 16).ok());
    let cands = candidates();
    let mut attempts = 0;
    for callvalue in [U256::ZERO, U256::from_u64(100_000_000_000_000_000)] {
        for nargs in 0..=6usize {
            // Uniform fillings: every argument the same candidate.
            for cand in cands {
                if try_calldata(
                    code,
                    selector,
                    &vec![cand; nargs],
                    callvalue,
                    pc,
                    &mut attempts,
                ) {
                    return Some(calldata(selector, &vec![cand; nargs]));
                }
            }
            // One argument varied, the rest zero: reaches guards keyed on a single parameter.
            for pos in 0..nargs {
                for cand in cands {
                    let mut args = vec![U256::ZERO; nargs];
                    args[pos] = cand;
                    if try_calldata(code, selector, &args, callvalue, pc, &mut attempts) {
                        return Some(calldata(selector, &args));
                    }
                }
            }
        }
    }
    None
}

/// Run one calldata shape and report whether it reached `pc`; counts against the attempt cap.
fn try_calldata(
    code: &[u8],
    selector: Option<u32>,
    args: &[U256],
    callvalue: U256,
    pc: usize,
    attempts: &mut usize,
) -> bool {
    if *attempts >= MAX_ATTEMPTS {
        return false;
    }
    *attempts += 1;
    let data = calldata(selector, args);
    let host = Host::controlled(
        U256::from_u64(SELF),
        U256::from_u64(ATTACKER),
        data,
        callvalue,
    );
    exec::run_frame(code, &host, &HashMap::new(), STEP_BUDGET).reached(pc)
}

/// `selector ++ args` as ABI-style calldata (each argument one 32-byte word).
fn calldata(selector: Option<u32>, args: &[U256]) -> Vec<u8> {
    let mut data = Vec::new();
    if let Some(sel) = selector {
        data.extend_from_slice(&sel.to_be_bytes());
    }
    for a in args {
        data.extend_from_slice(&a.to_be_bytes());
    }
    data
}
