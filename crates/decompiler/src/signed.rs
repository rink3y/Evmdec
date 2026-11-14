use crate::abi;
use crate::analyze::{push, Confidence, Finding, Severity};
use crate::decompile::{Contract, Function};
use crate::deploy;
use crate::exec;
use crate::function::FnKind;
use crate::opcode as op;
use crate::path::{self, Explorer, Explorers, Limits, Path};
use crate::solve::{Free, Inputs};
use crate::u256::U256;
use std::collections::HashMap;

const LIMITS: Limits = Limits {
    paths: 16,
    runs: 64,
};
const WORDS: usize = 12;
const MAX_FUNCTIONS: usize = 32;
pub const WORK: u64 = 3 * exec::WORK_PER_SECOND;
const RECOVER: U256 = U256::ONE;
const SIGNER: U256 = U256::from_u64(0x5167_5167_5167_5167);
const FIRST_ACCOUNT: u64 = 0x12;

fn outside(addr: U256) -> bool {
    !addr.fits_u64() || addr.low_u64() >= FIRST_ACCOUNT || addr.is_zero()
}

fn acts(p: &Path) -> bool {
    let calls_out =
        p.run.calls.iter().any(|c| {
            matches!(c.kind, op::CALL | op::CALLCODE | op::DELEGATECALL) && outside(c.addr)
        });
    calls_out || p.run.storage != p.inputs.storage
}

fn moves_value(p: &Path) -> bool {
    p.run.calls.iter().any(|c| {
        let sends = c.kind == op::CALL && !c.value.is_zero();
        let selector = c.input.get(..4);
        let transfers = selector == Some(&[0xa9, 0x05, 0x9c, 0xbb][..])
            || selector == Some(&[0x23, 0xb8, 0x72, 0xdd][..]);
        outside(c.addr) && (sends || transfers)
    })
}

fn digest_of(p: &Path) -> Option<Vec<u8>> {
    let recovery = p.run.calls.iter().find(|c| c.addr == RECOVER)?;
    recovery.input.get(..32).map(<[u8]>::to_vec)
}

fn start_for(f: &Function, begin: &HashMap<U256, U256>) -> (Inputs, Free) {
    let selector = exec::selector_of(f);
    let types: Vec<String> = f.params.iter().map(|p| p.ty.clone()).collect();
    let shaped = abi::layout(selector, &types);
    let flat = path::inputs_for(selector, WORDS);
    let (calldata, fixed) = if shaped.fixed.is_empty() {
        (flat.calldata.clone(), Vec::new())
    } else {
        (shaped.calldata, shaped.fixed)
    };
    // An amount left at zero would hide that the repeated call pays again.
    let calldata = path::fill_words(&calldata, &fixed, path::varied_word);
    let inputs = Inputs {
        calldata,
        returned: SIGNER.to_be_bytes().to_vec(),
        storage: begin.clone(),
        ..flat
    };
    // The signer check compares against storage this pass cannot fill by calls.
    // Storage is left free and the report says so.
    let free = Free {
        words: inputs.calldata.len() / 32,
        value: false,
        storage: true,
        answers: false,
        settings: None,
        fixed,
    };
    (inputs, free)
}

fn explored(
    explorer: &Explorer,
    f: &Function,
    begin: &HashMap<U256, U256>,
) -> (Vec<Path>, Vec<usize>) {
    let (start, free) = start_for(f, begin);
    (explorer.explore(&start, &free, LIMITS), free.fixed)
}

fn repeated(explorer: &Explorer, found: &[Path]) -> Option<Path> {
    for p in found {
        let Some(digest) = digest_of(p) else {
            continue;
        };
        if !p.succeeded() || !acts(p) {
            continue;
        }
        let mut again = p.inputs.clone();
        again.storage = p.run.storage.clone();
        again.signed = Some((digest.clone(), SIGNER));
        let second = explorer.run(&again);
        let accepted = second.succeeded() && acts(&second) && digest_of(&second) == Some(digest);
        if accepted {
            return Some(second);
        }
    }
    None
}

type Effect = (Vec<(U256, U256, Vec<u8>)>, Vec<(U256, U256)>);

fn effect(p: &Path) -> Effect {
    let calls = p.run.calls.iter().filter(|c| c.addr != RECOVER);
    let mut slots: Vec<(U256, U256)> = p.run.storage.iter().map(|(k, v)| (*k, *v)).collect();
    slots.sort();
    (
        calls.map(|c| (c.addr, c.value, c.input.clone())).collect(),
        slots,
    )
}

// A word that changes what the call does while the digest stays the same is not signed.
fn unsigned_words(explorer: &Explorer, first: &Path, fixed: &[usize]) -> Vec<(usize, Path)> {
    let Some(digest) = digest_of(first) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    let words = first.inputs.calldata.len().saturating_sub(4) / 32;
    for index in (0..words).filter(|i| !fixed.contains(i)) {
        let mut changed = first.inputs.clone();
        changed.calldata[4 + 32 * index + 31] ^= 1;
        changed.signed = Some((digest.clone(), SIGNER));
        let run = explorer.run(&changed);
        let same_message = digest_of(&run).as_ref() == Some(&digest);
        if run.succeeded() && same_message && effect(&run) != effect(first) {
            out.push((index, run));
        }
    }
    out
}

fn report_unsigned(out: &mut Vec<Finding>, f: &Function, words: &[(usize, Path)]) {
    let Some((_, run)) = words.first() else {
        return;
    };
    let list: Vec<String> = words.iter().map(|(i, _)| i.to_string()).collect();
    let severity = if words.iter().any(|(_, p)| moves_value(p)) {
        Severity::High
    } else {
        Severity::Medium
    };
    push(
        out,
        "signed-call-leaves-word-unsigned",
        "A signed call acts on a word the signature does not cover",
        severity,
        Confidence::High,
        Some(f),
        None,
        format!(
            "`{}` recovers a signer and acts on the result. Each of the argument words {} was changed in turn while recovery answered the signer only for the original digest. The digest stayed the same, the run still ended normally, and what the call did changed. Whoever submits the signed message chooses those words. Storage was chosen so the signer check passes.",
            f.name,
            list.join(", "),
        ),
        Vec::new(),
        "Include every argument the call acts on in the signed digest.",
    );
    if let Some(last) = out.last_mut() {
        last.confirm(run);
    }
}

pub fn findings(c: &Contract, out: &mut Vec<Finding>) {
    if std::env::var("EVMDEC_NO_CONFIRM").is_ok() || c.info.runtime.is_empty() {
        return;
    }
    let begin = deploy::storage(c);
    let mut explorers = Explorers::default();
    let external = |f: &&Function| f.kind == FnKind::External;
    for f in c.functions.iter().filter(external).take(MAX_FUNCTIONS) {
        if exec::spent() {
            break;
        }
        let code = c.code_of(f);
        if !code.contains(&op::STATICCALL) && !code.contains(&op::CALL) {
            continue;
        }
        let explorer = explorers.of(code);
        let (found, fixed) = explored(explorer, f, &begin);
        let acted = |p: &&Path| p.succeeded() && acts(p) && digest_of(p).is_some();
        if let Some(first) = found.iter().find(acted) {
            report_unsigned(out, f, &unsigned_words(explorer, first, &fixed));
        }
        let Some(second) = repeated(explorer, &found) else {
            continue;
        };
        let severity = if moves_value(&second) {
            Severity::High
        } else {
            Severity::Medium
        };
        push(
            out,
            "signed-message-accepted-twice",
            "The same signed message is accepted again after it was used",
            severity,
            Confidence::High,
            Some(f),
            None,
            format!(
                "`{}` recovers a signer and acts on the result. The attached call was run once and then run again, unchanged, from the storage the first run left. Recovery was made to answer the signer only for the digest of the first run, so a digest that included a counter or a used mark would have been refused. The second run ended normally and acted again, so nothing the function stores takes the message out of use. Storage was chosen so the signer check passes.",
                f.name,
            ),
            Vec::new(),
            "Put a per-signer counter or a single-use mark in the signed digest and update it when the message is accepted.",
        );
        if let Some(last) = out.last_mut() {
            last.confirm(&second);
        }
    }
}
