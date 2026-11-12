use crate::abi;
use crate::analyze::{display_name, Confidence, Finding};
use crate::decompile::{Contract, Function};
use crate::deploy;
use crate::evidence;
use crate::exec::{self, FrameRun};
use crate::expr::{self, ExprId, Node};
use crate::function::FnKind;
use crate::hex;
use crate::interp::{CallRecord, Outcome};
use crate::opcode as op;
use crate::path::{self, Explorer, Limits, Path};
use crate::seq::{self, Entry};
use crate::solve::{self, Free, Inputs, Item};
use crate::u256::U256;
use std::collections::{HashMap, HashSet};
use std::time::{Duration, Instant};

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
const BUDGET: Duration = Duration::from_secs(4);
// Enough words for a few offsets, lengths and elements of array arguments.
const SOLVED_WORDS: usize = 24;
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
    let start = deploy::storage(c);
    let deadline = Instant::now() + BUDGET;
    for finding in findings.iter_mut() {
        if Instant::now() >= deadline {
            break;
        }
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
        let code = c.code_of(f);
        let local = c.local_pc(f, pc);
        if let Some((witness, observed)) = reach(code, f, local, &finding.id, &start) {
            finding.confirmed = true;
            finding.witness = Some(hex::encode(&witness));
            finding.observed = observed;
            finding.confidence = Confidence::High;
            finding.description.push_str(CONFIRMED_NOTE);
            continue;
        }
        let entry = |g: &Function| Entry {
            selector: exec::selector_of(g),
            words: SOLVED_WORDS,
        };
        let same_code = |g: &&Function| {
            g.kind == FnKind::External && std::ptr::eq(c.code_of(g).as_ptr(), code.as_ptr())
        };
        let entries: Vec<Entry> = c.functions.iter().filter(same_code).map(entry).collect();
        let id = finding.id.clone();
        let goal = |p: &Path| p.run.reached(local) && p.succeeded() && shows_effect(&id, &p.run);
        let explorer = Explorer::new(code);
        if let Some(plan) = seq::reach(&explorer, &entries, entry(f), &start, &goal) {
            finding.confirm(&plan.last);
            finding.setup = plan
                .steps
                .iter()
                .map(|s| hex::encode(&s.calldata))
                .collect();
            finding.confidence = Confidence::High;
            finding.description.push_str(&format!(
                " Confirmed in {} calls from {}: an account holding no role first makes the attached earlier call{}, then reaches this sink and the transaction keeps its effect.",
                plan.steps.len() + 1,
                deploy::start_text(&start),
                if plan.steps.len() == 1 { "" } else { "s" },
            ));
        }
    }
}

// Entering the sink's block is not enough.
// A guard ahead of the sink or a later revert undoes the effect.
// So the run must end normally and show it.
fn reach(
    code: &[u8],
    f: &Function,
    pc: usize,
    id: &str,
    start: &HashMap<U256, U256>,
) -> Option<(Vec<u8>, Vec<String>)> {
    let selector = exec::selector_of(f);
    let shapes = [U256::ZERO, SOME_ETHER].into_iter().flat_map(|callvalue| {
        (0..=6usize)
            .flat_map(exec::arg_shapes)
            .map(move |args| (callvalue, args))
    });
    for (callvalue, args) in shapes.take(MAX_ATTEMPTS) {
        let data = exec::calldata(selector, &args);
        let host = exec::caller_host(data.clone(), callvalue);
        let run = exec::run_frame(code, &host, start.clone(), STEP_BUDGET);
        if run.reached(pc) && run.succeeded() && shows_effect(id, &run) {
            let mut inputs = path::inputs_for(selector, 0);
            (inputs.callvalue, inputs.storage) = (callvalue, start.clone());
            return Some((data, evidence::observed(&inputs, &run)));
        }
    }
    solved(code, f, pc, id, start)
}

// Storage stays as deployment left it. Only the call data and the value are solved for.
fn solved(
    code: &[u8],
    f: &Function,
    pc: usize,
    id: &str,
    begin: &HashMap<U256, U256>,
) -> Option<(Vec<u8>, Vec<String>)> {
    let explorer = Explorer::new(code);
    let selector = exec::selector_of(f);
    let types: Vec<String> = f.params.iter().map(|p| p.ty.clone()).collect();
    let shaped = abi::layout(selector, &types);
    let flat = path::inputs_for(selector, SOLVED_WORDS);
    let starts = [
        (flat.calldata.clone(), Vec::new()),
        (shaped.calldata, shaped.fixed),
    ];
    let mut answer = vec![0u8; 32];
    answer[31] = 1;
    for (calldata, fixed) in starts {
        let free = Free {
            words: SOLVED_WORDS.max(calldata.len() / 32),
            value: true,
            storage: false,
            fixed,
        };
        for returned in [Vec::new(), answer.clone()] {
            let start = Inputs {
                calldata: calldata.clone(),
                returned,
                storage: begin.clone(),
                ..flat.clone()
            };
            let hit = explorer
                .explore(&start, &free, Limits::default())
                .into_iter()
                .find(|p| p.run.reached(pc) && p.succeeded() && shows_effect(id, &p.run));
            if let Some(p) = hit {
                let observed = evidence::observed(&p.inputs, &p.run);
                return Some((p.inputs.calldata, observed));
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

const WRAP_IDS: &[&str] = &["unchecked-arithmetic", "unchecked-block-arithmetic"];
const MAX_WRAP_NODES: usize = 16;

fn wrap_checks(val: ExprId, out: &mut Vec<ExprId>) {
    let mut seen = HashSet::new();
    let mut stack = vec![val];
    while let Some(e) = stack.pop() {
        if !seen.insert(e) || seen.len() > 400 || out.len() >= MAX_WRAP_NODES {
            continue;
        }
        let from_input = |x: ExprId| expr::contains(x, &|n| matches!(n, Node::CallDataLoad(_)));
        if let Node::Op(o, v) = expr::node(e) {
            if let ([a, b], true) = (&v[..], from_input(e)) {
                let check = match o {
                    op::ADD => Some(expr::op2(op::LT, e, *a)),
                    op::SUB => Some(expr::op2(op::LT, *a, *b)),
                    // MAX / 0 is 0 in the EVM, so a zero factor would read as a wrap.
                    op::MUL => {
                        let room = expr::op2(op::DIV, expr::konst(U256::MAX), *b);
                        let nonzero = expr::op2(op::GT, *b, expr::konst(U256::ZERO));
                        Some(expr::op2(op::AND, nonzero, expr::op2(op::GT, *a, room)))
                    }
                    _ => None,
                };
                out.extend(check.filter(|c| expr::as_const(*c).is_none()));
            }
            stack.extend(v);
        }
    }
}

// The solver's model of a path can be wrong.
// Only a second run that takes the same path and ends normally counts.
fn wrapping_input(code: &[u8], f: &Function, begin: &HashMap<U256, U256>) -> Option<Path> {
    let explorer = Explorer::new(code);
    let selector = exec::selector_of(f);
    let types: Vec<String> = f.params.iter().map(|p| p.ty.clone()).collect();
    let shaped = abi::layout(selector, &types);
    let doubled = abi::layout_with(selector, &types, 2);
    let flat = path::inputs_for(selector, f.params.len().clamp(1, 8));
    let starts = [
        (flat.calldata.clone(), Vec::new()),
        (shaped.calldata, shaped.fixed),
        (doubled.calldata, doubled.fixed),
    ];
    for (calldata, fixed) in starts {
        let free = Free {
            words: calldata.len() / 32,
            value: true,
            storage: false,
            fixed,
        };
        let start = Inputs {
            calldata,
            storage: begin.clone(),
            ..flat.clone()
        };
        let found = explorer.explore(&start, &free, Limits::default());
        for p in found {
            if !p.succeeded() {
                continue;
            }
            let mut checks = Vec::new();
            for item in &p.items {
                if let Item::Store { val, .. } = item {
                    wrap_checks(*val, &mut checks);
                }
            }
            for cond in checks {
                let wrap = Item::Check {
                    cond,
                    holds: false,
                    pc: usize::MAX,
                };
                // Asked first so the later checks are repaired around the wrap, not the reverse.
                let mut first = vec![wrap.clone()];
                first.extend(p.items.iter().cloned());
                let mut want = vec![true];
                want.extend(&p.truth);
                let Some(inputs) = solve::solve(&first, &want, &p.inputs, &free) else {
                    continue;
                };
                let mut items = p.items.clone();
                items.push(wrap);
                let again = explorer.run(&inputs);
                let same = again.signature() == p.signature() && again.succeeded();
                let wrapped = solve::replay(&items, &inputs).last() == Some(&Some(true));
                if same && wrapped {
                    return Some(again);
                }
            }
        }
    }
    None
}

pub fn confirm_wraps(c: &Contract, findings: &mut [Finding]) {
    if std::env::var("EVMDEC_NO_CONFIRM").is_ok() || c.info.runtime.is_empty() {
        return;
    }
    let start = deploy::storage(c);
    let deadline = Instant::now() + BUDGET;
    for finding in findings.iter_mut() {
        if Instant::now() >= deadline {
            break;
        }
        if finding.confirmed || !WRAP_IDS.contains(&finding.id.as_str()) {
            continue;
        }
        let Some(name) = finding.function.as_deref() else {
            continue;
        };
        let function = c
            .functions
            .iter()
            .find(|f| f.kind == FnKind::External && display_name(f) == name);
        let Some(f) = function else { continue };
        if let Some(run) = wrapping_input(c.code_of(f), f, &start) {
            finding.confirm(&run);
            finding.confidence = Confidence::High;
            finding.description.push_str(&format!(
                " Confirmed: with the attached input, sent by an account holding no role to {}, the function ends normally after a stored result wrapped around.",
                deploy::start_text(&start),
            ));
        }
    }
}
