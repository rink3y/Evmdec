use crate::abi::{self, SEL_TRANSFER_FROM};
use crate::analyze::{display_name, Confidence, Finding, Severity};
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
use crate::range::Bounds;
use crate::seq::{self, Entry};
use crate::solve::{self, Free, Inputs, Item};
use crate::u256::U256;
use std::collections::{HashMap, HashSet};

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
pub const WORK: u64 = 4 * exec::WORK_PER_SECOND;
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
    for finding in findings.iter_mut() {
        if exec::spent() {
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
        let goal = |p: &Path| {
            let brought = p.inputs.callvalue;
            p.run.reached(local)
                && p.succeeded()
                && shows_effect(&id, &p.run, &p.inputs.storage, brought)
        };
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
        if exec::spent() {
            return None;
        }
        let data = exec::calldata(selector, &args);
        let host = exec::caller_host(data.clone(), callvalue);
        let run = exec::run_frame(code, &host, start.clone(), STEP_BUDGET);
        if run.reached(pc) && run.succeeded() && shows_effect(id, &run, start, callvalue) {
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
                .find(|p| {
                    p.run.reached(pc)
                        && p.succeeded()
                        && shows_effect(id, &p.run, &p.inputs.storage, p.inputs.callvalue)
                });
            if let Some(p) = hit {
                let observed = evidence::observed(&p.inputs, &p.run);
                return Some((p.inputs.calldata, observed));
            }
        }
    }
    None
}

// What a run stored is judged against what it started with. The run begins with what the
// constructor stored, so its storage is never empty once a constructor has written.
fn shows_effect(id: &str, run: &FrameRun, start: &HashMap<U256, U256>, brought: U256) -> bool {
    let call_of = |pred: &dyn Fn(&CallRecord) -> bool| run.calls.iter().any(pred);
    match id {
        "selfdestruct" => matches!(run.outcome, Outcome::SelfDestruct(_)),
        // Ether that came in with this call and goes back out is a refund.
        "unprotected-ether-withdrawal" => {
            let sent = run.calls.iter().filter(|c| c.kind == op::CALL);
            let out = sent.fold(U256::ZERO, |all, c| {
                all.checked_add(c.value).unwrap_or(U256::MAX)
            });
            out > brought
        }
        "arbitrary-call" => call_of(&|c| matches!(c.kind, op::CALL | op::CALLCODE)),
        "arbitrary-delegatecall" | "delegatecall-user-target" | "delegatecall-dynamic-target" => {
            call_of(&|c| c.kind == op::DELEGATECALL)
        }
        "arbitrary-transferfrom" => {
            call_of(&|c| c.input.starts_with(&SEL_TRANSFER_FROM.to_be_bytes()))
        }
        "unprotected-owner-write" | "unprotected-initializer" | "unprotected-upgrade" => {
            run.storage != *start
        }
        "silent-auth-failure" => {
            run.storage == *start && run.calls.is_empty() && run.logs.is_empty()
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
enum Wrap {
    Shown(Box<Path>),
    Bounded { paths: usize, results: usize },
    Open,
}

fn stored_arithmetic(p: &Path) -> Vec<ExprId> {
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    let mut stack: Vec<ExprId> = p
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Store { val, .. } => Some(*val),
            Item::Check { .. } => None,
        })
        .collect();
    while let Some(e) = stack.pop() {
        if !seen.insert(e) || seen.len() > 2_000 {
            continue;
        }
        if let Node::Op(o, parts) = expr::node(e) {
            // A constant on one side can wrap as well. A counter stepped down from zero does.
            let varies = parts.len() == 2 && parts.iter().any(|x| expr::as_const(*x).is_none());
            if matches!(o, op::ADD | op::SUB | op::MUL) && varies {
                out.push(e);
            }
            stack.extend(parts);
        }
    }
    out
}

fn wrapping_input(code: &[u8], f: &Function, begin: &HashMap<U256, U256>) -> Wrap {
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
    let (mut paths, mut results, mut open) = (0, 0, false);
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
            let bounds = Bounds::from_checks(&p.items);
            let stored = stored_arithmetic(&p);
            paths += 1;
            results += stored.len();
            open |= stored.iter().any(|e| bounds.may_wrap(*e));
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
                    return Wrap::Shown(Box::new(again));
                }
            }
        }
    }
    if open || results == 0 || open_with_other_storage(&explorer, f, begin) {
        Wrap::Open
    } else {
        Wrap::Bounded { paths, results }
    }
}

// A branch can need storage that another function sets. From the starting storage it is
// never taken, and what it stores would be missing from the verdict.
fn open_with_other_storage(explorer: &Explorer, f: &Function, begin: &HashMap<U256, U256>) -> bool {
    let selector = exec::selector_of(f);
    let flat = path::inputs_for(selector, f.params.len().clamp(1, 8));
    let free = Free {
        words: flat.calldata.len() / 32,
        value: true,
        storage: true,
        fixed: Vec::new(),
    };
    let start = Inputs {
        storage: begin.clone(),
        ..flat
    };
    let found = explorer.explore(&start, &free, Limits::default());
    found.iter().filter(|p| p.succeeded()).any(|p| {
        let bounds = Bounds::from_checks(&p.items);
        stored_arithmetic(p).iter().any(|e| bounds.may_wrap(*e))
    })
}

pub fn confirm_wraps(c: &Contract, findings: &mut [Finding]) {
    if std::env::var("EVMDEC_NO_CONFIRM").is_ok() || c.info.runtime.is_empty() {
        return;
    }
    let start = deploy::storage(c);
    for finding in findings.iter_mut() {
        if exec::spent() {
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
        match wrapping_input(c.code_of(f), f, &start) {
            Wrap::Shown(run) => {
                finding.confirm(&run);
                finding.confidence = Confidence::High;
                finding.description.push_str(&format!(
                    " Confirmed: with the attached input, sent by an account holding no role to {}, the function ends normally after a stored result wrapped around.",
                    deploy::start_text(&start),
                ));
            }
            Wrap::Bounded { paths, results } => {
                finding.severity = Severity::Info;
                finding.confidence = Confidence::High;
                finding.description.push_str(&format!(
                    " Range analysis of the {paths} path(s) found that end normally shows none of the {results} stored result(s) can wrap: masks and the checks on each path keep the operands small enough. Block times are taken to fit in 64 bits and a sent value in 128. Kept for the record at the lowest severity.",
                ));
            }
            Wrap::Open => {}
        }
    }
}

const CHANCE_ID: &str = "weak-randomness";
const LATER: [u64; 3] = [1, 2, 3];
const BLOCK_SECONDS: u64 = 12;
const STAKE: u64 = 0x1001;

fn paid_to_caller(p: &Path) -> U256 {
    let sent = p
        .run
        .calls
        .iter()
        .filter(|c| c.kind == op::CALL && c.addr == p.inputs.caller);
    sent.fold(U256::ZERO, |all, c| {
        all.checked_add(c.value).unwrap_or(U256::MAX)
    })
}

struct Chance {
    won: Path,
    blocks: u64,
    then: U256,
}

// A draw from block values is shown by its effect: a call that is paid more than it
// brought, and the same call a block or two later that is not. Nothing but the block
// differs between the two, and a contract reads the block before it decides to call.
fn chance_shown(explorer: &Explorer, f: &Function, begin: &HashMap<U256, U256>) -> Option<Chance> {
    let selector = exec::selector_of(f);
    let types: Vec<String> = f.params.iter().map(|p| p.ty.clone()).collect();
    let shaped = abi::layout(selector, &types);
    let flat = path::inputs_for(selector, f.params.len().clamp(1, 8));
    let starts = [
        (flat.calldata.clone(), Vec::new()),
        (shaped.calldata, shaped.fixed),
    ];
    for (calldata, fixed) in starts {
        let free = Free {
            words: calldata.len() / 32,
            value: true,
            // The limits such a function checks are set by an owner or a constructor.
            // They are chosen here so that the call is accepted.
            storage: true,
            fixed,
        };
        // No branch asks for a payment above zero, so the search would settle for none.
        let start = Inputs {
            calldata,
            callvalue: U256::from_u64(STAKE),
            storage: begin.clone(),
            ..flat.clone()
        };
        for p in explorer.explore(&start, &free, Limits::default()) {
            let paid = paid_to_caller(&p);
            if !p.succeeded() || paid <= p.inputs.callvalue {
                continue;
            }
            for blocks in LATER {
                let mut later = p.inputs.clone();
                later.number = later.number.wrapping_add(U256::from_u64(blocks));
                let seconds = U256::from_u64(blocks * BLOCK_SECONDS);
                later.timestamp = later.timestamp.wrapping_add(seconds);
                let again = explorer.run(&later);
                let then = paid_to_caller(&again);
                if again.succeeded() && then < paid {
                    return Some(Chance {
                        won: p,
                        blocks,
                        then,
                    });
                }
            }
        }
    }
    None
}

pub fn confirm_chance(c: &Contract, findings: &mut [Finding]) {
    if std::env::var("EVMDEC_NO_CONFIRM").is_ok() || c.info.runtime.is_empty() {
        return;
    }
    let start = deploy::storage(c);
    for finding in findings.iter_mut() {
        if exec::spent() {
            break;
        }
        if finding.confirmed || finding.id != CHANCE_ID {
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
        let explorer = Explorer::new(c.code_of(f));
        let Some(Chance { won, blocks, then }) = chance_shown(&explorer, f, &start) else {
            continue;
        };
        finding.description.push_str(&format!(
            " Confirmed by running it, with storage chosen so that the call is accepted: the attached call brings {} and is paid {}. The same call with the block number {blocks} higher is paid {}. Nothing but the block number and its time differs between the two runs.",
            won.inputs.callvalue.to_hex(),
            paid_to_caller(&won).to_hex(),
            then.to_hex(),
        ));
        finding.severity = Severity::High;
        finding.confidence = Confidence::High;
        finding.confirm(&won);
    }
}
