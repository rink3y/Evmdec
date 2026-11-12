use crate::abi;
use crate::analyze::{push, Confidence, Finding, Severity};
use crate::decompile::{Contract, Function};
use crate::emit::MappingLayout;
use crate::exec;
use crate::expr::{self, ExprId, Node};
use crate::function::FnKind;
use crate::hex;
use crate::lift::{Stmt, Term};
use crate::opcode as op;
use crate::path::{self, Explorer, Limits, Path};
use crate::solve::{self, Free, Inputs, Item, Step};
use crate::ssa;
use crate::u256::U256;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

const LIMITS: Limits = Limits {
    paths: 24,
    runs: 96,
};
const WORDS: usize = 12;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Place {
    Fixed(U256),
    Entry(U256),
}

struct Run<'a> {
    function: &'a Function,
    assumed: bool,
    path: Path,
    steps: Vec<Step>,
}

fn place(key: ExprId, layout: MappingLayout) -> Option<Place> {
    if let Some(slot) = expr::as_const(key) {
        return Some(Place::Fixed(slot));
    }
    let path = ssa::slot_path(key, layout)?;
    matches!(path.steps[..], [ssa::Step::Key(_)]).then_some(Place::Entry(path.root))
}

fn deltas(steps: &[Step], layout: MappingLayout) -> BTreeMap<Place, U256> {
    let mut net: BTreeMap<Place, U256> = BTreeMap::new();
    for step in steps {
        if let Step::Write {
            key, before, after, ..
        } = step
        {
            if let Some(p) = place(*key, layout) {
                let d = net.entry(p).or_insert(U256::ZERO);
                *d = d.wrapping_add(after.wrapping_sub(*before));
            }
        }
    }
    net
}

// Branches alone never ask for a non-zero amount, and a zero amount moves nothing.
fn varied(calldata: &[u8], fixed: &[usize]) -> Vec<u8> {
    let mut out = calldata.to_vec();
    for index in (0..calldata.len().saturating_sub(4) / 32).filter(|i| !fixed.contains(i)) {
        let at = 4 + 32 * index;
        let value = U256::from_u64(0x1001 + 2 * index as u64);
        out[at..at + 32].copy_from_slice(&value.to_be_bytes());
    }
    out
}

fn runs(c: &Contract) -> Vec<Run<'_>> {
    let mut out = Vec::new();
    let mut explorers: HashMap<*const u8, Explorer> = HashMap::new();
    for f in c.functions.iter().filter(|f| f.kind == FnKind::External) {
        let code = c.code_of(f);
        let explorer = explorers
            .entry(code.as_ptr())
            .or_insert_with(|| Explorer::new(code));
        let selector = exec::selector_of(f);
        let types: Vec<String> = f.params.iter().map(|p| p.ty.clone()).collect();
        let shaped = abi::layout(selector, &types);
        let flat = path::inputs_for(selector, WORDS);
        let starts = [
            (flat.calldata.clone(), Vec::new()),
            (varied(&flat.calldata, &[]), Vec::new()),
            (
                varied(&shaped.calldata, &shaped.fixed),
                shaped.fixed.clone(),
            ),
            (shaped.calldata, shaped.fixed),
        ];
        for (calldata, fixed) in starts {
            for assumed in [false, true] {
                let free = Free {
                    words: WORDS.max(calldata.len() / 32),
                    value: true,
                    storage: assumed,
                    fixed: fixed.clone(),
                };
                let start = Inputs {
                    calldata: calldata.clone(),
                    ..flat.clone()
                };
                for path in explorer.explore(&start, &free, LIMITS) {
                    if !path.succeeded() {
                        continue;
                    }
                    let steps = solve::steps(&path.effects, &path.inputs);
                    if steps.contains(&Step::Unknown) {
                        continue;
                    }
                    out.push(Run {
                        function: f,
                        assumed,
                        path,
                        steps,
                    });
                }
            }
        }
    }
    out
}

fn slot_text(slot: U256) -> String {
    let hex = slot.to_hex();
    format!("slot {hex}")
}

fn report(
    out: &mut Vec<Finding>,
    run: &Run,
    id: &str,
    title: &str,
    severity: Severity,
    description: String,
    advice: &str,
) {
    let state =
        " The input attached does this from empty storage, sent by an account holding no role.";
    push(
        out,
        id,
        title,
        severity,
        Confidence::High,
        Some(run.function),
        None,
        description + state,
        Vec::new(),
        advice,
    );
    if let Some(last) = out.last_mut() {
        last.witness = Some(hex::encode(&run.path.inputs.calldata));
        last.confirmed = true;
    }
}

// Two flags that both flip, or two counters that both step by one, move together by chance.
fn amount_sized(delta: U256) -> bool {
    let small = U256::from_u64(0xff);
    delta > small && U256::ZERO.wrapping_sub(delta) > small
}

fn in_step_pairs(all: &[Run], layout: MappingLayout) -> Vec<(U256, U256)> {
    let mut seen: BTreeMap<(U256, U256), BTreeSet<usize>> = BTreeMap::new();
    for run in all {
        let net = deltas(&run.steps, layout);
        for (place, moved) in &net {
            let Place::Entry(root) = place else { continue };
            if !amount_sized(*moved) {
                continue;
            }
            for (other, total) in &net {
                if let (Place::Fixed(slot), true) = (other, total == moved) {
                    seen.entry((*root, *slot))
                        .or_default()
                        .insert(run.function.pc);
                }
            }
        }
    }
    seen.into_iter()
        .filter(|(_, functions)| functions.len() >= 2)
        .map(|(pair, _)| pair)
        .collect()
}

fn out_of_step(all: &[Run], layout: MappingLayout, pairs: &[(U256, U256)], out: &mut Vec<Finding>) {
    for (root, total) in pairs {
        let mut told: BTreeSet<usize> = BTreeSet::new();
        for run in all.iter().filter(|r| !r.assumed) {
            let net = deltas(&run.steps, layout);
            let moved = net.get(&Place::Entry(*root)).copied().unwrap_or(U256::ZERO);
            let counted = net
                .get(&Place::Fixed(*total))
                .copied()
                .unwrap_or(U256::ZERO);
            if moved == counted || !told.insert(run.function.pc) {
                continue;
            }
            report(
                out,
                run,
                "entries-total-out-of-step",
                "A run changes a mapping's entries and its total by different amounts",
                Severity::Medium,
                format!(
                    "At least two functions move the entries of the mapping at {} and the value in {} by the same amount, so the two are kept in step. `{}` has a path that ends normally having changed the entries by {} in sum and the total by {}.",
                    slot_text(*root),
                    slot_text(*total),
                    run.function.name,
                    moved.to_hex(),
                    counted.to_hex(),
                ),
                "Move the total by the same amount as the entries on every path, or state why this path may differ.",
            );
        }
    }
}

fn open_at_call(
    all: &[Run],
    layout: MappingLayout,
    pairs: &[(U256, U256)],
    out: &mut Vec<Finding>,
) {
    for (root, total) in pairs {
        let mut told: BTreeSet<usize> = BTreeSet::new();
        for run in all.iter().filter(|r| !r.assumed) {
            let handed_out = run.steps.iter().enumerate().find(|(i, step)| {
                let outside = match step {
                    Step::Call { kind, to } => {
                        let precompile =
                            to.is_some_and(|a| a.fits_u64() && (1..0x12).contains(&a.low_u64()));
                        *kind != op::STATICCALL && !precompile
                    }
                    _ => false,
                };
                if !outside {
                    return false;
                }
                let so_far = deltas(&run.steps[..*i], layout);
                let moved = so_far.get(&Place::Entry(*root)).copied();
                let counted = so_far.get(&Place::Fixed(*total)).copied();
                moved.unwrap_or(U256::ZERO) != counted.unwrap_or(U256::ZERO)
            });
            let end = deltas(&run.steps, layout);
            let settled = end.get(&Place::Entry(*root)) == end.get(&Place::Fixed(*total));
            if handed_out.is_none() || !settled || !told.insert(run.function.pc) {
                continue;
            }
            report(
                out,
                run,
                "total-open-at-call",
                "A call leaves the contract while a mapping and its total disagree",
                Severity::Medium,
                format!(
                    "`{}` keeps the entries of the mapping at {} and the value in {} in step by the time it ends, but it makes a call to another account after changing one and before changing the other. Code that runs during that call, and anything that reads this contract from there, sees the two out of step.",
                    run.function.name,
                    slot_text(*root),
                    slot_text(*total),
                ),
                "Finish both updates before the call, or hold a lock that every reader and writer of the two respects.",
            );
        }
    }
}

fn lock_left(all: &[Run], out: &mut Vec<Finding>) {
    let ends = |run: &Run, slot: U256| -> Option<(U256, U256, usize)> {
        let writes: Vec<(U256, U256)> = run
            .steps
            .iter()
            .filter_map(|s| match s {
                Step::Write {
                    slot: at,
                    before,
                    after,
                    ..
                } if *at == slot => Some((*before, *after)),
                _ => None,
            })
            .collect();
        Some((writes.first()?.0, writes.last()?.1, writes.len()))
    };
    let mut toggled: BTreeSet<(usize, U256)> = BTreeSet::new();
    for run in all {
        for step in &run.steps {
            let Step::Write { slot, key, .. } = step else {
                continue;
            };
            if expr::as_const(*key).is_none() {
                continue;
            }
            if let Some((first, last, count)) = ends(run, *slot) {
                if count >= 2 && first == last {
                    toggled.insert((run.function.pc, *slot));
                }
            }
        }
    }
    let mut told: BTreeSet<(usize, U256)> = BTreeSet::new();
    for run in all.iter().filter(|r| !r.assumed) {
        for (pc, slot) in toggled.iter().filter(|(pc, _)| *pc == run.function.pc) {
            let Some((first, last, _)) = ends(run, *slot) else {
                continue;
            };
            if first == last || !told.insert((*pc, *slot)) {
                continue;
            }
            report(
                out,
                run,
                "lock-left-set",
                "A path ends without putting a toggled slot back",
                Severity::Medium,
                format!(
                    "`{}` sets {} and puts it back on its other paths, the way a lock is taken and released. On this path it ends normally with the slot changed from {} to {}, so later calls that test it see it still taken.",
                    run.function.name,
                    slot_text(*slot),
                    first.to_hex(),
                    last.to_hex(),
                ),
                "Restore the slot on every path that ends normally.",
            );
        }
    }
}

fn mentions(e: ExprId, target: ExprId) -> bool {
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if x == target {
            return true;
        }
        if seen.insert(x) && seen.len() < 4_000 {
            stack.extend(expr::children(x));
        }
    }
    false
}

fn read_of_one_slot(e: ExprId) -> Option<ExprId> {
    match expr::node(e) {
        Node::SLoad(key, false, _) => Some(key),
        Node::Op(_, parts) => {
            let mut key = None;
            for part in parts.iter().filter(|p| expr::as_const(**p).is_none()) {
                let found = read_of_one_slot(*part)?;
                if key.is_some_and(|k| k != found) {
                    return None;
                }
                key = Some(found);
            }
            key
        }
        _ => None,
    }
}

fn from_the_call(e: ExprId) -> bool {
    expr::contains(e, &|n| {
        matches!(
            n,
            Node::CallDataLoad(_) | Node::Env(op::CALLER | op::CALLVALUE | op::TIMESTAMP, _)
        )
    })
}

// Scratch space and the free pointer sit below this and are rewritten all the time.
const FIRST_ALLOCATED: u64 = 0x80;

fn dropped_change(run: &Run) -> Option<(ExprId, ExprId)> {
    let effects = &run.path.effects;
    let mut copies: HashMap<ExprId, ExprId> = HashMap::new();
    let mut changed: Vec<(usize, ExprId, ExprId)> = Vec::new();
    for (i, st) in effects.iter().enumerate() {
        let Stmt::MStore { off, val, .. } = st else {
            continue;
        };
        let allocated = expr::as_const(*off).is_some_and(|o| o >= U256::from_u64(FIRST_ALLOCATED));
        if !allocated {
            continue;
        }
        if let Some(key) = read_of_one_slot(*val) {
            copies.insert(*off, key);
        } else if let Some(key) = copies.remove(off) {
            if from_the_call(*val) {
                changed.push((i, key, *val));
            }
        }
    }
    let end_uses = |val: ExprId| match &run.path.end {
        Some(Term::Return { data, .. }) => data
            .as_ref()
            .is_none_or(|words| words.iter().any(|w| mentions(*w, val))),
        Some(Term::Stop) => false,
        _ => true,
    };
    let checked = |val: ExprId| {
        run.path.items.iter().any(|item| match item {
            Item::Check { cond, .. } => mentions(*cond, val),
            Item::Store { .. } => false,
        })
    };
    changed.into_iter().find_map(|(at, key, val)| {
        let used_later = effects[at + 1..].iter().any(|st| match st {
            Stmt::SStore { key: k, val: v, .. } => *k == key || mentions(*v, val),
            Stmt::Call { input, value, .. } => {
                let sent = value.is_some_and(|v| mentions(v, val));
                sent || input
                    .as_ref()
                    .is_none_or(|words| words.iter().any(|w| mentions(*w, val)))
            }
            Stmt::Log { data, topics, .. } => {
                topics.iter().any(|t| mentions(*t, val))
                    || data
                        .as_ref()
                        .is_none_or(|words| words.iter().any(|w| mentions(*w, val)))
            }
            Stmt::Create { .. } => true,
            Stmt::MStore { val: v, .. } => *v != val && mentions(*v, val),
            _ => false,
        });
        (!used_later && !end_uses(val) && !checked(val)).then_some((key, val))
    })
}

fn dropped_changes(all: &[Run], out: &mut Vec<Finding>) {
    let mut told: BTreeSet<usize> = BTreeSet::new();
    for run in all.iter().filter(|r| !r.assumed) {
        let Some((key, _)) = dropped_change(run) else {
            continue;
        };
        if !told.insert(run.function.pc) {
            continue;
        }
        let place = match solve::value_of(key, &run.path.inputs) {
            Some(slot) => slot_text(slot),
            None => "a stored record".to_string(),
        };
        report(
            out,
            run,
            "changed-copy-dropped",
            "A stored value is copied to memory, changed there and never stored back",
            Severity::Medium,
            format!(
                "`{}` reads {} into memory and then overwrites that memory word with a value taken from the call. On this path the function ends normally without writing the slot, and the new value is not returned, logged, passed to a call or tested. The change is lost, which is what a record declared as a memory copy instead of a storage reference does.",
                run.function.name, place,
            ),
            "Write the changed record back to storage, or work on a storage reference instead of a memory copy.",
        );
    }
}

pub fn findings(c: &Contract, out: &mut Vec<Finding>) {
    if std::env::var("EVMDEC_NO_CONFIRM").is_ok() || c.info.runtime.is_empty() {
        return;
    }
    let layout = c.compiler.layout;
    let all = runs(c);
    let pairs = in_step_pairs(&all, layout);
    out_of_step(&all, layout, &pairs, out);
    open_at_call(&all, layout, &pairs, out);
    lock_left(&all, out);
    dropped_changes(&all, out);
}
