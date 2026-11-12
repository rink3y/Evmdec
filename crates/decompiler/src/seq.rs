use crate::expr::{self, ExprId, Node};
use crate::opcode as op;
use crate::path::{Explorer, Limits, Path};
use crate::solve::{self, Free, Inputs, Item};
use crate::u256::U256;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Entry {
    pub selector: Option<u32>,
    pub words: usize,
}

#[derive(Clone, Debug)]
pub struct Plan {
    pub steps: Vec<Inputs>,
    pub last: Path,
}

#[derive(Clone, Debug)]
struct Need {
    key: U256,
    key_expr: ExprId,
    parts: HashMap<ExprId, U256>,
    value: U256,
}

const MAX_SETUP_STEPS: usize = 3;
const MAX_NEEDS: usize = 6;
const MAX_WRITER_PATHS: usize = 12;

fn inputs_at(entry: Entry, state: &HashMap<U256, U256>) -> Inputs {
    let mut inputs = crate::path::inputs_for(entry.selector, entry.words);
    inputs.storage = state.clone();
    inputs
}

fn free(entry: Entry, storage: bool) -> Free {
    Free {
        words: entry.words,
        value: true,
        storage,
        fixed: Vec::new(),
    }
}

fn load_keys(e: ExprId, out: &mut Vec<ExprId>, seen: &mut HashSet<ExprId>) {
    if !seen.insert(e) || seen.len() > 4_000 {
        return;
    }
    if let Node::SLoad(key, false, _) = expr::node(e) {
        out.push(key);
    }
    for child in expr::children(e) {
        load_keys(child, out, seen);
    }
}

fn subvalues(e: ExprId, inputs: &Inputs, out: &mut HashMap<ExprId, U256>) {
    if out.contains_key(&e) {
        return;
    }
    if let Some(v) = solve::value_of(e, inputs) {
        out.insert(e, v);
    }
    if let Node::Keccak(words, _) = expr::node(e) {
        for w in words {
            subvalues(w, inputs, out);
        }
    }
}

// What the path assumed about storage that the state does not hold.
fn needs(path: &Path, state: &HashMap<U256, U256>) -> Vec<Need> {
    let assumed: Vec<(U256, U256)> = path
        .inputs
        .storage
        .iter()
        .filter(|(k, v)| state.get(*k).copied().unwrap_or(U256::ZERO) != **v)
        .map(|(k, v)| (*k, *v))
        .collect();
    let mut keys = Vec::new();
    let mut seen = HashSet::new();
    for item in &path.items {
        if let Item::Check { cond, .. } = item {
            load_keys(*cond, &mut keys, &mut seen);
        }
    }
    let mut out = Vec::new();
    for (key, value) in assumed {
        let expr_of = keys
            .iter()
            .find(|k| solve::value_of(**k, &path.inputs) == Some(key));
        if let Some(key_expr) = expr_of {
            let mut parts = HashMap::new();
            subvalues(*key_expr, &path.inputs, &mut parts);
            out.push(Need {
                key,
                key_expr: *key_expr,
                parts,
                value,
            });
        }
    }
    out
}

// Hashes cannot be inverted, so two keys are matched part by part instead.
fn same_key(theirs: ExprId, need: &Need, wanted: ExprId, out: &mut Vec<ExprId>) -> bool {
    match (expr::node(theirs), expr::node(wanted)) {
        (Node::Keccak(a, ta), Node::Keccak(b, tb)) if a.len() == b.len() && ta == tb => {
            a.iter().zip(&b).all(|(x, y)| same_key(*x, need, *y, out))
        }
        _ => match need.parts.get(&wanted) {
            Some(v) => {
                out.push(expr::op2(op::EQ, theirs, expr::konst(*v)));
                true
            }
            None => false,
        },
    }
}

fn check(cond: ExprId) -> Item {
    Item::Check {
        cond,
        holds: false,
        pc: usize::MAX,
    }
}

fn write_for(
    explorer: &Explorer,
    entry: Entry,
    state: &HashMap<U256, U256>,
    need: &Need,
) -> Option<Path> {
    let start = inputs_at(entry, state);
    let paths = explorer.explore(&start, &free(entry, false), Limits::default());
    for path in paths
        .iter()
        .filter(|p| p.succeeded())
        .take(MAX_WRITER_PATHS)
    {
        for item in &path.items {
            let Item::Store { key, val, .. } = item else {
                continue;
            };
            let mut extra = Vec::new();
            if !same_key(*key, need, need.key_expr, &mut extra) {
                continue;
            }
            extra.push(expr::op2(op::EQ, *val, expr::konst(need.value)));
            let mut items = path.items.clone();
            let mut want = path.truth.clone();
            for cond in extra {
                items.push(check(cond));
                want.push(true);
            }
            let Some(inputs) = solve::solve(&items, &want, &path.inputs, &free(entry, false))
            else {
                continue;
            };
            let run = explorer.run(&inputs);
            let stored = run.run.storage.get(&need.key).copied();
            if run.succeeded() && stored == Some(need.value) {
                return Some(run);
            }
        }
    }
    None
}

// The plan is replayed from the starting storage before it is returned.
pub fn reach(
    explorer: &Explorer,
    entries: &[Entry],
    target: Entry,
    begin: &HashMap<U256, U256>,
    goal: &dyn Fn(&Path) -> bool,
) -> Option<Plan> {
    let mut state: HashMap<U256, U256> = begin.clone();
    let mut steps: Vec<Inputs> = Vec::new();
    for _ in 0..=MAX_SETUP_STEPS {
        let start = inputs_at(target, &state);
        let direct = explorer.explore(&start, &free(target, false), Limits::default());
        if let Some(last) = direct.into_iter().find(|p| goal(p)) {
            return replayed(explorer, steps, last, begin, goal);
        }
        let assumed = explorer.explore(&start, &free(target, true), Limits::default());
        let wanted: Vec<Need> = assumed
            .iter()
            .filter(|p| goal(p))
            .flat_map(|p| needs(p, &state))
            .take(MAX_NEEDS)
            .collect();
        let step = wanted.iter().find_map(|need| {
            entries
                .iter()
                .find_map(|entry| write_for(explorer, *entry, &state, need))
        })?;
        state = step.run.storage.clone();
        steps.push(step.inputs.clone());
    }
    None
}

fn replayed(
    explorer: &Explorer,
    steps: Vec<Inputs>,
    last: Path,
    begin: &HashMap<U256, U256>,
    goal: &dyn Fn(&Path) -> bool,
) -> Option<Plan> {
    let mut state: HashMap<U256, U256> = begin.clone();
    let mut clean = Vec::new();
    for step in &steps {
        let mut inputs = step.clone();
        inputs.storage = state.clone();
        let run = explorer.run(&inputs);
        if !run.succeeded() {
            return None;
        }
        state = run.run.storage.clone();
        clean.push(inputs);
    }
    let mut inputs = last.inputs.clone();
    inputs.storage = state;
    let last = explorer.run(&inputs);
    goal(&last).then_some(Plan { steps: clean, last })
}
