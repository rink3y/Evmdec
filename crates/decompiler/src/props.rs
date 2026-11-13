use crate::abi;
use crate::analyze::{display_name, push, Confidence, Finding, Section, Severity};
use crate::decompile::{Contract, Function};
use crate::deploy;
use crate::emit::MappingLayout;
use crate::exec;
use crate::expr::{self, ExprId, Node};
use crate::function::FnKind;
use crate::lift::{Stmt, Term};
use crate::opcode as op;
use crate::path::{self, Explorers, Limits, Path};
use crate::solve::{self, Free, Inputs, Item, Step};
use crate::ssa;
use crate::u256::U256;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

const LIMITS: Limits = Limits {
    paths: 24,
    runs: 96,
};
const WORDS: usize = 12;
pub const WORK: u64 = 3 * exec::WORK_PER_SECOND;
const GROWTH_WORK: u64 = exec::WORK_PER_SECOND;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Place {
    Fixed(U256),
    Entry(U256),
}

struct Run<'a> {
    function: &'a Function,
    from: &'static str,
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

fn varied(calldata: &[u8], fixed: &[usize]) -> Vec<u8> {
    path::fill_words(calldata, fixed, path::varied_word)
}

fn runs(c: &Contract) -> Vec<Run<'_>> {
    let mut out = Vec::new();
    let begin = deploy::storage(c);
    let from = deploy::start_text(&begin);
    let mut explorers = Explorers::default();
    for f in c.functions.iter().filter(|f| f.kind == FnKind::External) {
        let code = c.code_of(f);
        let explorer = explorers.of(code);
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
                    storage: begin.clone(),
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
                        from,
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
    let state = format!(
        " The input attached does this from {}, sent by an account holding no role.",
        run.from
    );
    push(
        out,
        id,
        title,
        severity,
        Confidence::High,
        Some(run.function),
        None,
        description + &state,
        Vec::new(),
        advice,
    );
    if let Some(last) = out.last_mut() {
        last.confirm(&run.path);
    }
}

// Two flags that both flip, or two counters that both step by one, move together by chance.
pub(crate) fn amount_sized(delta: U256) -> bool {
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
        let first = writes.first()?.0;
        // Adding nothing twice writes a slot twice and takes no lock.
        let moved = writes.iter().any(|(_, after)| *after != first);
        Some((
            first,
            writes.last()?.1,
            if moved { writes.len() } else { 0 },
        ))
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
            .is_none_or(|words| words.iter().any(|w| expr::has_part(*w, val))),
        Some(Term::Stop) => false,
        _ => true,
    };
    let checked = |val: ExprId| {
        run.path.items.iter().any(|item| match item {
            Item::Check { cond, .. } => expr::has_part(*cond, val),
            Item::Store { .. } => false,
        })
    };
    changed.into_iter().find_map(|(at, key, val)| {
        let used_later = effects[at + 1..].iter().any(|st| match st {
            Stmt::SStore { key: k, val: v, .. } => *k == key || expr::has_part(*v, val),
            Stmt::Call { input, value, .. } => {
                let sent = value.is_some_and(|v| expr::has_part(v, val));
                sent || input
                    .as_ref()
                    .is_none_or(|words| words.iter().any(|w| expr::has_part(*w, val)))
            }
            Stmt::Log { data, topics, .. } => {
                topics.iter().any(|t| expr::has_part(*t, val))
                    || data
                        .as_ref()
                        .is_none_or(|words| words.iter().any(|w| expr::has_part(*w, val)))
            }
            Stmt::Create { .. } => true,
            Stmt::MStore { val: v, .. } => *v != val && expr::has_part(*v, val),
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Clock {
    Time,
    Height,
}

impl Clock {
    fn text(self) -> &'static str {
        match self {
            Clock::Time => "the block timestamp",
            Clock::Height => "the block number",
        }
    }
}

fn clock_of(e: ExprId) -> Option<Clock> {
    let has = |which: u8| expr::contains(e, &|n| matches!(n, Node::Env(o, _) if *o == which));
    match (has(op::TIMESTAMP), has(op::NUMBER)) {
        (true, false) => Some(Clock::Time),
        (false, true) => Some(Clock::Height),
        _ => None,
    }
}

fn places_read(e: ExprId, layout: MappingLayout) -> Vec<Place> {
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 2_000 {
            continue;
        }
        if let Node::SLoad(key, false, _) = expr::node(x) {
            out.extend(place(key, layout));
        } else {
            stack.extend(expr::children(x));
        }
    }
    out
}

fn clock_mix(all: &[Run], layout: MappingLayout, out: &mut Vec<Finding>) {
    let mut written: BTreeMap<Place, BTreeSet<Clock>> = BTreeMap::new();
    for run in all {
        for item in &run.path.items {
            let Item::Store { key, val, .. } = item else {
                continue;
            };
            if let (Some(p), Some(clock)) = (place(*key, layout), clock_of(*val)) {
                written.entry(p).or_default().insert(clock);
            }
        }
    }
    let mut told: BTreeSet<Place> = BTreeSet::new();
    for run in all.iter().filter(|r| !r.assumed) {
        for item in &run.path.items {
            let Item::Check { cond, .. } = item else {
                continue;
            };
            let Some(read) = clock_of(*cond) else {
                continue;
            };
            for p in places_read(*cond, layout) {
                let Some(kinds) = written.get(&p) else {
                    continue;
                };
                let other = kinds.iter().find(|k| **k != read);
                let (Some(other), false) = (other, kinds.contains(&read)) else {
                    continue;
                };
                if !told.insert(p) {
                    continue;
                }
                let where_ = match p {
                    Place::Fixed(slot) => slot_text(slot),
                    Place::Entry(root) => format!("the mapping at {}", slot_text(root)),
                };
                report(
                    out,
                    run,
                    "clock-units-mixed",
                    "A value kept in one clock is compared with the other",
                    Severity::Medium,
                    format!(
                        "Every write of {where_} found takes its value from {}. `{}` compares it with {}. The two count in different units, so the comparison does not mean what either side intends.",
                        other.text(),
                        run.function.name,
                        read.text(),
                    ),
                    "Keep and compare the value in one clock.",
                );
            }
        }
    }
}

fn bits_read(cond: ExprId, slot: U256) -> U256 {
    let amount = |e: ExprId| {
        let by = expr::as_const(e).filter(U256::fits_u64)?.low_u64();
        u32::try_from(by).ok().filter(|by| *by < 256)
    };
    let mut read = U256::ZERO;
    let mut seen = HashSet::new();
    let mut stack = vec![(cond, U256::MAX)];
    while let Some((e, kept)) = stack.pop() {
        if !seen.insert((e, kept)) || seen.len() > 4_000 {
            continue;
        }
        match expr::node(e) {
            Node::SLoad(key, false, _) if expr::as_const(key) == Some(slot) => read = read | kept,
            Node::Op(op::AND, parts) if parts.len() == 2 => {
                match (expr::as_const(parts[0]), expr::as_const(parts[1])) {
                    (Some(mask), None) => stack.push((parts[1], kept & mask)),
                    (None, Some(mask)) => stack.push((parts[0], kept & mask)),
                    _ => stack.extend(parts.iter().map(|p| (*p, U256::MAX))),
                }
            }
            Node::Op(op::SHR, parts) if amount(parts[0]).is_some() => {
                stack.push((parts[1], kept << amount(parts[0]).unwrap_or(0)));
            }
            Node::Op(op::SHL, parts) if amount(parts[0]).is_some() => {
                stack.push((parts[1], kept >> amount(parts[0]).unwrap_or(0)));
            }
            _ => stack.extend(expr::children(e).into_iter().map(|c| (c, U256::MAX))),
        }
    }
    read
}

fn every_writer_seen(c: &Contract, all: &[Run]) -> bool {
    let finished: BTreeSet<usize> = all.iter().map(|r| r.function.pc).collect();
    c.functions
        .iter()
        .filter(|f| f.kind == FnKind::External && f.effects.writes_storage)
        .all(|f| finished.contains(&f.pc))
}

fn time_bounds(
    c: &Contract,
    all: &[Run],
    begin: &HashMap<U256, U256>,
    layout: MappingLayout,
    out: &mut Vec<Finding>,
) {
    let fixed = |key: ExprId| match place(key, layout) {
        Some(Place::Fixed(slot)) => Some(slot),
        _ => None,
    };
    let mut timed: BTreeMap<U256, &Run> = BTreeMap::new();
    let mut compared: BTreeMap<U256, U256> = BTreeMap::new();
    for run in all {
        for item in &run.path.items {
            let Item::Check { cond, .. } = item else {
                continue;
            };
            if clock_of(*cond).is_none() {
                continue;
            }
            for p in places_read(*cond, layout) {
                if let Place::Fixed(slot) = p {
                    timed.entry(slot).or_insert(run);
                    let bits = compared.entry(slot).or_insert(U256::ZERO);
                    *bits = *bits | bits_read(*cond, slot);
                }
            }
        }
    }
    // A slot can pack the bound with other fields. Only a write that moves the bits the
    // time check reads sets the bound.
    let moves_bound = |run: &Run, slot: U256| {
        let read = compared.get(&slot).copied().unwrap_or(U256::MAX);
        run.steps.iter().any(|step| match step {
            Step::Write {
                slot: at,
                before,
                after,
                ..
            } => *at == slot && !((*before ^ *after) & read).is_zero(),
            _ => false,
        })
    };
    let mut written: BTreeSet<U256> = BTreeSet::new();
    let mut set_by_call: BTreeMap<U256, &Run> = BTreeMap::new();
    for run in all {
        for item in &run.path.items {
            let Item::Store { key, val, .. } = item else {
                continue;
            };
            let Some(slot) = fixed(*key) else { continue };
            written.insert(slot);
            let from_input = expr::contains(*val, &|n| matches!(n, Node::CallDataLoad(_)));
            if from_input && !run.assumed && moves_bound(run, slot) {
                set_by_call.entry(slot).or_insert(run);
            }
        }
    }
    let complete = every_writer_seen(c, all);
    for (slot, reader) in &timed {
        if let Some(writer) = set_by_call.get(slot) {
            report(
                out,
                writer,
                "time-bound-set-by-anyone",
                "A time bound can be set by any caller",
                Severity::Medium,
                format!(
                    "`{}` compares {} with the block clock. `{}` needs no role and stores a value taken from its call there, so any caller decides when that check passes.",
                    reader.function.name,
                    slot_text(*slot),
                    writer.function.name,
                ),
                "Let only an authorised caller set the bound, or derive it from the clock inside the contract.",
            );
            continue;
        }
        let never_passes = !all
            .iter()
            .any(|r| !r.assumed && r.function.pc == reader.function.pc);
        let unset = begin.get(slot).is_none_or(|v| v.is_zero());
        if complete && unset && never_passes && !written.contains(slot) {
            push(
                out,
                "time-window-never-opens",
                "A time check reads a slot that nothing sets",
                Severity::Low,
                if begin.is_empty() { Confidence::Low } else { Confidence::Medium },
                Some(reader.function),
                None,
                format!(
                    "`{}` ends normally only when {} holds a value its time check accepts. The slot starts at zero, no path found writes it, and from the starting storage the function never ends normally.{}",
                    reader.function.name,
                    slot_text(*slot),
                    if begin.is_empty() {
                        " Only runtime code was given, so a constructor that sets it cannot be ruled out."
                    } else {
                        ""
                    },
                ),
                Vec::new(),
                "Set the bound during construction or through an authorised function, or remove the check.",
            );
        }
    }
}

type Field = (U256, u32, U256);

fn field_of(e: ExprId) -> Option<Field> {
    let slot_of = |x: ExprId| match expr::node(x) {
        Node::SLoad(key, false, _) => expr::as_const(key),
        _ => None,
    };
    if let Some(slot) = slot_of(e) {
        return Some((slot, 0, U256::MAX));
    }
    let Node::Op(op::AND, parts) = expr::node(e) else {
        return None;
    };
    let (mask, inner) = match (expr::as_const(parts[0]), expr::as_const(parts[1])) {
        (Some(m), None) => (m, parts[1]),
        (None, Some(m)) => (m, parts[0]),
        _ => return None,
    };
    if let Some(slot) = slot_of(inner) {
        return Some((slot, 0, mask));
    }
    let Node::Op(op::SHR, shifted) = expr::node(inner) else {
        return None;
    };
    let by = expr::as_const(shifted[0]).filter(U256::fits_u64)?.low_u64();
    Some((slot_of(shifted[1])?, u32::try_from(by).ok()?, mask))
}

fn required(cond: ExprId, holds: bool) -> Option<(Field, U256)> {
    match expr::node(cond) {
        Node::Op(op::ISZERO, inner) => match field_of(inner[0]) {
            Some(field) if holds => Some((field, U256::ZERO)),
            Some(_) => None,
            None => required(inner[0], !holds),
        },
        Node::Op(op::EQ, sides) if holds => {
            let (field, value) = match (expr::as_const(sides[0]), expr::as_const(sides[1])) {
                (Some(v), None) => (field_of(sides[1])?, v),
                (None, Some(v)) => (field_of(sides[0])?, v),
                _ => return None,
            };
            Some((field, value))
        }
        _ => None,
    }
}

const MAX_PHASE: u64 = 0xff;

fn read_field(word: U256, field: Field) -> U256 {
    (word >> field.1) & field.2
}

fn phases(
    c: &Contract,
    all: &[Run],
    begin: &HashMap<U256, U256>,
    out: &mut Vec<Finding>,
) -> Option<Section> {
    // A writer with no finished run could be the one that enters the missing phase.
    let every_writer_seen = every_writer_seen(c, all);
    let small = |v: &U256| v.fits_u64() && v.low_u64() <= MAX_PHASE;
    let wanted = |run: &Run| {
        let mut out: BTreeMap<Field, U256> = BTreeMap::new();
        for item in &run.path.items {
            let Item::Check { cond, holds, .. } = item else {
                continue;
            };
            if let Some((field, value)) = required(*cond, *holds).filter(|(_, v)| small(v)) {
                out.entry(field).or_insert(value);
            }
        }
        out
    };
    let wants: Vec<BTreeMap<Field, U256>> = all.iter().map(wanted).collect();
    let fields: BTreeSet<Field> = wants.iter().flat_map(|w| w.keys().copied()).collect();
    let mut asked: BTreeMap<(Field, &str), BTreeSet<Option<U256>>> = BTreeMap::new();
    for (run, want) in all.iter().zip(&wants) {
        for field in &fields {
            let values = asked.entry((*field, &run.function.name)).or_default();
            values.insert(want.get(field).copied());
        }
    }
    // A function that also finishes at another value, or without testing the field, takes
    // a branch on it. Only one that finishes at a single value waits for that value.
    let mut needs: BTreeMap<Field, BTreeMap<U256, BTreeSet<&str>>> = BTreeMap::new();
    for ((field, name), values) in asked {
        if let [Some(value)] = values.into_iter().collect::<Vec<_>>()[..] {
            let by_value = needs.entry(field).or_default();
            by_value.entry(value).or_default().insert(name);
        }
    }
    let mut lines = Vec::new();
    for (field, by_value) in &needs {
        let mut moves: BTreeSet<(U256, U256, &str)> = BTreeSet::new();
        let mut counted = false;
        for run in all {
            let writes: Vec<(U256, U256)> = run
                .steps
                .iter()
                .filter_map(|s| match s {
                    Step::Write {
                        slot,
                        before,
                        after,
                        ..
                    } if *slot == field.0 => Some((*before, *after)),
                    _ => None,
                })
                .collect();
            let (Some(first), Some(last)) = (writes.first(), writes.last()) else {
                continue;
            };
            let (from, to) = (read_field(first.0, *field), read_field(last.1, *field));
            let chosen_by_caller = run.path.items.iter().any(|item| match item {
                Item::Store { key, val, .. } => {
                    expr::as_const(*key) == Some(field.0) && from_the_call(*val)
                }
                Item::Check { .. } => false,
            });
            counted |= chosen_by_caller && from != to;
            if from != to {
                moves.insert((from, to, &run.function.name));
            }
        }
        let all_small = moves.iter().all(|(a, b, _)| small(a) && small(b));
        if moves.is_empty() || !all_small || counted {
            continue;
        }
        let at_start = read_field(begin.get(&field.0).copied().unwrap_or(U256::ZERO), *field);
        let name = match (field.1, field.2 == U256::MAX) {
            (0, true) => slot_text(field.0),
            (shift, _) => format!("{} from bit {shift}", slot_text(field.0)),
        };
        let mut line = format!("{name} starts at {}.", at_start.low_u64());
        for (from, to, function) in &moves {
            line.push_str(&format!(
                " `{function}` moves it from {} to {}.",
                from.low_u64(),
                to.low_u64()
            ));
        }
        for (value, functions) in by_value {
            let list: Vec<String> = functions.iter().map(|f| format!("`{f}`")).collect();
            line.push_str(&format!(
                " {} run only at {}.",
                list.join(", "),
                value.low_u64()
            ));
            let entered = *value == at_start || moves.iter().any(|(_, to, _)| to == value);
            let witness = all
                .iter()
                .find(|r| functions.contains(r.function.name.as_str()));
            let effect = |r: &&Run| r.function.effects.writes_storage || r.function.effects.calls;
            let witness = witness.filter(effect).filter(|_| every_writer_seen);
            if let (false, Some(run)) = (entered, witness) {
                let known = if begin.is_empty() {
                    " Only runtime code was given, so a constructor that sets it cannot be ruled out."
                } else {
                    ""
                };
                push(
                    out,
                    "phase-never-entered",
                    "Functions wait for a phase that no path enters",
                    Severity::Low,
                    if begin.is_empty() { Confidence::Low } else { Confidence::Medium },
                    Some(run.function),
                    None,
                    format!(
                        "{} run only while {name} holds {}. Other functions move that value between phases, but none of the paths found leaves it at {} and it does not start there, so these functions cannot be reached.{known}",
                        list.join(", "),
                        value.low_u64(),
                        value.low_u64(),
                    ),
                    Vec::new(),
                    "Add the missing transition, or remove the functions that wait for it.",
                );
            }
        }
        lines.push(line);
    }
    (!lines.is_empty()).then_some(Section {
        title: "Phases".to_string(),
        lines,
    })
}

// A hashed key lands on a slot nobody can aim.
// Only a word that reaches the place outside a hash can pick where it lands.
fn raw_words(e: ExprId) -> Vec<ExprId> {
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 2_000 {
            continue;
        }
        match expr::node(x) {
            Node::CallDataLoad(_) => out.push(x),
            Node::Op(..) => stack.extend(expr::children(x)),
            _ => {}
        }
    }
    out
}

fn unbounded_word(run: &Run, place: ExprId) -> Option<ExprId> {
    let tested = |word: ExprId| {
        run.path.items.iter().any(|item| match item {
            Item::Check { cond, .. } => expr::has_part(*cond, word),
            Item::Store { .. } => false,
        })
    };
    raw_words(place).into_iter().find(|w| !tested(*w))
}

fn aimed_writes(all: &[Run], out: &mut Vec<Finding>) {
    let mut told: BTreeSet<(usize, bool)> = BTreeSet::new();
    for run in all.iter().filter(|r| !r.assumed) {
        for st in &run.path.effects {
            let (place, val, storage) = match st {
                Stmt::SStore {
                    key,
                    val,
                    transient: false,
                    ..
                } => (*key, *val, true),
                Stmt::MStore { off, val, .. } => (*off, *val, false),
                _ => continue,
            };
            if !from_the_call(val) || unbounded_word(run, place).is_none() {
                continue;
            }
            if !told.insert((run.function.pc, storage)) {
                continue;
            }
            let (id, title, severity, what, advice) = if storage {
                (
                    "input-picks-storage-slot",
                    "A storage slot is chosen by the call with no bound",
                    Severity::High,
                    "a storage slot whose number is computed from a word of the call, not from a hash of it",
                    "Bound the index before the write, or key the data through a mapping.",
                )
            } else {
                (
                    "input-picks-memory-offset",
                    "A memory offset is chosen by the call with no bound",
                    Severity::Low,
                    "memory at an offset computed from a word of the call",
                    "Bound the offset against the allocated length before the write.",
                )
            };
            report(
                out,
                run,
                id,
                title,
                severity,
                format!(
                    "`{}` writes a value taken from the call to {what}. No check on this path tests that word, so the caller picks where the write lands.",
                    run.function.name,
                ),
                advice,
            );
        }
    }
}

fn short_input(c: &Contract, all: &[Run], out: &mut Vec<Finding>) {
    let mut explorers = Explorers::default();
    let mut accepted: Vec<&Run> = Vec::new();
    let mut seen: BTreeSet<usize> = BTreeSet::new();
    for run in all.iter().filter(|r| !r.assumed) {
        let inputs = &run.path.inputs;
        let reads_last = run.path.items.iter().any(|item| {
            let e = match item {
                Item::Check { cond, .. } => *cond,
                Item::Store { val, .. } => *val,
            };
            expr::contains(e, &|n| matches!(n, Node::CallDataLoad(_)))
        });
        let wrote = run.path.run.storage != inputs.storage;
        if !reads_last
            || !wrote
            || run.function.params.is_empty()
            || seen.contains(&run.function.pc)
        {
            continue;
        }
        let code = c.code_of(run.function);
        let explorer = explorers.of(code);
        let mut cut = inputs.clone();
        cut.calldata
            .truncate(4 + 32 * run.function.params.len() - 1);
        let again = explorer.run(&cut);
        if again.succeeded() && again.run.storage != cut.storage {
            seen.insert(run.function.pc);
            accepted.push(run);
        }
    }
    let Some(first) = accepted.first() else {
        return;
    };
    let names: Vec<String> = accepted
        .iter()
        .map(|r| format!("`{}`", r.function.name))
        .collect();
    report(
        out,
        first,
        "short-input-accepted",
        "Input shorter than the arguments is accepted",
        Severity::Low,
        format!(
            "{} read their arguments, write storage and end normally when the call data stops one byte short of the last argument. The missing byte is read as zero, which shifts the value of the last argument. Code built by a current compiler refuses such input.",
            names.join(", "),
        ),
        "Check the call data length against the arguments before reading them.",
    );
    if let Some(last) = out.last_mut() {
        last.sites = accepted.len();
    }
}

fn refusing_payee(c: &Contract, all: &[Run], out: &mut Vec<Finding>) {
    const KNOWN: [&str; 2] = ["blocking-payout-loop", "fixed-payee-can-block"];
    let mut explorers = Explorers::default();
    let mut told: BTreeSet<usize> = BTreeSet::new();
    for run in all.iter().filter(|r| !r.assumed) {
        if told.contains(&run.function.pc) {
            continue;
        }
        let inputs = &run.path.inputs;
        let targets = run.path.effects.iter().filter_map(|st| match st {
            Stmt::Call { addr, value, .. } => Some((*addr, *value)),
            _ => None,
        });
        // An account the caller names is the caller's own risk, and an asset is not a payee.
        // Only a payment of value to an account read from storage counts.
        let stored = |e: ExprId| {
            let reads = expr::contains(e, &|n| matches!(n, Node::SLoad(..)));
            reads && !expr::contains(e, &|n| matches!(n, Node::CallDataLoad(_)))
        };
        let carries = |value: Option<ExprId>| {
            value.is_some_and(|v| expr::as_const(v).is_none_or(|c| !c.is_zero()))
        };
        let payees: Vec<(usize, ExprId)> = targets
            .zip(&run.path.run.calls)
            .enumerate()
            .filter(|(_, ((target, value), call))| {
                let paid = call.kind == op::CALL && carries(*value) && stored(*target);
                paid && call.addr != inputs.caller
            })
            .map(|(index, ((target, _), _))| (index, target))
            .collect();
        // Two instalments to one account are one payee. The account is known by the place
        // it is read from, since from empty storage every stored account reads as zero.
        let read_from = |target: &ExprId| read_of_one_slot(*target).unwrap_or(*target);
        let distinct: BTreeSet<ExprId> = payees.iter().map(|(_, t)| read_from(t)).collect();
        if payees.is_empty() {
            continue;
        }
        let code = c.code_of(run.function);
        let explorer = explorers.of(code);
        let blocked = payees.iter().find_map(|(index, _)| {
            let mut refused = inputs.clone();
            refused.failing = Some(*index);
            let again = explorer.run(&refused);
            (!again.succeeded()).then_some(again)
        });
        let Some(again) = blocked else { continue };
        let name = display_name(run.function);
        let known = out.iter_mut().find(|f| {
            KNOWN.contains(&f.id.as_str()) && f.function.as_deref() == Some(name.as_str())
        });
        if let Some(f) = known {
            f.description.push_str(
                " Confirmed by running it: with the attached input the function ends normally, and it fails when one of the accounts it pays refuses the payment.",
            );
            f.confidence = Confidence::High;
            f.confirm(&again);
            told.insert(run.function.pc);
        } else if distinct.len() >= 2 {
            told.insert(run.function.pc);
            report(
                out,
                run,
                "one-refusal-blocks-all",
                "One account that refuses its payment makes the whole call fail",
                Severity::Medium,
                format!(
                    "`{}` pays {} different accounts in one call and ends normally when all of them accept. When one of them refuses, the call fails and none of the others is paid, so a single account can hold up everyone else for as long as it likes.",
                    run.function.name,
                    distinct.len(),
                ),
                "Record what each account is owed and let each one collect it in its own call.",
            );
        }
    }
}

const SHORT_LIST: u64 = 2;
const LONG_LIST: u64 = 34;
const STEPS_PER_ITEM: usize = 8;
const MAX_COUNTERS: usize = 4;
const LARGE_COUNT: u64 = 1 << 32;

fn growth(c: &Contract, all: &[Run], begin: &HashMap<U256, U256>, out: &mut Vec<Finding>) {
    let mut counters: BTreeMap<U256, &Run> = BTreeMap::new();
    for run in all.iter().filter(|r| !r.assumed) {
        for step in &run.steps {
            let Step::Write {
                key,
                slot,
                before,
                after,
            } = step
            else {
                continue;
            };
            let by_one = *after == before.wrapping_add(U256::ONE);
            if by_one && expr::as_const(*key).is_some() {
                counters.entry(*slot).or_insert(run);
            }
        }
    }
    let mut explorers = Explorers::default();
    for (slot, adder) in counters.into_iter().take(MAX_COUNTERS) {
        let mut slowed: Vec<(String, usize)> = Vec::new();
        for g in c.functions.iter().filter(|f| f.kind == FnKind::External) {
            if exec::spent() {
                break;
            }
            let code = c.code_of(g);
            let explorer = explorers.of(code);
            let steps_at = |length: u64| {
                let mut inputs = path::inputs_for(exec::selector_of(g), WORDS);
                inputs.storage = begin.clone();
                inputs.storage.insert(slot, U256::from_u64(length));
                let run = explorer.run(&inputs).run;
                run.succeeded().then_some(run.steps)
            };
            if let (Some(short), Some(long)) = (steps_at(SHORT_LIST), steps_at(LONG_LIST)) {
                let extra = long.saturating_sub(short);
                if extra >= (LONG_LIST - SHORT_LIST) as usize * STEPS_PER_ITEM {
                    slowed.push((format!("`{}`", g.name), extra));
                }
            }
        }
        let Some((_, extra)) = slowed.first() else {
            continue;
        };
        // A cap shows as the adder refusing once the count is large.
        let mut full = adder.path.inputs.clone();
        full.storage.insert(slot, U256::from_u64(LARGE_COUNT));
        let code = c.code_of(adder.function);
        let explorer = explorers.of(code);
        if !explorer.run(&full).succeeded() {
            continue;
        }
        let names: Vec<&str> = slowed.iter().map(|(n, _)| n.as_str()).collect();
        report(
            out,
            adder,
            "cost-grows-with-open-list",
            "Work grows with a count that any caller can raise",
            Severity::Medium,
            format!(
                "`{}` needs no role and raises {} by one each time it is called. {} do work for every unit of that count: with the count at {LONG_LIST} instead of {SHORT_LIST} a call runs {} more instructions. The same call still ends normally with the count at {LARGE_COUNT}, so nothing caps it and enough calls put those functions beyond what one block can run.",
                adder.function.name,
                slot_text(slot),
                names.join(", "),
                extra,
            ),
            "Cap the count, or let callers process the list in bounded pieces.",
        );
    }
}

pub fn findings(c: &Contract, out: &mut Vec<Finding>) -> Vec<Section> {
    if std::env::var("EVMDEC_NO_CONFIRM").is_ok() || c.info.runtime.is_empty() {
        return Vec::new();
    }
    let layout = c.compiler.layout;
    let all = exec::within(WORK, || runs(c));
    let pairs = in_step_pairs(&all, layout);
    out_of_step(&all, layout, &pairs, out);
    open_at_call(&all, layout, &pairs, out);
    lock_left(&all, out);
    dropped_changes(&all, out);
    clock_mix(&all, layout, out);
    aimed_writes(&all, out);
    short_input(c, &all, out);
    let begin = deploy::storage(c);
    refusing_payee(c, &all, out);
    time_bounds(c, &all, &begin, layout, out);
    exec::within(GROWTH_WORK, || growth(c, &all, &begin, out));
    phases(c, &all, &begin, out).into_iter().collect()
}
