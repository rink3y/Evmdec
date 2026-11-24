use crate::expr::{self, kind, ExprId, Node};
use crate::keccak;
use crate::lift::{self, Lifted, Stmt, Term, FREE_POINTER};
use crate::opcode as op;
use crate::sigs;
use crate::u256::U256;
use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::OnceLock;

const HASHED_SLOTS: u64 = 4096;

const HASH_OFFSET_RANGE: i64 = 16;

// A slot below the hash is not an element of the array that starts at the hash.
pub fn array_element(c: U256) -> Option<(U256, u64)> {
    let (root, k) = hashed_slot(c)?;
    u64::try_from(k).ok().map(|k| (root, k))
}

pub fn hashed_slot(c: U256) -> Option<(U256, i64)> {
    static TABLE: OnceLock<HashMap<U256, (u64, i64)>> = OnceLock::new();
    let table = TABLE.get_or_init(|| {
        let mut t = HashMap::new();
        for s in 0..HASHED_SLOTS {
            let h = U256::from_be_bytes(&keccak::keccak256(&U256::from_u64(s).to_be_bytes()));
            for k in -HASH_OFFSET_RANGE..=HASH_OFFSET_RANGE {
                let key = if k >= 0 {
                    h.wrapping_add(U256::from_u64(k as u64))
                } else {
                    h.wrapping_sub(U256::from_u64((-k) as u64))
                };
                t.entry(key).or_insert((s, k));
            }
        }
        t
    });
    if c.bits() < 200 {
        return None;
    }
    table.get(&c).map(|(s, k)| (U256::from_u64(*s), *k))
}

fn offset_index(idx: &str, k: i64) -> String {
    match k {
        0 => idx.to_string(),
        k if k > 0 => format!("{} + {}", idx, k),
        k => format!("{} - {}", idx, -k),
    }
}

pub fn is_plain_index(e: ExprId) -> bool {
    if expr::as_const(e).is_some() {
        return false;
    }
    match expr::node(e) {
        Node::Keccak(..) => false,
        Node::Op(op::ADD, v) => !v.iter().any(|x| matches!(expr::node(*x), Node::Keccak(..))),
        _ => true,
    }
}

fn fixed_array_base(c: U256, bases: &BTreeSet<U256>) -> Option<(U256, U256)> {
    if c.bits() > 32 {
        return None;
    }
    let b = *bases.range(..=c).next_back()?;
    let off = c.wrapping_sub(b);
    if off.low_u64() < 16 {
        Some((b, off))
    } else {
        None
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum MappingLayout {
    #[default]
    Solidity,
    Vyper,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum SlotSpace {
    Persistent,
    Transient,
}

impl SlotSpace {
    pub fn from_transient(transient: bool) -> SlotSpace {
        if transient {
            SlotSpace::Transient
        } else {
            SlotSpace::Persistent
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PayloadKind {
    Return,
    Revert,
}

#[derive(Clone, Debug, Default)]
pub struct Names {
    pub callee_reads: Option<std::sync::Arc<HashMap<usize, crate::lift::MemoryReads>>>,
    pub code: std::sync::Arc<Vec<u8>>,
    pub call_starts: HashSet<ExprId>,
    pub params: HashMap<u32, String>,
    pub in_helper: bool,
    pub aliases: HashMap<ExprId, String>,
    pub fields: HashMap<(U256, u32, u32), String>,
    pub field_types: HashMap<(U256, u32, u32), String>,
    pub args: HashMap<u32, String>,
    pub narrow: HashSet<String>,
    pub callee_names: HashMap<usize, String>,
    pub callee_params: std::sync::Arc<HashMap<usize, Vec<String>>>,
    pub payload_overrides: RefCell<HashMap<ExprId, String>>,
    pub blocks: Option<Blocks>,
    pub storage: HashMap<U256, String>,
    pub members: HashMap<(U256, u64), String>,
    pub member_fields: HashMap<(U256, u64, u32, u32), String>,
    pub struct_depth: HashMap<U256, usize>,
    pub array_bases: BTreeSet<U256>,
    pub stale: RefCell<HashMap<ExprId, String>>,
    pub block_stale: RefCell<Vec<ExprId>>,
    pub forwarded: RefCell<HashMap<ExprId, String>>,
    pub forward_places: RefCell<HashMap<ExprId, ExprId>>,
    pub bound: HashMap<ExprId, ExprId>,
    pub temp_seq: RefCell<u32>,
    pub seqs: RefCell<HashMap<u32, u32>>,
    pub vars: RefCell<HashMap<u32, u32>>,
    pub layout: MappingLayout,
    pub hide_checked: bool,
    pub checked: Option<Checked>,
    pub gas_named: RefCell<HashSet<ExprId>>,
    // Each word old code had its last call write the answer to, with the call and the
    // place of the word in the answer.
    pub answers: RefCell<HashMap<ExprId, (u32, u64)>>,
    pub offsets: Offsets,
    pub bare: RefCell<HashMap<ExprId, (String, u8)>>,
    pub temps: RefCell<Vec<(String, String)>>,
    pub temp_of: RefCell<HashMap<ExprId, String>>,
    pub pure_callees: HashSet<usize>,
    pub bools: HashSet<ExprId>,
    pub addresses: HashSet<ExprId>,
    pub return_types: Vec<String>,
    // Blocks of memory the function keeps to itself, shown as local values, with the
    // number of words each holds.
    pub scalars: HashMap<u32, u64>,
    pub lengths: HashMap<u32, u64>,
    // Blocks the text has taken from free memory so far, which it may then write to.
    pub taken: RefCell<HashSet<u32>>,
    // Addresses of one-word blocks that are handed on as the word.
    pub handed: HashMap<ExprId, u32>,
    pub bool_fields: HashSet<(U256, u32, u32)>,
    pub bool_returns: Vec<bool>,
    pub strict: bool,
    pub storage_types: HashMap<U256, String>,
    pub param_types: HashMap<u32, String>,
    pub arg_types: HashMap<u32, String>,
    pub dyn_arrays: HashSet<U256>,
    pub elem_types: HashMap<U256, String>,
    pub array_resizers: HashSet<usize>,
    pub memo: RefCell<HashMap<ExprId, (String, u8)>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Arithmetic {
    Tested,
    Untested,
    Exempt,
}

pub type Site = (usize, usize);

#[derive(Clone, Debug, Default)]
pub struct Checked {
    ops: HashMap<ExprId, Vec<Site>>,
    divisors: HashMap<ExprId, Vec<Site>>,
    untold: HashSet<ExprId>,
    limits: HashMap<ExprId, Limits>,
    narrow: HashMap<ExprId, u32>,
}

type Limits = Vec<(U256, Option<Site>)>;

impl Checked {
    /* A product with a constant is tested by holding the other factor to the largest
    value of a type divided by that constant. The division is done when the code is
    compiled, so only the quotient is left to compare with. */
    fn product_limit(&self, e: ExprId) -> Option<Vec<Site>> {
        self.product_limit_in(e).map(|(sites, _)| sites)
    }

    /* The sites of the tests, and the width of the type when it is narrower than a word.
    A factor that may be wider than the type is no number of that type, so its product
    does not say what was tested. */
    fn product_limit_in(&self, e: ExprId) -> Option<(Vec<Site>, Option<u32>)> {
        let Node::Op(op::MUL, v) = expr::node(e) else {
            return None;
        };
        let mut found: Option<(Vec<Site>, Option<u32>)> = None;
        for (x, k) in [(v[0], v[1]), (v[1], v[0])] {
            let Some(k) = expr::as_const(k).filter(|k| !k.is_zero()) else {
                continue;
            };
            let width = |limit: &U256| {
                let fits = |bytes: &u32| {
                    expr::mask_bits(8 * bytes) / k == *limit
                        && (*bytes == 32 || expr::value_bits(x) <= 8 * bytes)
                };
                (1..=32u32).rev().find(fits).map(|bytes| 8 * bytes)
            };
            for (limit, site) in self.limits.get(&x).into_iter().flatten() {
                let Some(bits) = width(limit) else {
                    continue;
                };
                let (sites, narrow) = found.get_or_insert_with(|| (Vec::new(), Some(bits)));
                sites.extend(site);
                *narrow = narrow.filter(|_| bits < 256).map(|n| n.min(bits));
            }
        }
        found
    }
}

fn tested(set: &mut HashMap<ExprId, Vec<Site>>, e: ExprId, site: Option<Site>) {
    let sites = set.entry(e).or_default();
    if let Some(site) = site.filter(|s| !sites.contains(s)) {
        sites.push(site);
    }
}

/* What the code tests before it reverts with Panic(0x11), Panic(0x12) or Panic(0x31) says
which of its sums, differences, products and quotients are checked. The test either holds
the result itself or compares the two operands. */
pub fn checked_ops(l: &Lifted) -> Checked {
    let code = |data: &Option<Vec<ExprId>>| -> Option<u64> {
        let words = data.as_deref().filter(|w| w.len() >= 2)?;
        if leading_selector(words[0], None) != Some(SEL_PANIC) {
            return None;
        }
        let len = 4 + 32 * (words.len() - 1);
        let code = expr::as_const(shifted_word_len(words, 0, Some(len)))?.low_u64();
        [PANIC_OVERFLOW, PANIC_DIV_BY_ZERO, PANIC_EMPTY_POP]
            .contains(&code)
            .then_some(code)
    };
    // The words of a panic are written on the way to a revert that several tests share.
    let panics = |mut node: usize| {
        for _ in 0..4 {
            let nd = &l.nodes[node];
            if !nd.stmts.iter().all(|s| matches!(s, Stmt::MStore { .. })) {
                return None;
            }
            match &nd.term {
                Term::Revert { data, .. } => return code(data),
                Term::Jump(next) => node = *next,
                _ => return None,
            }
        }
        None
    };
    let mut guards: Vec<(ExprId, u64, Option<Site>)> = Vec::new();
    for nd in &l.nodes {
        for (i, s) in nd.stmts.iter().enumerate() {
            if let Stmt::Require { cond, data, .. } = s {
                guards.extend(code(data).map(|c| (*cond, c, Some((nd.id, i)))));
            }
        }
        if let Term::Branch { cond, t, f } = &nd.term {
            guards.extend(
                t.and_then(panics)
                    .map(|c| (expr::op1(op::ISZERO, *cond), c, None)),
            );
            guards.extend(panics(*f).map(|c| (*cond, c, None)));
        }
    }
    let within = |part: ExprId, whole: ExprId| {
        let part = expr::node(part);
        expr::contains(whole, &|n| *n == part)
    };
    let max = konst_max();
    let mut found = Checked::default();
    for (cond, code, site) in guards {
        let mut pending = vec![cond];
        while let Some(e) = pending.pop() {
            match expr::node(e) {
                // A word under a constant mask is one value, not two tests.
                Node::Op(op::ISZERO | op::OR | op::AND, v)
                    if !v.iter().any(|x| expr::is_const(*x)) =>
                {
                    pending.extend(v)
                }
                // A difference tested against zero is a test for equality.
                Node::Op(op::EQ | op::LT | op::GT | op::SLT | op::SGT | op::SUB, v) => {
                    for (x, y) in [(v[0], v[1]), (v[1], v[0])] {
                        match expr::node(x) {
                            _ if within(x, y) => {}
                            Node::Op(op::DIV, d) => match expr::node(d[0]) {
                                Node::Op(op::MUL, m) if m.contains(&d[1]) => {
                                    tested(&mut found.ops, d[0], site);
                                }
                                _ => {
                                    tested(&mut found.ops, x, site);
                                }
                            },
                            // A division by a power of two is lifted as a shift.
                            Node::Op(op::SHR, d) if doubled_by(d[1], d[0]) => {
                                tested(&mut found.ops, d[1], site);
                            }
                            Node::Op(..) => {
                                tested(&mut found.ops, x, site);
                            }
                            _ => {}
                        }
                        tested(&mut found.ops, expr::op2(op::SUB, x, y), site);
                        /* Solidity up to 0.8.15 tests a sum against max - y and a
                        product against max / y. */
                        let other = match expr::node(y) {
                            Node::Op(op::SUB, w) if expr::is_const(w[0]) => Some((op::ADD, w[1])),
                            Node::Op(op::NOT, w) => Some((op::ADD, w[0])),
                            Node::Op(op::DIV, w) if expr::is_const(w[0]) => Some((op::MUL, w[1])),
                            _ => None,
                        };
                        if let Some((o, z)) = other {
                            tested(&mut found.ops, expr::op2(o, x, z), site);
                            tested(&mut found.ops, expr::op2(o, z, x), site);
                        }
                        let Some(c) = expr::as_const(y) else {
                            continue;
                        };
                        // The largest and the smallest value of a type guard a step by one.
                        if c.is_low_mask() {
                            tested(
                                &mut found.ops,
                                expr::op2(op::ADD, x, expr::konst_u64(1)),
                                site,
                            );
                        }
                        if (!c).is_low_mask() {
                            tested(
                                &mut found.ops,
                                expr::op2(op::SUB, x, expr::konst_u64(1)),
                                site,
                            );
                        }
                        if c.is_zero() {
                            tested(&mut found.divisors, x, site);
                        } else if c != max {
                            found.limits.entry(x).or_default().push((c, site));
                            /* The limit is the largest value of a type less what is
                            added. The type is not known, so each width stands. A sum in a
                            type narrower than a word says what was tested only when its
                            operand is of that type, so one that may be wider is left to
                            its test. */
                            for bytes in (c.byte_len().max(1) as u32)..=32 {
                                let top = expr::mask_bits(8 * bytes);
                                if top == c || (bytes < 32 && expr::value_bits(x) > 8 * bytes) {
                                    continue;
                                }
                                let sum = expr::op2(op::ADD, x, expr::konst(top.wrapping_sub(c)));
                                tested(&mut found.ops, sum, site);
                                if bytes < 32 {
                                    found.narrow.entry(sum).or_insert(8 * bytes);
                                }
                            }
                            let negated = expr::op2(op::SUB, expr::konst(U256::ZERO), x);
                            tested(&mut found.ops, negated, site);
                        }
                    }
                }
                _ if code == PANIC_DIV_BY_ZERO => {
                    tested(&mut found.divisors, e, site);
                }
                _ => {
                    tested(
                        &mut found.ops,
                        expr::op2(op::SUB, e, expr::konst_u64(1)),
                        site,
                    );
                }
            }
        }
    }
    found.untold = untold_tests(l, &found, &code);
    found
}

/* A test that is left out is told by the operator it guards printing bare. When that
operator stands nowhere in the function nothing tells the test, so it has to be printed. */
fn untold_tests(
    l: &Lifted,
    found: &Checked,
    code: &dyn Fn(&Option<Vec<ExprId>>) -> Option<u64>,
) -> HashSet<ExprId> {
    let mut printed: HashSet<ExprId> = HashSet::new();
    let mut pending: Vec<ExprId> = Vec::new();
    for nd in &l.nodes {
        for s in &nd.stmts {
            match s {
                Stmt::Drop(_) => {}
                Stmt::Require { data, .. } if code(data).is_some() => {}
                _ => pending.extend(lift::stmt_exprs(s)),
            }
        }
        pending.extend(lift::term_exprs(&nd.term));
    }
    pending.extend(l.edge_assigns.values().flatten().map(|(_, v)| *v));
    while let Some(e) = pending.pop() {
        if printed.insert(e) {
            pending.extend(expr::children(e));
        }
    }
    let mut told: HashSet<Site> = HashSet::new();
    for e in &printed {
        let Node::Op(o, v) = expr::node(*e) else {
            continue;
        };
        let quotient = matches!(o, op::DIV | op::SDIV | op::MOD | op::SMOD);
        if quotient || matches!(o, op::ADD | op::SUB | op::MUL) {
            told.extend(found.ops.get(e).into_iter().flatten());
            told.extend(found.product_limit(*e).into_iter().flatten());
        }
        if quotient {
            told.extend(found.divisors.get(&v[1]).into_iter().flatten());
        }
    }
    let mut untold = HashSet::new();
    for nd in &l.nodes {
        for (i, s) in nd.stmts.iter().enumerate() {
            if let Stmt::Require { cond, data, .. } = s {
                let overflow = matches!(code(data), Some(PANIC_OVERFLOW | PANIC_DIV_BY_ZERO));
                if overflow && !told.contains(&(nd.id, i)) {
                    untold.insert(*cond);
                }
            }
        }
    }
    untold
}

fn doubled_by(product: ExprId, shift: ExprId) -> bool {
    let (Node::Op(op::MUL, m), Some(k)) = (expr::node(product), expr::as_const(shift)) else {
        return false;
    };
    let factor = |x: &ExprId| {
        expr::as_const(*x).is_some_and(|c| {
            c.is_power_of_two() && k.fits_u64() && u64::from(c.trailing_zeros()) == k.low_u64()
        })
    };
    m.iter().any(factor)
}

fn konst_max() -> U256 {
    !U256::ZERO
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Places {
    params: BTreeSet<usize>,
    returns: BTreeSet<usize>,
}

/* The compiler adds and subtracts places in memory, storage and call data without a test,
and none of that is arithmetic the source wrote. A value is a place when it is used as
one: as the offset of a load, a store, a copy, a call or a log, in a bounds test against
the size of the call data, or by a helper that uses its parameter or its result as one.
What is added to a hash or to an allocated block is a number counted from it. A sum made
from that number elsewhere is no place. */
#[derive(Clone, Debug, Default)]
pub struct Offsets {
    places: HashSet<ExprId>,
    bases: HashSet<ExprId>,
    ranged: HashSet<ExprId>,
    handed: std::sync::Arc<HashMap<usize, BTreeSet<usize>>>,
}

pub fn offsets(units: &[(usize, &Lifted)]) -> Vec<Offsets> {
    let mut places: HashMap<usize, Places> = HashMap::new();
    loop {
        let before = places.clone();
        let found = units.iter().map(|(pc, l)| offsets_in(*pc, l, &mut places));
        let mut found: Vec<Offsets> = found.collect();
        if places == before {
            let params = places.iter().map(|(pc, p)| (*pc, p.params.clone()));
            let handed = std::sync::Arc::new(params.collect::<HashMap<_, _>>());
            for own in &mut found {
                own.handed = handed.clone();
            }
            return found;
        }
    }
}

type Defs = HashMap<ExprId, Vec<ExprId>>;

fn anchors(e: ExprId, defs: &Defs, depth: u32) -> bool {
    match expr::node(e) {
        Node::Keccak(..) | Node::KeccakMem(..) => true,
        Node::MLoad(at, _) => is_free_pointer(at),
        Node::Op(op::ADD, v) if depth < 6 => v.iter().any(|x| anchors(*x, defs, depth + 1)),
        Node::Op(op::SUB, v) if depth < 6 => anchors(v[0], defs, depth + 1),
        Node::Var(_) if depth < 6 => {
            let from = defs.get(&e).into_iter().flatten();
            from.into_iter().any(|x| anchors(*x, defs, depth + 1))
        }
        _ => false,
    }
}

/* A number moved by a constant and then found below another constant is a test of the
range the number lies in. The step is meant to wrap, and no place in memory is tested to
lie below a constant. A sum tested to lie above one is a size held to a limit. */
fn range_tested(moved: ExprId, limit: ExprId) -> Option<ExprId> {
    let fixed = |v: &[ExprId]| v.iter().any(|x| expr::is_const(*x));
    let step = |e: ExprId| match expr::node(e) {
        Node::Op(op::ADD | op::SUB, v) if fixed(&v) => Some(e),
        _ => None,
    };
    let under_mask = match expr::node(moved) {
        Node::Op(op::AND, v) if fixed(&v) => v.iter().find_map(|x| step(*x)),
        _ => None,
    };
    step(moved).or(under_mask).filter(|_| expr::is_const(limit))
}

fn offsets_in(pc: usize, l: &Lifted, places: &mut HashMap<usize, Places>) -> Offsets {
    let sizes = |e: ExprId| {
        expr::contains(e, &|n| {
            matches!(n, Node::Env(op::CALLDATASIZE | op::RETURNDATASIZE, _))
        })
    };
    let mut pending: Vec<ExprId> = Vec::new();
    let mut roots: Vec<ExprId> = l.edge_assigns.values().flatten().map(|(_, v)| *v).collect();
    let own = places.get(&pc).cloned().unwrap_or_default();
    for nd in &l.nodes {
        roots.extend(crate::lift::node_exprs(nd));
        for s in &nd.stmts {
            match s {
                Stmt::MStore { off, .. } => pending.push(*off),
                Stmt::SStore { key, .. } => pending.push(*key),
                Stmt::Log { off, len, .. } | Stmt::Create { off, len, .. } => {
                    pending.extend([*off, *len])
                }
                Stmt::Copy { dest, src, len, .. } => pending.extend([*dest, *src, *len]),
                Stmt::Call {
                    in_off,
                    in_len,
                    out_off,
                    out_len,
                    ..
                } => pending.extend([*in_off, *in_len, *out_off, *out_len]),
                Stmt::Internal { callee, args, .. } => {
                    let used = places.get(callee).map(|p| p.params.clone());
                    pending.extend(used.iter().flatten().filter_map(|j| args.get(*j)));
                }
                _ => {}
            }
        }
        match &nd.term {
            Term::Return { off, len, .. } | Term::Revert { off, len, .. } => {
                pending.extend([*off, *len])
            }
            Term::ReturnDyn { ptr, .. } => pending.push(*ptr),
            Term::InternalReturn(vals) => {
                pending.extend(own.returns.iter().filter_map(|j| vals.get(*j)))
            }
            _ => {}
        }
    }
    let mut seen = HashSet::new();
    let mut ranged: HashSet<ExprId> = HashSet::new();
    while let Some(e) = roots.pop() {
        if !seen.insert(e) {
            continue;
        }
        match expr::node(e) {
            Node::MLoad(a, _)
            | Node::SLoad(a, _, _)
            | Node::CallDataLoad(a)
            | Node::ReturnData(_, a)
            | Node::CopiedWord(_, a, _) => pending.push(a),
            Node::KeccakMem(a, b, _) => pending.extend([a, b]),
            Node::Op(op::LT | op::GT | op::SLT | op::SGT, v) if v.iter().any(|x| sizes(*x)) => {
                pending.extend(v)
            }
            Node::Op(op::LT, v) => ranged.extend(range_tested(v[0], v[1])),
            Node::Op(op::GT, v) => ranged.extend(range_tested(v[1], v[0])),
            _ => {}
        }
        roots.extend(expr::children(e));
    }
    let defs = crate::ssa::phi_defs(l);
    let arity = crate::ssa::arity(l);
    let anchored = |e: ExprId| anchors(e, &defs, 0);
    let mut found = Offsets {
        ranged,
        ..Offsets::default()
    };
    let mut pending: Vec<(ExprId, bool)> = pending.into_iter().map(|e| (e, true)).collect();
    while let Some((e, base)) = pending.pop() {
        let new = match base {
            true => found.bases.insert(e),
            false => !found.places.contains(&e),
        };
        found.places.insert(e);
        if !new {
            continue;
        }
        match expr::node(e) {
            Node::Op(op::ADD, v) if base && anchored(v[0]) != anchored(v[1]) => {
                pending.extend(v.iter().map(|x| (*x, anchored(*x))));
            }
            Node::Op(op::SUB, v) if base && anchored(v[0]) => {
                pending.extend([(v[0], true), (v[1], false)]);
            }
            Node::Op(op::ADD | op::SUB | op::AND, v) => {
                pending.extend(v.iter().map(|x| (*x, base)));
            }
            Node::Var(_) if base => {
                pending.extend(defs.get(&e).into_iter().flatten().map(|x| (*x, true)));
            }
            Node::Arg(slot) if base && (slot as usize) < arity => {
                let own = places.entry(pc).or_default();
                own.params.insert(arity - 1 - slot as usize);
            }
            _ => {}
        }
    }
    for nd in &l.nodes {
        for s in &nd.stmts {
            if let Stmt::Internal {
                callee, results, ..
            } = s
            {
                let used = (0..results.len()).filter(|j| found.bases.contains(&results[*j]));
                places.entry(*callee).or_default().returns.extend(used);
            }
        }
    }
    found
}

// Keeps the output linear in size.
const TEMP_THRESHOLD: usize = 160;

impl Names {
    /* Takes what was found about the blocks of memory this function keeps. A block it
    keeps to itself is shown as local values, and an address that stood for one word is
    shown as the word. */
    pub fn unbox(&mut self, found: crate::boxes::Found) {
        use crate::boxes::Shown;
        self.scalars = found.scalars;
        let mut named: Vec<(ExprId, String)> = Vec::new();
        for (e, shown) in &found.shown {
            match shown {
                Shown::Word(number) => {
                    self.handed.insert(*e, *number);
                }
                Shown::As(at) => named.push((*e, fmt_expr(*at, self))),
            }
        }
        self.aliases.extend(named);
    }

    #[must_use]
    pub fn callee_name(&self, pc: usize) -> String {
        self.callee_names
            .get(&pc)
            .cloned()
            .unwrap_or_else(|| format!("func_{pc:#x}"))
    }

    /* Solidity from 0.8 on tests by default, so there a bare operator has to mean a
    tested one. A division by a constant that is not zero needs no test, and an address
    in an allocated block is not a sum. */
    fn arithmetic(&self, e: ExprId) -> Option<Arithmetic> {
        let checked = self.checked.as_ref()?;
        // Multiplying or dividing by a power of two moves bits. It is how a field is packed.
        let shift = |x: ExprId| match expr::node(x) {
            Node::Const(c) => c.is_power_of_two(),
            Node::Op(op::EXP, v) => expr::as_const(v[0]).is_some_and(|c| c.is_power_of_two()),
            _ => false,
        };
        let (tested, safe) = match expr::node(e) {
            Node::Op(op::ADD | op::SUB, _) => (checked.ops.contains_key(&e), false),
            Node::Op(op::MUL, v) => (
                checked.ops.contains_key(&e) || checked.product_limit(e).is_some(),
                v.iter().any(|x| shift(*x)),
            ),
            Node::Op(op::DIV | op::SDIV | op::MOD | op::SMOD, v) => (
                checked.ops.contains_key(&e) || checked.divisors.contains_key(&v[1]),
                expr::as_const(v[1]).is_some_and(|c| !c.is_zero()) || shift(v[1]),
            ),
            _ => return None,
        };
        // A step of a range test is a place only where the code also uses it as one.
        let used = || block_ref(e, self).is_some() || self.offsets.places.contains(&e);
        let place = || used() || (!self.offsets.ranged.contains(&e) && self.is_offset(e, 0));
        Some(match tested {
            true => Arithmetic::Tested,
            false if safe || place() => Arithmetic::Exempt,
            false => Arithmetic::Untested,
        })
    }

    fn unchecked(&self, e: ExprId) -> bool {
        self.arithmetic(e) == Some(Arithmetic::Untested)
    }

    /* A sum or a product tested against the largest value of a type narrower than a word
    overflows in that type. Printed on bare operands it would read as one of whole words,
    which the test lets through far longer. */
    fn narrow_type(&self, e: ExprId) -> Option<u32> {
        let checked = self.checked.as_ref()?;
        let product = || checked.product_limit_in(e).and_then(|(_, bits)| bits);
        checked.narrow.get(&e).copied().or_else(product)
    }

    #[must_use]
    pub fn tests(&self, e: ExprId) -> bool {
        let mut seen = HashSet::new();
        let mut pending = vec![e];
        while let Some(x) = pending.pop() {
            if !seen.insert(x) || seen.len() > 5000 {
                continue;
            }
            if self.arithmetic(x) == Some(Arithmetic::Tested) {
                return true;
            }
            pending.extend(expr::children(x));
        }
        false
    }

    fn is_offset(&self, e: ExprId, depth: u32) -> bool {
        self.offsets.places.contains(&e)
            || match expr::node(e) {
                Node::Op(op::ADD | op::SUB, v) => v.iter().any(|x| self.is_base(*x, depth)),
                _ => false,
            }
    }

    fn is_base(&self, e: ExprId, depth: u32) -> bool {
        match expr::node(e) {
            Node::Const(_) => false,
            Node::Env(op::CALLDATASIZE | op::RETURNDATASIZE, _) => true,
            Node::MLoad(at, _) if is_free_pointer(at) => true,
            Node::Op(op::ADD | op::SUB, v) if depth < 8 => {
                self.offsets.bases.contains(&e) || v.iter().any(|x| self.is_base(*x, depth + 1))
            }
            _ => self.offsets.bases.contains(&e),
        }
    }

    #[must_use]
    pub fn test_sites(&self, e: ExprId) -> Vec<Site> {
        let Some(checked) = self.checked.as_ref() else {
            return Vec::new();
        };
        let mut sites = checked.ops.get(&e).cloned().unwrap_or_default();
        sites.extend(checked.product_limit(e).into_iter().flatten());
        if let Node::Op(op::DIV | op::SDIV | op::MOD | op::SMOD, v) = expr::node(e) {
            sites.extend(checked.divisors.get(&v[1]).into_iter().flatten());
        }
        sites
    }

    /* A shared value printed under a name changes every expression that holds it. What
    was found about the old expression is true of the new one. */
    pub fn rebind(&mut self, bindings: &[(Node, ExprId)]) {
        for (target, var) in bindings {
            self.bound.insert(*var, expr::intern(target.clone()));
            let mut memo = HashMap::new();
            let named = |n: &Node| (n == target).then_some(*var);
            let sets = [
                &mut self.offsets.places,
                &mut self.offsets.bases,
                &mut self.offsets.ranged,
                &mut self.call_starts,
            ];
            for set in sets {
                let renamed: Vec<ExprId> = set
                    .iter()
                    .map(|e| expr::substitute(*e, &named, &mut memo))
                    .collect();
                set.extend(renamed);
            }
            let Some(checked) = &mut self.checked else {
                continue;
            };
            for set in [&mut checked.ops, &mut checked.divisors] {
                let renamed: Vec<(ExprId, Vec<Site>)> = set
                    .iter()
                    .map(|(e, sites)| (expr::substitute(*e, &named, &mut memo), sites.clone()))
                    .collect();
                for (e, sites) in renamed {
                    set.entry(e).or_insert(sites);
                }
            }
            let renamed: Vec<(ExprId, Limits)> = checked
                .limits
                .iter()
                .map(|(e, l)| (expr::substitute(*e, &named, &mut memo), l.clone()))
                .collect();
            for (e, limits) in renamed {
                checked.limits.entry(e).or_insert(limits);
            }
            let renamed: Vec<(ExprId, u32)> = checked
                .narrow
                .iter()
                .map(|(e, bits)| (expr::substitute(*e, &named, &mut memo), *bits))
                .collect();
            for (e, bits) in renamed {
                checked.narrow.entry(e).or_insert(bits);
            }
            let renamed: Vec<ExprId> = checked
                .untold
                .iter()
                .map(|e| expr::substitute(*e, &named, &mut memo))
                .collect();
            checked.untold.extend(renamed);
        }
        for (target, var) in bindings {
            if self.is_base(expr::intern(target.clone()), 0) {
                self.offsets.bases.insert(*var);
            }
        }
    }

    // A name given to a value has the bits of the value.
    #[must_use]
    pub fn may_bits(&self, e: ExprId) -> U256 {
        let mut value = e;
        for _ in 0..8 {
            match self.bound.get(&value) {
                Some(named) => value = *named,
                None => break,
            }
        }
        expr::may_bits(value)
    }

    pub fn take_temps(&self) -> Vec<(String, String)> {
        std::mem::take(&mut *self.temps.borrow_mut())
    }

    // A temporary is declared where it is first used.
    // A later block must not refer to one declared inside another branch.
    pub fn end_block(&self) {
        self.temp_of.borrow_mut().clear();
        self.memo.borrow_mut().clear();
        self.bare.borrow_mut().clear();
        let mut stale = self.stale.borrow_mut();
        for e in self.block_stale.borrow_mut().drain(..) {
            stale.remove(&e);
        }
    }

    pub fn replace_stale_in_block(&self, loads: impl IntoIterator<Item = (ExprId, String)>) {
        let loads: Vec<(ExprId, String)> = loads.into_iter().collect();
        self.block_stale
            .borrow_mut()
            .extend(loads.iter().map(|(e, _)| *e));
        self.replace_stale(loads);
    }

    pub fn forward(&self, value: ExprId, name: String, place: ExprId) {
        self.forwarded.borrow_mut().insert(value, name);
        self.forward_places.borrow_mut().insert(value, place);
        self.memo.borrow_mut().clear();
    }

    // Text long enough to be moved to a line of its own cannot stand where it is worked out
    // again on every pass, such as a loop test. The names made for it are taken back.
    pub fn without_temps(&self, format: impl FnOnce() -> String) -> Option<String> {
        let made = self.temps.borrow().len();
        let (seq, named, memo) = (
            *self.temp_seq.borrow(),
            self.temp_of.borrow().clone(),
            self.memo.borrow().clone(),
        );
        let text = format();
        if self.temps.borrow().len() == made {
            return Some(text);
        }
        self.temps.borrow_mut().truncate(made);
        *self.temp_seq.borrow_mut() = seq;
        *self.temp_of.borrow_mut() = named;
        *self.memo.borrow_mut() = memo;
        None
    }

    pub fn replace_stale(&self, loads: impl IntoIterator<Item = (ExprId, String)>) {
        let mut stale = self.stale.borrow_mut();
        let before = stale.len();
        stale.extend(loads);
        if stale.len() != before {
            self.memo.borrow_mut().clear();
        }
    }
    fn seq(&self, s: u32) -> u32 {
        let mut m = self.seqs.borrow_mut();
        let n = m.len() as u32 + 1;
        *m.entry(s).or_insert(n)
    }
    fn var(&self, v: u32) -> u32 {
        let mut m = self.vars.borrow_mut();
        let n = m.len() as u32 + 1;
        *m.entry(v).or_insert(n)
    }
    #[must_use]
    pub fn merged(&self) -> Vec<(String, String)> {
        let vars = self.vars.borrow();
        let mut found: Vec<(u32, &str)> = vars
            .iter()
            .map(|(raw, shown)| (*shown, declared_as(expr::var(*raw), self)))
            .collect();
        found.sort_unstable();
        let named = found
            .into_iter()
            .map(|(n, ty)| (format!("v{n}"), ty.to_string()));
        named.collect()
    }
}

// Solidity's order, not C's. In Solidity the bitwise operators bind tighter than the
// comparisons, so `a | b <= c` there means `(a | b) <= c`.
const P_LOR: u8 = 1;
const P_LAND: u8 = 2;
const P_EQ: u8 = 3;
const P_CMP: u8 = 4;
const P_OR: u8 = 5;
const P_XOR: u8 = 6;
const P_AND: u8 = 7;
const P_SHIFT: u8 = 8;
const P_ADD: u8 = 9;
const P_MUL: u8 = 10;
const P_EXP: u8 = 11;
const P_UNARY: u8 = 12;
const P_PRIMARY: u8 = 13;

pub fn fmt_and_operand(e: ExprId, n: &Names) -> String {
    fmt_prec(e, P_LAND, n)
}

pub fn fmt_or_operand(e: ExprId, n: &Names) -> String {
    fmt_prec(e, P_LOR, n)
}

pub fn fmt_const(c: U256) -> String {
    if c.is_zero() {
        return "0".into();
    }
    if c == U256::MAX {
        return "type(uint256).max".into();
    }
    if c < U256::from_u64(1_000_000) {
        return c.to_decimal();
    }
    let dec = c.to_decimal();
    let trimmed = dec.trim_end_matches('0');
    let zeros = dec.len() - trimmed.len();
    if zeros >= 6 && trimmed.len() <= 4 {
        return format!("{}e{}", trimmed, zeros);
    }
    let bits = c.bits();
    if c.is_low_mask() && bits.is_multiple_of(8) && bits < 256 {
        return format!("type(uint{}).max", bits);
    }
    if (150..=160).contains(&bits) && c.byte_len() == 20 {
        return c.to_hex_padded(20);
    }
    if c.is_power_of_two() && bits > 32 {
        return format!("2**{}", bits - 1);
    }
    c.to_hex()
}

fn fmt_int_const(c: U256) -> String {
    if c.is_negative() {
        format!("-{}", fmt_const(-c))
    } else {
        fmt_const(c)
    }
}

pub fn is_selector_expr(e: ExprId) -> bool {
    match expr::node(e) {
        Node::Op(op::SHR, v) => {
            expr::as_const(v[0]) == Some(U256::from_u64(224))
                && matches!(expr::node(v[1]), Node::CallDataLoad(o) if expr::as_const(o) == Some(U256::ZERO))
        }
        Node::Op(op::AND, v) => {
            (is_selector_expr(v[0]) && expr::as_const(v[1]) == Some(U256::from_u64(0xffffffff)))
                || (expr::as_const(v[1]) == Some(U256::from_u64(0xffffffff) << 224)
                    && matches!(expr::node(v[0]), Node::CallDataLoad(o) if expr::as_const(o) == Some(U256::ZERO)))
        }
        Node::Op(op::DIV, v) => {
            expr::as_const(v[1]) == Some(U256::ONE << 224)
                && matches!(expr::node(v[0]), Node::CallDataLoad(o) if expr::as_const(o) == Some(U256::ZERO))
        }
        _ => false,
    }
}

pub fn selector_compare(e: ExprId) -> Option<u32> {
    if let Node::Op(op::EQ, v) = expr::node(e) {
        return selector_operands(&v);
    }
    None
}

pub fn selector_mismatch(e: ExprId) -> Option<u32> {
    if let Node::Op(o, v) = expr::node(e) {
        if o == op::XOR || o == op::SUB {
            return selector_operands(&v);
        }
    }
    None
}

fn selector_operands(v: &[ExprId]) -> Option<u32> {
    for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
        if is_selector_expr(a) {
            if let Some(c) = expr::as_const(b) {
                if c.fits_u64() && c.low_u64() <= u32::MAX as u64 {
                    return Some(c.low_u64() as u32);
                }
            }
        }
    }
    None
}

pub fn calldata_word_index(off: ExprId) -> Option<u32> {
    let c = expr::as_const(off)?;
    if c < U256::from_u64(4) || !c.fits_u64() {
        return None;
    }
    let o = c.low_u64() - 4;
    if o % 32 == 0 && o / 32 < 64 {
        Some((o / 32) as u32)
    } else {
        None
    }
}

fn paren(s: String, inner: u8, outer: u8) -> String {
    if inner < outer {
        format!("({})", s)
    } else {
        s
    }
}

pub fn fmt_expr(e: ExprId, n: &Names) -> String {
    fmt_prec(e, 0, n)
}

thread_local! {
    static NESTED: Cell<u32> = const { Cell::new(0) };
}

// The printer calls itself once per level of an expression. Past this many levels the
// parts are printed first, smallest first, so every later call finds its parts done.
const MAX_NESTED: u32 = 64;

struct Level(u32);

impl Drop for Level {
    fn drop(&mut self) {
        NESTED.with(|d| d.set(self.0));
    }
}

fn fmt_parts_first(e: ExprId, n: &Names) {
    let mut parts = Vec::new();
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if seen.insert(x) {
            parts.push(x);
            stack.extend(expr::children(x));
        }
    }
    parts.sort_by_key(|x| expr::depth(*x));
    for part in parts {
        if part != e {
            fmt_prec(part, 0, n);
        }
    }
}

fn fmt_prec(e: ExprId, outer: u8, n: &Names) -> String {
    if let Some(a) = n.aliases.get(&e) {
        return a.clone();
    }
    if let Some(a) = n.stale.borrow().get(&e) {
        return a.clone();
    }
    if let Some(a) = n.forwarded.borrow().get(&e) {
        return a.clone();
    }
    if let Some(t) = n.temp_of.borrow().get(&e) {
        return t.clone();
    }
    if let Some((s, p)) = n.memo.borrow().get(&e) {
        return paren(s.clone(), *p, outer);
    }
    let level = NESTED.with(Cell::get);
    let _restore = Level(level);
    if level >= MAX_NESTED {
        NESTED.with(|d| d.set(0));
        fmt_parts_first(e, n);
    }
    NESTED.with(|d| d.set(level + 1));
    let (s, p) = fmt_inner(e, n);
    if s.len() > TEMP_THRESHOLD && !matches!(expr::node(e), Node::Const(_)) {
        *n.temp_seq.borrow_mut() += 1;
        let name = format!("t{}", n.temp_seq.borrow());
        n.temps.borrow_mut().push((name.clone(), s));
        n.temp_of.borrow_mut().insert(e, name.clone());
        return name;
    }
    n.memo.borrow_mut().insert(e, (s.clone(), p));
    paren(s, p, outer)
}

// The declared types of an event a file can name, for a file a compiler has to take.
fn known_event_types(topics: &[ExprId], n: &Names) -> Vec<String> {
    let first = topics.first().and_then(|t| expr::as_const(*t));
    let known = first.and_then(|t0| sigs::event(&t0.to_be_bytes()));
    match known.filter(|_| n.strict) {
        Some(sig) => sigs::params_of(&sig),
        None => Vec::new(),
    }
}

fn as_declared(ty: &str, e: ExprId, n: &Names) -> String {
    match ty {
        "uint256" => as_word(e, n),
        "address" | "bool" => as_type(ty, e, n),
        _ if width_of(ty).is_some() || ty.starts_with("bytes") && ty.len() > 5 => as_type(ty, e, n),
        _ => fmt_expr(e, n),
    }
}

pub fn fmt_log_parts(topics: &[ExprId], data_args: Vec<String>, n: &Names) -> String {
    let mut args: Vec<String> = Vec::new();
    let mut name = None;
    if let Some(t0) = topics.first().and_then(|t| expr::as_const(*t)) {
        if let Some(sig) = sigs::event(&t0.to_be_bytes()) {
            name = Some(sigs::name_of(&sig).to_string());
        }
    }
    let start = if name.is_some() { 1 } else { 0 };
    let types = known_event_types(topics, n);
    for (i, t) in topics[start..].iter().enumerate() {
        args.push(match types.get(i) {
            Some(ty) => as_declared(ty, *t, n),
            None => fmt_expr(*t, n),
        });
    }
    args.extend(data_args);
    match name {
        Some(nm) => format!("emit {}({});", nm, args.join(", ")),
        None => match topics.first().and_then(|t| expr::as_const(*t)) {
            /* An event known only by its first topic is declared anonymous, with the
            topic as its first indexed value. Every other value is declared a word, which
            is what it is in the log whatever type the author gave it. */
            Some(t0) if n.strict => {
                let mut words = vec![t0.to_hex_padded(32)];
                words.extend(topics[1..].iter().map(|t| as_word(*t, n)));
                words.extend(args[topics.len()..].iter().cloned());
                format!("emit {}({});", event_placeholder_name(t0), words.join(", "))
            }
            Some(t0) => format!(
                "emit {}({});",
                event_placeholder_name(t0),
                args[1..].join(", ")
            ),
            None => format!("log{}({});", topics.len(), args.join(", ")),
        },
    }
}

pub fn is_add_const(e: ExprId, base: ExprId, k: u64) -> bool {
    match expr::node(e) {
        Node::Op(op::ADD, v) => {
            (v[0] == base && expr::as_const(v[1]) == Some(U256::from_u64(k)))
                || (v[1] == base && expr::as_const(v[0]) == Some(U256::from_u64(k)))
        }
        _ => false,
    }
}

fn written_range(s: &Stmt) -> Option<(u64, u64)> {
    match s {
        Stmt::MStore { off, width, .. } => {
            let o = expr::as_const(*off)?.as_usize()? as u64;
            Some((o, o.checked_add(*width as u64)?))
        }
        Stmt::Copy { dest, len, .. } => {
            let d = expr::as_const(*dest)?.as_usize()? as u64;
            let l = expr::as_const(*len)?.as_usize()? as u64;
            Some((d, d.checked_add(l)?))
        }
        _ => None,
    }
}

fn reads_memory(s: &Stmt) -> bool {
    match s {
        Stmt::MStore { .. } | Stmt::SStore { .. } | Stmt::Assign { .. } | Stmt::Drop(_) => {
            // A word copied from call data or code is fixed by its source.
            // Only one copied from memory depends on what memory held.
            let from_memory = |n: &Node| matches!(n, Node::CopiedWord(op::MCOPY, ..));
            crate::lift::stmt_exprs(s).iter().any(|e| {
                expr::holds(*e, kind::MLOAD | kind::KECCAK_MEM)
                    || (expr::holds(*e, kind::COPIED_WORD) && expr::contains(*e, &from_memory))
            })
        }
        Stmt::Copy { kind, .. } => *kind == op::MCOPY,
        _ => true,
    }
}

// A store that is overwritten is overwritten soon after.
// Looking further made a long run of stores quadratic.
const DEAD_STORE_WINDOW: usize = 256;

fn own_word(s: &Stmt) -> Option<(ExprId, u32, u32)> {
    let Stmt::MStore {
        off,
        val,
        width: 32,
        gen,
    } = s
    else {
        return None;
    };
    match expr::node(*val) {
        Node::MLoad(at, read) if at == *off => Some((at, read, *gen)),
        _ => None,
    }
}

/* A word stored to itself changes nothing, unless it was read before another store to it.
Then the store puts the old word back, and with it left out the other store would stand
for good. */
pub fn stores_put_back(l: &Lifted) -> HashSet<(usize, usize)> {
    let mut at: HashMap<ExprId, Vec<(u32, usize, usize)>> = HashMap::new();
    for nd in &l.nodes {
        for (i, s) in nd.stmts.iter().enumerate() {
            let word = match s {
                Stmt::MStore { off, gen, .. } => Some((*off, *gen)),
                Stmt::Copy { dest, gen, .. } => Some((*dest, *gen)),
                _ => None,
            };
            if let Some((word, gen)) = word.filter(|_| own_word(s).is_none()) {
                at.entry(word).or_default().push((gen, nd.id, i));
            }
        }
    }
    let mut put_back = HashSet::new();
    for nd in &l.nodes {
        for (i, s) in nd.stmts.iter().enumerate() {
            let Some((word, read, gen)) = own_word(s) else {
                continue;
            };
            // The stores of a folded helper share one version, so their order tells.
            let between = |(stored, node, j): &(u32, usize, usize)| {
                *stored > read && (*stored < gen || (*stored == gen && *node == nd.id && *j < i))
            };
            if at
                .get(&word)
                .is_some_and(|stores| stores.iter().any(between))
            {
                put_back.insert((nd.id, i));
            }
        }
    }
    put_back
}

pub fn on_node(places: &HashSet<(usize, usize)>, node: usize) -> HashSet<usize> {
    let here = places.iter().filter(|(n, _)| *n == node);
    here.map(|(_, i)| *i).collect()
}

pub fn dead_memory_stores(stmts: &[Stmt], put_back: &HashSet<usize>) -> HashSet<usize> {
    let mut dead = HashSet::new();
    let reads: Vec<bool> = stmts.iter().map(reads_memory).collect();
    let ranges: Vec<Option<(u64, u64)>> = stmts.iter().map(written_range).collect();
    for (i, s) in stmts.iter().enumerate() {
        if let Some((word, _, _)) = own_word(s) {
            // With no read between the two, the store it undoes was never seen either.
            let stored = |j: &usize| match &stmts[*j] {
                Stmt::MStore { off: at, .. } | Stmt::Copy { dest: at, .. } => *at == word,
                _ => false,
            };
            let unread = (0..i).rev().take_while(|j| !reads[*j]).find(stored);
            if !put_back.contains(&i) || unread.is_some() {
                dead.extend(unread.into_iter().chain([i]));
                continue;
            }
        }
        let Some((lo, hi)) = ranges[i] else {
            continue;
        };
        for later in (i + 1..stmts.len()).take(DEAD_STORE_WINDOW) {
            if let Some((l2, h2)) = ranges[later] {
                if l2 <= lo && h2 >= hi {
                    dead.insert(i);
                    break;
                }
            }
            if reads[later] {
                break;
            }
        }
    }
    dead
}

fn is_abi_validator(cond: ExprId) -> bool {
    let Node::Op(op::EQ, v) = expr::node(cond) else {
        return false;
    };
    /* The type in the signature says this of a parameter in the head. For a word found
    through an offset, an element of an array say, only the test itself says it. */
    let is_param = |e: ExprId| match expr::node(e) {
        Node::CallDataLoad(at) => calldata_word_index(at).is_some(),
        _ => false,
    };
    let cleaned = |x: ExprId, y: ExprId| -> bool {
        match expr::node(y) {
            Node::Op(op::AND, w) => {
                (w[0] == x && expr::as_const(w[1]) == Some(expr::mask_bits(160)))
                    || (w[1] == x && expr::as_const(w[0]) == Some(expr::mask_bits(160)))
            }
            Node::Op(op::ISZERO, w) => {
                matches!(expr::node(w[0]), Node::Op(op::ISZERO, z) if z[0] == x)
            }
            _ => false,
        }
    };
    (is_param(v[0]) && cleaned(v[0], v[1])) || (is_param(v[1]) && cleaned(v[1], v[0]))
}

pub fn is_hidden_require(cond: ExprId, data: Option<&[ExprId]>, n: &Names) -> bool {
    if is_abi_validator(cond) {
        return true;
    }
    if !n.hide_checked || n.checked.as_ref().is_some_and(|c| c.untold.contains(&cond)) {
        return false;
    }
    let Some(words) = data else {
        return false;
    };
    if words.len() < 2 || leading_selector(words[0], None) != Some(SEL_PANIC) {
        return false;
    }
    let len = 4 + 32 * (words.len() - 1);
    matches!(
        expr::as_const(shifted_word_len(words, 0, Some(len))),
        Some(c) if [PANIC_OVERFLOW, PANIC_DIV_BY_ZERO].contains(&c.low_u64())
            && c.fits_u64()
    )
}

pub const SEL_PANIC: u32 = 0x4e487b71;
pub const SEL_ERROR: u32 = 0x08c379a0;
const PANIC_OVERFLOW: u64 = 0x11;
const PANIC_DIV_BY_ZERO: u64 = 0x12;
const PANIC_EMPTY_POP: u64 = 0x31;

// A flag by its declared type, which only counts where the output has to be typed.
fn declared_flag(e: ExprId, n: &Names) -> bool {
    let typed = |ty: Option<&String>| ty.is_some_and(|t| t == "bool");
    match expr::node(e) {
        Node::CallDataLoad(off) => {
            typed(calldata_word_index(off).and_then(|i| n.param_types.get(&i)))
        }
        Node::Arg(i) => typed(n.arg_types.get(&i)),
        _ => false,
    }
}

pub fn is_bool(e: ExprId, n: &Names) -> bool {
    // A value two paths give is a flag in a file only where it is declared one. The
    // mark on the expression is shared by every function that numbers a value alike.
    if n.strict && matches!(expr::node(e), Node::Var(_)) {
        return n.bools.contains(&e);
    }
    let joined = |e: ExprId| match expr::node(e) {
        Node::Op(op::OR | op::AND, v) => logical(&v, n),
        _ => false,
    };
    expr::is_boolean(e)
        || (n.strict && (declared_flag(e, n) || joined(e)))
        || n.bools.contains(&e)
        || packed_read(e).is_some_and(|(k, off, bits)| n.bool_fields.contains(&(k, off, bits)))
        || bool_element(e, n)
}

// A constant operand is a mask. Only a type that was guessed could make it a truth value.
fn logical(v: &[ExprId], n: &Names) -> bool {
    v.iter().all(|x| is_bool(*x, n) && !expr::is_const(*x))
}

fn bool_element(e: ExprId, n: &Names) -> bool {
    let load = element_typed_load(e, n).unwrap_or(e);
    match expr::node(load) {
        Node::SLoad(key, false, _) => element_root(key)
            .and_then(|r| n.elem_types.get(&r))
            .is_some_and(|t| t == "bool"),
        _ => false,
    }
}

/* What follows is only for output a compiler has to accept. There an address is not a
number: it is compared with `address(0)`, and a number becomes one through a cast. */
fn is_address(e: ExprId, n: &Names) -> bool {
    let typed = |ty: Option<&String>| ty.is_some_and(|t| t == "address");
    match expr::node(e) {
        Node::Op(op::AND, v) => expr::as_const(v[1]) == Some(expr::mask_bits(160)),
        Node::Env(o, _) => matches!(o, op::CALLER | op::ORIGIN | op::ADDRESS | op::COINBASE),
        Node::SLoad(key, false, _) => match expr::as_const(key) {
            Some(slot) => typed(n.storage_types.get(&slot)),
            None => typed(element_root(key).and_then(|r| n.elem_types.get(&r))),
        },
        Node::CallDataLoad(off) => {
            typed(calldata_word_index(off).and_then(|i| n.param_types.get(&i)))
        }
        Node::Arg(i) => typed(n.arg_types.get(&i)),
        Node::Var(_) => n.addresses.contains(&e),
        _ => false,
    }
}

// A value the text gives a type shorter than a word: a cast, or a variable sharing a slot.
fn short_number(e: ExprId, n: &Names) -> bool {
    let cast = |m: U256| m.is_low_mask() && m.bits() < 256 && m.bits().is_multiple_of(8);
    match expr::node(e) {
        Node::Op(op::AND, v) => expr::as_const(v[1]).is_some_and(cast),
        _ => packed_read(e).is_some_and(|field| n.fields.contains_key(&field)),
    }
}

/* A compiler does no sums on a flag or an address, which the bytecode does freely. It
also does a sum of two short numbers in their own short type, where the bytecode does
every sum on whole words. */
fn fmt_number(e: ExprId, outer: u8, n: &Names) -> String {
    if !n.strict || expr::is_const(e) {
        return fmt_prec(e, outer, n);
    }
    if is_bool(e, n) || is_address(e, n) {
        return as_word(e, n);
    }
    match short_number(e, n) {
        true => format!("uint256({})", fmt_expr(e, n)),
        false => fmt_prec(e, outer, n),
    }
}

// The variables that share one slot, from the lowest byte up, each with its type.
fn sharing(key: ExprId, n: &Names) -> Vec<(u32, u32, &String, &str)> {
    let Some(slot) = expr::as_const(key) else {
        return Vec::new();
    };
    let own = n.fields.iter().filter(|((at, _, _), _)| *at == slot);
    let mut all: Vec<(u32, u32, &String, &str)> = own
        .map(|(field, name)| {
            let ty = n.field_types.get(field).map_or("", String::as_str);
            (field.1, field.2, name, ty)
        })
        .collect();
    all.sort_unstable();
    all
}

/* A slot several variables share has no name of its own in a file. Read whole it is the
variables side by side, and a write of the whole word is a write to each of them. */
fn whole_packed(key: ExprId, n: &Names) -> Option<String> {
    let word = |(offset, _, name, ty): &(u32, u32, &String, &str)| {
        let number = match *ty {
            "bool" => format!("({name} ? 1 : 0)"),
            "address" => format!("uint256(uint160({name}))"),
            _ => format!("uint256({name})"),
        };
        match offset {
            0 => number,
            _ => format!("{number} << {}", 8 * offset),
        }
    };
    let parts: Vec<String> = sharing(key, n).iter().map(word).collect();
    (!parts.is_empty()).then(|| format!("({})", parts.join(" | ")))
}

fn packed_store(key: ExprId, val: ExprId, n: &Names) -> Option<String> {
    let whole = fmt_prec(val, P_SHIFT + 1, n);
    let given = |(offset, bits, name, ty): &(u32, u32, &String, &str)| {
        let part = match offset {
            0 => fmt_expr(val, n),
            _ => format!("{whole} >> {}", 8 * offset),
        };
        let value = match *ty {
            "bool" => format!("uint8({part}) != 0"),
            "address" => format!("address(uint160({part}))"),
            "" => format!("uint{bits}({part})"),
            ty => format!("{ty}({part})"),
        };
        format!("{name} = {value};")
    };
    let writes: Vec<String> = sharing(key, n).iter().map(given).collect();
    (!writes.is_empty()).then(|| writes.join(" "))
}

// A flag is not ordered for a compiler, nor is an address against a number.
fn fmt_ordered(e: ExprId, other: ExprId, n: &Names) -> String {
    let flag = is_bool(e, n) && !expr::is_const(e);
    let lone = is_address(e, n) && !is_address(other, n);
    match n.strict && (flag || lone) {
        true => as_word(e, n),
        false => fmt_prec(e, P_CMP + 1, n),
    }
}

// A hash is thirty-two bytes to a compiler, and a number wherever this text uses it.
fn hash_word(text: String, n: &Names) -> String {
    match n.strict {
        true => format!("uint256({text})"),
        false => text,
    }
}

fn handed_word(e: ExprId, n: &Names) -> Option<String> {
    n.handed.get(&e).map(|number| format!("s{number}_0"))
}

fn declared_as(var: ExprId, n: &Names) -> &'static str {
    match (n.bools.contains(&var), n.addresses.contains(&var)) {
        (true, _) => "bool",
        (false, true) => "address",
        (false, false) => "uint256",
    }
}

/* A value two paths give is declared once, with one type. In a file for a compiler
every path gives it as that type. */
pub fn fmt_assigned(var: ExprId, val: ExprId, n: &Names) -> String {
    if let Some(word) = handed_word(val, n) {
        return word;
    }
    if !n.strict || !matches!(expr::node(var), Node::Var(_)) {
        return fmt_expr(val, n);
    }
    match (declared_as(var, n), expr::as_const(val)) {
        ("bool", Some(c)) => (!c.is_zero()).to_string(),
        ("bool", None) => fmt_cond(val, n),
        ("address", _) => as_address(val, n),
        _ => as_word(val, n),
    }
}

// A merged value is an address when every path gives it one, or gives it nothing.
pub fn note_address_vars(l: &Lifted, n: &mut Names) {
    let mut given: HashMap<ExprId, Vec<ExprId>> = HashMap::new();
    for (var, val) in l.edge_assigns.values().flatten() {
        given.entry(*var).or_default().push(*val);
    }
    for s in l.nodes.iter().flat_map(|nd| &nd.stmts) {
        if let Stmt::Assign { var, value } = s {
            given.entry(*var).or_default().push(*value);
        }
    }
    loop {
        let empty = |v: &ExprId| expr::as_const(*v).is_some_and(|c| c.is_zero());
        let fits = |vals: &Vec<ExprId>| {
            vals.iter().all(|v| is_address(*v, n) || empty(v))
                && vals.iter().any(|v| is_address(*v, n))
        };
        let new = |var: &ExprId| !n.addresses.contains(var) && !n.bools.contains(var);
        let found: Vec<ExprId> = given
            .iter()
            .filter(|(var, vals)| new(var) && fits(vals))
            .map(|(var, _)| *var)
            .collect();
        if found.is_empty() {
            return;
        }
        n.addresses.extend(found);
    }
}

fn zero_of(e: ExprId, n: &Names) -> &'static str {
    match n.strict && is_address(e, n) {
        true => "address(0)",
        false => "0",
    }
}

fn as_address(e: ExprId, n: &Names) -> String {
    match expr::as_const(e) {
        Some(c) if c.is_zero() => "address(0)".to_string(),
        Some(c) => format!("address({})", c.to_hex_padded(20)),
        None if is_address(e, n) => fmt_expr(e, n),
        None => format!("address(uint160({}))", fmt_expr(e, n)),
    }
}

fn as_word(e: ExprId, n: &Names) -> String {
    if is_address(e, n) {
        return format!("uint256(uint160({}))", fmt_expr(e, n));
    }
    match is_bool(e, n) && !expr::is_const(e) {
        true => format!("({} ? 1 : 0)", fmt_expr(e, n)),
        false => fmt_expr(e, n),
    }
}

fn width_of(ty: &str) -> Option<u32> {
    match ty {
        "address" => Some(160),
        "bool" => Some(8),
        _ => ty.strip_prefix("uint").and_then(|d| d.parse().ok()),
    }
}

fn as_type(ty: &str, e: ExprId, n: &Names) -> String {
    match ty {
        "address" => as_address(e, n),
        "bool" if expr::is_const(e) => (expr::as_const(e) != Some(U256::ZERO)).to_string(),
        "bool" if is_bool(e, n) => fmt_expr(e, n),
        "bool" => format!("{} != 0", fmt_prec(e, P_EQ + 1, n)),
        _ => format!("{ty}({})", as_word(e, n)),
    }
}

pub fn fmt_cond(cond: ExprId, n: &Names) -> String {
    if let Some(text) = difference_test(cond, n) {
        return text;
    }
    if is_bool(cond, n) {
        fmt_expr(cond, n)
    } else {
        format!("{} != {}", fmt_prec(cond, P_EQ + 1, n), zero_of(cond, n))
    }
}

pub fn fmt_truth(cond: ExprId, n: &Names) -> String {
    if n.strict {
        return fmt_cond(cond, n);
    }
    difference_test(cond, n).unwrap_or_else(|| fmt_expr(cond, n))
}

fn difference_test(cond: ExprId, n: &Names) -> Option<String> {
    let (inner, sym) = match expr::node(cond) {
        Node::Op(op::ISZERO, v) => (v[0], "=="),
        _ => (cond, "!="),
    };
    let Node::Op(op::SUB | op::XOR, v) = expr::node(inner) else {
        return None;
    };
    let (left, right) = match expr::as_const(v[0]).is_some() && expr::as_const(v[1]).is_none() {
        true => (v[1], v[0]),
        false => (v[0], v[1]),
    };
    Some(format!(
        "{} {sym} {}",
        fmt_prec(left, P_EQ + 1, n),
        fmt_prec(right, P_EQ + 1, n)
    ))
}

pub fn event_placeholder_name(topic0: U256) -> String {
    let b = topic0.to_be_bytes();
    format!("Event_{:08x}", u32::from_be_bytes([b[0], b[1], b[2], b[3]]))
}

// solc's ABI size checks are signed compares on a value that cannot be negative.
fn size_compare(o: u8, a: ExprId, b: ExprId, n: &Names) -> Option<String> {
    let k = expr::as_const(b)?;
    let (base, c) = expr::split_offset(a);
    let base = base?;
    let name = fmt_expr(base, n);
    if name != "msg.data.length" && name != "returndatasize()" {
        return None;
    }
    let bound = k.wrapping_sub(c);
    if bound.bits() > 64 {
        return None;
    }
    let sym = if o == op::SLT { "<" } else { ">" };
    Some(format!("{} {} {}", name, sym, bound.low_u64()))
}

fn is_signed_op(o: u8) -> bool {
    matches!(o, op::SLT | op::SGT | op::SDIV | op::SMOD | op::SAR)
}

pub type Blocks = HashMap<Option<ExprId>, Vec<(U256, u32)>>;

pub(crate) fn is_free_pointer(off: ExprId) -> bool {
    expr::as_const(off) == Some(U256::from_u64(FREE_POINTER))
}

#[must_use]
pub fn number_blocks(l: &Lifted) -> Blocks {
    let mut starts: Vec<ExprId> = l.entry_free_pointer().into_iter().collect();
    let mut seen: HashSet<ExprId> = HashSet::new();
    let mut note_loads = |roots: Vec<ExprId>, starts: &mut Vec<ExprId>| {
        let mut found: Vec<(u32, ExprId)> = Vec::new();
        let mut stack = roots;
        while let Some(x) = stack.pop() {
            if !seen.insert(x) {
                continue;
            }
            if let Node::MLoad(off, version) = expr::node(x) {
                if is_free_pointer(off) {
                    found.push((version, x));
                }
            }
            stack.extend(expr::children(x));
        }
        found.sort_unstable();
        starts.extend(found.into_iter().map(|(_, x)| x));
    };
    for nd in &l.nodes {
        for st in &nd.stmts {
            note_loads(crate::lift::stmt_exprs(st), &mut starts);
            if let Stmt::MStore {
                off,
                val,
                width: 32,
                ..
            } = st
            {
                if is_free_pointer(*off) {
                    starts.push(*val);
                }
            }
        }
        note_loads(crate::lift::term_exprs(&nd.term), &mut starts);
    }
    note_loads(
        l.edge_assigns
            .values()
            .flatten()
            .map(|(_, val)| *val)
            .collect(),
        &mut starts,
    );
    let mut blocks = Blocks::new();
    let mut number = 0;
    for start in starts {
        let (base, offset) = expr::split_offset(start);
        // Solidity before 0.4.22 starts its free memory at 0x60.
        if base.is_none() && offset < U256::from_u64(0x60) {
            continue;
        }
        let at = blocks.entry(base).or_default();
        if !at.iter().any(|(o, _)| *o == offset) {
            number += 1;
            at.push((offset, number));
        }
    }
    blocks
}

pub(crate) fn block_ref(e: ExprId, n: &Names) -> Option<(u32, U256)> {
    let blocks = n.blocks.as_ref()?;
    let (base, offset) = expr::split_offset(e);
    blocks
        .get(&base)?
        .iter()
        .filter(|(start, _)| *start <= offset)
        .max_by_key(|(start, _)| *start)
        .map(|(start, number)| (*number, offset.wrapping_sub(*start)))
}

fn fmt_block_ref(number: u32, offset: U256) -> String {
    if offset.is_zero() {
        format!("ptr{number}")
    } else {
        format!("ptr{number} + {}", offset.to_decimal())
    }
}

/* A word whose first four bytes alone are set, stored where the data of a call starts, is
the selector of that call. The word itself is what the store writes, so the name says
only which function the four bytes stand for. */
fn stored_selector(off: ExprId, val: ExprId, n: &Names) -> Option<String> {
    let word = expr::as_const(val).filter(|_| n.call_starts.contains(&off))?;
    let selector = (word >> 224).low_u64() as u32;
    let bare = selector != 0 && (word & expr::mask_bits(224)).is_zero();
    let sig = sigs::function(selector).filter(|_| bare)?;
    Some(format!("bytes32({}.selector)", sigs::name_of(&sig)))
}

fn fmt_stored_word(val: ExprId, n: &Names) -> String {
    match (expr::as_const(val), block_ref(val, n)) {
        (Some(_), Some((number, offset))) if offset.is_zero() => format!("ptr{number}"),
        _ => fmt_expr(val, n),
    }
}

#[must_use]
pub fn free_pointer_updates(stmts: &[Stmt], n: &Names) -> HashSet<usize> {
    // A file states each one, as the taking of a block.
    if n.blocks.is_none() || n.strict {
        return HashSet::new();
    }
    stmts
        .iter()
        .enumerate()
        .filter(|(_, s)| matches!(s, Stmt::MStore { off, .. } if is_free_pointer(*off)))
        .map(|(i, _)| i)
        .collect()
}

#[derive(Clone, Debug)]
pub struct BlockLiteral {
    pub first: usize,
    pub rest: Vec<usize>,
    pub text: String,
}

// Blocks do not overlap, so the stores to one may be gathered past stores to others.
#[must_use]
pub fn block_literals(stmts: &[Stmt], hidden: &HashSet<usize>, n: &Names) -> Vec<BlockLiteral> {
    let word_of = |s: &Stmt| -> Option<(u32, u64, ExprId)> {
        let Stmt::MStore {
            off,
            val,
            width: 32,
            ..
        } = s
        else {
            return None;
        };
        let (number, offset) = block_ref(*off, n).filter(|(k, _)| !n.scalars.contains_key(k))?;
        let aligned =
            offset.fits_u64() && offset.low_u64().is_multiple_of(32) && offset.low_u64() < 32 * 64;
        let reads_memory = expr::contains(*val, &|x| matches!(x, Node::MLoad(..)));
        (aligned && !reads_memory).then(|| (number, offset.low_u64() / 32, *val))
    };
    /* A test that reads no memory says the same before a store as after it, and when it
    fails the store is undone with all else. The stores on its two sides are one run. */
    let reads = kind::MLOAD | kind::KECCAK_MEM | kind::COPIED_WORD;
    let passed = |s: &Stmt| {
        matches!(s, Stmt::Require { .. })
            && !crate::lift::stmt_exprs(s)
                .iter()
                .any(|e| expr::holds(*e, reads))
    };
    let live: Vec<usize> = (0..stmts.len()).filter(|i| !hidden.contains(i)).collect();
    let mut out = Vec::new();
    let mut at = 0;
    while at < live.len() {
        let mut end = at;
        let stored = |i: usize| word_of(&stmts[live[i]]).is_some();
        while end < live.len() && (stored(end) || (end > at && passed(&stmts[live[end]]))) {
            end += 1;
        }
        let mut by_block: BTreeMap<u32, Vec<(usize, u64, ExprId)>> = BTreeMap::new();
        for i in &live[at..end] {
            if let Some((number, index, val)) = word_of(&stmts[*i]) {
                by_block.entry(number).or_default().push((*i, index, val));
            }
        }
        for (number, words) in by_block {
            let mut sorted = words.clone();
            sorted.sort_by_key(|(_, index, _)| *index);
            let dense = sorted
                .iter()
                .map(|(_, index, _)| *index)
                .eq(0..sorted.len() as u64);
            if sorted.len() < 2 || !dense {
                continue;
            }
            let raw: Vec<ExprId> = sorted.iter().map(|(_, _, v)| *v).collect();
            let text = decode_plain_string(&raw)
                .filter(|_| {
                    expr::as_const(raw[0])
                        .and_then(|l| l.as_usize())
                        .is_some_and(|l| l.div_ceil(32) == raw.len() - 1)
                })
                .map(|t| format!("\"{t}\""));
            // In a file a block is written a word at a time, into memory it has taken.
            if n.strict && text.is_none() {
                continue;
            }
            let values: Vec<String> = match text {
                Some(t) => vec![t],
                None => raw.iter().map(|v| fmt_stored_word(*v, n)).collect(),
            };
            let mut indices: Vec<usize> = words.iter().map(|(i, _, _)| *i).collect();
            indices.sort_unstable();
            out.push(BlockLiteral {
                first: indices[0],
                rest: indices[1..].to_vec(),
                text: format!("ptr{number} = memory({});", values.join(", ")),
            });
        }
        at = end.max(at + 1);
    }
    out
}

const WORD: u64 = 32;

/* One word of a block the function keeps to itself. A block of one word is a local
value. A longer one is a struct in memory, as it was for the author, which keeps the
function within the few values a compiler can reach at once. */
fn scalar_word(off: ExprId, n: &Names) -> Option<String> {
    let (number, offset) = block_ref(off, n)?;
    let words = *n.scalars.get(&number)?;
    let index = offset.low_u64() / WORD;
    let whole = offset.fits_u64() && offset.low_u64().is_multiple_of(WORD) && index < words;
    match (whole, words) {
        (false, _) => None,
        (true, 1) => Some(format!("s{number}_0")),
        (true, _) => Some(format!("s{number}.w{index}")),
    }
}

pub fn fmt_mem_word(off: ExprId, n: &Names) -> String {
    if let Some(name) = scalar_word(off, n) {
        return name;
    }
    if n.layout != MappingLayout::Vyper {
        return format!("mem[{}]", fmt_mem_off(off, n));
    }
    let local = |c: U256| {
        (c.fits_u64() && c.low_u64() >= 2 * WORD && c.low_u64().is_multiple_of(WORD))
            .then(|| format!("loc_{:x}", c.low_u64()))
    };
    let scaled = |e: ExprId| match expr::node(e) {
        Node::Op(op::MUL, v) => [(v[0], v[1]), (v[1], v[0])]
            .into_iter()
            .find(|(_, by)| expr::as_const(*by) == Some(U256::from_u64(WORD)))
            .map(|(index, _)| index),
        Node::Op(op::SHL, v) if expr::as_const(v[0]) == Some(U256::from_u64(5)) => Some(v[1]),
        _ => None,
    };
    let named = match expr::split_offset(off) {
        (None, c) => local(c),
        (Some(base), c) => local(c)
            .zip(scaled(base))
            .map(|(name, index)| format!("{name}[{}]", fmt_expr(index, n))),
    };
    named.unwrap_or_else(|| format!("mem[{}]", fmt_mem_off(off, n)))
}

// A place is spelled the way a store to it spells it, so one buffer has one spelling.
fn fmt_mem_at(e: ExprId, n: &Names) -> String {
    match (expr::as_const(e), block_ref(e, n)) {
        (Some(_), Some((number, offset))) => fmt_block_ref(number, offset),
        (Some(c), None) if !c.is_zero() && c.bits() <= 64 => c.to_hex(),
        _ => fmt_expr(e, n),
    }
}

pub fn fmt_mem_range(off: ExprId, len: ExprId, n: &Names) -> String {
    let start = fmt_mem_at(off, n);
    let end = expr::op2(op::ADD, off, len);
    let (past, from) = expr::split_offset(end);
    match past {
        Some(past) if expr::as_const(off) == Some(from) && block_ref(off, n).is_some() => {
            format!("mem[{start}:{start} + {}]", fmt_prec(past, P_ADD, n))
        }
        _ => format!("mem[{start}:{}]", fmt_mem_at(end, n)),
    }
}

/* Memory the file may write to: a block it has taken, or whatever an address that was
handed to it points at. A block not taken yet is free memory, where a compiler puts
values of its own between two lines of the text, and a fixed address is scratch space it
uses as well. A write to either is left in the notation no compiler reads. */
fn owned_memory(off: ExprId, n: &Names) -> bool {
    if !n.strict || n.layout == MappingLayout::Vyper {
        return false;
    }
    let within = block_ref(off, n).map(|(number, _)| number);
    match (
        within.or_else(|| block_started(off, n)),
        expr::split_offset(off).0,
    ) {
        (Some(number), _) => n.taken.borrow().contains(&number),
        (None, base) => base.is_some(),
    }
}

fn block_started(e: ExprId, n: &Names) -> Option<u32> {
    match (block_ref(e, n), expr::node(e)) {
        (Some((number, at)), _) if at.is_zero() => Some(number),
        (_, Node::Op(op::ADD, v)) => v.iter().find_map(|x| block_started(*x, n)),
        _ => None,
    }
}

/* The code takes a block by moving the start of free memory past it. A file does the
same, so the block is memory nothing else is put in, and names the block by a value of
its own. A block the function keeps as local values needs no memory. */
fn fmt_taken(val: ExprId, n: &Names) -> Option<String> {
    let (number, end) = taking(val, n)?;
    let fresh = !n.scalars.contains_key(&number) && n.taken.borrow_mut().insert(number);
    fresh.then(|| format!("ptr{number} = _free(); _take({end});"))
}

fn taking(val: ExprId, n: &Names) -> Option<(u32, String)> {
    let blocks = n.blocks.as_ref()?;
    let (base, to) = expr::split_offset(val);
    let before = blocks.get(&base).into_iter().flatten();
    let fixed = before
        .filter(|(start, _)| *start < to)
        .max_by_key(|(start, _)| *start);
    match (fixed, expr::node(val)) {
        (Some((start, number)), _) => {
            let size = to.wrapping_sub(*start).to_decimal();
            Some((*number, format!("ptr{number} + {size}")))
        }
        // The size is worked out as the code runs: the new start is the block plus it.
        (None, Node::Op(op::ADD, v)) => {
            let number = v.iter().find_map(|x| block_started(*x, n))?;
            Some((number, fmt_op(op::ADD, &v, n).0))
        }
        _ => None,
    }
}

/* A new array has its length written a step before its block is taken. The writes
between the two touch that block alone, so a file can state the taking first. */
pub fn taking_ahead(stmts: &[Stmt], i: usize, n: &Names) -> Option<String> {
    let target = |s: &Stmt| match s {
        Stmt::MStore { off, .. } if !is_free_pointer(*off) => Some(*off),
        Stmt::Copy { dest, .. } => Some(*dest),
        _ => None,
    };
    let block = |at: ExprId| {
        let within = block_ref(at, n).map(|(number, _)| number);
        within.or_else(|| block_started(at, n))
    };
    let number = block(target(&stmts[i])?)?;
    if !n.strict || n.taken.borrow().contains(&number) {
        return None;
    }
    let writes = stmts[i..].iter();
    let writes = writes.take_while(|s| target(s).and_then(block) == Some(number));
    match stmts.get(i + writes.count())? {
        Stmt::MStore { off, val, .. } if is_free_pointer(*off) => {
            let found = taking(*val, n).filter(|(taken, _)| *taken == number);
            found.and_then(|_| fmt_taken(*val, n))
        }
        _ => None,
    }
}

/* Code that builds a value in free memory and takes the block when it is done writes
before it takes. A file takes the block first, where its length is fixed, so that
nothing a compiler makes between two lines can land in it. This is the taking, stated
ahead of the first write, or nothing where the block is taken already. */
fn taken_ahead(off: ExprId, n: &Names) -> String {
    let known = block_ref(off, n).and_then(|(number, _)| Some((number, *n.lengths.get(&number)?)));
    match known.filter(|(number, _)| n.strict && !n.scalars.contains_key(number)) {
        Some((number, length)) if n.taken.borrow_mut().insert(number) => {
            format!("ptr{number} = _free(); _take(ptr{number} + {length}); ")
        }
        _ => String::new(),
    }
}

pub fn note_block_lengths(l: &Lifted, n: &mut Names) {
    let Some(blocks) = n.blocks.as_ref() else {
        return;
    };
    let mut lengths: HashMap<u32, Option<u64>> = HashMap::new();
    for s in l.nodes.iter().flat_map(|nd| &nd.stmts) {
        let Stmt::MStore { off, val, .. } = s else {
            continue;
        };
        if !is_free_pointer(*off) {
            continue;
        }
        let (base, to) = expr::split_offset(*val);
        let before = blocks.get(&base).into_iter().flatten();
        let taken = before
            .filter(|(start, _)| *start < to)
            .max_by_key(|(start, _)| *start);
        if let Some((start, number)) = taken {
            let length = to.wrapping_sub(*start);
            let fixed = length.fits_u64().then(|| length.low_u64());
            let known = lengths.entry(*number).or_insert(fixed);
            *known = known.filter(|k| Some(*k) == fixed);
        }
    }
    n.lengths = lengths
        .into_iter()
        .filter_map(|(number, length)| Some((number, length?)))
        .collect();
}

pub fn fmt_mem_read(off: ExprId, n: &Names) -> String {
    let raw = n.layout != MappingLayout::Vyper && scalar_word(off, n).is_none();
    match n.strict && raw {
        true => format!("_memory({})", fmt_mem_off(off, n)),
        false => fmt_mem_word(off, n),
    }
}

fn fmt_bytes_range(off: ExprId, len: ExprId, n: &Names) -> String {
    match (n.strict, bytes_value(off, len)) {
        (false, _) => fmt_mem_range(off, len, n),
        (true, Some(pointer)) => format!("_bytes({})", fmt_mem_off(pointer, n)),
        (true, None) => format!("_range({}, {})", fmt_mem_off(off, n), fmt_expr(len, n)),
    }
}

pub fn fmt_mem_off(off: ExprId, n: &Names) -> String {
    match (expr::as_const(off), block_ref(off, n)) {
        (Some(_), Some((number, offset))) => fmt_block_ref(number, offset),
        (Some(c), None) if c.bits() <= 64 => c.to_hex(),
        _ => fmt_expr(off, n),
    }
}

fn fmt_signed(e: ExprId, n: &Names) -> String {
    if let Some(c) = expr::as_const(e) {
        return fmt_int_const(c);
    }
    match expr::node(e) {
        Node::Op(op::SIGNEXTEND, _) => fmt_prec(e, P_PRIMARY, n),
        Node::Op(o, _) if is_signed_op(o) => fmt_prec(e, P_UNARY, n),
        _ => format!("int256({})", fmt_expr(e, n)),
    }
}

pub fn packed_read(e: ExprId) -> Option<(U256, u32, u32)> {
    fn shifted_slot(e: ExprId) -> Option<(U256, u32)> {
        match expr::node(e) {
            Node::SLoad(k, false, _) => Some((expr::as_const(k)?, 0)),
            Node::Op(op::SHR, w) => {
                let s = expr::as_const(w[0])?;
                if let Node::SLoad(k, false, _) = expr::node(w[1]) {
                    if s.fits_u64() && s.low_u64() % 8 == 0 && s.low_u64() < 256 {
                        return Some((expr::as_const(k)?, s.low_u64() as u32));
                    }
                }
                None
            }
            Node::Op(op::DIV, w) => {
                let d = expr::as_const(w[1])?;
                if let Node::SLoad(k, false, _) = expr::node(w[0]) {
                    if d.is_power_of_two() && d.trailing_zeros() % 8 == 0 && d.trailing_zeros() > 0
                    {
                        return Some((expr::as_const(k)?, d.trailing_zeros()));
                    }
                }
                None
            }
            _ => None,
        }
    }
    match expr::node(e) {
        Node::Op(op::AND, v) => {
            let m = expr::as_const(v[1])?;
            if !m.is_low_mask() {
                return None;
            }
            let (k, s) = shifted_slot(v[0])?;
            let bits = m.bits();
            /* A field is a whole number of bytes or one flag bit. A mask of any other
            width takes part of a field, and naming that part would hide the mask. */
            if s + bits <= 256 && (bits == 1 || bits.is_multiple_of(8)) {
                Some((k, s / 8, bits))
            } else {
                None
            }
        }
        Node::Op(op::SIGNEXTEND, v) => {
            let nb = expr::as_const(v[0])?;
            if !nb.fits_u64() || nb.low_u64() >= 31 {
                return None;
            }
            let (k, s) = shifted_slot(v[1])?;
            let bits = 8 * (nb.low_u64() as u32 + 1);
            if s + bits <= 256 {
                Some((k, s / 8, bits))
            } else {
                None
            }
        }
        Node::Op(op::SHR, _) | Node::Op(op::DIV, _) => {
            let (k, s) = shifted_slot(e)?;
            if s > 0 {
                Some((k, s / 8, 256 - s))
            } else {
                None
            }
        }
        _ => None,
    }
}

pub fn packed_write(key: ExprId, val: ExprId) -> Option<(U256, u32, u32, ExprId)> {
    let k = expr::as_const(key)?;
    let read = |e: ExprId| match expr::node(e) {
        Node::SLoad(kk, false, _) => expr::as_const(kk),
        _ => None,
    };
    packed_write_of(k, val, &read)
}

/* A second write to a slot keeps bytes of the word the first one stored, which is no
longer a read of the slot. The printer shows that word by the slot's name, so a write
that keeps it is a write to one variable all the same. */
fn packed_write_shown(key: ExprId, val: ExprId, n: &Names) -> Option<(U256, u32, u32, ExprId)> {
    let k = expr::as_const(key)?;
    let name = fmt_slot(key, n, SlotSpace::Persistent);
    let read = |e: ExprId| match expr::node(e) {
        Node::SLoad(kk, false, _) => expr::as_const(kk),
        _ => (fmt_expr(e, n) == name).then_some(k),
    };
    packed_write_of(k, val, &read)
}

fn packed_write_of(
    k: U256,
    val: ExprId,
    read: &dyn Fn(ExprId) -> Option<U256>,
) -> Option<(U256, u32, u32, ExprId)> {
    if let Node::Op(op::AND, w) = expr::node(val) {
        if let (kk, Some(keep)) = (read(w[0]), expr::as_const(w[1])) {
            if kk == Some(k) {
                let field = !keep;
                let s = field.trailing_zeros();
                let shifted = field >> s;
                if !field.is_zero() && shifted.is_low_mask() && s % 8 == 0 {
                    return Some((k, s / 8, shifted.bits(), expr::konst(U256::ZERO)));
                }
            }
        }
    }
    let Node::Op(op::OR, v) = expr::node(val) else {
        return None;
    };
    for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
        let Node::Op(op::AND, w) = expr::node(a) else {
            continue;
        };
        let (Some(kk), Some(keep)) = (read(w[0]), expr::as_const(w[1])) else {
            continue;
        };
        if kk != k {
            continue;
        }
        let field = !keep;
        if field.is_zero() {
            continue;
        }
        let s = field.trailing_zeros();
        let shifted = field >> s;
        if !shifted.is_low_mask() || s % 8 != 0 {
            continue;
        }
        let bits = shifted.bits();
        let mut value = if s == 0 {
            b
        } else {
            match expr::node(b) {
                Node::Op(op::SHL, x) if expr::as_const(x[0]) == Some(U256::from_u64(s as u64)) => {
                    x[1]
                }
                Node::Op(op::MUL, x)
                    if expr::as_const(x[1])
                        .is_some_and(|c| c.is_power_of_two() && c.trailing_zeros() == s) =>
                {
                    x[0]
                }
                Node::Const(c) => expr::konst(c >> s),
                _ => expr::op2(op::SHR, expr::konst_u64(s as u64), b),
            }
        };
        if let Node::Op(op::AND, x) = expr::node(value) {
            if expr::as_const(x[1]) == Some(expr::mask_bits(bits)) {
                value = x[0];
            }
        }
        return Some((k, s / 8, bits, value));
    }
    None
}

// Only when the declared type fills exactly the cleared bytes.
// Then the kept bytes are known to be zero and the mask is noise.
pub fn element_write(key: ExprId, val: ExprId, n: &Names) -> Option<(U256, ExprId)> {
    let root = element_root(key)?;
    let width_bits = element_width(n.elem_types.get(&root)?)?;
    let kept_mask = |e: ExprId| -> Option<U256> {
        let Node::Op(op::AND, w) = expr::node(e) else {
            return None;
        };
        // The word kept can be the one an earlier write stored, shown by the same name.
        let same = |a: ExprId| match expr::node(a) {
            Node::SLoad(k, false, _) if k == key => true,
            _ => n.strict && fmt_expr(a, n) == fmt_slot(key, n, SlotSpace::Persistent),
        };
        [(w[0], w[1]), (w[1], w[0])]
            .into_iter()
            .find_map(|(a, b)| expr::as_const(b).filter(|_| same(a)))
    };
    let keeps = |e: ExprId| kept_mask(e).is_some_and(|m| !m == expr::mask_bits(width_bits));
    match expr::node(val) {
        Node::Op(op::OR, v) if keeps(v[1]) => Some((root, v[0])),
        Node::Op(op::OR, v) if keeps(v[0]) => Some((root, v[1])),
        _ if keeps(val) => Some((root, expr::konst(U256::ZERO))),
        _ => None,
    }
}

fn element_typed_load(e: ExprId, n: &Names) -> Option<ExprId> {
    let Node::Op(op::AND, v) = expr::node(e) else {
        return None;
    };
    for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
        let (Node::SLoad(key, false, _), Some(m)) = (expr::node(a), expr::as_const(b)) else {
            continue;
        };
        if !m.is_low_mask() {
            continue;
        }
        let root = element_root(key)?;
        let width = element_width(n.elem_types.get(&root)?)?;
        if m.bits() == width {
            return Some(a);
        }
    }
    None
}

pub fn element_width(ty: &str) -> Option<u32> {
    match ty {
        "bool" => Some(8),
        "address" => Some(160),
        t => t.strip_prefix("uint")?.parse().ok(),
    }
}

pub fn element_root(key: ExprId) -> Option<U256> {
    match expr::node(key) {
        Node::Keccak(words, 0) if words.len() == 2 => words
            .iter()
            .find_map(|w| expr::as_const(*w).filter(|c| c.bits() <= 32)),
        Node::Keccak(words, 0) if words.len() == 1 => expr::as_const(words[0]),
        Node::Op(op::ADD, v) => v.iter().find_map(|a| match expr::node(*a) {
            Node::Keccak(w, 0) if w.len() == 1 => expr::as_const(w[0]),
            Node::Const(c) => array_element(c).map(|(s, _)| s),
            _ => None,
        }),
        Node::Const(c) => array_element(c).map(|(s, _)| s),
        _ => None,
    }
}

fn slot_name(s: U256, n: &Names, space: SlotSpace) -> String {
    // The names belong to storage. A transient slot with the same number is another place.
    if let Some(name) = n.storage.get(&s).filter(|_| space == SlotSpace::Persistent) {
        return name.clone();
    }
    let prefix = match space {
        SlotSpace::Persistent => "stor",
        SlotSpace::Transient => "tstor",
    };
    if s.bits() <= 32 {
        format!("{}_{}", prefix, s.to_decimal())
    } else {
        format!("{}_{}", prefix, s.to_hex())
    }
}

fn base_name(e: ExprId, n: &Names, space: SlotSpace) -> String {
    match expr::as_const(e) {
        Some(c) if array_element(c).is_none() => slot_name(c, n, space),
        _ => fmt_slot(e, n, space),
    }
}

/* A slot that is a mapping's value slot plus i * k plus c, with c below k, is field c of
element i in a list of records k slots long. The sum may come in any order and nesting. */
fn record_field(e: ExprId) -> Option<(ExprId, ExprId, U256)> {
    fn terms(e: ExprId, out: &mut Vec<ExprId>) {
        match expr::node(e) {
            Node::Op(op::ADD, v) => v.iter().for_each(|t| terms(*t, out)),
            _ => out.push(e),
        }
    }
    let mut all = Vec::new();
    terms(e, &mut all);
    let hashed = |t: &ExprId| matches!(expr::node(*t), Node::Keccak(w, 0) if w.len() == 2);
    let [record] = all.iter().copied().filter(hashed).collect::<Vec<_>>()[..] else {
        return None;
    };
    let mut field = U256::ZERO;
    let mut scaled = None;
    for t in all.into_iter().filter(|t| *t != record) {
        match (expr::as_const(t), expr::node(t)) {
            (Some(c), _) => field = field.wrapping_add(c),
            (None, Node::Op(op::MUL, v)) if scaled.is_none() => {
                let pairs = [(v[0], v[1]), (v[1], v[0])].into_iter();
                let mut found = pairs.filter_map(|(i, k)| Some((i, expr::as_const(k)?)));
                scaled = Some(found.find(|(_, k)| k > &U256::ONE)?);
            }
            _ => return None,
        }
    }
    let (i, k) = scaled?;
    (field < k).then_some((record, i, field))
}

fn struct_member(e: ExprId, n: &Names) -> Option<(U256, u64, &String)> {
    if n.struct_depth.is_empty() {
        return None;
    }
    let path = crate::ssa::slot_path(e, n.layout)?;
    let depth = *n.struct_depth.get(&path.root)?;
    let selects = |steps: &[crate::ssa::Step]| {
        steps.len() == depth
            && steps
                .iter()
                .all(|s| !matches!(s, crate::ssa::Step::Offset(_)))
    };
    let offset = match path.steps.split_last() {
        Some((crate::ssa::Step::Offset(o), element)) if selects(element) => *o,
        _ if selects(&path.steps) => 0,
        _ => return None,
    };
    let name = n.members.get(&(path.root, offset))?;
    Some((path.root, offset, name))
}

fn member_field_read(e: ExprId, n: &Names) -> Option<String> {
    if n.member_fields.is_empty() {
        return None;
    }
    let field = crate::ssa::field_read(e)?;
    member_field(field.key, field.bit_offset, field.bits, n)
}

fn member_field(key: ExprId, bit_offset: u32, bits: u32, n: &Names) -> Option<String> {
    let (root, offset, member) = struct_member(key, n)?;
    let name = n.member_fields.get(&(root, offset, bit_offset / 8, bits))?;
    let whole = fmt_slot(key, n, SlotSpace::Persistent);
    Some(format!("{}{}", whole.strip_suffix(member.as_str())?, name))
}

pub fn fmt_slot(e: ExprId, n: &Names, space: SlotSpace) -> String {
    let text = fmt_slot_path(e, n, space);
    match struct_member(e, n) {
        Some((_, 0, name)) if space == SlotSpace::Persistent => format!("{text}.{name}"),
        _ => text,
    }
}

fn fmt_slot_path(e: ExprId, n: &Names, space: SlotSpace) -> String {
    let prefix = match space {
        SlotSpace::Persistent => "stor",
        SlotSpace::Transient => "tstor",
    };
    if let Some(c) = expr::as_const(e) {
        if let Some(name) = n.storage.get(&c).filter(|_| space == SlotSpace::Persistent) {
            if n.dyn_arrays.contains(&c) {
                return format!("{}.length", name);
            }
            return name.clone();
        }
        if let Some((s, k)) = array_element(c) {
            return format!("{}[{}]", slot_name(s, n, space), k);
        }
        return if c.bits() <= 32 {
            format!("{}_{}", prefix, c.to_decimal())
        } else {
            format!("{}_{}", prefix, c.to_hex())
        };
    }
    match expr::node(e) {
        Node::Keccak(words, 0) if words.len() == 2 => {
            let (key, slot) = if n.layout == MappingLayout::Vyper
                || (expr::as_const(words[0]).is_some_and(|c| c.bits() <= 16)
                    && !expr::as_const(words[1]).is_some_and(|c| c.bits() <= 16))
            {
                (words[1], words[0])
            } else {
                (words[0], words[1])
            };
            format!("{}[{}]", base_name(slot, n, space), fmt_expr(key, n))
        }
        Node::Keccak(words, 0) if words.len() == 1 => {
            format!("{}[0]", base_name(words[0], n, space))
        }
        Node::Op(op::ADD, v) => {
            let (base, idx) = (v[0], v[1]);
            if let Some((record, i, field)) = record_field(e) {
                if struct_member(e, n).is_none() {
                    let path = fmt_slot_path(record, n, space);
                    return format!("{path}[{}].field{}", fmt_expr(i, n), field.to_decimal());
                }
            }
            for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
                if let Some((s, k)) = expr::as_const(a).and_then(hashed_slot) {
                    return format!(
                        "{}[{}]",
                        slot_name(s, n, space),
                        offset_index(&fmt_expr(b, n), k)
                    );
                }
            }
            for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
                if let (Some(c), true) = (expr::as_const(a), is_plain_index(b)) {
                    if let Some((root, off)) = fixed_array_base(c, &n.array_bases) {
                        let idx_s = if off.is_zero() {
                            fmt_expr(b, n)
                        } else {
                            format!("{} + {}", fmt_expr(b, n), off.to_decimal())
                        };
                        return format!("{}[{}]", slot_name(root, n, space), idx_s);
                    }
                }
            }
            match expr::node(base) {
                Node::Keccak(words, 0) if words.len() == 1 => {
                    format!("{}[{}]", base_name(words[0], n, space), fmt_expr(idx, n))
                }
                Node::Keccak(words, 0) if words.len() == 2 => {
                    let path = fmt_slot_path(base, n, space);
                    match (struct_member(e, n), expr::as_const(idx)) {
                        (Some((_, _, name)), _) => format!("{path}.{name}"),
                        (None, Some(field)) => format!("{path}.field{}", field.to_decimal()),
                        (None, None) => format!("{path}[{}]", fmt_expr(idx, n)),
                    }
                }
                _ => format!("{}[{}]", prefix, fmt_expr(e, n)),
            }
        }
        _ => format!("{}[{}]", prefix, fmt_expr(e, n)),
    }
}

fn env_name(o: u8, seq: u32, n: &Names) -> String {
    match o {
        op::ADDRESS => "address(this)".into(),
        op::ORIGIN => "tx.origin".into(),
        op::CALLER => "msg.sender".into(),
        op::CALLVALUE => "msg.value".into(),
        op::CALLDATASIZE => "msg.data.length".into(),
        op::CODESIZE => "address(this).code.length".into(),
        op::GASPRICE => "tx.gasprice".into(),
        op::RETURNDATASIZE => "returndatasize()".into(),
        op::COINBASE => "block.coinbase".into(),
        op::TIMESTAMP => "block.timestamp".into(),
        op::NUMBER => "block.number".into(),
        op::PREVRANDAO => "block.prevrandao".into(),
        op::GASLIMIT => "block.gaslimit".into(),
        op::CHAINID => "block.chainid".into(),
        op::SELFBALANCE => "address(this).balance".into(),
        op::BASEFEE => "block.basefee".into(),
        op::BLOBBASEFEE => "block.blobbasefee".into(),
        op::GAS
            if n.gas_named
                .borrow()
                .contains(&expr::intern(Node::Env(o, seq))) =>
        {
            format!("gasleft_{}", n.seq(seq))
        }
        op::GAS => format!("gasleft_{}()", n.seq(seq)),
        op::MSIZE => format!("msize_{}()", n.seq(seq)),
        op::PC => "pc".into(),
        _ => format!("{}()", op::name(o).to_lowercase()),
    }
}

fn dynamic_type(ty: &str) -> bool {
    ty == "bytes" || ty == "string" || ty.ends_with(']') || ty.starts_with('(')
}

// A word of the call data a function header declares by name with a type of one word.
fn named_word(off: ExprId, n: &Names) -> bool {
    let index = calldata_word_index(off).filter(|_| !n.in_helper);
    let declared = index.and_then(|i| n.param_types.get(&i));
    declared.is_some_and(|ty| !dynamic_type(ty))
}

fn copy_source(kind: u8) -> &'static str {
    match kind {
        op::CALLDATACOPY => "msg.data",
        op::CODECOPY => "address(this).code",
        op::RETURNDATACOPY => "returndata",
        op::EXTCODECOPY => "extcode",
        op::MCOPY => "mem",
        _ => "copied",
    }
}

pub fn field_name(e: ExprId, n: &Names) -> Option<String> {
    member_field_read(e, n).or_else(|| {
        let field = packed_read(e).filter(|_| !n.fields.is_empty())?;
        n.fields.get(&field).cloned()
    })
}

fn fmt_inner(e: ExprId, n: &Names) -> (String, u8) {
    if let Some(text) = field_name(e, n) {
        return (text, P_PRIMARY);
    }
    if let Some(load) = element_typed_load(e, n) {
        return (fmt_expr(load, n), P_PRIMARY);
    }
    if !expr::is_const(e) {
        if let Some((number, offset)) = block_ref(e, n) {
            let precedence = if offset.is_zero() { P_PRIMARY } else { P_ADD };
            return (fmt_block_ref(number, offset), precedence);
        }
    }
    match expr::node(e) {
        Node::Const(c) => (fmt_const(c), P_PRIMARY),
        Node::Env(op::RETURNDATASIZE, _) if n.strict => ("_returndatasize()".into(), P_PRIMARY),
        Node::Env(o, seq) => (env_name(o, seq, n), P_PRIMARY),
        Node::Var(v) => (format!("v{}", n.var(v)), P_PRIMARY),
        Node::Arg(i) => (
            n.args
                .get(&i)
                .cloned()
                .unwrap_or_else(|| format!("arg{}", i)),
            P_PRIMARY,
        ),
        Node::Unknown(u) => (format!("unknown_{}", n.seq(u)), P_PRIMARY),
        /* For a compiler an argument of a dynamic type is the data itself, where the
        code has the place the data lies at. The place is read from the call data, as is
        any word of the call data that is not an argument of its own. */
        Node::CallDataLoad(off) if n.strict && !named_word(off, n) => {
            (format!("_calldata({})", fmt_expr(off, n)), P_PRIMARY)
        }
        Node::CallDataLoad(off) => {
            // Inside a helper the name argN is taken by what the caller passed.
            if let Some(i) = calldata_word_index(off).filter(|_| !n.in_helper) {
                return (
                    n.params
                        .get(&i)
                        .cloned()
                        .unwrap_or_else(|| format!("arg{}", i)),
                    P_PRIMARY,
                );
            }
            if expr::as_const(off) == Some(U256::ZERO) {
                return ("msg.data[0:32]".into(), P_PRIMARY);
            }
            (format!("calldata[{}]", fmt_expr(off, n)), P_PRIMARY)
        }
        Node::MLoad(off, _) if n.answers.borrow().contains_key(&off) => {
            let (seq, at) = n.answers.borrow()[&off];
            (format!("_word(returned_{}, {at})", n.seq(seq)), P_PRIMARY)
        }
        /* A read of memory through an address is written as one. It reads what the file
        itself put there, so it only gives the word the code read where the memory was
        laid out the same way, as it is for a value a compiler made. */
        Node::MLoad(off, _) => (fmt_mem_read(off, n), P_PRIMARY),
        Node::SLoad(key, false, _) if n.strict && whole_packed(key, n).is_some() => {
            (whole_packed(key, n).unwrap_or_default(), P_PRIMARY)
        }
        Node::SLoad(key, transient, _) => (
            fmt_slot(key, n, SlotSpace::from_transient(transient)),
            P_PRIMARY,
        ),
        Node::Keccak(..) if expr::pieces(e).is_some() => {
            let pieces = expr::pieces(e).unwrap_or_default();
            /* Where every piece is a whole word, abi.encode says so whatever the type of
            each value. Packed, an address or a short number would read as fewer bytes. */
            let whole = pieces.iter().all(|p| p.1 == 32);
            let part = |p: &(ExprId, u8)| match (whole, p.1) {
                (true, _) => fmt_expr(p.0, n),
                (false, 32) => fmt_whole_word(p.0, n),
                (false, _) => fmt_piece(p, n),
            };
            let parts: Vec<String> = pieces.iter().map(part).collect();
            let encoder = match whole {
                true => "abi.encode",
                false => "abi.encodePacked",
            };
            (
                hash_word(format!("keccak256({encoder}({}))", parts.join(", ")), n),
                P_PRIMARY,
            )
        }
        Node::Keccak(words, tail) => {
            let mut parts: Vec<String> = Vec::new();
            for (i, w) in words.iter().enumerate() {
                if tail > 0 && i == words.len() - 1 {
                    parts.push(format!("bytes{}({})", tail, fmt_expr(*w, n)));
                } else if tail > 0 {
                    parts.push(fmt_whole_word(*w, n));
                } else {
                    parts.push(fmt_expr(*w, n));
                }
            }
            let encoder = match tail {
                0 => "abi.encode",
                _ => "abi.encodePacked",
            };
            (
                hash_word(format!("keccak256({encoder}({}))", parts.join(", ")), n),
                P_PRIMARY,
            )
        }
        Node::KeccakMem(off, len, _) => (
            hash_word(format!("keccak256({})", fmt_bytes_range(off, len, n)), n),
            P_PRIMARY,
        ),
        Node::CallResult(seq) => (format!("success_{}", n.seq(seq)), P_PRIMARY),
        Node::CreateResult(seq) => (format!("deployed_{}", n.seq(seq)), P_PRIMARY),
        Node::ReturnData(seq, off) if n.strict => (
            format!("_word(returned_{}, {})", n.seq(seq), fmt_expr(off, n)),
            P_PRIMARY,
        ),
        Node::ReturnData(seq, off) => (
            format!("returndata_{}[{}]", n.seq(seq), fmt_expr(off, n)),
            P_PRIMARY,
        ),
        // A word copied from memory is spelled like the store that wrote it.
        Node::CopiedWord(op::MCOPY, src, _) => (fmt_mem_read(src, n), P_PRIMARY),
        Node::CopiedWord(op::CALLDATACOPY, src, _) if n.strict => {
            (format!("_calldata({})", fmt_expr(src, n)), P_PRIMARY)
        }
        Node::CopiedWord(kind, src, _) => (
            format!("{}[{}]", copy_source(kind), fmt_expr(src, n)),
            P_PRIMARY,
        ),
        Node::IntRet(seq, j) => (format!("ret_{}_{}", n.seq(seq), j), P_PRIMARY),
        Node::Op(..) if n.unchecked(e) => (format!("unchecked({})", fmt_bare(e, 0, n)), P_PRIMARY),
        Node::Op(o @ (op::ADD | op::MUL), v) if n.narrow_type(e).is_some() => {
            let bits = n.narrow_type(e).unwrap_or(256);
            let (number, fixed) = match expr::is_const(v[0]) {
                true => (v[1], v[0]),
                false => (v[0], v[1]),
            };
            let cast = format!("uint{bits}(");
            let number = match fmt_expr(number, n) {
                typed if typed.starts_with(&cast) => typed,
                plain => format!("{cast}{plain})"),
            };
            let (sign, prec) = match o {
                op::ADD => ("+", P_ADD),
                _ => ("*", P_MUL),
            };
            let fixed = fmt_prec(fixed, prec + 1, n);
            (format!("{number} {sign} {fixed}"), prec)
        }
        Node::Op(o, v) => fmt_op(o, &v, n),
    }
}

/* Inside the marker of an unchecked operator an operand that is unchecked too needs no
marker of its own. One that is checked has to say so, or it would read as unchecked. */
fn fmt_bare(e: ExprId, outer: u8, n: &Names) -> String {
    if !n.unchecked(e) {
        return fmt_prec(e, outer, n);
    }
    if let Some((s, p)) = n.bare.borrow().get(&e) {
        return paren(s.clone(), *p, outer);
    }
    let Node::Op(o, v) = expr::node(e) else {
        return fmt_prec(e, outer, n);
    };
    let operand = |x: ExprId, prec: u8| match expr::node(x) {
        Node::Op(op::ADD | op::SUB | op::MUL | op::DIV | op::SDIV | op::MOD | op::SMOD, _)
            if n.arithmetic(x) == Some(Arithmetic::Tested)
                && n.temp_of.borrow().get(&x).is_none() =>
        {
            format!("checked({})", fmt_expr(x, n))
        }
        _ => fmt_bare(x, prec, n),
    };
    let (sign, p) = match o {
        op::ADD => ("+", P_ADD),
        op::SUB => ("-", P_ADD),
        op::MUL => ("*", P_MUL),
        op::DIV => ("/", P_MUL),
        op::MOD => ("%", P_MUL),
        _ => {
            let (s, p) = fmt_op(o, &v, n);
            return paren(s, p, outer);
        }
    };
    let s = format!("{} {sign} {}", operand(v[0], p), operand(v[1], p + 1));
    n.bare.borrow_mut().insert(e, (s.clone(), p));
    paren(s, p, outer)
}

fn fmt_op(o: u8, v: &[ExprId], n: &Names) -> (String, u8) {
    match (o, v.len()) {
        (op::ISZERO, 1) => {
            let a = v[0];
            if let Node::Op(io, iv) = expr::node(a) {
                match io {
                    op::EQ => {
                        if let Some((b, truth)) = bool_against_const(iv[0], iv[1], n) {
                            return if truth {
                                (format!("!{}", fmt_prec(b, P_UNARY, n)), P_UNARY)
                            } else {
                                (fmt_prec(b, P_PRIMARY, n), P_PRIMARY)
                            };
                        }
                        return (
                            format!(
                                "{} != {}",
                                fmt_prec(iv[0], P_EQ + 1, n),
                                fmt_eq_rhs(iv[0], iv[1], P_EQ + 1, n)
                            ),
                            P_EQ,
                        );
                    }
                    op::LT => {
                        return (
                            format!(
                                "{} >= {}",
                                fmt_ordered(iv[0], iv[1], n),
                                fmt_ordered(iv[1], iv[0], n)
                            ),
                            P_CMP,
                        )
                    }
                    op::GT => {
                        return (
                            format!(
                                "{} <= {}",
                                fmt_ordered(iv[0], iv[1], n),
                                fmt_ordered(iv[1], iv[0], n)
                            ),
                            P_CMP,
                        )
                    }
                    op::SLT | op::SGT if size_compare(io, iv[0], iv[1], n).is_some() => {
                        let Some(s) = size_compare(io, iv[0], iv[1], n) else {
                            unreachable!("guard checked size_compare")
                        };
                        return (
                            s.replacen(
                                if io == op::SLT { " < " } else { " > " },
                                if io == op::SLT { " >= " } else { " <= " },
                                1,
                            ),
                            P_CMP,
                        );
                    }
                    op::SLT => {
                        return (
                            format!("{} >= {}", fmt_signed(iv[0], n), fmt_signed(iv[1], n)),
                            P_CMP,
                        )
                    }
                    op::SGT => {
                        return (
                            format!("{} <= {}", fmt_signed(iv[0], n), fmt_signed(iv[1], n)),
                            P_CMP,
                        )
                    }
                    _ => {}
                }
            }
            if let Node::Op(op::ISZERO, iv) = expr::node(a) {
                if !is_bool(iv[0], n) {
                    let zero = zero_of(iv[0], n);
                    return (format!("{} != {zero}", fmt_prec(iv[0], P_EQ + 1, n)), P_EQ);
                }
                return (fmt_prec(iv[0], P_PRIMARY, n), P_PRIMARY);
            }
            if is_bool(a, n) {
                (format!("!{}", fmt_prec(a, P_UNARY, n)), P_UNARY)
            } else {
                let zero = zero_of(a, n);
                (format!("{} == {zero}", fmt_prec(a, P_EQ + 1, n)), P_EQ)
            }
        }
        (op::NOT, 1) => (format!("~{}", fmt_prec(v[0], P_UNARY, n)), P_UNARY),
        (op::CLZ, 1) => (format!("clz({})", fmt_expr(v[0], n)), P_PRIMARY),
        (op::BALANCE, 1 | 2) => (
            format!("{}.balance", fmt_prec(v[0], P_PRIMARY, n)),
            P_PRIMARY,
        ),
        (op::EXTCODESIZE, 1 | 2) => (
            format!("{}.code.length", fmt_prec(v[0], P_PRIMARY, n)),
            P_PRIMARY,
        ),
        (op::EXTCODEHASH, 1 | 2) => (
            format!("{}.codehash", fmt_prec(v[0], P_PRIMARY, n)),
            P_PRIMARY,
        ),
        (op::BLOCKHASH, 1) => (format!("blockhash({})", fmt_expr(v[0], n)), P_PRIMARY),
        (op::BLOBHASH, 1) => (format!("blobhash({})", fmt_expr(v[0], n)), P_PRIMARY),
        (op::ADD, 2) => (
            format!(
                "{} + {}",
                fmt_number(v[0], P_ADD, n),
                fmt_number(v[1], P_ADD + 1, n)
            ),
            P_ADD,
        ),
        (op::SUB, 2) => (
            format!(
                "{} - {}",
                fmt_number(v[0], P_ADD, n),
                fmt_number(v[1], P_ADD + 1, n)
            ),
            P_ADD,
        ),
        (op::MUL, 2) => (
            format!(
                "{} * {}",
                fmt_number(v[0], P_MUL, n),
                fmt_number(v[1], P_MUL + 1, n)
            ),
            P_MUL,
        ),
        (op::DIV, 2) => (
            format!(
                "{} / {}",
                fmt_number(v[0], P_MUL, n),
                fmt_number(v[1], P_MUL + 1, n)
            ),
            P_MUL,
        ),
        (op::MOD, 2) => (
            format!(
                "{} % {}",
                fmt_number(v[0], P_MUL, n),
                fmt_number(v[1], P_MUL + 1, n)
            ),
            P_MUL,
        ),
        (op::SDIV, 2) => (
            format!("{} / {}", fmt_signed(v[0], n), fmt_signed(v[1], n)),
            P_MUL,
        ),
        (op::SMOD, 2) => (
            format!("{} % {}", fmt_signed(v[0], n), fmt_signed(v[1], n)),
            P_MUL,
        ),
        (op::EXP, 2) => (
            format!(
                "{} ** {}",
                fmt_number(v[0], P_EXP + 1, n),
                fmt_number(v[1], P_EXP, n)
            ),
            P_EXP,
        ),
        (op::LT, 2) => (
            format!(
                "{} < {}",
                fmt_ordered(v[0], v[1], n),
                fmt_ordered(v[1], v[0], n)
            ),
            P_CMP,
        ),
        (op::GT, 2) => (
            format!(
                "{} > {}",
                fmt_ordered(v[0], v[1], n),
                fmt_ordered(v[1], v[0], n)
            ),
            P_CMP,
        ),
        (op::SLT, 2) | (op::SGT, 2) => match size_compare(o, v[0], v[1], n) {
            Some(s) => (s, P_CMP),
            None if o == op::SLT => (
                format!("{} < {}", fmt_signed(v[0], n), fmt_signed(v[1], n)),
                P_CMP,
            ),
            None => (
                format!("{} > {}", fmt_signed(v[0], n), fmt_signed(v[1], n)),
                P_CMP,
            ),
        },
        (op::EQ, 2) => {
            if let Some((b, truth)) = bool_against_const(v[0], v[1], n) {
                return if truth {
                    (fmt_prec(b, P_PRIMARY, n), P_PRIMARY)
                } else {
                    (format!("!{}", fmt_prec(b, P_UNARY, n)), P_UNARY)
                };
            }
            (
                format!(
                    "{} == {}",
                    fmt_prec(v[0], P_EQ + 1, n),
                    fmt_eq_rhs(v[0], v[1], P_EQ + 1, n)
                ),
                P_EQ,
            )
        }
        (op::AND, 2) if logical(v, n) => (
            format!(
                "{} && {}",
                fmt_prec(v[0], P_LAND, n),
                fmt_prec(v[1], P_LAND + 1, n)
            ),
            P_LAND,
        ),
        (op::OR, 2) if logical(v, n) => (
            format!(
                "{} || {}",
                fmt_prec(v[0], P_LOR, n),
                fmt_prec(v[1], P_LOR + 1, n)
            ),
            P_LOR,
        ),
        (op::AND, 2) => {
            if is_selector_expr(expr::intern(Node::Op(op::AND, v.to_vec()))) {
                return ("msg.sig".into(), P_PRIMARY);
            }
            if let Some(m) = expr::as_const(v[1]) {
                if m.is_low_mask() {
                    let bits = m.bits();
                    if bits == 160 && n.strict && is_address(v[0], n) {
                        return (fmt_prec(v[0], P_PRIMARY, n), P_PRIMARY);
                    }
                    if bits == 160 && n.strict {
                        return (
                            format!("address(uint160({}))", fmt_expr(v[0], n)),
                            P_PRIMARY,
                        );
                    }
                    if bits == 160 {
                        return (format!("address({})", fmt_expr(v[0], n)), P_PRIMARY);
                    }
                    if bits % 8 == 0 && bits < 256 {
                        return (format!("uint{}({})", bits, fmt_expr(v[0], n)), P_PRIMARY);
                    }
                }
            }
            (
                format!(
                    "{} & {}",
                    fmt_prec(v[0], P_AND, n),
                    fmt_prec(v[1], P_AND + 1, n)
                ),
                P_AND,
            )
        }
        (op::OR, 2) => (
            format!(
                "{} | {}",
                fmt_prec(v[0], P_OR, n),
                fmt_prec(v[1], P_OR + 1, n)
            ),
            P_OR,
        ),
        (op::XOR, 2) => (
            format!(
                "{} ^ {}",
                fmt_prec(v[0], P_XOR, n),
                fmt_prec(v[1], P_XOR + 1, n)
            ),
            P_XOR,
        ),
        (op::SHL, 2) => (
            format!(
                "{} << {}",
                fmt_prec(v[1], P_SHIFT, n),
                fmt_prec(v[0], P_SHIFT + 1, n)
            ),
            P_SHIFT,
        ),
        (op::SHR, 2) => {
            if is_selector_expr(expr::intern(Node::Op(op::SHR, v.to_vec()))) {
                return ("msg.sig".into(), P_PRIMARY);
            }
            (
                format!(
                    "{} >> {}",
                    fmt_prec(v[1], P_SHIFT, n),
                    fmt_prec(v[0], P_SHIFT + 1, n)
                ),
                P_SHIFT,
            )
        }
        (op::SAR, 2) => (
            format!(
                "{} >> {}",
                fmt_signed(v[1], n),
                fmt_prec(v[0], P_SHIFT + 1, n)
            ),
            P_SHIFT,
        ),
        (op::BYTE, 2) => (
            format!("byte({}, {})", fmt_expr(v[0], n), fmt_expr(v[1], n)),
            P_PRIMARY,
        ),
        (op::SIGNEXTEND, 2) => {
            if let Some(k) = expr::as_const(v[0]) {
                if k < U256::from_u64(31) {
                    return (
                        format!("int{}({})", 8 * (k.low_u64() + 1), fmt_expr(v[1], n)),
                        P_PRIMARY,
                    );
                }
            }
            (
                format!("signextend({}, {})", fmt_expr(v[0], n), fmt_expr(v[1], n)),
                P_PRIMARY,
            )
        }
        (op::ADDMOD, 3) => (
            format!(
                "addmod({}, {}, {})",
                fmt_expr(v[0], n),
                fmt_expr(v[1], n),
                fmt_expr(v[2], n)
            ),
            P_PRIMARY,
        ),
        (op::MULMOD, 3) => (
            format!(
                "mulmod({}, {}, {})",
                fmt_expr(v[0], n),
                fmt_expr(v[1], n),
                fmt_expr(v[2], n)
            ),
            P_PRIMARY,
        ),
        _ => {
            let args: Vec<String> = v.iter().map(|x| fmt_expr(*x, n)).collect();
            (
                format!("{}({})", op::name(o).to_lowercase(), args.join(", ")),
                P_PRIMARY,
            )
        }
    }
}

fn bool_against_const(a: ExprId, b: ExprId, n: &Names) -> Option<(ExprId, bool)> {
    for (x, c) in [(a, b), (b, a)] {
        if let Some(k) = expr::as_const(c) {
            if is_bool(x, n) && !expr::is_const(x) {
                if k == U256::ONE {
                    return Some((x, true));
                }
                if k.is_zero() {
                    return Some((x, false));
                }
            }
        }
    }
    None
}

fn fmt_eq_rhs(lhs: ExprId, rhs: ExprId, prec: u8, n: &Names) -> String {
    if is_selector_expr(lhs) {
        if let Some(c) = expr::as_const(rhs) {
            // Masked where the call data holds it, a selector is the constant's high four bytes.
            let in_place =
                matches!(expr::node(lhs), Node::Op(op::AND, v) if !is_selector_expr(v[0]));
            let c = if in_place { c >> 224 } else { c };
            let sel = c.low_u64() as u32;
            let s = c.to_hex_padded(4).to_string();
            return match sigs::function(sel) {
                Some(sig) => format!("{} /* {} */", s, sig),
                None => s,
            };
        }
    }
    if n.strict && is_address(lhs, n) && !is_address(rhs, n) {
        return as_address(rhs, n);
    }
    fmt_prec(rhs, prec, n)
}

pub fn leading_selector(word0: ExprId, len: Option<usize>) -> Option<u32> {
    let first_bytes = len.map(|l| l.min(32)).unwrap_or(32) as u32;
    if first_bytes < 4 {
        return None;
    }
    let from_const = |c: U256| -> Option<u32> {
        let sel = (c >> (8 * (first_bytes - 4))).low_u64() as u32;
        if sel == 0 {
            None
        } else {
            Some(sel)
        }
    };
    if let Some(c) = expr::as_const(word0) {
        return from_const(c);
    }
    if first_bytes == 32 {
        if let Node::Op(op::OR, v) = expr::node(word0) {
            for (x, y) in [(v[0], v[1]), (v[1], v[0])] {
                if let Some(c) = expr::as_const(x) {
                    if (c & expr::mask_bits(224)).is_zero() && expr::value_bits(y) <= 224 {
                        return from_const(c);
                    }
                }
            }
        }
    }
    None
}

pub fn fmt_payload(words: &[ExprId], len: Option<U256>, n: &Names, kind: PayloadKind) -> String {
    if words.is_empty() {
        return String::new();
    }
    let lenu = len.and_then(|l| l.as_usize());
    if let Some(sel) = leading_selector(words[0], lenu) {
        let top4_only = lenu.map_or(
            expr::as_const(words[0]).is_none_or(|c| (c & expr::mask_bits(224)).is_zero()),
            |l| l >= 4 && (l - 4) % 32 == 0,
        );
        if kind == PayloadKind::Revert && top4_only {
            if sel == SEL_ERROR {
                if let Some(s) = decode_string_payload(words, lenu) {
                    return format!("\"{}\"", s);
                }
            }
            if sel == SEL_PANIC && words.len() >= 2 {
                if let Some(code) = expr::as_const(shifted_word_len(words, 0, lenu)) {
                    return format!("Panic({})", panic_name(code.low_u64()));
                }
            }
            let nargs = lenu
                .map(|l| l.saturating_sub(4) / 32)
                .unwrap_or(words.len().saturating_sub(1));
            let word = |i: usize| shifted_word_len(words, i, lenu);
            let known = sigs::error(sel).filter(|sig| {
                !n.strict || sigs::error_named(sigs::name_of(sig), nargs).is_some_and(|s| s == *sig)
            });
            if let Some(sig) = known {
                let types = sigs::params_of(&sig);
                let typed = |i: usize| match types.get(i).filter(|_| n.strict) {
                    Some(ty) => as_type(ty, word(i), n),
                    None => fmt_expr(word(i), n),
                };
                let args: Vec<String> = (0..nargs).map(typed).collect();
                return format!("{}({})", sigs::name_of(&sig), args.join(", "));
            }
            let plain = |i: usize| match n.strict {
                true => as_word(word(i), n),
                false => fmt_expr(word(i), n),
            };
            let args: Vec<String> = (0..nargs).map(plain).collect();
            return format!("CustomError_{:08x}({})", sel, args.join(", "));
        }
    }
    if kind == PayloadKind::Return
        && words.len() >= 3
        && expr::as_const(words[0]) == Some(U256::from_u64(32))
    {
        if let Some(len) = expr::as_const(words[1]).and_then(|l| l.as_usize()) {
            if len > 0
                && len <= 32 * (words.len() - 2)
                && lenu.is_none_or(|l| l == 64 + len.div_ceil(32) * 32)
            {
                let mut bytes = Vec::new();
                for w in &words[2..] {
                    match expr::as_const(*w) {
                        Some(c) => bytes.extend_from_slice(&c.to_be_bytes()),
                        None => {
                            bytes.clear();
                            break;
                        }
                    }
                }
                if bytes.len() >= len {
                    bytes.truncate(len);
                    if bytes.iter().all(|b| (0x20..0x7f).contains(b)) {
                        return format!("\"{}\"", escape(&String::from_utf8_lossy(&bytes)));
                    }
                }
            }
        }
    }
    let parts: Vec<String> = words.iter().map(|w| fmt_expr(*w, n)).collect();
    parts.join(", ")
}

pub fn shifted_word_len(words: &[ExprId], i: usize, len: Option<usize>) -> ExprId {
    let align = |j: usize| -> ExprId {
        let w = words
            .get(j)
            .copied()
            .unwrap_or_else(|| expr::konst(U256::ZERO));
        match len {
            Some(l) if j == words.len() - 1 && l % 32 != 0 => {
                expr::op2(op::SHL, expr::konst_u64(8 * (32 - (l % 32)) as u64), w)
            }
            _ => w,
        }
    };
    let hi = align(i);
    let lo = align(i + 1);
    expr::op2(
        op::OR,
        expr::op2(op::SHL, expr::konst_u64(32), hi),
        expr::op2(op::SHR, expr::konst_u64(224), lo),
    )
}

const PANICS: [(u64, &str); 10] = [
    (0x00, "generic"),
    (0x01, "assert failed"),
    (0x11, "arithmetic overflow"),
    (0x12, "division by zero"),
    (0x21, "invalid enum value"),
    (0x22, "invalid storage byte array"),
    (0x31, "pop on empty array"),
    (0x32, "array index out of bounds"),
    (0x41, "memory allocation too large"),
    (0x51, "uninitialized function pointer"),
];

fn panic_name(code: u64) -> String {
    let known = PANICS.iter().find(|(c, _)| *c == code);
    known.map_or_else(|| format!("{code:#x}"), |(_, name)| name.to_string())
}

/* A compiler takes a text reason in a require and nothing else. Every other failure is
written as the statement that makes it. */
pub fn failure(reason: &str) -> String {
    if reason.starts_with('"') {
        return format!("revert({reason});");
    }
    let Some((name, rest)) = reason.split_once('(') else {
        let word = reason.strip_prefix("0x").filter(|w| w.len() <= 8);
        return match word.and_then(|w| u32::from_str_radix(w, 16).ok()) {
            Some(selector) => format!("_fail(abi.encodeWithSelector(bytes4({selector:#010x})));"),
            None => format!("revert({reason});"),
        };
    };
    let given = rest.strip_suffix(')').unwrap_or(rest);
    if name == "Panic" {
        let named = PANICS.iter().find(|(_, n)| *n == given).map(|(c, _)| *c);
        let code = named.or_else(|| u64::from_str_radix(given.trim_start_matches("0x"), 16).ok());
        return format!("_panic({:#04x});", code.unwrap_or(0));
    }
    match name.strip_prefix("CustomError_") {
        Some(selector) if given.is_empty() => {
            format!("_fail(abi.encodeWithSelector(bytes4(0x{selector})));")
        }
        Some(selector) => {
            format!("_fail(abi.encodeWithSelector(bytes4(0x{selector}), {given}));")
        }
        None => format!("revert {reason};"),
    }
}

fn known_bits(e: ExprId, asked: U256) -> Option<U256> {
    if let Some(word) = expr::as_const(e) {
        return Some(word & asked);
    }
    if (expr::may_bits(e) & asked).is_zero() {
        return Some(U256::ZERO);
    }
    let by = |amount: ExprId| expr::as_const(amount).and_then(|k| k.as_usize());
    match expr::node(e) {
        Node::Op(op::OR, v) => {
            let mut parts = v.iter().map(|x| known_bits(*x, asked));
            parts.try_fold(U256::ZERO, |all, part| Some(all | part?))
        }
        Node::Op(op::SHL, v) => {
            let k = by(v[0]).filter(|k| *k < 256)? as u32;
            Some(known_bits(v[1], asked >> k)? << k)
        }
        Node::Op(op::SHR, v) => {
            let k = by(v[0]).filter(|k| *k < 256)? as u32;
            Some(known_bits(v[1], asked << k)? >> k)
        }
        _ => None,
    }
}

pub fn decode_string_payload(words: &[ExprId], payload_len: Option<usize>) -> Option<String> {
    let offset = expr::as_const(shifted_word_len(words, 0, payload_len))?;
    if offset != U256::from_u64(0x20) {
        return None;
    }
    let len = expr::as_const(shifted_word_len(words, 1, payload_len))?.as_usize()?;
    if len > 1024 {
        return None;
    }
    let mut bytes = Vec::new();
    let mut i = 2;
    while bytes.len() < len {
        // The text can end inside a word whose other bytes are whatever memory held.
        let left = (len - bytes.len()).min(32) as u32;
        let asked = !expr::mask_bits(8 * (32 - left));
        let w = known_bits(shifted_word_len(words, i, payload_len), asked)?;
        bytes.extend_from_slice(&w.to_be_bytes());
        i += 1;
        if i > words.len() + 1 {
            break;
        }
    }
    bytes.truncate(len);
    Some(escape(&String::from_utf8_lossy(&bytes)))
}

pub fn decode_plain_string(words: &[ExprId]) -> Option<String> {
    let len = expr::as_const(*words.first()?)?.as_usize()?;
    if len == 0 || len > 1024 || words.len() < 2 {
        return None;
    }
    let mut bytes = Vec::new();
    for w in &words[1..] {
        bytes.extend_from_slice(&expr::as_const(*w)?.to_be_bytes());
        if bytes.len() >= len {
            break;
        }
    }
    if bytes.len() < len {
        return None;
    }
    bytes.truncate(len);
    if !bytes
        .iter()
        .all(|b| *b >= 0x20 && *b < 0x7f || *b == b'\n' || *b == b'\t')
    {
        return None;
    }
    Some(escape(&String::from_utf8_lossy(&bytes)))
}

// The bytes of a literal the code keeps in itself say more than where it keeps them.
fn code_text(kind: u8, src: ExprId, len: ExprId, n: &Names) -> Option<String> {
    let at = expr::as_const(src)?.as_usize()?;
    let len = expr::as_const(len)?.as_usize()?;
    let bytes = n.code.get(at..at.checked_add(len)?)?;
    let text = |b: &u8| *b >= 0x20 && *b < 0x7f || *b == b'\n' || *b == b'\t';
    (kind == op::CODECOPY && len >= 4 && bytes.iter().all(text))
        .then(|| escape(&String::from_utf8_lossy(bytes)))
}

pub fn escape(s: &str) -> String {
    let mut out = String::new();
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            // The report puts expressions in code spans. A backtick from the bytecode would
            // close one and let the rest of the string through as markup.
            '`' => out.push_str("\\x60"),
            c if (c as u32) < 0x20 || c == '\u{fffd}' => {
                out.push_str(&format!("\\x{:02x}", c as u32 & 0xff))
            }
            c => out.push(c),
        }
    }
    out
}

pub fn fmt_call_output(off: ExprId, len: ExprId, n: &Names) -> String {
    let size = format!("min({}, returndatasize())", fmt_expr(len, n));
    format!(
        "mem[{}:+{size}] = returndata[0:+{size}];",
        fmt_mem_at(off, n)
    )
}

pub fn fmt_call_input(
    words: &[ExprId],
    in_len: Option<U256>,
    n: &Names,
) -> (Option<String>, Vec<String>) {
    if words.is_empty() {
        return (None, vec![]);
    }
    let in_len = in_len.and_then(|l| l.as_usize());
    if let Some(sel) = leading_selector(words[0], in_len) {
        let looks_like_selector = in_len.map_or(
            expr::as_const(words[0]).is_none_or(|c| (c & expr::mask_bits(224)).is_zero()),
            |l| l >= 4 && (l - 4) % 32 == 0,
        );
        if looks_like_selector {
            let nargs = in_len
                .map(|l| l.saturating_sub(4) / 32)
                .unwrap_or(words.len().saturating_sub(1));
            let args: Vec<String> = (0..nargs.min(words.len()))
                .map(|i| fmt_expr(shifted_word_len(words, i, in_len), n))
                .collect();
            let name = match sigs::function(sel) {
                Some(sig) => sigs::name_of(&sig).to_string(),
                None => format!("func_{:08x}", sel),
            };
            return (Some(name), args);
        }
    }
    (None, words.iter().map(|w| fmt_expr(*w, n)).collect())
}

/* Call data that is not a selector and whole words has no abi.encode form of its true
length. It is printed as packed bytes, each piece with its width. */
// Packed, a value cast to a narrower type reads as fewer bytes than the word that is hashed.
fn fmt_whole_word(e: ExprId, n: &Names) -> String {
    let text = fmt_expr(e, n);
    let cast = text.split_once('(').map_or("", |(cast, _)| cast);
    let width = cast.trim_start_matches(|c: char| c.is_ascii_alphabetic());
    let named = matches!(text.as_str(), "msg.sender" | "tx.origin" | "block.coinbase")
        || n.narrow.contains(&text);
    let narrow = named
        || match cast.strip_suffix(width) {
            Some("uint" | "int") => width != "256" && !width.is_empty(),
            Some("bytes") => width != "32" && !width.is_empty(),
            Some("address" | "bool") => width.is_empty(),
            _ => false,
        };
    // The compiler packs a bare literal into the fewest bytes that hold it.
    match narrow || (n.strict && expr::as_const(e).is_some()) {
        true => format!("uint256({text})"),
        false => text,
    }
}

fn fmt_piece((e, width): &(ExprId, u8), n: &Names) -> String {
    let bits = 8 * u32::from(*width);
    match (expr::as_const(*e), expr::node(*e)) {
        _ if *width == 32 => fmt_expr(*e, n),
        (Some(c), _) => format!("bytes{width}({})", c.to_hex_padded(usize::from(*width))),
        (None, Node::Op(op::SHR, v)) if expr::as_const(v[0]) == Some(U256::from(256 - bits)) => {
            format!("bytes{width}({})", fmt_expr(v[1], n))
        }
        // Packed, an address is its twenty bytes.
        (None, Node::Env(op::CALLER | op::ADDRESS | op::ORIGIN | op::COINBASE, _))
            if *width == 20 =>
        {
            fmt_expr(*e, n)
        }
        _ => match fmt_expr(*e, n) {
            cast if cast.starts_with(&format!("uint{bits}(")) => {
                format!("bytes{width}({cast})")
            }
            value => format!("bytes{width}(uint{bits}({value}))"),
        },
    }
}

fn fmt_call_pieces(
    pieces: &[(ExprId, u8)],
    n: &Names,
) -> (Option<String>, Vec<String>, &'static str) {
    let usual = pieces[0].1 == 4 && pieces[1..].iter().all(|(_, width)| *width == 32);
    // Packed, a whole word cast to a narrower type would read as fewer bytes than are sent.
    let piece = |p: &(ExprId, u8)| match (usual, p.1) {
        (false, 32) => fmt_whole_word(p.0, n),
        _ => fmt_piece(p, n),
    };
    let encoder = match usual && pieces.len() > 1 {
        true => "abi.encodeWithSelector",
        false => "abi.encodePacked",
    };
    match expr::as_const(pieces[0].0).filter(|_| usual) {
        Some(sel) => {
            let sel = sel.low_u64() as u32;
            let name = match sigs::function(sel) {
                Some(sig) => sigs::name_of(&sig).to_string(),
                None => format!("func_{sel:08x}"),
            };
            let args = pieces[1..].iter().map(|(e, _)| fmt_expr(*e, n)).collect();
            (Some(name), args, encoder)
        }
        None => (None, pieces.iter().map(piece).collect(), encoder),
    }
}

fn precompile_name(addr: U256) -> Option<&'static str> {
    if !addr.fits_u64() {
        return None;
    }
    Some(match addr.low_u64() {
        1 => "ecrecover",
        2 => "sha256",
        3 => "ripemd160",
        4 => "identity",
        5 => "modexp",
        6 => "bn256Add",
        7 => "bn256ScalarMul",
        8 => "bn256Pairing",
        9 => "blake2f",
        10 => "pointEvaluation",
        _ => return None,
    })
}

#[must_use]
pub fn bytes_value(off: ExprId, len: ExprId) -> Option<ExprId> {
    let Node::MLoad(pointer, _) = expr::node(len) else {
        return None;
    };
    (expr::add_const(pointer, U256::from_u64(32)) == off).then_some(pointer)
}

fn fmt_call_arg(arg: &crate::lift::Arg, n: &Names) -> String {
    use crate::lift::Arg;
    match arg {
        Arg::Word(e) => fmt_expr(*e, n),
        Arg::List(words) => {
            let items: Vec<String> = words.iter().map(|w| fmt_expr(*w, n)).collect();
            format!("[{}]", items.join(", "))
        }
        Arg::Bytes(len, words) => {
            let mut sized = vec![expr::konst_u64(*len)];
            sized.extend(words);
            let fixed: Option<Vec<U256>> = words.iter().map(|w| expr::as_const(*w)).collect();
            match (decode_plain_string(&sized), fixed) {
                (Some(text), _) => format!("\"{text}\""),
                (None, Some(consts)) => {
                    let bytes: Vec<u8> = consts.iter().flat_map(|c| c.to_be_bytes()).collect();
                    let digits: Vec<String> = bytes[..(*len as usize).min(bytes.len())]
                        .iter()
                        .map(|b| format!("{b:02x}"))
                        .collect();
                    format!("hex\"{}\"", digits.concat())
                }
                (None, None) if *len == 32 * words.len() as u64 => {
                    let items: Vec<String> = words.iter().map(|w| fmt_expr(*w, n)).collect();
                    format!("abi.encode({})", items.join(", "))
                }
                (None, None) => {
                    let items: Vec<String> = words.iter().map(|w| fmt_expr(*w, n)).collect();
                    format!("bytes{}(abi.encodePacked({}))", len, items.join(", "))
                }
            }
        }
        Arg::Copied { kind, src, len } => match *kind {
            op::MCOPY if n.strict => fmt_bytes_range(*src, *len, n),
            op::MCOPY => match bytes_value(*src, *len) {
                Some(pointer) => format!("bytes({})", fmt_mem_off(pointer, n)),
                None => format!("mem[{}:+{}]", fmt_mem_at(*src, n), fmt_expr(*len, n)),
            },
            _ => match code_text(*kind, *src, *len, n) {
                Some(text) => format!("\"{text}\""),
                // A stretch of the call data is a value a compiler knows, written from
                // its first byte to the one after its last.
                None if n.strict && *kind == op::CALLDATACOPY => {
                    let from = fmt_expr(*src, n);
                    format!("msg.data[{from}:{from} + {}]", fmt_prec(*len, P_ADD + 1, n))
                }
                None => format!(
                    "{}[{}:+{}]",
                    copy_source(*kind),
                    fmt_expr(*src, n),
                    fmt_expr(*len, n)
                ),
            },
        },
    }
}

/* The first arguments of a call read off the words at the start of its data. An argument
made from a word of the data that no write is known for says nothing, so the list stops
before it. */
fn fmt_call_head(head: &[ExprId], in_off: ExprId, n: &Names) -> (Option<String>, Vec<String>) {
    let Some((sel, args)) = call_head(head, in_off) else {
        return (None, vec![]);
    };
    let name = match sigs::function(sel) {
        Some(sig) => sigs::name_of(&sig).to_string(),
        None => format!("func_{sel:08x}"),
    };
    (
        Some(name),
        args.into_iter().map(|arg| fmt_expr(arg, n)).collect(),
    )
}

// Without a selector the call prints as the memory it reads, so none of its head is given.
#[must_use]
pub fn call_head(head: &[ExprId], in_off: ExprId) -> Option<(u32, Vec<ExprId>)> {
    let sel = head.first().and_then(|w| leading_selector(*w, None))?;
    let (base, start) = expr::split_offset(in_off);
    let unwritten = |x: &Node| match x {
        Node::MLoad(at, _) => {
            let (b, o) = expr::split_offset(*at);
            b == base && o >= start
        }
        _ => false,
    };
    let args = (0..head.len().saturating_sub(1))
        .map(|i| shifted_word_len(head, i, None))
        .take_while(|arg| !expr::contains(*arg, &unwritten))
        .collect();
    Some((sel, args))
}

fn forwards_all_gas(gas: ExprId) -> bool {
    let left = |e: ExprId| matches!(expr::node(e), Node::Env(op::GAS, _));
    left(gas) || matches!(expr::node(gas), Node::Op(op::SUB, v) if left(v[0]))
}

/* The gas left is state, so a value read at one point is not the value at a later one.
Passing all gas to a call is the one use that needs no name. */
pub fn name_gas_reads(l: &Lifted, n: &Names) {
    let mut roots: Vec<ExprId> = l.edge_assigns.values().flatten().map(|(_, v)| *v).collect();
    let mut read: HashSet<ExprId> = HashSet::new();
    for nd in &l.nodes {
        for s in &nd.stmts {
            let exprs = crate::lift::stmt_exprs(s);
            match s {
                Stmt::Drop(e) if matches!(expr::node(*e), Node::Env(op::GAS, _)) => {
                    read.insert(*e);
                }
                Stmt::Call { gas, .. } if forwards_all_gas(*gas) => {
                    roots.extend(exprs.into_iter().filter(|e| e != gas))
                }
                _ => roots.extend(exprs),
            }
        }
        roots.extend(crate::lift::term_exprs(&nd.term));
    }
    let mut used: HashSet<ExprId> = HashSet::new();
    while let Some(e) = roots.pop() {
        if used.insert(e) {
            roots.extend(expr::children(e));
        }
    }
    read.retain(|e| used.contains(e));
    *n.gas_named.borrow_mut() = read;
}

/* A copy from where the call data ends reads zeros. Shown as a copy it reads as if it
brought data in, so whole words at fixed places are stated as the zeros they get. */
fn zero_words(kind: u8, dest: ExprId, src: ExprId, len: ExprId) -> Option<Vec<ExprId>> {
    let past_end = matches!(expr::node(src), Node::Env(op::CALLDATASIZE, _));
    let at = expr::as_const(dest).filter(|d| d.fits_u64())?.low_u64();
    let n = expr::as_const(len).filter(|l| l.fits_u64())?.low_u64();
    let whole = n > 0 && n <= 256 && n.is_multiple_of(32);
    (kind == op::CALLDATACOPY && past_end && whole)
        .then(|| (0..n / 32).map(|k| expr::konst_u64(at + 32 * k)).collect())
}

pub fn fmt_stmt(s: &Stmt, n: &Names) -> String {
    match s {
        Stmt::Assign { var, value } => {
            format!("{} = {};", fmt_expr(*var, n), fmt_assigned(*var, *value, n))
        }
        Stmt::MStore {
            off, val, width, ..
        } => {
            n.answers.borrow_mut().remove(off);
            if n.strict && is_free_pointer(*off) {
                return fmt_taken(*val, n).unwrap_or_default();
            }
            let ahead = match scalar_word(*off, n) {
                Some(_) => String::new(),
                None => taken_ahead(*off, n),
            };
            if owned_memory(*off, n) && scalar_word(*off, n).is_none() {
                let store = match width {
                    1 => "_store8",
                    _ => "_store",
                };
                let (at, word) = (fmt_mem_off(*off, n), as_word(*val, n));
                return format!("{ahead}{store}({at}, {word});");
            }
            if *width == 1 {
                format!("mem8[{}] = {};", fmt_mem_off(*off, n), fmt_expr(*val, n))
            } else if let Some(selector) = stored_selector(*off, *val, n) {
                format!("{} = {selector};", fmt_mem_word(*off, n))
            } else if let Some(name) = scalar_word(*off, n) {
                let value = handed_word(*val, n).unwrap_or_else(|| as_word(*val, n));
                format!("{name} = {value};")
            } else {
                format!("{} = {};", fmt_mem_word(*off, n), fmt_stored_word(*val, n))
            }
        }
        Stmt::SStore {
            key,
            val,
            transient,
            ..
        } => {
            if !n.fields.is_empty() && !*transient {
                if let Some((k, off, bits, value)) = packed_write_shown(*key, *val, n) {
                    if let Some(name) = n.fields.get(&(k, off, bits)) {
                        let shown = match expr::as_const(value) {
                            Some(c) if n.bool_fields.contains(&(k, off, bits)) && c.is_zero() => {
                                "false".to_string()
                            }
                            Some(c)
                                if n.bool_fields.contains(&(k, off, bits)) && c == U256::ONE =>
                            {
                                "true".to_string()
                            }
                            _ => fmt_expr(value, n),
                        };
                        return format!("{} = {};", name, shown);
                    }
                }
            }
            if n.strict && !*transient {
                // A variable narrower than its slot is stored by keeping the other bytes.
                // In source that is a plain assignment.
                if let Some((k, 0, bits, value)) = packed_write(*key, *val) {
                    let ty = n.storage_types.get(&k);
                    if let Some(ty) = ty.filter(|t| width_of(t) == Some(bits)) {
                        let name = fmt_slot(*key, n, SlotSpace::Persistent);
                        return format!("{name} = {};", as_type(ty, value, n));
                    }
                }
            }
            if let Some(writes) = packed_store(*key, *val, n).filter(|_| n.strict && !*transient) {
                return writes;
            }
            if !*transient && !n.member_fields.is_empty() {
                if let Some(w) = crate::ssa::field_write(*key, *val) {
                    if let Some(field) = member_field(*key, w.bit_offset, w.bits, n) {
                        return format!("{} = {};", field, fmt_expr(w.value, n));
                    }
                }
            }
            if !*transient {
                if let Some((root, value)) = element_write(*key, *val, n) {
                    let shown = match (
                        expr::as_const(value),
                        n.elem_types.get(&root).map(String::as_str),
                    ) {
                        (Some(c), Some("bool")) if c.is_zero() => "false".to_string(),
                        (Some(c), Some("bool")) if c == U256::ONE => "true".to_string(),
                        _ => fmt_expr(value, n),
                    };
                    return format!("{} = {};", fmt_slot(*key, n, SlotSpace::Persistent), shown);
                }
            }
            format!(
                "{} = {};",
                fmt_slot(*key, n, SlotSpace::from_transient(*transient)),
                fmt_expr(*val, n)
            )
        }
        Stmt::Log {
            off,
            len,
            topics,
            data,
        } => {
            let first = topics.first().and_then(|t| expr::as_const(*t));
            let unnamed = first.is_some_and(|t0| sigs::event(&t0.to_be_bytes()).is_none());
            let types = known_event_types(topics, n);
            let declared = |i: usize| types.get(topics.len().saturating_sub(1) + i);
            let data_args: Vec<String> = match data {
                Some(words) if n.strict && unnamed => {
                    words.iter().map(|w| as_word(*w, n)).collect()
                }
                Some(words) if n.strict && words.len() + topics.len() == types.len() + 1 => {
                    let typed = |(i, w): (usize, &ExprId)| match declared(i) {
                        Some(ty) => as_declared(ty, *w, n),
                        None => fmt_expr(*w, n),
                    };
                    words.iter().enumerate().map(typed).collect()
                }
                Some(words) => words.iter().map(|w| fmt_expr(*w, n)).collect(),
                None if expr::as_const(*len) != Some(U256::ZERO) => {
                    vec![fmt_mem_range(*off, *len, n)]
                }
                None => Vec::new(),
            };
            fmt_log_parts(topics, data_args, n)
        }
        Stmt::Call {
            kind,
            gas,
            addr,
            value,
            in_off,
            in_len,
            out_len: _,
            input,
            input_head,
            layout,
            args: decoded,
            result,
            ..
        } => {
            let target = match expr::as_const(*addr).and_then(precompile_name) {
                Some(name) => name.to_string(),
                None => fmt_prec(*addr, P_PRIMARY, n),
            };
            let mut opts = Vec::new();
            if let Some(v) = value {
                if expr::as_const(*v) != Some(U256::ZERO) {
                    opts.push(format!("value: {}", fmt_expr(*v, n)));
                }
            }
            if !forwards_all_gas(*gas) {
                opts.push(format!("gas: {}", fmt_expr(*gas, n)));
            }
            let opts_s = if opts.is_empty() {
                String::new()
            } else {
                format!("{{{}}}", opts.join(", "))
            };
            let method = match *kind {
                op::CALL => "call",
                op::CALLCODE => "callcode",
                op::DELEGATECALL => "delegatecall",
                op::STATICCALL => "staticcall",
                _ => "call",
            };
            // The built-in that copies memory reads as the copy printed after it.
            let copy = expr::as_const(*addr) == Some(U256::from_u64(4));
            let known = !copy && (input.is_some() || layout.is_some());
            let partial = !copy && !known && !n.payload_overrides.borrow().contains_key(in_off);
            let tail = expr::as_const(*in_len).map_or(0, |l| (l.low_u64() % 32) as u8);
            let aligned = |words: &[ExprId]| -> Vec<(ExprId, u8)> {
                let last = words.len() - 1;
                let width = |i: usize| if i == last { tail } else { 32 };
                words
                    .iter()
                    .enumerate()
                    .map(|(i, w)| (*w, width(i)))
                    .collect()
            };
            let usual = layout
                .as_deref()
                .filter(|l| l[0].1 == 4 && l[1..].iter().all(|(_, width)| *width == 32));
            /* Code that ors the selector into the first word leaves no piece of four
            bytes. The words then still give the call when the selector is taken off. */
            let (fname, mut args, encoder) = match (usual, input) {
                _ if copy => (None, vec![], "abi.encode"),
                (Some(pieces), _) => fmt_call_pieces(pieces, n),
                (None, Some(words)) => match fmt_call_input(words, expr::as_const(*in_len), n) {
                    (None, _) if layout.is_some() || (tail != 0 && !words.is_empty()) => {
                        fmt_call_pieces(&layout.clone().unwrap_or_else(|| aligned(words)), n)
                    }
                    (fname, args) => (fname, args, "abi.encode"),
                },
                (None, None) if partial => {
                    let (fname, args) = fmt_call_head(input_head, *in_off, n);
                    (fname, args, "abi.encode")
                }
                (None, None) => (None, vec![], "abi.encode"),
            };
            let whole = decoded.as_ref().filter(|_| fname.is_some());
            if let Some(decoded) = whole {
                args = decoded.iter().map(|a| fmt_call_arg(a, n)).collect();
            } else if partial && fname.is_some() {
                args.push("...".to_string());
            }
            let selector = call_selector(layout.as_deref(), input.as_deref(), input_head);
            let payload = match (&fname, known) {
                // A compiler knows a selector by its four bytes, and by a name only for a
                // function declared where it can see it.
                (Some(_), _) if n.strict && selector.is_some() => format!(
                    "abi.encodeWithSelector(bytes4({:#010x}), {})",
                    selector.unwrap_or(0),
                    args.join(", ")
                )
                .replace(", )", ")"),
                (Some(f), _) => format!(
                    "abi.encodeWithSelector({}.selector, {})",
                    f,
                    args.join(", ")
                )
                .replace(", )", ")"),
                (None, true) if args.is_empty() => "\"\"".into(),
                (None, true) => format!("{encoder}({})", args.join(", ")),
                (None, false) => {
                    if expr::as_const(*in_len) == Some(U256::ZERO) {
                        "\"\"".into()
                    } else if let Some(text) =
                        n.payload_overrides.borrow().get(in_off).filter(|_| !copy)
                    {
                        text.clone()
                    } else if let Some(pointer) =
                        bytes_value(*in_off, *in_len).filter(|_| !n.strict)
                    {
                        format!("bytes({})", fmt_mem_off(pointer, n))
                    } else {
                        fmt_bytes_range(*in_off, *in_len, n)
                    }
                }
            };
            let answered = match expr::node(*result) {
                Node::CallResult(seq) if n.strict && !copy && method != "callcode" => Some(seq),
                _ => None,
            };
            if let Some(seq) = answered {
                return format!(
                    "({}, returned_{}) = {}.{method}{opts_s}({payload});",
                    fmt_expr(*result, n),
                    n.seq(seq),
                    as_address(*addr, n)
                );
            }
            match fname {
                Some(f) if *kind == op::CALL || *kind == op::STATICCALL => {
                    format!(
                        "{} = {}.{}{}({}); // {}({})",
                        fmt_expr(*result, n),
                        target,
                        method,
                        opts_s,
                        payload,
                        f,
                        args.join(", ")
                    )
                }
                _ => format!(
                    "{} = {}.{}{}({});",
                    fmt_expr(*result, n),
                    target,
                    method,
                    opts_s,
                    payload
                ),
            }
        }
        Stmt::Create {
            kind,
            value,
            off,
            len,
            salt,
            result,
            init,
            ..
        } => {
            let code = match init {
                Some(words) if !words.is_empty() => format!("bytecode[{} words]", words.len()),
                _ => fmt_mem_range(*off, *len, n),
            };
            let v = if expr::as_const(*value) == Some(U256::ZERO) {
                String::new()
            } else {
                format!("{{value: {}}}", fmt_expr(*value, n))
            };
            match (kind, salt) {
                (&op::CREATE2, Some(s)) => format!(
                    "{} = create2{}({}, salt: {});",
                    fmt_expr(*result, n),
                    v,
                    code,
                    fmt_expr(*s, n)
                ),
                _ => format!("{} = create{}({});", fmt_expr(*result, n), v, code),
            }
        }
        Stmt::Copy {
            kind,
            dest,
            src,
            len,
            addr,
            ..
        } => {
            if let Some(words) = zero_words(*kind, *dest, *src, *len) {
                let zeroed: Vec<String> = words
                    .into_iter()
                    .map(|w| match owned_memory(w, n) {
                        true => format!("_store({}, 0);", fmt_mem_off(w, n)),
                        false => format!("{} = 0;", fmt_mem_word(w, n)),
                    })
                    .collect();
                return zeroed.join(" ");
            }
            let copier = match (*kind, addr) {
                (op::CALLDATACOPY, None) => Some("_copy_calldata"),
                (op::RETURNDATACOPY, None) => Some("_copy_returned"),
                (op::MCOPY, None) => Some("_copy"),
                _ => None,
            };
            let ahead = match copier {
                Some(_) => taken_ahead(*dest, n),
                None => String::new(),
            };
            if let Some(copier) = copier.filter(|_| owned_memory(*dest, n)) {
                let (to, from) = (fmt_mem_off(*dest, n), fmt_mem_off(*src, n));
                return format!("{ahead}{copier}({to}, {from}, {});", fmt_expr(*len, n));
            }
            let src_s = match addr {
                Some(a) => format!(
                    "{}.code[{}:+{}]",
                    fmt_prec(*a, P_PRIMARY, n),
                    fmt_expr(*src, n),
                    fmt_expr(*len, n)
                ),
                None if *kind == op::MCOPY => {
                    format!("mem[{}:+{}]", fmt_mem_at(*src, n), fmt_expr(*len, n))
                }
                None if code_text(*kind, *src, *len, n).is_some() => {
                    format!(
                        "\"{}\"",
                        code_text(*kind, *src, *len, n).unwrap_or_default()
                    )
                }
                None => format!(
                    "{}[{}:+{}]",
                    copy_source(*kind),
                    fmt_expr(*src, n),
                    fmt_expr(*len, n)
                ),
            };
            format!(
                "mem[{}:+{}] = {};",
                fmt_mem_at(*dest, n),
                fmt_expr(*len, n),
                src_s
            )
        }
        Stmt::Internal {
            callee,
            args,
            results,
            ..
        } => {
            // A number handed to a helper that uses it as a place is the block that starts there.
            let places = n.offsets.handed.get(callee);
            let place = |j: &usize| places.is_some_and(|p| p.contains(j));
            let declared = n.callee_params.get(callee).filter(|_| n.strict);
            let shown = |(j, x): (usize, &ExprId)| match (handed_word(*x, n), place(&j)) {
                (Some(word), _) => word,
                (None, true) => fmt_stored_word(*x, n),
                (None, false) => match declared.and_then(|types| types.get(j)) {
                    Some(ty) => as_declared(ty, *x, n),
                    None => fmt_expr(*x, n),
                },
            };
            let a: Vec<String> = args.iter().enumerate().map(shown).collect();
            let call = format!("{}({})", n.callee_name(*callee), a.join(", "));
            /* A result every caller knows as a constant has no name here. Its place in
            the list stays empty so the others keep theirs. */
            let bound: Vec<String> = results
                .iter()
                .map(|r| match expr::is_const(*r) {
                    true => String::new(),
                    false => fmt_expr(*r, n),
                })
                .collect();
            match bound.as_slice() {
                all if all.iter().all(String::is_empty) => format!("{};", call),
                [one] => format!("{} = {};", one, call),
                _ => format!("({}) = {};", bound.join(", "), call),
            }
        }
        Stmt::Drop(e) if matches!(expr::node(*e), Node::Env(op::GAS, _)) => {
            match n.gas_named.borrow().contains(e) {
                true => format!("{} = gasleft();", fmt_expr(*e, n)),
                false => String::new(),
            }
        }
        Stmt::Drop(e) => format!("// ignored: {}", fmt_expr(*e, n)),
        Stmt::Require {
            cond,
            data,
            invalid,
        } => {
            // Printing the test first would leave its parts behind as unused temporaries.
            if !*invalid && is_hidden_require(*cond, data.as_deref(), n) {
                return String::new();
            }
            let c = fmt_cond(*cond, n);
            if *invalid {
                return format!("assert({});", c);
            }
            match data {
                Some(words) if !words.is_empty() => {
                    let len = leading_selector(words[0], None)
                        .map(|_| U256::from_u64(4 + 32 * (words.len() as u64 - 1)));
                    let p = fmt_payload(words, len, n, PayloadKind::Revert);
                    if p == "Panic(assert failed)" {
                        format!("assert({});", c)
                    } else if n.strict && !p.starts_with('"') {
                        let failed = fmt_cond(expr::op1(op::ISZERO, *cond), n);
                        format!("if ({failed}) {}", failure(&p))
                    } else if p.starts_with('"') || p.starts_with("Panic(") {
                        format!("require({}, {});", c, p)
                    } else {
                        format!(
                            "if ({}) revert {};",
                            fmt_expr(expr::op1(op::ISZERO, *cond), n),
                            p
                        )
                    }
                }
                _ => format!("require({});", c),
            }
        }
    }
}

fn strip_outer_parens(s: &str) -> &str {
    let b = s.as_bytes();
    if b.len() < 2 || b[0] != b'(' || b[b.len() - 1] != b')' {
        return s;
    }
    let mut depth = 0i32;
    for (i, &c) in b.iter().enumerate() {
        match c {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 && i != b.len() - 1 {
                    return s;
                }
            }
            _ => {}
        }
    }
    &s[1..s.len() - 1]
}

fn call_selector(
    layout: Option<&[(ExprId, u8)]>,
    input: Option<&[ExprId]>,
    head: &[ExprId],
) -> Option<u32> {
    let piece = layout.and_then(|l| l.first()).map(|(e, _)| *e);
    let word = input.and_then(|w| w.first()).copied();
    let start = piece.or(word).or(head.first().copied())?;
    // Some code ors the selector into a word that also holds the start of the first
    // argument, and the word is then no constant.
    let Some(first) = expr::as_const(start) else {
        return leading_selector(start, None);
    };
    let high = first.bits() > 32;
    Some(if high { first >> 224 } else { first }.low_u64() as u32)
}

// The failure of a call handed on as it came: its data copied to memory and given as
// this call's own.
pub fn bubbled(stmts: &[Stmt], off: ExprId, len: ExprId) -> bool {
    let whole = matches!(expr::node(len), Node::Env(op::RETURNDATASIZE, _));
    let copied = stmts.iter().any(|st| match st {
        Stmt::Copy {
            kind: op::RETURNDATACOPY,
            dest,
            src,
            len: n,
            ..
        } => *dest == off && *n == len && expr::as_const(*src) == Some(U256::ZERO),
        _ => false,
    });
    whole && copied
}

/* A reason that is a string already in memory: its length is read from where the
string lies and its bytes are copied from the word after. What is printed is the place
it lies at, which a function taking the reason has as an argument. */
fn held_string(stmts: &[Stmt], at: &dyn Fn(ExprId) -> Option<U256>, n: &Names) -> Option<String> {
    let length = stmts.iter().rev().find_map(|st| match st {
        Stmt::MStore {
            off,
            val,
            width: 32,
            ..
        } if at(*off) == Some(U256::from_u64(36)) => Some(*val),
        _ => None,
    })?;
    let Node::MLoad(lies_at, _) = expr::node(length) else {
        return None;
    };
    // The bytes go across from the word after the length to the word after the length
    // written. Some code moves the first word by itself and the rest in a loop, so a
    // move that starts further in still counts, as long as it keeps the two in step.
    let (base, start) = expr::split_offset(lies_at);
    let in_step = |dest: ExprId, src: ExprId| {
        let (from, read) = expr::split_offset(src);
        let written = at(dest).map(|w| w.wrapping_sub(U256::from_u64(68)));
        from == base && written == Some(read.wrapping_sub(start).wrapping_sub(U256::from_u64(32)))
    };
    let copied = stmts.iter().any(|st| match st {
        Stmt::Copy {
            kind: op::MCOPY,
            dest,
            src,
            ..
        } => in_step(*dest, *src),
        Stmt::MStore {
            off,
            val,
            width: 32,
            ..
        } => matches!(expr::node(*val), Node::MLoad(src, _) if in_step(*off, src)),
        _ => false,
    });
    copied.then(|| fmt_expr(lies_at, n))
}

const ERROR_STRING: u64 = 0x08c3_79a0;
const LONGEST_REASON: usize = 1024;

/* The reason a revert gives, read back from the stores that wrote it. A reason longer
than a word is copied out of the code, or stored a word at a time, and the printer then
shows the revert as a range of memory. In source it is one string. */
pub fn error_string(stmts: &[Stmt], off: ExprId, n: &Names) -> Option<String> {
    let (base, start) = expr::split_offset(off);
    let at = |e: ExprId| {
        let (b, c) = expr::split_offset(e);
        (b == base).then(|| c.wrapping_sub(start))
    };
    let stored = |rel: usize| {
        stmts.iter().rev().find_map(|st| match st {
            Stmt::MStore {
                off,
                val,
                width: 32,
                ..
            } if at(*off) == Some(U256::from(rel)) => expr::as_const(*val),
            _ => None,
        })
    };
    let named = stored(0)? >> 224 == U256::from_u64(ERROR_STRING);
    if !named || stored(4)? != U256::from_u64(32) {
        return None;
    }
    if let Some(text) = held_string(stmts, &at, n) {
        return Some(format!("revert(_string({text}));"));
    }
    let length = stored(36)?.as_usize().filter(|l| *l <= LONGEST_REASON)?;
    let copied = stmts.iter().rev().find_map(|st| match st {
        Stmt::Copy {
            kind,
            dest,
            src,
            len,
            addr: None,
            ..
        } if at(*dest) == Some(U256::from_u64(68))
            && expr::as_const(*len) == Some(U256::from(length)) =>
        {
            code_text(*kind, *src, *len, n)
        }
        _ => None,
    });
    if let Some(text) = copied {
        return Some(format!("revert(\"{text}\");"));
    }
    let mut bytes = Vec::new();
    for word in 0..length.div_ceil(32) {
        bytes.extend(stored(68 + 32 * word)?.to_be_bytes());
    }
    bytes.truncate(length);
    let text = |b: &u8| *b >= 0x20 && *b < 0x7f;
    let shown = bytes
        .iter()
        .all(text)
        .then(|| escape(&String::from_utf8_lossy(&bytes)))?;
    Some(format!("revert(\"{shown}\");"))
}

fn flag_or(j: usize, v: ExprId, n: &Names) -> String {
    if let Some(word) = handed_word(v, n) {
        return word;
    }
    if let Some(ty) = n.return_types.get(j).filter(|_| n.strict) {
        return as_declared(ty, v, n);
    }
    let flag = n.bool_returns.get(j).copied() == Some(true);
    match expr::as_const(v) {
        Some(c) if flag && c.is_zero() => "false".to_string(),
        Some(c) if flag && c == U256::ONE => "true".to_string(),
        _ => fmt_expr(v, n),
    }
}

pub fn fmt_term_halt(t: &Term, n: &Names) -> Option<String> {
    Some(match t {
        Term::Return { off, len, data } => match data {
            Some(words)
                if words.len() == n.bool_returns.len()
                    && (n.strict || n.bool_returns.contains(&true))
                    && expr::as_const(*len) == Some(U256::from(32 * words.len())) =>
            {
                let listed = words.iter().enumerate().map(|(j, v)| flag_or(j, *v, n));
                format!("return ({});", listed.collect::<Vec<_>>().join(", "))
            }
            Some(words) if !words.is_empty() => format!(
                "return ({});",
                strip_outer_parens(&fmt_payload(
                    words,
                    expr::as_const(*len),
                    n,
                    PayloadKind::Return
                ))
            ),
            Some(_) => "return;".into(),
            None => {
                if expr::as_const(*len) == Some(U256::ZERO) {
                    "return;".into()
                } else {
                    match n.strict {
                        true => {
                            format!("_return({}, {});", fmt_mem_off(*off, n), fmt_expr(*len, n))
                        }
                        false => format!("return {};", fmt_mem_range(*off, *len, n)),
                    }
                }
            }
        },
        Term::Revert { off, len, data } => match data {
            Some(words) if !words.is_empty() => {
                let p = fmt_payload(words, expr::as_const(*len), n, PayloadKind::Revert);
                if p.starts_with('"')
                    || p.starts_with("Panic(")
                    || p.chars().next().is_some_and(|c| c.is_ascii_uppercase())
                {
                    if n.strict {
                        failure(&p)
                    } else if p.starts_with('"') {
                        format!("revert({});", p)
                    } else {
                        format!("revert {};", p)
                    }
                } else {
                    format!("revert({});", p)
                }
            }
            Some(_) => "revert();".into(),
            None => {
                if expr::as_const(*len) == Some(U256::ZERO) {
                    "revert();".into()
                } else {
                    match n.strict {
                        true => {
                            format!("_revert({}, {});", fmt_mem_off(*off, n), fmt_expr(*len, n))
                        }
                        false => format!("revert({});", fmt_mem_range(*off, *len, n)),
                    }
                }
            }
        },
        Term::Stop => "return;".into(),
        Term::ReturnDyn { ptr, .. } => format!("return {};", fmt_expr(*ptr, n)),
        Term::Invalid => "assert(false); // INVALID".into(),
        Term::SelfDestruct(a) if n.strict => {
            format!("selfdestruct(payable({}));", as_address(*a, n))
        }
        Term::SelfDestruct(a) => format!("selfdestruct({});", fmt_expr(*a, n)),
        Term::InternalReturn(vals) => {
            if vals.is_empty() {
                "return;".into()
            } else {
                format!(
                    "return ({});",
                    vals.iter()
                        .enumerate()
                        .map(|(j, v)| flag_or(j, *v, n))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        }
        Term::Unresolved(t) => format!("jump({}); // unresolved target", fmt_expr(*t, n)),
        Term::CondJump { cond, target } => format!(
            "if ({}) jump({});",
            fmt_expr(*cond, n),
            fmt_expr(*target, n)
        ),
        Term::Infeasible => "// unreachable (invalid jump or stack underflow)".into(),
        _ => return None,
    })
}

pub fn label(l: &Lifted, node: usize) -> String {
    format!("L{:x}@{node}", l.nodes[node].pc)
}

/* One block is lifted once for each stack it is entered with, so its address alone does
not name a place. A label keeps the bare address while no other copy is a target too. */
pub fn name_labels(text: &str) -> String {
    let marked = |at: usize| -> Option<(usize, usize)> {
        let pc = text[..at].bytes().rev().take_while(u8::is_ascii_hexdigit);
        let start = at - pc.count();
        let node = text[at + 1..].bytes().take_while(u8::is_ascii_digit);
        let end = at + 1 + node.count();
        let begins = text[..start].ends_with('L')
            && !text[..start - 1].ends_with(|c: char| c.is_ascii_alphanumeric() || c == '_');
        (begins && start < at && end > at + 1).then_some((start, end))
    };
    let labels: Vec<(usize, usize)> = text
        .match_indices('@')
        .filter_map(|(at, _)| marked(at))
        .collect();
    let mut copies: BTreeMap<&str, BTreeSet<usize>> = BTreeMap::new();
    let parts = |(start, end): (usize, usize)| {
        let (pc, node) = text[start..end].split_once('@').expect("a marked label");
        (pc, node.parse::<usize>().unwrap_or(0))
    };
    for l in &labels {
        let (pc, node) = parts(*l);
        copies.entry(pc).or_default().insert(node);
    }
    let mut out = String::with_capacity(text.len());
    let mut from = 0;
    for l in labels {
        let (pc, node) = parts(l);
        out.push_str(&text[from..l.0]);
        out.push_str(pc);
        match copies[pc].iter().position(|n| *n == node) {
            Some(earlier) if earlier > 0 => out.push_str(&format!("_{}", earlier + 1)),
            _ => {}
        }
        from = l.1;
    }
    out.push_str(&text[from..]);
    out
}

pub fn fmt_flat(l: &Lifted, n: &Names, indent: &str) -> String {
    name_gas_reads(l, n);
    let put_back = stores_put_back(l);
    let mut out = String::new();
    let reach = crate::lift::reachable(l);
    let order = crate::lift::reverse_postorder(l);
    let mut needs_label: HashSet<usize> = HashSet::new();
    for (idx, &nid) in order.iter().enumerate() {
        let nd = &l.nodes[nid];
        if !reach.contains(&nid) {
            continue;
        }
        let prev = if idx > 0 { Some(order[idx - 1]) } else { None };
        let falls = prev.is_some_and(|p| {
            matches!(l.nodes[p].term, Term::Jump(t) if t == nid)
                && nd.preds.len() == 1
                && !l.edge_assigns.contains_key(&(p, nid))
        });
        // The node made for a helper that starts on a loop would repeat the loop's label.
        let made =
            nd.preds.is_empty() && matches!(nd.term, Term::Jump(t) if l.nodes[t].pc == nd.pc);
        if !falls && !made {
            needs_label.insert(nid);
        }
    }
    for (idx, &nid) in order.iter().enumerate() {
        let nd = &l.nodes[nid];
        if needs_label.contains(&nid) {
            out.push_str(&format!("{}{}:\n", indent, label(l, nid)));
        }
        n.end_block();
        let mut dead = dead_memory_stores(&nd.stmts, &on_node(&put_back, nid));
        dead.extend(free_pointer_updates(&nd.stmts, n));
        for (i, s) in nd.stmts.iter().enumerate() {
            if dead.contains(&i) {
                continue;
            }
            let txt = fmt_stmt(s, n);
            for (name, def) in n.take_temps() {
                out.push_str(&format!("{}    uint256 {} = {};\n", indent, name, def));
            }
            if !txt.is_empty() {
                out.push_str(&format!("{}    {}\n", indent, txt));
            }
        }
        let goto = |to: usize| -> String {
            let mut s = String::new();
            if let Some(assigns) = l.edge_assigns.get(&(nid, to)) {
                for (var, val) in assigns {
                    s.push_str(&format!("{} = {}; ", fmt_expr(*var, n), fmt_expr(*val, n)));
                }
            }
            s.push_str(&format!("goto {};", label(l, to)));
            s
        };
        let next = order.get(idx + 1).copied();
        match &nd.term {
            Term::Jump(t) => {
                if Some(*t) != next || l.edge_assigns.contains_key(&(nid, *t)) {
                    out.push_str(&format!("{}    {}\n", indent, goto(*t)));
                }
            }
            Term::Branch { cond, t, f } => {
                match t {
                    Some(t) => out.push_str(&format!(
                        "{}    if ({}) {{ {} }}\n",
                        indent,
                        fmt_expr(*cond, n),
                        goto(*t)
                    )),
                    None => out.push_str(&format!(
                        "{}    if ({}) {{ revert(); }}\n",
                        indent,
                        fmt_expr(*cond, n)
                    )),
                }
                if Some(*f) != next || l.edge_assigns.contains_key(&(nid, *f)) {
                    out.push_str(&format!("{}    {}\n", indent, goto(*f)));
                }
            }
            Term::Switch { target, cases } => {
                out.push_str(&format!(
                    "{}    switch ({}) {{ {} }}\n",
                    indent,
                    fmt_expr(*target, n),
                    cases.iter().map(|c| goto(*c)).collect::<Vec<_>>().join(" ")
                ));
            }
            other => {
                if let Some(s) = fmt_term_halt(other, n) {
                    for (name, def) in n.take_temps() {
                        out.push_str(&format!("{}    uint256 {} = {};\n", indent, name, def));
                    }
                    out.push_str(&format!("{}    {}\n", indent, s));
                }
            }
        }
        for (name, def) in n.take_temps() {
            out.push_str(&format!("{}    uint256 {} = {};\n", indent, name, def));
        }
    }
    name_labels(&out)
}

#[cfg(test)]
mod tests {
    use super::{failure, strip_outer_parens};

    #[test]
    fn a_failure_is_written_as_the_statement_that_makes_it() {
        assert_eq!(failure("\"no\""), "revert(\"no\");");
        assert_eq!(failure("Panic(array index out of bounds)"), "_panic(0x32);");
        let unnamed = "_fail(abi.encodeWithSelector(bytes4(0xb838de96), a));";
        assert_eq!(failure("CustomError_b838de96(a)"), unnamed);
        assert_eq!(failure("Unauthorized()"), "revert Unauthorized();");
    }

    #[test]
    fn outer_parens_are_stripped_only_when_they_wrap_everything() {
        assert_eq!(strip_outer_parens("(a, b)"), "a, b");
        assert_eq!(strip_outer_parens("(uint8(x))"), "uint8(x)");
        assert_eq!(strip_outer_parens("uint8(x)"), "uint8(x)");
        assert_eq!(strip_outer_parens("(a) + (b)"), "(a) + (b)");
        assert_eq!(strip_outer_parens(""), "");
    }
}
