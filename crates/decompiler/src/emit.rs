use crate::expr::{self, kind, ExprId, Node};
use crate::keccak;
use crate::lift::{Lifted, Stmt, Term, FREE_POINTER};
use crate::opcode as op;
use crate::sigs;
use crate::u256::U256;
use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::OnceLock;

const HASHED_SLOTS: u64 = 4096;

const HASH_OFFSET_RANGE: i64 = 16;

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
    pub params: HashMap<u32, String>,
    pub aliases: HashMap<ExprId, String>,
    pub fields: HashMap<(U256, u32, u32), String>,
    pub args: HashMap<u32, String>,
    pub callee_names: HashMap<usize, String>,
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
    pub temp_seq: RefCell<u32>,
    pub seqs: RefCell<HashMap<u32, u32>>,
    pub vars: RefCell<HashMap<u32, u32>>,
    pub layout: MappingLayout,
    pub hide_checked: bool,
    pub temps: RefCell<Vec<(String, String)>>,
    pub temp_of: RefCell<HashMap<ExprId, String>>,
    pub pure_callees: HashSet<usize>,
    pub bools: HashSet<ExprId>,
    pub bool_fields: HashSet<(U256, u32, u32)>,
    pub bool_returns: Vec<bool>,
    pub dyn_arrays: HashSet<U256>,
    pub elem_types: HashMap<U256, String>,
    pub array_resizers: HashSet<usize>,
    pub memo: RefCell<HashMap<ExprId, (String, u8)>>,
}

// Keeps the output linear in size.
const TEMP_THRESHOLD: usize = 160;

impl Names {
    #[must_use]
    pub fn callee_name(&self, pc: usize) -> String {
        self.callee_names
            .get(&pc)
            .cloned()
            .unwrap_or_else(|| format!("func_{pc:#x}"))
    }

    pub fn take_temps(&self) -> Vec<(String, String)> {
        std::mem::take(&mut *self.temps.borrow_mut())
    }

    // A temporary is declared where it is first used.
    // A later block must not refer to one declared inside another branch.
    pub fn end_block(&self) {
        self.temp_of.borrow_mut().clear();
        self.memo.borrow_mut().clear();
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

    pub fn forward(&self, value: ExprId, name: String) {
        self.forwarded.borrow_mut().insert(value, name);
        self.memo.borrow_mut().clear();
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
}

const P_OR: u8 = 2;
const P_XOR: u8 = 3;
const P_AND: u8 = 4;
const P_EQ: u8 = 5;
const P_CMP: u8 = 6;
const P_SHIFT: u8 = 7;
const P_ADD: u8 = 8;
const P_MUL: u8 = 9;
const P_EXP: u8 = 10;
const P_UNARY: u8 = 11;
const P_PRIMARY: u8 = 12;

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

pub fn fmt_log_parts(topics: &[ExprId], data_args: Vec<String>, n: &Names) -> String {
    let mut args: Vec<String> = Vec::new();
    let mut name = None;
    if let Some(t0) = topics.first().and_then(|t| expr::as_const(*t)) {
        if let Some(sig) = sigs::event(&t0.to_be_bytes()) {
            name = Some(sigs::name_of(&sig).to_string());
        }
    }
    let start = if name.is_some() { 1 } else { 0 };
    for t in &topics[start..] {
        args.push(fmt_expr(*t, n));
    }
    args.extend(data_args);
    match name {
        Some(nm) => format!("emit {}({});", nm, args.join(", ")),
        None => match topics.first().and_then(|t| expr::as_const(*t)) {
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

fn stmt_exprs(s: &Stmt) -> Vec<ExprId> {
    crate::lift::node_exprs(&crate::lift::LNode {
        id: 0,
        block: 0,
        pc: 0,
        stmts: vec![s.clone()],
        term: Term::Stop,
        preds: vec![],
        succs: vec![],
        entry_stack: vec![],
        exit_stack: vec![],
    })
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
            stmt_exprs(s).iter().any(|e| {
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

pub fn dead_memory_stores(stmts: &[Stmt]) -> HashSet<usize> {
    let mut dead = HashSet::new();
    let reads: Vec<bool> = stmts.iter().map(reads_memory).collect();
    let ranges: Vec<Option<(u64, u64)>> = stmts.iter().map(written_range).collect();
    for (i, s) in stmts.iter().enumerate() {
        if let Stmt::MStore {
            off,
            val,
            width: 32,
            ..
        } = s
        {
            if matches!(expr::node(*val), Node::MLoad(a, _) if a == *off) {
                dead.insert(i);
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
    let is_param = |e: ExprId| matches!(expr::node(e), Node::CallDataLoad(_));
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
    if !n.hide_checked {
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
        Some(c) if [PANIC_OVERFLOW, PANIC_DIV_BY_ZERO, PANIC_ALLOCATION].contains(&c.low_u64())
            && c.fits_u64()
    )
}

pub const SEL_PANIC: u32 = 0x4e487b71;
pub const SEL_ERROR: u32 = 0x08c379a0;
const PANIC_OVERFLOW: u64 = 0x11;
const PANIC_DIV_BY_ZERO: u64 = 0x12;
const PANIC_ALLOCATION: u64 = 0x41;

pub fn is_bool(e: ExprId, n: &Names) -> bool {
    expr::is_boolean(e)
        || n.bools.contains(&e)
        || packed_read(e).is_some_and(|(k, off, bits)| n.bool_fields.contains(&(k, off, bits)))
        || bool_element(e, n)
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

pub fn fmt_cond(cond: ExprId, n: &Names) -> String {
    if let Some(text) = difference_test(cond, n) {
        return text;
    }
    if is_bool(cond, n) {
        fmt_expr(cond, n)
    } else {
        format!("{} != 0", fmt_prec(cond, P_EQ + 1, n))
    }
}

pub fn fmt_truth(cond: ExprId, n: &Names) -> String {
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
        if base.is_none() && offset < U256::from_u64(0x80) {
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

fn fmt_stored_word(val: ExprId, n: &Names) -> String {
    match (expr::as_const(val), block_ref(val, n)) {
        (Some(_), Some((number, offset))) if offset.is_zero() => format!("ptr{number}"),
        _ => fmt_expr(val, n),
    }
}

#[must_use]
pub fn free_pointer_updates(stmts: &[Stmt], n: &Names) -> HashSet<usize> {
    if n.blocks.is_none() {
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
        let (number, offset) = block_ref(*off, n)?;
        let aligned =
            offset.fits_u64() && offset.low_u64().is_multiple_of(32) && offset.low_u64() < 32 * 64;
        let reads_memory = expr::contains(*val, &|x| matches!(x, Node::MLoad(..)));
        (aligned && !reads_memory).then(|| (number, offset.low_u64() / 32, *val))
    };
    let live: Vec<usize> = (0..stmts.len()).filter(|i| !hidden.contains(i)).collect();
    let mut out = Vec::new();
    let mut at = 0;
    while at < live.len() {
        let mut end = at;
        while end < live.len() && word_of(&stmts[live[end]]).is_some() {
            end += 1;
        }
        let mut by_block: BTreeMap<u32, Vec<(usize, u64, ExprId)>> = BTreeMap::new();
        for i in &live[at..end] {
            let (number, index, val) = word_of(&stmts[*i]).expect("the run holds word stores");
            by_block.entry(number).or_default().push((*i, index, val));
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

pub fn fmt_mem_word(off: ExprId, n: &Names) -> String {
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
            if s + bits <= 256 {
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
    if let Node::Op(op::AND, w) = expr::node(val) {
        if let (Node::SLoad(kk, false, _), Some(keep)) = (expr::node(w[0]), expr::as_const(w[1])) {
            if expr::as_const(kk) == Some(k) {
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
        let (Node::SLoad(kk, false, _), Some(keep)) = (expr::node(w[0]), expr::as_const(w[1]))
        else {
            continue;
        };
        if expr::as_const(kk) != Some(k) {
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
        [(w[0], w[1]), (w[1], w[0])].into_iter().find_map(|(a, b)| {
            match (expr::node(a), expr::as_const(b)) {
                (Node::SLoad(k, false, _), Some(m)) if k == key => Some(m),
                _ => None,
            }
        })
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
            Node::Const(c) => hashed_slot(c).map(|(s, _)| s),
            _ => None,
        }),
        Node::Const(c) => hashed_slot(c).map(|(s, _)| s),
        _ => None,
    }
}

fn slot_name(s: U256, n: &Names, prefix: &str) -> String {
    if let Some(name) = n.storage.get(&s) {
        return name.clone();
    }
    if s.bits() <= 32 {
        format!("{}_{}", prefix, s.to_decimal())
    } else {
        format!("{}_{}", prefix, s.to_hex())
    }
}

fn base_name(e: ExprId, n: &Names, space: SlotSpace) -> String {
    let prefix = match space {
        SlotSpace::Persistent => "stor",
        SlotSpace::Transient => "tstor",
    };
    match expr::as_const(e) {
        Some(c) if hashed_slot(c).is_none() => slot_name(c, n, prefix),
        _ => fmt_slot(e, n, space),
    }
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
        if let Some(name) = n.storage.get(&c) {
            if n.dyn_arrays.contains(&c) {
                return format!("{}.length", name);
            }
            return name.clone();
        }
        if let Some((s, k)) = hashed_slot(c) {
            return format!("{}[{}]", slot_name(s, n, prefix), k.max(0));
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
            for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
                if let Some((s, k)) = expr::as_const(a).and_then(hashed_slot) {
                    return format!(
                        "{}[{}]",
                        slot_name(s, n, prefix),
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
                        return format!("{}[{}]", slot_name(root, n, prefix), idx_s);
                    }
                }
            }
            match expr::node(base) {
                Node::Keccak(words, 0) if words.len() == 1 => {
                    format!("{}[{}]", base_name(words[0], n, space), fmt_expr(idx, n))
                }
                Node::Keccak(words, 0) if words.len() == 2 => {
                    let member = match struct_member(e, n) {
                        Some((_, _, name)) => name.clone(),
                        None => format!("field{}", fmt_expr(idx, n)),
                    };
                    format!("{}.{}", fmt_slot_path(base, n, space), member)
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
        op::GAS => format!("gasleft_{}()", n.seq(seq)),
        op::MSIZE => format!("msize_{}()", n.seq(seq)),
        op::PC => "pc".into(),
        _ => format!("{}()", op::name(o).to_lowercase()),
    }
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

fn fmt_inner(e: ExprId, n: &Names) -> (String, u8) {
    if let Some(text) = member_field_read(e, n) {
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
    if !n.fields.is_empty() {
        if let Some((k, off, bits)) = packed_read(e) {
            if let Some(name) = n.fields.get(&(k, off, bits)) {
                return (name.clone(), P_PRIMARY);
            }
        }
    }
    match expr::node(e) {
        Node::Const(c) => (fmt_const(c), P_PRIMARY),
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
        Node::CallDataLoad(off) => {
            if let Some(i) = calldata_word_index(off) {
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
        Node::MLoad(off, _) => (fmt_mem_word(off, n), P_PRIMARY),
        Node::SLoad(key, transient, _) => (
            fmt_slot(key, n, SlotSpace::from_transient(transient)),
            P_PRIMARY,
        ),
        Node::Keccak(words, tail) => {
            let mut parts: Vec<String> = Vec::new();
            for (i, w) in words.iter().enumerate() {
                if tail > 0 && i == words.len() - 1 {
                    parts.push(format!("bytes{}({})", tail, fmt_expr(*w, n)));
                } else {
                    parts.push(fmt_expr(*w, n));
                }
            }
            (
                format!("keccak256(abi.encodePacked({}))", parts.join(", ")),
                P_PRIMARY,
            )
        }
        Node::KeccakMem(off, len, _) => (
            format!(
                "keccak256(mem[{}:{}])",
                fmt_expr(off, n),
                fmt_prec(expr::op2(op::ADD, off, len), 0, n)
            ),
            P_PRIMARY,
        ),
        Node::CallResult(seq) => (format!("success_{}", n.seq(seq)), P_PRIMARY),
        Node::CreateResult(seq) => (format!("deployed_{}", n.seq(seq)), P_PRIMARY),
        Node::ReturnData(seq, off) => (
            format!("returndata_{}[{}]", n.seq(seq), fmt_expr(off, n)),
            P_PRIMARY,
        ),
        Node::CopiedWord(kind, src, _) => (
            format!("{}[{}]", copy_source(kind), fmt_expr(src, n)),
            P_PRIMARY,
        ),
        Node::IntRet(seq, j) => (format!("ret_{}_{}", n.seq(seq), j), P_PRIMARY),
        Node::Op(o, v) => fmt_op(o, &v, n),
    }
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
                                fmt_prec(iv[0], P_CMP + 1, n),
                                fmt_prec(iv[1], P_CMP + 1, n)
                            ),
                            P_CMP,
                        )
                    }
                    op::GT => {
                        return (
                            format!(
                                "{} <= {}",
                                fmt_prec(iv[0], P_CMP + 1, n),
                                fmt_prec(iv[1], P_CMP + 1, n)
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
                    return (format!("{} != 0", fmt_prec(iv[0], P_EQ + 1, n)), P_EQ);
                }
                return (fmt_prec(iv[0], P_PRIMARY, n), P_PRIMARY);
            }
            if is_bool(a, n) {
                (format!("!{}", fmt_prec(a, P_UNARY, n)), P_UNARY)
            } else {
                (format!("{} == 0", fmt_prec(a, P_EQ + 1, n)), P_EQ)
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
                fmt_prec(v[0], P_ADD, n),
                fmt_prec(v[1], P_ADD + 1, n)
            ),
            P_ADD,
        ),
        (op::SUB, 2) => (
            format!(
                "{} - {}",
                fmt_prec(v[0], P_ADD, n),
                fmt_prec(v[1], P_ADD + 1, n)
            ),
            P_ADD,
        ),
        (op::MUL, 2) => (
            format!(
                "{} * {}",
                fmt_prec(v[0], P_MUL, n),
                fmt_prec(v[1], P_MUL + 1, n)
            ),
            P_MUL,
        ),
        (op::DIV, 2) => (
            format!(
                "{} / {}",
                fmt_prec(v[0], P_MUL, n),
                fmt_prec(v[1], P_MUL + 1, n)
            ),
            P_MUL,
        ),
        (op::MOD, 2) => (
            format!(
                "{} % {}",
                fmt_prec(v[0], P_MUL, n),
                fmt_prec(v[1], P_MUL + 1, n)
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
                fmt_prec(v[0], P_EXP + 1, n),
                fmt_prec(v[1], P_EXP, n)
            ),
            P_EXP,
        ),
        (op::LT, 2) => (
            format!(
                "{} < {}",
                fmt_prec(v[0], P_CMP + 1, n),
                fmt_prec(v[1], P_CMP + 1, n)
            ),
            P_CMP,
        ),
        (op::GT, 2) => (
            format!(
                "{} > {}",
                fmt_prec(v[0], P_CMP + 1, n),
                fmt_prec(v[1], P_CMP + 1, n)
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
        (op::AND, 2) if is_bool(v[0], n) && is_bool(v[1], n) => (
            format!(
                "{} && {}",
                fmt_prec(v[0], P_AND, n),
                fmt_prec(v[1], P_AND + 1, n)
            ),
            P_AND,
        ),
        (op::OR, 2) if is_bool(v[0], n) && is_bool(v[1], n) => (
            format!(
                "{} || {}",
                fmt_prec(v[0], P_OR, n),
                fmt_prec(v[1], P_OR + 1, n)
            ),
            P_OR,
        ),
        (op::AND, 2) => {
            if is_selector_expr(expr::intern(Node::Op(op::AND, v.to_vec()))) {
                return ("msg.sig".into(), P_PRIMARY);
            }
            if let Some(m) = expr::as_const(v[1]) {
                if m.is_low_mask() {
                    let bits = m.bits();
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
            let sel = c.low_u64() as u32;
            let s = c.to_hex_padded(4).to_string();
            return match sigs::function(sel) {
                Some(sig) => format!("{} /* {} */", s, sig),
                None => s,
            };
        }
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
            if let Some(sig) = sigs::error(sel) {
                let args: Vec<String> = (0..nargs)
                    .map(|i| fmt_expr(shifted_word_len(words, i, lenu), n))
                    .collect();
                return format!("{}({})", sigs::name_of(&sig), args.join(", "));
            }
            let args: Vec<String> = (0..nargs)
                .map(|i| fmt_expr(shifted_word_len(words, i, lenu), n))
                .collect();
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

fn panic_name(code: u64) -> String {
    match code {
        0x00 => "generic".into(),
        0x01 => "assert failed".into(),
        0x11 => "arithmetic overflow".into(),
        0x12 => "division by zero".into(),
        0x21 => "invalid enum value".into(),
        0x22 => "invalid storage byte array".into(),
        0x31 => "pop on empty array".into(),
        0x32 => "array index out of bounds".into(),
        0x41 => "memory allocation too large".into(),
        0x51 => "uninitialized function pointer".into(),
        _ => format!("{:#x}", code),
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
        let w = expr::as_const(shifted_word_len(words, i, payload_len))?;
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

pub fn escape(s: &str) -> String {
    let mut out = String::new();
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 || c == '\u{fffd}' => {
                out.push_str(&format!("\\x{:02x}", c as u32 & 0xff))
            }
            c => out.push(c),
        }
    }
    out
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

fn fmt_call_head(head: &[ExprId], n: &Names) -> (Option<String>, Vec<String>) {
    let Some(sel) = head.first().and_then(|w| leading_selector(*w, None)) else {
        return (None, vec![]);
    };
    let name = match sigs::function(sel) {
        Some(sig) => sigs::name_of(&sig).to_string(),
        None => format!("func_{sel:08x}"),
    };
    let args = (0..head.len().saturating_sub(1))
        .map(|i| fmt_expr(shifted_word_len(head, i, None), n))
        .collect();
    (Some(name), args)
}

pub fn fmt_stmt(s: &Stmt, n: &Names) -> String {
    match s {
        Stmt::Assign { var, value } => format!("{} = {};", fmt_expr(*var, n), fmt_expr(*value, n)),
        Stmt::MStore {
            off, val, width, ..
        } => {
            if *width == 1 {
                format!("mem8[{}] = {};", fmt_mem_off(*off, n), fmt_expr(*val, n))
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
                if let Some((k, off, bits, value)) = packed_write(*key, *val) {
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
            let data_args: Vec<String> = match data {
                Some(words) => words.iter().map(|w| fmt_expr(*w, n)).collect(),
                None if expr::as_const(*len) != Some(U256::ZERO) => vec![format!(
                    "mem[{}:{}]",
                    fmt_expr(*off, n),
                    fmt_expr(expr::op2(op::ADD, *off, *len), n)
                )],
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
            let gas_is_all = matches!(expr::node(*gas), Node::Env(op::GAS, _))
                || matches!(expr::node(*gas), Node::Op(op::SUB, v) if matches!(expr::node(v[0]), Node::Env(op::GAS, _)));
            if !gas_is_all {
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
            let partial = input.is_none() && !n.payload_overrides.borrow().contains_key(in_off);
            let (fname, mut args) = match input {
                Some(words) => fmt_call_input(words, expr::as_const(*in_len), n),
                None if partial => fmt_call_head(input_head, n),
                None => (None, vec![]),
            };
            if partial && fname.is_some() {
                args.push("...".to_string());
            }
            let payload = match (&fname, input) {
                (Some(f), _) => format!(
                    "abi.encodeWithSelector({}.selector, {})",
                    f,
                    args.join(", ")
                )
                .replace(", )", ")"),
                (None, Some(_)) if args.is_empty() => "\"\"".into(),
                (None, Some(_)) => format!("abi.encode({})", args.join(", ")),
                (None, None) => {
                    if expr::as_const(*in_len) == Some(U256::ZERO) {
                        "\"\"".into()
                    } else if let Some(text) = n.payload_overrides.borrow().get(in_off) {
                        text.clone()
                    } else if let Some(pointer) = bytes_value(*in_off, *in_len) {
                        format!("bytes({})", fmt_mem_off(pointer, n))
                    } else {
                        format!(
                            "mem[{}:{}]",
                            fmt_expr(*in_off, n),
                            fmt_expr(expr::op2(op::ADD, *in_off, *in_len), n)
                        )
                    }
                }
            };
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
                _ => format!(
                    "mem[{}:{}]",
                    fmt_expr(*off, n),
                    fmt_expr(expr::op2(op::ADD, *off, *len), n)
                ),
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
        } => {
            let src_s = match addr {
                Some(a) => format!(
                    "{}.code[{}:+{}]",
                    fmt_prec(*a, P_PRIMARY, n),
                    fmt_expr(*src, n),
                    fmt_expr(*len, n)
                ),
                None => format!(
                    "{}[{}:+{}]",
                    copy_source(*kind),
                    fmt_expr(*src, n),
                    fmt_expr(*len, n)
                ),
            };
            format!(
                "mem[{}:+{}] = {};",
                fmt_expr(*dest, n),
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
            let a: Vec<String> = args.iter().map(|x| fmt_expr(*x, n)).collect();
            let call = format!("{}({})", n.callee_name(*callee), a.join(", "));
            match results.len() {
                0 => format!("{};", call),
                1 => format!("{} = {};", fmt_expr(results[0], n), call),
                _ => format!(
                    "({}) = {};",
                    results
                        .iter()
                        .map(|r| fmt_expr(*r, n))
                        .collect::<Vec<_>>()
                        .join(", "),
                    call
                ),
            }
        }
        Stmt::Drop(e) => format!("// ignored: {}", fmt_expr(*e, n)),
        Stmt::Require {
            cond,
            data,
            invalid,
        } => {
            if is_abi_validator(*cond) {
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
                    if n.hide_checked
                        && (p == "Panic(arithmetic overflow)"
                            || p == "Panic(division by zero)"
                            || p == "Panic(memory allocation too large)")
                    {
                        return String::new();
                    }
                    if p == "Panic(assert failed)" {
                        format!("assert({});", c)
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

pub fn fmt_term_halt(t: &Term, n: &Names) -> Option<String> {
    Some(match t {
        Term::Return { off, len, data } => match data {
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
                    format!(
                        "return mem[{}:{}];",
                        fmt_expr(*off, n),
                        fmt_expr(expr::op2(op::ADD, *off, *len), n)
                    )
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
                    if p.starts_with('"') {
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
                    format!(
                        "revert(mem[{}:{}]);",
                        fmt_expr(*off, n),
                        fmt_expr(expr::op2(op::ADD, *off, *len), n)
                    )
                }
            }
        },
        Term::Stop => "return;".into(),
        Term::ReturnDyn { ptr } => format!("return {};", fmt_expr(*ptr, n)),
        Term::Invalid => "assert(false); // INVALID".into(),
        Term::SelfDestruct(a) => format!("selfdestruct({});", fmt_expr(*a, n)),
        Term::InternalReturn(vals) => {
            if vals.is_empty() {
                "return;".into()
            } else {
                let k = vals.len();
                format!(
                    "return ({});",
                    vals.iter()
                        .enumerate()
                        .map(|(j, v)| {
                            let is_bool_pos = n.bool_returns.get(k - 1 - j).copied() == Some(true);
                            match expr::as_const(*v) {
                                Some(c) if is_bool_pos && c.is_zero() => "false".to_string(),
                                Some(c) if is_bool_pos && c == U256::ONE => "true".to_string(),
                                _ => fmt_expr(*v, n),
                            }
                        })
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

pub fn fmt_flat(l: &Lifted, n: &Names, indent: &str) -> String {
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
        if !falls {
            needs_label.insert(nid);
        }
    }
    for (idx, &nid) in order.iter().enumerate() {
        let nd = &l.nodes[nid];
        if needs_label.contains(&nid) {
            out.push_str(&format!("{}L{:x}:\n", indent, nd.pc));
        }
        n.end_block();
        let mut dead = dead_memory_stores(&nd.stmts);
        dead.extend(free_pointer_updates(&nd.stmts, n));
        for (i, s) in nd.stmts.iter().enumerate() {
            if dead.contains(&i) {
                continue;
            }
            let txt = fmt_stmt(s, n);
            for (name, def) in n.take_temps() {
                out.push_str(&format!("{}    uint256 {} = {};\n", indent, name, def));
            }
            out.push_str(&format!("{}    {}\n", indent, txt));
        }
        let goto = |to: usize| -> String {
            let mut s = String::new();
            if let Some(assigns) = l.edge_assigns.get(&(nid, to)) {
                for (var, val) in assigns {
                    s.push_str(&format!("{} = {}; ", fmt_expr(*var, n), fmt_expr(*val, n)));
                }
            }
            s.push_str(&format!("goto L{:x};", l.nodes[to].pc));
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
    out
}

#[cfg(test)]
mod tests {
    use super::strip_outer_parens;

    #[test]
    fn outer_parens_are_stripped_only_when_they_wrap_everything() {
        assert_eq!(strip_outer_parens("(a, b)"), "a, b");
        assert_eq!(strip_outer_parens("(uint8(x))"), "uint8(x)");
        assert_eq!(strip_outer_parens("uint8(x)"), "uint8(x)");
        assert_eq!(strip_outer_parens("(a) + (b)"), "(a) + (b)");
        assert_eq!(strip_outer_parens(""), "");
    }
}
