//! Rendering expressions and statements as pseudo-Solidity.

use crate::expr::{self, ExprId, Node};
use crate::keccak;
use crate::lift::{Lifted, Stmt, Term};
use crate::opcode as op;
use crate::sigs;
use crate::u256::U256;
use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::sync::OnceLock;

/// How many small slots the hashed-slot table covers.
const HASHED_SLOTS: u64 = 4096;

/// Offsets around a precomputed hash that still count as that array (`keccak256(s) - 1` for
/// `arr[arr.length - 1]`, `keccak256(s) + 2` for a struct field).
const HASH_OFFSET_RANGE: i64 = 16;

/// The slot `s` whose dynamic-array data lives at `keccak256(s)`, and the element offset `k`,
/// for a constant `c = keccak256(s) + k` with small `s` and `|k| <= 16`. Compilers precompute
/// that hash for state variables (and fold small offsets into it), so the constant shows up in
/// the code as is.
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
                // The exact hash wins over a neighbour's offset.
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

/// `idx + k` / `idx - k` for an element offset folded into a hash constant.
fn offset_index(idx: &str, k: i64) -> String {
    match k {
        0 => idx.to_string(),
        k if k > 0 => format!("{} + {}", idx, k),
        k => format!("{} - {}", idx, -k),
    }
}

/// An index into a storage array rather than a hashed slot: not a constant, not a
/// `keccak256(...)` and not `keccak256(...) + k` (a mapping value used as the index is fine).
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

/// `slot_in_fixed_array`: a key `x + c` with a small constant `c` addresses element `x + (c - b)`
/// of the fixed-size array whose first slot `b` is the nearest known base at or below `c`.
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

/// How a compiler lays out mapping slots: `keccak(key . slot)` (Solidity) or `keccak(slot . key)`
/// (Vyper).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum MappingLayout {
    /// Solidity: the key precedes the slot in the hashed preimage.
    #[default]
    Solidity,
    /// Vyper: the slot precedes the key in the hashed preimage.
    Vyper,
}

impl MappingLayout {
    /// The layout used by the compiler a [`Contract::language`](crate::decompile::Contract) names.
    pub fn of_language(language: &str) -> MappingLayout {
        if language.starts_with("vyper") {
            MappingLayout::Vyper
        } else {
            MappingLayout::Solidity
        }
    }
}

/// Which storage a slot expression addresses.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SlotSpace {
    /// Persistent storage (`SLOAD` / `SSTORE`), printed as `stor…`.
    Persistent,
    /// Transient storage (`TLOAD` / `TSTORE`, EIP-1153), printed as `tstor…`.
    Transient,
}

impl SlotSpace {
    /// The space a statement's `transient` flag selects.
    pub fn from_transient(transient: bool) -> SlotSpace {
        if transient {
            SlotSpace::Transient
        } else {
            SlotSpace::Persistent
        }
    }
}

/// What an ABI-encoded payload is for; decides how a selector-led payload is rendered.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PayloadKind {
    /// Data handed to `RETURN`.
    Return,
    /// Data handed to `REVERT`: `Error(string)`, `Panic(uint256)` and custom errors are decoded.
    Revert,
}

/// Naming context for one function.
#[derive(Debug, Default)]
pub struct Names {
    /// calldata word index -> parameter name
    pub params: HashMap<u32, String>,
    /// Expressions printed under a fixed name (e.g. the pointer returned by a storage-string
    /// loader prints as the storage variable).
    pub aliases: HashMap<ExprId, String>,
    /// Packed storage fields: (slot, byte offset, bits) -> name.
    pub fields: HashMap<(U256, u32, u32), String>,
    /// internal-unit argument index -> name
    pub args: HashMap<u32, String>,
    /// storage slot (constant) -> name
    pub storage: HashMap<U256, String>,
    /// First slots of fixed-size storage arrays (`uint[256] owners` occupies `base..base+256`).
    pub array_bases: BTreeSet<U256>,
    /// Loads that read a slot's value from before a store printed earlier on the path: printed
    /// under the temporary that saved that value. Filled by the structurer as it prints.
    pub stale: RefCell<HashMap<ExprId, String>>,
    /// The value just stored to a slot, printed as the slot while no later store intervenes:
    /// the compiler forwards the stored value instead of reloading it. Filled by the structurer.
    pub forwarded: RefCell<HashMap<ExprId, String>>,
    /// Number of temporaries handed out so far (names stay unique across blocks).
    pub temp_seq: RefCell<u32>,
    /// Sequence numbers renamed to small indices.
    pub seqs: RefCell<HashMap<u32, u32>>,
    /// Phi variables renamed to small indices (`v1`, `v2`, …) in order of first use.
    pub vars: RefCell<HashMap<u32, u32>>,
    /// Mapping slot layout of the source compiler.
    pub layout: MappingLayout,
    /// solc >= 0.8: the compiler's own overflow / division-by-zero panics are not printed.
    pub hide_checked: bool,
    /// Large shared sub-expressions are hoisted into temporaries: pending definitions.
    pub temps: RefCell<Vec<(String, String)>>,
    /// Expression -> temporary name, for expressions already hoisted.
    pub temp_of: RefCell<HashMap<ExprId, String>>,
    /// Entry pcs of internal functions without side effects (view/pure): a call to one does
    /// not move ether, whatever the lifter's conservative storage model assumed.
    pub pure_callees: HashSet<usize>,
    /// Expressions known to be booleans beyond their shape: results of helpers that return
    /// `bool`.
    pub bools: HashSet<ExprId>,
    /// Packed storage fields of type `bool`: (slot, byte offset, bits).
    pub bool_fields: HashSet<(U256, u32, u32)>,
    /// Which of the current function's return positions (declaration order) are `bool`.
    pub bool_returns: Vec<bool>,
    /// Rendered text and precedence of the expressions printed so far.
    pub memo: RefCell<HashMap<ExprId, (String, u8)>>,
}

/// Rendered expressions longer than this become temporaries (keeps output linear in size).
const TEMP_THRESHOLD: usize = 160;

impl Names {
    /// Temporaries created while rendering the last statement(s); the caller prints them first.
    pub fn take_temps(&self) -> Vec<(String, String)> {
        std::mem::take(&mut *self.temps.borrow_mut())
    }

    /// Forget the temporaries of the block just printed: a temporary is declared where it is
    /// first used, so a later block must not refer to one declared inside another branch.
    pub fn end_block(&self) {
        self.temp_of.borrow_mut().clear();
        self.memo.borrow_mut().clear();
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

/// A constant in its most readable form: decimal, `type(uintN).max`, `NeK`, `2**K`, an address,
/// or hex.
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
    // n * 10^k with small n
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

/// Is `e` the function selector, `calldataload(0) >> 224` in one of the shapes solc emits?
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

/// Extract the selector constant from a comparison `sel == C` / `C == sel`.
pub fn selector_compare(e: ExprId) -> Option<u32> {
    if let Node::Op(op::EQ, v) = expr::node(e) {
        return selector_operands(&v);
    }
    None
}

/// `sel XOR C` / `sel - C` / `C - sel`: zero exactly when the selector matches.
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

/// Index of the ABI word at a constant calldata offset `4 + 32*i`; `None` for anything else.
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

/// Render an expression; sub-expressions longer than the threshold become temporaries.
pub fn fmt_expr(e: ExprId, n: &Names) -> String {
    fmt_prec(e, 0, n)
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

/// An event emission from its topics and already-printed data arguments: `emit Name(...)` when
/// topic0 is a known signature, a placeholder name for an unknown one, `logN(...)` otherwise.
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

/// Is `e` the sum `base + k`?
pub fn is_add_const(e: ExprId, base: ExprId, k: u64) -> bool {
    match expr::node(e) {
        Node::Op(op::ADD, v) => {
            (v[0] == base && expr::as_const(v[1]) == Some(U256::from_u64(k)))
                || (v[1] == base && expr::as_const(v[0]) == Some(U256::from_u64(k)))
        }
        _ => false,
    }
}

/// Every expression a statement mentions.
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

/// The constant byte range a statement writes to memory, when it is a plain store.
fn written_range(s: &Stmt) -> Option<(u64, u64)> {
    match s {
        Stmt::MStore { off, width, .. } => {
            let o = expr::as_const(*off)?.as_usize()? as u64;
            Some((o, o + *width as u64))
        }
        Stmt::Copy { dest, len, .. } => {
            let d = expr::as_const(*dest)?.as_usize()? as u64;
            let l = expr::as_const(*len)?.as_usize()? as u64;
            Some((d, d + l))
        }
        _ => None,
    }
}

/// Could the statement read memory? Anything but a store whose operands are memory-free.
fn reads_memory(s: &Stmt) -> bool {
    match s {
        Stmt::MStore { .. } | Stmt::SStore { .. } | Stmt::Assign { .. } | Stmt::Drop(_) => {
            stmt_exprs(s)
                .iter()
                .any(|e| expr::contains(*e, &|n| matches!(n, Node::MLoad(..))))
        }
        Stmt::Copy { kind, .. } => *kind == op::MCOPY,
        _ => true,
    }
}

/// Statements of one block that store to memory and are overwritten by a later store of the
/// same block before anything could read them, plus `mem[x] = mem[x]` no-ops. The lifted IR is
/// left as is (the oracle checks it); only the printout drops them.
pub fn dead_memory_stores(stmts: &[Stmt]) -> std::collections::HashSet<usize> {
    let mut dead = std::collections::HashSet::new();
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
        let Some((lo, hi)) = written_range(s) else {
            continue;
        };
        for later in &stmts[i + 1..] {
            if let Some((l2, h2)) = written_range(later) {
                if l2 <= lo && h2 >= hi {
                    dead.insert(i);
                    break;
                }
            }
            if reads_memory(later) {
                break;
            }
        }
    }
    dead
}

/// solc's ABI decoder validators on a calldata word: `x == address(x)` (the word is a clean
/// address) and `x == bool(x)`. The parameter type already says so.
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

/// A `require` the printer leaves out: an ABI decoder validator (the parameter type says it),
/// or, on solc >= 0.8, the compiler's own overflow / division-by-zero panic.
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
        Some(c) if c == U256::from_u64(PANIC_OVERFLOW) || c == U256::from_u64(PANIC_DIV_BY_ZERO)
    )
}

/// Selector of `Panic(uint256)`.
const SEL_PANIC: u32 = 0x4e487b71;
/// `Panic` code for arithmetic overflow.
const PANIC_OVERFLOW: u64 = 0x11;
/// `Panic` code for division by zero.
const PANIC_DIV_BY_ZERO: u64 = 0x12;

/// Is `e` boolean-valued: by its shape, as a helper's `bool` result, or as a `bool` field?
pub fn is_bool(e: ExprId, n: &Names) -> bool {
    expr::is_boolean(e)
        || n.bools.contains(&e)
        || packed_read(e).is_some_and(|(k, off, bits)| n.bool_fields.contains(&(k, off, bits)))
}

/// A condition as a boolean: `x` when boolean-valued, `x != 0` otherwise.
pub fn fmt_cond(cond: ExprId, n: &Names) -> String {
    if is_bool(cond, n) {
        fmt_expr(cond, n)
    } else {
        format!("{} != 0", fmt_prec(cond, P_EQ + 1, n))
    }
}

/// Name of an event whose signature is unknown: `Event_<first four bytes of topic0>`.
pub fn event_placeholder_name(topic0: U256) -> String {
    let b = topic0.to_be_bytes();
    format!("Event_{:08x}", u32::from_be_bytes([b[0], b[1], b[2], b[3]]))
}

/// `slt(sub(calldatasize, c), k)` and friends: solc's ABI-size checks are signed compares on a
/// value that cannot be negative. Printed as the unsigned comparison with the constants folded.
fn size_compare(o: u8, a: ExprId, b: ExprId, n: &Names) -> Option<String> {
    let k = expr::as_const(b)?;
    let (base, c) = expr::split_offset(a);
    let base = base?;
    let name = fmt_expr(base, n);
    if name != "msg.data.length" && name != "returndatasize()" {
        return None;
    }
    // a = base + c (c may be a wrapped negative constant): base <op> k - c
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

/// Memory offsets print in hex (0x40 is the free memory pointer, 0x00..0x3f scratch).
pub fn fmt_mem_off(off: ExprId, n: &Names) -> String {
    match expr::as_const(off) {
        Some(c) if c.bits() <= 64 => c.to_hex(),
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

/// Storage location rendering: `stor_5`, `stor_3[key]`, `stor_7[k1][k2]`, `stor_9[i]`.
/// A read of a packed storage field: `(slot, byte offset, bits)` for `slot & mask`,
/// `(slot >> 8k) & mask`, `(slot / 2^8k) & mask` and the top field `slot >> 8k`.
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
        // signextend(n, slot >> 8k): a signed field of 8(n+1) bits.
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

/// A write of a packed storage field: `slot = slot & ~(mask << 8k) | (value << 8k)` gives
/// `(slot, byte offset, bits, value)`.
pub fn packed_write(key: ExprId, val: ExprId) -> Option<(U256, u32, u32, ExprId)> {
    let k = expr::as_const(key)?;
    // `slot = slot & ~mask`: the field under the mask is set to zero.
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
        // Undo the placement: value << s, value * 2^s, or a constant.
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

/// Render a storage key: a named variable or `stor_N` for a constant, `name[key]` for mapping and
/// array elements, `name.fieldN` for struct fields.
pub fn fmt_slot(e: ExprId, n: &Names, space: SlotSpace) -> String {
    let prefix = match space {
        SlotSpace::Persistent => "stor",
        SlotSpace::Transient => "tstor",
    };
    if let Some(c) = expr::as_const(e) {
        if let Some(name) = n.storage.get(&c) {
            return name.clone();
        }
        if let Some((s, k)) = hashed_slot(c) {
            return format!("{}[{}]", fmt_slot(expr::konst(s), n, space), k.max(0));
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
            format!("{}[{}]", fmt_slot(slot, n, space), fmt_expr(key, n))
        }
        Node::Keccak(words, 0) if words.len() == 1 => {
            format!("{}[0]", fmt_slot(words[0], n, space))
        }
        Node::Op(op::ADD, v) => {
            // array element: keccak(slot) + i, or (base) + i for struct fields in mappings
            let (base, idx) = (v[0], v[1]);
            // A precomputed `keccak256(slot)` on either side: element `idx` of that array.
            for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
                if let Some((s, k)) = expr::as_const(a).and_then(hashed_slot) {
                    return format!(
                        "{}[{}]",
                        fmt_slot(expr::konst(s), n, space),
                        offset_index(&fmt_expr(b, n), k)
                    );
                }
            }
            // `index + small constant`: a fixed-size array laid out from a known base slot.
            for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
                if let (Some(c), true) = (expr::as_const(a), is_plain_index(b)) {
                    if let Some((root, off)) = fixed_array_base(c, &n.array_bases) {
                        let idx_s = if off.is_zero() {
                            fmt_expr(b, n)
                        } else {
                            format!("{} + {}", fmt_expr(b, n), off.to_decimal())
                        };
                        return format!("{}[{}]", fmt_slot(expr::konst(root), n, space), idx_s);
                    }
                }
            }
            match expr::node(base) {
                Node::Keccak(words, 0) if words.len() == 1 => {
                    format!("{}[{}]", fmt_slot(words[0], n, space), fmt_expr(idx, n))
                }
                Node::Keccak(words, 0) if words.len() == 2 => {
                    format!("{}.field{}", fmt_slot(base, n, space), fmt_expr(idx, n))
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
        Node::MLoad(off, _) => (format!("mem[{}]", fmt_mem_off(off, n)), P_PRIMARY),
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
            // Negated comparisons
            if let Node::Op(io, iv) = expr::node(a) {
                match io {
                    op::EQ => {
                        if let Some((b, truth)) = bool_against_const(iv[0], iv[1], n) {
                            // `!(b == 1)` is `!b`; `!(b == 0)` is `b`.
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
                // `!!b` of a boolean is `b`.
                return (fmt_prec(iv[0], P_PRIMARY, n), P_PRIMARY);
            }
            if is_bool(a, n) {
                (format!("!{}", fmt_prec(a, P_UNARY, n)), P_UNARY)
            } else {
                (format!("{} == 0", fmt_prec(a, P_EQ + 1, n)), P_EQ)
            }
        }
        (op::NOT, 1) => (format!("~{}", fmt_prec(v[0], P_UNARY, n)), P_UNARY),
        (op::BALANCE, 1) => (
            format!("{}.balance", fmt_prec(v[0], P_PRIMARY, n)),
            P_PRIMARY,
        ),
        (op::EXTCODESIZE, 1) => (
            format!("{}.code.length", fmt_prec(v[0], P_PRIMARY, n)),
            P_PRIMARY,
        ),
        (op::EXTCODEHASH, 1) => (
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

/// `b == 1` / `b == 0` with `b` boolean-valued: the boolean and whether the comparison holds
/// when it is true.
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

/// Right-hand side of a comparison, annotating selectors.
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

// ------------------------------------------------------------------------------------------
// Statements
// ------------------------------------------------------------------------------------------

/// Decode a revert/return payload into a readable form.
/// The 4-byte selector at the start of a payload word, if the word is `sel << 224 | rest` where
/// `rest` is anything with its top 32 bits clear (constant, or an OR with such a constant), or a
/// short right-aligned word.
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

/// Render ABI-encoded payload words: a revert reason string, `Panic(…)`, a custom error with its
/// arguments, a returned string, or the words joined with commas.
pub fn fmt_payload(words: &[ExprId], len: Option<U256>, n: &Names, kind: PayloadKind) -> String {
    if words.is_empty() {
        return String::new();
    }
    // Error(string) / Panic / custom error: first word's top 4 bytes
    let lenu = len.and_then(|l| l.as_usize());
    if let Some(sel) = leading_selector(words[0], lenu) {
        let top4_only = lenu.map_or(
            expr::as_const(words[0]).is_none_or(|c| (c & expr::mask_bits(224)).is_zero()),
            |l| l >= 4 && (l - 4) % 32 == 0,
        );
        if kind == PayloadKind::Revert && top4_only {
            if sel == 0x08c379a0 {
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
    // A single dynamic value `(32, len, data…)` returned in place: show the text when it is one.
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

/// ABI word `i` of a payload that starts with a 4-byte selector: bytes `4 + 32*i .. 36 + 32*i`,
/// which straddle memory words `i` and `i + 1`. The last word of a payload whose length is not a
/// multiple of 32 holds its `len % 32` bytes right-aligned and is left-aligned here first.
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
    // (hi << 32) | (lo >> 224)
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

/// Decode `Error(string)` payload words (selector-shifted) into the string.
pub fn decode_string_payload(words: &[ExprId], payload_len: Option<usize>) -> Option<String> {
    // ABI words after the selector: [offset (0x20), length, data...]
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

/// Decode a string from plain (unshifted) words: [len, data...].
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

/// Escape a string for a double-quoted Solidity literal.
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

/// Render the input of an external call: `abi.encodeWithSelector(...)` decoded when possible.
pub fn fmt_call_input(
    words: &[ExprId],
    in_len: Option<U256>,
    n: &Names,
) -> (Option<String>, Vec<String>) {
    // Returns (function name if known, args)
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

/// Render one statement as a line of pseudo-Solidity, without indentation.
pub fn fmt_stmt(s: &Stmt, n: &Names) -> String {
    match s {
        Stmt::Assign { var, value } => format!("{} = {};", fmt_expr(*var, n), fmt_expr(*value, n)),
        Stmt::MStore { off, val, width } => {
            if *width == 1 {
                format!("mem8[{}] = {};", fmt_mem_off(*off, n), fmt_expr(*val, n))
            } else {
                format!("mem[{}] = {};", fmt_mem_off(*off, n), fmt_expr(*val, n))
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
            result,
            ..
        } => {
            let target = fmt_prec(*addr, P_PRIMARY, n);
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
            let (fname, args) = match input {
                Some(words) => fmt_call_input(words, expr::as_const(*in_len), n),
                None => (None, vec![]),
            };
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
                    } else {
                        format!(
                            "mem[{}:{}]",
                            fmt_expr(*in_off, n),
                            fmt_expr(expr::op2(op::ADD, *in_off, *in_len), n)
                        )
                    }
                }
            };
            // Known target function: show as a typed call.
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
            let call = format!("func_{:#x}({})", callee, a.join(", "));
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
                    // Selector payloads (Error(string), Panic(code), custom errors) are 4 + 32n bytes.
                    let len = leading_selector(words[0], None)
                        .map(|_| U256::from_u64(4 + 32 * (words.len() as u64 - 1)));
                    let p = fmt_payload(words, len, n, PayloadKind::Revert);
                    if n.hide_checked
                        && (p == "Panic(arithmetic overflow)" || p == "Panic(division by zero)")
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

/// Remove one pair of enclosing parentheses when they wrap the whole string.
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

/// Render a terminator that ends the function (`return`, `revert`, `selfdestruct`, …) or has no
/// structured form (an unresolved `jump`); `None` for branches and jumps within the function.
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
                // Values are deepest first; `bool_returns` is in declaration order.
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

/// Unstructured rendering: labels and gotos. Used as the fallback and for debugging.
pub fn fmt_flat(l: &Lifted, n: &Names, indent: &str) -> String {
    let mut out = String::new();
    let reach = crate::lift::reachable(l);
    let mut order: Vec<usize> = Vec::new();
    // Reverse post-order from entry.
    let mut seen = std::collections::HashSet::new();
    fn dfs(
        l: &Lifted,
        x: usize,
        seen: &mut std::collections::HashSet<usize>,
        order: &mut Vec<usize>,
    ) {
        if !seen.insert(x) {
            return;
        }
        for s in &l.nodes[x].succs {
            dfs(l, *s, seen, order);
        }
        order.push(x);
    }
    dfs(l, l.entry, &mut seen, &mut order);
    order.reverse();
    // A node needs a label unless its only predecessor is the node printed just before it and
    // that predecessor falls through with a plain jump.
    let mut needs_label: std::collections::HashSet<usize> = std::collections::HashSet::new();
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
        let dead = dead_memory_stores(&nd.stmts);
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
