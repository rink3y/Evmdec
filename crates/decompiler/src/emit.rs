//! Rendering expressions and statements as pseudo-Solidity.

use crate::expr::{self, ExprId, Node};
use crate::lift::{Lifted, Stmt, Term};
use crate::opcode as op;
use crate::sigs;
use crate::u256::U256;
use std::cell::RefCell;
use std::collections::HashMap;

/// Naming context for one function.
#[derive(Default)]
pub struct Names {
    /// calldata word index -> parameter name
    pub params: HashMap<u32, String>,
    /// internal-unit argument index -> name
    pub args: HashMap<u32, String>,
    /// storage slot (constant) -> name
    pub storage: HashMap<U256, String>,
    /// Sequence numbers renamed to small indices.
    pub seqs: RefCell<HashMap<u32, u32>>,
    pub vars: RefCell<HashMap<u32, u32>>,
    /// Vyper-style mapping layout (slot first, then key).
    pub vyper: bool,
    /// Large shared sub-expressions are hoisted into temporaries: pending definitions.
    pub temps: RefCell<Vec<(String, String)>>,
    pub temp_of: RefCell<HashMap<ExprId, String>>,
    pub memo: RefCell<HashMap<ExprId, (String, u8)>>,
}

/// Rendered expressions longer than this become temporaries (keeps output linear in size).
const TEMP_THRESHOLD: usize = 160;

impl Names {
    /// Temporaries created while rendering the last statement(s); the caller prints them first.
    pub fn take_temps(&self) -> Vec<(String, String)> {
        std::mem::take(&mut *self.temps.borrow_mut())
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
    // n * 10^k with small n
    let dec = c.to_decimal();
    let trimmed = dec.trim_end_matches('0');
    let zeros = dec.len() - trimmed.len();
    if zeros >= 6 && trimmed.len() <= 4 {
        return format!("{}e{}", trimmed, zeros);
    }
    let bits = c.bits();
    if c.is_low_mask() && bits % 8 == 0 && bits < 256 {
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
        format!("-{}", fmt_const(c.neg()))
    } else {
        fmt_const(c)
    }
}

pub fn is_selector_expr(e: ExprId) -> bool {
    match expr::node(e) {
        Node::Op(op::SHR, v) => expr::as_const(v[0]) == Some(U256::from_u64(224)) && matches!(expr::node(v[1]), Node::CallDataLoad(o) if expr::as_const(o) == Some(U256::ZERO)),
        Node::Op(op::AND, v) => is_selector_expr(v[0]) && expr::as_const(v[1]) == Some(U256::from_u64(0xffffffff)),
        Node::Op(op::DIV, v) => expr::as_const(v[1]) == Some(U256::ONE.shl(224)) && matches!(expr::node(v[0]), Node::CallDataLoad(o) if expr::as_const(o) == Some(U256::ZERO)),
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

fn fmt_prec(e: ExprId, outer: u8, n: &Names) -> String {
    if let Some(t) = n.temp_of.borrow().get(&e) {
        return t.clone();
    }
    if let Some((s, p)) = n.memo.borrow().get(&e) {
        return paren(s.clone(), *p, outer);
    }
    let (s, p) = fmt_inner(e, n);
    if s.len() > TEMP_THRESHOLD && !matches!(expr::node(e), Node::Const(_)) {
        let name = format!("t{}", n.temp_of.borrow().len() + 1);
        n.temps.borrow_mut().push((name.clone(), s));
        n.temp_of.borrow_mut().insert(e, name.clone());
        return name;
    }
    n.memo.borrow_mut().insert(e, (s.clone(), p));
    paren(s, p, outer)
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
pub fn fmt_slot(e: ExprId, n: &Names, transient: bool) -> String {
    let prefix = if transient { "tstor" } else { "stor" };
    if let Some(c) = expr::as_const(e) {
        if let Some(name) = n.storage.get(&c) {
            return name.clone();
        }
        return if c.bits() <= 32 { format!("{}_{}", prefix, c.to_decimal()) } else { format!("{}_{}", prefix, c.to_hex()) };
    }
    match expr::node(e) {
        Node::Keccak(words, 0) if words.len() == 2 => {
            let (key, slot) = if n.vyper || (expr::as_const(words[0]).map_or(false, |c| c.bits() <= 16) && !expr::as_const(words[1]).map_or(false, |c| c.bits() <= 16)) { (words[1], words[0]) } else { (words[0], words[1]) };
            format!("{}[{}]", fmt_slot(slot, n, transient), fmt_expr(key, n))
        }
        Node::Keccak(words, 0) if words.len() == 1 => format!("{}[0]", fmt_slot(words[0], n, transient)),
        Node::Op(op::ADD, v) => {
            // array element: keccak(slot) + i, or (base) + i for struct fields in mappings
            let (base, idx) = (v[0], v[1]);
            match expr::node(base) {
                Node::Keccak(words, 0) if words.len() == 1 => format!("{}[{}]", fmt_slot(words[0], n, transient), fmt_expr(idx, n)),
                Node::Keccak(words, 0) if words.len() == 2 => format!("{}.field{}", fmt_slot(base, n, transient), fmt_expr(idx, n)),
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
    match expr::node(e) {
        Node::Const(c) => (fmt_const(c), P_PRIMARY),
        Node::Env(o, seq) => (env_name(o, seq, n), P_PRIMARY),
        Node::Var(v) => (format!("v{}", n.var(v)), P_PRIMARY),
        Node::Arg(i) => (n.args.get(&i).cloned().unwrap_or_else(|| format!("arg{}", i)), P_PRIMARY),
        Node::Unknown(u) => (format!("unknown_{}", n.seq(u)), P_PRIMARY),
        Node::CallDataLoad(off) => {
            if let Some(i) = calldata_word_index(off) {
                return (n.params.get(&i).cloned().unwrap_or_else(|| format!("arg{}", i)), P_PRIMARY);
            }
            if expr::as_const(off) == Some(U256::ZERO) {
                return ("msg.data[0:32]".into(), P_PRIMARY);
            }
            (format!("calldata[{}]", fmt_expr(off, n)), P_PRIMARY)
        }
        Node::MLoad(off, _) => (format!("mem[{}]", fmt_mem_off(off, n)), P_PRIMARY),
        Node::SLoad(key, transient, _) => (fmt_slot(key, n, transient), P_PRIMARY),
        Node::Keccak(words, tail) => {
            let mut parts: Vec<String> = Vec::new();
            for (i, w) in words.iter().enumerate() {
                if tail > 0 && i == words.len() - 1 {
                    parts.push(format!("bytes{}({})", tail, fmt_expr(*w, n)));
                } else {
                    parts.push(fmt_expr(*w, n));
                }
            }
            (format!("keccak256(abi.encodePacked({}))", parts.join(", ")), P_PRIMARY)
        }
        Node::KeccakMem(off, len, _) => (format!("keccak256(mem[{}:{}])", fmt_expr(off, n), fmt_prec(expr::op2(op::ADD, off, len), 0, n)), P_PRIMARY),
        Node::CallResult(seq) => (format!("success_{}", n.seq(seq)), P_PRIMARY),
        Node::CreateResult(seq) => (format!("deployed_{}", n.seq(seq)), P_PRIMARY),
        Node::ReturnData(seq, off) => (format!("returndata_{}[{}]", n.seq(seq), fmt_expr(off, n)), P_PRIMARY),
        Node::CopiedWord(kind, src, _) => (format!("{}[{}]", copy_source(kind), fmt_expr(src, n)), P_PRIMARY),
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
                    op::EQ => return (format!("{} != {}", fmt_prec(iv[0], P_EQ + 1, n), fmt_eq_rhs(iv[0], iv[1], P_EQ + 1, n)), P_EQ),
                    op::LT => return (format!("{} >= {}", fmt_prec(iv[0], P_CMP + 1, n), fmt_prec(iv[1], P_CMP + 1, n)), P_CMP),
                    op::GT => return (format!("{} <= {}", fmt_prec(iv[0], P_CMP + 1, n), fmt_prec(iv[1], P_CMP + 1, n)), P_CMP),
                    op::SLT => return (format!("{} >= {}", fmt_signed(iv[0], n), fmt_signed(iv[1], n)), P_CMP),
                    op::SGT => return (format!("{} <= {}", fmt_signed(iv[0], n), fmt_signed(iv[1], n)), P_CMP),
                    _ => {}
                }
            }
            if let Node::Op(op::ISZERO, iv) = expr::node(a) {
                if !expr::is_boolean(iv[0]) {
                    return (format!("{} != 0", fmt_prec(iv[0], P_EQ + 1, n)), P_EQ);
                }
            }
            if expr::is_boolean(a) {
                (format!("!{}", fmt_prec(a, P_UNARY, n)), P_UNARY)
            } else {
                (format!("{} == 0", fmt_prec(a, P_EQ + 1, n)), P_EQ)
            }
        }
        (op::NOT, 1) => (format!("~{}", fmt_prec(v[0], P_UNARY, n)), P_UNARY),
        (op::BALANCE, 1) => (format!("{}.balance", fmt_prec(v[0], P_PRIMARY, n)), P_PRIMARY),
        (op::EXTCODESIZE, 1) => (format!("{}.code.length", fmt_prec(v[0], P_PRIMARY, n)), P_PRIMARY),
        (op::EXTCODEHASH, 1) => (format!("{}.codehash", fmt_prec(v[0], P_PRIMARY, n)), P_PRIMARY),
        (op::BLOCKHASH, 1) => (format!("blockhash({})", fmt_expr(v[0], n)), P_PRIMARY),
        (op::BLOBHASH, 1) => (format!("blobhash({})", fmt_expr(v[0], n)), P_PRIMARY),
        (op::ADD, 2) => (format!("{} + {}", fmt_prec(v[0], P_ADD, n), fmt_prec(v[1], P_ADD + 1, n)), P_ADD),
        (op::SUB, 2) => (format!("{} - {}", fmt_prec(v[0], P_ADD, n), fmt_prec(v[1], P_ADD + 1, n)), P_ADD),
        (op::MUL, 2) => (format!("{} * {}", fmt_prec(v[0], P_MUL, n), fmt_prec(v[1], P_MUL + 1, n)), P_MUL),
        (op::DIV, 2) => (format!("{} / {}", fmt_prec(v[0], P_MUL, n), fmt_prec(v[1], P_MUL + 1, n)), P_MUL),
        (op::MOD, 2) => (format!("{} % {}", fmt_prec(v[0], P_MUL, n), fmt_prec(v[1], P_MUL + 1, n)), P_MUL),
        (op::SDIV, 2) => (format!("{} / {}", fmt_signed(v[0], n), fmt_signed(v[1], n)), P_MUL),
        (op::SMOD, 2) => (format!("{} % {}", fmt_signed(v[0], n), fmt_signed(v[1], n)), P_MUL),
        (op::EXP, 2) => (format!("{} ** {}", fmt_prec(v[0], P_EXP + 1, n), fmt_prec(v[1], P_EXP, n)), P_EXP),
        (op::LT, 2) => (format!("{} < {}", fmt_prec(v[0], P_CMP + 1, n), fmt_prec(v[1], P_CMP + 1, n)), P_CMP),
        (op::GT, 2) => (format!("{} > {}", fmt_prec(v[0], P_CMP + 1, n), fmt_prec(v[1], P_CMP + 1, n)), P_CMP),
        (op::SLT, 2) => (format!("{} < {}", fmt_signed(v[0], n), fmt_signed(v[1], n)), P_CMP),
        (op::SGT, 2) => (format!("{} > {}", fmt_signed(v[0], n), fmt_signed(v[1], n)), P_CMP),
        (op::EQ, 2) => (format!("{} == {}", fmt_prec(v[0], P_EQ + 1, n), fmt_eq_rhs(v[0], v[1], P_EQ + 1, n)), P_EQ),
        (op::AND, 2) => {
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
            (format!("{} & {}", fmt_prec(v[0], P_AND, n), fmt_prec(v[1], P_AND + 1, n)), P_AND)
        }
        (op::OR, 2) => (format!("{} | {}", fmt_prec(v[0], P_OR, n), fmt_prec(v[1], P_OR + 1, n)), P_OR),
        (op::XOR, 2) => (format!("{} ^ {}", fmt_prec(v[0], P_XOR, n), fmt_prec(v[1], P_XOR + 1, n)), P_XOR),
        (op::SHL, 2) => (format!("{} << {}", fmt_prec(v[1], P_SHIFT, n), fmt_prec(v[0], P_SHIFT + 1, n)), P_SHIFT),
        (op::SHR, 2) => {
            if is_selector_expr(expr::intern(Node::Op(op::SHR, v.to_vec()))) {
                return ("msg.sig".into(), P_PRIMARY);
            }
            (format!("{} >> {}", fmt_prec(v[1], P_SHIFT, n), fmt_prec(v[0], P_SHIFT + 1, n)), P_SHIFT)
        }
        (op::SAR, 2) => (format!("{} >> {}", fmt_signed(v[1], n), fmt_prec(v[0], P_SHIFT + 1, n)), P_SHIFT),
        (op::BYTE, 2) => (format!("byte({}, {})", fmt_expr(v[0], n), fmt_expr(v[1], n)), P_PRIMARY),
        (op::SIGNEXTEND, 2) => {
            if let Some(k) = expr::as_const(v[0]) {
                if k < U256::from_u64(31) {
                    return (format!("int{}({})", 8 * (k.low_u64() + 1), fmt_expr(v[1], n)), P_PRIMARY);
                }
            }
            (format!("signextend({}, {})", fmt_expr(v[0], n), fmt_expr(v[1], n)), P_PRIMARY)
        }
        (op::ADDMOD, 3) => (format!("addmod({}, {}, {})", fmt_expr(v[0], n), fmt_expr(v[1], n), fmt_expr(v[2], n)), P_PRIMARY),
        (op::MULMOD, 3) => (format!("mulmod({}, {}, {})", fmt_expr(v[0], n), fmt_expr(v[1], n), fmt_expr(v[2], n)), P_PRIMARY),
        _ => {
            let args: Vec<String> = v.iter().map(|x| fmt_expr(*x, n)).collect();
            (format!("{}({})", op::name(o).to_lowercase(), args.join(", ")), P_PRIMARY)
        }
    }
}

/// Right-hand side of a comparison, annotating selectors.
fn fmt_eq_rhs(lhs: ExprId, rhs: ExprId, prec: u8, n: &Names) -> String {
    if is_selector_expr(lhs) {
        if let Some(c) = expr::as_const(rhs) {
            let sel = c.low_u64() as u32;
            let s = format!("{}", c.to_hex_padded(4));
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
pub fn fmt_payload(words: &[ExprId], len: Option<U256>, n: &Names, revert: bool) -> String {
    if words.is_empty() {
        return String::new();
    }
    // Error(string) / Panic / custom error: first word's top 4 bytes
    if let Some(c0) = expr::as_const(words[0]) {
        let sel = (c0.shr(224)).low_u64() as u32;
        let top4_only = (c0 & expr::mask_bits(224)).is_zero();
        if revert && top4_only {
            if sel == 0x08c379a0 {
                if let Some(s) = decode_string_payload(words) {
                    return format!("\"{}\"", s);
                }
            }
            if sel == 0x4e487b71 && words.len() >= 2 {
                if let Some(code) = expr::as_const(shifted_word(words, 0)) {
                    return format!("Panic({})", panic_name(code.low_u64()));
                }
            }
            let nargs = len.and_then(|l| l.as_usize()).map(|l| l.saturating_sub(4) / 32).unwrap_or(words.len().saturating_sub(1));
            if let Some(sig) = sigs::error(sel) {
                let args: Vec<String> = (0..nargs).map(|i| fmt_expr(shifted_word(words, i), n)).collect();
                return format!("{}({})", sigs::name_of(sig), args.join(", "));
            }
            let args: Vec<String> = (0..nargs).map(|i| fmt_expr(shifted_word(words, i), n)).collect();
            return format!("CustomError_{:08x}({})", sel, args.join(", "));
        }
    }
    let parts: Vec<String> = words.iter().map(|w| fmt_expr(*w, n)).collect();
    parts.join(", ")
}

/// ABI word `i` of a payload that starts with a 4-byte selector: bytes `4 + 32*i .. 36 + 32*i`,
/// which straddle memory words `i` and `i + 1`.
fn shifted_word(words: &[ExprId], i: usize) -> ExprId {
    let hi = words.get(i).copied().unwrap_or_else(|| expr::konst(U256::ZERO));
    let lo = words.get(i + 1).copied().unwrap_or_else(|| expr::konst(U256::ZERO));
    // (hi << 32) | (lo >> 224)
    expr::op2(op::OR, expr::op2(op::SHL, expr::konst_u64(32), hi), expr::op2(op::SHR, expr::konst_u64(224), lo))
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
pub fn decode_string_payload(words: &[ExprId]) -> Option<String> {
    // ABI words after the selector: [offset (0x20), length, data...]
    let offset = expr::as_const(shifted_word(words, 0))?;
    if offset != U256::from_u64(0x20) {
        return None;
    }
    let len = expr::as_const(shifted_word(words, 1))?.as_usize()?;
    if len > 1024 {
        return None;
    }
    let mut bytes = Vec::new();
    let mut i = 2;
    while bytes.len() < len {
        let w = expr::as_const(shifted_word(words, i))?;
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
    if !bytes.iter().all(|b| *b >= 0x20 && *b < 0x7f || *b == b'\n' || *b == b'\t') {
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
            c if (c as u32) < 0x20 || c == '\u{fffd}' => out.push_str(&format!("\\x{:02x}", c as u32 & 0xff)),
            c => out.push(c),
        }
    }
    out
}

/// Render the input of an external call: `abi.encodeWithSelector(...)` decoded when possible.
pub fn fmt_call_input(words: &[ExprId], in_len: Option<U256>, n: &Names) -> (Option<String>, Vec<String>) {
    // Returns (function name if known, args)
    if words.is_empty() {
        return (None, vec![]);
    }
    let in_len = in_len.and_then(|l| l.as_usize());
    if let Some(c0) = expr::as_const(words[0]) {
        // The first word holds min(len, 32) bytes, right-aligned when shorter than a word.
        let first_bytes = in_len.map(|l| l.min(32)).unwrap_or(32);
        let looks_like_selector = in_len.map_or((c0 & expr::mask_bits(224)).is_zero(), |l| l >= 4 && (l - 4) % 32 == 0);
        if looks_like_selector && first_bytes >= 4 {
            let sel = c0.shr(8 * (first_bytes as u32 - 4)).low_u64() as u32;
            let nargs = in_len.map(|l| l.saturating_sub(4) / 32).unwrap_or(words.len().saturating_sub(1));
            let args: Vec<String> = (0..nargs.min(words.len())).map(|i| fmt_expr(shifted_word(words, i), n)).collect();
            let name = match sigs::function(sel) {
                Some(sig) => sigs::name_of(sig).to_string(),
                None => format!("func_{:08x}", sel),
            };
            return (Some(name), args);
        }
    }
    (None, words.iter().map(|w| fmt_expr(*w, n)).collect())
}

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
        Stmt::SStore { key, val, transient } => format!("{} = {};", fmt_slot(*key, n, *transient), fmt_expr(*val, n)),
        Stmt::Log { off, len, topics, data } => {
            let mut args: Vec<String> = Vec::new();
            let mut name = None;
            if let Some(t0) = topics.first().and_then(|t| expr::as_const(*t)) {
                if let Some(sig) = sigs::event(&t0.to_be_bytes()) {
                    name = Some(sigs::name_of(sig).to_string());
                }
            }
            let start = if name.is_some() { 1 } else { 0 };
            for t in &topics[start..] {
                args.push(fmt_expr(*t, n));
            }
            match data {
                Some(words) => {
                    for w in words {
                        args.push(fmt_expr(*w, n));
                    }
                }
                None => {
                    if expr::as_const(*len) != Some(U256::ZERO) {
                        args.push(format!("mem[{}:{}]", fmt_expr(*off, n), fmt_expr(expr::op2(op::ADD, *off, *len), n)));
                    }
                }
            }
            match name {
                Some(nm) => format!("emit {}({});", nm, args.join(", ")),
                None => format!("log{}({});", topics.len(), args.join(", ")),
            }
        }
        Stmt::Call { kind, gas, addr, value, in_off, in_len, out_len, input, result, .. } => {
            let target = fmt_prec(*addr, P_PRIMARY, n);
            let mut opts = Vec::new();
            if let Some(v) = value {
                if expr::as_const(*v) != Some(U256::ZERO) {
                    opts.push(format!("value: {}", fmt_expr(*v, n)));
                }
            }
            let gas_is_all = matches!(expr::node(*gas), Node::Env(op::GAS, _)) || matches!(expr::node(*gas), Node::Op(op::SUB, v) if matches!(expr::node(v[0]), Node::Env(op::GAS, _)));
            if !gas_is_all {
                opts.push(format!("gas: {}", fmt_expr(*gas, n)));
            }
            let opts_s = if opts.is_empty() { String::new() } else { format!("{{{}}}", opts.join(", ")) };
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
                (Some(f), _) => format!("abi.encodeWithSelector({}.selector, {})", f, args.join(", ")).replace(", )", ")"),
                (None, Some(_)) if args.is_empty() => "\"\"".into(),
                (None, Some(_)) => format!("abi.encode({})", args.join(", ")),
                (None, None) => {
                    if expr::as_const(*in_len) == Some(U256::ZERO) {
                        "\"\"".into()
                    } else {
                        format!("mem[{}:{}]", fmt_expr(*in_off, n), fmt_expr(expr::op2(op::ADD, *in_off, *in_len), n))
                    }
                }
            };
            let ret = if expr::as_const(*out_len) == Some(U256::ZERO) { String::new() } else { String::new() };
            let _ = ret;
            // Known target function: show as a typed call.
            match fname {
                Some(f) if *kind == op::CALL || *kind == op::STATICCALL => {
                    format!("{} = {}.{}{}({}); // {}({})", fmt_expr(*result, n), target, method, opts_s, payload, f, args.join(", "))
                }
                _ => format!("{} = {}.{}{}({});", fmt_expr(*result, n), target, method, opts_s, payload),
            }
        }
        Stmt::Create { kind, value, off, len, salt, result, init, .. } => {
            let code = match init {
                Some(words) if !words.is_empty() => format!("bytecode[{} words]", words.len()),
                _ => format!("mem[{}:{}]", fmt_expr(*off, n), fmt_expr(expr::op2(op::ADD, *off, *len), n)),
            };
            let v = if expr::as_const(*value) == Some(U256::ZERO) { String::new() } else { format!("{{value: {}}}", fmt_expr(*value, n)) };
            match (kind, salt) {
                (&op::CREATE2, Some(s)) => format!("{} = create2{}({}, salt: {});", fmt_expr(*result, n), v, code, fmt_expr(*s, n)),
                _ => format!("{} = create{}({});", fmt_expr(*result, n), v, code),
            }
        }
        Stmt::Copy { kind, dest, src, len, addr } => {
            let src_s = match addr {
                Some(a) => format!("{}.code[{}:+{}]", fmt_prec(*a, P_PRIMARY, n), fmt_expr(*src, n), fmt_expr(*len, n)),
                None => format!("{}[{}:+{}]", copy_source(*kind), fmt_expr(*src, n), fmt_expr(*len, n)),
            };
            format!("mem[{}:+{}] = {};", fmt_expr(*dest, n), fmt_expr(*len, n), src_s)
        }
        Stmt::Internal { callee, args, results, .. } => {
            let a: Vec<String> = args.iter().map(|x| fmt_expr(*x, n)).collect();
            let call = format!("func_{:#x}({})", callee, a.join(", "));
            match results.len() {
                0 => format!("{};", call),
                1 => format!("{} = {};", fmt_expr(results[0], n), call),
                _ => format!("({}) = {};", results.iter().map(|r| fmt_expr(*r, n)).collect::<Vec<_>>().join(", "), call),
            }
        }
        Stmt::Drop(e) => format!("// ignored: {}", fmt_expr(*e, n)),
    }
}

pub fn fmt_term_halt(t: &Term, n: &Names) -> Option<String> {
    Some(match t {
        Term::Return { off, len, data } => match data {
            Some(words) if !words.is_empty() => format!("return ({});", fmt_payload(words, expr::as_const(*len), n, false)).replace("return ((", "return (").replace("));", ");"),
            Some(_) => "return;".into(),
            None => {
                if expr::as_const(*len) == Some(U256::ZERO) {
                    "return;".into()
                } else {
                    format!("return mem[{}:{}];", fmt_expr(*off, n), fmt_expr(expr::op2(op::ADD, *off, *len), n))
                }
            }
        },
        Term::Revert { off, len, data } => match data {
            Some(words) if !words.is_empty() => {
                let p = fmt_payload(words, expr::as_const(*len), n, true);
                if p.starts_with('"') || p.starts_with("Panic(") || p.chars().next().map_or(false, |c| c.is_ascii_uppercase()) {
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
                    format!("revert(mem[{}:{}]);", fmt_expr(*off, n), fmt_expr(expr::op2(op::ADD, *off, *len), n))
                }
            }
        },
        Term::Stop => "return;".into(),
        Term::Invalid => "assert(false); // INVALID".into(),
        Term::SelfDestruct(a) => format!("selfdestruct({});", fmt_expr(*a, n)),
        Term::InternalReturn(vals) => {
            if vals.is_empty() {
                "return;".into()
            } else {
                format!("return ({});", vals.iter().map(|v| fmt_expr(*v, n)).collect::<Vec<_>>().join(", "))
            }
        }
        Term::Unresolved(t) => format!("jump({}); // unresolved target", fmt_expr(*t, n)),
        Term::CondJump { cond, target } => format!("if ({}) jump({});", fmt_expr(*cond, n), fmt_expr(*target, n)),
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
    fn dfs(l: &Lifted, x: usize, seen: &mut std::collections::HashSet<usize>, order: &mut Vec<usize>) {
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
        let falls = prev.map_or(false, |p| matches!(l.nodes[p].term, Term::Jump(t) if t == nid) && nd.preds.len() == 1 && !l.edge_assigns.contains_key(&(p, nid)));
        if !falls {
            needs_label.insert(nid);
        }
    }
    for (idx, &nid) in order.iter().enumerate() {
        let nd = &l.nodes[nid];
        if needs_label.contains(&nid) {
            out.push_str(&format!("{}L{:x}:\n", indent, nd.pc));
        }
        for s in &nd.stmts {
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
                    Some(t) => out.push_str(&format!("{}    if ({}) {{ {} }}\n", indent, fmt_expr(*cond, n), goto(*t))),
                    None => out.push_str(&format!("{}    if ({}) {{ revert(); }}\n", indent, fmt_expr(*cond, n))),
                }
                if Some(*f) != next || l.edge_assigns.contains_key(&(nid, *f)) {
                    out.push_str(&format!("{}    {}\n", indent, goto(*f)));
                }
            }
            Term::Switch { target, cases } => {
                out.push_str(&format!("{}    switch ({}) {{ {} }}\n", indent, fmt_expr(*target, n), cases.iter().map(|c| goto(*c)).collect::<Vec<_>>().join(" ")));
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
