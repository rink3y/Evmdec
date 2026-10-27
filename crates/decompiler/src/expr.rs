//! Hash-consed expression IR. Every expression is an `ExprId` into a thread-local arena, so
//! structural equality is pointer equality and shared sub-expressions cost nothing.

use crate::opcode as op;
use crate::u256::U256;
use std::cell::RefCell;
use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct ExprId(pub u32);

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Node {
    Const(U256),
    /// Opcode with no operands (CALLER, CALLVALUE, TIMESTAMP, ...). `PC` and `MSIZE`/`GAS`
    /// carry a sequence number so distinct evaluations are not merged.
    Env(u8, u32),
    /// Unary/binary/ternary EVM operation on expressions.
    Op(u8, Vec<ExprId>),
    /// `MLOAD(offset)` whose value is not known from earlier writes; `version` separates
    /// loads separated by unknown writes.
    MLoad(ExprId, u32),
    /// `SLOAD(key)` / `TLOAD(key)`: `transient` distinguishes TLOAD.
    SLoad(ExprId, bool, u32),
    /// `CALLDATALOAD(offset)`.
    CallDataLoad(ExprId),
    /// KECCAK256 of known memory words (each 32 bytes, last may be partial: `tail_bytes`).
    Keccak(Vec<ExprId>, u8),
    /// KECCAK256 of a memory range whose content is unknown: (offset, length, memory version).
    KeccakMem(ExprId, ExprId, u32),
    /// Result (success flag) of a CALL-family instruction; `seq` is the statement sequence number.
    CallResult(u32),
    /// Result (address) of CREATE/CREATE2.
    CreateResult(u32),
    /// A value flowing in from predecessors that differs between them (SSA phi), or a stack
    /// slot of unknown origin at a function entry (`Arg`).
    Var(u32),
    Arg(u32),
    /// Return-data word: value loaded from the output region of call `seq` at word `off`.
    ReturnData(u32, ExprId),
    /// Bytes read from a copied region (CALLDATACOPY/CODECOPY/RETURNDATACOPY/EXTCODECOPY/MCOPY):
    /// `kind` is the copying opcode, then (source offset, memory version).
    CopiedWord(u8, ExprId, u32),
    /// The j-th result of internal call `seq`.
    IntRet(u32, u16),
    /// Memory word of unknown content at (offset) after an internal call `seq`... (reserved)
    Unknown(u32),
}

struct Arena {
    nodes: Vec<Node>,
    map: HashMap<Node, ExprId>,
    seq: u32,
}

thread_local! {
    static ARENA: RefCell<Arena> = RefCell::new(Arena { nodes: Vec::new(), map: HashMap::new(), seq: 0 });
}

pub fn intern(n: Node) -> ExprId {
    ARENA.with(|a| {
        let mut a = a.borrow_mut();
        if let Some(id) = a.map.get(&n) {
            return *id;
        }
        let id = ExprId(a.nodes.len() as u32);
        a.nodes.push(n.clone());
        a.map.insert(n, id);
        id
    })
}

pub fn node(id: ExprId) -> Node {
    ARENA.with(|a| a.borrow().nodes[id.0 as usize].clone())
}

pub fn with_node<R>(id: ExprId, f: impl FnOnce(&Node) -> R) -> R {
    ARENA.with(|a| f(&a.borrow().nodes[id.0 as usize]))
}

/// Fresh sequence number for versioned nodes.
pub fn next_seq() -> u32 {
    ARENA.with(|a| {
        let mut a = a.borrow_mut();
        a.seq += 1;
        a.seq
    })
}

pub fn arena_size() -> usize {
    ARENA.with(|a| a.borrow().nodes.len())
}

pub fn konst(v: U256) -> ExprId {
    intern(Node::Const(v))
}
pub fn konst_u64(v: u64) -> ExprId {
    konst(U256::from_u64(v))
}
pub fn as_const(id: ExprId) -> Option<U256> {
    with_node(id, |n| if let Node::Const(v) = n { Some(*v) } else { None })
}
pub fn is_const(id: ExprId) -> bool {
    as_const(id).is_some()
}
pub fn var(n: u32) -> ExprId {
    intern(Node::Var(n))
}
pub fn arg(n: u32) -> ExprId {
    intern(Node::Arg(n))
}
pub fn env(o: u8) -> ExprId {
    intern(Node::Env(o, 0))
}
pub fn env_seq(o: u8) -> ExprId {
    intern(Node::Env(o, next_seq()))
}
pub fn calldataload(off: ExprId) -> ExprId {
    intern(Node::CallDataLoad(off))
}

pub fn mask_bits(bits: u32) -> U256 {
    if bits >= 256 {
        U256::MAX
    } else {
        U256::ONE.shl(bits).wrapping_sub(U256::ONE)
    }
}

/// Split `e` into `(base, constant offset)`: `ADD(x, c)` → `(Some(x), c)`, `c` → `(None, c)`.
pub fn split_offset(e: ExprId) -> (Option<ExprId>, U256) {
    match node(e) {
        Node::Const(c) => (None, c),
        Node::Op(op::ADD, v) => {
            if let Some(c) = as_const(v[1]) {
                let (b, c2) = split_offset(v[0]);
                (b, c2.wrapping_add(c))
            } else if let Some(c) = as_const(v[0]) {
                let (b, c2) = split_offset(v[1]);
                (b, c2.wrapping_add(c))
            } else {
                (Some(e), U256::ZERO)
            }
        }
        Node::Op(op::SUB, v) => {
            if let Some(c) = as_const(v[1]) {
                let (b, c2) = split_offset(v[0]);
                (b, c2.wrapping_sub(c))
            } else {
                (Some(e), U256::ZERO)
            }
        }
        _ => (Some(e), U256::ZERO),
    }
}

pub fn add_const(e: ExprId, c: U256) -> ExprId {
    if c.is_zero() {
        e
    } else {
        op2(op::ADD, e, konst(c))
    }
}

fn is_commutative(o: u8) -> bool {
    matches!(o, op::ADD | op::MUL | op::AND | op::OR | op::XOR | op::EQ)
}

fn fold2(o: u8, a: U256, b: U256) -> Option<U256> {
    Some(match o {
        op::ADD => a.wrapping_add(b),
        op::MUL => a.wrapping_mul(b),
        op::SUB => a.wrapping_sub(b),
        op::DIV => a.div(b),
        op::SDIV => a.sdiv(b),
        op::MOD => a.rem(b),
        op::SMOD => a.smod(b),
        op::EXP => a.pow(b),
        op::SIGNEXTEND => U256::signextend(a, b),
        op::LT => U256::from(a < b),
        op::GT => U256::from(a > b),
        op::SLT => U256::from(a.scmp(&b) == std::cmp::Ordering::Less),
        op::SGT => U256::from(a.scmp(&b) == std::cmp::Ordering::Greater),
        op::EQ => U256::from(a == b),
        op::AND => a & b,
        op::OR => a | b,
        op::XOR => a ^ b,
        op::BYTE => U256::byte(a, b),
        op::SHL => {
            if a >= U256::from_u64(256) {
                U256::ZERO
            } else {
                b.shl(a.low_u64() as u32)
            }
        }
        op::SHR => {
            if a >= U256::from_u64(256) {
                U256::ZERO
            } else {
                b.shr(a.low_u64() as u32)
            }
        }
        op::SAR => {
            if a >= U256::from_u64(256) {
                if b.is_negative() {
                    U256::MAX
                } else {
                    U256::ZERO
                }
            } else {
                b.sar(a.low_u64() as u32)
            }
        }
        _ => return None,
    })
}

/// Build a unary op with simplification.
pub fn op1(o: u8, a: ExprId) -> ExprId {
    if let Some(c) = as_const(a) {
        match o {
            op::ISZERO => return konst(U256::from(c.is_zero())),
            op::NOT => return konst(!c),
            _ => {}
        }
    }
    match o {
        op::ISZERO => {
            // ISZERO(a - b) / ISZERO(a ^ b) -> a == b
            if let Node::Op(io, v) = node(a) {
                if io == op::SUB || io == op::XOR {
                    return op2(op::EQ, v[0], v[1]);
                }
            }
            // ISZERO(ISZERO(ISZERO(x))) -> ISZERO(x)
            if let Node::Op(op::ISZERO, v) = node(a) {
                if let Node::Op(op::ISZERO, w) = node(v[0]) {
                    return op1(op::ISZERO, w[0]);
                }
                // ISZERO(ISZERO(cmp)) -> cmp for boolean-valued comparisons
                if is_boolean(v[0]) {
                    return v[0];
                }
            }
        }
        op::NOT => {
            if let Node::Op(op::NOT, v) = node(a) {
                return v[0];
            }
        }
        _ => {}
    }
    intern(Node::Op(o, vec![a]))
}

/// True if the expression can only evaluate to 0 or 1.
pub fn is_boolean(e: ExprId) -> bool {
    match node(e) {
        Node::Op(o, _) => matches!(o, op::LT | op::GT | op::SLT | op::SGT | op::EQ | op::ISZERO),
        Node::Const(c) => c.is_zero() || c == U256::ONE,
        Node::CallResult(_) => true,
        _ => false,
    }
}

/// Build a binary op with constant folding and algebraic normalisation.
/// Operand order follows the EVM: `op2(SUB, a, b)` is `a - b` where `a` was the top of stack.
pub fn op2(o: u8, a: ExprId, b: ExprId) -> ExprId {
    let (ca, cb) = (as_const(a), as_const(b));
    if let (Some(x), Some(y)) = (ca, cb) {
        if let Some(r) = fold2(o, x, y) {
            return konst(r);
        }
    }
    // Canonical operand order for commutative ops: constant on the right.
    let (a, b, ca, cb) = if is_commutative(o) && ca.is_some() && cb.is_none() { (b, a, cb, ca) } else { (a, b, ca, cb) };
    match o {
        op::ADD => {
            if cb == Some(U256::ZERO) {
                return a;
            }
            // x + (y - x) -> y ; (y - x) + x -> y
            if let Node::Op(op::SUB, v) = node(b) {
                if v[1] == a {
                    return v[0];
                }
            }
            if let Node::Op(op::SUB, v) = node(a) {
                if v[1] == b {
                    return v[0];
                }
            }
            // (x + c1) + c2 -> x + (c1+c2)
            if let Some(c2) = cb {
                if let Node::Op(op::ADD, v) = node(a) {
                    if let Some(c1) = as_const(v[1]) {
                        return op2(op::ADD, v[0], konst(c1.wrapping_add(c2)));
                    }
                }
                if let Node::Op(op::SUB, v) = node(a) {
                    if let Some(c1) = as_const(v[1]) {
                        // (x - c1) + c2
                        return if c2 >= c1 { op2(op::ADD, v[0], konst(c2.wrapping_sub(c1))) } else { op2(op::SUB, v[0], konst(c1.wrapping_sub(c2))) };
                    }
                }
                // Negative constant: x + (2^256 - k) -> x - k, for small k (nicer output)
                if c2.is_negative() && c2.neg() < U256::from_u64(1 << 32) {
                    return intern(Node::Op(op::SUB, vec![a, konst(c2.neg())]));
                }
            }
        }
        op::SUB => {
            if cb == Some(U256::ZERO) {
                return a;
            }
            if a == b {
                return konst(U256::ZERO);
            }
            // (x + y) - x -> y ; (x + y) - y -> x
            if let Node::Op(op::ADD, v) = node(a) {
                if v[0] == b {
                    return v[1];
                }
                if v[1] == b {
                    return v[0];
                }
                // (x + c1) - (x + c2) -> c1 - c2
                if let Node::Op(op::ADD, w) = node(b) {
                    if v[0] == w[0] {
                        if let (Some(c1), Some(c2)) = (as_const(v[1]), as_const(w[1])) {
                            return konst(c1.wrapping_sub(c2));
                        }
                    }
                }
            }
            // x - (x - y) -> y
            if let Node::Op(op::SUB, v) = node(b) {
                if v[0] == a {
                    return v[1];
                }
            }
            if let Some(c2) = cb {
                if let Node::Op(op::ADD, v) = node(a) {
                    if let Some(c1) = as_const(v[1]) {
                        return if c1 >= c2 { op2(op::ADD, v[0], konst(c1.wrapping_sub(c2))) } else { op2(op::SUB, v[0], konst(c2.wrapping_sub(c1))) };
                    }
                }
                if let Node::Op(op::SUB, v) = node(a) {
                    if let Some(c1) = as_const(v[1]) {
                        return op2(op::SUB, v[0], konst(c1.wrapping_add(c2)));
                    }
                }
            }
        }
        op::MUL => {
            if cb == Some(U256::ONE) {
                return a;
            }
            if cb == Some(U256::ZERO) {
                return konst(U256::ZERO);
            }
        }
        op::DIV => {
            if cb == Some(U256::ONE) {
                return a;
            }
            if cb == Some(U256::ZERO) {
                return konst(U256::ZERO);
            }
            // x / 2^k -> x >> k
            if let Some(c) = cb {
                if c.is_power_of_two() {
                    return op2(op::SHR, konst_u64(c.trailing_zeros() as u64), a);
                }
            }
        }
        op::MOD => {
            if cb == Some(U256::ONE) || cb == Some(U256::ZERO) {
                return konst(U256::ZERO);
            }
        }
        op::EXP => {
            if cb == Some(U256::ZERO) {
                return konst(U256::ONE);
            }
            if cb == Some(U256::ONE) {
                return a;
            }
        }
        op::AND => {
            if cb == Some(U256::MAX) {
                return a;
            }
            if cb == Some(U256::ZERO) {
                return konst(U256::ZERO);
            }
            if a == b {
                return a;
            }
            if let Some(m) = cb {
                // AND(AND(x, m1), m2) -> AND(x, m1&m2)
                if let Node::Op(op::AND, v) = node(a) {
                    if let Some(m1) = as_const(v[1]) {
                        return op2(op::AND, v[0], konst(m1 & m));
                    }
                }
                // Masking a boolean or a value already narrower than the mask is a no-op.
                if m.is_low_mask() && m.bits() >= value_bits(a) {
                    return a;
                }
            }
        }
        op::OR => {
            if cb == Some(U256::ZERO) {
                return a;
            }
            if cb == Some(U256::MAX) {
                return konst(U256::MAX);
            }
            if a == b {
                return a;
            }
        }
        op::XOR => {
            if cb == Some(U256::ZERO) {
                return a;
            }
            if a == b {
                return konst(U256::ZERO);
            }
        }
        op::SHL => {
            // SHL(shift, value): a is shift
            if ca == Some(U256::ZERO) {
                return b;
            }
            if let Some(s) = ca {
                if s >= U256::from_u64(256) {
                    return konst(U256::ZERO);
                }
                // SHL(k, SHR(k, x)) -> AND(x, ~mask)
                if let Node::Op(op::SHR, v) = node(b) {
                    if as_const(v[0]) == Some(s) {
                        return op2(op::AND, v[1], konst(!mask_bits(s.low_u64() as u32)));
                    }
                }
            }
        }
        op::SHR => {
            if ca == Some(U256::ZERO) {
                return b;
            }
            if let Some(s) = ca {
                if s >= U256::from_u64(256) {
                    return konst(U256::ZERO);
                }
                // SHR(k, SHL(k, x)) -> AND(x, mask(256-k))
                if let Node::Op(op::SHL, v) = node(b) {
                    if as_const(v[0]) == Some(s) {
                        return op2(op::AND, v[1], konst(mask_bits(256 - s.low_u64() as u32)));
                    }
                }
                // SHR(k, AND(x, m)) where m has no bits below k... keep as is.
            }
        }
        op::SAR => {
            if ca == Some(U256::ZERO) {
                return b;
            }
        }
        op::EQ => {
            if a == b {
                return konst(U256::ONE);
            }
            // EQ(x, 0) -> ISZERO(x)
            if cb == Some(U256::ZERO) {
                return op1(op::ISZERO, a);
            }
            // EQ(ISZERO(x), 0)... handled above. EQ(bool, 1) -> bool
            if cb == Some(U256::ONE) && is_boolean(a) {
                return a;
            }
        }
        op::LT | op::GT | op::SLT | op::SGT => {
            if a == b {
                return konst(U256::ZERO);
            }
            // LT(x, 0) is false; GT(0, x) is false
            if (o == op::LT && cb == Some(U256::ZERO)) || (o == op::GT && ca == Some(U256::ZERO)) {
                return konst(U256::ZERO);
            }
            // GT(x, 0) -> ISZERO(ISZERO(x)); LT(0, x) likewise
            if o == op::GT && cb == Some(U256::ZERO) {
                return op1(op::ISZERO, op1(op::ISZERO, a));
            }
            if o == op::LT && ca == Some(U256::ZERO) {
                return op1(op::ISZERO, op1(op::ISZERO, b));
            }
        }
        op::SIGNEXTEND => {
            if let Some(k) = ca {
                if k >= U256::from_u64(31) {
                    return b;
                }
            }
        }
        _ => {}
    }
    intern(Node::Op(o, vec![a, b]))
}

pub fn op3(o: u8, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
    if let (Some(x), Some(y), Some(z)) = (as_const(a), as_const(b), as_const(c)) {
        match o {
            op::ADDMOD => return konst(x.addmod(y, z)),
            op::MULMOD => return konst(x.mulmod(y, z)),
            _ => {}
        }
    }
    intern(Node::Op(o, vec![a, b, c]))
}

/// Upper bound on the number of significant bits of a value, from its shape.
pub fn value_bits(e: ExprId) -> u32 {
    match node(e) {
        Node::Const(c) => c.bits(),
        Node::Env(o, _) => match o {
            op::CALLER | op::ADDRESS | op::ORIGIN | op::COINBASE => 160,
            op::TIMESTAMP | op::NUMBER | op::GASLIMIT | op::GAS | op::CALLDATASIZE | op::RETURNDATASIZE | op::CODESIZE | op::MSIZE | op::PC => 64,
            _ => 256,
        },
        Node::Op(o, v) => match o {
            op::ISZERO | op::LT | op::GT | op::SLT | op::SGT | op::EQ => 1,
            op::AND => {
                let a = value_bits(v[0]);
                let b = value_bits(v[1]);
                a.min(b)
            }
            op::OR | op::XOR => value_bits(v[0]).max(value_bits(v[1])),
            op::SHR => {
                if let Some(s) = as_const(v[0]) {
                    let s = s.low_u64().min(256) as u32;
                    value_bits(v[1]).saturating_sub(s)
                } else {
                    256
                }
            }
            op::SHL => {
                if let Some(s) = as_const(v[0]) {
                    (value_bits(v[1]) + s.low_u64().min(256) as u32).min(256)
                } else {
                    256
                }
            }
            op::DIV => {
                if let Some(c) = as_const(v[1]) {
                    if c.is_zero() {
                        0
                    } else {
                        value_bits(v[0]).saturating_sub(c.bits() - 1)
                    }
                } else {
                    value_bits(v[0])
                }
            }
            op::MOD => {
                if let Some(c) = as_const(v[1]) {
                    c.bits()
                } else {
                    256
                }
            }
            op::BYTE => 8,
            op::EXTCODESIZE | op::BALANCE => 256,
            _ => 256,
        },
        Node::CallResult(_) => 1,
        Node::CreateResult(_) => 160,
        _ => 256,
    }
}

/// Size of the expression tree counting shared nodes once per occurrence (capped).
pub fn size(e: ExprId) -> usize {
    fn go(e: ExprId, budget: &mut usize) -> usize {
        if *budget == 0 {
            return 1;
        }
        *budget -= 1;
        match node(e) {
            Node::Op(_, v) | Node::Keccak(v, _) => 1 + v.iter().map(|x| go(*x, budget)).sum::<usize>(),
            Node::MLoad(a, _) | Node::SLoad(a, _, _) | Node::CallDataLoad(a) | Node::ReturnData(_, a) | Node::CopiedWord(_, a, _) => 1 + go(a, budget),
            Node::KeccakMem(a, b, _) => 1 + go(a, budget) + go(b, budget),
            _ => 1,
        }
    }
    let mut budget = 10_000;
    go(e, &mut budget)
}

/// Direct children of an expression.
pub fn children(e: ExprId) -> Vec<ExprId> {
    match node(e) {
        Node::Op(_, v) | Node::Keccak(v, _) => v,
        Node::MLoad(a, _) | Node::SLoad(a, _, _) | Node::CallDataLoad(a) | Node::ReturnData(_, a) | Node::CopiedWord(_, a, _) => vec![a],
        Node::KeccakMem(a, b, _) => vec![a, b],
        _ => vec![],
    }
}

/// Does `e` contain a node satisfying `pred`? Bounded traversal.
pub fn contains(e: ExprId, pred: &dyn Fn(&Node) -> bool) -> bool {
    let mut seen = std::collections::HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 20_000 {
            continue;
        }
        if with_node(x, |n| pred(n)) {
            return true;
        }
        stack.extend(children(x));
    }
    false
}

/// Replace every `Var(i)` / `Arg(i)` according to `f` (returns None to keep). Memoised.
pub fn substitute(e: ExprId, f: &dyn Fn(&Node) -> Option<ExprId>, memo: &mut HashMap<ExprId, ExprId>) -> ExprId {
    if let Some(r) = memo.get(&e) {
        return *r;
    }
    let n = node(e);
    if let Some(r) = f(&n) {
        memo.insert(e, r);
        return r;
    }
    let r = match n {
        Node::Op(o, v) => {
            let nv: Vec<ExprId> = v.iter().map(|x| substitute(*x, f, memo)).collect();
            if nv == v {
                e
            } else {
                match nv.len() {
                    1 => op1(o, nv[0]),
                    2 => op2(o, nv[0], nv[1]),
                    _ => op3(o, nv[0], nv[1], nv[2]),
                }
            }
        }
        Node::Keccak(v, t) => {
            let nv: Vec<ExprId> = v.iter().map(|x| substitute(*x, f, memo)).collect();
            intern(Node::Keccak(nv, t))
        }
        Node::MLoad(a, ver) => intern(Node::MLoad(substitute(a, f, memo), ver)),
        Node::SLoad(a, t, ver) => intern(Node::SLoad(substitute(a, f, memo), t, ver)),
        Node::CallDataLoad(a) => intern(Node::CallDataLoad(substitute(a, f, memo))),
        Node::ReturnData(s, a) => intern(Node::ReturnData(s, substitute(a, f, memo))),
        Node::CopiedWord(k, a, ver) => intern(Node::CopiedWord(k, substitute(a, f, memo), ver)),
        Node::KeccakMem(a, b, ver) => intern(Node::KeccakMem(substitute(a, f, memo), substitute(b, f, memo), ver)),
        _ => e,
    };
    memo.insert(e, r);
    r
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn folding() {
        let a = konst_u64(5);
        let b = konst_u64(7);
        assert_eq!(as_const(op2(op::ADD, a, b)), Some(U256::from_u64(12)));
        let x = arg(0);
        let e = op2(op::ADD, op2(op::ADD, x, konst_u64(4)), konst_u64(32));
        assert_eq!(split_offset(e), (Some(x), U256::from_u64(36)));
        assert_eq!(op2(op::DIV, x, konst(U256::ONE.shl(224))), op2(op::SHR, konst_u64(224), x));
        assert_eq!(op1(op::ISZERO, op1(op::ISZERO, op2(op::EQ, x, konst_u64(3)))), op2(op::EQ, x, konst_u64(3)));
        assert_eq!(op2(op::AND, op2(op::AND, x, konst(mask_bits(160))), konst(mask_bits(160))), op2(op::AND, x, konst(mask_bits(160))));
        assert_eq!(op2(op::SUB, op2(op::ADD, x, konst_u64(10)), konst_u64(4)), op2(op::ADD, x, konst_u64(6)));
    }
}
