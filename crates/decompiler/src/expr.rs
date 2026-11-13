use crate::opcode as op;
use crate::u256::U256;
use std::cell::RefCell;
use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct ExprId(pub u32);

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Node {
    Const(U256),
    Env(u8, u32),
    Op(u8, Vec<ExprId>),
    MLoad(ExprId, u32),
    SLoad(ExprId, bool, u32),
    CallDataLoad(ExprId),
    Keccak(Vec<ExprId>, u8),
    KeccakMem(ExprId, ExprId, u32),
    CallResult(u32),
    CreateResult(u32),
    Var(u32),
    Arg(u32),
    ReturnData(u32, ExprId),
    CopiedWord(u8, ExprId, u32),
    IntRet(u32, u16),
    Unknown(u32),
}

pub mod kind {
    pub const CONST: u16 = 1 << 0;
    pub const ENV: u16 = 1 << 1;
    pub const OP: u16 = 1 << 2;
    pub const MLOAD: u16 = 1 << 3;
    pub const SLOAD: u16 = 1 << 4;
    pub const CALLDATALOAD: u16 = 1 << 5;
    pub const KECCAK: u16 = 1 << 6;
    pub const KECCAK_MEM: u16 = 1 << 7;
    pub const CALL_RESULT: u16 = 1 << 8;
    pub const CREATE_RESULT: u16 = 1 << 9;
    pub const VAR: u16 = 1 << 10;
    pub const ARG: u16 = 1 << 11;
    pub const RETURN_DATA: u16 = 1 << 12;
    pub const COPIED_WORD: u16 = 1 << 13;
    pub const INT_RET: u16 = 1 << 14;
    pub const UNKNOWN: u16 = 1 << 15;
}

// bits, may, depth and kinds are worked out once, when a node is made, from its children.
// Walking a shared expression for them again cost 2^n on n nested operators.
#[derive(Default)]
struct Arena {
    nodes: Vec<Node>,
    map: HashMap<Node, ExprId>,
    bits: Vec<u16>,
    may: Vec<U256>,
    depth: Vec<u32>,
    kinds: Vec<u16>,
    seq: u32,
}

thread_local! {
    static ARENA: RefCell<Arena> = RefCell::new(Arena::default());
}

// Deeper than this, code that walks an expression by calling itself can run out of stack.
// No compiler output comes near it. A deeper value is kept as an unknown.
const MAX_DEPTH: u32 = 1_024;

impl Arena {
    fn konst(&self, id: ExprId) -> Option<U256> {
        match &self.nodes[id.0 as usize] {
            Node::Const(c) => Some(*c),
            _ => None,
        }
    }

    fn depth_below(&self, n: &Node) -> u32 {
        let of = |id: &ExprId| self.depth[id.0 as usize];
        match n {
            Node::Op(_, v) | Node::Keccak(v, _) => v.iter().map(of).max().unwrap_or(0),
            Node::MLoad(a, _)
            | Node::SLoad(a, _, _)
            | Node::CallDataLoad(a)
            | Node::ReturnData(_, a)
            | Node::CopiedWord(_, a, _) => of(a),
            Node::KeccakMem(a, b, _) => of(a).max(of(b)),
            _ => 0,
        }
    }

    fn kinds_of(&self, n: &Node) -> u16 {
        let of = |id: &ExprId| self.kinds[id.0 as usize];
        let all = |v: &[ExprId]| v.iter().fold(0, |seen, id| seen | of(id));
        match n {
            Node::Const(_) => kind::CONST,
            Node::Env(..) => kind::ENV,
            Node::Op(_, v) => kind::OP | all(v),
            Node::MLoad(a, _) => kind::MLOAD | of(a),
            Node::SLoad(a, _, _) => kind::SLOAD | of(a),
            Node::CallDataLoad(a) => kind::CALLDATALOAD | of(a),
            Node::Keccak(v, _) => kind::KECCAK | all(v),
            Node::KeccakMem(a, b, _) => kind::KECCAK_MEM | of(a) | of(b),
            Node::CallResult(_) => kind::CALL_RESULT,
            Node::CreateResult(_) => kind::CREATE_RESULT,
            Node::Var(_) => kind::VAR,
            Node::Arg(_) => kind::ARG,
            Node::ReturnData(_, a) => kind::RETURN_DATA | of(a),
            Node::CopiedWord(_, a, _) => kind::COPIED_WORD | of(a),
            Node::IntRet(..) => kind::INT_RET,
            Node::Unknown(_) => kind::UNKNOWN,
        }
    }

    fn bits_of(&self, n: &Node) -> u32 {
        let bits = |id: ExprId| u32::from(self.bits[id.0 as usize]);
        match n {
            Node::Const(c) => c.bits(),
            Node::Env(o, _) => match *o {
                op::CALLER | op::ADDRESS | op::ORIGIN | op::COINBASE => 160,
                op::TIMESTAMP
                | op::NUMBER
                | op::GASLIMIT
                | op::GAS
                | op::CALLDATASIZE
                | op::RETURNDATASIZE
                | op::CODESIZE
                | op::MSIZE
                | op::PC => 64,
                _ => 256,
            },
            Node::Op(o, v) => match *o {
                op::ISZERO | op::LT | op::GT | op::SLT | op::SGT | op::EQ => 1,
                op::AND => bits(v[0]).min(bits(v[1])),
                op::OR | op::XOR => bits(v[0]).max(bits(v[1])),
                op::SHR => match self.konst(v[0]) {
                    Some(s) => bits(v[1]).saturating_sub(s.low_u64().min(256) as u32),
                    None => 256,
                },
                op::SHL => match self.konst(v[0]) {
                    Some(s) => (bits(v[1]) + s.low_u64().min(256) as u32).min(256),
                    None => 256,
                },
                op::DIV => match self.konst(v[1]) {
                    Some(c) if c.is_zero() => 0,
                    Some(c) => bits(v[0]).saturating_sub(c.bits() - 1),
                    None => bits(v[0]),
                },
                op::MOD => self.konst(v[1]).map_or(256, |c| c.bits()),
                op::BYTE => 8,
                _ => 256,
            },
            Node::CallResult(_) => 1,
            Node::CreateResult(_) => 160,
            _ => 256,
        }
    }

    fn may_of(&self, n: &Node, bits: u32) -> U256 {
        let may = |id: ExprId| self.may[id.0 as usize];
        let shift = |v: &[ExprId], left: bool| match self.konst(v[0]) {
            Some(s) if s.fits_u64() && s.low_u64() < 256 => {
                let by = s.low_u64() as u32;
                if left {
                    may(v[1]) << by
                } else {
                    may(v[1]) >> by
                }
            }
            Some(_) => U256::ZERO,
            None => U256::MAX,
        };
        match n {
            Node::Const(c) => *c,
            Node::Op(op::AND, v) => may(v[0]) & may(v[1]),
            Node::Op(op::OR | op::XOR, v) => may(v[0]) | may(v[1]),
            Node::Op(op::SHL, v) => shift(v, true),
            Node::Op(op::SHR, v) => shift(v, false),
            _ => mask_bits(bits),
        }
    }
}

pub fn intern(n: Node) -> ExprId {
    ARENA.with(|a| {
        let mut a = a.borrow_mut();
        if let Some(id) = a.map.get(&n) {
            return *id;
        }
        let mut depth = a.depth_below(&n) + 1;
        let n = if depth > MAX_DEPTH {
            a.seq += 1;
            depth = 1;
            Node::Unknown(a.seq)
        } else {
            n
        };
        let bits = a.bits_of(&n);
        let may = a.may_of(&n, bits);
        let kinds = a.kinds_of(&n);
        let id = ExprId(a.nodes.len() as u32);
        a.nodes.push(n.clone());
        a.bits.push(bits as u16);
        a.may.push(may);
        a.depth.push(depth);
        a.kinds.push(kinds);
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
    with_node(id, |n| {
        if let Node::Const(v) = n {
            Some(*v)
        } else {
            None
        }
    })
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
        (U256::ONE << bits).wrapping_sub(U256::ONE)
    }
}

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
        op::DIV => a / b,
        op::SDIV => a.sdiv(b),
        op::MOD => a % b,
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
                b << a.low_u64() as u32
            }
        }
        op::SHR => {
            if a >= U256::from_u64(256) {
                U256::ZERO
            } else {
                b >> a.low_u64() as u32
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
            if let Node::Op(io, v) = node(a) {
                if io == op::SUB || io == op::XOR {
                    return op2(op::EQ, v[0], v[1]);
                }
            }
            if let Node::Op(op::ISZERO, v) = node(a) {
                if let Node::Op(op::ISZERO, w) = node(v[0]) {
                    return op1(op::ISZERO, w[0]);
                }
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

pub fn is_boolean(e: ExprId) -> bool {
    match node(e) {
        Node::Op(o, _) => matches!(o, op::LT | op::GT | op::SLT | op::SGT | op::EQ | op::ISZERO),
        Node::Const(c) => c.is_zero() || c == U256::ONE,
        Node::CallResult(_) => true,
        Node::Var(_) => BOOL_VARS.with(|b| b.borrow().contains(&e)),
        _ => false,
    }
}

thread_local! {
    static BOOL_VARS: RefCell<std::collections::HashSet<ExprId>> = RefCell::new(std::collections::HashSet::new());
}

pub fn mark_boolean(var: ExprId) {
    if matches!(node(var), Node::Var(_)) {
        BOOL_VARS.with(|b| b.borrow_mut().insert(var));
    }
}

pub fn may_bits(e: ExprId) -> U256 {
    ARENA.with(|a| a.borrow().may[e.0 as usize])
}

pub fn op2(o: u8, a: ExprId, b: ExprId) -> ExprId {
    let (ca, cb) = (as_const(a), as_const(b));
    if let (Some(x), Some(y)) = (ca, cb) {
        if let Some(r) = fold2(o, x, y) {
            return konst(r);
        }
    }
    let (a, b, ca, cb) = if is_commutative(o) && ca.is_some() && cb.is_none() {
        (b, a, cb, ca)
    } else {
        (a, b, ca, cb)
    };
    match o {
        op::ADD => {
            if cb == Some(U256::ZERO) {
                return a;
            }
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
            if let Some(c2) = cb {
                if let Node::Op(op::ADD, v) = node(a) {
                    if let Some(c1) = as_const(v[1]) {
                        return op2(op::ADD, v[0], konst(c1.wrapping_add(c2)));
                    }
                }
                if let Node::Op(op::SUB, v) = node(a) {
                    if let Some(c1) = as_const(v[1]) {
                        return if c2 >= c1 {
                            op2(op::ADD, v[0], konst(c2.wrapping_sub(c1)))
                        } else {
                            op2(op::SUB, v[0], konst(c1.wrapping_sub(c2)))
                        };
                    }
                }
                if c2.is_negative() && (-c2) < U256::from_u64(1 << 32) {
                    return intern(Node::Op(op::SUB, vec![a, konst(-c2)]));
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
            if let Node::Op(op::ADD, v) = node(a) {
                if v[0] == b {
                    return v[1];
                }
                if v[1] == b {
                    return v[0];
                }
                if let Node::Op(op::ADD, w) = node(b) {
                    if v[0] == w[0] {
                        if let (Some(c1), Some(c2)) = (as_const(v[1]), as_const(w[1])) {
                            return konst(c1.wrapping_sub(c2));
                        }
                    }
                }
            }
            if let Node::Op(op::SUB, v) = node(b) {
                if v[0] == a {
                    return v[1];
                }
            }
            if let Some(c2) = cb {
                if let Node::Op(op::ADD, v) = node(a) {
                    if let Some(c1) = as_const(v[1]) {
                        return if c1 >= c2 {
                            op2(op::ADD, v[0], konst(c1.wrapping_sub(c2)))
                        } else {
                            op2(op::SUB, v[0], konst(c2.wrapping_sub(c1)))
                        };
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
                if let Node::Op(op::AND, v) = node(a) {
                    if let Some(m1) = as_const(v[1]) {
                        return op2(op::AND, v[0], konst(m1 & m));
                    }
                }
                if m.is_low_mask() && m.bits() >= value_bits(a) {
                    return a;
                }
                let may = may_bits(a);
                if (may & !m).is_zero() {
                    return a;
                }
                if (may & m).is_zero() {
                    return konst(U256::ZERO);
                }
                if let Node::Op(op::OR, v) = node(a) {
                    if (may_bits(v[0]) & m).is_zero() {
                        return op2(op::AND, v[1], konst(m));
                    }
                    if (may_bits(v[1]) & m).is_zero() {
                        return op2(op::AND, v[0], konst(m));
                    }
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
            if let (Node::Op(op::AND, v), Node::Op(op::AND, w)) = (node(a), node(b)) {
                if v[0] == w[0] {
                    if let (Some(m1), Some(m2)) = (as_const(v[1]), as_const(w[1])) {
                        return op2(op::AND, v[0], konst(m1 | m2));
                    }
                }
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
            if ca == Some(U256::ZERO) {
                return b;
            }
            if let Some(s) = ca {
                if s >= U256::from_u64(256) {
                    return konst(U256::ZERO);
                }
                if let Node::Op(op::SHL, v) = node(b) {
                    if let Some(j) = as_const(v[0]) {
                        return op2(op::SHL, konst(s.wrapping_add(j)), v[1]);
                    }
                }
                // Only the side that survives the shift is rebuilt.
                // Rebuilding both to see which is zero doubled the work per level.
                if let (Node::Op(op::OR, v), true) = (node(b), s.fits_u64()) {
                    let gone = |x: ExprId| (may_bits(x) << s.low_u64() as u32).is_zero();
                    if gone(v[0]) {
                        return op2(op::SHL, a, v[1]);
                    }
                    if gone(v[1]) {
                        return op2(op::SHL, a, v[0]);
                    }
                }
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
                if let Node::Op(op::SHR, v) = node(b) {
                    if let Some(j) = as_const(v[0]) {
                        return op2(op::SHR, konst(s.wrapping_add(j)), v[1]);
                    }
                }
                if let (Node::Op(op::OR, v), true) = (node(b), s.fits_u64()) {
                    let gone = |x: ExprId| (may_bits(x) >> s.low_u64() as u32).is_zero();
                    if gone(v[0]) {
                        return op2(op::SHR, a, v[1]);
                    }
                    if gone(v[1]) {
                        return op2(op::SHR, a, v[0]);
                    }
                }
                if let Node::Op(op::SHL, v) = node(b) {
                    if as_const(v[0]) == Some(s) {
                        return op2(op::AND, v[1], konst(mask_bits(256 - s.low_u64() as u32)));
                    }
                }
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
            if cb == Some(U256::ZERO) {
                return op1(op::ISZERO, a);
            }
            if cb == Some(U256::ONE) && is_boolean(a) {
                return a;
            }
        }
        op::LT | op::GT | op::SLT | op::SGT => {
            if a == b {
                return konst(U256::ZERO);
            }
            if (o == op::LT && cb == Some(U256::ZERO)) || (o == op::GT && ca == Some(U256::ZERO)) {
                return konst(U256::ZERO);
            }
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

pub fn value_bits(e: ExprId) -> u32 {
    ARENA.with(|a| u32::from(a.borrow().bits[e.0 as usize]))
}

pub fn holds(e: ExprId, kinds: u16) -> bool {
    ARENA.with(|a| a.borrow().kinds[e.0 as usize] & kinds != 0)
}

pub fn depth(e: ExprId) -> u32 {
    ARENA.with(|a| a.borrow().depth[e.0 as usize])
}

pub fn size(e: ExprId) -> usize {
    fn go(e: ExprId, budget: &mut usize) -> usize {
        if *budget == 0 {
            return 1;
        }
        *budget -= 1;
        match node(e) {
            Node::Op(_, v) | Node::Keccak(v, _) => {
                1 + v.iter().map(|x| go(*x, budget)).sum::<usize>()
            }
            Node::MLoad(a, _)
            | Node::SLoad(a, _, _)
            | Node::CallDataLoad(a)
            | Node::ReturnData(_, a)
            | Node::CopiedWord(_, a, _) => 1 + go(a, budget),
            Node::KeccakMem(a, b, _) => 1 + go(a, budget) + go(b, budget),
            _ => 1,
        }
    }
    let mut budget = 10_000;
    go(e, &mut budget)
}

pub fn children(e: ExprId) -> Vec<ExprId> {
    match node(e) {
        Node::Op(_, v) | Node::Keccak(v, _) => v,
        Node::MLoad(a, _)
        | Node::SLoad(a, _, _)
        | Node::CallDataLoad(a)
        | Node::ReturnData(_, a)
        | Node::CopiedWord(_, a, _) => vec![a],
        Node::KeccakMem(a, b, _) => vec![a, b],
        _ => vec![],
    }
}

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

pub fn substitute(
    e: ExprId,
    f: &dyn Fn(&Node) -> Option<ExprId>,
    memo: &mut HashMap<ExprId, ExprId>,
) -> ExprId {
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
        Node::KeccakMem(a, b, ver) => intern(Node::KeccakMem(
            substitute(a, f, memo),
            substitute(b, f, memo),
            ver,
        )),
        _ => e,
    };
    memo.insert(e, r);
    r
}

pub fn restamp_memory(e: ExprId, version: u32, memo: &mut HashMap<ExprId, ExprId>) -> ExprId {
    if let Some(r) = memo.get(&e) {
        return *r;
    }
    let mut again = |x: ExprId| restamp_memory(x, version, memo);
    let r = match node(e) {
        Node::Op(o, v) => {
            let nv: Vec<ExprId> = v.iter().map(|x| again(*x)).collect();
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
            let nv: Vec<ExprId> = v.iter().map(|x| again(*x)).collect();
            intern(Node::Keccak(nv, t))
        }
        Node::MLoad(a, _) => intern(Node::MLoad(again(a), version)),
        Node::SLoad(a, t, ver) => intern(Node::SLoad(again(a), t, ver)),
        Node::CallDataLoad(a) => intern(Node::CallDataLoad(again(a))),
        Node::ReturnData(s, a) => intern(Node::ReturnData(s, again(a))),
        Node::CopiedWord(k, a, ver) => intern(Node::CopiedWord(k, again(a), ver)),
        Node::KeccakMem(a, b, _) => {
            let (a, b) = (again(a), again(b));
            intern(Node::KeccakMem(a, b, version))
        }
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
        assert_eq!(
            op2(op::DIV, x, konst(U256::ONE << 224)),
            op2(op::SHR, konst_u64(224), x)
        );
        assert_eq!(
            op1(op::ISZERO, op1(op::ISZERO, op2(op::EQ, x, konst_u64(3)))),
            op2(op::EQ, x, konst_u64(3))
        );
        assert_eq!(
            op2(
                op::AND,
                op2(op::AND, x, konst(mask_bits(160))),
                konst(mask_bits(160))
            ),
            op2(op::AND, x, konst(mask_bits(160)))
        );
        assert_eq!(
            op2(op::SUB, op2(op::ADD, x, konst_u64(10)), konst_u64(4)),
            op2(op::ADD, x, konst_u64(6))
        );
    }
}
