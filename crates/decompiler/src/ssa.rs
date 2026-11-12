use crate::emit::{hashed_slot, MappingLayout, SlotSpace};
use crate::expr::{self, ExprId, Node};
use crate::lift::{Lifted, Stmt, Term};
use crate::opcode as op;
use crate::u256::U256;
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Step {
    Key(ExprId),
    Index(ExprId),
    Offset(u64),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SlotPath {
    pub root: U256,
    pub steps: Vec<Step>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ShapeStep {
    Key,
    Index,
    Offset(u64),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Shape {
    pub root: U256,
    pub steps: Vec<ShapeStep>,
    pub space: SlotSpace,
}

impl SlotPath {
    pub fn shape(&self, space: SlotSpace) -> Shape {
        Shape {
            root: self.root,
            steps: self
                .steps
                .iter()
                .map(|s| match s {
                    Step::Key(_) => ShapeStep::Key,
                    Step::Index(_) => ShapeStep::Index,
                    Step::Offset(o) => ShapeStep::Offset(*o),
                })
                .collect(),
            space,
        }
    }
}

pub fn space_of(transient: bool) -> SlotSpace {
    if transient {
        SlotSpace::Transient
    } else {
        SlotSpace::Persistent
    }
}

fn key_and_slot(words: &[ExprId], layout: MappingLayout) -> (ExprId, ExprId) {
    let small = |e: ExprId| expr::as_const(e).is_some_and(|c| c.bits() <= 16);
    if layout == MappingLayout::Vyper || (small(words[0]) && !small(words[1])) {
        (words[1], words[0])
    } else {
        (words[0], words[1])
    }
}

const MAX_PATH_DEPTH: u32 = 8;

pub fn slot_path(key: ExprId, layout: MappingLayout) -> Option<SlotPath> {
    slot_path_at(key, layout, 0)
}

fn precomputed_element(c: U256) -> Option<Option<(U256, u64)>> {
    match hashed_slot(c) {
        Some((root, k)) if k >= 0 => Some(Some((root, k as u64))),
        Some(_) => None,
        None => Some(None),
    }
}

fn slot_path_at(key: ExprId, layout: MappingLayout, depth: u32) -> Option<SlotPath> {
    if depth > MAX_PATH_DEPTH {
        return None;
    }
    if let Some(c) = expr::as_const(key) {
        return Some(match precomputed_element(c)? {
            Some((root, k)) => SlotPath {
                root,
                steps: vec![Step::Index(expr::konst_u64(k))],
            },
            None => SlotPath {
                root: c,
                steps: Vec::new(),
            },
        });
    }
    match expr::node(key) {
        Node::Keccak(words, 0) if words.len() == 2 => {
            let (k, slot) = key_and_slot(&words, layout);
            let mut p = slot_path_at(slot, layout, depth + 1)?;
            p.steps.push(Step::Key(k));
            Some(p)
        }
        Node::Keccak(words, 0) if words.len() == 1 => {
            let mut p = slot_path_at(words[0], layout, depth + 1)?;
            p.steps.push(Step::Index(expr::konst(U256::ZERO)));
            Some(p)
        }
        Node::Op(op::ADD, v) => {
            for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
                if let Node::Keccak(w, 0) = expr::node(a) {
                    if w.len() == 1 {
                        let mut p = slot_path_at(w[0], layout, depth + 1)?;
                        p.steps.push(Step::Index(b));
                        return Some(p);
                    }
                }
                if let Some(Some((root, k))) = expr::as_const(a).and_then(precomputed_element) {
                    let idx = if k == 0 {
                        b
                    } else {
                        expr::op2(op::ADD, b, expr::konst_u64(k))
                    };
                    return Some(SlotPath {
                        root,
                        steps: vec![Step::Index(idx)],
                    });
                }
            }
            for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
                if let Some(c) = expr::as_const(b) {
                    if c.fits_u64() && c.low_u64() < 1 << 16 {
                        let mut p = slot_path_at(a, layout, depth + 1)?;
                        p.steps.push(Step::Offset(c.low_u64()));
                        return Some(p);
                    }
                }
            }
            for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
                if let Some(mut p) = slot_path_at(a, layout, depth + 1) {
                    p.steps.push(Step::Index(b));
                    return Some(p);
                }
            }
            None
        }
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FieldRef {
    pub key: ExprId,
    pub bit_offset: u32,
    pub bits: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FieldWrite {
    pub bit_offset: u32,
    pub bits: u32,
    pub value: ExprId,
}

fn shifted_slot(e: ExprId) -> Option<(ExprId, u32)> {
    match expr::node(e) {
        Node::SLoad(k, false, _) => Some((k, 0)),
        Node::Op(op::SHR, w) => {
            let s = expr::as_const(w[0])?;
            let Node::SLoad(k, false, _) = expr::node(w[1]) else {
                return None;
            };
            (s.fits_u64() && s.low_u64().is_multiple_of(8) && s.low_u64() < 256)
                .then(|| (k, s.low_u64() as u32))
        }
        Node::Op(op::DIV, w) => {
            let d = expr::as_const(w[1])?;
            let Node::SLoad(k, false, _) = expr::node(w[0]) else {
                return None;
            };
            (d.is_power_of_two() && d.trailing_zeros().is_multiple_of(8) && d.trailing_zeros() > 0)
                .then(|| (k, d.trailing_zeros()))
        }
        _ => None,
    }
}

pub fn field_read(e: ExprId) -> Option<FieldRef> {
    let field = |key, bit_offset, bits| FieldRef {
        key,
        bit_offset,
        bits,
    };
    match expr::node(e) {
        Node::Op(op::AND, v) => {
            let m = expr::as_const(v[1])?;
            if !m.is_low_mask() {
                return None;
            }
            let (k, s) = shifted_slot(v[0])?;
            (s + m.bits() <= 256 && (s > 0 || m.bits() < 256)).then(|| field(k, s, m.bits()))
        }
        Node::Op(op::SIGNEXTEND, v) => {
            let nb = expr::as_const(v[0])?;
            if !nb.fits_u64() || nb.low_u64() >= 31 {
                return None;
            }
            let (k, s) = shifted_slot(v[1])?;
            let bits = 8 * (nb.low_u64() as u32 + 1);
            (s + bits <= 256).then(|| field(k, s, bits))
        }
        Node::Op(op::SHR, _) | Node::Op(op::DIV, _) => {
            let (k, s) = shifted_slot(e)?;
            (s > 0).then(|| field(k, s, 256 - s))
        }
        _ => None,
    }
}

fn shifted_then_masked(e: ExprId) -> Option<FieldWrite> {
    let Node::Op(op::AND, w) = expr::node(e) else {
        return None;
    };
    [(w[0], w[1]), (w[1], w[0])].into_iter().find_map(|(m, x)| {
        let m = expr::as_const(m)?;
        let shift = m.trailing_zeros();
        let Node::Op(op::SHL, v) = expr::node(x) else {
            return None;
        };
        let moved = expr::as_const(v[0]).filter(|s| s.fits_u64())?.low_u64();
        (shift > 0 && shift < 256 && moved == u64::from(shift) && (m >> shift).is_low_mask()).then(
            || FieldWrite {
                bit_offset: shift,
                bits: m.count_ones(),
                value: v[1],
            },
        )
    })
}

pub fn field_writes(key: ExprId, val: ExprId) -> Vec<FieldWrite> {
    if let Some(w) = field_write(key, val) {
        return vec![w];
    }
    let mut leaves = Vec::new();
    let mut pending = vec![val];
    while let Some(e) = pending.pop() {
        match expr::node(e) {
            Node::Op(op::OR, v) if leaves.len() + pending.len() < 16 => pending.extend(v),
            _ => leaves.push(e),
        }
    }
    let kept = |e: ExprId| match expr::node(e) {
        Node::Op(op::AND, w) => [(w[0], w[1]), (w[1], w[0])].into_iter().find_map(|(a, b)| {
            matches!(expr::node(a), Node::SLoad(k, false, _) if k == key)
                .then(|| expr::as_const(b))
                .flatten()
        }),
        _ => None,
    };
    let Some(keep) = leaves.iter().find_map(|e| kept(*e)) else {
        return Vec::new();
    };
    let cleared = !keep;
    let run_at = |shift: u32| (!(cleared >> shift)).trailing_zeros();
    let low_masked = |e: ExprId| match expr::node(e) {
        Node::Op(op::AND, w) => [(w[0], w[1]), (w[1], w[0])].into_iter().find_map(|(m, x)| {
            expr::as_const(m)
                .filter(|m| m.is_low_mask())
                .map(|m| (m.bits(), x))
        }),
        _ => None,
    };
    let mut out = Vec::new();
    for leaf in leaves.into_iter().filter(|e| kept(*e).is_none()) {
        let found = shifted_then_masked(leaf).or_else(|| match expr::node(leaf) {
            Node::Op(op::SHL, v) => {
                let shift = expr::as_const(v[0]).filter(|s| s.fits_u64())?.low_u64();
                let shift = u32::try_from(shift).ok().filter(|s| *s < 256)?;
                let (bits, value) = low_masked(v[1]).unwrap_or((run_at(shift), v[1]));
                Some(FieldWrite {
                    bit_offset: shift,
                    bits,
                    value,
                })
            }
            _ => {
                let (bits, value) = low_masked(leaf).unwrap_or((run_at(0), leaf));
                Some(FieldWrite {
                    bit_offset: 0,
                    bits,
                    value,
                })
            }
        });
        match found {
            Some(w) if w.bits > 0 && w.bits < 256 && run_at(w.bit_offset) >= w.bits => out.push(w),
            _ => return Vec::new(),
        }
    }
    out
}

pub fn field_write(key: ExprId, val: ExprId) -> Option<FieldWrite> {
    if let Node::Op(op::AND, w) = expr::node(val) {
        for (a, b) in [(w[0], w[1]), (w[1], w[0])] {
            let (Node::SLoad(k, false, _), Some(keep)) = (expr::node(a), expr::as_const(b)) else {
                continue;
            };
            let field = !keep;
            let shift = field.trailing_zeros();
            if k == key && !field.is_zero() && (field >> shift).is_low_mask() {
                return Some(FieldWrite {
                    bit_offset: shift,
                    bits: (field >> shift).bits(),
                    value: expr::konst(U256::ZERO),
                });
            }
        }
        return None;
    }
    let Node::Op(op::OR, v) = expr::node(val) else {
        return None;
    };
    let cleared_bits = |e: ExprId| -> Option<u32> {
        let Node::Op(op::AND, w) = expr::node(e) else {
            return None;
        };
        for (a, b) in [(w[0], w[1]), (w[1], w[0])] {
            if let (Node::SLoad(k, false, _), Some(m)) = (expr::node(a), expr::as_const(b)) {
                if k == key {
                    return Some(256 - m.count_ones());
                }
            }
        }
        None
    };
    for (old, new) in [(v[0], v[1]), (v[1], v[0])] {
        let Some(cleared) = cleared_bits(old) else {
            continue;
        };
        if let Some(w) = shifted_then_masked(new) {
            return Some(w);
        }
        let (shift, inner) = match expr::node(new) {
            Node::Op(op::SHL, w) if expr::as_const(w[0]).is_some_and(|s| s.fits_u64()) => {
                (expr::as_const(w[0]).map_or(0, |s| s.low_u64() as u32), w[1])
            }
            Node::Op(op::MUL, w) => match (expr::as_const(w[0]), expr::as_const(w[1])) {
                (Some(c), _) if c.is_power_of_two() => (c.trailing_zeros(), w[1]),
                (_, Some(c)) if c.is_power_of_two() => (c.trailing_zeros(), w[0]),
                _ => (0, new),
            },
            _ => (0, new),
        };
        let (bits, value) = match expr::node(inner) {
            Node::Op(op::AND, w) => match (expr::as_const(w[0]), expr::as_const(w[1])) {
                (_, Some(m)) if m.is_low_mask() => (m.bits(), w[0]),
                (Some(m), _) if m.is_low_mask() => (m.bits(), w[1]),
                _ => (cleared, inner),
            },
            _ => (cleared, inner),
        };
        if bits > 0 && shift + bits <= 256 {
            return Some(FieldWrite {
                bit_offset: shift,
                bits,
                value,
            });
        }
    }
    None
}

pub fn phi_defs(l: &Lifted) -> HashMap<ExprId, Vec<ExprId>> {
    let mut defs: HashMap<ExprId, Vec<ExprId>> = HashMap::new();
    for assigns in l.edge_assigns.values() {
        for (var, val) in assigns {
            defs.entry(*var).or_default().push(*val);
        }
    }
    for nd in &l.nodes {
        for s in &nd.stmts {
            if let Stmt::Assign { var, value } = s {
                defs.entry(*var).or_default().push(*value);
            }
        }
    }
    defs
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallSite {
    pub callee: usize,
    pub seq: u32,
    pub args: Vec<(u32, ExprId)>,
    pub results: Vec<(u16, ExprId)>,
}

pub fn call_sites(l: &Lifted, arity: impl Fn(usize) -> Option<usize>) -> Vec<CallSite> {
    let mut out = Vec::new();
    for nd in &l.nodes {
        for s in &nd.stmts {
            let Stmt::Internal {
                seq,
                callee,
                args,
                results,
                ..
            } = s
            else {
                continue;
            };
            let Some(k) = arity(*callee) else { continue };
            let bound = args
                .iter()
                .enumerate()
                .filter(|(j, _)| *j < k)
                .map(|(j, a)| (j as u32, *a))
                .collect();
            out.push(CallSite {
                callee: *callee,
                seq: *seq,
                args: bound,
                results: results
                    .iter()
                    .enumerate()
                    .map(|(j, r)| (j as u16, *r))
                    .collect(),
            });
        }
    }
    out
}

pub fn arity(l: &Lifted) -> usize {
    l.ret_slot.map_or(l.n_args, |k| k as usize)
}

pub fn returns(l: &Lifted) -> Vec<&[ExprId]> {
    l.nodes
        .iter()
        .filter_map(|nd| match &nd.term {
            Term::InternalReturn(v) => Some(v.as_slice()),
            _ => None,
        })
        .collect()
}

pub fn stored_address_slot(e: ExprId) -> Option<ExprId> {
    let inner = match expr::node(e) {
        Node::Op(op::AND, v) if expr::as_const(v[1]).is_some_and(|m| m.is_low_mask()) => v[0],
        _ => e,
    };
    match expr::node(inner) {
        Node::SLoad(k, false, _) if expr::is_const(k) => Some(k),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn k(n: u64) -> ExprId {
        expr::konst_u64(n)
    }

    #[test]
    fn mapping_in_mapping_with_struct_member() {
        let key_j = expr::var(7);
        let key_k = expr::var(8);
        let inner = expr::intern(Node::Keccak(vec![key_j, k(5)], 0));
        let outer = expr::intern(Node::Keccak(vec![key_k, inner], 0));
        let member = expr::op2(op::ADD, outer, k(1));
        let p = slot_path(member, MappingLayout::Solidity).expect("path");
        assert_eq!(p.root, U256::from_u64(5));
        assert_eq!(
            p.steps,
            vec![Step::Key(key_j), Step::Key(key_k), Step::Offset(1)]
        );
        assert_eq!(
            p.shape(SlotSpace::Persistent).steps,
            vec![ShapeStep::Key, ShapeStep::Key, ShapeStep::Offset(1)]
        );
    }

    #[test]
    fn vyper_hashes_the_slot_first() {
        let key = expr::var(9);
        let e = expr::intern(Node::Keccak(vec![k(3), key], 0));
        let p = slot_path(e, MappingLayout::Vyper).expect("path");
        assert_eq!(p.root, U256::from_u64(3));
        assert_eq!(p.steps, vec![Step::Key(key)]);
        let p = slot_path(e, MappingLayout::Solidity).expect("path");
        assert_eq!(p.root, U256::from_u64(3));
    }

    #[test]
    fn dynamic_array_element_and_precomputed_hash() {
        let i = expr::var(10);
        let data = expr::intern(Node::Keccak(vec![k(2)], 0));
        let e = expr::op2(op::ADD, data, i);
        let p = slot_path(e, MappingLayout::Solidity).expect("path");
        assert_eq!(p.root, U256::from_u64(2));
        assert_eq!(p.steps, vec![Step::Index(i)]);
        let h = U256::from_be_bytes(&crate::keccak::keccak256(&U256::from_u64(2).to_be_bytes()));
        let p = slot_path(
            expr::konst(h.wrapping_add(U256::from_u64(3))),
            MappingLayout::Solidity,
        )
        .expect("path");
        assert_eq!(p.root, U256::from_u64(2));
        assert_eq!(p.steps, vec![Step::Index(k(3))]);
        assert_eq!(
            slot_path(
                expr::konst(h.wrapping_sub(U256::from_u64(3))),
                MappingLayout::Solidity
            ),
            None
        );
    }

    #[test]
    fn packed_field_read_and_write() {
        let slot = expr::intern(Node::SLoad(k(4), false, 0));
        let read = expr::op2(
            op::AND,
            expr::op2(op::SHR, k(160), slot),
            expr::konst(expr::mask_bits(32)),
        );
        assert_eq!(
            field_read(read),
            Some(FieldRef {
                key: k(4),
                bit_offset: 160,
                bits: 32
            })
        );
        let value = expr::var(11);
        let cleared = expr::op2(op::AND, slot, expr::konst(!(expr::mask_bits(32) << 160)));
        let placed = expr::op2(
            op::SHL,
            k(160),
            expr::op2(op::AND, value, expr::konst(expr::mask_bits(32))),
        );
        let written = expr::op2(op::OR, cleared, placed);
        assert_eq!(
            field_write(k(4), written),
            Some(FieldWrite {
                bit_offset: 160,
                bits: 32,
                value
            })
        );
    }
}
