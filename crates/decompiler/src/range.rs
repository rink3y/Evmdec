use crate::expr::{self, ExprId, Node};
use crate::opcode as op;
use crate::solve::Item;
use crate::u256::U256;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Range {
    pub lo: U256,
    pub hi: U256,
}

const FULL: Range = Range {
    lo: U256::ZERO,
    hi: U256::MAX,
};
const FLAG: Range = Range {
    lo: U256::ZERO,
    hi: U256::ONE,
};
const MAX_DEPTH: u32 = 48;

// These two are assumptions about the chain, not facts about the code.
// A block time or number past 64 bits and a sent value past 128 bits are taken not to occur.
const CLOCK_BITS: u32 = 64;
const VALUE_BITS: u32 = 128;
const ADDRESS_BITS: u32 = 160;

fn below(bits: u32) -> Range {
    Range {
        lo: U256::ZERO,
        hi: (U256::ONE << bits).wrapping_sub(U256::ONE),
    }
}

fn exact(value: U256) -> Range {
    Range {
        lo: value,
        hi: value,
    }
}

fn product(a: U256, b: U256) -> Option<U256> {
    let out = a.wrapping_mul(b);
    (a.is_zero() || out / a == b).then_some(out)
}

fn sum(a: U256, b: U256) -> Option<U256> {
    let (out, carried) = a.overflowing_add(b);
    (!carried).then_some(out)
}

impl Range {
    fn meet(self, other: Range) -> Range {
        let (lo, hi) = (self.lo.max(other.lo), self.hi.min(other.hi));
        // Two bounds that exclude each other mean the path was misread. Keep the wider one.
        if lo > hi {
            self
        } else {
            Range { lo, hi }
        }
    }
}

#[derive(Default)]
pub struct Bounds {
    known: HashMap<ExprId, Range>,
    at_least: HashSet<(ExprId, ExprId)>,
}

impl Bounds {
    pub fn from_checks(items: &[Item]) -> Bounds {
        let mut bounds = Bounds::default();
        for item in items {
            if let Item::Check { cond, holds, .. } = item {
                bounds.learn(*cond, *holds, 0);
            }
        }
        bounds
    }

    fn narrow(&mut self, e: ExprId, to: Range) {
        let now = self.of(e).meet(to);
        self.known.insert(e, now);
    }

    fn order(&mut self, low: ExprId, high: ExprId, strict: bool) {
        let (l, h) = (self.of(low), self.of(high));
        let step = U256::from(strict);
        if let Some(least) = sum(l.lo, step) {
            self.narrow(
                high,
                Range {
                    lo: least,
                    hi: U256::MAX,
                },
            );
        }
        if h.hi >= step {
            self.narrow(
                low,
                Range {
                    lo: U256::ZERO,
                    hi: h.hi.wrapping_sub(step),
                },
            );
        }
        self.at_least.insert((high, low));
    }

    fn learn(&mut self, cond: ExprId, holds: bool, depth: u32) {
        if depth > MAX_DEPTH {
            return;
        }
        let Node::Op(o, parts) = expr::node(cond) else {
            return;
        };
        match (o, &parts[..]) {
            (op::ISZERO, [x]) if expr::is_boolean(*x) => self.learn(*x, !holds, depth + 1),
            (op::ISZERO, [x]) if holds => self.narrow(*x, exact(U256::ZERO)),
            (op::ISZERO, [x]) => self.order(expr::konst(U256::ZERO), *x, true),
            (op::LT, [a, b]) if holds => self.order(*a, *b, true),
            (op::LT, [a, b]) => self.order(*b, *a, false),
            (op::GT, [a, b]) if holds => self.order(*b, *a, true),
            (op::GT, [a, b]) => self.order(*a, *b, false),
            (op::EQ, [a, b]) if holds => {
                let both = self.of(*a).meet(self.of(*b));
                self.narrow(*a, both);
                self.narrow(*b, both);
            }
            (op::AND, [a, b]) if holds && expr::is_boolean(*a) && expr::is_boolean(*b) => {
                self.learn(*a, true, depth + 1);
                self.learn(*b, true, depth + 1);
            }
            (op::OR, [a, b]) if !holds => {
                self.learn(*a, false, depth + 1);
                self.learn(*b, false, depth + 1);
            }
            _ => {}
        }
    }

    pub fn of(&self, e: ExprId) -> Range {
        self.walk(e, 0, &mut HashMap::new())
    }

    // A value shared by both sides of many operations would otherwise be walked once per use.
    fn walk(&self, e: ExprId, depth: u32, done: &mut HashMap<ExprId, Range>) -> Range {
        if let Some(range) = done.get(&e) {
            return *range;
        }
        if depth > MAX_DEPTH {
            return self.known.get(&e).map_or(FULL, |known| FULL.meet(*known));
        }
        let shape = self.shape(e, depth + 1, done);
        let range = match self.known.get(&e) {
            Some(known) => shape.meet(*known),
            None => shape,
        };
        done.insert(e, range);
        range
    }

    fn shape(&self, e: ExprId, depth: u32, done: &mut HashMap<ExprId, Range>) -> Range {
        let (o, parts) = match expr::node(e) {
            Node::Const(c) => return exact(c),
            Node::Env(which, _) => {
                return match which {
                    op::CALLER | op::ORIGIN | op::ADDRESS | op::COINBASE => below(ADDRESS_BITS),
                    op::TIMESTAMP | op::NUMBER => below(CLOCK_BITS),
                    op::CALLVALUE | op::SELFBALANCE => below(VALUE_BITS),
                    _ => FULL,
                }
            }
            Node::CallResult(_) => return FLAG,
            Node::Op(o, parts) => (o, parts),
            _ => return FULL,
        };
        let sides: Vec<Range> = parts.iter().map(|p| self.walk(*p, depth, done)).collect();
        let at = |i: usize| sides[i];
        match (o, parts.len()) {
            (op::ISZERO, _) | (op::LT | op::GT | op::SLT | op::SGT | op::EQ, _) => FLAG,
            (op::AND, 2) => Range {
                lo: U256::ZERO,
                hi: at(0).hi.min(at(1).hi),
            },
            (op::OR | op::XOR, 2) => {
                let bits = 256 - at(0).hi.max(at(1).hi).leading_zeros();
                if bits >= 256 {
                    FULL
                } else {
                    below(bits)
                }
            }
            (op::ADD, 2) => match (sum(at(0).lo, at(1).lo), sum(at(0).hi, at(1).hi)) {
                (Some(lo), Some(hi)) => Range { lo, hi },
                _ => FULL,
            },
            (op::MUL, 2) => match (product(at(0).lo, at(1).lo), product(at(0).hi, at(1).hi)) {
                (Some(lo), Some(hi)) => Range { lo, hi },
                _ => FULL,
            },
            (op::SUB, 2) if at(0).lo >= at(1).hi => Range {
                lo: at(0).lo.wrapping_sub(at(1).hi),
                hi: at(0).hi.wrapping_sub(at(1).lo),
            },
            (op::SUB, 2) if self.at_least.contains(&(parts[0], parts[1])) => Range {
                lo: U256::ZERO,
                hi: at(0).hi,
            },
            (op::DIV, 2) => Range {
                lo: U256::ZERO,
                hi: at(0).hi / at(1).lo.max(U256::ONE),
            },
            (op::MOD, 2) if !at(1).hi.is_zero() => Range {
                lo: U256::ZERO,
                hi: at(0).hi.min(at(1).hi.wrapping_sub(U256::ONE)),
            },
            (op::SHR, 2) => match expr::as_const(parts[0]).filter(U256::fits_u64) {
                Some(by) if by.low_u64() < 256 => Range {
                    lo: U256::ZERO,
                    hi: at(1).hi >> by.low_u64() as u32,
                },
                _ => FULL,
            },
            _ => FULL,
        }
    }

    pub fn may_wrap(&self, e: ExprId) -> bool {
        let Node::Op(o, parts) = expr::node(e) else {
            return false;
        };
        let [a, b] = parts[..] else {
            return false;
        };
        let (x, y) = (self.of(a), self.of(b));
        match o {
            op::ADD => sum(x.hi, y.hi).is_none(),
            op::MUL => product(x.hi, y.hi).is_none(),
            op::SUB => x.lo < y.hi && !self.at_least.contains(&(a, b)),
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn word(index: u64) -> ExprId {
        expr::calldataload(expr::konst_u64(4 + 32 * index))
    }

    fn check(cond: ExprId, holds: bool) -> Item {
        Item::Check { cond, holds, pc: 0 }
    }

    #[test]
    fn two_masked_words_cannot_wrap_a_product_and_two_bare_words_can() {
        let mask = expr::konst_u64(0xffff);
        let narrow = |i| expr::op2(op::AND, word(i), mask);
        let none = Bounds::default();
        assert!(!none.may_wrap(expr::op2(op::MUL, narrow(0), narrow(1))));
        assert!(none.may_wrap(expr::op2(op::MUL, word(0), word(1))));
    }

    #[test]
    fn a_check_on_the_path_bounds_the_word_it_tests() {
        let limit = expr::konst(U256::ONE << 100);
        let items = [
            check(expr::op2(op::LT, word(0), limit), true),
            check(expr::op2(op::LT, word(1), limit), true),
        ];
        let bounds = Bounds::from_checks(&items);
        assert_eq!(
            bounds.of(word(0)).hi,
            (U256::ONE << 100).wrapping_sub(U256::ONE)
        );
        assert!(!bounds.may_wrap(expr::op2(op::ADD, word(0), word(1))));
        assert!(!bounds.may_wrap(expr::op2(op::MUL, word(0), word(1))));
    }

    #[test]
    fn a_value_doubled_many_times_is_bounded_without_walking_every_copy() {
        let mut value = expr::op2(op::AND, word(0), expr::konst_u64(1));
        for _ in 0..40 {
            let next = expr::op2(op::ADD, value, expr::konst_u64(1));
            value = expr::op2(op::MUL, value, next);
        }
        assert_eq!(Bounds::default().of(value).lo, U256::ZERO);
    }

    #[test]
    fn a_difference_is_safe_once_the_path_shows_the_first_is_not_smaller() {
        let difference = expr::op2(op::SUB, word(0), word(1));
        assert!(Bounds::default().may_wrap(difference));
        let items = [check(expr::op2(op::LT, word(0), word(1)), false)];
        assert!(!Bounds::from_checks(&items).may_wrap(difference));
    }
}
