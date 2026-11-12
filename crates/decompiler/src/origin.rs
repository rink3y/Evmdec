use crate::emit::MappingLayout;
use crate::expr::{self, ExprId, Node};
use crate::opcode as op;
use crate::ssa;
use crate::u256::U256;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Origin(u16);

impl Origin {
    pub const NONE: Origin = Origin(0);
    pub const CONSTANT: Origin = Origin(1);
    pub const CALLER: Origin = Origin(1 << 1);
    pub const INPUT: Origin = Origin(1 << 2);
    pub const VALUE: Origin = Origin(1 << 3);
    pub const BLOCK: Origin = Origin(1 << 4);
    pub const SELF: Origin = Origin(1 << 5);
    pub const RETURNED: Origin = Origin(1 << 6);
    pub const GATED: Origin = Origin(1 << 7);
    pub const UNSET: Origin = Origin(1 << 8);
    pub const OTHER: Origin = Origin(1 << 9);

    pub fn with(self, other: Origin) -> Origin {
        Origin(self.0 | other.0)
    }

    pub fn has(self, other: Origin) -> bool {
        self.0 & other.0 != 0
    }

    // Whoever calls decides the value: it is an argument, or it is the caller itself.
    pub fn open(self) -> bool {
        self.has(Origin::INPUT) || self.has(Origin::CALLER)
    }
}

pub type Loc = (U256, usize);

#[derive(Clone, Copy, Debug)]
pub struct Store {
    pub loc: Loc,
    pub gated: bool,
    pub value: ExprId,
    pub by: usize,
}

#[derive(Clone, Debug)]
pub struct Model {
    layout: MappingLayout,
    slots: HashMap<Loc, Origin>,
    direct: HashSet<Loc>,
}

const ROUNDS: usize = 8;
const MAX_NODES: usize = 4_000;

pub fn loc_of(key: ExprId, layout: MappingLayout) -> Option<Loc> {
    let path = ssa::slot_path(key, layout)?;
    let keyed = path
        .steps
        .iter()
        .filter(|s| !matches!(s, ssa::Step::Offset(_)))
        .count();
    Some((path.root, keyed))
}

impl Model {
    pub fn build(stores: &[Store], layout: MappingLayout) -> Model {
        let mut model = Model {
            layout,
            slots: stores.iter().map(|s| (s.loc, Origin::NONE)).collect(),
            direct: HashSet::new(),
        };
        for store in stores.iter().filter(|s| !s.gated) {
            // A packed field is written as the old word with the field replaced.
            let layout = model.layout;
            let elsewhere = expr::contains(store.value, &|n| match n {
                Node::SLoad(k, false, _) => loc_of(*k, layout) != Some(store.loc),
                _ => false,
            });
            if !elsewhere && model.of_inputs(store.value).open() {
                model.direct.insert(store.loc);
            }
        }
        for _ in 0..ROUNDS {
            let mut changed = false;
            for store in stores {
                let add = match store.gated {
                    true => Origin::GATED,
                    false => model.of(store.value),
                };
                let held = model.slots.entry(store.loc).or_default();
                let next = held.with(add);
                changed |= next != *held;
                *held = next;
            }
            if !changed {
                break;
            }
        }
        model
    }

    pub fn slot(&self, loc: Loc) -> Origin {
        self.slots.get(&loc).copied().unwrap_or(Origin::UNSET)
    }

    // An ungated function stores an argument or the caller there without reading storage.
    pub fn set_directly(&self, loc: Loc) -> bool {
        self.direct.contains(&loc)
    }

    fn of_inputs(&self, e: ExprId) -> Origin {
        self.walk(e, false)
    }

    pub fn of(&self, e: ExprId) -> Origin {
        self.walk(e, true)
    }

    fn walk(&self, e: ExprId, through_storage: bool) -> Origin {
        let mut out = Origin::NONE;
        let mut seen = HashSet::new();
        let mut stack = vec![e];
        while let Some(x) = stack.pop() {
            if !seen.insert(x) {
                continue;
            }
            if seen.len() > MAX_NODES {
                return out.with(Origin::OTHER);
            }
            let add = match expr::node(x) {
                Node::Const(_) => Origin::CONSTANT,
                Node::Env(o, _) => match o {
                    op::CALLER | op::ORIGIN => Origin::CALLER,
                    op::CALLVALUE => Origin::VALUE,
                    op::ADDRESS | op::SELFBALANCE | op::CODESIZE => Origin::SELF,
                    op::CALLDATASIZE => Origin::INPUT,
                    op::TIMESTAMP | op::NUMBER | op::PREVRANDAO | op::COINBASE => Origin::BLOCK,
                    op::GASLIMIT | op::CHAINID | op::BASEFEE | op::BLOBBASEFEE => Origin::BLOCK,
                    _ => Origin::OTHER,
                },
                Node::CallDataLoad(_) | Node::CopiedWord(op::CALLDATACOPY, ..) => Origin::INPUT,
                Node::ReturnData(..) | Node::CallResult(_) | Node::CreateResult(_) => {
                    Origin::RETURNED
                }
                Node::SLoad(..) if !through_storage => Origin::NONE,
                Node::SLoad(key, false, _) => match loc_of(key, self.layout) {
                    Some(loc) => self.slot(loc),
                    None => Origin::OTHER,
                },
                Node::Op(..) | Node::Keccak(..) => {
                    stack.extend(expr::children(x));
                    Origin::NONE
                }
                _ => Origin::OTHER,
            };
            out = out.with(add);
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn slot(n: u64) -> ExprId {
        expr::intern(Node::SLoad(expr::konst_u64(n), false, 0))
    }

    fn store(n: u64, gated: bool, value: ExprId) -> Store {
        Store {
            loc: (U256::from_u64(n), 0),
            gated,
            value,
            by: 0,
        }
    }

    #[test]
    fn an_argument_reaches_a_slot_through_another_slot() {
        let argument = expr::calldataload(expr::konst_u64(4));
        let stores = [store(1, false, argument), store(2, false, slot(1))];
        let model = Model::build(&stores, MappingLayout::default());
        assert!(model.slot((U256::from_u64(2), 0)).open());
        assert!(model.set_directly((U256::from_u64(1), 0)));
        assert!(!model.set_directly((U256::from_u64(2), 0)));
    }

    #[test]
    fn a_store_behind_a_gate_carries_only_the_gate() {
        let argument = expr::calldataload(expr::konst_u64(4));
        let stores = [store(1, true, argument), store(2, false, slot(1))];
        let model = Model::build(&stores, MappingLayout::default());
        let held = model.slot((U256::from_u64(2), 0));
        assert!(held.has(Origin::GATED) && !held.open());
        assert_eq!(model.slot((U256::from_u64(9), 0)), Origin::UNSET);
    }
}
