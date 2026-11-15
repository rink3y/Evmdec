use crate::decompile::Contract;
use crate::emit::MappingLayout;
use crate::expr::{self, ExprId, Node};
use crate::lift::Stmt;
use crate::opcode as op;
use crate::ssa::{self, ShapeStep, Step};
use crate::types::{Loc, Ty, TypeEnv};
use crate::u256::U256;
use std::collections::HashSet;

pub(crate) fn is_ledger(c: &Contract, root: U256) -> bool {
    let layout = c.compiler.layout;
    let entry_of = |key: ExprId| is_entry_of(key, root, layout);
    let reads_entry = |e: ExprId| -> bool { sload_keys(e).into_iter().any(entry_of) };
    for f in &c.functions {
        let Some(l) = &f.lifted else { continue };
        for nd in &l.nodes {
            for st in &nd.stmts {
                match st {
                    Stmt::SStore {
                        key,
                        val,
                        transient: false,
                        ..
                    } if entry_of(*key) && minuends(*val).into_iter().any(reads_entry) => {
                        return true;
                    }
                    Stmt::Call {
                        value, input_head, ..
                    } if value.is_some_and(reads_entry)
                        || input_head.iter().any(|w| reads_entry(*w)) =>
                    {
                        return true;
                    }
                    _ => {}
                }
            }
        }
    }
    false
}

pub(crate) fn balance_mappings(env: &TypeEnv) -> Vec<U256> {
    let mut out: Vec<U256> = Vec::new();
    for loc in env.locations() {
        let Loc::Slot(shape) = loc else { continue };
        if shape.steps != [ShapeStep::Key] || out.contains(&shape.root) {
            continue;
        }
        let key_addr = env
            .key_type(shape.root, &[ShapeStep::Key])
            .is_some_and(|t| t == "address");
        let Some(info) = env.info(loc) else { continue };
        let val_num = match info.ty {
            Ty::Uint(n) => n >= 8,
            Ty::Unknown => info.arith || info.arith_def,
            _ => false,
        };
        if key_addr && val_num {
            out.push(shape.root);
        }
    }
    out
}

fn is_entry_of(key: ExprId, root: U256, layout: MappingLayout) -> bool {
    ssa::slot_path(key, layout)
        .is_some_and(|p| p.root == root && matches!(p.steps[..], [Step::Key(_)]))
}

fn sload_keys(e: ExprId) -> Vec<ExprId> {
    let mut keys = Vec::new();
    walk(e, &mut |n| {
        if let Node::SLoad(k, false, _) = n {
            keys.push(*k);
        }
    });
    keys
}

fn minuends(e: ExprId) -> Vec<ExprId> {
    let mut out = Vec::new();
    walk(e, &mut |n| {
        if let Node::Op(op::SUB, v) = n {
            out.extend(v.first().copied());
        }
    });
    out
}

fn walk(e: ExprId, visit: &mut impl FnMut(&Node)) {
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 20_000 {
            continue;
        }
        let n = expr::node(x);
        visit(&n);
        stack.extend(expr::children(x));
    }
}
