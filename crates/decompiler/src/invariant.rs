use crate::analyze::{display_name, push, Confidence, Finding, Severity};
use crate::decompile::{Contract, Function};
use crate::emit::MappingLayout;
use crate::exec;
use crate::expr::{self, ExprId, Node};
use crate::function::{FnKind, Mutability};
use crate::hex;
use crate::keccak;
use crate::lift::{self, Stmt};
use crate::opcode as op;
use crate::ssa::{self, ShapeStep, Step};
use crate::types::{Loc, Ty, TypeEnv};
use crate::u256::U256;
use std::collections::{HashMap, HashSet};

const STEP_BUDGET: usize = 120_000;
const MAX_ATTEMPTS: usize = 200;

pub fn findings(c: &Contract, env: &TypeEnv, out: &mut Vec<Finding>) {
    if std::env::var("EVMDEC_NO_CONFIRM").is_ok() || c.info.runtime.is_empty() {
        return;
    }
    let ledgers: Vec<Ledger> = balance_mappings(env)
        .into_iter()
        .filter(|l| is_ledger(c, l.root) && !is_signed(c, env, l.root))
        .collect();
    if ledgers.is_empty() {
        return;
    }
    self_credit(c, &ledgers, out);
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct Ledger {
    pub(crate) root: U256,
    pub(crate) compared_unsigned: bool,
}

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

pub(crate) fn balance_mappings(env: &TypeEnv) -> Vec<Ledger> {
    let mut out: Vec<Ledger> = Vec::new();
    for loc in env.locations() {
        let Loc::Slot(shape) = loc else { continue };
        if shape.steps != [ShapeStep::Key] || out.iter().any(|l| l.root == shape.root) {
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
            out.push(Ledger {
                root: shape.root,
                compared_unsigned: info.unsigned_cmp,
            });
        }
    }
    out
}

fn is_signed(c: &Contract, env: &TypeEnv, root: U256) -> bool {
    let layout = c.compiler.layout;
    let entry_of = |key: ExprId| is_entry_of(key, root, layout);
    let feeds_entry = |a: ExprId| arith_sload_keys(a).into_iter().any(entry_of);
    let arity = |pc: usize| {
        c.functions
            .iter()
            .find(|g| g.pc == pc)
            .and_then(|g| g.lifted.as_ref())
            .map(ssa::arity)
    };
    for f in &c.functions {
        let Some(l) = &f.lifted else { continue };
        for nd in &l.nodes {
            for e in lift::node_exprs(nd) {
                let mut operands = Vec::new();
                walk(e, &mut |n| {
                    if let Node::Op(
                        op::SDIV | op::SMOD | op::SLT | op::SGT | op::SAR | op::SIGNEXTEND,
                        v,
                    ) = n
                    {
                        operands.extend(v.iter().copied());
                    }
                });
                if operands.into_iter().any(feeds_entry) {
                    return true;
                }
            }
        }
        for site in ssa::call_sites(l, arity) {
            let Some(k) = arity(site.callee) else {
                continue;
            };
            for (idx, val) in site.args {
                let slot = (k - 1 - idx as usize) as u32;
                let param = Loc::Arg {
                    unit: site.callee,
                    slot,
                };
                if env.info(&param).is_some_and(|i| i.signed_cmp) && feeds_entry(val) {
                    return true;
                }
            }
        }
    }
    false
}

fn is_entry_of(key: ExprId, root: U256, layout: MappingLayout) -> bool {
    ssa::slot_path(key, layout)
        .is_some_and(|p| p.root == root && matches!(p.steps[..], [Step::Key(_)]))
}

fn arith_sload_keys(e: ExprId) -> Vec<ExprId> {
    let mut keys = Vec::new();
    let mut stack = vec![e];
    let mut seen = HashSet::new();
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 20_000 {
            continue;
        }
        match expr::node(x) {
            Node::SLoad(k, false, _) => keys.push(k),
            Node::Op(op::ADD | op::SUB | op::MUL, v) => stack.extend(v),
            _ => {}
        }
    }
    keys
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

fn entry_key(root: U256, account: U256, layout: MappingLayout) -> U256 {
    let mut pre = Vec::with_capacity(64);
    if layout == MappingLayout::Vyper {
        pre.extend_from_slice(&root.to_be_bytes());
        pre.extend_from_slice(&account.to_be_bytes());
    } else {
        pre.extend_from_slice(&account.to_be_bytes());
        pre.extend_from_slice(&root.to_be_bytes());
    }
    U256::from_be_bytes(&keccak::keccak256(&pre))
}

fn self_credit(c: &Contract, ledgers: &[Ledger], out: &mut Vec<Finding>) {
    let caller = exec::CALLER;
    let keys: Vec<(Ledger, U256)> = ledgers
        .iter()
        .map(|l| (*l, entry_key(l.root, caller, c.compiler.layout)))
        .collect();
    for f in c.functions.iter().filter(|f| creditable(f)) {
        if let Some(Credit {
            witness,
            root,
            wrapped,
        }) = search_credit(c.code_of(f), f, &keys)
        {
            let how = if wrapped {
                "A subtraction on that path wraps below zero, so the balance becomes a near-2^256 number: the debit is missing the check that other paths apply to this mapping."
            } else {
                "A balance should only rise against a payment, a transfer in or a privileged mint; this path mints it for free."
            };
            push(
                out,
                "unprivileged-balance-credit",
                "An arbitrary caller can increase its own balance from nothing",
                Severity::High,
                Confidence::Medium,
                Some(f),
                Some(f.pc),
                format!(
                    "Calling `{}` from a fresh state, sending no ether and holding no balance, leaves the caller with a non-zero entry in the balance mapping at slot {}. {how}",
                    display_name(f),
                    root.to_hex()
                ),
                vec![format!("witness calldata: {}", hex::encode(&witness))],
                "Credit a balance only against ether received, tokens pulled, or an access-controlled mint.",
            );
        }
    }
}

fn creditable(f: &Function) -> bool {
    f.kind == FnKind::External && !matches!(f.mutability, Mutability::View | Mutability::Pure)
}

struct Credit {
    witness: Vec<u8>,
    root: U256,
    wrapped: bool,
}

fn search_credit(code: &[u8], f: &Function, keys: &[(Ledger, U256)]) -> Option<Credit> {
    let selector = exec::selector_of(f);
    let mut attempts = 0;
    for nargs in 0..=5usize {
        for args in exec::arg_shapes(nargs) {
            if attempts >= MAX_ATTEMPTS {
                return None;
            }
            attempts += 1;
            let data = exec::calldata(selector, &args);
            let host = exec::caller_host(data.clone(), U256::ZERO);
            let run = exec::run_frame(code, &host, HashMap::new(), STEP_BUDGET);
            if !run.succeeded() {
                continue;
            }
            for (ledger, key) in keys {
                let Some(v) = run.storage.get(key).filter(|v| !v.is_zero()) else {
                    continue;
                };
                let wrapped = v.is_negative();
                if !wrapped || ledger.compared_unsigned {
                    return Some(Credit {
                        witness: data,
                        root: ledger.root,
                        wrapped,
                    });
                }
            }
        }
    }
    None
}
