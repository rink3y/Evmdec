//! Public function discovery (dispatcher analysis) and function properties.

use crate::emit::{self, calldata_word_index};
use crate::expr::{self, ExprId, Node};
use crate::lift::{self, Lifted, Stmt, Term};
use crate::opcode as op;
use crate::u256::U256;
use serde::Serialize;
use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum FnKind {
    External,
    Fallback,
    Receive,
    Constructor,
    Internal,
    Orphan,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Mutability {
    Pure,
    View,
    NonPayable,
    Payable,
}

#[derive(Clone, Debug)]
pub struct Discovered {
    pub selector: u32,
    /// Entry node (in the main lifted graph).
    pub entry: usize,
}

#[derive(Clone, Debug)]
pub struct Dispatch {
    pub functions: Vec<Discovered>,
    pub fallback: Option<usize>,
    pub receive: Option<usize>,
    /// Nodes forming the dispatcher itself.
    pub dispatcher: HashSet<usize>,
}

fn branch_polarity(cond: ExprId) -> Option<(u32, bool)> {
    // Returns (selector, body_is_true_branch)
    if let Some(sel) = emit::selector_compare(cond) {
        return Some((sel, true));
    }
    if let Some(sel) = emit::selector_mismatch(cond) {
        return Some((sel, false));
    }
    if let Node::Op(op::ISZERO, v) = expr::node(cond) {
        if let Some(sel) = emit::selector_compare(v[0]) {
            return Some((sel, false));
        }
        if let Some(sel) = emit::selector_mismatch(v[0]) {
            return Some((sel, true));
        }
    }
    None
}

/// The dispatcher itself rejects `msg.value` (the whole contract is non-payable).
pub fn dispatcher_nonpayable(main: &Lifted, dispatcher: &HashSet<usize>) -> bool {
    for &n in dispatcher {
        if let Term::Branch { cond, t, f } = &main.nodes[n].term {
            let reverts = |x: Option<usize>| x.map_or(true, |x| is_plain_revert(main, x));
            match expr::node(*cond) {
                Node::Op(op::ISZERO, v) if matches!(expr::node(v[0]), Node::Env(op::CALLVALUE, _)) => {
                    if reverts(Some(*f)) {
                        return true;
                    }
                }
                Node::Env(op::CALLVALUE, _) => {
                    if reverts(*t) {
                        return true;
                    }
                }
                _ => {}
            }
        }
    }
    false
}

fn mentions(e: ExprId, pred: &dyn Fn(&Node) -> bool) -> bool {
    expr::contains(e, pred)
}


/// Find the external functions reachable from the dispatcher of the main lifted unit.
pub fn discover(main: &Lifted) -> Dispatch {
    let mut functions: Vec<Discovered> = Vec::new();
    let mut entries: HashSet<usize> = HashSet::new();
    let mut sel_nodes: Vec<usize> = Vec::new();
    // Pass 1: selector branches anywhere reachable.
    let reach = lift::reachable(main);
    for &nid in &reach {
        if let Term::Branch { cond, t, f } = &main.nodes[nid].term {
            if let Some((sel, body_true)) = branch_polarity(*cond) {
                let body = if body_true { *t } else { Some(*f) };
                if let Some(b) = body {
                    if !functions.iter().any(|d| d.selector == sel) {
                        functions.push(Discovered { selector: sel, entry: b });
                        entries.insert(b);
                    }
                    sel_nodes.push(nid);
                }
            }
        }
    }
    // Dispatcher = nodes reachable from entry without entering a body, from which a selector
    // branch is reachable without entering a body.
    let mut fwd: HashSet<usize> = HashSet::new();
    let mut q = VecDeque::new();
    q.push_back(main.entry);
    while let Some(x) = q.pop_front() {
        if entries.contains(&x) || !fwd.insert(x) {
            continue;
        }
        for s in &main.nodes[x].succs {
            q.push_back(*s);
        }
    }
    // Backward from selector nodes within fwd.
    let mut preds: HashMap<usize, Vec<usize>> = HashMap::new();
    for &x in &fwd {
        for s in &main.nodes[x].succs {
            preds.entry(*s).or_default().push(x);
        }
    }
    let mut dispatcher: HashSet<usize> = HashSet::new();
    let mut q: VecDeque<usize> = sel_nodes.iter().copied().filter(|n| fwd.contains(n)).collect();
    while let Some(x) = q.pop_front() {
        if !dispatcher.insert(x) {
            continue;
        }
        if let Some(ps) = preds.get(&x) {
            for p in ps {
                if fwd.contains(p) {
                    q.push_back(*p);
                }
            }
        }
    }
    if dispatcher.is_empty() {
        dispatcher.insert(main.entry);
    }
    // Exits of the dispatcher that are not bodies: fallback / receive candidates.
    let mut fallback = None;
    let mut receive = None;
    let mut exits: Vec<(usize, usize)> = Vec::new(); // (from, to)
    for &d in &dispatcher {
        for s in &main.nodes[d].succs {
            if !dispatcher.contains(s) && !entries.contains(s) {
                exits.push((d, *s));
            }
        }
    }
    exits.sort();
    exits.dedup();
    for (from, to) in exits {
        let node = &main.nodes[to];
        // A bare revert is "no fallback".
        if is_plain_revert(main, to) {
            continue;
        }
        let from_term = &main.nodes[from].term;
        let is_receive = match from_term {
            Term::Branch { cond, t, .. } => {
                // receive: calldatasize == 0 branch taken
                let cz = matches!(expr::node(*cond), Node::Op(op::ISZERO, ref v) if matches!(expr::node(v[0]), Node::Env(op::CALLDATASIZE, _)));
                cz && *t == Some(to)
            }
            _ => false,
        };
        let _ = node;
        if is_receive && receive.is_none() {
            receive = Some(to);
        } else if fallback.is_none() {
            fallback = Some(to);
        }
    }
    functions.sort_by_key(|d| d.selector);
    Dispatch { functions, fallback, receive, dispatcher }
}

fn is_plain_revert(l: &Lifted, n: usize) -> bool {
    let nd = &l.nodes[n];
    match &nd.term {
        Term::Revert { data, len, .. } => nd.stmts.iter().all(|s| matches!(s, Stmt::MStore { .. })) && (data.as_ref().map_or(false, |d| d.is_empty()) || expr::as_const(*len) == Some(U256::ZERO)),
        Term::Invalid | Term::Infeasible => true,
        Term::Jump(t) if nd.stmts.is_empty() && *t != n => is_plain_revert(l, *t),
        _ => false,
    }
}

/// Copy the sub-graph reachable from `entry` into a new `Lifted`.
pub fn slice(l: &Lifted, entry: usize) -> Lifted {
    let mut order = Vec::new();
    let mut seen = HashSet::new();
    let mut q = VecDeque::new();
    q.push_back(entry);
    while let Some(x) = q.pop_front() {
        if !seen.insert(x) {
            continue;
        }
        order.push(x);
        for s in &l.nodes[x].succs {
            q.push_back(*s);
        }
    }
    let map: HashMap<usize, usize> = order.iter().enumerate().map(|(i, n)| (*n, i)).collect();
    let mut nodes = Vec::new();
    for &old in &order {
        let mut nd = l.nodes[old].clone();
        nd.id = map[&old];
        nd.succs = nd.succs.iter().map(|s| map[s]).collect();
        nd.preds = nd.preds.iter().filter_map(|p| map.get(p).copied()).collect();
        nd.term = remap(&nd.term, &map);
        nodes.push(nd);
    }
    let mut edge_assigns = HashMap::new();
    for ((a, b), v) in &l.edge_assigns {
        if let (Some(a2), Some(b2)) = (map.get(a), map.get(b)) {
            edge_assigns.insert((*a2, *b2), v.clone());
        }
    }
    Lifted { nodes, entry: 0, edge_assigns, n_args: l.n_args, reprocess_count: 0, ret_slot: l.ret_slot }
}

fn remap(t: &Term, map: &HashMap<usize, usize>) -> Term {
    let m = |x: &usize| map[x];
    match t {
        Term::Jump(n) => Term::Jump(m(n)),
        Term::Branch { cond, t, f } => Term::Branch { cond: *cond, t: t.as_ref().map(m), f: m(f) },
        Term::Switch { target, cases } => Term::Switch { target: *target, cases: cases.iter().map(m).collect() },
        other => other.clone(),
    }
}

/// Side-effect summary of a lifted graph (before considering internal callees).
#[derive(Clone, Debug, Default, Serialize)]
pub struct Effects {
    pub writes_storage: bool,
    pub reads_storage: bool,
    pub logs: bool,
    pub calls: bool,
    pub static_calls: bool,
    pub creates: bool,
    pub selfdestruct: bool,
    pub delegatecall: bool,
    pub reads_env: bool,
    pub internal_callees: Vec<usize>,
}

pub fn effects(l: &Lifted) -> Effects {
    let mut e = Effects::default();
    for nd in &l.nodes {
        for s in &nd.stmts {
            match s {
                Stmt::SStore { .. } => e.writes_storage = true,
                Stmt::Log { .. } => e.logs = true,
                Stmt::Call { kind, .. } => {
                    if *kind == op::STATICCALL {
                        e.static_calls = true;
                    } else {
                        e.calls = true;
                    }
                    if *kind == op::DELEGATECALL || *kind == op::CALLCODE {
                        e.delegatecall = true;
                    }
                }
                Stmt::Create { .. } => e.creates = true,
                Stmt::Internal { callee, .. } => {
                    if !e.internal_callees.contains(callee) {
                        e.internal_callees.push(*callee);
                    }
                }
                _ => {}
            }
        }
        if let Term::SelfDestruct(_) = nd.term {
            e.selfdestruct = true;
        }
        for x in lift::node_exprs(nd) {
            if mentions(x, &|n| matches!(n, Node::SLoad(..))) {
                e.reads_storage = true;
            }
            if mentions(x, &|n| matches!(n, Node::Env(o, _) if matches!(*o, op::CALLER | op::ORIGIN | op::TIMESTAMP | op::NUMBER | op::COINBASE | op::GASLIMIT | op::CHAINID | op::SELFBALANCE | op::BASEFEE | op::ADDRESS | op::PREVRANDAO | op::GASPRICE | op::BLOBBASEFEE)) || matches!(n, Node::Op(o, _) if matches!(*o, op::BALANCE | op::EXTCODESIZE | op::EXTCODEHASH | op::BLOCKHASH))) {
                e.reads_env = true;
            }
        }
    }
    e
}

/// Is the function non-payable (checks `msg.value == 0` and reverts otherwise)?
pub fn is_nonpayable(l: &Lifted) -> bool {
    for nd in &l.nodes {
        if let Term::Branch { cond, t, f } = &nd.term {
            let n = expr::node(*cond);
            let reverts = |x: Option<usize>| x.map_or(true, |x| is_plain_revert(l, x) || matches!(l.nodes[x].term, Term::Revert { .. }));
            match n {
                Node::Op(op::ISZERO, v) if matches!(expr::node(v[0]), Node::Env(op::CALLVALUE, _)) => {
                    if reverts(Some(*f)) {
                        return true;
                    }
                }
                Node::Env(op::CALLVALUE, _) => {
                    if reverts(*t) {
                        return true;
                    }
                }
                _ => {}
            }
        }
    }
    false
}

#[derive(Clone, Debug, Default, Serialize)]
pub struct Param {
    pub index: u32,
    pub ty: String,
    pub name: String,
}

/// Expressions of a function plus those of the internal functions it calls (two levels), with
/// callee arguments substituted by the caller's actual values, so that decoding done in helper
/// functions (solc >= 0.8) is visible.
pub fn exprs_with_callees(l: &Lifted, resolve: &dyn Fn(usize) -> Option<&'static Lifted>, depth: usize) -> Vec<ExprId> {
    let mut out: Vec<ExprId> = Vec::new();
    for nd in &l.nodes {
        out.extend(lift::node_exprs(nd));
        if depth == 0 {
            continue;
        }
        for s in &nd.stmts {
            if let Stmt::Internal { callee, args, .. } = s {
                if let Some(cl) = resolve(*callee) {
                    let k = cl.ret_slot.map(|k| k as usize).unwrap_or(usize::MAX);
                    // Arg(i) (i < k) is the (k-1-i)-th argument in natural order.
                    let mut map: HashMap<u32, ExprId> = HashMap::new();
                    for (j, a) in args.iter().enumerate() {
                        if k != usize::MAX && j < k {
                            map.insert((k - 1 - j) as u32, *a);
                        }
                    }
                    let inner = exprs_with_callees(cl, resolve, depth - 1);
                    let mut memo = HashMap::new();
                    for e in inner {
                        let sub = expr::substitute(e, &|n| if let Node::Arg(i) = n { map.get(i).copied() } else { None }, &mut memo);
                        out.push(sub);
                    }
                }
            }
        }
    }
    out
}

/// Infer calldata parameters from usage.
pub fn infer_params(l: &Lifted) -> Vec<Param> {
    let exprs: Vec<ExprId> = l.nodes.iter().flat_map(lift::node_exprs).collect();
    infer_params_from(&exprs)
}

pub fn infer_params_from(exprs: &[ExprId]) -> Vec<Param> {
    let mut max_idx: Option<u32> = None;
    let mut types: HashMap<u32, String> = HashMap::new();
    let mut dynamic: HashSet<u32> = HashSet::new();
    let mut head_words: Option<u32> = None;
    let mut visit = |e: ExprId| {
        let mut seen = HashSet::new();
        let mut stack = vec![e];
        while let Some(x) = stack.pop() {
            if !seen.insert(x) || seen.len() > 50_000 {
                continue;
            }
            let n = expr::node(x);
            match &n {
                Node::CallDataLoad(off) => {
                    if let Some(i) = calldata_word_index(*off) {
                        max_idx = Some(max_idx.map_or(i, |m| m.max(i)));
                    } else {
                        // calldataload(4 + arg_i + k): arg_i is a dynamic offset
                        let (base, _) = expr::split_offset(*off);
                        if let Some(b) = base {
                            if let Node::CallDataLoad(o2) = expr::node(b) {
                                if let Some(i) = calldata_word_index(o2) {
                                    dynamic.insert(i);
                                }
                            }
                        }
                    }
                }
                Node::Op(op::AND, v) => {
                    if let (Node::CallDataLoad(off), Some(m)) = (expr::node(v[0]), expr::as_const(v[1])) {
                        if let Some(i) = calldata_word_index(off) {
                            if m.is_low_mask() {
                                let bits = m.bits();
                                let ty = if bits == 160 { "address".to_string() } else if bits == 1 { "bool".to_string() } else { format!("uint{}", bits) };
                                types.entry(i).or_insert(ty);
                            }
                        }
                    }
                }
                Node::Op(op::SIGNEXTEND, v) => {
                    if let (Some(k), Node::CallDataLoad(off)) = (expr::as_const(v[0]), expr::node(v[1])) {
                        if let Some(i) = calldata_word_index(off) {
                            if k < U256::from_u64(31) {
                                types.entry(i).or_insert(format!("int{}", 8 * (k.low_u64() + 1)));
                            }
                        }
                    }
                }
                Node::Op(op::ISZERO, v) => {
                    if let Node::Op(op::ISZERO, w) = expr::node(v[0]) {
                        if let Node::CallDataLoad(off) = expr::node(w[0]) {
                            if let Some(i) = calldata_word_index(off) {
                                types.entry(i).or_insert("bool".into());
                            }
                        }
                    }
                }
                Node::Op(op::LT, v) | Node::Op(op::GT, v) | Node::Op(op::SLT, v) | Node::Op(op::SGT, v) => {
                    // calldatasize - 4 < 32n  or  calldatasize < 4 + 32n (head size check)
                    for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
                        if let Some(c) = expr::as_const(b) {
                            if c.fits_u64() {
                                let (base, delta) = expr::split_offset(a);
                                if base.map_or(false, |x| matches!(expr::node(x), Node::Env(op::CALLDATASIZE, _))) {
                                    // a = calldatasize - 4 (delta = -4) or calldatasize
                                    let k = c.low_u64() as i128 - if delta.is_negative() { 0 } else { 4 };
                                    if k >= 0 && k % 32 == 0 && k / 32 <= 64 {
                                        let w = (k / 32) as u32;
                                        head_words = Some(head_words.map_or(w, |h| h.max(w)));
                                    }
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
            stack.extend(expr::children(x));
        }
    };
    for e in exprs {
        visit(*e);
    }
    // The ABI head-size check (solc >= 0.5) gives the exact head word count; otherwise fall back
    // to the highest calldata word read. Reads beyond a present check are not parameters (e.g.
    // `LogNote`-style modifiers logging raw calldata words).
    let count = match (max_idx, head_words) {
        (_, Some(h)) => h,
        (Some(m), None) => m + 1,
        (None, None) => 0,
    };
    (0..count)
        .map(|i| {
            let ty = if dynamic.contains(&i) { "bytes".to_string() } else { types.get(&i).cloned().unwrap_or_else(|| "uint256".into()) };
            Param { index: i, ty, name: format!("arg{}", i) }
        })
        .collect()
}

/// Infer return types from `return` payloads.
pub fn infer_returns(l: &Lifted) -> Vec<String> {
    let mut best: Vec<String> = Vec::new();
    for nd in &l.nodes {
        if let Term::Return { len, data, .. } = &nd.term {
            let tys: Vec<String> = match (data, expr::as_const(*len)) {
                (Some(words), Some(_)) => words.iter().map(|w| type_of_value(*w)).collect(),
                (None, Some(l)) if l.fits_u64() && l.low_u64() % 32 == 0 && l.low_u64() <= 32 * 16 => vec!["uint256".to_string(); (l.low_u64() / 32) as usize],
                (None, Some(_)) => vec!["bytes".into()],
                (_, None) => vec!["bytes".into()],
            };
            if tys.len() > best.len() || (tys.len() == best.len() && tys.iter().filter(|t| *t != "uint256").count() > best.iter().filter(|t| *t != "uint256").count()) {
                best = tys;
            }
        }
    }
    best
}

pub fn type_of_value(e: ExprId) -> String {
    match expr::node(e) {
        Node::Op(op::AND, v) => {
            if let Some(m) = expr::as_const(v[1]) {
                if m.is_low_mask() {
                    let bits = m.bits();
                    return if bits == 160 { "address".into() } else if bits == 1 { "bool".into() } else if bits % 8 == 0 { format!("uint{}", bits) } else { "uint256".into() };
                }
            }
            "uint256".into()
        }
        Node::Op(op::SIGNEXTEND, v) => match expr::as_const(v[0]) {
            Some(k) if k < U256::from_u64(31) => format!("int{}", 8 * (k.low_u64() + 1)),
            _ => "int256".into(),
        },
        Node::Env(op::CALLER, _) | Node::Env(op::ADDRESS, _) | Node::Env(op::ORIGIN, _) | Node::Env(op::COINBASE, _) | Node::CreateResult(_) => "address".into(),
        Node::Env(op::TIMESTAMP, _) | Node::Env(op::NUMBER, _) => "uint256".into(),
        n if expr::is_boolean(e) && !matches!(n, Node::Const(_)) => "bool".into(),
        Node::Const(c) if c.byte_len() == 20 && (150..=160).contains(&c.bits()) => "address".into(),
        Node::Op(op::SHR, _) | Node::Op(op::DIV, _) | Node::Op(op::BYTE, _) => {
            let b = expr::value_bits(e);
            if b < 256 && b % 8 == 0 && b > 0 {
                if b == 160 { "address".into() } else { format!("uint{}", b) }
            } else {
                "uint256".into()
            }
        }
        _ => "uint256".into(),
    }
}
