//! Public function discovery (dispatcher analysis) and function properties.

use crate::emit::{self, calldata_word_index};
use crate::expr::{self, ExprId, Node};
use crate::lift::{self, Lifted, Root, Stmt, Term};
use crate::opcode as op;
use crate::u256::U256;
use serde::Serialize;
use std::collections::{HashMap, HashSet, VecDeque};

/// The role a recovered function plays in the contract.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum FnKind {
    /// Selector-dispatched function reachable from the dispatcher.
    External,
    /// Code run when no selector matches (or the whole entry region when there is no dispatcher).
    Fallback,
    /// Code run for empty calldata (the `calldatasize == 0` branch of the dispatcher).
    Receive,
    /// Entry point of creation code: the fallback of a constructor unit, reclassified.
    Constructor,
    /// Internal helper reached by jump-and-return calls, never dispatched directly.
    Internal,
    /// Code region reached by no recovered jump or call (`orphan_<pc>`).
    Orphan,
}

/// Solidity state mutability of a function, inferred from its side effects.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Mutability {
    /// Neither reads nor writes state (storage, chain environment, external calls).
    Pure,
    /// Reads storage or the chain environment, or makes static calls, but never writes state.
    View,
    /// May change state and rejects a non-zero `msg.value`.
    NonPayable,
    /// Accepts `msg.value`: no check reverts on a non-zero call value.
    Payable,
}

/// An external function found in the dispatcher: its selector and body entry.
#[derive(Clone, Debug)]
pub struct Discovered {
    /// Four-byte function selector the dispatcher compares against.
    pub selector: u32,
    /// Entry node (in the main lifted graph).
    pub entry: usize,
}

/// Result of dispatcher analysis on the main lifted graph.
#[derive(Clone, Debug)]
pub struct Dispatch {
    /// Selector-dispatched functions, sorted by selector.
    pub functions: Vec<Discovered>,
    /// Entry node of the fallback body: a non-reverting dispatcher exit that is not a function.
    pub fallback: Option<usize>,
    /// Entry node of the receive body (the `calldatasize == 0` branch), if any.
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
            let reverts = |x: Option<usize>| x.is_none_or(|x| is_plain_revert(main, x));
            match expr::node(*cond) {
                Node::Op(op::ISZERO, v)
                    if matches!(expr::node(v[0]), Node::Env(op::CALLVALUE, _)) =>
                {
                    if reverts(Some(*f)) {
                        return true;
                    }
                }
                Node::Env(op::CALLVALUE, _) if reverts(*t) => {
                    return true;
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
                        functions.push(Discovered {
                            selector: sel,
                            entry: b,
                        });
                        entries.insert(b);
                    }
                    sel_nodes.push(nid);
                }
            }
        }
    }
    // No selector dispatcher at all (hand-written contract, minimal proxy, pure fallback): the
    // whole entry region is the fallback.
    if sel_nodes.is_empty() {
        return Dispatch {
            functions: vec![],
            fallback: Some(main.entry),
            receive: None,
            dispatcher: HashSet::new(),
        };
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
    let mut q: VecDeque<usize> = sel_nodes
        .iter()
        .copied()
        .filter(|n| fwd.contains(n))
        .collect();
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
    Dispatch {
        functions,
        fallback,
        receive,
        dispatcher,
    }
}

fn is_plain_revert(l: &Lifted, n: usize) -> bool {
    let nd = &l.nodes[n];
    match &nd.term {
        Term::Revert { data, len, .. } => {
            nd.stmts.iter().all(|s| matches!(s, Stmt::MStore { .. }))
                && (data.as_ref().is_some_and(|d| d.is_empty())
                    || expr::as_const(*len) == Some(U256::ZERO))
        }
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
        nd.preds = nd
            .preds
            .iter()
            .filter_map(|p| map.get(p).copied())
            .collect();
        nd.term = remap(&nd.term, &map);
        nodes.push(nd);
    }
    let mut edge_assigns = HashMap::new();
    for ((a, b), v) in &l.edge_assigns {
        if let (Some(a2), Some(b2)) = (map.get(a), map.get(b)) {
            edge_assigns.insert((*a2, *b2), v.clone());
        }
    }
    Lifted {
        nodes,
        entry: 0,
        edge_assigns,
        n_args: l.n_args,
        reprocess_count: 0,
        ret_slot: l.ret_slot,
        entry_states: Vec::new(),
        node_map: HashMap::new(),
    }
}

fn remap(t: &Term, map: &HashMap<usize, usize>) -> Term {
    let m = |x: &usize| map[x];
    match t {
        Term::Jump(n) => Term::Jump(m(n)),
        Term::Branch { cond, t, f } => Term::Branch {
            cond: *cond,
            t: t.as_ref().map(m),
            f: m(f),
        },
        Term::Switch { target, cases } => Term::Switch {
            target: *target,
            cases: cases.iter().map(m).collect(),
        },
        other => other.clone(),
    }
}

/// Side-effect summary of a lifted graph (before considering internal callees).
#[derive(Clone, Debug, Default, Serialize)]
pub struct Effects {
    /// Contains an `SSTORE`.
    pub writes_storage: bool,
    /// Reads a storage slot (`SLOAD`).
    pub reads_storage: bool,
    /// Emits an event (`LOG0`..`LOG4`).
    pub logs: bool,
    /// Makes a non-static external call (`CALL`, `CALLCODE` or `DELEGATECALL`).
    pub calls: bool,
    /// Makes a `STATICCALL`.
    pub static_calls: bool,
    /// Deploys a contract (`CREATE` or `CREATE2`).
    pub creates: bool,
    /// Ends in `SELFDESTRUCT`.
    pub selfdestruct: bool,
    /// Makes a `DELEGATECALL` or `CALLCODE` (runs foreign code in this contract's context).
    pub delegatecall: bool,
    /// Reads chain or transaction environment (`CALLER`, `TIMESTAMP`, `BALANCE`, ...).
    pub reads_env: bool,
    /// Entry pcs of the internal functions called directly, in first-call order, no duplicates.
    pub internal_callees: Vec<usize>,
}

/// Summarises the side effects of a lifted graph, ignoring those of its internal callees.
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
                Stmt::Internal { callee, .. } if !e.internal_callees.contains(callee) => {
                    e.internal_callees.push(*callee);
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
            if mentions(x, &|n| {
                matches!(n, Node::Env(o, _) if matches!(*o, op::CALLER | op::ORIGIN | op::TIMESTAMP | op::NUMBER | op::COINBASE | op::GASLIMIT | op::CHAINID | op::SELFBALANCE | op::BASEFEE | op::ADDRESS | op::PREVRANDAO | op::GASPRICE | op::BLOBBASEFEE))
                    || matches!(n, Node::Op(o, _) if matches!(*o, op::BALANCE | op::EXTCODESIZE | op::EXTCODEHASH | op::BLOCKHASH))
            }) {
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
            let reverts = |x: Option<usize>| {
                x.is_none_or(|x| {
                    is_plain_revert(l, x) || matches!(l.nodes[x].term, Term::Revert { .. })
                })
            };
            match n {
                Node::Op(op::ISZERO, v)
                    if matches!(expr::node(v[0]), Node::Env(op::CALLVALUE, _)) =>
                {
                    if reverts(Some(*f)) {
                        return true;
                    }
                }
                Node::Env(op::CALLVALUE, _) if reverts(*t) => {
                    return true;
                }
                _ => {}
            }
        }
    }
    false
}

/// A recovered calldata parameter.
#[derive(Clone, Debug, Default, Serialize)]
pub struct Param {
    /// Zero-based position among the ABI head words.
    pub index: u32,
    /// Inferred Solidity type (`uint256` when nothing narrows it).
    pub ty: String,
    /// Placeholder name, `arg<index>`.
    pub name: String,
}

/// Expressions of a function plus those of the internal functions it calls (two levels), with
/// callee arguments substituted by the caller's actual values, so that decoding done in helper
/// functions (solc >= 0.8) is visible.
pub fn exprs_with_callees<'a>(
    l: &Lifted,
    resolve: &dyn Fn(usize) -> Option<&'a Lifted>,
    depth: usize,
) -> Vec<ExprId> {
    exprs_with_callees_tagged(l, resolve, depth)
        .into_iter()
        .map(|r| r.expr)
        .collect()
}

/// [`exprs_with_callees`], each root tagged with whether it is a payload word (see
/// [`lift::Root`]).
pub fn exprs_with_callees_tagged<'a>(
    l: &Lifted,
    resolve: &dyn Fn(usize) -> Option<&'a Lifted>,
    depth: usize,
) -> Vec<Root> {
    let mut out: Vec<Root> = Vec::new();
    for nd in &l.nodes {
        out.extend(lift::roots(nd));
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
                    let inner = exprs_with_callees_tagged(cl, resolve, depth - 1);
                    let mut memo = HashMap::new();
                    for root in inner {
                        let sub = expr::substitute(
                            root.expr,
                            &|n| {
                                if let Node::Arg(i) = n {
                                    map.get(i).copied()
                                } else {
                                    None
                                }
                            },
                            &mut memo,
                        );
                        out.push(Root {
                            expr: sub,
                            payload: root.payload,
                        });
                    }
                }
            }
        }
    }
    out
}

/// Infer calldata parameters from usage.
pub fn infer_params(l: &Lifted) -> Vec<Param> {
    let roots: Vec<Root> = l.nodes.iter().flat_map(lift::roots).collect();
    infer_params_from(&roots)
}

/// Masks and shifts that carve a piece of a value for a packed payload word (`x & 0xffffffff
/// << 224 | y >> 32`): the operands of an `OR`, `SHL` or power-of-two `MUL`, and the root of a
/// payload word (the 4-byte tail of a `4 + 32n` payload is `x & 0xffffffff` on its own). They
/// say nothing about the type of what they mask.
pub fn packing_masks(roots: &[Root]) -> HashSet<ExprId> {
    let mut out = HashSet::new();
    let mut seen = HashSet::new();
    let mut stack: Vec<ExprId> = Vec::new();
    for r in roots {
        stack.push(r.expr);
        if r.payload && matches!(expr::node(r.expr), Node::Op(op::AND | op::SHR | op::DIV, _)) {
            out.insert(r.expr);
        }
    }
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 200_000 {
            continue;
        }
        let kids = expr::children(x);
        if matches!(expr::node(x), Node::Op(op::OR | op::SHL | op::MUL, _)) {
            for k in &kids {
                if matches!(expr::node(*k), Node::Op(op::AND | op::SHR | op::DIV, _)) {
                    out.insert(*k);
                }
            }
        }
        stack.extend(kids);
    }
    out
}

/// Infers calldata parameters from a set of expression roots, each tagged with whether it is a
/// payload word.
///
/// Masks and sign-extensions give the types; the ABI head-size check (or, failing that, the
/// highest calldata word read) gives the count.
pub fn infer_params_from(roots: &[Root]) -> Vec<Param> {
    let mut max_idx: Option<u32> = None;
    let mut types: HashMap<u32, String> = HashMap::new();
    let mut dynamic: HashSet<u32> = HashSet::new();
    let mut head_words: Option<u32> = None;
    let packing = packing_masks(roots);
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
                Node::Op(op::AND, v) if !packing.contains(&x) => {
                    if let (Node::CallDataLoad(off), Some(m)) =
                        (expr::node(v[0]), expr::as_const(v[1]))
                    {
                        if let Some(i) = calldata_word_index(off) {
                            if m.is_low_mask() {
                                let bits = m.bits();
                                let ty = if bits == 160 {
                                    Some("address".to_string())
                                } else if bits == 1 {
                                    Some("bool".to_string())
                                } else if bits % 8 == 0 {
                                    Some(format!("uint{}", bits))
                                } else {
                                    // `x & (2^255 - 1)` strips a flag bit from a uint256.
                                    None
                                };
                                if let Some(ty) = ty {
                                    types.entry(i).or_insert(ty);
                                }
                            }
                        }
                    }
                }
                Node::Op(op::SIGNEXTEND, v) => {
                    if let (Some(k), Node::CallDataLoad(off)) =
                        (expr::as_const(v[0]), expr::node(v[1]))
                    {
                        if let Some(i) = calldata_word_index(off) {
                            if k < U256::from_u64(31) {
                                types
                                    .entry(i)
                                    .or_insert(format!("int{}", 8 * (k.low_u64() + 1)));
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
                Node::Op(op::LT, v)
                | Node::Op(op::GT, v)
                | Node::Op(op::SLT, v)
                | Node::Op(op::SGT, v) => {
                    // calldatasize - 4 < 32n  or  calldatasize < 4 + 32n (head size check)
                    for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
                        if let Some(c) = expr::as_const(b) {
                            if c.fits_u64() {
                                let (base, delta) = expr::split_offset(a);
                                if base.is_some_and(|x| {
                                    matches!(expr::node(x), Node::Env(op::CALLDATASIZE, _))
                                }) {
                                    // a = calldatasize - 4 (delta = -4) or calldatasize
                                    let k = c.low_u64() as i128
                                        - if delta.is_negative() { 0 } else { 4 };
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
    for r in roots {
        visit(r.expr);
    }
    // `iszero(iszero(x))` is both the bool cleanup and `x != 0`: a word is a bool only when it
    // is never used raw anywhere else (arithmetic, comparison, call argument, hash input).
    {
        let bool_words: Vec<u32> = types
            .iter()
            .filter(|(_, t)| *t == "bool")
            .map(|(i, _)| *i)
            .collect();
        if !bool_words.is_empty() {
            let mut raw: HashSet<u32> = HashSet::new();
            let mut seen = HashSet::new();
            let mut stack: Vec<ExprId> = roots.iter().map(|r| r.expr).collect();
            while let Some(x) = stack.pop() {
                if !seen.insert(x) || seen.len() > 200_000 {
                    continue;
                }
                let kids = expr::children(x);
                let is_cleanup = matches!(expr::node(x), Node::Op(op::ISZERO, ref v) if matches!(expr::node(v[0]), Node::Op(op::ISZERO, _)));
                let is_validator = matches!(expr::node(x), Node::Op(op::EQ, ref v) if v.iter().any(|y| matches!(expr::node(*y), Node::Op(op::ISZERO, _))));
                if !is_cleanup && !is_validator && !matches!(expr::node(x), Node::Op(op::ISZERO, _))
                {
                    for k in &kids {
                        if let Node::CallDataLoad(off) = expr::node(*k) {
                            if let Some(i) = calldata_word_index(off) {
                                raw.insert(i);
                            }
                        }
                    }
                }
                stack.extend(kids);
            }
            for i in bool_words {
                if raw.contains(&i) {
                    types.remove(&i);
                }
            }
        }
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
            let ty = if dynamic.contains(&i) {
                "bytes".to_string()
            } else {
                types.get(&i).cloned().unwrap_or_else(|| "uint256".into())
            };
            Param {
                index: i,
                ty,
                name: format!("arg{}", i),
            }
        })
        .collect()
}

/// Infer return types from `return` payloads.
pub fn infer_returns(l: &Lifted) -> Vec<String> {
    let mut best: Vec<String> = Vec::new();
    for nd in &l.nodes {
        if let Term::Return { len, data, .. } = &nd.term {
            let tys: Vec<String> = match (data, expr::as_const(*len)) {
                // `(32, n, <n bytes>)`: one dynamic value encoded in place.
                (Some(words), Some(l))
                    if words.len() >= 2
                        && expr::as_const(words[0]) == Some(U256::from_u64(32))
                        && expr::as_const(words[1]).is_some_and(|n| {
                            n.fits_u64() && l == U256::from_u64(64 + n.low_u64().div_ceil(32) * 32)
                        }) =>
                {
                    // Printable constant text is a `string`; anything else stays `bytes`.
                    let text = emit::decode_plain_string(&words[1..]).is_some_and(|t| {
                        !t.is_empty() && t.chars().all(|c| !c.is_control() && c != '\u{fffd}')
                    });
                    vec![if text {
                        "string".into()
                    } else {
                        "bytes".into()
                    }]
                }
                (Some(words), Some(_)) => words.iter().map(|w| type_of_value(*w)).collect(),
                (None, Some(l))
                    if l.fits_u64() && l.low_u64() % 32 == 0 && l.low_u64() <= 32 * 16 =>
                {
                    vec!["uint256".to_string(); (l.low_u64() / 32) as usize]
                }
                (None, Some(_)) => vec!["bytes".into()],
                (_, None) => vec!["bytes".into()],
            };
            if tys.len() > best.len()
                || (tys.len() == best.len()
                    && tys.iter().filter(|t| *t != "uint256").count()
                        > best.iter().filter(|t| *t != "uint256").count())
            {
                best = tys;
            }
        } else if let Term::ReturnDyn { .. } = &nd.term {
            if best.is_empty() {
                best = vec!["bytes".into()];
            }
        }
    }
    // A position that only ever returns the constants 0 and 1, with 1 seen, is a bool.
    if !best.is_empty() {
        let rets: Vec<&Vec<ExprId>> = l
            .nodes
            .iter()
            .filter_map(|nd| {
                if let Term::Return { data: Some(w), .. } = &nd.term {
                    if w.len() == best.len() {
                        Some(w)
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect();
        if !rets.is_empty() {
            for (i, ty) in best.iter_mut().enumerate() {
                if ty != "uint256" {
                    continue;
                }
                let consts: Vec<Option<U256>> = rets.iter().map(|w| expr::as_const(w[i])).collect();
                if consts
                    .iter()
                    .all(|c| matches!(c, Some(c) if *c == U256::ZERO || *c == U256::ONE))
                    && consts.contains(&Some(U256::ONE))
                {
                    *ty = "bool".into();
                }
            }
        }
    }
    best
}

/// Return types of an internal unit with `n_rets` results: a position that only ever returns
/// the constants 0 and 1, with 1 seen, or only comparisons, is a `bool`; everything else is
/// `uint256`.
pub fn infer_internal_returns(l: &Lifted, n_rets: usize) -> Vec<String> {
    let mut tys = vec!["uint256".to_string(); n_rets];
    let rets: Vec<&Vec<ExprId>> = l
        .nodes
        .iter()
        .filter_map(|nd| match &nd.term {
            Term::InternalReturn(v) if v.len() == n_rets => Some(v),
            _ => None,
        })
        .collect();
    if rets.is_empty() {
        return tys;
    }
    for (i, ty) in tys.iter_mut().enumerate() {
        // Values are deepest first: the j-th result is the j-th from the top.
        let j = n_rets - 1 - i;
        let consts: Vec<Option<U256>> = rets.iter().map(|w| expr::as_const(w[j])).collect();
        let all_flags = consts
            .iter()
            .all(|c| matches!(c, Some(c) if *c == U256::ZERO || *c == U256::ONE));
        let comparisons = rets.iter().all(|w| expr::is_boolean(w[j]));
        if (all_flags && consts.contains(&Some(U256::ONE))) || (comparisons && !all_flags) {
            *ty = "bool".into();
        }
    }
    tys
}

/// Parameter types of an internal unit with `n_params` parameters (`arg0` is the deepest):
/// `address` for a parameter used as a call target, a `selfdestruct` beneficiary, compared with
/// `msg.sender` or masked to 160 bits; `uint256` otherwise.
pub fn internal_param_types(l: &Lifted, n_params: usize) -> Vec<String> {
    let mut tys = vec!["uint256".to_string(); n_params];
    let k = l.ret_slot.map(|k| k as usize).unwrap_or(l.n_args);
    let param_of = |e: ExprId| -> Option<usize> {
        let e = match expr::node(e) {
            Node::Op(op::AND, v) if expr::as_const(v[1]) == Some(expr::mask_bits(160)) => v[0],
            Node::Op(op::AND, v) if expr::as_const(v[0]) == Some(expr::mask_bits(160)) => v[1],
            _ => e,
        };
        match expr::node(e) {
            Node::Arg(i) if (i as usize) < k => Some(k - 1 - i as usize),
            _ => None,
        }
    };
    let mut address = |e: ExprId| {
        if let Some(j) = param_of(e) {
            if j < n_params {
                tys[j] = "address".to_string();
            }
        }
    };
    for nd in &l.nodes {
        for s in &nd.stmts {
            if let Stmt::Call { addr, .. } = s {
                address(*addr);
            }
        }
        if let Term::SelfDestruct(a) = &nd.term {
            address(*a);
        }
        for e in lift::node_exprs(nd) {
            let mut seen = HashSet::new();
            let mut stack = vec![e];
            while let Some(x) = stack.pop() {
                if !seen.insert(x) || seen.len() > 20_000 {
                    continue;
                }
                match expr::node(x) {
                    Node::Op(op::AND, v)
                        if v.iter()
                            .any(|m| expr::as_const(*m) == Some(expr::mask_bits(160))) =>
                    {
                        address(x);
                    }
                    Node::Op(op::EQ, v) => {
                        let caller = |y: ExprId| matches!(expr::node(y), Node::Env(op::CALLER, _));
                        if caller(v[0]) {
                            address(v[1]);
                        }
                        if caller(v[1]) {
                            address(v[0]);
                        }
                    }
                    _ => {}
                }
                stack.extend(expr::children(x));
            }
        }
    }
    tys
}

/// Best-effort Solidity type of a value from the shape of its expression (`uint256` by default).
pub fn type_of_value(e: ExprId) -> String {
    match expr::node(e) {
        Node::Op(op::AND, v) => {
            if let Some(m) = expr::as_const(v[1]) {
                if m.is_low_mask() {
                    let bits = m.bits();
                    return if bits == 160 {
                        "address".into()
                    } else if bits == 1 {
                        "bool".into()
                    } else if bits % 8 == 0 {
                        format!("uint{}", bits)
                    } else {
                        "uint256".into()
                    };
                }
            }
            "uint256".into()
        }
        Node::Op(op::SIGNEXTEND, v) => match expr::as_const(v[0]) {
            Some(k) if k < U256::from_u64(31) => format!("int{}", 8 * (k.low_u64() + 1)),
            _ => "int256".into(),
        },
        Node::Env(op::CALLER, _)
        | Node::Env(op::ADDRESS, _)
        | Node::Env(op::ORIGIN, _)
        | Node::Env(op::COINBASE, _)
        | Node::CreateResult(_) => "address".into(),
        Node::Env(op::TIMESTAMP, _) | Node::Env(op::NUMBER, _) => "uint256".into(),
        n if expr::is_boolean(e) && !matches!(n, Node::Const(_)) => "bool".into(),
        Node::Const(c) if c.byte_len() == 20 && (150..=160).contains(&c.bits()) => "address".into(),
        Node::Op(op::SHR, _) | Node::Op(op::DIV, _) | Node::Op(op::BYTE, _) => {
            let b = expr::value_bits(e);
            if b < 256 && b.is_multiple_of(8) && b > 0 {
                if b == 160 {
                    "address".into()
                } else {
                    format!("uint{}", b)
                }
            } else {
                "uint256".into()
            }
        }
        _ => "uint256".into(),
    }
}
