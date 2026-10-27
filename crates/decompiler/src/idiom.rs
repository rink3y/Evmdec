//! Idiom recognition on lifted graphs: compiler boilerplate that is folded into one statement
//! after lifting, before structuring.

use crate::expr::{self, ExprId, Node};
use crate::lift::{Lifted, Stmt, Term};
use crate::opcode as op;
use crate::u256::U256;
use std::collections::HashSet;

/// Memory/storage loads rewritten to version 0, so that `mem[0x40]` read at different points
/// compares equal (the idioms below never write the free memory pointer in between).
fn unversioned(e: ExprId) -> ExprId {
    let mut memo = std::collections::HashMap::new();
    expr::substitute(
        e,
        &|n| match n {
            Node::MLoad(a, v) if *v != 0 => Some(expr::intern(Node::MLoad(unversioned(*a), 0))),
            Node::SLoad(a, t, v) if *v != 0 => Some(expr::intern(Node::SLoad(unversioned(*a), *t, 0))),
            _ => None,
        },
        &mut memo,
    )
}

/// Flatten an addition tree into its non-constant addends (sorted, unversioned) and its constant.
fn addends(e: ExprId) -> (Vec<ExprId>, U256) {
    let mut terms = Vec::new();
    let mut c = U256::ZERO;
    let mut stack = vec![unversioned(e)];
    while let Some(x) = stack.pop() {
        match expr::node(x) {
            Node::Const(k) => c = c.wrapping_add(k),
            Node::Op(o, v) if o == op::ADD => {
                stack.push(v[0]);
                stack.push(v[1]);
            }
            _ => terms.push(x),
        }
    }
    terms.sort();
    (terms, c)
}

fn mload_addr(e: ExprId) -> Option<ExprId> {
    if let Node::MLoad(a, _) = expr::node(e) {
        Some(a)
    } else {
        None
    }
}

fn u(n: u64) -> U256 {
    U256::from_u64(n)
}

struct DynReturn {
    ptr: ExprId,
    header: usize,
    dead: Vec<usize>,
}

/// The solc (0.4 – 0.7) encoder for returning one `bytes`/`string` value held in memory at `p`:
///
/// ```text
/// S: mem[a] = 32; mem[a + 32] = mem[p]; v = 0
/// H: while (v < mem[p]) { B: mem[a + 64 + v] = mem[p + 32 + v]; v += 32 }
/// E…: zero the padding of the last word
/// R: return mem[a : end]
/// ```
fn match_dynamic_return(l: &Lifted, s: usize) -> Option<DynReturn> {
    let sn = &l.nodes[s];
    let Term::Jump(h) = sn.term else { return None };
    // The two head stores are the last memory writes; explicit assignments may follow them.
    let mut k = sn.stmts.len();
    while k > 0 && matches!(sn.stmts[k - 1], Stmt::Assign { .. }) {
        k -= 1;
    }
    if k < 2 {
        return None;
    }
    let (Stmt::MStore { off: a, val: v32, width: 32 }, Stmt::MStore { off: a32, val: lenv, width: 32 }) = (&sn.stmts[k - 2], &sn.stmts[k - 1]) else { return None };
    if expr::as_const(*v32) != Some(u(32)) {
        return None;
    }
    let (ta, ca) = addends(*a);
    let (ta32, ca32) = addends(*a32);
    if ta != ta32 || ca32 != ca.wrapping_add(u(32)) {
        return None;
    }
    let p = unversioned(mload_addr(*lenv)?);
    // Loop counter initialised to zero, on the edge into the header or by a trailing assignment.
    let from_edge = l.edge_assigns.get(&(s, h)).and_then(|ea| ea.iter().find(|(_, val)| expr::as_const(*val) == Some(U256::ZERO)).map(|(var, _)| *var));
    let from_stmt = sn.stmts[k..].iter().find_map(|st| if let Stmt::Assign { var, value } = st { if expr::as_const(*value) == Some(U256::ZERO) { Some(*var) } else { None } } else { None });
    let v = from_edge.or(from_stmt)?;
    let Node::Var(vi) = expr::node(v) else { return None };
    let hn = &l.nodes[h];
    if !hn.stmts.is_empty() {
        return None;
    }
    let Term::Branch { cond, t: Some(t), f } = &hn.term else { return None };
    let back = |x: usize| matches!(l.nodes[x].term, Term::Jump(y) if y == h);
    let (b, e) = if back(*f) && !back(*t) {
        (*f, *t)
    } else if back(*t) && !back(*f) {
        (*t, *f)
    } else {
        return None;
    };
    if !expr::contains(*cond, &|n| matches!(n, Node::Var(i) if *i == vi)) || !expr::contains(*cond, &|n| matches!(n, Node::MLoad(pp, _) if unversioned(*pp) == p)) {
        return None;
    }
    // Body: exactly one word copied.
    let bn = &l.nodes[b];
    if bn.stmts.len() != 1 {
        return None;
    }
    let Stmt::MStore { off: bo, val: bv, width: 32 } = &bn.stmts[0] else { return None };
    let (tbo, cbo) = addends(*bo);
    let mut want = ta.clone();
    want.push(v);
    want.sort();
    if tbo != want || cbo != ca.wrapping_add(u(64)) {
        return None;
    }
    let src = mload_addr(*bv)?;
    let (tsv, csv) = addends(src);
    // The loop variable must survive unversioning unchanged (it is a plain Var).
    debug_assert_eq!(unversioned(v), v);
    let (tp, cp) = addends(p);
    let mut wantp = tp.clone();
    wantp.push(v);
    wantp.sort();
    if tsv != wantp || csv != cp.wrapping_add(u(32)) {
        return None;
    }
    // Back edge: v += 32.
    let inc = l.edge_assigns.get(&(b, h))?.iter().any(|(var, val)| {
        let (tv, cv) = addends(*val);
        *var == v && tv == vec![v] && cv == u(32)
    });
    if !inc {
        return None;
    }
    // Exit region: padding stores only, ending in `return mem[a : …]`.
    let mut dead = vec![h, b];
    let mut work = vec![e];
    let mut seen = HashSet::new();
    let mut found = false;
    while let Some(x) = work.pop() {
        if !seen.insert(x) {
            continue;
        }
        if seen.len() > 8 {
            return None;
        }
        let xn = &l.nodes[x];
        if !xn.stmts.iter().all(|st| matches!(st, Stmt::MStore { .. })) {
            return None;
        }
        match &xn.term {
            Term::Jump(y) => work.push(*y),
            Term::Branch { t: Some(t), f, .. } => {
                work.push(*t);
                work.push(*f);
            }
            Term::Return { off, .. } => {
                let (to, co) = addends(*off);
                if to != ta || co != ca {
                    return None;
                }
                found = true;
            }
            _ => return None,
        }
        dead.push(x);
    }
    if !found {
        return None;
    }
    // Nothing else may flow into the folded region.
    for &d in &dead {
        if l.nodes[d].preds.iter().any(|pr| *pr != s && !dead.contains(pr)) {
            return None;
        }
    }
    Some(DynReturn { ptr: p, header: h, dead })
}

/// Fold recognised idioms in place. Returns the number of rewrites.
pub fn fold(l: &mut Lifted) -> usize {
    let mut count = 0;
    for s in 0..l.nodes.len() {
        let Some(m) = match_dynamic_return(l, s) else { continue };
        let mut k = l.nodes[s].stmts.len();
        while k > 0 && matches!(l.nodes[s].stmts[k - 1], Stmt::Assign { .. }) {
            k -= 1;
        }
        let tail: Vec<Stmt> = l.nodes[s].stmts.drain(k..).collect();
        l.nodes[s].stmts.truncate(k - 2);
        // Trailing assignments other than the loop counter keep their place.
        l.nodes[s].stmts.extend(tail.into_iter().filter(|st| !matches!(st, Stmt::Assign { value, .. } if expr::as_const(*value) == Some(U256::ZERO))));
        l.nodes[s].term = Term::ReturnDyn { ptr: m.ptr };
        l.nodes[s].succs.clear();
        l.edge_assigns.remove(&(s, m.header));
        for d in m.dead {
            let nd = &mut l.nodes[d];
            nd.stmts.clear();
            nd.term = Term::Infeasible;
            nd.succs.clear();
            nd.preds.clear();
        }
        count += 1;
    }
    count
}

/// Is `l` the helper that copies a storage `string`/`bytes` variable to memory and returns the
/// pointer? (solc 0.4 – 0.7: it reads one slot `k`, decodes the short/long length with
/// `slot & 1` and `>> 1` or `/ 2`, and returns the free memory pointer.)
pub fn storage_string_loader(l: &Lifted) -> Option<U256> {
    let mut returns = 0;
    let mut and1: HashSet<U256> = HashSet::new();
    let mut halved: HashSet<U256> = HashSet::new();
    let slot_of = |e: ExprId| -> Option<U256> {
        if let Node::SLoad(k, false, _) = expr::node(e) {
            expr::as_const(k)
        } else {
            None
        }
    };
    for nd in &l.nodes {
        for st in &nd.stmts {
            match st {
                Stmt::SStore { .. } | Stmt::Log { .. } | Stmt::Call { .. } | Stmt::Create { .. } | Stmt::Internal { .. } => return None,
                _ => {}
            }
        }
        match &nd.term {
            Term::InternalReturn(vals) => {
                if vals.len() != 1 || !matches!(expr::node(vals[0]), Node::MLoad(a, _) if expr::as_const(a) == Some(u(0x40))) {
                    return None;
                }
                returns += 1;
            }
            Term::Return { .. } | Term::ReturnDyn { .. } | Term::SelfDestruct(_) | Term::Stop => return None,
            _ => {}
        }
        for e in crate::lift::node_exprs(nd) {
            let mut seen = HashSet::new();
            let mut stack = vec![e];
            while let Some(x) = stack.pop() {
                if !seen.insert(x) || seen.len() > 5000 {
                    continue;
                }
                if let Node::Op(o, v) = expr::node(x) {
                    if o == op::AND && v.len() == 2 {
                        for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
                            if expr::as_const(b) == Some(U256::ONE) {
                                if let Some(k) = slot_of(a) {
                                    and1.insert(k);
                                }
                            }
                        }
                    }
                    let shifted = (o == op::SHR && expr::as_const(v[0]) == Some(U256::ONE)) || (o == op::DIV && expr::as_const(v[1]) == Some(u(2)));
                    if shifted {
                        let inner = if o == op::SHR { v[1] } else { v[0] };
                        let mut st2 = vec![inner];
                        let mut seen2 = HashSet::new();
                        while let Some(y) = st2.pop() {
                            if !seen2.insert(y) || seen2.len() > 500 {
                                continue;
                            }
                            if let Some(k) = slot_of(y) {
                                halved.insert(k);
                            }
                            st2.extend(expr::children(y));
                        }
                    }
                    stack.extend(v.iter().copied());
                } else {
                    stack.extend(expr::children(x));
                }
            }
        }
    }
    if returns == 0 {
        return None;
    }
    let mut both: Vec<U256> = and1.intersection(&halved).copied().collect();
    both.sort();
    if both.len() == 1 {
        Some(both[0])
    } else {
        None
    }
}

/// Does `ptr` hold the memory pointer returned by a storage-string loader call in `l`?
pub fn is_string_pointer(l: &Lifted, ptr: ExprId, loaders: &std::collections::HashMap<usize, U256>) -> Option<U256> {
    let Node::IntRet(seq, _) = expr::node(ptr) else { return None };
    for nd in &l.nodes {
        for st in &nd.stmts {
            if let Stmt::Internal { seq: s2, callee, .. } = st {
                if *s2 == seq {
                    return loaders.get(callee).copied();
                }
            }
        }
    }
    None
}
