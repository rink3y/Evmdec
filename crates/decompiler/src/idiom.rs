//! Idiom recognition on lifted graphs: compiler boilerplate that is folded into one statement
//! after lifting, before structuring.

use crate::expr::{self, ExprId, Node};
use crate::lift::{CopyLoop, CopyShape, Lifted, Stmt, Term};
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

/// Does `e` mention `mem[p]` (any version)? Walks owned nodes, so it may intern while comparing.
fn mentions_mload_of(e: ExprId, p: ExprId) -> bool {
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 5000 {
            continue;
        }
        if let Node::MLoad(pp, _) = expr::node(x) {
            if unversioned(pp) == p {
                return true;
            }
        }
        stack.extend(expr::children(x));
    }
    false
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
    /// Statements removed from the end of the head node (after trailing assignments).
    dropped: usize,
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
    // The two head stores are the last memory writes (a summarised copy may follow them);
    // explicit assignments may follow.
    let mut k = sn.stmts.len();
    while k > 0 && matches!(sn.stmts[k - 1], Stmt::Assign { .. }) {
        k -= 1;
    }
    let copy_form = k >= 3 && matches!(sn.stmts[k - 1], Stmt::Copy { kind: op::MCOPY, .. });
    let kk = if copy_form { k - 1 } else { k };
    if kk < 2 {
        return None;
    }
    let (Stmt::MStore { off: a, val: v32, width: 32 }, Stmt::MStore { off: a32, val: lenv, width: 32 }) = (&sn.stmts[kk - 2], &sn.stmts[kk - 1]) else { return None };
    if expr::as_const(*v32) != Some(u(32)) {
        return None;
    }
    let (ta, ca) = addends(*a);
    let (ta32, ca32) = addends(*a32);
    if ta != ta32 || ca32 != ca.wrapping_add(u(32)) {
        return None;
    }
    let p = unversioned(mload_addr(*lenv)?);
    let (tp, cp) = addends(p);
    let mut dead: Vec<usize> = Vec::new();
    let region_start: Vec<usize>;
    let dropped;
    if copy_form {
        // mem[a + 64 : …] = mem[p + 32 : …]
        let Stmt::Copy { dest, src, .. } = &sn.stmts[k - 1] else { return None };
        let (td, cd) = addends(*dest);
        let (ts, cs) = addends(*src);
        if td != ta || cd != ca.wrapping_add(u(64)) || ts != tp || cs != cp.wrapping_add(u(32)) {
            return None;
        }
        region_start = sn.succs.clone();
        dropped = 3;
    } else {
        let Term::Jump(h) = sn.term else { return None };
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
        if !expr::contains(*cond, &|n| matches!(n, Node::Var(i) if *i == vi)) || !mentions_mload_of(*cond, p) {
            return None;
        }
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
        let mut wantp = tp.clone();
        wantp.push(v);
        wantp.sort();
        if tsv != wantp || csv != cp.wrapping_add(u(32)) {
            return None;
        }
        let inc = l.edge_assigns.get(&(b, h))?.iter().any(|(var, val)| {
            let (tv, cv) = addends(*val);
            *var == v && tv == vec![v] && cv == u(32)
        });
        if !inc {
            return None;
        }
        dead.push(h);
        dead.push(b);
        region_start = vec![e];
        dropped = 2;
    }
    // Exit region: padding stores only, ending in `return mem[a : …]`.
    let mut work = region_start;
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
            Term::Return { off, data, .. } => {
                let (to, co) = addends(*off);
                if to != ta || co != ca {
                    return None;
                }
                // A payload the lifter already decoded (a literal string) is better than `return p`.
                if data.as_ref().map_or(false, |d| !d.is_empty()) {
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
    Some(DynReturn { ptr: p, dropped, dead })
}

/// `return p` where the same node stored a constant-length payload at `p` (`mem[p] = len`,
/// `mem[p + 32..] = data`): the ABI-encoded `bytes`/`string` return `(32, len, data...)`.
fn literal_return(stmts: &[Stmt], ptr: ExprId) -> Option<Term> {
    let (pt, pc) = addends(ptr);
    let mut len: Option<u64> = None;
    let mut words: Vec<(u64, ExprId)> = Vec::new();
    for st in stmts {
        if let Stmt::MStore { off, val, width: 32 } = st {
            let (t, c) = addends(*off);
            if t != pt || c < pc {
                continue;
            }
            let rel = (c - pc).low_u64();
            if rel == 0 {
                len = expr::as_const(*val).filter(|l| l.fits_u64()).map(|l| l.low_u64());
            } else if rel >= 32 && rel % 32 == 0 {
                words.retain(|(r, _)| *r != rel);
                words.push((rel, *val));
            }
        }
    }
    let len = len?;
    if len == 0 || len > 8 * 32 {
        return None;
    }
    let n = (len + 31) / 32;
    let mut data = vec![expr::konst(U256::from_u64(32)), expr::konst(U256::from_u64(len))];
    for i in 0..n {
        let rel = 32 + 32 * i;
        data.push(words.iter().find(|(r, _)| *r == rel)?.1);
    }
    Some(Term::Return { off: ptr, len: expr::konst(U256::from_u64(64 + 32 * n)), data: Some(data) })
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
        l.nodes[s].stmts.truncate(k - m.dropped);
        // Trailing assignments other than the loop counter keep their place.
        l.nodes[s].stmts.extend(tail.into_iter().filter(|st| !matches!(st, Stmt::Assign { value, .. } if expr::as_const(*value) == Some(U256::ZERO))));
        // The payload stores may sit in the straight-line predecessors of the return node.
        let mut chain: Vec<Stmt> = Vec::new();
        let mut cur = s;
        let mut hops = 0;
        loop {
            let mut these = l.nodes[cur].stmts.clone();
            these.extend(chain);
            chain = these;
            if l.nodes[cur].preds.len() != 1 || hops >= 4 {
                break;
            }
            let p = l.nodes[cur].preds[0];
            if l.nodes[p].succs.len() != 1 || p == cur {
                break;
            }
            cur = p;
            hops += 1;
        }
        l.nodes[s].term = literal_return(&chain, m.ptr).unwrap_or(Term::ReturnDyn { ptr: m.ptr });
        let old_succs = l.nodes[s].succs.clone();
        l.nodes[s].succs.clear();
        for os in old_succs {
            l.edge_assigns.remove(&(s, os));
        }
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

/// Word-copy loops in a lifted graph, described for the lifter (unit node ids). Three forms:
/// a while-loop with the phi on the condition node, a rotated loop with the phi on the body
/// and the test after it, and a body that loops on itself.
pub fn copy_loops(l: &Lifted) -> Vec<CopyLoop> {
    let mut inv: std::collections::HashMap<usize, usize> = std::collections::HashMap::new();
    for (u, ln) in &l.node_map {
        inv.insert(*ln, *u);
    }
    let debug = std::env::var("EVMDEC_DEBUG_LOOPS").is_ok();
    let mut out = Vec::new();
    let step32 = |assigns: &Vec<(ExprId, ExprId)>, var: ExprId| -> bool {
        assigns.iter().any(|(v, val)| {
            *v == var && {
                let (tv, cv) = addends(*val);
                tv == vec![var] && cv == u(32)
            }
        })
    };
    let step = |assigns: &Vec<(ExprId, ExprId)>, var: ExprId| -> Option<(bool, U256)> {
        assigns.iter().find(|(v, _)| *v == var).and_then(|(_, val)| match expr::node(*val) {
            Node::Op(o, v) if (o == op::ADD || o == op::SUB) && v[0] == var => expr::as_const(v[1]).map(|c| (o == op::ADD, c)),
            Node::Op(o, v) if o == op::ADD && v[1] == var => expr::as_const(v[0]).map(|c| (true, c)),
            _ => None,
        })
    };
    for xn in &l.nodes {
        let x = xn.id;
        let Term::Branch { cond, t: Some(t), f } = &xn.term else { continue };
        if !xn.stmts.is_empty() && !(*t == x || *f == x) {
            continue;
        }
        // The body: a successor holding exactly one store, looping back to x (or x itself).
        let is_body = |b: usize| l.nodes[b].stmts.len() == 1 && (b == x || matches!(l.nodes[b].term, Term::Jump(y) if y == x));
        let (b, e) = if is_body(*f) && !is_body(*t) {
            (*f, *t)
        } else if is_body(*t) && !is_body(*f) {
            (*t, *f)
        } else {
            continue;
        };
        let Stmt::MStore { off: bo, val: bv, width: 32 } = &l.nodes[b].stmts[0] else { continue };
        let Some(bs) = mload_addr(*bv) else { continue };
        let (Some(&xu), Some(&bu), Some(&eu)) = (inv.get(&x), inv.get(&b), inv.get(&e)) else { continue };
        if debug {
            eprintln!("[loops]  candidate latch {} pc {:#x} body {} exit {} cond {:?}", x, xn.pc, b, e, expr::node(*cond));
        }
        // Countdown: mem[d] = mem[s]; n -= 32; d += 32; s += 32; while n >= 32 (phi on x).
        if b != x {
            if let (Node::Var(_), Node::Var(_), Some(assigns)) = (expr::node(*bo), expr::node(bs), l.edge_assigns.get(&(b, x))) {
                let (d, sv) = (*bo, bs);
                if let Some(nv) = assigns.iter().find(|(v, _)| *v != d && *v != sv).map(|(v, _)| *v) {
                    let ok_steps = step(assigns, d) == Some((true, u(32))) && step(assigns, sv) == Some((true, u(32))) && step(assigns, nv) == Some((false, u(32)));
                    let lt32 = |c: ExprId| matches!(expr::node(c), Node::Op(op::LT, ref v) if v[0] == nv && expr::as_const(v[1]) == Some(u(32)));
                    let cond_ok = (lt32(*cond) && *t == e) || (matches!(expr::node(*cond), Node::Op(op::ISZERO, ref v) if lt32(v[0])) && *t == b);
                    let slot_of = |var: ExprId| xn.entry_stack.iter().rposition(|y| *y == var).map(|k| xn.entry_stack.len() - 1 - k);
                    if ok_steps && cond_ok && assigns.len() == 3 {
                        if let (Some(n), Some(dslot), Some(sslot)) = (slot_of(nv), slot_of(d), slot_of(sv)) {
                            out.push(CopyLoop { entry: xu, latch: xu, body: bu, exit: eu, shape: CopyShape::Countdown { n, d: dslot, s: sslot } });
                            continue;
                        }
                    }
                }
            }
        }
        // Index forms: a Var shared by the store address and the load address, stepped by 32.
        let (tbo, _) = addends(*bo);
        let (tbs, _) = addends(bs);
        let shared: Vec<ExprId> = tbo.iter().copied().filter(|v| matches!(expr::node(*v), Node::Var(_)) && tbs.contains(v)).collect();
        let Some(iv) = shared.first().copied() else {
            if debug {
                eprintln!("[loops]   reject: no shared counter var in {:?} / {:?}", tbo.iter().map(|e| expr::node(*e)).collect::<Vec<_>>(), tbs.iter().map(|e| expr::node(*e)).collect::<Vec<_>>());
            }
            continue;
        };
        // Where is the phi, and where is the step?
        let (phi_node, rotated) = if b == x {
            (b, true)
        } else if l.edge_assigns.get(&(b, x)).map_or(false, |a| step32(a, iv)) && l.nodes[x].entry_stack.contains(&iv) {
            (x, false)
        } else if l.edge_assigns.get(&(x, b)).map_or(false, |a| step32(a, iv)) && l.nodes[b].entry_stack.contains(&iv) {
            (b, true)
        } else {
            if debug {
                eprintln!("[loops]   reject: no +32 step for the counter (assigns b->x {:?}, x->b {:?})", l.edge_assigns.get(&(b, x)).map(|a| a.len()), l.edge_assigns.get(&(x, b)).map(|a| a.len()));
            }
            continue;
        };
        if b == x && !l.edge_assigns.get(&(b, b)).map_or(false, |a| step32(a, iv)) {
            continue;
        }
        // The condition compares the counter (while) or counter + 32 (rotated) with a bound and
        // continues into the body.
        let counter_term = |c: ExprId| -> bool {
            let (ta, ca) = addends(c);
            ta == vec![iv] && ca == if rotated { u(32) } else { U256::ZERO }
        };
        let continues_on_true = match expr::node(*cond) {
            Node::Op(op::LT, v) if counter_term(v[0]) => Some(true),
            Node::Op(op::GT, v) if counter_term(v[1]) => Some(true),
            Node::Op(op::ISZERO, v) => match expr::node(v[0]) {
                Node::Op(op::LT, w) if counter_term(w[0]) => Some(false),
                Node::Op(op::GT, w) if counter_term(w[1]) => Some(false),
                _ => None,
            },
            _ => None,
        };
        let Some(on_true) = continues_on_true else {
            if debug {
                eprintln!("[loops]   reject: condition shape {:?} (rotated {})", expr::node(*cond), rotated);
            }
            continue;
        };
        if (on_true && *t != b) || (!on_true && *f != b) {
            if debug {
                eprintln!("[loops]   reject: branch direction");
            }
            continue;
        }
        let pn = &l.nodes[phi_node];
        let Some(slot) = pn.entry_stack.iter().rposition(|y| *y == iv).map(|k| pn.entry_stack.len() - 1 - k) else { continue };
        let entry = if rotated { bu } else { xu };
        out.push(CopyLoop { entry, latch: xu, body: bu, exit: eu, shape: CopyShape::Index { slot, rotated } });
    }
    out
}
