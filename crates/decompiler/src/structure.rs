use crate::emit::{self, Names, PayloadKind};
use crate::expr::{self, kind, ExprId, Node};
use crate::lift::{self, Lifted, Stmt, Term};
use crate::opcode as op;
use crate::u256::U256;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet, VecDeque};

struct Graph {
    succs: Vec<Vec<usize>>,
    preds: Vec<Vec<usize>>,
    rpo_index: Vec<usize>,
    idom: Vec<Option<usize>>,
    ipdom: Vec<Option<usize>>,
    reachable: Vec<bool>,
}

fn dominators(
    n: usize,
    entry: usize,
    succs: &[Vec<usize>],
    preds: &[Vec<usize>],
    rpo: &[usize],
    rpo_index: &[usize],
) -> Vec<Option<usize>> {
    let mut idom: Vec<Option<usize>> = vec![None; n];
    idom[entry] = Some(entry);
    let intersect = |mut a: usize, mut b: usize, idom: &Vec<Option<usize>>| -> usize {
        while a != b {
            while rpo_index[a] > rpo_index[b] {
                a = idom[a].expect("processed nodes have an immediate dominator");
            }
            while rpo_index[b] > rpo_index[a] {
                b = idom[b].expect("processed nodes have an immediate dominator");
            }
        }
        a
    };
    let mut changed = true;
    let mut iters = 0;
    while changed && iters < 1000 {
        changed = false;
        iters += 1;
        for &b in rpo {
            if b == entry {
                continue;
            }
            let mut new_idom: Option<usize> = None;
            for &p in &preds[b] {
                if idom[p].is_none() {
                    continue;
                }
                new_idom = Some(match new_idom {
                    None => p,
                    Some(x) => intersect(p, x, &idom),
                });
            }
            if new_idom != idom[b] && new_idom.is_some() {
                idom[b] = new_idom;
                changed = true;
            }
        }
    }
    let _ = succs;
    idom
}

impl Graph {
    fn new(l: &Lifted) -> Graph {
        let n = l.nodes.len();
        let mut succs: Vec<Vec<usize>> = vec![Vec::new(); n];
        for nd in &l.nodes {
            for s in &nd.succs {
                if !succs[nd.id].contains(s) {
                    succs[nd.id].push(*s);
                }
            }
        }
        let mut reachable = vec![false; n];
        let mut order = Vec::new();
        let mut state = vec![0u8; n];
        let mut stack: Vec<(usize, usize)> = vec![(l.entry, 0)];
        state[l.entry] = 1;
        reachable[l.entry] = true;
        while let Some((x, i)) = stack.pop() {
            if i < succs[x].len() {
                stack.push((x, i + 1));
                let s = succs[x][i];
                if state[s] == 0 {
                    state[s] = 1;
                    reachable[s] = true;
                    stack.push((s, 0));
                }
            } else {
                state[x] = 2;
                order.push(x);
            }
        }
        order.reverse();
        let rpo = order;
        let mut rpo_index = vec![usize::MAX; n];
        for (i, &x) in rpo.iter().enumerate() {
            rpo_index[x] = i;
        }
        let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
        for x in 0..n {
            if !reachable[x] {
                continue;
            }
            for &s in &succs[x] {
                preds[s].push(x);
            }
        }
        let idom = dominators(n, l.entry, &succs, &preds, &rpo, &rpo_index);
        let noreturn = noreturn_leaves(l);
        let mut rsuccs: Vec<Vec<usize>> = vec![Vec::new(); n + 1];
        let mut rpreds: Vec<Vec<usize>> = vec![Vec::new(); n + 1];
        for x in 0..n {
            if !reachable[x] {
                continue;
            }
            let live: Vec<usize> = succs[x].iter().copied().filter(|s| !noreturn[*s]).collect();
            if live.is_empty() {
                rsuccs[n].push(x);
                rpreds[x].push(n);
            }
            for s in live {
                rsuccs[s].push(x);
                rpreds[x].push(s);
            }
        }
        {
            let mut to_exit = vec![false; n + 1];
            let mut q = VecDeque::new();
            q.push_back(n);
            to_exit[n] = true;
            while let Some(x) = q.pop_front() {
                for &p in &rsuccs[x] {
                    if !to_exit[p] {
                        to_exit[p] = true;
                        q.push_back(p);
                    }
                }
            }
            for x in 0..n {
                if reachable[x] && !to_exit[x] {
                    rsuccs[n].push(x);
                    rpreds[x].push(n);
                }
            }
        }
        let mut rorder = Vec::new();
        let mut rstate = vec![0u8; n + 1];
        let mut rstack: Vec<(usize, usize)> = vec![(n, 0)];
        rstate[n] = 1;
        while let Some((x, i)) = rstack.pop() {
            if i < rsuccs[x].len() {
                rstack.push((x, i + 1));
                let s = rsuccs[x][i];
                if rstate[s] == 0 {
                    rstate[s] = 1;
                    rstack.push((s, 0));
                }
            } else {
                rorder.push(x);
            }
        }
        rorder.reverse();
        let mut rrpo_index = vec![usize::MAX; n + 1];
        for (i, &x) in rorder.iter().enumerate() {
            rrpo_index[x] = i;
        }
        let ipdom_full = dominators(n + 1, n, &rsuccs, &rpreds, &rorder, &rrpo_index);
        let ipdom: Vec<Option<usize>> = (0..n)
            .map(|x| ipdom_full[x].filter(|d| *d != n && *d != x))
            .collect();
        Graph {
            succs,
            preds,
            rpo_index,
            idom,
            ipdom,
            reachable,
        }
    }

    fn dominates(&self, a: usize, mut b: usize) -> bool {
        loop {
            if a == b {
                return true;
            }
            match self.idom[b] {
                Some(d) if d != b => b = d,
                _ => return false,
            }
        }
    }

    fn common_dominator(&self, mut a: usize, mut b: usize) -> Option<usize> {
        while a != b {
            let lower = match self.rpo_index[a] > self.rpo_index[b] {
                true => &mut a,
                false => &mut b,
            };
            *lower = self.idom[*lower].filter(|d| d != lower)?;
        }
        Some(a)
    }

    fn reached(&self, from: impl Iterator<Item = usize>, barrier: &[usize]) -> HashSet<usize> {
        let mut seen = HashSet::new();
        let mut stack: Vec<usize> = from.collect();
        while let Some(x) = stack.pop() {
            if !barrier.contains(&x) && seen.insert(x) {
                stack.extend(&self.succs[x]);
            }
        }
        seen
    }
}

// Every node on a chain of plain jumps shares the answer of the node the chain ends at.
// Asking each node on its own walked a long chain once per node.
fn noreturn_leaves(l: &Lifted) -> Vec<bool> {
    let mut known: Vec<Option<bool>> = vec![None; l.nodes.len()];
    let mut on_chain = vec![false; l.nodes.len()];
    for start in 0..l.nodes.len() {
        let mut chain = Vec::new();
        let mut x = start;
        let leaf = loop {
            if let Some(leaf) = known[x] {
                break leaf;
            }
            if on_chain[x] {
                break false;
            }
            on_chain[x] = true;
            chain.push(x);
            let nd = &l.nodes[x];
            if !nd.stmts.iter().all(|s| matches!(s, Stmt::MStore { .. })) {
                break false;
            }
            match &nd.term {
                Term::Revert { .. } | Term::Invalid | Term::Infeasible | Term::Unresolved(_) => {
                    break true
                }
                Term::Jump(t) => x = *t,
                _ => break false,
            }
        };
        for x in chain {
            known[x] = Some(leaf);
            on_chain[x] = false;
        }
    }
    known.into_iter().map(|leaf| leaf == Some(true)).collect()
}

struct Loop {
    body: HashSet<usize>,
    exits: Vec<usize>,
}

fn find_loops(g: &Graph) -> HashMap<usize, Loop> {
    let mut loops: HashMap<usize, Loop> = HashMap::new();
    for x in 0..g.succs.len() {
        if !g.reachable[x] {
            continue;
        }
        for &s in &g.succs[x] {
            if g.dominates(s, x) {
                let entry = loops.entry(s).or_insert(Loop {
                    body: HashSet::new(),
                    exits: Vec::new(),
                });
                entry.body.insert(s);
                let mut stack = vec![x];
                while let Some(y) = stack.pop() {
                    if !entry.body.insert(y) {
                        continue;
                    }
                    for &p in &g.preds[y] {
                        if !entry.body.contains(&p) {
                            stack.push(p);
                        }
                    }
                }
            }
        }
    }
    for lp in loops.values_mut() {
        let mut exits: Vec<usize> = Vec::new();
        for &b in &lp.body {
            for &s in &g.succs[b] {
                if !lp.body.contains(&s) && !exits.contains(&s) {
                    exits.push(s);
                }
            }
        }
        exits.sort_by_key(|e| g.rpo_index[*e]);
        lp.exits = exits;
    }
    loops
}

struct Printer<'a> {
    l: &'a Lifted,
    g: Graph,
    loops: HashMap<usize, Loop>,
    names: &'a Names,
    out: String,
    emitted: HashSet<usize>,
    labels: HashSet<usize>,
    nesting: usize,
    loop_stack: Vec<(usize, Option<usize>, usize)>,
    active: HashSet<usize>,
    next_tmp: u32,
    used: Vec<ExprId>,
    facts: Vec<(ExprId, bool, usize)>,
    stale_plan: StalePlan,
    early_reads: StalePlan,
    scope: HashMap<usize, Vec<(ExprId, String)>>,
    left: HashMap<usize, HashMap<ExprId, String>>,
    given: HashMap<(ExprId, String), usize>,
    stored: Vec<(usize, usize, String, ExprId, ExprId)>,
    dead_stores: HashSet<(usize, usize)>,
    put_back: HashSet<(usize, usize)>,
    memory_reads: Vec<Vec<(usize, Span)>>,
    // Filled while the printer's &self methods run, hence the cell.
    skipped: RefCell<HashSet<(usize, usize)>>,
    printed_last: Option<usize>,
}

struct FoldedLog {
    index: usize,
    text: String,
    hidden: Vec<usize>,
}

fn encoded_bytes_logs(stmts: &[Stmt]) -> Vec<FoldedLog> {
    let mut out = Vec::new();
    for (i, s) in stmts.iter().enumerate() {
        let Stmt::Log {
            off, data: None, ..
        } = s
        else {
            continue;
        };
        if i < 4 {
            continue;
        }
        let (
            Stmt::MStore {
                off: o1,
                val: v1,
                width: 32,
                ..
            },
            Stmt::MStore {
                off: o2,
                val: len,
                width: 32,
                ..
            },
            Stmt::Copy {
                kind: op::CALLDATACOPY,
                dest,
                src,
                len: clen,
                ..
            },
            Stmt::MStore {
                off: o4,
                val: v4,
                width: 32,
                ..
            },
        ) = (&stmts[i - 4], &stmts[i - 3], &stmts[i - 2], &stmts[i - 1])
        else {
            continue;
        };
        let fp = *o1;
        let len_node = expr::node(*len);
        if *off != fp
            || expr::as_const(*v1) != Some(U256::from_u64(32))
            || !emit::is_add_const(*o2, fp, 32)
            || !emit::is_add_const(*dest, fp, 64)
            || clen != len
            || expr::as_const(*v4) != Some(U256::ZERO)
            || !expr::contains(*o4, &|nd| *nd == len_node)
        {
            continue;
        }
        let whole = expr::as_const(*src) == Some(U256::ZERO)
            && matches!(len_node, Node::Env(op::CALLDATASIZE, _));
        let text = if whole {
            "abi.encode(msg.data)".to_string()
        } else {
            format!(
                "abi.encode(msg.data[{}:+{}])",
                emit::fmt_expr(*src, &Names::default()),
                emit::fmt_expr(*len, &Names::default())
            )
        };
        out.push(FoldedLog {
            index: i,
            text,
            hidden: vec![i - 4, i - 3, i - 2, i - 1],
        });
    }
    out
}

fn forwarded_calldata(stmts: &[Stmt], hidden: &HashSet<usize>, names: &Names) -> Vec<usize> {
    let live: Vec<usize> = (0..stmts.len()).filter(|i| !hidden.contains(i)).collect();
    let mut folded = Vec::new();
    for pair in live.windows(2) {
        let (
            Stmt::Copy {
                kind: op::CALLDATACOPY,
                dest,
                src,
                len,
                ..
            },
            Stmt::Call {
                in_off,
                in_len,
                input: None,
                ..
            },
        ) = (&stmts[pair[0]], &stmts[pair[1]])
        else {
            continue;
        };
        if dest != in_off || len != in_len {
            continue;
        }
        let whole = expr::as_const(*src) == Some(U256::ZERO)
            && matches!(expr::node(*len), Node::Env(op::CALLDATASIZE, _));
        let text = if whole {
            "msg.data".to_string()
        } else {
            format!(
                "msg.data[{}:+{}]",
                emit::fmt_expr(*src, names),
                emit::fmt_expr(*len, names)
            )
        };
        names.payload_overrides.borrow_mut().insert(*in_off, text);
        folded.push(pair[0]);
    }
    folded
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Overwritten {
    Slot(ExprId, bool),
    Balance,
    Memory(ExprId),
}

fn stale_loads_in(
    e: ExprId,
    what: Overwritten,
    gen: u32,
    skip: Option<ExprId>,
    field: &dyn Fn(ExprId) -> Option<bool>,
    out: &mut Vec<ExprId>,
) {
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if Some(x) == skip || !seen.insert(x) || seen.len() > 20_000 {
            continue;
        }
        match field(x) {
            Some(true) if !out.contains(&x) => out.push(x),
            Some(false) => continue,
            _ => {}
        }
        let stale = match (expr::node(x), what) {
            (Node::SLoad(k, t, g), Overwritten::Slot(key, transient)) => {
                k == key && t == transient && g <= gen
            }
            (Node::Env(op::SELFBALANCE, g), Overwritten::Balance) => g <= gen,
            (
                Node::MLoad(at, g) | Node::CopiedWord(op::MCOPY, at, g),
                Overwritten::Memory(addr),
            ) => at == addr && g <= gen,
            _ => false,
        };
        if stale && !out.contains(&x) {
            out.push(x);
        }
        stack.extend(expr::children(x));
    }
}

// A named field prints by its name, so a new name for the load under it is never reached.
fn named_field(e: ExprId, names: &Names) -> Option<(crate::ssa::FieldRef, u32)> {
    let field = crate::ssa::field_read(e)?;
    emit::field_name(e, names)?;
    let mut inner = expr::children(e);
    inner.extend(inner.clone().into_iter().flat_map(expr::children));
    let version = inner.into_iter().find_map(|part| match expr::node(part) {
        Node::SLoad(key, false, version) if key == field.key => Some(version),
        _ => None,
    })?;
    Some((field, version))
}

fn overwrites(st: &Stmt, names: &Names) -> Option<(Overwritten, u32)> {
    match st {
        Stmt::SStore {
            key,
            transient,
            gen,
            ..
        } => Some((Overwritten::Slot(*key, *transient), *gen)),
        Stmt::Call { gen: Some(g), .. } => Some((Overwritten::Balance, *g)),
        Stmt::Internal {
            gen: Some(g),
            callee,
            ..
        } if !names.pure_callees.contains(callee) => Some((Overwritten::Balance, *g)),
        Stmt::Create { gen, .. } => Some((Overwritten::Balance, *gen)),
        Stmt::MStore {
            off,
            width: 32,
            gen,
            ..
        } if *gen > 0 && !(names.blocks.is_some() && emit::is_free_pointer(*off)) => {
            Some((Overwritten::Memory(*off), *gen - 1))
        }
        _ => None,
    }
}

/* A word copied from memory prints as the word it came from. A write over part of that word
or of a word at a fixed address changes what the name reads from then on. */
fn overlapped(
    st: &Stmt,
    loads: &HashMap<Overwritten, Vec<(ExprId, u32)>>,
    exact: Option<Overwritten>,
    names: &Names,
) -> Vec<(Overwritten, u32)> {
    let at = |e: ExprId| {
        expr::as_const(e)
            .filter(|c| c.fits_u64())
            .map(|c| c.low_u64())
    };
    // An address that stays below the first block the code allocates picks a word among
    // those at fixed places.
    let places = |e: ExprId| {
        at(e).map(|c| (c, c)).or_else(|| {
            let most = names.may_bits(e);
            (most.fits_u64() && most.low_u64() < lift::FREE_POINTER * 2)
                .then(|| (0, most.low_u64()))
        })
    };
    let (start, place, len, gen) = match st {
        Stmt::MStore {
            off, width, gen, ..
        } => (*off, places(*off), Some(u64::from(*width)), *gen),
        Stmt::Copy { dest, len, gen, .. } => (*dest, places(*dest), at(*len), *gen),
        _ => return Vec::new(),
    };
    let Some((lo, last)) = place.filter(|_| gen > 0) else {
        return beside(start, len, gen, loads, exact, names);
    };
    let hi = len.map(|n| last.saturating_add(n));
    let pointer = |a: ExprId| names.blocks.is_some() && emit::is_free_pointer(a);
    let hit =
        |(first, last): (u64, u64)| last.saturating_add(32) > lo && hi.is_none_or(|h| first < h);
    let mut out: Vec<(Overwritten, u32)> = loads
        .keys()
        .filter(|w| Some(**w) != exact)
        .filter_map(|w| match w {
            Overwritten::Memory(a) if !pointer(*a) => places(*a).filter(|p| hit(*p)).map(|_| *w),
            _ => None,
        })
        .map(|w| (w, gen - 1))
        .collect();
    out.sort_by_key(|(w, _)| match w {
        Overwritten::Memory(a) => (at(*a), *a),
        _ => (None, ExprId(0)),
    });
    out
}

/* Two words a few bytes apart through the same pointer share bytes. A read of one made
before a store to the other no longer holds once the store is made. */
fn beside(
    start: ExprId,
    len: Option<u64>,
    gen: u32,
    loads: &HashMap<Overwritten, Vec<(ExprId, u32)>>,
    exact: Option<Overwritten>,
    names: &Names,
) -> Vec<(Overwritten, u32)> {
    let Some(len) = len.filter(|l| *l > 0 && gen > 0) else {
        return Vec::new();
    };
    let (base, from) = expr::split_offset(start);
    if base.is_none() {
        return Vec::new();
    }
    let pointer = |a: ExprId| names.blocks.is_some() && emit::is_free_pointer(a);
    let within = |d: U256, n: u64| d.fits_u64() && d.low_u64() < n;
    let mut out: Vec<(Overwritten, u32)> = loads
        .keys()
        .filter(|w| Some(**w) != exact)
        .filter_map(|w| match w {
            Overwritten::Memory(a) if !pointer(*a) => {
                let (b, d) = expr::split_offset(*a);
                let hit = b == base
                    && (within(d.wrapping_sub(from), len) || within(from.wrapping_sub(d), 32));
                hit.then_some((*w, gen - 1))
            }
            _ => None,
        })
        .collect();
    out.sort_by_key(|(w, _)| match w {
        Overwritten::Memory(a) => *a,
        _ => ExprId(0),
    });
    out
}

fn memory_word(read: ExprId) -> Option<ExprId> {
    match expr::node(read) {
        Node::MLoad(at, _) | Node::CopiedWord(op::MCOPY, at, _) => Some(at),
        _ => None,
    }
}

type Span = (Option<ExprId>, u64, u64);

// A length the code works out leaves the end open.
fn reach(off: ExprId, len: ExprId) -> Span {
    let (base, d) = expr::split_offset(off);
    let fits = |c: U256| c.fits_u64().then(|| c.low_u64());
    let from = fits(d).unwrap_or(0);
    let to = expr::as_const(len).and_then(fits);
    (base, from, to.map_or(u64::MAX, |n| from.saturating_add(n)))
}

fn reads_in(roots: Vec<ExprId>, seen: &mut HashSet<ExprId>, out: &mut Vec<Span>) {
    let word = expr::konst_u64(32);
    let mut pending = roots;
    while let Some(e) = pending.pop() {
        if !seen.insert(e) {
            continue;
        }
        match expr::node(e) {
            Node::MLoad(at, _) | Node::CopiedWord(op::MCOPY, at, _) => out.push(reach(at, word)),
            Node::KeccakMem(off, len, _) => out.push(reach(off, len)),
            _ => {}
        }
        pending.extend(expr::children(e));
    }
}

// What the end of a node and the edges out of it read has the index past the last.
fn memory_reads(l: &Lifted) -> Vec<Vec<(usize, Span)>> {
    let mut all = Vec::with_capacity(l.nodes.len());
    for nd in &l.nodes {
        let mut reads: Vec<(usize, Span)> = Vec::new();
        for (i, st) in nd.stmts.iter().enumerate() {
            let mut found = Vec::new();
            reads_in(lift::stmt_exprs(st), &mut HashSet::new(), &mut found);
            found.extend(match st {
                Stmt::Call { in_off, in_len, .. } => Some(reach(*in_off, *in_len)),
                Stmt::Log { off, len, .. } | Stmt::Create { off, len, .. } => {
                    Some(reach(*off, *len))
                }
                Stmt::Copy {
                    kind: op::MCOPY,
                    src,
                    len,
                    ..
                } => Some(reach(*src, *len)),
                _ => None,
            });
            reads.extend(found.into_iter().map(|read| (i, read)));
        }
        let mut found = Vec::new();
        let mut roots = lift::term_exprs(&nd.term);
        let leaving = l
            .edge_assigns
            .iter()
            .filter(|((from, _), _)| *from == nd.id);
        roots.extend(leaving.flat_map(|(_, assigns)| assigns.iter().map(|(_, v)| *v)));
        reads_in(roots, &mut HashSet::new(), &mut found);
        found.extend(match &nd.term {
            Term::Return { off, len, .. } | Term::Revert { off, len, .. } => {
                Some(reach(*off, *len))
            }
            _ => None,
        });
        reads.extend(found.into_iter().map(|read| (nd.stmts.len(), read)));
        all.push(reads);
    }
    all
}

fn loads_of(l: &Lifted) -> HashMap<Overwritten, Vec<(ExprId, u32)>> {
    let mut loads: HashMap<Overwritten, Vec<(ExprId, u32)>> = HashMap::new();
    let mut seen: HashSet<ExprId> = HashSet::new();
    let mut pending: Vec<ExprId> = l.nodes.iter().flat_map(lift::node_exprs).collect();
    pending.extend(l.edge_assigns.values().flatten().map(|(_, v)| *v));
    while let Some(e) = pending.pop() {
        if !seen.insert(e) {
            continue;
        }
        let read = match expr::node(e) {
            Node::MLoad(addr, version) | Node::CopiedWord(op::MCOPY, addr, version) => {
                Some((Overwritten::Memory(addr), version))
            }
            Node::SLoad(key, transient, version) => {
                Some((Overwritten::Slot(key, transient), version))
            }
            Node::Env(op::SELFBALANCE, version) => Some((Overwritten::Balance, version)),
            _ => None,
        };
        if let Some((what, version)) = read {
            loads.entry(what).or_default().push((e, version));
        }
        pending.extend(expr::children(e));
    }
    loads
}

fn memory_forward(stmts: &[Stmt], i: usize) -> Option<ExprId> {
    let Stmt::MStore {
        val,
        width: 32,
        gen,
        ..
    } = &stmts[i]
    else {
        return None;
    };
    let writes_memory = |s: &Stmt| {
        matches!(
            s,
            Stmt::MStore { .. }
                | Stmt::Copy { .. }
                | Stmt::Call { .. }
                | Stmt::Create { .. }
                | Stmt::Internal { .. }
        )
    };
    // A variable or a parameter has a name of its own, and the word would be printed where
    // the variable is assigned again.
    let named = matches!(expr::node(*val), Node::Var(_) | Node::Arg(_));
    let plain =
        *gen > 0 && !expr::is_const(*val) && !named && !stmts[i + 1..].iter().any(writes_memory);
    plain.then_some(*val)
}

fn prev_name(what: Overwritten, names: &Names) -> String {
    prev_of(&match what {
        Overwritten::Slot(key, transient) => {
            emit::fmt_slot(key, names, emit::SlotSpace::from_transient(transient))
        }
        Overwritten::Balance => "balance".to_string(),
        Overwritten::Memory(addr) => emit::fmt_mem_word(addr, names),
    })
}

fn prev_of(base: &str) -> String {
    let mut id = String::new();
    for c in base.chars() {
        if c.is_ascii_alphanumeric() || c == '_' {
            id.push(c);
        } else if !id.ends_with('_') {
            id.push('_');
        }
    }
    format!("prev_{}", id.trim_end_matches('_'))
}

fn exprs_after(l: &Lifted, nd: &lift::LNode, i: usize, in_block_only: bool) -> Vec<ExprId> {
    let mut after: Vec<ExprId> = Vec::new();
    for later in &nd.stmts[i + 1..] {
        after.extend(lift::stmt_exprs(later));
    }
    after.extend(lift::term_exprs(&nd.term));
    let mut seen = HashSet::new();
    /* A block that only jumps on to one reached from nowhere else is cut in two by the
    code, a folded helper being one way. What follows the jump is still the same run. */
    let mut last = nd.id;
    while let (true, Some(next)) = (in_block_only, run_on(l, last)) {
        if !seen.insert(next) || next == nd.id {
            break;
        }
        after.extend(lift::node_exprs(&l.nodes[next]));
        last = next;
    }
    let mut stack: Vec<usize> = match in_block_only {
        true => Vec::new(),
        false => nd.succs.clone(),
    };
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 5000 {
            continue;
        }
        after.extend(lift::node_exprs(&l.nodes[x]));
        stack.extend(l.nodes[x].succs.iter().copied());
    }
    for ((from, _), assigns) in &l.edge_assigns {
        if *from == nd.id || seen.contains(from) {
            after.extend(assigns.iter().map(|(_, v)| *v));
        }
    }
    after
}

fn run_on(l: &Lifted, from: usize) -> Option<usize> {
    let Term::Jump(next) = l.nodes[from].term else {
        return None;
    };
    let alone = l.nodes[next].preds == [from] && !l.edge_assigns.contains_key(&(from, next));
    alone.then_some(next)
}

fn account_read(e: ExprId) -> Option<(u8, u32)> {
    match expr::node(e) {
        Node::Op(o @ (op::BALANCE | op::EXTCODESIZE | op::EXTCODEHASH), v) => {
            let stamp = v.get(1).and_then(|s| expr::as_const(*s));
            Some((o, stamp.map_or(0, |c| c.low_u64() as u32)))
        }
        _ => None,
    }
}

// A call or a create can change another account's balance and code, and a store through
// one pointer can change what another pointer reads. A read made before such a step and
// used after it gets a name first, or the old and the new read print the same.
fn plan_early_reads(l: &Lifted, names: &Names, kept: &mut Kept) {
    let mut reads: Vec<(ExprId, u32)> = Vec::new();
    let mut loads: Vec<(ExprId, ExprId, u32)> = Vec::new();
    let mut slots: Vec<(ExprId, ExprId, u32)> = Vec::new();
    let mut seen: HashSet<ExprId> = HashSet::new();
    let mut pending: Vec<ExprId> = l.nodes.iter().flat_map(lift::node_exprs).collect();
    pending.extend(l.edge_assigns.values().flatten().map(|(_, v)| *v));
    while let Some(e) = pending.pop() {
        if !seen.insert(e) {
            continue;
        }
        if let Some((_, version)) = account_read(e) {
            reads.push((e, version));
        }
        if let Node::MLoad(at, version) = expr::node(e) {
            loads.push((e, at, version));
        }
        if let Some((field, version)) = named_field(e, names) {
            slots.push((e, field.key, version));
        }
        if let Node::SLoad(key, _, version) = expr::node(e) {
            slots.push((e, key, version));
        }
        pending.extend(expr::children(e));
    }
    // A later read carries the store's own version only when that store may have changed it.
    let reread = |at: ExprId, gen: u32| loads.iter().any(|(_, a, v)| *a == at && *v == gen);
    let mut first: HashMap<ExprId, (u32, usize, usize)> = HashMap::new();
    let mut made: HashMap<ExprId, u32> = HashMap::new();
    for nd in &l.nodes {
        for (i, st) in nd.stmts.iter().enumerate() {
            if let Stmt::MStore { off, gen, .. } = st {
                let old: Vec<ExprId> = loads
                    .iter()
                    .filter(|(_, at, v)| at != off && v < gen && reread(*at, *gen))
                    .map(|(e, _, _)| *e)
                    .collect();
                if old.is_empty() {
                    continue;
                }
                let after = exprs_after(l, nd, i, true);
                for read in old {
                    let target = expr::node(read);
                    if after.iter().any(|e| expr::contains(*e, &|n| *n == target)) {
                        first.entry(read).or_insert((*gen, nd.id, i));
                        kept.overwritten.entry(read).or_default().push((nd.id, i));
                    }
                }
                continue;
            }
            let Some((Overwritten::Balance, gen)) = overwrites(st, names) else {
                continue;
            };
            /* A helper may write any slot, and so may an outside call that calls back in.
            A slot read before either and printed after it would read as its new value. */
            let held = slots
                .iter()
                .filter(|(_, _, version)| *version <= gen)
                .map(|(e, _, version)| (*e, *version));
            let old: Vec<(ExprId, u32)> = reads
                .iter()
                .filter(|(_, version)| *version <= gen)
                .copied()
                .chain(held)
                .collect();
            if old.is_empty() {
                continue;
            }
            let after = exprs_after(l, nd, i, false);
            for (read, version) in old {
                let target = expr::node(read);
                if after.iter().any(|e| expr::contains(*e, &|n| *n == target)) {
                    let at = first.entry(read).or_insert((gen, nd.id, i));
                    if gen < at.0 {
                        *at = (gen, nd.id, i);
                    }
                    made.insert(read, version);
                    kept.overwritten.entry(read).or_default().push((nd.id, i));
                }
            }
        }
    }
    let mut ordered: Vec<(ExprId, (u32, usize, usize))> = first.into_iter().collect();
    ordered.sort_by_key(|(e, at)| (*at, e.0));
    for (read, (gen, node, i)) in ordered {
        let base = match (account_read(read), expr::node(read)) {
            (Some((op::BALANCE, _)), _) => "prev_account_balance".to_string(),
            (Some((op::EXTCODESIZE, _)), _) => "prev_code_size".to_string(),
            (Some(_), _) => "prev_code_hash".to_string(),
            (None, Node::SLoad(key, transient, _)) => {
                prev_name(Overwritten::Slot(key, transient), names)
            }
            (None, Node::MLoad(..)) => "prev_mem".to_string(),
            (None, _) => prev_of(&emit::fmt_expr(read, names)),
        };
        kept.named.push(Snapshot {
            read,
            version: made.get(&read).copied(),
            gen,
            at: (node, i),
            name: base,
            word: None,
            early: true,
        });
    }
}

type StalePlan = HashMap<(usize, usize), Vec<(ExprId, String)>>;

struct Snapshot {
    read: ExprId,
    version: Option<u32>,
    gen: u32,
    at: (usize, usize),
    name: String,
    word: Option<ExprId>,
    early: bool,
}

#[derive(Default)]
struct Kept {
    named: Vec<Snapshot>,
    counts: HashMap<String, u32>,
    overwritten: HashMap<ExprId, Vec<(usize, usize)>>,
    printed_after: HashSet<(ExprId, (usize, usize))>,
}

/* A stored value prints as its slot only until a call or a helper may write the slot.
Past that it prints as what it is made of, and an old read inside it shows. */
fn forward_spans(l: &Lifted, g: &Graph, nd: &lift::LNode, i: usize) -> Vec<(ExprId, bool)> {
    let rest = &nd.stmts[i + 1..];
    let upto = rest.iter().position(may_change_storage);
    let mut out: Vec<(ExprId, bool)> = Vec::new();
    for (k, st) in rest.iter().enumerate() {
        let held = upto.is_none_or(|u| k <= u);
        out.extend(lift::stmt_exprs(st).into_iter().map(|e| (e, held)));
    }
    out.extend(
        lift::term_exprs(&nd.term)
            .into_iter()
            .map(|e| (e, upto.is_none())),
    );
    let kept = |x: usize| {
        x == nd.id || (upto.is_none() && g.dominates(nd.id, x) && unchanged_between(l, g, nd.id, x))
    };
    let mut seen = HashSet::new();
    let mut stack = nd.succs.clone();
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 5000 {
            continue;
        }
        let held = kept(x);
        out.extend(lift::node_exprs(&l.nodes[x]).into_iter().map(|e| (e, held)));
        stack.extend(l.nodes[x].succs.iter().copied());
    }
    for ((from, _), assigns) in &l.edge_assigns {
        if *from == nd.id || seen.contains(from) {
            let held = kept(*from) && (*from != nd.id || upto.is_none());
            out.extend(assigns.iter().map(|(_, v)| (*v, held)));
        }
    }
    out
}

fn unchanged_between(l: &Lifted, g: &Graph, from: usize, to: usize) -> bool {
    let mut seen = HashSet::new();
    let mut stack = g.preds[to].clone();
    while let Some(x) = stack.pop() {
        if x == from || !seen.insert(x) {
            continue;
        }
        if seen.len() > 5000 || l.nodes[x].stmts.iter().any(may_change_storage) {
            return false;
        }
        stack.extend(&g.preds[x]);
    }
    true
}

fn storage_may_change_after(l: &Lifted, nd: &lift::LNode, i: usize) -> bool {
    if nd.stmts[i + 1..].iter().any(may_change_storage) {
        return true;
    }
    let mut seen = HashSet::new();
    let mut stack = nd.succs.clone();
    while let Some(x) = stack.pop() {
        if !seen.insert(x) {
            continue;
        }
        if seen.len() > 5000 || l.nodes[x].stmts.iter().any(may_change_storage) {
            return true;
        }
        stack.extend(l.nodes[x].succs.iter().copied());
    }
    false
}

fn may_change_storage(st: &Stmt) -> bool {
    matches!(
        st,
        Stmt::Call { gen: Some(_), .. } | Stmt::Internal { gen: Some(_), .. } | Stmt::Create { .. }
    )
}

fn version_after(st: &Stmt) -> Option<u32> {
    match st {
        Stmt::SStore { gen, .. } | Stmt::Create { gen, .. } => Some(gen + 1),
        Stmt::Call { gen: Some(gen), .. } | Stmt::Internal { gen: Some(gen), .. } => Some(gen + 1),
        _ => None,
    }
}

fn last_at(nd: &lift::LNode, version: u32) -> Option<usize> {
    let mut current = nd.sgen;
    for (i, st) in nd.stmts.iter().enumerate() {
        if let Some(next) = version_after(st) {
            if current == version {
                return Some(i);
            }
            current = next;
        }
    }
    (current == version).then_some(nd.stmts.len())
}

fn read_version(e: ExprId, names: &Names) -> Option<u32> {
    match expr::node(e) {
        Node::SLoad(_, _, version) | Node::Env(op::SELFBALANCE, version) => Some(version),
        _ => named_field(e, names).map(|(_, version)| version),
    }
}

const MAX_WORD_NAME: usize = 40;

struct Words<'a> {
    l: &'a Lifted,
    g: &'a Graph,
    heads: Vec<usize>,
    assigned: HashMap<ExprId, Vec<usize>>,
    made: HashMap<u32, usize>,
}

fn word_version(read: ExprId) -> Option<u32> {
    match expr::node(read) {
        Node::MLoad(_, version) | Node::CopiedWord(op::MCOPY, _, version) => Some(version),
        _ => None,
    }
}

impl<'a> Words<'a> {
    fn new(l: &'a Lifted, g: &'a Graph) -> Words<'a> {
        let mut heads: Vec<usize> = find_loops(g).into_keys().collect();
        heads.sort_unstable();
        let mut assigned: HashMap<ExprId, Vec<usize>> = HashMap::new();
        for ((_, to), assigns) in &l.edge_assigns {
            for (var, _) in assigns {
                assigned.entry(*var).or_default().push(*to);
            }
        }
        let mut made: HashMap<u32, usize> = HashMap::new();
        for nd in &l.nodes {
            for st in &nd.stmts {
                match st {
                    Stmt::Assign { var, .. } => assigned.entry(*var).or_default().push(nd.id),
                    Stmt::Call { seq, .. }
                    | Stmt::Create { seq, .. }
                    | Stmt::Internal { seq, .. } => {
                        made.insert(*seq, nd.id);
                    }
                    _ => {}
                }
            }
        }
        Words {
            l,
            g,
            heads,
            assigned,
            made,
        }
    }

    // The node's own stores count up from the version it starts with.
    fn version_left(&self, n: usize) -> u32 {
        let stores = self.l.nodes[n].stmts.iter().filter_map(|st| match st {
            Stmt::MStore { gen, .. } | Stmt::Copy { gen, .. } => Some(*gen),
            _ => None,
        });
        stores.fold(self.l.nodes[n].mgen, u32::max)
    }

    fn printable_after(&self, word: ExprId, n: usize) -> bool {
        let mut slots_now = self.l.nodes[n].stmts.iter().filter_map(version_after);
        let slots_now = slots_now.next_back().unwrap_or(self.l.nodes[n].sgen);
        let memory_now = self.version_left(n);
        let above = |at: &usize| self.g.dominates(*at, n);
        let mut seen = HashSet::new();
        let mut pending = vec![word];
        while let Some(e) = pending.pop() {
            if !seen.insert(e) {
                continue;
            }
            if seen.len() > 5000 {
                return false;
            }
            let known = match expr::node(e) {
                Node::Const(_) | Node::Arg(_) | Node::Op(..) | Node::CallDataLoad(_) => true,
                Node::Keccak(..) => true,
                Node::Env(op::SELFBALANCE, version) | Node::SLoad(_, _, version) => {
                    version <= slots_now
                }
                Node::Env(_, seq) => seq == 0,
                Node::MLoad(_, version)
                | Node::KeccakMem(_, _, version)
                | Node::CopiedWord(op::MCOPY, _, version) => version <= memory_now,
                Node::Var(_) => self.assigned.get(&e).is_none_or(|at| at.iter().all(above)),
                Node::CallResult(seq) | Node::CreateResult(seq) | Node::IntRet(seq, _) => {
                    self.made.get(&seq).is_some_and(above)
                }
                _ => false,
            };
            if !known {
                return false;
            }
            pending.extend(expr::children(e));
        }
        true
    }

    /* A loop that writes memory starts each round on a version of its own. A read that
    carries at least that version was made in this round, so a store of the round before
    is not what it saw. Past the head of such a loop the read is a new one and needs no
    name. Short of one, a block a store leads to may hold the read from before the store.

    At a store the name is right when no store to the word leads to it that way. Else
    it goes above the stores, where the word still has what was read and its address can
    be printed. With no such place it stays at the stores, which is still nearer the
    truth than the word read anew after them. */
    fn place(
        &self,
        read: ExprId,
        word: ExprId,
        writes: &[(usize, usize)],
        roots: &[(usize, usize)],
        later: &[usize],
        named: &dyn Fn(&(usize, usize)) -> bool,
    ) -> Vec<(usize, usize)> {
        let (l, g) = (self.l, self.g);
        let Some(version) = word_version(read) else {
            return roots.to_vec();
        };
        let read_anew = |head: &&usize| l.nodes[**head].mgen <= version;
        let heads: Vec<usize> = self.heads.iter().filter(read_anew).copied().collect();
        let stored = writes.iter().flat_map(|w| g.succs[w.0].iter().copied());
        let held = g.reached(stored, &heads);
        let old: Vec<usize> = later.iter().copied().filter(|n| held.contains(n)).collect();
        let below = |n: &usize| roots.iter().any(|r| g.dominates(r.0, *n));
        let serves = |r: &(usize, usize)| named(r) || old.iter().any(|n| g.dominates(r.0, *n));
        let unsure = |r: &(usize, usize)| held.contains(&r.0) && serves(r);
        if old.iter().all(below) && !roots.iter().any(unsure) {
            return roots.to_vec();
        }
        let mut top = Some(roots[0].0);
        for n in roots.iter().map(|w| w.0).chain(old.iter().copied()) {
            top = top.and_then(|a| g.common_dominator(a, n));
        }
        for n in std::iter::successors(top, |n| g.idom[*n].filter(|d| d != n)) {
            if self.version_left(n) < version {
                break;
            }
            if held.contains(&n) || writes.iter().any(|w| w.0 == n) {
                continue;
            }
            if !self.printable_after(word, n) {
                break;
            }
            return vec![(n, l.nodes[n].stmts.len())];
        }
        roots.to_vec()
    }
}

/* A name stands for a value read before its slot was written. Declared at the write, it
has no value on a path that skips the write, so it is declared where every later use
passes and the slot still holds what was read. A place that has the version of the read
again after a write is one where the code may read anew. From there on the slot is
printed as it is. */
fn settle(
    l: &Lifted,
    g: &Graph,
    printed: &Names,
    mut kept: Kept,
    stale: &mut StalePlan,
    early: &mut StalePlan,
) -> HashMap<usize, Vec<(ExprId, String)>> {
    let mut scope: HashMap<usize, Vec<(ExprId, String)>> = HashMap::new();
    let mut names = HashMap::new();
    kept.named.sort_by_key(|s| (s.gen, s.at, s.read.0));
    let mut wanted: HashSet<ExprId> = HashSet::new();
    kept.named.retain(|s| wanted.insert(s.read));
    let mut words: Option<Words> = None;
    let mut held: HashMap<ExprId, HashSet<usize>> = HashMap::new();
    let mut note = |exprs: Vec<ExprId>, node: usize| {
        let mut seen = HashSet::new();
        let mut pending = exprs;
        while let Some(e) = pending.pop() {
            if seen.insert(e) {
                if wanted.contains(&e) {
                    held.entry(e).or_default().insert(node);
                }
                pending.extend(expr::children(e));
            }
        }
    };
    for nd in &l.nodes {
        note(lift::node_exprs(nd), nd.id);
    }
    for ((from, _), assigns) in &l.edge_assigns {
        note(assigns.iter().map(|(_, v)| *v).collect(), *from);
    }
    for s in kept.named {
        let writes = &kept.overwritten[&s.read];
        let target = expr::node(s.read);
        let used_after = |&(node, i): &(usize, usize)| {
            let after = exprs_after(l, &l.nodes[node], i, true);
            after.iter().any(|e| expr::contains(*e, &|n| *n == target))
        };
        let fresh = |n: &usize| {
            s.version
                .is_some_and(|v| last_at(&l.nodes[*n], v).is_some())
        };
        let read_again: Vec<usize> = (0..l.nodes.len()).filter(fresh).collect();
        let holders = held.get(&s.read);
        let uses_after = |w: &(usize, usize)| {
            let later = g.reached(g.succs[w.0].iter().copied(), &read_again);
            let holders = holders.into_iter().flatten().copied();
            let mut uses: Vec<usize> = holders.filter(|n| later.contains(n)).collect();
            uses.extend(used_after(w).then_some(w.0));
            uses
        };
        let after: Vec<Vec<usize>> = writes.iter().map(uses_after).collect();
        let used = writes
            .iter()
            .zip(&after)
            .filter(|(_, uses)| !uses.is_empty());
        let live: Vec<(usize, usize)> = used.map(|(w, _)| *w).collect();
        let under = |a: &(usize, usize), b: &(usize, usize)| match a.0 == b.0 {
            true => a.1 < b.1,
            false => g.dominates(a.0, b.0),
        };
        let roots: Vec<(usize, usize)> = live
            .iter()
            .filter(|w| !live.iter().any(|o| under(o, w)))
            .copied()
            .collect();
        let Some(first) = roots.first() else {
            continue;
        };
        let old: Vec<usize> = after.into_iter().flatten().collect();
        let words = words.get_or_insert_with(|| Words::new(l, g));
        let placed_word = s.word.map(|word| {
            let named = |at: &(usize, usize)| kept.printed_after.contains(&(s.read, *at));
            words.place(s.read, word, writes, &roots, &old, &named)
        });
        let covered = roots.len() == 1 && old.iter().all(|n| g.dominates(first.0, *n));
        let mut above = (!covered).then_some(first.0);
        for n in roots.iter().map(|w| w.0).chain(old.iter().copied()) {
            above = above.and_then(|a| g.common_dominator(a, n));
        }
        let up = std::iter::successors(above, |n| g.idom[*n].filter(|d| d != n));
        let read_at = |n: usize| Some((n, last_at(&l.nodes[n], s.version?)?));
        let defs = match (placed_word, up.into_iter().find_map(read_at)) {
            (Some(placed), _) => placed,
            (None, Some(def)) => vec![def],
            (None, None) if s.early && s.version.is_none() => vec![s.at],
            (None, None) => roots,
        };
        let placed: Vec<usize> = defs.iter().map(|d| d.0).collect();
        let mut base: Option<String> = None;
        let next = live.iter().flat_map(|w| g.succs[w.0].iter().copied());
        let after = g.reached(next, &placed);
        let again = g.reached(after.into_iter().filter(fresh), &placed);
        for def in defs {
            let within: Vec<usize> = (0..l.nodes.len())
                .filter(|n| *n != def.0 && g.dominates(def.0, *n) && !again.contains(n))
                .collect();
            let hoisted = !writes.contains(&def);
            if !hoisted && !used_after(&def) && !old.iter().any(|n| within.contains(n)) {
                continue;
            }
            let plan = match !s.early && def == s.at {
                true => &mut *stale,
                false => &mut *early,
            };
            // An address that is itself read from memory through a chain makes no name.
            let base = base.get_or_insert_with(|| match s.word {
                Some(word) => Some(prev_name(Overwritten::Memory(word), printed))
                    .filter(|name| name.len() <= MAX_WORD_NAME)
                    .unwrap_or_else(|| "prev_mem".to_string()),
                None => s.name.clone(),
            });
            // Reads of one slot share a name. A call's reads are of different things.
            let name = names.entry((def, base.clone(), s.early.then_some(s.read)));
            let name = name.or_insert_with(|| numbered(&mut kept.counts, base));
            plan.entry(def).or_default().push((s.read, name.clone()));
            for n in within {
                scope.entry(n).or_default().push((s.read, name.clone()));
            }
        }
    }
    scope
}

fn numbered(counts: &mut HashMap<String, u32>, base: &str) -> String {
    let n = counts.entry(base.to_string()).or_insert(0);
    *n += 1;
    match *n {
        1 => base.to_string(),
        n => base.replacen("prev_", &format!("prev{n}_"), 1),
    }
}

// Printing these loads as the slot name would read the new value.
fn plan_stale_loads(l: &Lifted, g: &Graph, names: &Names, kept: &mut Kept) -> StalePlan {
    let mut plan: HashMap<(usize, usize), Vec<(ExprId, String)>> = HashMap::new();
    let mut found: Vec<(usize, usize, Overwritten, u32, Vec<ExprId>)> = Vec::new();
    let loads = loads_of(l);
    for nd in &l.nodes {
        for (i, st) in nd.stmts.iter().enumerate() {
            let exact = overwrites(st, names);
            let partly = overlapped(st, &loads, exact.map(|w| w.0), names);
            for (what, gen) in exact.into_iter().chain(partly) {
                // Only a read made before the write can be stale.
                // Without one, looking through everything after the write finds nothing.
                let old = loads.get(&what).into_iter().flatten();
                let old: Vec<ExprId> = old.filter(|(_, v)| *v <= gen).map(|(e, _)| *e).collect();
                if old.is_empty() {
                    continue;
                }
                let in_block_only = matches!(what, Overwritten::Memory(_));
                let after = exprs_after(l, nd, i, in_block_only);
                let forwarded = match st {
                    Stmt::SStore { val, .. } if !expr::is_const(*val) => Some(*val),
                    _ => None,
                };
                let skip = match Some(what) == exact.map(|w| w.0) {
                    true => forwarded.or(memory_forward(&nd.stmts, i)),
                    false => None,
                };
                let written = match st {
                    Stmt::SStore { key, val, .. } => crate::ssa::field_writes(*key, *val),
                    _ => Vec::new(),
                };
                let field = |x: ExprId| {
                    let Overwritten::Slot(key, false) = what else {
                        return None;
                    };
                    let (read, version) = named_field(x, names).filter(|(f, _)| f.key == key)?;
                    let apart = |w: &crate::ssa::FieldWrite| {
                        w.bit_offset >= read.bit_offset + read.bits
                            || read.bit_offset >= w.bit_offset + w.bits
                    };
                    let kept = !written.is_empty() && written.iter().all(apart);
                    Some(!kept && version <= gen)
                };
                let mut stale: Vec<ExprId> = Vec::new();
                match forwarded.is_some() && storage_may_change_after(l, nd, i) {
                    true => {
                        for (e, held) in forward_spans(l, g, nd, i) {
                            let skip = skip.filter(|_| held);
                            stale_loads_in(e, what, gen, skip, &field, &mut stale);
                        }
                    }
                    false => {
                        for e in after {
                            stale_loads_in(e, what, gen, skip, &field, &mut stale);
                        }
                    }
                }
                /* The code may hold what it read from a word on the stack past the store,
                so the read is looked for in every later block, not only in this one. */
                if in_block_only {
                    let found: HashSet<ExprId> = stale.iter().copied().collect();
                    kept.printed_after
                        .extend(found.iter().map(|e| (*e, (nd.id, i))));
                    stale.extend(old.into_iter().filter(|e| !found.contains(e)));
                }
                if stale.is_empty() {
                    continue;
                }
                found.push((nd.id, i, what, gen, stale));
            }
        }
    }
    let mut first_gen: HashMap<ExprId, u32> = HashMap::new();
    for (_, _, _, gen, stale) in &found {
        for e in stale {
            let g = first_gen.entry(*e).or_insert(*gen);
            *g = (*g).min(*gen);
        }
    }
    for (node, i, what, gen, stale) in found {
        let per_store = matches!(what, Overwritten::Memory(_));
        for e in &stale {
            kept.overwritten.entry(*e).or_default().push((node, i));
        }
        let mine: Vec<ExprId> = stale
            .into_iter()
            .filter(|e| per_store || first_gen.get(e) == Some(&gen))
            .collect();
        if mine.is_empty() {
            continue;
        }
        let mut tmps: HashMap<String, String> = HashMap::new();
        for read in mine {
            // Printing an address numbers its variables, so a word is named once it is kept.
            if let Overwritten::Memory(word) = what {
                kept.named.push(Snapshot {
                    read,
                    version: None,
                    gen,
                    at: (node, i),
                    name: String::new(),
                    word: Some(word),
                    early: false,
                });
                continue;
            }
            let name = match emit::field_name(read, names) {
                Some(field) => prev_of(&field),
                None => prev_name(what, names),
            };
            if let Some(version) = read_version(read, names) {
                kept.named.push(Snapshot {
                    read,
                    version: Some(version),
                    gen,
                    at: (node, i),
                    name,
                    word: None,
                    early: false,
                });
                continue;
            }
            let tmp = tmps.entry(name.clone());
            let tmp = tmp.or_insert_with(|| numbered(&mut kept.counts, &name));
            plan.entry((node, i)).or_default().push((read, tmp.clone()));
        }
    }
    plan
}

type Peel = (Vec<(ExprId, ExprId)>, Vec<(usize, usize)>);

fn with_init(e: ExprId, init: &HashMap<ExprId, ExprId>) -> ExprId {
    expr::substitute(
        e,
        &|n| match n {
            Node::Var(_) => init.get(&expr::intern(n.clone())).copied(),
            _ => None,
        },
        &mut HashMap::new(),
    )
}

pub fn reroll_peeled_loops(l: &Lifted) -> Lifted {
    let g = Graph::new(l);
    let loops = find_loops(&g);
    let mut out = l.clone();
    let mut changed = false;
    let mut consumed: HashSet<usize> = HashSet::new();
    let mut headers: Vec<usize> = loops.keys().copied().collect();
    headers.sort_by_key(|h| g.rpo_index[*h]);
    for h in headers {
        let lp = &loops[&h];
        let mut found: Option<(usize, usize, Peel)> = None;
        'search: for hp in 0..l.nodes.len() {
            if !g.reachable[hp] || consumed.contains(&hp) || lp.body.contains(&hp) {
                continue;
            }
            for &q0 in &lp.body {
                if l.nodes[hp].block != l.nodes[q0].block
                    || l.nodes[hp].entry_stack.len() != l.nodes[q0].entry_stack.len()
                    || g.preds[hp].iter().any(|p| lp.body.contains(p))
                {
                    continue;
                }
                if let Some(peel) = peel_of(l, lp, q0, hp) {
                    found = Some((hp, q0, peel));
                    break 'search;
                }
            }
        }
        let Some((hp, q0, (init, pairs))) = found else {
            continue;
        };
        let preds: Vec<usize> = g.preds[hp].clone();
        for p in preds {
            let m: HashMap<usize, usize> = HashMap::from([(hp, q0)]);
            out.nodes[p].term = remap_term_nodes(&out.nodes[p].term, &m);
            for sx in out.nodes[p].succs.iter_mut() {
                if *sx == hp {
                    *sx = q0;
                }
            }
            let mut assigns = out.edge_assigns.remove(&(p, hp)).unwrap_or_default();
            assigns.extend(init.iter().map(|(v, x)| (*v, *x)));
            out.edge_assigns.insert((p, q0), assigns);
        }
        consumed.extend(pairs.iter().map(|(p, _)| *p));
        changed = true;
    }
    if !changed {
        return l.clone();
    }
    for nd in out.nodes.iter_mut() {
        nd.preds.clear();
    }
    let edges: Vec<(usize, usize)> = out
        .nodes
        .iter()
        .flat_map(|nd| nd.succs.iter().map(move |s| (nd.id, *s)))
        .collect();
    for (from, to) in edges {
        if !out.nodes[to].preds.contains(&from) {
            out.nodes[to].preds.push(from);
        }
    }
    out
}

fn peel_of(l: &Lifted, lp: &Loop, q0: usize, hp: usize) -> Option<Peel> {
    let mut pairs: Vec<(usize, usize)> = vec![(hp, q0)];
    let mut i = 0;
    while i < pairs.len() {
        let (p, q) = pairs[i];
        i += 1;
        let (ps, qs) = (&l.nodes[p].succs, &l.nodes[q].succs);
        if ps.len() != qs.len() {
            return None;
        }
        for (&a, &b) in ps.iter().zip(qs) {
            if a == b {
                continue;
            }
            if lp.body.contains(&a) || l.nodes[a].block != l.nodes[b].block {
                return None;
            }
            match pairs.iter().find(|(x, _)| *x == a) {
                Some((_, y)) if *y != b => return None,
                Some(_) => {}
                None => pairs.push((a, b)),
            }
        }
        if pairs.len() > 96 {
            return None;
        }
    }
    let mut sub: HashMap<ExprId, ExprId> = HashMap::new();
    let mut derived: Vec<(ExprId, ExprId)> = Vec::new();
    for (p, q) in &pairs {
        let (sp, sq) = (&l.nodes[*p].entry_stack, &l.nodes[*q].entry_stack);
        if sp.len() != sq.len() {
            return None;
        }
        for (a, b) in sp.iter().zip(sq) {
            if a == b {
                continue;
            }
            if !matches!(expr::node(*b), Node::Var(_)) {
                derived.push((*a, *b));
                continue;
            }
            if sub.insert(*b, *a).is_some_and(|old| old != *a) {
                return None;
            }
        }
    }
    if sub.is_empty() {
        return None;
    }
    for (a, b) in derived {
        if with_init(b, &sub) != a {
            return None;
        }
    }
    let subst = |e: ExprId| with_init(e, &sub);
    let same_stmts = |p: usize, q: usize| {
        let mut rest = l.nodes[p].stmts.iter();
        let mut next = rest.next();
        for sq in &l.nodes[q].stmts {
            let mapped = lift::map_stmt(sq, &subst);
            if next.is_some_and(|sp| mapped == *sp) {
                next = rest.next();
                continue;
            }
            let trivially_true = matches!(
                mapped,
                Stmt::Require { cond, .. } if expr::as_const(cond).is_some_and(|c| !c.is_zero())
            );
            if !trivially_true {
                return false;
            }
        }
        next.is_none()
    };
    let same_term = |p: usize, q: usize| match (&l.nodes[p].term, &l.nodes[q].term) {
        (Term::Branch { cond: a, .. }, Term::Branch { cond: b, .. }) => subst(*b) == *a,
        (Term::Jump(_), Term::Jump(_)) => true,
        (ta, tb) if l.nodes[p].succs.is_empty() && l.nodes[q].succs.is_empty() => {
            lift::map_term(tb, &subst) == *ta
        }
        _ => false,
    };
    let assigns_of = |x: usize, y: usize| -> HashMap<ExprId, ExprId> {
        l.edge_assigns
            .get(&(x, y))
            .map(|v| v.iter().copied().collect())
            .unwrap_or_default()
    };
    let same_edges = |p: usize, q: usize| {
        l.nodes[p]
            .succs
            .iter()
            .zip(&l.nodes[q].succs)
            .all(|(&a, &b)| {
                let (ca, la) = (assigns_of(p, a), assigns_of(q, b));
                if a == b {
                    let mut vars: Vec<ExprId> = ca.keys().chain(la.keys()).copied().collect();
                    vars.sort();
                    vars.dedup();
                    vars.iter().all(|var| {
                        let from_copy = ca.get(var).copied().unwrap_or(*var);
                        let from_loop = subst(la.get(var).copied().unwrap_or(*var));
                        from_copy == from_loop
                    })
                } else {
                    let norm = |m: &HashMap<ExprId, ExprId>, s: &dyn Fn(ExprId) -> ExprId| {
                        let mut v: Vec<(ExprId, ExprId)> =
                            m.iter().map(|(var, val)| (s(*var), s(*val))).collect();
                        v.retain(|(var, val)| var != val);
                        v.sort();
                        v
                    };
                    norm(&ca, &|e| e) == norm(&la, &subst)
                }
            })
    };
    for (p, q) in &pairs {
        if !same_stmts(*p, *q) {
            return None;
        }
        if !same_term(*p, *q) {
            return None;
        }
        if !same_edges(*p, *q) {
            return None;
        }
    }
    let init: Vec<(ExprId, ExprId)> = l.nodes[q0]
        .entry_stack
        .iter()
        .zip(&l.nodes[hp].entry_stack)
        .filter(|(b, a)| a != b)
        .map(|(b, a)| (*b, *a))
        .collect();
    if init.is_empty() {
        return None;
    }
    Some((init, pairs))
}

fn remap_term_nodes(t: &Term, m: &HashMap<usize, usize>) -> Term {
    let map = |x: usize| *m.get(&x).unwrap_or(&x);
    match t {
        Term::Jump(x) => Term::Jump(map(*x)),
        Term::Branch { cond, t, f } => Term::Branch {
            cond: *cond,
            t: t.map(map),
            f: map(*f),
        },
        Term::Switch { target, cases } => Term::Switch {
            target: *target,
            cases: cases.iter().map(|c| map(*c)).collect(),
        },
        other => other.clone(),
    }
}

fn stores_dead_until_exit(l: &Lifted) -> HashSet<(usize, usize)> {
    let mentions_memory = |e: ExprId| {
        expr::contains(e, &|n| {
            matches!(
                n,
                Node::MLoad(..) | Node::KeccakMem(..) | Node::CopiedWord(..)
            )
        })
    };
    let reads_memory = |s: &Stmt| match s {
        Stmt::MStore { val, .. } => mentions_memory(*val),
        Stmt::Copy { kind, .. } => *kind == op::MCOPY,
        Stmt::SStore { .. } | Stmt::Assign { .. } | Stmt::Drop(_) | Stmt::Require { .. } => {
            lift::stmt_exprs(s).iter().any(|e| mentions_memory(*e))
        }
        Stmt::Log { topics, data, .. } => match data {
            None => true,
            Some(d) => topics.iter().chain(d).any(|e| mentions_memory(*e)),
        },
        Stmt::Call { .. } | Stmt::Create { .. } | Stmt::Internal { .. } => true,
    };
    let term_reads_memory = |t: &Term| match t {
        Term::Return { data, .. } | Term::Revert { data, .. } => match data {
            None => true,
            Some(d) => d.iter().any(|e| mentions_memory(*e)),
        },
        // What a helper wrote is the caller's to read after it returns.
        Term::ReturnDyn { .. }
        | Term::Unresolved(_)
        | Term::Switch { .. }
        | Term::InternalReturn(_) => true,
        _ => lift::term_exprs(t).iter().any(|e| mentions_memory(*e)),
    };
    let mut reads_ahead: Vec<bool> = vec![false; l.nodes.len()];
    for nd in &l.nodes {
        let own = nd.stmts.iter().any(&reads_memory)
            || term_reads_memory(&nd.term)
            || l.edge_assigns
                .iter()
                .any(|((from, _), a)| *from == nd.id && a.iter().any(|(_, v)| mentions_memory(*v)));
        reads_ahead[nd.id] = own;
    }
    loop {
        let mut changed = false;
        for nd in &l.nodes {
            if !reads_ahead[nd.id] && nd.succs.iter().any(|s| reads_ahead[*s]) {
                reads_ahead[nd.id] = true;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let mut dead = HashSet::new();
    for nd in &l.nodes {
        if nd.succs.iter().any(|s| reads_ahead[*s]) || term_reads_memory(&nd.term) {
            continue;
        }
        if l.edge_assigns
            .iter()
            .any(|((from, _), a)| *from == nd.id && a.iter().any(|(_, v)| mentions_memory(*v)))
        {
            continue;
        }
        for (i, s) in nd.stmts.iter().enumerate().rev() {
            if reads_memory(s) {
                break;
            }
            if matches!(s, Stmt::MStore { .. } | Stmt::Copy { .. }) {
                dead.insert((nd.id, i));
            }
        }
    }
    dead
}

// A later overwrite does not end a store's life.
// A store into a named block is left alone. The block's line is built from it.
fn unread_fixed_stores(l: &Lifted, names: &Names) -> HashSet<(usize, usize)> {
    let fixed = |s: &Stmt| match s {
        Stmt::MStore { off, width, .. } if emit::block_ref(*off, names).is_none() => {
            expr::as_const(*off)
                .filter(|c| c.fits_u64())
                .map(|c| (c.low_u64(), u64::from(*width)))
        }
        _ => None,
    };
    if !l
        .nodes
        .iter()
        .flat_map(|nd| &nd.stmts)
        .any(|s| fixed(s).is_some())
    {
        return HashSet::new();
    }
    let callee = |pc: usize| names.callee_reads.as_ref().and_then(|m| m.get(&pc));
    let returns_to_reader = l.ret_slot.is_some();
    let tails: Vec<lift::MemoryReads> = l
        .nodes
        .iter()
        .map(|nd| {
            let mut reads = lift::MemoryReads::default();
            reads.term(&nd.term, returns_to_reader);
            let carried = l
                .edge_assigns
                .iter()
                .filter(|((from, _), _)| *from == nd.id)
                .flat_map(|(_, assigns)| assigns.iter().map(|(_, v)| *v));
            reads.exprs(carried);
            reads
        })
        .collect();
    let per_stmt: Vec<Vec<lift::MemoryReads>> = l
        .nodes
        .iter()
        .map(|nd| {
            nd.stmts
                .iter()
                .map(|s| {
                    let mut reads = lift::MemoryReads::default();
                    reads.stmt(s, &callee);
                    reads
                })
                .collect()
        })
        .collect();
    let nothing = lift::MemoryReads::default();
    let mut dead: HashSet<(usize, usize)> = HashSet::new();
    loop {
        let read_by = |n: usize, i: usize| match dead.contains(&(n, i)) {
            true => &nothing,
            false => &per_stmt[n][i],
        };
        let mut from_here: Vec<lift::MemoryReads> = l
            .nodes
            .iter()
            .map(|nd| {
                let mut reads = tails[nd.id].clone();
                for i in 0..nd.stmts.len() {
                    reads.add(read_by(nd.id, i));
                }
                reads
            })
            .collect();
        loop {
            let mut changed = false;
            for nd in &l.nodes {
                for succ in &nd.succs {
                    let ahead = from_here[*succ].clone();
                    changed |= from_here[nd.id].add(&ahead);
                }
            }
            if !changed {
                break;
            }
        }
        let mut found = HashSet::new();
        for nd in &l.nodes {
            let mut after = tails[nd.id].clone();
            for succ in &nd.succs {
                after.add(&from_here[*succ]);
            }
            for (i, s) in nd.stmts.iter().enumerate().rev() {
                if fixed(s).is_some_and(|(addr, len)| !after.reads(addr, len)) {
                    found.insert((nd.id, i));
                } else {
                    after.add(read_by(nd.id, i));
                }
            }
        }
        if found == dead {
            return dead;
        }
        dead = found;
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
enum Pos {
    Stmt(usize),
    Term,
    Edge,
}

// The walk ends once enough are found. Counting them all made naming quadratic.
fn has_operations(e: ExprId, wanted: usize) -> bool {
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    let mut found = 0;
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 2000 {
            continue;
        }
        match expr::node(x) {
            Node::Op(op::AND, v)
                if v.iter()
                    .any(|a| expr::as_const(*a).is_some_and(|m| m.is_low_mask())) => {}
            Node::Op(..) => found += 1,
            _ => {}
        }
        if found >= wanted {
            return true;
        }
        stack.extend(expr::children(x));
    }
    false
}

// Memory reads are never bound. A temporary would hide which version of memory they read.
fn bindable(e: ExprId) -> bool {
    let unbound = kind::MLOAD | kind::KECCAK_MEM | kind::COPIED_WORD | kind::UNKNOWN;
    !expr::is_boolean(e) && !expr::is_const(e) && !expr::holds(e, unbound) && has_operations(e, 2)
}

// Counts are carried down the shared graph. Walking each repetition again is exponential.
// Storage keys and hashes stay whole. A bound key would lose the slot's name.
// The packing of an encoded word stays whole. The printer undoes it to show the arguments.
fn bindable_subexprs(e: ExprId, encoded: bool) -> Vec<(ExprId, usize)> {
    let mut out: Vec<(ExprId, usize)> = Vec::new();
    let packs = |x: ExprId, encoded: bool| {
        encoded
            && matches!(expr::node(x), Node::Op(o, _) if matches!(o, op::OR | op::SHL | op::SHR | op::AND | op::MUL | op::DIV))
            && expr::children(x)
                .iter()
                .any(|c| expr::as_const(*c).is_some())
    };
    let whole = |x: ExprId| {
        matches!(
            expr::node(x),
            Node::SLoad(..) | Node::Keccak(..) | Node::KeccakMem(..)
        )
    };
    let operands = |x: ExprId| match whole(x) {
        true => Vec::new(),
        false => expr::children(x),
    };
    let mut order: Vec<(ExprId, bool)> = Vec::new();
    let mut seen: HashSet<(ExprId, bool)> = HashSet::new();
    let mut stack: Vec<((ExprId, bool), bool)> = vec![((e, encoded), false)];
    while let Some((state, done)) = stack.pop() {
        if done {
            order.push(state);
            continue;
        }
        if !seen.insert(state) {
            continue;
        }
        stack.push((state, true));
        let inner = packs(state.0, state.1);
        for c in operands(state.0).into_iter().rev() {
            stack.push(((c, inner), false));
        }
    }
    let mut times: HashMap<(ExprId, bool), usize> = HashMap::from([((e, encoded), 1)]);
    for state in order.iter().rev() {
        let n = times.get(state).copied().unwrap_or(0);
        let inner = packs(state.0, state.1);
        for c in operands(state.0) {
            let t = times.entry((c, inner)).or_insert(0);
            *t = t.saturating_add(n);
        }
    }
    let mut place: HashMap<ExprId, usize> = HashMap::new();
    for state in &order {
        let (x, encoded) = *state;
        if whole(x) || packs(x, encoded) || !bindable(x) {
            continue;
        }
        let n = times.get(state).copied().unwrap_or(0);
        match place.get(&x) {
            Some(at) => out[*at].1 = out[*at].1.saturating_add(n),
            None => {
                place.insert(x, out.len());
                out.push((x, n));
            }
        }
    }
    out
}

fn term_reads(t: &Term) -> Vec<(ExprId, bool)> {
    match t {
        Term::Branch { cond, .. } => vec![(*cond, false)],
        Term::Return { data: Some(d), .. } | Term::Revert { data: Some(d), .. } => {
            d.iter().map(|w| (*w, true)).collect()
        }
        Term::SelfDestruct(a) => vec![(*a, false)],
        Term::InternalReturn(vals) => vals.iter().map(|v| (*v, false)).collect(),
        _ => vec![],
    }
}

fn vars_in(e: ExprId) -> HashSet<ExprId> {
    let mut out = HashSet::new();
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 5000 {
            continue;
        }
        if matches!(expr::node(x), Node::Var(_)) {
            out.insert(x);
        }
        stack.extend(expr::children(x));
    }
    out
}

fn stmt_reads(s: &Stmt, names: &Names) -> Vec<(ExprId, bool)> {
    let plain = |v: &[ExprId]| v.iter().map(|e| (*e, false)).collect::<Vec<_>>();
    let words = |v: &[ExprId]| v.iter().map(|e| (*e, true)).collect::<Vec<_>>();
    match s {
        Stmt::Assign { value, .. } => vec![(*value, false)],
        Stmt::Drop(_) | Stmt::Copy { .. } => vec![],
        Stmt::MStore { val, .. } => vec![(*val, true)],
        Stmt::SStore { key, val, .. } => {
            if emit::packed_write(*key, *val).is_some() {
                vec![]
            } else {
                vec![(*val, false)]
            }
        }
        Stmt::Log { topics, data, .. } => {
            let mut v = plain(topics);
            if let Some(d) = data {
                v.extend(words(d));
            }
            v
        }
        Stmt::Call {
            gas,
            addr,
            value,
            input,
            input_head,
            layout,
            ..
        } => {
            let mut v = vec![(*gas, false), (*addr, false)];
            if let Some(x) = value {
                v.push((*x, false));
            }
            match (layout, input) {
                (Some(pieces), _) => v.extend(pieces.iter().map(|(e, _)| (*e, true))),
                (None, Some(w)) => v.extend(words(w)),
                (None, None) => v.extend(words(input_head)),
            }
            v
        }
        Stmt::Create {
            value, salt, init, ..
        } => {
            let mut v = vec![(*value, false)];
            if let Some(x) = salt {
                v.push((*x, false));
            }
            if let Some(d) = init {
                v.extend(words(d));
            }
            v
        }
        Stmt::Internal { args, .. } => plain(args),
        Stmt::Require { cond, data, .. } => {
            if emit::is_hidden_require(*cond, data.as_deref(), names) {
                vec![]
            } else {
                let mut v = vec![(*cond, false)];
                if let Some(d) = data {
                    v.extend(words(d));
                }
                v
            }
        }
    }
}

fn result_seqs(e: ExprId) -> HashSet<u32> {
    let mut out = HashSet::new();
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 5000 {
            continue;
        }
        match expr::node(x) {
            Node::CallResult(s)
            | Node::CreateResult(s)
            | Node::ReturnData(s, _)
            | Node::IntRet(s, _) => {
                out.insert(s);
            }
            _ => {}
        }
        stack.extend(expr::children(x));
    }
    out
}

fn common_dominator(g: &Graph, nodes: &[usize]) -> usize {
    let chain = |mut x: usize| -> Vec<usize> {
        let mut v = vec![x];
        while let Some(d) = g.idom[x] {
            if d == x {
                break;
            }
            v.push(d);
            x = d;
        }
        v
    };
    let mut common = chain(nodes[0]);
    for n in &nodes[1..] {
        let c = chain(*n);
        common.retain(|x| c.contains(x));
    }
    common[0]
}

fn newest_gen(e: ExprId) -> u32 {
    let mut g = 0;
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 5000 {
            continue;
        }
        match expr::node(x) {
            Node::SLoad(_, _, v) | Node::Env(op::SELFBALANCE, v) => g = g.max(v),
            _ => {}
        }
        stack.extend(expr::children(x));
    }
    g
}

fn available_at(
    l: &Lifted,
    g: &Graph,
    names: &Names,
    d: usize,
    frontier: &[(usize, Pos)],
    e: ExprId,
) -> bool {
    let reads = vars_in(e);
    let seqs = result_seqs(e);
    let loaded = newest_gen(e);
    let mut from_d = HashSet::new();
    let mut stack: Vec<usize> = l.nodes[d].succs.clone();
    while let Some(x) = stack.pop() {
        if x == d || !from_d.insert(x) || from_d.len() > 5000 {
            continue;
        }
        stack.extend(l.nodes[x].succs.iter().copied());
    }
    let mut to_front = HashSet::new();
    let mut stack: Vec<usize> = frontier.iter().map(|(n, _)| *n).collect();
    while let Some(x) = stack.pop() {
        if !to_front.insert(x) || to_front.len() > 5000 {
            continue;
        }
        if x != d {
            stack.extend(g.preds[x].iter().copied());
        }
    }
    let clean_stmt = |s: &Stmt| match s {
        Stmt::SStore { gen, .. } | Stmt::Create { gen, .. } => *gen >= loaded,
        Stmt::Call { gen, seq, .. } => gen.is_none_or(|g| g >= loaded) && !seqs.contains(seq),
        Stmt::Internal {
            callee, seq, gen, ..
        } => {
            (names.pure_callees.contains(callee) || gen.is_none_or(|g| g >= loaded))
                && !seqs.contains(seq)
        }
        Stmt::Assign { var, .. } => !reads.contains(var),
        _ => true,
    };
    let clean_edges = |x: usize| {
        l.edge_assigns
            .iter()
            .filter(|((from, _), _)| *from == x)
            .all(|(_, assigns)| assigns.iter().all(|(v, _)| !reads.contains(v)))
    };
    if !clean_edges(d) {
        return false;
    }
    for &x in from_d.intersection(&to_front) {
        if x == d {
            continue;
        }
        let use_pos = frontier
            .iter()
            .filter(|(n, _)| *n == x)
            .map(|(_, p)| *p)
            .min();
        let passes_on = frontier
            .iter()
            .any(|(u, _)| *u != x && from_d.contains(u) && reaches_within(l, x, *u, &from_d));
        let limit = match (use_pos, passes_on) {
            (Some(Pos::Stmt(i)), false) => i,
            _ => l.nodes[x].stmts.len(),
        };
        if l.nodes[x].stmts[..limit].iter().any(|s| !clean_stmt(s)) {
            return false;
        }
        if limit == l.nodes[x].stmts.len() && !clean_edges(x) {
            return false;
        }
    }
    true
}

fn reaches(l: &Lifted, a: usize, b: usize) -> bool {
    let mut seen = HashSet::new();
    let mut stack: Vec<usize> = l.nodes[a].succs.clone();
    while let Some(x) = stack.pop() {
        if x == b {
            return true;
        }
        if !seen.insert(x) || seen.len() > 5000 {
            continue;
        }
        stack.extend(l.nodes[x].succs.iter().copied());
    }
    false
}

fn reaches_within(l: &Lifted, a: usize, b: usize, within: &HashSet<usize>) -> bool {
    let mut seen = HashSet::new();
    let mut stack: Vec<usize> = l.nodes[a].succs.clone();
    while let Some(x) = stack.pop() {
        if x == b {
            return true;
        }
        if !within.contains(&x) || !seen.insert(x) || seen.len() > 5000 {
            continue;
        }
        stack.extend(l.nodes[x].succs.iter().copied());
    }
    false
}

pub fn bind_shared(l: &Lifted, names: &Names) -> (Lifted, Bindings) {
    let g = Graph::new(l);
    let mut uses: HashMap<ExprId, Vec<(usize, Pos)>> = HashMap::new();
    let mut count: HashMap<ExprId, usize> = HashMap::new();
    let mut first_seen: HashMap<ExprId, usize> = HashMap::new();
    let mut note = |(e, encoded): (ExprId, bool), at: (usize, Pos)| {
        for (x, k) in bindable_subexprs(e, encoded) {
            let n = first_seen.len();
            first_seen.entry(x).or_insert(n);
            *count.entry(x).or_default() += k;
            let v = uses.entry(x).or_default();
            if !v.contains(&at) {
                v.push(at);
            }
        }
    };
    for nd in &l.nodes {
        if !g.reachable[nd.id] {
            continue;
        }
        for (i, st) in nd.stmts.iter().enumerate() {
            for e in stmt_reads(st, names) {
                note(e, (nd.id, Pos::Stmt(i)));
            }
        }
        for e in term_reads(&nd.term) {
            note(e, (nd.id, Pos::Term));
        }
    }
    let mut edge_keys: Vec<(usize, usize)> = l.edge_assigns.keys().copied().collect();
    edge_keys.sort_unstable();
    for key in edge_keys {
        if g.reachable[key.0] {
            for (_, v) in &l.edge_assigns[&key] {
                note((*v, false), (key.0, Pos::Edge));
            }
        }
    }
    let mut edge_assigned: Vec<HashSet<ExprId>> = vec![HashSet::new(); l.nodes.len()];
    for ((from, _), assigns) in &l.edge_assigns {
        edge_assigned[*from].extend(assigns.iter().map(|(v, _)| *v));
    }
    let mut stmt_assigned: Vec<Vec<(usize, ExprId)>> = vec![Vec::new(); l.nodes.len()];
    for nd in &l.nodes {
        for (i, st) in nd.stmts.iter().enumerate() {
            if let Stmt::Assign { var, .. } = st {
                stmt_assigned[nd.id].push((i, *var));
            }
        }
    }
    let order = |at: &(usize, Pos)| (g.rpo_index[at.0], at.1);
    let mut plan: Vec<(usize, Pos, ExprId)> = Vec::new();
    for (e, mut at) in uses {
        if count[&e] < 2 {
            continue;
        }
        at.sort_by_key(order);
        let dominated_by = |f: usize, pos: Pos, (u, p): &(usize, Pos)| {
            (*u != f && g.dominates(f, *u)) || (*u == f && *p > pos)
        };
        let (f, pos) = at[0];
        let (f, pos) = if at[1..].iter().all(|u| dominated_by(f, pos, u)) {
            (f, pos)
        } else {
            let nodes: Vec<usize> = at.iter().map(|(n, _)| *n).collect();
            let d = common_dominator(&g, &nodes);
            let frontier: Vec<(usize, Pos)> = at
                .iter()
                .copied()
                .filter(|u| !at.iter().any(|v| v != u && dominated_by(v.0, v.1, u)))
                .collect();
            // A test printed above the place the code makes it would fail where the code does not.
            if d == f || names.tests(e) || !available_at(l, &g, names, d, &frontier, e) {
                continue;
            }
            (d, Pos::Term)
        };
        let reads = vars_in(e);
        if !reads.is_empty() {
            let mut seen = HashSet::new();
            let mut stack: Vec<usize> = vec![f];
            let mut clobbered = false;
            while let Some(x) = stack.pop() {
                if !seen.insert(x) || seen.len() > 5000 {
                    continue;
                }
                let later_use = |p: Pos| {
                    at.iter().any(|(u, q)| {
                        (*u == x && *q > p) || (*u != x && *u != f && reaches(l, x, *u))
                    })
                };
                let by_stmt = stmt_assigned[x].iter().any(|(i, v)| {
                    reads.contains(v)
                        && (x != f || Pos::Stmt(*i) >= pos)
                        && later_use(Pos::Stmt(*i))
                });
                let by_edge =
                    edge_assigned[x].iter().any(|v| reads.contains(v)) && later_use(Pos::Edge);
                if by_stmt || by_edge {
                    clobbered = true;
                    break;
                }
                stack.extend(l.nodes[x].succs.iter().copied());
            }
            if clobbered {
                continue;
            }
        }
        plan.push((f, pos, e));
    }
    plan.sort_by_key(|(f, pos, e)| (g.rpo_index[*f], *pos, first_seen[e]));
    bind(l, &g, plan, &bindable)
}

type Bindings = Vec<(Node, ExprId)>;

fn bind(
    l: &Lifted,
    g: &Graph,
    plan: Vec<(usize, Pos, ExprId)>,
    wanted: &dyn Fn(ExprId) -> bool,
) -> (Lifted, Bindings) {
    if plan.is_empty() {
        return (l.clone(), Vec::new());
    }
    let mut out = l.clone();
    let mut next_var: u32 = 0;
    for nd in &l.nodes {
        for e in lift::node_exprs(nd) {
            let mut seen = HashSet::new();
            let mut stack = vec![e];
            while let Some(x) = stack.pop() {
                if !seen.insert(x) || seen.len() > 20_000 {
                    continue;
                }
                if let Node::Var(v) = expr::node(x) {
                    next_var = next_var.max(v + 1);
                }
                stack.extend(expr::children(x));
            }
        }
    }
    for assigns in l.edge_assigns.values() {
        for (v, _) in assigns {
            if let Node::Var(k) = expr::node(*v) {
                next_var = next_var.max(k + 1);
            }
        }
    }
    let mut inserted: Vec<Vec<usize>> = vec![Vec::new(); l.nodes.len()];
    let mut bound: Vec<(Node, ExprId, usize)> = Vec::new();
    for (f, pos, e) in plan {
        let mut e = e;
        // A name given in another branch is not known here.
        for (target, var, _) in bound.iter().filter(|(_, _, at)| g.dominates(*at, f)) {
            e = expr::substitute(
                e,
                &|n| if n == target { Some(*var) } else { None },
                &mut HashMap::new(),
            );
        }
        let known = |(t, _, at): &(Node, ExprId, usize)| *t == expr::node(e) && g.dominates(*at, f);
        if bound.iter().any(known) || !wanted(e) {
            continue;
        }
        let var = expr::intern(Node::Var(next_var));
        next_var += 1;
        let at = match pos {
            Pos::Stmt(i) => i + inserted[f].iter().filter(|k| **k <= i).count(),
            Pos::Term | Pos::Edge => out.nodes[f].stmts.len(),
        };
        if let Pos::Stmt(i) = pos {
            inserted[f].push(i);
        }
        out.nodes[f]
            .stmts
            .insert(at, Stmt::Assign { var, value: e });
        let target = expr::node(e);
        bound.push((target.clone(), var, f));
        let sub = |x: ExprId| {
            expr::substitute(
                x,
                &|n| if *n == target { Some(var) } else { None },
                &mut HashMap::new(),
            )
        };
        for u in 0..out.nodes.len() {
            if !g.reachable[u] || !g.dominates(f, u) {
                continue;
            }
            let first = if u == f { at + 1 } else { 0 };
            let node = &mut out.nodes[u];
            for st in node.stmts.iter_mut().skip(first) {
                *st = lift::map_stmt(st, &sub);
            }
            node.term = lift::map_term(&node.term, &sub);
        }
        for ((from, _), assigns) in out.edge_assigns.iter_mut() {
            if g.reachable[*from] && g.dominates(f, *from) {
                for (_, v) in assigns.iter_mut() {
                    *v = sub(*v);
                }
            }
        }
    }
    let bound = bound.into_iter().map(|(target, var, _)| (target, var));
    (out, bound.collect())
}

fn ordered(st: &Stmt, names: &Names) -> bool {
    match st {
        Stmt::Call { .. }
        | Stmt::Create { .. }
        | Stmt::SStore { .. }
        | Stmt::Log { .. }
        | Stmt::Internal { .. } => true,
        Stmt::Require { cond, data, .. } => !emit::is_hidden_require(*cond, data.as_deref(), names),
        Stmt::Assign { .. } | Stmt::MStore { .. } | Stmt::Copy { .. } | Stmt::Drop(_) => false,
    }
}

/* A test the printer leaves out is told by its operator, and an operator prints where its
value is used. When a step whose order shows lies between the test and the use, the value
gets a name where the code tests it. */
pub fn name_tested(l: &Lifted, names: &Names) -> (Lifted, Bindings) {
    let g = Graph::new(l);
    let mut uses: HashMap<ExprId, Vec<(usize, Pos)>> = HashMap::new();
    let mut first_seen: HashMap<ExprId, usize> = HashMap::new();
    let mut sites: HashMap<ExprId, Vec<emit::Site>> = HashMap::new();
    let mut note = |roots: Vec<ExprId>, at: (usize, Pos)| {
        let mut seen = HashSet::new();
        let mut stack = roots;
        while let Some(x) = stack.pop() {
            if !seen.insert(x) || seen.len() > 20_000 {
                continue;
            }
            stack.extend(expr::children(x));
            if !sites
                .entry(x)
                .or_insert_with(|| names.test_sites(x))
                .is_empty()
            {
                let n = first_seen.len();
                first_seen.entry(x).or_insert(n);
                uses.entry(x).or_default().push(at);
            }
        }
    };
    for nd in l.nodes.iter().filter(|nd| g.reachable[nd.id]) {
        for (i, st) in nd.stmts.iter().enumerate() {
            let hidden = matches!(st, Stmt::Require { cond, data, .. }
                if emit::is_hidden_require(*cond, data.as_deref(), names));
            if !hidden {
                note(lift::stmt_exprs(st), (nd.id, Pos::Stmt(i)));
            }
        }
        note(lift::term_exprs(&nd.term), (nd.id, Pos::Term));
    }
    let mut edges: Vec<&(usize, usize)> = l.edge_assigns.keys().collect();
    edges.sort_unstable();
    for edge in edges.into_iter().filter(|k| g.reachable[k.0]) {
        let read = l.edge_assigns[edge].iter().map(|(_, v)| *v);
        note(read.collect(), (edge.0, Pos::Edge));
    }
    let assigned = |x: usize, reads: &HashSet<ExprId>| {
        let by_stmt = l.nodes[x]
            .stmts
            .iter()
            .any(|s| matches!(s, Stmt::Assign { var, .. } if reads.contains(var)));
        let mut edges = l.edge_assigns.iter().filter(|((from, _), _)| *from == x);
        by_stmt || edges.any(|(_, a)| a.iter().any(|(v, _)| reads.contains(v)))
    };
    let mut plan: Vec<(usize, Pos, ExprId)> = Vec::new();
    for (e, at) in &uses {
        let mut tests = sites[e].clone();
        tests.retain(|(n, _)| g.reachable[*n]);
        tests.sort_by_key(|(n, i)| (g.rpo_index[*n], *i));
        for (n, i) in tests {
            let after = |(u, p): &&(usize, Pos)| {
                (*u != n && g.dominates(n, *u)) || (*u == n && *p > Pos::Stmt(i))
            };
            let later: Vec<&(usize, Pos)> = at.iter().filter(after).collect();
            let mut reach: HashMap<usize, Pos> = HashMap::new();
            let (mut node, mut from) = (n, i + 1);
            loop {
                let stmts = &l.nodes[node].stmts[from..];
                if let Some(k) = stmts.iter().position(|s| ordered(s, names)) {
                    reach.insert(node, Pos::Stmt(from + k));
                    break;
                }
                reach.insert(node, Pos::Edge);
                match l.nodes[node].term {
                    Term::Jump(t) if g.preds[t].len() == 1 && !reach.contains_key(&t) => {
                        (node, from) = (t, 0);
                    }
                    _ => break,
                }
            }
            let beside = |(u, p): &(usize, Pos)| reach.get(u).is_some_and(|last| p <= last);
            if later.is_empty() || later.iter().all(|u| beside(u)) {
                continue;
            }
            let reads = vars_in(*e);
            let region = (0..l.nodes.len()).filter(|u| g.reachable[*u] && g.dominates(n, *u));
            if !reads.is_empty() && region.into_iter().any(|u| assigned(u, &reads)) {
                continue;
            }
            plan.push((n, Pos::Stmt(i), *e));
        }
    }
    plan.sort_by_key(|(f, pos, e)| (g.rpo_index[*f], *pos, first_seen[e]));
    bind(l, &g, plan, &|e| matches!(expr::node(e), Node::Op(..)))
}

fn writes_memory(st: &Stmt) -> bool {
    match st {
        Stmt::MStore { .. } | Stmt::Copy { .. } | Stmt::Internal { .. } => true,
        Stmt::Call { out_len, .. } => expr::as_const(*out_len) != Some(U256::ZERO),
        _ => false,
    }
}

fn hash_mark(st: &Stmt) -> Option<ExprId> {
    match st {
        Stmt::Drop(e) if matches!(expr::node(*e), Node::KeccakMem(..)) => Some(*e),
        _ => None,
    }
}

/* A hash of memory prints as the range it was taken over, which reads as the memory of
the place it is printed at. Where memory may be written between the hash and a use of it,
the hash gets a name at the mark the lifter left where the code took it. */
pub fn name_hashes(l: &Lifted) -> (Lifted, Bindings) {
    let marked = |nd: &lift::LNode| nd.stmts.iter().any(|s| hash_mark(s).is_some());
    if !l.nodes.iter().any(marked) {
        return (l.clone(), Vec::new());
    }
    let g = Graph::new(l);
    let writes: Vec<Vec<usize>> = l
        .nodes
        .iter()
        .map(|nd| {
            let at = nd.stmts.iter().enumerate();
            at.filter(|(_, s)| writes_memory(s))
                .map(|(i, _)| i)
                .collect()
        })
        .collect();
    let holds = |e: ExprId, hash: ExprId| {
        let target = expr::node(hash);
        expr::holds(e, kind::KECCAK_MEM) && expr::contains(e, &|n| *n == target)
    };
    let uses_of = |nd: &lift::LNode, hash: ExprId| -> Vec<usize> {
        let mut at: Vec<usize> = Vec::new();
        for (i, st) in nd.stmts.iter().enumerate() {
            let used =
                hash_mark(st).is_none() && lift::stmt_exprs(st).into_iter().any(|e| holds(e, hash));
            if used {
                at.push(i);
            }
        }
        let leaving = l
            .edge_assigns
            .iter()
            .filter(|((from, _), _)| *from == nd.id);
        let mut last = lift::term_exprs(&nd.term);
        last.extend(leaving.flat_map(|(_, a)| a.iter().map(|(_, v)| *v)));
        if last.into_iter().any(|e| holds(e, hash)) {
            at.push(nd.stmts.len());
        }
        at
    };
    let mut plan: Vec<(usize, Pos, ExprId)> = Vec::new();
    for nd in l.nodes.iter().filter(|nd| g.reachable[nd.id]) {
        for (i, st) in nd.stmts.iter().enumerate() {
            let Some(hash) = hash_mark(st) else { continue };
            let written_before = |node: usize, end: usize, from: usize| {
                writes[node].iter().any(|w| *w >= from && *w < end)
            };
            let here = uses_of(nd, hash);
            let mut late = here.iter().any(|u| *u > i && written_before(nd.id, *u, i));
            if !late {
                let after = g.reached(nd.succs.iter().copied(), &[]);
                let tail = written_before(nd.id, nd.stmts.len(), i);
                for other in l.nodes.iter().filter(|o| after.contains(&o.id)) {
                    let Some(first) = uses_of(other, hash).into_iter().next() else {
                        continue;
                    };
                    let again = other.id == nd.id;
                    let head = match again {
                        true => !writes[other.id].is_empty(),
                        false => written_before(other.id, first, 0),
                    };
                    let between = || {
                        let mut before: HashSet<usize> = HashSet::new();
                        let mut pending: Vec<usize> = g.preds[other.id].clone();
                        while let Some(m) = pending.pop() {
                            if after.contains(&m) && before.insert(m) {
                                pending.extend(&g.preds[m]);
                            }
                        }
                        let ends = [nd.id, other.id];
                        let mut on_way = before.iter().filter(|m| !ends.contains(m));
                        on_way.any(|m| !writes[*m].is_empty())
                    };
                    if tail || head || between() {
                        late = true;
                        break;
                    }
                }
            }
            if late {
                plan.push((nd.id, Pos::Stmt(i), hash));
            }
        }
    }
    let wanted = |e: ExprId| matches!(expr::node(e), Node::KeccakMem(..));
    let (mut out, bindings) = bind(l, &g, plan, &wanted);
    let named: HashSet<ExprId> = bindings.iter().map(|(_, var)| *var).collect();
    for nd in out.nodes.iter_mut() {
        nd.stmts.retain(|s| match s {
            Stmt::Drop(e) => hash_mark(s).is_none() && !named.contains(e),
            _ => true,
        });
    }
    (out, bindings)
}

const DUP_LIMIT: usize = 6;

impl<'a> Printer<'a> {
    fn line(&mut self, depth: usize, s: &str) {
        if s.is_empty() {
            return;
        }
        // A name declared in a block is gone where the block ends. A label is no end.
        if !s.ends_with(':') {
            self.given.retain(|_, at| *at <= depth);
        }
        for (name, def) in self.names.take_temps() {
            for _ in 0..depth {
                self.out.push_str("    ");
            }
            self.out.push_str(&format!("uint256 {} = {};\n", name, def));
        }
        for _ in 0..depth {
            self.out.push_str("    ");
        }
        self.out.push_str(s);
        self.out.push('\n');
    }

    fn label(&self, n: usize) -> String {
        emit::label(self.l, n)
    }

    fn is_small_terminal(&self, mut n: usize) -> bool {
        let mut count = 0;
        let mut seen = HashSet::new();
        loop {
            if !seen.insert(n) || count > DUP_LIMIT {
                return false;
            }
            let nd = &self.l.nodes[n];
            count += nd.stmts.len() + 1;
            match &nd.term {
                Term::Jump(t) => n = *t,
                Term::Branch { .. } | Term::Switch { .. } => return false,
                _ => return count <= DUP_LIMIT,
            }
        }
    }

    /* A revert folded into a require loses the edges into it. The values those edges give
    its arguments are put in, or the arguments read names nothing assigned. */
    fn revert_reason(&self, from: usize, mut n: usize) -> Option<Option<String>> {
        let mut seen = HashSet::new();
        let mut stores: Vec<(ExprId, ExprId)> = Vec::new();
        let mut edges: Vec<&[(ExprId, ExprId)]> = Vec::new();
        let mut prev = from;
        loop {
            if !seen.insert(n) {
                return None;
            }
            edges.push(
                self.l
                    .edge_assigns
                    .get(&(prev, n))
                    .map_or(&[], |a| a.as_slice()),
            );
            let entering = |e: ExprId| {
                edges.iter().rev().fold(e, |e, edge| {
                    let given = |nd: &Node| {
                        let var = edge.iter().find(|(var, _)| expr::node(*var) == *nd);
                        var.map(|(_, value)| *value)
                    };
                    expr::substitute(e, &given, &mut HashMap::new())
                })
            };
            let nd = &self.l.nodes[n];
            if !nd.stmts.iter().all(|s| matches!(s, Stmt::MStore { .. })) {
                return None;
            }
            for s in &nd.stmts {
                if let Stmt::MStore {
                    off,
                    val,
                    width: 32,
                    ..
                } = s
                {
                    stores.push((entering(*off), entering(*val)));
                }
            }
            match &nd.term {
                Term::Jump(t) => (prev, n) = (n, *t),
                Term::Revert { data, len, off } => {
                    let data = data
                        .as_ref()
                        .map(|w| w.iter().map(|x| entering(*x)).collect::<Vec<_>>());
                    let off = &entering(*off);
                    return Some(match data {
                        Some(words) if !words.is_empty() => {
                            let p = emit::fmt_payload(
                                &words,
                                expr::as_const(*len),
                                self.names,
                                PayloadKind::Revert,
                            );
                            Some(p)
                        }
                        Some(_) => None,
                        None => {
                            if expr::as_const(*len) == Some(U256::ZERO) {
                                None
                            } else if let Some((words, l)) = payload_from_stores(&stores, *off) {
                                let p = emit::fmt_payload(
                                    &words,
                                    Some(U256::from_u64(l)),
                                    self.names,
                                    PayloadKind::Revert,
                                );
                                if p.starts_with('"') || p.starts_with("Panic(") || p.contains('(')
                                {
                                    Some(p)
                                } else {
                                    return None;
                                }
                            } else {
                                return None;
                            }
                        }
                    });
                }
                Term::Invalid => return Some(Some(INVALID.into())),
                Term::Infeasible => return Some(None),
                _ => return None,
            }
        }
    }

    // A temporary made for one edge is declared in that arm only. The next arm makes its own.
    fn edge_assigns(&mut self, from: usize, to: usize, depth: usize) {
        self.named_in(from, false);
        if let Some(assigns) = self.l.edge_assigns.get(&(from, to)) {
            let assigns = assigns.clone();
            let temps = self.names.temp_of.borrow().clone();
            self.assign_lines(&assigns, depth);
            *self.names.temp_of.borrow_mut() = temps;
            self.names.memo.borrow_mut().clear();
        }
    }

    fn try_transfer_idiom(&mut self, n: usize, stop: Option<usize>, depth: usize) -> bool {
        let nd = &self.l.nodes[n];
        let Term::Branch {
            cond,
            t: Some(t),
            f,
        } = &nd.term
        else {
            return false;
        };
        let Some(Stmt::Call {
            kind: op::CALL,
            addr,
            value: Some(value),
            in_len,
            gas,
            seq,
            ..
        }) = nd.stmts.last()
        else {
            return false;
        };
        if expr::as_const(*in_len) != Some(U256::ZERO) {
            return false;
        }
        let stipend = expr::as_const(*gas).is_some_and(|g| g == U256::from_u64(2300))
            || matches!(expr::node(*gas), Node::Op(op::MUL, ref v) if expr::as_const(v[1]) == Some(U256::from_u64(2300)) || expr::as_const(v[0]) == Some(U256::from_u64(2300)));
        if !stipend {
            return false;
        }
        let is_result = |e: ExprId| matches!(expr::node(e), Node::CallResult(s) if s == *seq);
        let (ok, revert) = if is_result(*cond) {
            (*t, *f)
        } else if matches!(expr::node(*cond), Node::Op(op::ISZERO, ref v) if is_result(v[0])) {
            (*f, *t)
        } else {
            return false;
        };
        if self.revert_reason(n, revert) != Some(None) {
            return false;
        }
        let (addr, value, cond) = (*addr, *value, *cond);
        let count = nd.stmts.len();
        for s in &self.l.nodes[n].stmts[..count - 1] {
            let txt = emit::fmt_stmt(s, self.names);
            self.line(depth, &txt);
        }
        self.line(
            depth,
            &format!(
                "payable({}).transfer({});",
                emit::fmt_expr(addr, self.names),
                emit::fmt_expr(value, self.names)
            ),
        );
        self.facts.push((cond, ok == *t, ok));
        self.transfer(n, ok, stop, depth);
        self.facts.pop();
        true
    }

    fn array_resize(
        &self,
        node: usize,
        index: usize,
        slot: ExprId,
        new_len: ExprId,
    ) -> Option<String> {
        let c = expr::as_const(slot)?;
        let name = self
            .names
            .storage
            .get(&c)
            .cloned()
            .unwrap_or_else(|| format!("stor_{}", c.to_decimal()));
        let reads_len = |e: ExprId| matches!(expr::node(e), Node::SLoad(k, false, _) if k == slot);
        let delta = match expr::node(new_len) {
            Node::Op(op::ADD, v) if reads_len(v[0]) && expr::as_const(v[1]) == Some(U256::ONE) => 1,
            Node::Op(op::ADD, v) if reads_len(v[1]) && expr::as_const(v[0]) == Some(U256::ONE) => 1,
            Node::Op(op::SUB, v) if reads_len(v[0]) && expr::as_const(v[1]) == Some(U256::ONE) => {
                -1
            }
            _ => 0,
        };
        if delta == 1 {
            let next = if index + 1 < self.l.nodes[node].stmts.len() {
                Some((node, index + 1))
            } else {
                match self.l.nodes[node].term {
                    Term::Jump(t) if !self.l.nodes[t].stmts.is_empty() => Some((t, 0)),
                    _ => None,
                }
            };
            if let Some((nn, ni)) = next {
                if let Stmt::SStore { key, val, .. } = &self.l.nodes[nn].stmts[ni] {
                    let data_start = |a: ExprId| match expr::node(a) {
                        Node::Keccak(w, 0) => w.len() == 1 && w[0] == slot,
                        Node::Const(h) => emit::hashed_slot(h) == Some((c, 0)),
                        _ => false,
                    };
                    let at_old_len = match expr::node(*key) {
                        Node::Op(op::ADD, v) => {
                            v.iter().any(|a| reads_len(*a)) && v.iter().any(|a| data_start(*a))
                        }
                        _ => false,
                    };
                    if at_old_len {
                        let value = emit::element_write(*key, *val, self.names)
                            .map(|(_, v)| v)
                            .unwrap_or(*val);
                        self.skipped.borrow_mut().insert((nn, ni));
                        return Some(format!(
                            "{}.push({});",
                            name,
                            emit::fmt_expr(value, self.names)
                        ));
                    }
                }
            }
            return Some(format!("{}.length++;", name));
        }
        if delta == -1 {
            return Some(format!("{}.pop();", name));
        }
        Some(format!(
            "{}.length = {};",
            name,
            emit::fmt_expr(new_len, self.names)
        ))
    }

    fn refresh_forwarded(&self, n: usize) {
        let mut fw = self.names.forwarded.borrow_mut();
        let mut places = self.names.forward_places.borrow_mut();
        fw.clear();
        places.clear();
        for (node, at, name, val, key) in &self.stored {
            if *node != n && self.g.dominates(*node, n) && self.storage_kept(*node, *at, n) {
                fw.insert(*val, name.clone());
                places.insert(*val, *key);
            }
        }
    }

    // A call can call back in and a helper can write any slot. A value stored before one
    // of them is no longer what the slot holds after it.
    fn storage_kept(&self, node: usize, at: usize, n: usize) -> bool {
        let stmts = &self.l.nodes[node].stmts;
        !stmts[at + 1..].iter().any(may_change_storage)
            && unchanged_between(self.l, &self.g, node, n)
    }

    fn forget_stored(&self) {
        self.names.forwarded.borrow_mut().retain(|v, nm| {
            !self
                .stored
                .iter()
                .any(|(_, _, name, val, _)| val == v && name == nm)
        });
    }

    fn named_in(&self, n: usize, entering: bool) {
        let left = self.left.get(&n).filter(|_| !entering).cloned();
        let named = left.unwrap_or_else(|| {
            let named = self.scope.get(&n).cloned().unwrap_or_default();
            let given = named
                .into_iter()
                .filter(|name| self.given.contains_key(name));
            given.rev().collect()
        });
        if *self.names.stale.borrow() != named {
            self.names.memo.borrow_mut().clear();
            self.names.stale.replace(named);
        }
    }

    fn early(&mut self, at: (usize, usize), depth: usize) {
        let named = self.early_reads.get(&at).cloned().unwrap_or_default();
        for (i, (read, name)) in named.iter().enumerate() {
            if self.names.stale.borrow().contains_key(read) {
                continue;
            }
            // A slot whose value was just put in memory would print as that memory word.
            let stored_on = self.names.forwarded.borrow().contains_key(read);
            let current = match (emit::field_name(*read, self.names), expr::node(*read)) {
                (None, Node::SLoad(key, transient, _)) => {
                    emit::fmt_slot(key, self.names, emit::SlotSpace::from_transient(transient))
                }
                // Stored on to another word, the read would print as that word.
                (None, Node::MLoad(at, _)) if stored_on => emit::fmt_mem_word(at, self.names),
                _ => emit::fmt_expr(*read, self.names),
            };
            if !named[..i].iter().any(|(_, earlier)| earlier == name) {
                self.line(depth, &format!("uint256 {name} = {current};"));
            }
            self.given.insert((*read, name.clone()), depth);
            self.names.replace_stale([(*read, name.clone())]);
        }
    }

    fn stmts(&mut self, n: usize, depth: usize) {
        // A name given in a block holds on in the block its run goes on in.
        let run = self.printed_last.filter(|p| run_on(self.l, *p) == Some(n));
        let held: Vec<(ExprId, String)> = match run {
            Some(_) => {
                let stale = self.names.stale.borrow();
                let given = self.names.block_stale.borrow();
                let named = given
                    .iter()
                    .filter_map(|e| Some((*e, stale.get(e)?.clone())));
                named.collect()
            }
            None => Vec::new(),
        };
        self.printed_last = Some(n);
        self.names.end_block();
        self.named_in(n, true);
        self.names.replace_stale_in_block(held);
        self.refresh_forwarded(n);
        let put_back = emit::on_node(&self.put_back, n);
        let mut dead = emit::dead_memory_stores(&self.l.nodes[n].stmts, &put_back);
        dead.extend(
            self.dead_stores
                .iter()
                .filter(|(node, _)| *node == n)
                .map(|(_, i)| *i),
        );
        let folded = encoded_bytes_logs(&self.l.nodes[n].stmts);
        for f in &folded {
            dead.extend(f.hidden.iter().copied());
        }
        dead.extend(emit::free_pointer_updates(
            &self.l.nodes[n].stmts,
            self.names,
        ));
        self.names.payload_overrides.borrow_mut().clear();
        dead.extend(forwarded_calldata(
            &self.l.nodes[n].stmts,
            &dead,
            self.names,
        ));
        let hidden: HashSet<usize> = dead
            .iter()
            .copied()
            .chain(
                self.skipped
                    .borrow()
                    .iter()
                    .filter(|(node, _)| *node == n)
                    .map(|(_, i)| *i),
            )
            .collect();
        let literals = emit::block_literals(&self.l.nodes[n].stmts, &hidden, self.names);
        for lit in &literals {
            dead.extend(lit.rest.iter().copied());
        }
        let mut replaced: Vec<(ExprId, String)> = Vec::new();
        let mut kept_early: HashSet<usize> = HashSet::new();
        for (i, s) in self.l.nodes[n].stmts.iter().enumerate() {
            self.names.replace_stale_in_block(replaced.drain(..));
            if i > 0 && may_change_storage(&self.l.nodes[n].stmts[i - 1]) {
                self.forget_stored();
            }
            /* Stores gathered into one line are all stated where the first stands. What
            a later one of them overwrites has to be kept before that line, not after. */
            let gathered = literals.iter().find(|lit| lit.first == i);
            let stores = std::iter::once(i).chain(gathered.iter().flat_map(|lit| lit.rest.clone()));
            for j in stores
                .filter(|j| !kept_early.contains(j))
                .collect::<Vec<_>>()
            {
                let planned = self.stale_plan.get(&(n, j)).cloned();
                let (Stmt::MStore { off, .. }, Some(stale)) = (&self.l.nodes[n].stmts[j], planned)
                else {
                    continue;
                };
                for (at, (read, name)) in stale.iter().enumerate() {
                    if stale[..at].iter().any(|(_, earlier)| earlier == name) {
                        continue;
                    }
                    let word = memory_word(*read).unwrap_or(*off);
                    let current = emit::fmt_mem_word(word, self.names);
                    self.line(depth, &format!("uint256 {name} = {current};"));
                }
                self.given
                    .extend(stale.iter().cloned().map(|name| (name, depth)));
                replaced.extend(stale);
                if j != i {
                    kept_early.insert(j);
                }
            }
            if dead.contains(&i) || self.skipped.borrow().contains(&(n, i)) {
                continue;
            }
            if let Some(lit) = literals.iter().find(|lit| lit.first == i) {
                self.line(depth, &lit.text);
                continue;
            }
            if let (Some(f), Stmt::Log { topics, .. }) = (folded.iter().find(|f| f.index == i), s) {
                let txt = emit::fmt_log_parts(topics, vec![f.text.clone()], self.names);
                self.line(depth, &txt);
                continue;
            }
            let rewrites_memory = matches!(s, Stmt::MStore { .. });
            if let Some(stale) = self.stale_plan.get(&(n, i)).filter(|_| !rewrites_memory) {
                let loads = stale.clone();
                let written = overwrites(s, self.names).map(|w| w.0);
                for (at, (read, tmp)) in loads.iter().enumerate() {
                    if loads[..at].iter().any(|(_, earlier)| earlier == tmp) {
                        continue;
                    }
                    let what = memory_word(*read).map(Overwritten::Memory).or(written);
                    let what = what.expect("stale plan entries overwrite something");
                    let current = match (emit::field_name(*read, self.names), what) {
                        (Some(field), _) => field,
                        (None, Overwritten::Slot(key, transient)) => {
                            let space = emit::SlotSpace::from_transient(transient);
                            emit::fmt_slot(key, self.names, space)
                        }
                        (None, Overwritten::Balance) => "address(this).balance".to_string(),
                        (None, Overwritten::Memory(addr)) => emit::fmt_mem_word(addr, self.names),
                    };
                    self.line(depth, &format!("uint256 {tmp} = {current};"));
                }
                self.given
                    .extend(loads.iter().cloned().map(|name| (name, depth)));
                self.names.replace_stale(loads);
            }
            self.early((n, i), depth);
            if let Stmt::Internal { results, .. } = s {
                if !results.is_empty() && results.iter().all(|r| self.names.aliases.contains_key(r))
                {
                    continue;
                }
            }
            if let Stmt::Internal { callee, args, .. } = s {
                if self.names.array_resizers.contains(callee) && args.len() == 2 {
                    if let Some(txt) = self.array_resize(n, i, args[0], args[1]) {
                        self.line(depth, &txt);
                        continue;
                    }
                }
            }
            if let Stmt::Drop(e) = s {
                let target = expr::node(*e);
                if matches!(target, Node::Env(op::GAS, _)) {
                    let txt = emit::fmt_stmt(s, self.names);
                    if !txt.is_empty() {
                        self.line(depth, &txt);
                    }
                    continue;
                }
                if self
                    .used
                    .iter()
                    .any(|u| expr::contains(*u, &|nd| *nd == target))
                {
                    continue;
                }
            }
            let txt = emit::fmt_stmt(s, self.names);
            self.line(depth, &txt);
            if let Some(out) = self.call_output(n, i, s) {
                self.line(depth, &out);
            }
            if let (Stmt::MStore { off, .. }, Some(val)) =
                (s, memory_forward(&self.l.nodes[n].stmts, i))
            {
                let word = emit::fmt_mem_word(*off, self.names);
                self.names.forward(val, word, *off);
            }
            if let Stmt::SStore {
                key,
                val,
                transient: false,
                ..
            } = s
            {
                let name = emit::fmt_slot(*key, self.names, emit::SlotSpace::Persistent);
                self.stored.retain(|(_, _, nm, _, _)| *nm != name);
                let mut fw = self.names.forwarded.borrow_mut();
                fw.retain(|_, nm| *nm != name);
                if !expr::is_const(*val) && has_operations(*val, 1) {
                    self.stored.push((n, i, name.clone(), *val, *key));
                    fw.insert(*val, name);
                    self.names.forward_places.borrow_mut().insert(*val, *key);
                }
            }
        }
        self.names.replace_stale_in_block(replaced);
        if self.l.nodes[n].stmts.last().is_some_and(may_change_storage) {
            self.forget_stored();
        }
        self.early((n, self.l.nodes[n].stmts.len()), depth);
        self.left.insert(n, self.names.stale.borrow().clone());
    }

    // Edge copies are simultaneous.
    // A copy is printed once nothing still waiting reads the variable it writes.
    // The readers of each variable are counted once. Searching every value again
    // for every variable on every round was cubic in the number of copies.
    fn assign_lines(&mut self, assigns: &[(ExprId, ExprId)], depth: usize) {
        let mut rem: Vec<(ExprId, ExprId)> =
            assigns.iter().copied().filter(|(a, b)| a != b).collect();
        while !rem.is_empty() {
            let mut writers: HashMap<ExprId, Vec<usize>> = HashMap::new();
            for (i, (var, _)) in rem.iter().enumerate() {
                writers.entry(*var).or_default().push(i);
            }
            let read_by: Vec<Vec<usize>> = rem
                .iter()
                .map(|(var, rhs)| {
                    let mut read = Vec::new();
                    let mut seen = HashSet::new();
                    let mut stack = vec![*rhs];
                    while let Some(x) = stack.pop() {
                        if !seen.insert(x) || seen.len() > 20_000 {
                            continue;
                        }
                        if x != *var {
                            read.extend(writers.get(&x).into_iter().flatten().copied());
                        }
                        // A value printed as the place it was stored at reads what the
                        // place is made of.
                        if self.names.forwarded.borrow().contains_key(&x) {
                            stack.extend(self.names.forward_places.borrow().get(&x));
                        }
                        stack.extend(expr::children(x));
                    }
                    read
                })
                .collect();
            let mut readers = vec![0usize; rem.len()];
            for read in &read_by {
                for i in read {
                    readers[*i] += 1;
                }
            }
            let mut waiting = vec![true; rem.len()];
            while let Some(i) = (0..rem.len()).find(|i| waiting[*i] && readers[*i] == 0) {
                waiting[i] = false;
                for read in &read_by[i] {
                    readers[*read] -= 1;
                }
                let (var, val) = rem[i];
                let s = format!(
                    "{} = {};",
                    emit::fmt_expr(var, self.names),
                    emit::fmt_expr(val, self.names)
                );
                self.line(depth, &s);
            }
            rem = (0..rem.len())
                .filter(|i| waiting[*i])
                .map(|i| rem[i])
                .collect();
            let Some((var, _)) = rem.first().copied() else {
                break;
            };
            let tmp = expr::intern(Node::Var(self.next_tmp));
            self.next_tmp += 1;
            let s = format!(
                "{} = {};",
                emit::fmt_expr(tmp, self.names),
                emit::fmt_expr(var, self.names)
            );
            self.line(depth, &s);
            let target = expr::node(var);
            for (_, rhs) in rem.iter_mut() {
                *rhs = expr::substitute(
                    *rhs,
                    &|nd| if *nd == target { Some(tmp) } else { None },
                    &mut HashMap::new(),
                );
            }
        }
    }

    /* A call writes what it returns over its output area. Memory read there later would
    otherwise show only the stores made before the call. The read may be a load, a hash, a
    copy, a log, the data of another call or what the function hands back, and it may reach
    the area through an address the code works out. */
    fn call_output(&self, n: usize, i: usize, s: &Stmt) -> Option<String> {
        let Stmt::Call {
            addr,
            out_off,
            out_len,
            ..
        } = s
        else {
            return None;
        };
        let area = reach(*out_off, *out_len);
        let copy = expr::as_const(*addr) == Some(U256::from_u64(4));
        if copy || area.2 <= area.1 {
            return None;
        }
        let after = self.g.reached(self.g.succs[n].iter().copied(), &[]);
        let here = self.memory_reads[n].iter().filter(|(at, _)| *at > i);
        let later = after
            .iter()
            .flat_map(|node| self.memory_reads[*node].iter());
        let read = here
            .chain(later)
            .any(|(_, read)| self.may_overlap(area, *read));
        /* Memory outlives a helper, so what its caller reads is not seen here. A caller
        does not read a block the helper allocated unless it is handed the block. */
        let handed_back =
            |node: &usize| matches!(self.l.nodes[*node].term, Term::InternalReturn(_));
        let blocks = self.names.blocks.as_ref();
        let own = area.0.is_some() && blocks.is_some_and(|known| known.contains_key(&area.0));
        let kept =
            self.names.in_helper && !own && std::iter::once(&n).chain(&after).any(handed_back);
        (read || kept).then(|| emit::fmt_call_output(*out_off, *out_len, self.names))
    }

    /* Two blocks the code allocated are apart, and so is a block from a fixed place. An
    address made any other way is unsigned, so it lies at or above the number added to it. */
    fn may_overlap(&self, a: Span, b: Span) -> bool {
        if a.0 == b.0 {
            return a.1 < b.2 && b.1 < a.2;
        }
        let blocks = self.names.blocks.as_ref();
        let placed = |base: Option<ExprId>| {
            base.is_none() || blocks.is_some_and(|known| known.contains_key(&base))
        };
        match (a.0, b.0) {
            _ if placed(a.0) && placed(b.0) => false,
            (None, Some(_)) => a.2 > b.1,
            (Some(_), None) => b.2 > a.1,
            _ => true,
        }
    }

    fn transfer(&mut self, from: usize, to: usize, stop: Option<usize>, depth: usize) {
        self.edge_assigns(from, to, depth);
        self.go(to, stop, depth);
    }

    fn go(&mut self, n: usize, stop: Option<usize>, depth: usize) {
        let Some(n) = self.next(n, stop, depth) else {
            return;
        };
        // Each nested region calls back into the printer. Past this depth the rest is
        // printed at the top level under a label, so a long chain cannot use up the stack.
        if self.nesting >= MAX_NESTING {
            self.labels.insert(n);
            self.line(depth, &format!("goto {};", self.label(n)));
            return;
        }
        self.nesting += 1;
        self.emit_node(n, stop, depth);
        self.nesting -= 1;
    }

    fn next(&mut self, n: usize, stop: Option<usize>, depth: usize) -> Option<usize> {
        if Some(n) == stop {
            return None;
        }
        for i in (0..self.loop_stack.len()).rev() {
            let (header, exit, body_depth) = self.loop_stack[i];
            let innermost = i == self.loop_stack.len() - 1;
            if n == header {
                if innermost {
                    if depth != body_depth {
                        self.line(depth, "continue;");
                    }
                } else {
                    self.labels.insert(n);
                    self.line(
                        depth,
                        &format!("goto {}; // continue outer loop", self.label(n)),
                    );
                }
                return None;
            }
            if exit == Some(n) {
                if innermost {
                    self.line(depth, "break;");
                } else {
                    self.labels.insert(n);
                    self.line(
                        depth,
                        &format!("goto {}; // break outer loop", self.label(n)),
                    );
                }
                return None;
            }
        }
        if self.emitted.contains(&n) || self.active.contains(&n) {
            if self.is_small_terminal(n) && !self.active.contains(&n) {
                self.emit_dup(n, depth);
                return None;
            }
            self.labels.insert(n);
            self.line(depth, &format!("goto {};", self.label(n)));
            return None;
        }
        Some(n)
    }

    fn emit_dup(&mut self, mut n: usize, depth: usize) {
        loop {
            self.stmts(n, depth);
            let nd = &self.l.nodes[n];
            match &nd.term {
                Term::Jump(t) => {
                    let t = *t;
                    self.edge_assigns(n, t, depth);
                    n = t;
                }
                other => {
                    if let Some(s) = emit::fmt_term_halt(other, self.names) {
                        self.line(depth, &s);
                    }
                    return;
                }
            }
        }
    }

    fn emit_node(&mut self, mut n: usize, stop: Option<usize>, depth: usize) {
        loop {
            crate::clock::check();
            if let Some(lp) = self.loops.get(&n) {
                if !self.emitted.contains(&n) && !self.loop_stack.iter().any(|(h, _, _)| *h == n) {
                    let body: HashSet<usize> = lp.body.clone();
                    let exits = lp.exits.clone();
                    self.emit_loop(n, &body, &exits, stop, depth);
                    return;
                }
            }
            self.emitted.insert(n);
            if self.labels.contains(&n) {
                self.line(depth.saturating_sub(1), &format!("{}:", self.label(n)));
            }
            if self.try_transfer_idiom(n, stop, depth) {
                return;
            }
            self.stmts(n, depth);
            let to = match self.l.nodes[n].term.clone() {
                Term::Jump(t) => t,
                Term::Branch { t: Some(t), f, .. } if t == f => f,
                Term::Branch { cond, t, f } => {
                    self.emit_branch(n, cond, t, f, stop, depth);
                    return;
                }
                Term::Switch { target, cases } => {
                    let tgt = emit::fmt_expr(target, self.names);
                    self.line(depth, &format!("switch ({}) {{", tgt));
                    for (i, c) in cases.iter().enumerate() {
                        self.line(depth + 1, &format!("case {}: {{", i));
                        self.transfer(n, *c, stop, depth + 2);
                        self.line(depth + 1, "}");
                    }
                    self.line(depth, "}");
                    return;
                }
                other => {
                    if let Some(s) = emit::fmt_term_halt(&other, self.names) {
                        self.line(depth, &s);
                    }
                    return;
                }
            };
            self.edge_assigns(n, to, depth);
            match self.next(to, stop, depth) {
                Some(following) => n = following,
                None => return,
            }
        }
    }

    fn emit_loop(
        &mut self,
        header: usize,
        body: &HashSet<usize>,
        exits: &[usize],
        stop: Option<usize>,
        depth: usize,
    ) {
        self.emitted.insert(header);
        if self.labels.contains(&header) {
            self.line(depth.saturating_sub(1), &format!("{}:", self.label(header)));
        }
        /* A way out that only reverts is a test inside the loop. Taken as the exit, the
        code after the loop was printed inside it and reached by a jump into it. */
        let ends = |e: &&usize| self.revert_reason(header, **e).is_none();
        let kept: Vec<usize> = exits.iter().filter(ends).copied().collect();
        let exits = match kept.is_empty() {
            true => exits,
            false => &kept[..],
        };
        let after = |x: usize, e: usize| {
            let up = std::iter::successors(Some(x), |n| self.g.ipdom[*n]);
            up.take(self.l.nodes.len()).any(|n| n == e)
        };
        // Ways out that all lead on to one of them leave the loop there.
        let joined = |e: &&usize| exits.iter().all(|x| after(*x, **e));
        let exit = match exits.len() {
            0 => None,
            1 => Some(exits[0]),
            _ => {
                let pd = self.g.ipdom[header];
                match pd {
                    Some(p) if exits.contains(&p) => Some(p),
                    _ => exits.iter().find(joined).or(exits.first()).copied(),
                }
            }
        };
        let nd = &self.l.nodes[header];
        let mut while_cond: Option<(String, usize)> = None;
        let mut exit = exit;
        let mut cond_node = header;
        if nd.stmts.is_empty() {
            if let Term::Jump(j) = &nd.term {
                let jn = &self.l.nodes[*j];
                if body.contains(j)
                    && jn.stmts.is_empty()
                    && jn.preds.len() == 1
                    && !self.l.edge_assigns.contains_key(&(header, *j))
                    && matches!(jn.term, Term::Branch { .. })
                {
                    cond_node = *j;
                }
            }
        }
        let cn = &self.l.nodes[cond_node];
        self.named_in(cond_node, false);
        /* A name given a value on the way to the test needs a line there. A loop that is
        printed with its test at the top has none. */
        let named = [header, cond_node].map(|n| self.early_reads.contains_key(&(n, 0)));
        if cn.stmts.is_empty() && named == [false, false] {
            if let Term::Branch {
                cond,
                t: Some(t),
                f,
            } = &cn.term
            {
                {
                    let test =
                        |e: ExprId| self.names.without_temps(|| emit::fmt_expr(e, self.names));
                    let ends = |e: &usize| self.revert_reason(cond_node, *e).is_none();
                    if body.contains(t) && !body.contains(f) && ends(f) {
                        while_cond = test(*cond).map(|text| (text, *t));
                    } else if body.contains(f) && !body.contains(t) && ends(t) {
                        while_cond = test(expr::op1(op::ISZERO, *cond)).map(|text| (text, *f));
                    }
                    if let Some((_, into)) = &while_cond {
                        exit = Some(if into == t { *f } else { *t });
                    }
                }
            }
        }
        if while_cond.is_some() && cond_node != header {
            self.emitted.insert(cond_node);
        }
        // The loop is left from the node that holds its test, which is not always the header.
        let left_from = match while_cond.is_some() {
            true => cond_node,
            false => header,
        };
        self.loop_stack.push((header, exit, depth + 1));
        match while_cond {
            Some((c, first)) => {
                self.line(depth, &format!("while ({}) {{", c));
                self.active.insert(header);
                self.edge_assigns(cond_node, first, depth + 1);
                self.go(first, None, depth + 1);
                self.active.remove(&header);
                self.line(depth, "}");
            }
            None => {
                self.line(depth, "while (true) {");
                self.active.insert(header);
                self.stmts(header, depth + 1);
                let term = self.l.nodes[header].term.clone();
                match term {
                    Term::Jump(t) => self.transfer(header, t, None, depth + 1),
                    Term::Branch { cond, t, f } => {
                        self.emit_branch(header, cond, t, f, None, depth + 1)
                    }
                    other => {
                        if let Some(s) = emit::fmt_term_halt(&other, self.names) {
                            self.line(depth + 1, &s);
                        }
                    }
                }
                self.active.remove(&header);
                self.line(depth, "}");
            }
        }
        self.loop_stack.pop();
        if let Some(e) = exit {
            if let Some(a) = self.l.edge_assigns.get(&(left_from, e)) {
                if while_cond_exit_from_header(&self.l.nodes[left_from].term, e) {
                    let a = a.clone();
                    self.assign_lines(&a, depth);
                }
            }
            self.go(e, stop, depth);
        }
    }

    fn known(&self, cond: ExprId, at: usize) -> Option<bool> {
        let ncond = expr::op1(op::ISZERO, cond);
        /* A branch settles its test only for what can be reached through that side alone.
        A block printed inside the side and also jumped to from elsewhere is not that. */
        let holds = |side: usize| self.g.preds[side].len() == 1 && self.g.dominates(side, at);
        for (c, v, _) in self.facts.iter().rev().filter(|(_, _, side)| holds(*side)) {
            if *c == cond {
                return Some(*v);
            }
            if *c == ncond {
                return Some(!*v);
            }
        }
        None
    }

    fn emit_branch(
        &mut self,
        n: usize,
        cond: ExprId,
        t: Option<usize>,
        f: usize,
        stop: Option<usize>,
        depth: usize,
    ) {
        if let Some(v) = self.known(cond, n) {
            match (v, t) {
                (true, Some(t)) => {
                    self.transfer(n, t, stop, depth);
                    return;
                }
                (false, _) => {
                    self.transfer(n, f, stop, depth);
                    return;
                }
                _ => {}
            }
        }
        let t_rev = t.map_or(Some(None), |t| self.revert_reason(n, t));
        let f_rev = self.revert_reason(n, f);
        let join = self.g.ipdom[n];
        if let Some(reason) = f_rev.clone() {
            if let (Some(t), None) = (t, &t_rev) {
                let text = emit::fmt_cond(cond, self.names);
                self.line(depth, &guard(&text, &reason, self.names.hide_checked));
                self.facts.push((cond, true, t));
                self.transfer(n, t, stop, depth);
                self.facts.pop();
                return;
            }
        }
        if let Some(reason) = t_rev.clone() {
            if f_rev.is_none() {
                let ncond = expr::op1(op::ISZERO, cond);
                let text = emit::fmt_cond(ncond, self.names);
                self.line(depth, &guard(&text, &reason, self.names.hide_checked));
                self.facts.push((cond, false, f));
                self.transfer(n, f, stop, depth);
                self.facts.pop();
                return;
            }
        }
        let Some(t) = t else {
            self.line(
                depth,
                &format!("if ({}) {{ revert(); }}", emit::fmt_truth(cond, self.names)),
            );
            self.transfer(n, f, stop, depth);
            return;
        };
        if let Some(txt) = self.try_bool_return(cond, t, f) {
            self.line(depth, &txt);
            return;
        }
        if self.same_side(t, f) {
            self.transfer(n, t, stop, depth);
            return;
        }
        if let Some(j) = join {
            if let Some(txt) = self.try_ternary(n, cond, t, f, j) {
                self.line(depth, &txt);
                self.go(j, stop, depth);
                return;
            }
        }
        let join = match join {
            Some(j) if j != n => Some(j),
            _ => stop,
        };
        let t_terminal = self.region_is_terminal(t, join);
        let f_terminal = self.region_is_terminal(f, join);
        let (first_cond, first, second, first_terminal) = if t_terminal && !f_terminal {
            (cond, t, f, true)
        } else if f_terminal && !t_terminal {
            (expr::op1(op::ISZERO, cond), f, t, true)
        } else {
            if Some(f) == join {
                (cond, t, f, false)
            } else if Some(t) == join {
                (expr::op1(op::ISZERO, cond), f, t, false)
            } else {
                (cond, t, f, false)
            }
        };
        let first_is_true_side = first == t && first_cond == cond;
        self.line(
            depth,
            &format!("if ({}) {{", emit::fmt_truth(first_cond, self.names)),
        );
        self.active.insert(n);
        self.facts.push((cond, first_is_true_side, first));
        self.transfer(n, first, join, depth + 1);
        self.facts.pop();
        if first_terminal {
            self.line(depth, "}");
            self.facts.push((cond, !first_is_true_side, second));
            self.transfer(n, second, stop, depth);
            self.facts.pop();
        } else if Some(second) == join {
            if self.l.edge_assigns.contains_key(&(n, second)) {
                self.line(depth, "} else {");
                self.edge_assigns(n, second, depth + 1);
            }
            self.line(depth, "}");
            self.go(second, stop, depth);
        } else {
            self.line(depth, "} else {");
            self.facts.push((cond, !first_is_true_side, second));
            self.transfer(n, second, join, depth + 1);
            self.facts.pop();
            self.line(depth, "}");
            if let Some(j) = join {
                if Some(j) != stop {
                    self.go(j, stop, depth);
                }
            }
        }
        self.active.remove(&n);
    }

    fn visible_stmts(&self, n: usize) -> Vec<&Stmt> {
        let put_back = emit::on_node(&self.put_back, n);
        let dead = emit::dead_memory_stores(&self.l.nodes[n].stmts, &put_back);
        self.l.nodes[n]
            .stmts
            .iter()
            .enumerate()
            .filter(|(i, s)| {
                !dead.contains(i)
                    && !self.dead_stores.contains(&(n, *i))
                    && !matches!(s, Stmt::Drop(_))
                    && !matches!(s, Stmt::Require { cond, data, .. } if emit::is_hidden_require(*cond, data.as_deref(), self.names))
            })
            .map(|(_, s)| s)
            .collect()
    }

    fn skip_empty(&self, mut n: usize) -> usize {
        for _ in 0..8 {
            let has_edges = self
                .l
                .edge_assigns
                .iter()
                .any(|((from, _), a)| *from == n && !a.is_empty());
            match self.l.nodes[n].term {
                Term::Jump(t) if self.visible_stmts(n).is_empty() && !has_edges => n = t,
                _ => break,
            }
        }
        n
    }

    fn same_side(&self, a: usize, b: usize) -> bool {
        self.same_side_depth(a, b, 3)
    }

    fn same_side_depth(&self, a: usize, b: usize, depth: usize) -> bool {
        let (a, b) = (self.skip_empty(a), self.skip_empty(b));
        if a == b {
            return true;
        }
        if depth == 0 {
            return false;
        }
        let (na, nb) = (&self.l.nodes[a], &self.l.nodes[b]);
        let same_term = match (&na.term, &nb.term) {
            (Term::Jump(x), Term::Jump(y)) => x == y || self.same_side_depth(*x, *y, depth - 1),
            (
                Term::Branch {
                    cond: c1,
                    t: t1,
                    f: f1,
                },
                Term::Branch {
                    cond: c2,
                    t: t2,
                    f: f2,
                },
            ) => {
                c1 == c2
                    && match (t1, t2) {
                        (Some(x), Some(y)) => x == y || self.same_side_depth(*x, *y, depth - 1),
                        (None, None) => true,
                        _ => false,
                    }
                    && (f1 == f2 || self.same_side_depth(*f1, *f2, depth - 1))
            }
            (x, y) if na.succs.is_empty() && nb.succs.is_empty() => {
                format!("{x:?}") == format!("{y:?}")
            }
            _ => false,
        };
        if !same_term {
            return false;
        }
        let (sa, sb) = (self.visible_stmts(a), self.visible_stmts(b));
        if sa.len() != sb.len()
            || sa
                .iter()
                .zip(&sb)
                .any(|(x, y)| format!("{x:?}") != format!("{y:?}"))
        {
            return false;
        }
        let edges = |x: usize| -> Vec<(ExprId, ExprId)> {
            let mut v: Vec<(ExprId, ExprId)> = self
                .l
                .edge_assigns
                .iter()
                .filter(|((from, _), _)| *from == x)
                .flat_map(|(_, a)| a.iter().copied())
                .collect();
            v.sort();
            v
        };
        edges(a) == edges(b)
    }

    fn try_bool_return(&self, cond: ExprId, t: usize, f: usize) -> Option<String> {
        if self.names.bool_returns.as_slice() != [true] {
            return None;
        }
        let as_flag = |e: ExprId| match expr::as_const(e) {
            Some(c) if c.is_zero() => Some(false),
            Some(c) if c == U256::ONE => Some(true),
            _ => None,
        };
        fn flag(
            p: &Printer,
            n: usize,
            depth: usize,
            as_flag: &dyn Fn(ExprId) -> Option<bool>,
        ) -> Option<bool> {
            if depth == 0 || !p.visible_stmts(n).is_empty() {
                return None;
            }
            match &p.l.nodes[n].term {
                Term::InternalReturn(v) if v.len() == 1 => as_flag(v[0]),
                Term::Jump(x) => {
                    let handed = match &p.l.nodes[*x].term {
                        Term::InternalReturn(v) if v.len() == 1 => {
                            p.l.edge_assigns
                                .get(&(n, *x))
                                .and_then(|a| a.iter().find(|(var, _)| *var == v[0]))
                                .and_then(|(_, val)| as_flag(*val))
                        }
                        _ => None,
                    };
                    handed.or_else(|| flag(p, *x, depth - 1, as_flag))
                }
                _ => None,
            }
        }
        let flag = |n: usize| flag(self, n, 3, &as_flag);
        match (flag(t)?, flag(f)?) {
            (true, false) => Some(format!("return ({});", emit::fmt_cond(cond, self.names))),
            (false, true) => Some(format!(
                "return ({});",
                emit::fmt_cond(expr::op1(op::ISZERO, cond), self.names)
            )),
            _ => None,
        }
    }

    fn side_assigns(&self, n: usize, side: usize, join: usize) -> Option<Vec<(ExprId, ExprId)>> {
        if side == join {
            return Some(
                self.l
                    .edge_assigns
                    .get(&(n, side))
                    .cloned()
                    .unwrap_or_default(),
            );
        }
        let nd = &self.l.nodes[side];
        if !nd.stmts.is_empty() || nd.preds.len() != 1 || self.emitted.contains(&side) {
            return None;
        }
        match nd.term {
            Term::Jump(t) if t == join => {
                let mut v = self
                    .l
                    .edge_assigns
                    .get(&(n, side))
                    .cloned()
                    .unwrap_or_default();
                v.extend(
                    self.l
                        .edge_assigns
                        .get(&(side, join))
                        .cloned()
                        .unwrap_or_default(),
                );
                Some(v)
            }
            _ => None,
        }
    }

    fn try_ternary(
        &mut self,
        n: usize,
        cond: ExprId,
        t: usize,
        f: usize,
        join: usize,
    ) -> Option<String> {
        let ta = self.side_assigns(n, t, join)?;
        let fa = self.side_assigns(n, f, join)?;
        if ta.len() != 1 || fa.len() != 1 || ta[0].0 != fa[0].0 {
            return None;
        }
        let var = ta[0].0;
        let (x, y) = (ta[0].1, fa[0].1);
        if t != join {
            self.emitted.insert(t);
        }
        if f != join {
            self.emitted.insert(f);
        }
        let ncond = expr::op1(op::ISZERO, cond);
        let var_s = emit::fmt_expr(var, self.names);
        let both = |a: ExprId, b: ExprId| {
            let (a, b) = (
                emit::fmt_and_operand(a, self.names),
                emit::fmt_and_operand(b, self.names),
            );
            format!("{var_s} = {a} && {b};")
        };
        let either = |a: ExprId, b: ExprId| {
            let (a, b) = (
                emit::fmt_or_operand(a, self.names),
                emit::fmt_or_operand(b, self.names),
            );
            format!("{var_s} = {a} || {b};")
        };
        let c_s = emit::fmt_or_operand(cond, self.names);
        let txt = if y == cond {
            both(cond, x)
        } else if x == cond {
            either(cond, y)
        } else if x == ncond {
            both(ncond, y)
        } else if y == ncond {
            either(ncond, x)
        } else {
            format!(
                "{} = {} ? {} : {};",
                var_s,
                c_s,
                emit::fmt_expr(x, self.names),
                emit::fmt_expr(y, self.names)
            )
        };
        if expr::is_boolean(x) && expr::is_boolean(y) {
            expr::mark_boolean(var);
        }
        Some(txt)
    }

    fn region_is_terminal(&self, start: usize, join: Option<usize>) -> bool {
        let mut seen = HashSet::new();
        let mut stack = vec![start];
        let mut size = 0;
        while let Some(x) = stack.pop() {
            if Some(x) == join {
                return false;
            }
            if join.is_none() && (self.emitted.contains(&x) || self.active.contains(&x)) {
                return false;
            }
            if !seen.insert(x) {
                continue;
            }
            size += 1;
            if size > 64 {
                return false;
            }
            if self
                .loop_stack
                .iter()
                .any(|(h, e, _)| *h == x || *e == Some(x))
            {
                continue;
            }
            for &s in &self.g.succs[x] {
                stack.push(s);
            }
        }
        true
    }
}

fn while_cond_exit_from_header(term: &Term, exit: usize) -> bool {
    matches!(term, Term::Branch { t, f, .. } if *t == Some(exit) || *f == exit)
}

// Stands for the invalid opcode. It carries no data, so it is no reason to print.
const INVALID: &str = "INVALID";

// Where a failed assert reverts with a Panic, the opcode is named to tell the two apart.
fn guard(cond: &str, reason: &Option<String>, panics: bool) -> String {
    match reason.as_deref() {
        Some(INVALID) if panics => format!("assert({cond}); // INVALID"),
        Some(INVALID) => format!("assert({cond});"),
        Some(r) => format!("require({cond}, {r});"),
        None => format!("require({cond});"),
    }
}

const MAX_NESTING: usize = 400;

pub fn structure(l: &Lifted, names: &Names, base_depth: usize) -> String {
    emit::name_gas_reads(l, names);
    let g = Graph::new(l);
    let loops = find_loops(&g);
    let mut used: Vec<ExprId> = Vec::new();
    for nd in &l.nodes {
        let mut probe = nd.clone();
        probe.stmts.retain(|s| !matches!(s, Stmt::Drop(_)));
        used.extend(lift::node_exprs(&probe));
    }
    used.extend(l.edge_assigns.values().flatten().map(|(_, v)| *v));
    let mut kept = Kept::default();
    let mut stale_plan = plan_stale_loads(l, &g, names, &mut kept);
    plan_early_reads(l, names, &mut kept);
    let mut early_reads = StalePlan::new();
    let scope = settle(l, &g, names, kept, &mut stale_plan, &mut early_reads);
    let mut p = Printer {
        l,
        g,
        loops,
        names,
        out: String::new(),
        emitted: HashSet::new(),
        labels: HashSet::new(),
        nesting: 0,
        loop_stack: Vec::new(),
        active: HashSet::new(),
        next_tmp: 1 << 30,
        used,
        facts: Vec::new(),
        stale_plan,
        early_reads,
        scope,
        left: HashMap::new(),
        given: HashMap::new(),
        stored: Vec::new(),
        dead_stores: stores_dead_until_exit(l)
            .into_iter()
            .chain(unread_fixed_stores(l, names))
            .collect(),
        put_back: emit::stores_put_back(l),
        memory_reads: memory_reads(l),
        skipped: Default::default(),
        printed_last: None,
    };
    names.stale.borrow_mut().clear();
    p.go(l.entry, None, base_depth);
    let mut pending: Vec<usize> = p
        .labels
        .iter()
        .copied()
        .filter(|n| !p.emitted.contains(n))
        .collect();
    let mut rounds = 0;
    while !pending.is_empty() && rounds < 64 + l.nodes.len() / MAX_NESTING {
        rounds += 1;
        pending.sort_by_key(|n| p.g.rpo_index[*n]);
        for n in pending {
            if !p.emitted.contains(&n) {
                p.emit_node(n, None, base_depth);
            }
        }
        pending = p
            .labels
            .iter()
            .copied()
            .filter(|n| !p.emitted.contains(n))
            .collect();
    }
    let text = if p.labels.iter().any(|n| p.emitted.contains(n)) {
        let g2 = Graph::new(l);
        let loops2 = find_loops(&g2);
        let mut p2 = Printer {
            l,
            g: g2,
            loops: loops2,
            names,
            out: String::new(),
            next_tmp: p.next_tmp,
            used: p.used.clone(),
            emitted: HashSet::new(),
            labels: p.labels.clone(),
            nesting: 0,
            loop_stack: Vec::new(),
            active: HashSet::new(),
            facts: Vec::new(),
            stale_plan: std::mem::take(&mut p.stale_plan),
            early_reads: std::mem::take(&mut p.early_reads),
            scope: std::mem::take(&mut p.scope),
            left: HashMap::new(),
            given: HashMap::new(),
            stored: Vec::new(),
            dead_stores: std::mem::take(&mut p.dead_stores),
            put_back: std::mem::take(&mut p.put_back),
            memory_reads: std::mem::take(&mut p.memory_reads),
            skipped: Default::default(),
            printed_last: None,
        };
        names.stale.borrow_mut().clear();
        p2.go(l.entry, None, base_depth);
        let mut pending: Vec<usize> = p2
            .labels
            .iter()
            .copied()
            .filter(|n| !p2.emitted.contains(n))
            .collect();
        let mut rounds = 0;
        while !pending.is_empty() && rounds < 64 + l.nodes.len() / MAX_NESTING {
            rounds += 1;
            pending.sort_by_key(|n| p2.g.rpo_index[*n]);
            for n in pending {
                if !p2.emitted.contains(&n) {
                    p2.emit_node(n, None, base_depth);
                }
            }
            pending = p2
                .labels
                .iter()
                .copied()
                .filter(|n| !p2.emitted.contains(n))
                .collect();
        }
        p2.out
    } else {
        p.out
    };
    emit::name_labels(&drop_empty_else(&drop_unused_previous(&text)))
}

fn drop_unused_previous(text: &str) -> String {
    let declared = |line: &str| -> Option<String> {
        let rest = line.trim_start().strip_prefix("uint256 prev")?;
        let name = rest.split(" = ").next()?;
        let whole = name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
        (whole && rest.ends_with(';')).then(|| format!("prev{name}"))
    };
    let mentions = |line: &str, name: &str| {
        line.match_indices(name).any(|(at, _)| {
            let after = line[at + name.len()..].chars().next();
            let before = line[..at].chars().next_back();
            let part = |c: Option<char>| c.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_');
            !part(before) && !part(after)
        })
    };
    let lines: Vec<&str> = text.lines().collect();
    let mut kept: Vec<&str> = Vec::with_capacity(lines.len());
    for (i, line) in lines.iter().enumerate() {
        let unused = declared(line).is_some_and(|name| {
            !lines
                .iter()
                .enumerate()
                .any(|(j, other)| j != i && mentions(other, &name))
        });
        if !unused {
            kept.push(line);
        }
    }
    let mut out = kept.join("\n");
    if text.ends_with('\n') {
        out.push('\n');
    }
    out
}

// Repeated until stable. Removing an else can expose an empty if.
fn drop_empty_else(text: &str) -> String {
    let mut cur = text.to_string();
    for _ in 0..16 {
        let next = drop_empty_once(&cur);
        if next == cur {
            break;
        }
        cur = next;
    }
    cur
}

fn drop_empty_once(text: &str) -> String {
    let lines: Vec<&str> = text.lines().collect();
    let indent = |l: &str| l.len() - l.trim_start().len();
    let mut out: Vec<&str> = Vec::with_capacity(lines.len());
    let mut i = 0;
    while i < lines.len() {
        let l = lines[i];
        if l.trim() == "} else {"
            && i + 1 < lines.len()
            && lines[i + 1].trim() == "}"
            && indent(lines[i + 1]) == indent(l)
        {
            out.push(lines[i + 1]);
            i += 2;
            continue;
        }
        let t = l.trim();
        if t.starts_with("if (")
            && t.ends_with(") {")
            && i + 1 < lines.len()
            && lines[i + 1].trim() == "}"
            && indent(lines[i + 1]) == indent(l)
            && !(i + 2 < lines.len() && lines[i + 2].trim().starts_with("else"))
        {
            i += 2;
            continue;
        }
        out.push(l);
        i += 1;
    }
    let mut s = out.join("\n");
    s.push('\n');
    s
}

pub fn fmt_structured(l: &Lifted, n: &Names, indent: &str) -> String {
    expr::clear_boolean_marks();
    let depth = indent.len() / 4;
    let text = structure(l, n, depth);
    expr::clear_boolean_marks();
    text
}

fn payload_from_stores(stores: &[(ExprId, ExprId)], ptr: ExprId) -> Option<(Vec<ExprId>, u64)> {
    let (pt, pc) = crate::idiom::addends(ptr);
    let mut image: Vec<u8> = Vec::new();
    let mut any = false;
    for (off, val) in stores {
        let (t, c) = crate::idiom::addends(*off);
        if t != pt || c < pc {
            continue;
        }
        let rel = (c - pc).low_u64();
        if rel > 4096 {
            return None;
        }
        let v = expr::as_const(*val)?;
        let end = (rel + 32) as usize;
        if image.len() < end {
            image.resize(end, 0);
        }
        image[rel as usize..end].copy_from_slice(&v.to_be_bytes());
        any = true;
    }
    if !any || image.len() < 4 {
        return None;
    }
    let mut len = image.len() as u64;
    if image[..4] == [0x08, 0xc3, 0x79, 0xa0] && image.len() >= 68 {
        let n = U256::from_be_bytes(&image[36..68]);
        if n.fits_u64() {
            len = len.min(68 + n.low_u64().div_ceil(32) * 32);
        }
    }
    let mut words = Vec::new();
    let mut i = 0usize;
    while i < image.len() {
        let mut w = [0u8; 32];
        let k = (image.len() - i).min(32);
        w[32 - k..].copy_from_slice(&image[i..i + k]);
        words.push(expr::konst(U256::from_be_bytes(&w)));
        i += 32;
    }
    Some((words, len))
}

#[cfg(test)]
mod tests {
    #[test]
    fn empty_branches_are_dropped() {
        let t = "            } else {\n                if (32 > returndatasize()) {\n                }\n                log1(x);\n            }\n";
        let out = super::drop_empty_else(t);
        assert!(!out.contains("if (32"), "{}", out);
    }
}
