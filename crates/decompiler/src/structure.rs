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
    gotos: usize,
    active: HashSet<usize>,
    next_tmp: u32,
    used: Vec<ExprId>,
    facts: Vec<(ExprId, bool)>,
    stale_plan: HashMap<(usize, usize), Vec<(ExprId, String)>>,
    stored: Vec<(usize, String, ExprId)>,
    dead_stores: HashSet<(usize, usize)>,
    // Filled while the printer's &self methods run, hence the cell.
    skipped: RefCell<HashSet<(usize, usize)>>,
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
    Slot(ExprId),
    Balance,
    Memory(ExprId),
}

fn stale_loads_in(
    e: ExprId,
    what: Overwritten,
    gen: u32,
    skip: Option<ExprId>,
    out: &mut Vec<ExprId>,
) {
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if Some(x) == skip || !seen.insert(x) || seen.len() > 20_000 {
            continue;
        }
        let stale = match (expr::node(x), what) {
            (Node::SLoad(k, false, g), Overwritten::Slot(key)) => k == key && g <= gen,
            (Node::Env(op::SELFBALANCE, g), Overwritten::Balance) => g <= gen,
            (Node::MLoad(at, g), Overwritten::Memory(addr)) => at == addr && g <= gen,
            _ => false,
        };
        if stale && !out.contains(&x) {
            out.push(x);
        }
        stack.extend(expr::children(x));
    }
}

fn overwrites(st: &Stmt, names: &Names) -> Option<(Overwritten, u32)> {
    match st {
        Stmt::SStore {
            key,
            transient: false,
            gen,
            ..
        } => Some((Overwritten::Slot(*key), *gen)),
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

fn earliest_loads(l: &Lifted) -> HashMap<Overwritten, u32> {
    let mut earliest: HashMap<Overwritten, u32> = HashMap::new();
    let mut seen: HashSet<ExprId> = HashSet::new();
    let mut pending: Vec<ExprId> = l.nodes.iter().flat_map(lift::node_exprs).collect();
    pending.extend(l.edge_assigns.values().flatten().map(|(_, v)| *v));
    while let Some(e) = pending.pop() {
        if !seen.insert(e) {
            continue;
        }
        let read = match expr::node(e) {
            Node::MLoad(addr, version) => Some((Overwritten::Memory(addr), version)),
            Node::SLoad(key, false, version) => Some((Overwritten::Slot(key), version)),
            Node::Env(op::SELFBALANCE, version) => Some((Overwritten::Balance, version)),
            _ => None,
        };
        if let Some((what, version)) = read {
            let first = earliest.entry(what).or_insert(version);
            *first = (*first).min(version);
        }
        pending.extend(expr::children(e));
    }
    earliest
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
    let plain = *gen > 0 && !expr::is_const(*val) && !stmts[i + 1..].iter().any(writes_memory);
    plain.then_some(*val)
}

fn prev_name(what: Overwritten, names: &Names) -> String {
    let base = match what {
        Overwritten::Slot(key) => emit::fmt_slot(key, names, emit::SlotSpace::Persistent),
        Overwritten::Balance => "balance".to_string(),
        Overwritten::Memory(addr) => emit::fmt_mem_word(addr, names),
    };
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

// Printing these loads as the slot name would read the new value.
fn plan_stale_loads(l: &Lifted, names: &Names) -> HashMap<(usize, usize), Vec<(ExprId, String)>> {
    let mut plan: HashMap<(usize, usize), Vec<(ExprId, String)>> = HashMap::new();
    let mut counts: HashMap<String, u32> = HashMap::new();
    let mut found: Vec<(usize, usize, Overwritten, u32, Vec<ExprId>)> = Vec::new();
    let earliest = earliest_loads(l);
    for nd in &l.nodes {
        for (i, st) in nd.stmts.iter().enumerate() {
            let Some((what, gen)) = overwrites(st, names) else {
                continue;
            };
            // Only a read made before the write can be stale.
            // Without one, looking through everything after the write finds nothing.
            if earliest.get(&what).is_none_or(|first| *first > gen) {
                continue;
            }
            let mut after: Vec<ExprId> = Vec::new();
            for later in &nd.stmts[i + 1..] {
                after.extend(lift::stmt_exprs(later));
            }
            after.extend(lift::term_exprs(&nd.term));
            let in_block_only = matches!(what, Overwritten::Memory(_));
            let mut seen = HashSet::new();
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
            let forwarded = match st {
                Stmt::SStore { val, .. } if !expr::is_const(*val) => Some(*val),
                _ => None,
            };
            let skip = forwarded.or(memory_forward(&nd.stmts, i));
            let mut stale: Vec<ExprId> = Vec::new();
            for e in after {
                stale_loads_in(e, what, gen, skip, &mut stale);
            }
            if stale.is_empty() {
                continue;
            }
            found.push((nd.id, i, what, gen, stale));
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
        let mine: Vec<ExprId> = stale
            .into_iter()
            .filter(|e| per_store || first_gen.get(e) == Some(&gen))
            .collect();
        if mine.is_empty() {
            continue;
        }
        let base = prev_name(what, names);
        let n = counts.entry(base.clone()).or_insert(0);
        *n += 1;
        let tmp = if *n == 1 {
            base
        } else {
            base.replacen("prev_", &format!("prev{}_", n), 1)
        };
        plan.insert(
            (node, i),
            mine.into_iter().map(|e| (e, tmp.clone())).collect(),
        );
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

fn reroll_peeled_loops(l: &Lifted) -> Lifted {
    let g = Graph::new(l);
    let loops = find_loops(&g);
    let debug = std::env::var("EVMDEC_DEBUG_PEEL").is_ok();
    if debug && !loops.is_empty() {
        for nd in &l.nodes {
            eprintln!(
                "[peel]   node {} block {} pc {:#x} succs {:?} stmts {} term {}",
                nd.id,
                nd.block,
                nd.pc,
                nd.succs,
                nd.stmts.len(),
                match &nd.term {
                    Term::Jump(_) => "jump".to_string(),
                    Term::Branch { .. } => "branch".to_string(),
                    other => format!("{other:?}").chars().take(30).collect(),
                }
            );
        }
        for (h, lp) in &loops {
            eprintln!("[peel]   loop {} body {:?}", h, lp.body);
        }
    }
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
            if debug {
                eprintln!(
                    "[peel] loop at {} (block {:#x}): no peeled iteration",
                    h, l.nodes[h].pc
                );
            }
            continue;
        };
        if debug {
            eprintln!(
                "[peel] loop at {} (block {:#x}): copy {} of node {} is one iteration ({} node pairs)",
                h, l.nodes[h].pc, hp, q0, pairs.len()
            );
        }
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
    let debug = std::env::var("EVMDEC_DEBUG_PEEL").is_ok();
    let fail = |why: &str| {
        if debug {
            eprintln!("[peel]     copy {} of {}: {}", hp, q0, why);
        }
    };
    let mut pairs: Vec<(usize, usize)> = vec![(hp, q0)];
    let mut i = 0;
    while i < pairs.len() {
        let (p, q) = pairs[i];
        i += 1;
        let (ps, qs) = (&l.nodes[p].succs, &l.nodes[q].succs);
        if ps.len() != qs.len() {
            fail("successor counts differ");
            return None;
        }
        for (&a, &b) in ps.iter().zip(qs) {
            if a == b {
                continue;
            }
            if lp.body.contains(&a) || l.nodes[a].block != l.nodes[b].block {
                fail(&format!("successors {a}/{b} are not copies"));
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
    let mut derived: Vec<(usize, usize, ExprId, ExprId)> = Vec::new();
    for (p, q) in &pairs {
        let (sp, sq) = (&l.nodes[*p].entry_stack, &l.nodes[*q].entry_stack);
        if sp.len() != sq.len() {
            fail(&format!("stack heights of {p}/{q} differ"));
            return None;
        }
        for (a, b) in sp.iter().zip(sq) {
            if a == b {
                continue;
            }
            if !matches!(expr::node(*b), Node::Var(_)) {
                derived.push((*p, *q, *a, *b));
                continue;
            }
            if sub.insert(*b, *a).is_some_and(|old| old != *a) {
                fail("a loop variable has two initial values");
                return None;
            }
        }
    }
    if sub.is_empty() {
        fail("no variables differ");
        return None;
    }
    for (p, q, a, b) in derived {
        if with_init(b, &sub) != a {
            fail(&format!(
                "stack of {}/{} differs beyond the variables: {} vs {}",
                p,
                q,
                emit::fmt_expr(a, &Names::default()),
                emit::fmt_expr(b, &Names::default())
            ));
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
            fail(&format!("statements of {p}/{q} differ"));
            return None;
        }
        if !same_term(*p, *q) {
            fail(&format!("terminators of {p}/{q} differ"));
            return None;
        }
        if !same_edges(*p, *q) {
            fail(&format!("phi copies out of {p}/{q} differ"));
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
        Term::ReturnDyn { .. } | Term::Unresolved(_) | Term::Switch { .. } => true,
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
    let debug = std::env::var("EVMDEC_DEBUG_DEAD").is_ok();
    for nd in &l.nodes {
        if debug && nd.stmts.iter().any(|s| matches!(s, Stmt::Copy { .. })) {
            eprintln!(
                "[dead] node {} succs {:?} reads_ahead_succ {} term_reads {} stmts {:?}",
                nd.id,
                nd.succs,
                nd.succs.iter().any(|s| reads_ahead[*s]),
                term_reads_memory(&nd.term),
                nd.stmts
                    .iter()
                    .map(|s| emit::fmt_stmt(s, &Names::default()))
                    .collect::<Vec<_>>()
            );
        }
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
            ..
        } => {
            let mut v = vec![(*gas, false), (*addr, false)];
            if let Some(x) = value {
                v.push((*x, false));
            }
            match input {
                Some(w) => v.extend(words(w)),
                None => v.extend(words(input_head)),
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
        if let Some(bad) = l.nodes[x].stmts[..limit].iter().find(|s| !clean_stmt(s)) {
            if std::env::var("EVMDEC_DEBUG_BIND").is_ok() {
                eprintln!(
                    "[bind]   node {} blocks hoisting: {}",
                    x,
                    emit::fmt_stmt(bad, &Names::default())
                );
            }
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

fn bind_shared(l: &Lifted, names: &Names) -> Lifted {
    let g = Graph::new(l);
    let debug = std::env::var("EVMDEC_DEBUG_BIND").is_ok();
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
            if d == f || !available_at(l, &g, names, d, &frontier, e) {
                if debug {
                    eprintln!(
                        "[bind] skip {} (dominator {} not usable; uses {:?})",
                        emit::fmt_expr(e, &Names::default()),
                        d,
                        at
                    );
                }
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
                if debug {
                    eprintln!(
                        "[bind] skip {} (a variable it reads is reassigned before a use)",
                        emit::fmt_expr(e, &Names::default())
                    );
                }
                continue;
            }
        }
        plan.push((f, pos, e));
    }
    if plan.is_empty() {
        return l.clone();
    }
    plan.sort_by_key(|(f, pos, e)| (g.rpo_index[*f], *pos, first_seen[e]));
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
    let mut bound: Vec<(Node, ExprId)> = Vec::new();
    for (f, pos, e) in plan {
        let mut e = e;
        for (target, var) in &bound {
            e = expr::substitute(
                e,
                &|n| if n == target { Some(*var) } else { None },
                &mut HashMap::new(),
            );
        }
        if bound.iter().any(|(t, _)| *t == expr::node(e)) || !bindable(e) {
            continue;
        }
        if debug {
            eprintln!(
                "[bind] node {} {:?}: {}",
                f,
                pos,
                emit::fmt_expr(e, &Names::default())
            );
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
        bound.push((target.clone(), var));
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
    out
}

const DUP_LIMIT: usize = 6;

impl<'a> Printer<'a> {
    fn line(&mut self, depth: usize, s: &str) {
        if s.is_empty() {
            return;
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

    fn node_pc(&self, n: usize) -> usize {
        self.l.nodes[n].pc
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

    fn revert_reason(&self, mut n: usize) -> Option<Option<String>> {
        let mut seen = HashSet::new();
        let mut stores: Vec<(ExprId, ExprId)> = Vec::new();
        loop {
            if !seen.insert(n) {
                return None;
            }
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
                    stores.push((*off, *val));
                }
            }
            match &nd.term {
                Term::Jump(t) => n = *t,
                Term::Revert { data, len, off } => {
                    return Some(match data {
                        Some(words) if !words.is_empty() => {
                            let p = emit::fmt_payload(
                                words,
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
                Term::Invalid => return Some(Some("Panic(assert)".into())),
                Term::Infeasible => return Some(None),
                _ => return None,
            }
        }
    }

    fn edge_assigns(&mut self, from: usize, to: usize, depth: usize) {
        if let Some(assigns) = self.l.edge_assigns.get(&(from, to)) {
            let assigns = assigns.clone();
            self.assign_lines(&assigns, depth);
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
        if self.revert_reason(revert) != Some(None) {
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
        self.facts.push((cond, ok == *t));
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
        fw.clear();
        for (node, name, val) in &self.stored {
            if *node != n && self.g.dominates(*node, n) {
                fw.insert(*val, name.clone());
            }
        }
    }

    fn stmts(&mut self, n: usize, depth: usize) {
        self.names.end_block();
        self.refresh_forwarded(n);
        let mut dead = emit::dead_memory_stores(&self.l.nodes[n].stmts);
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
        for (i, s) in self.l.nodes[n].stmts.iter().enumerate() {
            self.names.replace_stale_in_block(replaced.drain(..));
            if let (Stmt::MStore { off, .. }, Some(stale)) = (s, self.stale_plan.get(&(n, i))) {
                let current = emit::fmt_mem_word(*off, self.names);
                let def = format!("uint256 {} = {};", stale[0].1, current);
                replaced = stale.clone();
                self.line(depth, &def);
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
                let (loads, tmp) = (stale.clone(), stale[0].1.clone());
                let (what, _) =
                    overwrites(s, self.names).expect("stale plan entries overwrite something");
                let current = match what {
                    Overwritten::Slot(key) => {
                        emit::fmt_slot(key, self.names, emit::SlotSpace::Persistent)
                    }
                    Overwritten::Balance => "address(this).balance".to_string(),
                    Overwritten::Memory(addr) => emit::fmt_mem_word(addr, self.names),
                };
                let def = format!("uint256 {} = {};", tmp, current);
                self.line(depth, &def);
                self.names.replace_stale(loads);
            }
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
            if let (Stmt::MStore { off, .. }, Some(val)) =
                (s, memory_forward(&self.l.nodes[n].stmts, i))
            {
                let word = emit::fmt_mem_word(*off, self.names);
                self.names.forward(val, word);
            }
            if let Stmt::SStore {
                key,
                val,
                transient: false,
                ..
            } = s
            {
                let name = emit::fmt_slot(*key, self.names, emit::SlotSpace::Persistent);
                self.stored.retain(|(_, nm, _)| *nm != name);
                let mut fw = self.names.forwarded.borrow_mut();
                fw.retain(|_, nm| *nm != name);
                if !expr::is_const(*val) && has_operations(*val, 1) {
                    self.stored.push((n, name.clone(), *val));
                    fw.insert(*val, name);
                }
            }
        }
        self.names.replace_stale_in_block(replaced);
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
            self.gotos += 1;
            self.line(depth, &format!("goto L{:x};", self.node_pc(n)));
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
                    self.gotos += 1;
                    self.line(
                        depth,
                        &format!("goto L{:x}; // continue outer loop", self.node_pc(n)),
                    );
                }
                return None;
            }
            if exit == Some(n) {
                if innermost {
                    self.line(depth, "break;");
                } else {
                    self.labels.insert(n);
                    self.gotos += 1;
                    self.line(
                        depth,
                        &format!("goto L{:x}; // break outer loop", self.node_pc(n)),
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
            self.gotos += 1;
            self.line(depth, &format!("goto L{:x};", self.node_pc(n)));
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
                self.line(depth.saturating_sub(1), &format!("L{:x}:", self.node_pc(n)));
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
            self.line(
                depth.saturating_sub(1),
                &format!("L{:x}:", self.node_pc(header)),
            );
        }
        let exit = match exits.len() {
            0 => None,
            1 => Some(exits[0]),
            _ => {
                let pd = self.g.ipdom[header];
                match pd {
                    Some(p) if exits.contains(&p) => Some(p),
                    _ => Some(exits[0]),
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
        if cn.stmts.is_empty() {
            if let Term::Branch {
                cond,
                t: Some(t),
                f,
            } = &cn.term
            {
                {
                    if body.contains(t) && !body.contains(f) {
                        while_cond = Some((emit::fmt_expr(*cond, self.names), *t));
                        exit = Some(*f);
                    } else if body.contains(f) && !body.contains(t) {
                        while_cond =
                            Some((emit::fmt_expr(expr::op1(op::ISZERO, *cond), self.names), *f));
                        exit = Some(*t);
                    }
                }
            }
        }
        if while_cond.is_some() && cond_node != header {
            self.emitted.insert(cond_node);
        }
        if std::env::var("EVMDEC_DEBUG_LOOP").is_ok() {
            let tf = match &nd.term {
                Term::Branch { t, f, .. } => format!(
                    "branch t={:?} (in body {:?}) f={} (in body {})",
                    t,
                    t.map(|t| body.contains(&t)),
                    f,
                    body.contains(f)
                ),
                Term::Jump(j) => format!("jump {}", j),
                Term::Switch { .. } => "switch".into(),
                _ => "other".into(),
            };
            eprintln!(
                "loop header {} pc={:#x} stmts={} {} body={:?} exits={:?} while={}",
                header,
                self.node_pc(header),
                nd.stmts.len(),
                tf,
                body.iter().collect::<Vec<_>>(),
                exits,
                while_cond.is_some()
            );
        }
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
            if let Some(a) = self.l.edge_assigns.get(&(header, e)) {
                if while_cond_exit_from_header(&self.l.nodes[header].term, e) {
                    let a = a.clone();
                    self.assign_lines(&a, depth);
                }
            }
            self.go(e, stop, depth);
        }
    }

    fn known(&self, cond: ExprId) -> Option<bool> {
        let ncond = expr::op1(op::ISZERO, cond);
        for (c, v) in self.facts.iter().rev() {
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
        if let Some(v) = self.known(cond) {
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
        let t_rev = t.map_or(Some(None), |t| self.revert_reason(t));
        let f_rev = self.revert_reason(f);
        let join = self.g.ipdom[n];
        if let Some(reason) = f_rev.clone() {
            if let (Some(t), None) = (t, &t_rev) {
                self.line(
                    depth,
                    &format!(
                        "require({}{});",
                        emit::fmt_cond(cond, self.names),
                        reason_suffix(&reason)
                    ),
                );
                self.facts.push((cond, true));
                self.transfer(n, t, stop, depth);
                self.facts.pop();
                return;
            }
        }
        if let Some(reason) = t_rev.clone() {
            if f_rev.is_none() {
                let ncond = expr::op1(op::ISZERO, cond);
                self.line(
                    depth,
                    &format!(
                        "require({}{});",
                        emit::fmt_cond(ncond, self.names),
                        reason_suffix(&reason)
                    ),
                );
                self.facts.push((cond, false));
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
        self.facts.push((cond, first_is_true_side));
        self.transfer(n, first, join, depth + 1);
        self.facts.pop();
        if first_terminal {
            self.line(depth, "}");
            self.facts.push((cond, !first_is_true_side));
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
            self.facts.push((cond, !first_is_true_side));
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
        let dead = emit::dead_memory_stores(&self.l.nodes[n].stmts);
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
        if std::env::var("EVMDEC_DEBUG_FOLD").is_ok() {
            eprintln!(
                "[fold] bool return sides {} {:?} {:?} / {} {:?} {:?}",
                t,
                self.l.nodes[t].stmts,
                self.l.nodes[t].term,
                f,
                self.l.nodes[f].stmts,
                self.l.nodes[f].term
            );
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
        let (var_s, c_s, nc_s) = (
            emit::fmt_expr(var, self.names),
            emit::fmt_expr(cond, self.names),
            emit::fmt_expr(ncond, self.names),
        );
        let txt = if y == cond {
            format!("{} = {} && {};", var_s, c_s, emit::fmt_expr(x, self.names))
        } else if x == cond {
            format!("{} = {} || {};", var_s, c_s, emit::fmt_expr(y, self.names))
        } else if x == ncond {
            format!("{} = {} && {};", var_s, nc_s, emit::fmt_expr(y, self.names))
        } else if y == ncond {
            format!("{} = {} || {};", var_s, nc_s, emit::fmt_expr(x, self.names))
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

fn reason_suffix(reason: &Option<String>) -> String {
    match reason {
        Some(r) => format!(", {}", r),
        None => String::new(),
    }
}

#[derive(Clone, Debug)]
pub struct Structured {
    pub text: String,
    pub gotos: usize,
}

const MAX_NESTING: usize = 400;

pub fn structure(l: &Lifted, names: &Names, base_depth: usize) -> Structured {
    let g = Graph::new(l);
    let loops = find_loops(&g);
    let mut used: Vec<ExprId> = Vec::new();
    for nd in &l.nodes {
        let mut probe = nd.clone();
        probe.stmts.retain(|s| !matches!(s, Stmt::Drop(_)));
        used.extend(lift::node_exprs(&probe));
    }
    used.extend(l.edge_assigns.values().flatten().map(|(_, v)| *v));
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
        gotos: 0,
        active: HashSet::new(),
        next_tmp: 1 << 30,
        used,
        facts: Vec::new(),
        stale_plan: plan_stale_loads(l, names),
        stored: Vec::new(),
        dead_stores: stores_dead_until_exit(l)
            .into_iter()
            .chain(unread_fixed_stores(l, names))
            .collect(),
        skipped: Default::default(),
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
            gotos: 0,
            active: HashSet::new(),
            facts: Vec::new(),
            stale_plan: std::mem::take(&mut p.stale_plan),
            stored: Vec::new(),
            dead_stores: std::mem::take(&mut p.dead_stores),
            skipped: Default::default(),
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
        p.gotos = p2.gotos;
        p2.out
    } else {
        p.out
    };
    Structured {
        text: drop_empty_else(&drop_unused_previous(&text)),
        gotos: p.gotos,
    }
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
    let depth = indent.len() / 4;
    let rolled = reroll_peeled_loops(l);
    let bound = bind_shared(&rolled, n);
    structure(&bound, n, depth).text
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
