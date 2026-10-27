//! Control-flow structuring: turns the lifted graph into nested `if`/`else`/`while`/`require`
//! with `break`/`continue`, falling back to labelled `goto` only when the graph is irreducible.

use crate::emit::{self, Names};
use crate::expr::{self, ExprId, Node};
use crate::lift::{self, Lifted, Stmt, Term};
use crate::opcode as op;
use crate::u256::U256;
use std::collections::{HashMap, HashSet, VecDeque};

struct Graph {
    #[allow(dead_code)]
    n: usize,
    succs: Vec<Vec<usize>>,
    preds: Vec<Vec<usize>>,
    #[allow(dead_code)]
    rpo: Vec<usize>,
    rpo_index: Vec<usize>,
    idom: Vec<Option<usize>>,
    ipdom: Vec<Option<usize>>,
    reachable: Vec<bool>,
}

fn dominators(n: usize, entry: usize, succs: &[Vec<usize>], preds: &[Vec<usize>], rpo: &[usize], rpo_index: &[usize]) -> Vec<Option<usize>> {
    // Cooper-Harvey-Kennedy.
    let mut idom: Vec<Option<usize>> = vec![None; n];
    idom[entry] = Some(entry);
    let intersect = |mut a: usize, mut b: usize, idom: &Vec<Option<usize>>| -> usize {
        while a != b {
            while rpo_index[a] > rpo_index[b] {
                a = idom[a].unwrap();
            }
            while rpo_index[b] > rpo_index[a] {
                b = idom[b].unwrap();
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
        // Reachability and RPO.
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
        // Post-dominators: reverse graph with a virtual exit (index n). Edges into "noreturn"
        // leaves (reverts, invalid jumps) are ignored so that `require`-style checks do not
        // break the post-dominance of the normal path.
        let noreturn: Vec<bool> = (0..n).map(|x| is_noreturn_leaf(l, x)).collect();
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
        // Nodes in infinite loops never reach the exit; connect loop headers of such regions too:
        // every reachable node without a path to exit gets an edge to the virtual exit.
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
        // RPO on the reverse graph from the virtual exit.
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
        let ipdom: Vec<Option<usize>> = (0..n).map(|x| ipdom_full[x].filter(|d| *d != n && *d != x)).collect();
        Graph { n, succs, preds, rpo, rpo_index, idom, ipdom, reachable }
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

/// A node (or jump chain) that only reverts / fails, with no other side effects.
fn is_noreturn_leaf(l: &Lifted, mut x: usize) -> bool {
    let mut seen = HashSet::new();
    loop {
        if !seen.insert(x) {
            return false;
        }
        let nd = &l.nodes[x];
        if !nd.stmts.iter().all(|s| matches!(s, Stmt::MStore { .. })) {
            return false;
        }
        match &nd.term {
            Term::Revert { .. } | Term::Invalid | Term::Infeasible | Term::Unresolved(_) => return true,
            Term::Jump(t) => x = *t,
            _ => return false,
        }
    }
}

struct Loop {
    #[allow(dead_code)]
    header: usize,
    body: HashSet<usize>,
    /// Nodes outside the loop that are jumped to from inside.
    exits: Vec<usize>,
}

fn find_loops(g: &Graph) -> HashMap<usize, Loop> {
    let mut loops: HashMap<usize, Loop> = HashMap::new();
    for x in 0..g.n {
        if !g.reachable[x] {
            continue;
        }
        for &s in &g.succs[x] {
            if g.dominates(s, x) {
                // Back edge x -> s. Natural loop body: nodes reaching x without passing s.
                let entry = loops.entry(s).or_insert(Loop { header: s, body: HashSet::new(), exits: Vec::new() });
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
    /// Nodes that have been referenced by a goto and so need a label.
    labels: HashSet<usize>,
    /// Loop context stack: (header, exit node to break to, body depth).
    loop_stack: Vec<(usize, Option<usize>, usize)>,
    gotos: usize,
    /// Nodes currently being emitted as a structured region (to avoid re-entering).
    active: HashSet<usize>,
    /// Boolean facts known on the current path: (condition, value).
    facts: Vec<(ExprId, bool)>,
}

const DUP_LIMIT: usize = 6;

impl<'a> Printer<'a> {
    fn line(&mut self, depth: usize, s: &str) {
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

    /// Is `n` a small terminal region (ends the call frame within a few nodes, no branches)?
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

    /// Is `n` a plain revert (possibly with a reason) with no other side effects?
    fn revert_reason(&self, mut n: usize) -> Option<Option<String>> {
        let mut seen = HashSet::new();
        loop {
            if !seen.insert(n) {
                return None;
            }
            let nd = &self.l.nodes[n];
            if !nd.stmts.iter().all(|s| matches!(s, Stmt::MStore { .. })) {
                return None;
            }
            match &nd.term {
                Term::Jump(t) => n = *t,
                Term::Revert { data, len, .. } => {
                    return Some(match data {
                        Some(words) if !words.is_empty() => {
                            let p = emit::fmt_payload(words, expr::as_const(*len), self.names, true);
                            Some(p)
                        }
                        Some(_) => None,
                        None => {
                            if expr::as_const(*len) == Some(U256::ZERO) {
                                None
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
            for (var, val) in assigns.clone() {
                let s = format!("{} = {};", emit::fmt_expr(var, self.names), emit::fmt_expr(val, self.names));
                self.line(depth, &s);
            }
        }
    }

    /// `success = to.call{value: v, gas: (v == 0) * 2300}(""); require(success);` is Solidity's
    /// `to.transfer(v)`: print it that way and continue on the success path.
    fn try_transfer_idiom(&mut self, n: usize, stop: Option<usize>, depth: usize) -> bool {
        let nd = &self.l.nodes[n];
        let Term::Branch { cond, t: Some(t), f } = &nd.term else { return false };
        let Some(Stmt::Call { kind: op::CALL, addr, value: Some(value), in_len, gas, seq, .. }) = nd.stmts.last() else { return false };
        if expr::as_const(*in_len) != Some(U256::ZERO) {
            return false;
        }
        let stipend = expr::as_const(*gas).map_or(false, |g| g == U256::from_u64(2300)) || matches!(expr::node(*gas), Node::Op(op::MUL, ref v) if expr::as_const(v[1]) == Some(U256::from_u64(2300)) || expr::as_const(v[0]) == Some(U256::from_u64(2300)));
        if !stipend {
            return false;
        }
        let is_result = |e: ExprId| matches!(expr::node(e), Node::CallResult(s) if s == *seq);
        // require(success): the revert side has no reason.
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
        self.line(depth, &format!("payable({}).transfer({});", emit::fmt_expr(addr, self.names), emit::fmt_expr(value, self.names)));
        self.facts.push((cond, ok == *t));
        self.transfer(n, ok, stop, depth);
        self.facts.pop();
        true
    }

    fn stmts(&mut self, n: usize, depth: usize) {
        for s in &self.l.nodes[n].stmts {
            // A call whose every result prints under an alias (storage-string loader) is implied.
            if let Stmt::Internal { results, .. } = s {
                if !results.is_empty() && results.iter().all(|r| self.names.aliases.contains_key(r)) {
                    continue;
                }
            }
            let txt = emit::fmt_stmt(s, self.names);
            self.line(depth, &txt);
        }
    }

    /// Emit control transfer to `to` from `from` at the end of a region: either falls through to
    /// `stop`, breaks/continues, or emits the node inline / a goto.
    fn transfer(&mut self, from: usize, to: usize, stop: Option<usize>, depth: usize) {
        self.edge_assigns(from, to, depth);
        self.go(to, stop, depth);
    }

    /// Continue emission at node `n` until `stop`.
    fn go(&mut self, n: usize, stop: Option<usize>, depth: usize) {
        if Some(n) == stop {
            return;
        }
        // Loop control.
        for i in (0..self.loop_stack.len()).rev() {
            let (header, exit, body_depth) = self.loop_stack[i];
            let innermost = i == self.loop_stack.len() - 1;
            if n == header {
                if innermost {
                    // A `continue` directly at the body level is always the last statement of the body.
                    if depth != body_depth {
                        self.line(depth, "continue;");
                    }
                } else {
                    self.labels.insert(n);
                    self.gotos += 1;
                    self.line(depth, &format!("goto L{:x}; // continue outer loop", self.node_pc(n)));
                }
                return;
            }
            if exit == Some(n) {
                if innermost {
                    self.line(depth, "break;");
                } else {
                    self.labels.insert(n);
                    self.gotos += 1;
                    self.line(depth, &format!("goto L{:x}; // break outer loop", self.node_pc(n)));
                }
                return;
            }
        }
        if self.emitted.contains(&n) || self.active.contains(&n) {
            if self.is_small_terminal(n) && !self.active.contains(&n) {
                self.emit_dup(n, depth);
                return;
            }
            self.labels.insert(n);
            self.gotos += 1;
            self.line(depth, &format!("goto L{:x};", self.node_pc(n)));
            return;
        }
        self.emit_node(n, stop, depth);
    }

    /// Emit a copy of a small terminal chain.
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

    fn emit_node(&mut self, n: usize, stop: Option<usize>, depth: usize) {
        // Loop header?
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
        let term = self.l.nodes[n].term.clone();
        match term {
            Term::Jump(t) => self.transfer(n, t, stop, depth),
            Term::Branch { t: Some(t), f, .. } if t == f => self.transfer(n, f, stop, depth),
            Term::Branch { cond, t, f } => self.emit_branch(n, cond, t, f, stop, depth),
            Term::Switch { target, cases } => {
                let tgt = emit::fmt_expr(target, self.names);
                self.line(depth, &format!("switch ({}) {{", tgt));
                for (i, c) in cases.iter().enumerate() {
                    self.line(depth + 1, &format!("case {}: {{", i));
                    self.transfer(n, *c, stop, depth + 2);
                    self.line(depth + 1, "}");
                }
                self.line(depth, "}");
            }
            other => {
                if let Some(s) = emit::fmt_term_halt(&other, self.names) {
                    self.line(depth, &s);
                }
            }
        }
    }

    fn emit_loop(&mut self, header: usize, body: &HashSet<usize>, exits: &[usize], stop: Option<usize>, depth: usize) {
        self.emitted.insert(header);
        if self.labels.contains(&header) {
            self.line(depth.saturating_sub(1), &format!("L{:x}:", self.node_pc(header)));
        }
        // Prefer the post-dominator of the header as the loop's continuation if it is an exit.
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
        // `while (cond)` form: header has no statements and branches to an exit.
        let mut while_cond: Option<(String, usize)> = None;
        if nd.stmts.is_empty() {
            if let Term::Branch { cond, t, f } = &nd.term {
                if let Some(t) = t {
                    if exit == Some(*f) && body.contains(t) {
                        while_cond = Some((emit::fmt_expr(*cond, self.names), *t));
                    } else if exit == Some(*t) && body.contains(f) {
                        while_cond = Some((emit::fmt_expr(expr::op1(op::ISZERO, *cond), self.names), *f));
                    }
                }
            }
        }
        self.loop_stack.push((header, exit, depth + 1));
        match while_cond {
            Some((c, first)) => {
                self.line(depth, &format!("while ({}) {{", c));
                self.active.insert(header);
                self.edge_assigns(header, first, depth + 1);
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
                    Term::Branch { cond, t, f } => self.emit_branch(header, cond, t, f, None, depth + 1),
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
            // Edge assignments on the exit edge(s) are emitted inside the loop before `break`;
            // for the `while (cond)` form the header->exit edge assignments go here.
            if let Some(a) = self.l.edge_assigns.get(&(header, e)) {
                if while_cond_exit_from_header(&self.l.nodes[header].term, e) {
                    for (var, val) in a.clone() {
                        let s = format!("{} = {};", emit::fmt_expr(var, self.names), emit::fmt_expr(val, self.names));
                        self.line(depth, &s);
                    }
                }
            }
            self.go(e, stop, depth);
        }
    }

    /// Is `cond` known true/false on the current path?
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

    fn emit_branch(&mut self, n: usize, cond: ExprId, t: Option<usize>, f: usize, stop: Option<usize>, depth: usize) {
        // A condition already decided on this path: only one side can execute.
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
        // require(): one side is a plain revert.
        let t_rev = t.map_or(Some(None), |t| self.revert_reason(t));
        let f_rev = self.revert_reason(f);
        let join = self.g.ipdom[n];
        if let Some(reason) = f_rev.clone() {
            if t.is_some() && t_rev.is_none() {
                // if (!cond) revert  =>  require(cond)
                let t = t.unwrap();
                self.line(depth, &format!("require({}{});", emit::fmt_expr(cond, self.names), reason_suffix(&reason)));
                self.facts.push((cond, true));
                self.transfer(n, t, stop, depth);
                self.facts.pop();
                return;
            }
        }
        if let Some(reason) = t_rev.clone() {
            if f_rev.is_none() {
                let ncond = expr::op1(op::ISZERO, cond);
                self.line(depth, &format!("require({}{});", emit::fmt_expr(ncond, self.names), reason_suffix(&reason)));
                self.facts.push((cond, false));
                self.transfer(n, f, stop, depth);
                self.facts.pop();
                return;
            }
        }
        let Some(t) = t else {
            self.line(depth, &format!("if ({}) {{ revert(); }}", emit::fmt_expr(cond, self.names)));
            self.transfer(n, f, stop, depth);
            return;
        };
        // Conditional assignment: `if (c) { v = X } else { v = Y }` with nothing else happening.
        if let Some(j) = join {
            if let Some(txt) = self.try_ternary(n, cond, t, f, j) {
                self.line(depth, &txt);
                self.go(j, stop, depth);
                return;
            }
        }
        // Choose the join: immediate post-dominator (if it is beyond both sides), else `stop`.
        let join = match join {
            Some(j) if j != n => Some(j),
            _ => stop,
        };
        // If one side is terminal (never reaches the join) and small, print it as an early exit.
        let t_terminal = self.region_is_terminal(t, join);
        let f_terminal = self.region_is_terminal(f, join);
        let (first_cond, first, second, first_terminal) = if t_terminal && !f_terminal {
            (cond, t, f, true)
        } else if f_terminal && !t_terminal {
            (expr::op1(op::ISZERO, cond), f, t, true)
        } else {
            // Prefer the "else-less" shape when the false side is the join itself.
            if Some(f) == join {
                (cond, t, f, false)
            } else if Some(t) == join {
                (expr::op1(op::ISZERO, cond), f, t, false)
            } else {
                (cond, t, f, false)
            }
        };
        let first_is_true_side = first == t && first_cond == cond;
        self.line(depth, &format!("if ({}) {{", emit::fmt_expr(first_cond, self.names)));
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
            // The direct edge may carry phi copies: they belong in an else branch.
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

    /// Edge copies of a side that is either the join itself or a statement-free node jumping to it.
    fn side_assigns(&self, n: usize, side: usize, join: usize) -> Option<Vec<(ExprId, ExprId)>> {
        if side == join {
            return Some(self.l.edge_assigns.get(&(n, side)).cloned().unwrap_or_default());
        }
        let nd = &self.l.nodes[side];
        if !nd.stmts.is_empty() || nd.preds.len() != 1 || self.emitted.contains(&side) {
            return None;
        }
        match nd.term {
            Term::Jump(t) if t == join => {
                let mut v = self.l.edge_assigns.get(&(n, side)).cloned().unwrap_or_default();
                v.extend(self.l.edge_assigns.get(&(side, join)).cloned().unwrap_or_default());
                Some(v)
            }
            _ => None,
        }
    }

    fn try_ternary(&mut self, n: usize, cond: ExprId, t: usize, f: usize, join: usize) -> Option<String> {
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
        // `v = c ? x : y` with one side equal to the condition (or its negation) is a
        // short-circuit:  c ? x : c  = c && x      c ? c : y  = c || y
        //                 c ? !c : y = !c && y     c ? x : !c = !c || x
        let (var_s, c_s, nc_s) = (emit::fmt_expr(var, self.names), emit::fmt_expr(cond, self.names), emit::fmt_expr(ncond, self.names));
        let txt = if y == cond {
            format!("{} = {} && {};", var_s, c_s, emit::fmt_expr(x, self.names))
        } else if x == cond {
            format!("{} = {} || {};", var_s, c_s, emit::fmt_expr(y, self.names))
        } else if x == ncond {
            format!("{} = {} && {};", var_s, nc_s, emit::fmt_expr(y, self.names))
        } else if y == ncond {
            format!("{} = {} || {};", var_s, nc_s, emit::fmt_expr(x, self.names))
        } else {
            format!("{} = {} ? {} : {};", var_s, c_s, emit::fmt_expr(x, self.names), emit::fmt_expr(y, self.names))
        };
        if expr::is_boolean(x) && expr::is_boolean(y) {
            expr::mark_boolean(var);
        }
        Some(txt)
    }

    /// Does the region starting at `start` never reach `join` (every path halts, breaks or continues)?
    /// With no join, the region must be small and every path must end in a halt.
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
            // Loop control edges count as terminal.
            if self.loop_stack.iter().any(|(h, e, _)| *h == x || *e == Some(x)) {
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

pub struct Structured {
    pub text: String,
    pub gotos: usize,
}

pub fn structure(l: &Lifted, names: &Names, base_depth: usize) -> Structured {
    let g = Graph::new(l);
    let loops = find_loops(&g);
    let mut p = Printer { l, g, loops, names, out: String::new(), emitted: HashSet::new(), labels: HashSet::new(), loop_stack: Vec::new(), gotos: 0, active: HashSet::new(), facts: Vec::new() };
    p.go(l.entry, None, base_depth);
    // Emit any reachable nodes that were targeted by gotos but never emitted (irreducible parts).
    let mut pending: Vec<usize> = p.labels.iter().copied().filter(|n| !p.emitted.contains(n)).collect();
    let mut rounds = 0;
    while !pending.is_empty() && rounds < 64 {
        rounds += 1;
        pending.sort_by_key(|n| p.g.rpo_index[*n]);
        for n in pending {
            if !p.emitted.contains(&n) {
                p.emit_node(n, None, base_depth);
            }
        }
        pending = p.labels.iter().copied().filter(|n| !p.emitted.contains(n)).collect();
    }
    // Labels are known only after printing: insert them where referenced nodes were emitted.
    // The printer emits labels eagerly when known; a second pass handles labels discovered later.
    let text = if p.labels.iter().any(|n| p.emitted.contains(n)) {
        let g2 = Graph::new(l);
        let loops2 = find_loops(&g2);
        let mut p2 = Printer { l, g: g2, loops: loops2, names, out: String::new(), emitted: HashSet::new(), labels: p.labels.clone(), loop_stack: Vec::new(), gotos: 0, active: HashSet::new(), facts: Vec::new() };
        p2.go(l.entry, None, base_depth);
        let mut pending: Vec<usize> = p2.labels.iter().copied().filter(|n| !p2.emitted.contains(n)).collect();
        let mut rounds = 0;
        while !pending.is_empty() && rounds < 64 {
            rounds += 1;
            pending.sort_by_key(|n| p2.g.rpo_index[*n]);
            for n in pending {
                if !p2.emitted.contains(&n) {
                    p2.emit_node(n, None, base_depth);
                }
            }
            pending = p2.labels.iter().copied().filter(|n| !p2.emitted.contains(n)).collect();
        }
        p.gotos = p2.gotos;
        p2.out
    } else {
        p.out
    };
    Structured { text: drop_empty_else(&text), gotos: p.gotos }
}

/// Empty branches: `} else {` directly followed by `}` loses the else; `if (...) {` directly
/// followed by `}` (and no else) disappears entirely (conditions are pure). Repeated until stable,
/// since removing an else can expose an empty if and vice versa.
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
        if l.trim() == "} else {" && i + 1 < lines.len() && lines[i + 1].trim() == "}" && indent(lines[i + 1]) == indent(l) {
            out.push(lines[i + 1]);
            i += 2;
            continue;
        }
        let t = l.trim();
        if t.starts_with("if (") && t.ends_with(") {") && i + 1 < lines.len() && lines[i + 1].trim() == "}" && indent(lines[i + 1]) == indent(l) && !(i + 2 < lines.len() && lines[i + 2].trim().starts_with("else")) {
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
    structure(l, n, depth).text
}

#[allow(dead_code)]
fn unused(_: &Node) {}
#[allow(dead_code)]
fn unused2(_: &dyn Fn(&lift::LNode)) {}

#[cfg(test)]
mod tests {
    #[test]
    fn empty_branches_are_dropped() {
        let t = "            } else {\n                if (32 > returndatasize()) {\n                }\n                log1(x);\n            }\n";
        let out = super::drop_empty_else(t);
        assert!(!out.contains("if (32"), "{}", out);
    }
}

