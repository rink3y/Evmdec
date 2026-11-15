use crate::emit::{self, calldata_word_index};
use crate::expr::{self, ExprId, Node};
use crate::lift::{self, Lifted, Root, Stmt, Term};
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
    pub entry: usize,
}

#[derive(Clone, Debug)]
pub struct Dispatch {
    pub functions: Vec<Discovered>,
    pub fallback: Option<usize>,
    pub receive: Option<usize>,
    pub dispatcher: HashSet<usize>,
}

fn branch_polarity(cond: ExprId) -> Option<(u32, bool)> {
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

pub fn discover(main: &Lifted) -> Dispatch {
    let mut functions: Vec<Discovered> = Vec::new();
    let mut entries: HashSet<usize> = HashSet::new();
    let mut sel_nodes: Vec<usize> = Vec::new();
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
    if sel_nodes.is_empty() {
        return Dispatch {
            functions: vec![],
            fallback: Some(main.entry),
            receive: None,
            dispatcher: HashSet::new(),
        };
    }
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
    let mut fallback = None;
    let mut receive = None;
    let mut exits: Vec<(usize, usize)> = Vec::new();
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
        if is_plain_revert(main, to) {
            continue;
        }
        let from_term = &main.nodes[from].term;
        let is_receive = match from_term {
            Term::Branch { cond, t, .. } => {
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
    let mut at = n;
    // Empty blocks can jump to each other in a ring. The hop count ends that walk.
    for _ in 0..=l.nodes.len() {
        let nd = &l.nodes[at];
        match &nd.term {
            Term::Revert { data, len, .. } => {
                return nd.stmts.iter().all(|s| matches!(s, Stmt::MStore { .. }))
                    && (data.as_ref().is_some_and(|d| d.is_empty())
                        || expr::as_const(*len) == Some(U256::ZERO));
            }
            Term::Invalid | Term::Infeasible => return true,
            Term::Jump(t) if nd.stmts.is_empty() => at = *t,
            _ => return false,
        }
    }
    false
}

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
        entry_loads: l.entry_loads.clone(),
        mem_writes: l.mem_writes.clone(),
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
                Stmt::Call { kind, addr, .. } => {
                    let built_in = expr::as_const(*addr).is_some_and(crate::interp::built_in);
                    if *kind == op::STATICCALL || built_in {
                        e.static_calls = true;
                    } else {
                        e.calls = true;
                    }
                    if !built_in && (*kind == op::DELEGATECALL || *kind == op::CALLCODE) {
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
            if expr::contains(x, &|n| matches!(n, Node::SLoad(..))) {
                e.reads_storage = true;
            }
            if expr::contains(x, &|n| {
                matches!(n, Node::Env(o, _) if matches!(*o, op::CALLER | op::ORIGIN | op::TIMESTAMP | op::NUMBER | op::COINBASE | op::GASLIMIT | op::CHAINID | op::SELFBALANCE | op::BASEFEE | op::ADDRESS | op::PREVRANDAO | op::GASPRICE | op::BLOBBASEFEE))
                    || matches!(n, Node::Op(o, _) if matches!(*o, op::BALANCE | op::EXTCODESIZE | op::EXTCODEHASH | op::BLOCKHASH))
            }) {
                e.reads_env = true;
            }
        }
    }
    e
}

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

#[derive(Clone, Debug, Default, Serialize)]
pub struct Param {
    pub index: u32,
    pub ty: String,
    pub name: String,
}

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

type Start = (Vec<ExprId>, u64);

const MAX_MEMBERS: u64 = 32;
const MAX_STRIDE: u64 = 16;
const MAX_NESTING: u32 = 2;

fn sum_of(e: ExprId, minus: bool, parts: &mut [Vec<ExprId>; 2], konst: &mut U256, depth: u32) {
    let (same, other) = (minus, !minus);
    match expr::node(e) {
        Node::Const(c) if minus => *konst = konst.wrapping_sub(c),
        Node::Const(c) => *konst = konst.wrapping_add(c),
        Node::Op(op::ADD, v) if depth < 8 => {
            sum_of(v[0], same, parts, konst, depth + 1);
            sum_of(v[1], same, parts, konst, depth + 1);
        }
        Node::Op(op::SUB, v) if depth < 8 => {
            sum_of(v[0], same, parts, konst, depth + 1);
            sum_of(v[1], other, parts, konst, depth + 1);
        }
        _ => parts[usize::from(minus)].push(e),
    }
}

fn start_of(offset: ExprId) -> Option<Start> {
    let (mut parts, mut konst) = ([Vec::new(), Vec::new()], U256::ZERO);
    sum_of(offset, false, &mut parts, &mut konst, 0);
    let [mut plus, minus] = parts;
    if plus.is_empty() || plus.len() > 3 || !minus.is_empty() || !konst.fits_u64() {
        return None;
    }
    plus.sort();
    Some((plus, konst.low_u64()))
}

fn left_after(e: ExprId) -> Option<Start> {
    let (mut parts, mut konst) = ([Vec::new(), Vec::new()], U256::ZERO);
    sum_of(e, false, &mut parts, &mut konst, 0);
    let [plus, mut past] = parts;
    let size = |e: &ExprId| matches!(expr::node(*e), Node::Env(op::CALLDATASIZE, _));
    let after = U256::ZERO.wrapping_sub(konst);
    if plus.len() != 1 || !size(&plus[0]) || past.is_empty() || !after.fits_u64() {
        return None;
    }
    past.sort();
    Some((past, after.low_u64()))
}

// A struct is decoded by checking that a fixed number of bytes follow its pointer and
// reading fields at fixed places after it. An array has its length scaled by the size of
// one element. A byte string has neither.
#[derive(Default)]
struct Pointed {
    loads: HashMap<Start, ExprId>,
    heads: HashMap<Start, u64>,
    strides: HashMap<ExprId, u64>,
    addresses: HashSet<ExprId>,
    tails: HashMap<ExprId, Vec<(Vec<ExprId>, u64)>>,
}

impl Pointed {
    fn note(&mut self, x: ExprId, n: &Node) {
        let load = |e: ExprId| matches!(expr::node(e), Node::CallDataLoad(_));
        match n {
            Node::CallDataLoad(offset) => {
                if let Some(at) = start_of(*offset) {
                    self.loads.entry(at).or_insert(x);
                }
            }
            Node::Op(op::MUL, v) => {
                for (length, by) in [(v[0], v[1]), (v[1], v[0])] {
                    let words = expr::as_const(by)
                        .filter(|c| c.fits_u64())
                        .map(|c| c.low_u64());
                    if let Some(w) =
                        words.filter(|w| *w % 32 == 0 && (1..=MAX_STRIDE).contains(&(*w / 32)))
                    {
                        let stride = self.strides.entry(length).or_insert(w / 32);
                        *stride = (*stride).max(w / 32);
                    }
                }
            }
            Node::Op(op::SHL, v) => {
                let shift = expr::as_const(v[0])
                    .filter(|c| c.fits_u64())
                    .map(|c| c.low_u64());
                if let Some(s) = shift.filter(|s| (5..=9).contains(s)) {
                    let stride = self.strides.entry(v[1]).or_insert(1 << (s - 5));
                    *stride = (*stride).max(1 << (s - 5));
                }
            }
            // A narrower mask on a member may be one field taken out of a packed word,
            // which says nothing of how wide the member is declared.
            Node::Op(op::AND, v) if load(v[0]) => {
                if expr::as_const(v[1]) == Some(expr::mask_bits(160)) {
                    self.addresses.insert(v[0]);
                }
            }
            Node::Op(op::LT | op::GT | op::SLT | op::SGT, v) => {
                for (left, bound) in [(v[0], v[1]), (v[1], v[0])] {
                    let Some((past, after)) = left_after(left) else {
                        continue;
                    };
                    let words = expr::as_const(bound).filter(|c| c.fits_u64());
                    let words = words.map(|c| c.low_u64()).filter(|n| n % 32 == 0);
                    match words {
                        Some(n) if (1..=MAX_MEMBERS).contains(&(n / 32)) => {
                            let head = self.heads.entry((past, after)).or_insert(n);
                            *head = (*head).max(n);
                        }
                        None if load(bound) => {
                            self.tails.entry(bound).or_default().push((past, after));
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }

    fn word(&self, address: bool) -> String {
        match address {
            true => "address".to_string(),
            false => "uint256".to_string(),
        }
    }

    fn type_at(&self, at: &Start, depth: u32) -> String {
        self.typed(at, self.heads.get(at).copied(), depth)
    }

    // A nested value's position is counted from where the outer value's words begin, not
    // from the start of the call data.
    fn within(&self, outer: &Start, pointer: ExprId, depth: u32) -> Option<String> {
        let (through, from) = outer;
        let mut inner = through.clone();
        inner.push(pointer);
        inner.sort();
        if depth >= MAX_NESTING || !self.loads.keys().any(|(terms, _)| *terms == inner) {
            return None;
        }
        // A struct reached this way is checked by comparing its pointer with what is
        // left of the call data less its head. One word of head is also what a byte
        // string has, so that says nothing.
        let checked = self.tails.get(&pointer).into_iter().flatten();
        let head = checked
            .filter(|(minus, after)| minus == through && *after > *from)
            .map(|(_, after)| after - from + 1)
            .find(|n| n % 32 == 0 && (2..=MAX_MEMBERS).contains(&(n / 32)));
        let start = (inner, *from);
        Some(self.typed(&start, head.or(self.heads.get(&start).copied()), depth + 1))
    }

    fn array_at(&self, at: &Start, words: u64, depth: u32) -> String {
        let (through, from) = at;
        let first = from + 32;
        // An element is read at an index, which is no pointer, past the length.
        let read = |member: u64| {
            let pointer = |t: &&ExprId| matches!(expr::node(**t), Node::CallDataLoad(_));
            let mut found: Vec<ExprId> = self
                .loads
                .iter()
                .filter(|((terms, k), _)| {
                    let index: Vec<&ExprId> =
                        terms.iter().filter(|t| !through.contains(t)).collect();
                    let inside = terms.len() == through.len() + index.len() && index.len() <= 1;
                    inside && !index.iter().any(pointer) && *k == first + 32 * member
                })
                .map(|(_, load)| *load)
                .collect();
            found.sort();
            found
        };
        let plain =
            |member: u64| self.word(read(member).iter().any(|l| self.addresses.contains(l)));
        if words > 1 {
            let members: Vec<String> = (0..words).map(plain).collect();
            return format!("({})[]", members.join(","));
        }
        let data = (through.clone(), first);
        let nested = read(0)
            .into_iter()
            .find_map(|l| self.within(&data, l, depth));
        format!("{}[]", nested.unwrap_or_else(|| plain(0)))
    }

    fn typed(&self, at: &Start, head: Option<u64>, depth: u32) -> String {
        let (through, from) = at;
        let Some(head) = head else {
            let length = self.loads.get(at);
            return match length.and_then(|l| self.strides.get(l)) {
                Some(words) => self.array_at(at, *words, depth),
                None => "bytes".to_string(),
            };
        };
        let mut members: Vec<Option<String>> = (0..head / 32)
            .map(|k| {
                let member = *self.loads.get(&(through.clone(), from + 32 * k))?;
                let nested = self.within(at, member, depth);
                Some(nested.unwrap_or_else(|| self.word(self.addresses.contains(&member))))
            })
            .collect();
        // A struct is only passed by pointer when one of its members is. When the code
        // reads none of them through a pointer, the last one it leaves unread is taken
        // to be that member.
        let by_pointer = |ty: &String| ty == "bytes" || ty.ends_with("[]") || ty.starts_with('(');
        if !members.iter().flatten().any(by_pointer) {
            let unread = members.iter().rposition(Option::is_none);
            let last = unread.unwrap_or(members.len() - 1);
            members[last] = Some("bytes".to_string());
        }
        let members: Vec<String> = members
            .into_iter()
            .map(|m| m.unwrap_or("uint256".into()))
            .collect();
        format!("({})", members.join(","))
    }
}

pub fn infer_params_from(roots: &[Root]) -> Vec<Param> {
    let mut pointed = Pointed::default();
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
            pointed.note(x, &n);
            match &n {
                Node::CallDataLoad(off) => {
                    if let Some(i) = calldata_word_index(*off) {
                        max_idx = Some(max_idx.map_or(i, |m| m.max(i)));
                    } else {
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
                    for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
                        if let Some(c) = expr::as_const(b) {
                            if c.fits_u64() {
                                let (base, delta) = expr::split_offset(a);
                                if base.is_some_and(|x| {
                                    matches!(expr::node(x), Node::Env(op::CALLDATASIZE, _))
                                }) {
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
    let count = match (max_idx, head_words) {
        (_, Some(h)) => h,
        (Some(m), None) => m + 1,
        (None, None) => 0,
    };
    (0..count)
        .map(|i| {
            let ty = if dynamic.contains(&i) {
                let pointer = expr::calldataload(expr::konst_u64(4 + 32 * u64::from(i)));
                pointed.type_at(&(vec![pointer], 4), 0)
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

pub fn infer_returns(l: &Lifted) -> Vec<String> {
    let mut best: Vec<String> = Vec::new();
    for nd in &l.nodes {
        if let Term::Return { len, data, .. } = &nd.term {
            let tys: Vec<String> = match (data, expr::as_const(*len)) {
                (Some(words), Some(l))
                    if words.len() >= 2
                        && expr::as_const(words[0]) == Some(U256::from_u64(32))
                        && expr::as_const(words[1]).is_some_and(|n| {
                            n.fits_u64() && l == U256::from_u64(64 + n.low_u64().div_ceil(32) * 32)
                        }) =>
                {
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
