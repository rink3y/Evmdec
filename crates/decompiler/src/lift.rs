//! Lifting: symbolic execution of a recovered unit into expression statements.
//!
//! Every node of a `cfg::Unit` is executed with a stack of expressions, a symbolic memory and a
//! storage cache. Values that reach a node from several predecessors with different expressions
//! become `Var`s (phis) assigned on the incoming edges. Processing iterates to a fixpoint: a
//! node is re-run when its entry state changes (phis only ever increase, memory knowledge only
//! ever shrinks, so this terminates).

use crate::cfg::{AVal, Edge, Program, Unit};
use crate::expr::{self, konst, konst_u64, op1, op2, op3, ExprId, Node};
use crate::opcode as op;
use crate::u256::U256;
use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Clone, Debug)]
pub enum Stmt {
    /// `var = value` (phi copies live on edges; this is for explicit temporaries).
    Assign { var: ExprId, value: ExprId },
    MStore { off: ExprId, val: ExprId, width: u8 },
    SStore { key: ExprId, val: ExprId, transient: bool },
    Log { off: ExprId, len: ExprId, topics: Vec<ExprId>, data: Option<Vec<ExprId>> },
    Call { seq: u32, kind: u8, gas: ExprId, addr: ExprId, value: Option<ExprId>, in_off: ExprId, in_len: ExprId, out_off: ExprId, out_len: ExprId, input: Option<Vec<ExprId>>, result: ExprId },
    Create { seq: u32, kind: u8, value: ExprId, off: ExprId, len: ExprId, salt: Option<ExprId>, result: ExprId, init: Option<Vec<ExprId>> },
    /// CALLDATACOPY / CODECOPY / RETURNDATACOPY / EXTCODECOPY / MCOPY.
    Copy { kind: u8, dest: ExprId, src: ExprId, len: ExprId, addr: Option<ExprId> },
    /// Call of an internal function (another unit).
    Internal { seq: u32, callee: usize, args: Vec<ExprId>, results: Vec<ExprId> },
    /// Explicit `POP` of a value that had side effects (a call result that is ignored).
    Drop(ExprId),
}

#[derive(Clone, Debug)]
pub enum Term {
    Jump(usize),
    /// `t == None`: the true branch jumps to an invalid destination (reverts).
    Branch { cond: ExprId, t: Option<usize>, f: usize },
    Switch { target: ExprId, cases: Vec<usize> },
    Return { off: ExprId, len: ExprId, data: Option<Vec<ExprId>> },
    Revert { off: ExprId, len: ExprId, data: Option<Vec<ExprId>> },
    Stop,
    Invalid,
    SelfDestruct(ExprId),
    /// Return from an internal function unit with these values (deepest first).
    InternalReturn(Vec<ExprId>),
    /// Jump whose target could not be resolved.
    Unresolved(ExprId),
    /// Oracle mode only: a JUMPI with its condition and target expressions.
    CondJump { cond: ExprId, target: ExprId },
    /// A branch to an invalid jump destination, or stack underflow in a real frame.
    Infeasible,
}

#[derive(Clone, Debug)]
pub struct LNode {
    pub id: usize,
    pub block: usize,
    pub pc: usize,
    pub stmts: Vec<Stmt>,
    pub term: Term,
    pub preds: Vec<usize>,
    pub succs: Vec<usize>,
    /// Entry stack expressions (deepest first). Phi slots hold `Var`s.
    pub entry_stack: Vec<ExprId>,
    pub exit_stack: Vec<ExprId>,
}

#[derive(Clone, Debug)]
pub struct Lifted {
    pub nodes: Vec<LNode>,
    pub entry: usize,
    /// Phi copies to perform when taking edge (from, to): `(var, value)`.
    pub edge_assigns: HashMap<(usize, usize), Vec<(ExprId, ExprId)>>,
    /// Number of entry-stack arguments the unit consumes (`Arg(0..n)`).
    pub n_args: usize,
    pub reprocess_count: usize,
    /// Stack slot (from the top at entry) holding the return address, for internal units.
    pub ret_slot: Option<u32>,
    /// Entry state of every node (indexed by the *unit* node id), for re-lifting sub-regions.
    #[allow(dead_code)]
    pub(crate) entry_states: Vec<Option<State>>,
    /// Map from unit node id to lifted node id.
    pub node_map: HashMap<usize, usize>,
}

// ------------------------------------------------------------------------------------------
// Memory model
// ------------------------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
enum MVal {
    Word(ExprId),
    Byte(ExprId),
    /// Copied region: opcode, source offset expression, external address (EXTCODECOPY).
    Copy(u8, ExprId, Option<ExprId>),
    /// Output region of call `seq`.
    CallOut(u32),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct MemWrite {
    base: Option<ExprId>,
    off: u64,
    /// Length in bytes; `None` when symbolic.
    len: Option<u64>,
    val: MVal,
    /// Statement that produced this write: (unit node, statement index).
    origin: Option<(usize, usize)>,
    /// Memory generation *after* the statement that made this write.
    gen: u32,
}

#[derive(Clone, Debug)]
struct Mem {
    writes: Vec<MemWrite>,
    /// Untouched bytes read as zero (true at the start of a call frame).
    fresh: bool,
    /// Memory generation: advanced once per memory-writing statement. An unknown read is
    /// stamped with the generation of the last write that may alias it, so `mem[x]` denotes the
    /// memory at a precise program point (the oracle relies on this) while unrelated writes in
    /// between do not change the expression.
    gen: u32,
    /// Generation after the last event that may have changed arbitrary memory (clobber, forgotten writes).
    clobber_gen: u32,
}

const BIG: u64 = 1 << 40;

/// Normalise an offset into `(base, delta)` with a small delta.
fn norm_offset(e: ExprId) -> (Option<ExprId>, u64) {
    let (b, d) = expr::split_offset(e);
    if d.fits_u64() && d.low_u64() < BIG {
        (b, d.low_u64())
    } else if b.is_none() {
        // A huge constant offset: keep as a symbolic base.
        (Some(e), 0)
    } else {
        (Some(e), 0)
    }
}

impl Mem {
    fn new(fresh: bool) -> Mem {
        Mem { writes: Vec::new(), fresh, gen: 0, clobber_gen: 0 }
    }

    /// Advance the generation (once per memory-writing statement).
    fn tick(&mut self) {
        self.gen += 1;
    }

    /// Version stamp for an unknown read of `n` bytes at `off`: the generation of the latest
    /// write that may alias it (same base and overlapping, or symbolic length on the same base),
    /// else the last clobber.
    fn version_for(&self, off: ExprId, n: u64) -> u32 {
        let (base, d) = norm_offset(off);
        let mut v = self.clobber_gen;
        for w in &self.writes {
            if w.base != base {
                continue;
            }
            let hit = match w.len {
                Some(wl) => w.off < d + n && d < w.off + wl,
                None => d + n > w.off,
            };
            if hit {
                v = v.max(w.gen);
            }
        }
        v
    }

    fn store(&mut self, off: ExprId, len: Option<u64>, val: MVal) {
        self.store_from(off, len, val, None)
    }

    fn store_from(&mut self, off: ExprId, len: Option<u64>, val: MVal, origin: Option<(usize, usize)>) {
        let (base, d) = norm_offset(off);
        if let Some(l) = len {
            // Remove writes fully covered by this one (same base).
            self.writes.retain(|w| !(w.base == base && w.len.map_or(false, |wl| w.off >= d && w.off + wl <= d + l)));
        }
        if self.writes.len() > 256 {
            // Forgotten writes: anything may have changed since this point.
            self.writes.drain(..64);
            self.fresh = false;
            self.clobber_gen = self.gen + 1;
        }
        self.writes.push(MemWrite { base, off: d, len, val, origin, gen: self.gen + 1 });
    }

    /// Origins of the word writes that a read of `n` bytes at `off` would consume.
    fn consumers(&self, off: ExprId, n: u64) -> Vec<(usize, usize)> {
        let (base, d) = norm_offset(off);
        let mut out = Vec::new();
        for w in self.writes.iter().rev() {
            if w.base != base {
                continue;
            }
            let Some(wl) = w.len else { break };
            if w.off < d + n && d < w.off + wl {
                if let Some(o) = w.origin {
                    out.push(o);
                }
            }
        }
        out
    }

    /// Forget everything (after an internal call or an unknown-length write to a symbolic base).
    fn clobber(&mut self) {
        self.writes.clear();
        self.fresh = false;
        self.gen += 1;
        self.clobber_gen = self.gen;
    }

    /// Read `n` bytes (n <= 32) at `off` as a word (right-aligned), if known.
    fn load_bytes(&self, off: ExprId, n: u64, version: u32) -> Option<ExprId> {
        let (base, d) = norm_offset(off);
        // Collect per-byte sources.
        let mut pieces: Vec<Option<(ExprId, u64)>> = vec![None; n as usize]; // (word expr, byte index within word)
        let mut copy_hit: Option<(u8, ExprId, Option<ExprId>, u64, u32)> = None;
        let mut covered = 0usize;
        for w in self.writes.iter().rev() {
            if covered == n as usize {
                break;
            }
            if w.base != base {
                // Different bases are assumed not to alias, except symbolic-length writes on the same base.
                continue;
            }
            let Some(wl) = w.len else {
                // Unknown-length write on the same base: anything at or past its start may be clobbered.
                if d + n > w.off {
                    return None;
                }
                continue;
            };
            let lo = w.off.max(d);
            let hi = (w.off + wl).min(d + n);
            if lo >= hi {
                continue;
            }
            match &w.val {
                MVal::Word(v) => {
                    for b in lo..hi {
                        let i = (b - d) as usize;
                        if pieces[i].is_none() {
                            pieces[i] = Some((*v, b - w.off));
                            covered += 1;
                        }
                    }
                }
                MVal::Byte(v) => {
                    let i = (lo - d) as usize;
                    if pieces[i].is_none() {
                        pieces[i] = Some((op2(op::SHL, konst_u64(248), *v), 0));
                        covered += 1;
                    }
                }
                MVal::Copy(k, src, addr) => {
                    // Whole read inside one copy and nothing newer overlapping: a copied word.
                    if lo == d && hi == d + n && covered == 0 {
                        copy_hit = Some((*k, *src, *addr, d - w.off, w.gen));
                        covered = n as usize;
                        break;
                    }
                    return None;
                }
                MVal::CallOut(seq) => {
                    if lo == d && hi == d + n && covered == 0 {
                        let seq = *seq;
                        let word = expr::intern(Node::ReturnData(seq, konst_u64(d - w.off)));
                        return Some(if n == 32 { word } else { op2(op::SHR, konst_u64(8 * (32 - n)), word) });
                    }
                    return None;
                }
            }
        }
        let _ = version;
        if let Some((k, src, _addr, delta, wgen)) = copy_hit {
            let word = expr::intern(Node::CopiedWord(k, expr::add_const(src, U256::from(delta)), wgen));
            return Some(if n == 32 { word } else { op2(op::SHR, konst_u64(8 * (32 - n)), word) });
        }
        if covered < n as usize {
            if !self.fresh {
                return None;
            }
        }
        // Fast path: a single word write exactly aligned.
        if n == 32 {
            if let Some((v, 0)) = pieces[0] {
                if pieces.iter().enumerate().all(|(i, p)| *p == Some((v, i as u64))) {
                    return Some(v);
                }
            }
        }
        // Compose byte by byte: result byte j (0 = most significant of the n-byte value) comes from
        // byte `bi` of word `v` : (v >> (8*(31-bi))) & 0xff, placed at shift 8*(n-1-j).
        let mut acc: Option<ExprId> = None;
        let mut j = 0usize;
        while j < n as usize {
            match pieces[j] {
                None => {
                    j += 1; // zero byte (fresh memory)
                }
                Some((v, bi)) => {
                    // Extend the run of consecutive bytes from the same word.
                    let mut run = 1usize;
                    while j + run < n as usize {
                        match pieces[j + run] {
                            Some((v2, bi2)) if v2 == v && bi2 == bi + run as u64 => run += 1,
                            _ => break,
                        }
                    }
                    // Extract bytes [bi, bi+run) of v as a right-aligned value.
                    let shr = 8 * (32 - (bi + run as u64));
                    let mut piece = if shr > 0 { op2(op::SHR, konst_u64(shr), v) } else { v };
                    if bi > 0 {
                        piece = op2(op::AND, piece, konst(expr::mask_bits(8 * run as u32)));
                    }
                    let place = 8 * (n as usize - j - run) as u64;
                    if place > 0 {
                        piece = op2(op::SHL, konst_u64(place), piece);
                    }
                    acc = Some(match acc {
                        None => piece,
                        Some(a) => op2(op::OR, a, piece),
                    });
                    j += run;
                }
            }
        }
        Some(acc.unwrap_or_else(|| konst(U256::ZERO)))
    }

    fn load_word(&self, off: ExprId, version: u32) -> ExprId {
        match self.load_bytes(off, 32, version) {
            Some(v) => v,
            None => expr::intern(Node::MLoad(off, self.version_for(off, 32))),
        }
    }

    /// Known words of a region of `len` bytes (len multiple-of-32 or with a tail).
    fn read_region(&self, off: ExprId, len: u64, version: u32) -> Option<(Vec<ExprId>, u8)> {
        if len > 8192 {
            return None;
        }
        let mut words = Vec::new();
        let mut i = 0;
        while i + 32 <= len {
            words.push(self.load_bytes(expr::add_const(off, U256::from(i)), 32, version)?);
            i += 32;
        }
        let tail = (len - i) as u8;
        if tail > 0 {
            words.push(self.load_bytes(expr::add_const(off, U256::from(i)), tail as u64, version)?);
        }
        Some((words, tail))
    }

    /// Intersection with another memory (merge point).
    fn intersect(&mut self, other: &Mem) -> bool {
        let before = self.writes.len();
        let fresh_before = self.fresh;
        let gen_before = self.gen;
        // Same write = same base/offset/length/value (generation and origin may differ).
        self.writes.retain(|w| other.writes.iter().any(|o| o.base == w.base && o.off == w.off && o.len == w.len && o.val == w.val));
        self.fresh &= other.fresh;
        if other.gen != self.gen || other.clobber_gen != self.clobber_gen {
            // Different histories: unknown reads must not be conflated across predecessors.
            self.gen = self.gen.max(other.gen) + 1;
            self.clobber_gen = self.gen;
        }
        before != self.writes.len() || fresh_before != self.fresh || gen_before != self.gen
    }
}

// ------------------------------------------------------------------------------------------
// Lifting
// ------------------------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct State {
    stack: Vec<ExprId>,
    /// Lazily materialised entry arguments (`Arg(i)`), count.
    args_used: usize,
    mem: Mem,
    /// Storage cache: writes known on this path (key -> value) in order.
    storage: Vec<(ExprId, ExprId, bool)>,
    version: u32,
    /// Storage generation: bumped when storage may have changed in an unknown way.
    sgen: u32,
    /// An external call or create has happened on this path (return data may be non-empty).
    called: bool,
}

impl State {
    fn pop(&mut self, root: bool, underflow: &mut bool) -> ExprId {
        match self.stack.pop() {
            Some(v) => v,
            None => {
                if root {
                    *underflow = true;
                }
                let v = expr::arg(self.args_used as u32);
                self.args_used += 1;
                v
            }
        }
    }
    fn peek(&mut self, n: usize, root: bool, underflow: &mut bool) -> ExprId {
        while self.stack.len() < n {
            if root {
                *underflow = true;
            }
            let v = expr::arg(self.args_used as u32);
            self.args_used += 1;
            self.stack.insert(0, v);
        }
        self.stack[self.stack.len() - n]
    }
}

pub struct Lifter<'a> {
    pub prog: &'a Program,
    /// Root frame semantics (main unit): empty stack, zero memory.
    pub root: bool,
    /// Effect summaries of simple internal functions, by entry block.
    pub summaries: HashMap<usize, CalleeSummary>,
    /// Oracle mode: keep jump target/condition expressions instead of resolving successors.
    pub oracle: bool,
}

/// What a *simple* internal function does, in terms of its entry-stack arguments `Arg(i)`:
/// straight-line (apart from require-style reverts), no calls, no loops.
#[derive(Clone, Debug, Default)]
pub struct CalleeSummary {
    /// Returned values (deepest first), excluding the return address.
    pub returns: Vec<ExprId>,
    /// 32-byte memory writes in order.
    pub mstores: Vec<(ExprId, ExprId)>,
    /// Writes storage, logs, calls or creates.
    pub side_effects: bool,
    /// Every path reverts with this payload (offset, length, decoded words): a panic/revert helper.
    pub reverts: Option<(ExprId, ExprId, Option<Vec<ExprId>>)>,
}

/// Compute a summary from a lifted internal function, if it is simple enough.
pub fn summarize(l: &Lifted) -> Option<CalleeSummary> {
    let mut n = l.entry;
    let mut seen = HashSet::new();
    let mut sum = CalleeSummary::default();
    loop {
        if !seen.insert(n) || seen.len() > 64 {
            return None;
        }
        let nd = &l.nodes[n];
        for s in &nd.stmts {
            match s {
                Stmt::MStore { off, val, width: 32 } => sum.mstores.push((*off, *val)),
                Stmt::MStore { .. } => return None,
                Stmt::Copy { .. } | Stmt::Internal { .. } | Stmt::Call { .. } | Stmt::Create { .. } => return None,
                Stmt::SStore { .. } | Stmt::Log { .. } => sum.side_effects = true,
                Stmt::Assign { .. } | Stmt::Drop(_) => {}
            }
        }
        match &nd.term {
            Term::Revert { off, len, data } if seen.len() <= 4 => {
                // A helper whose only job is to revert (solc panic/error helpers).
                sum.reverts = Some((*off, *len, data.clone()));
                return Some(sum);
            }
            Term::InternalReturn(vals) => {
                sum.returns = vals.clone();
                // Expressions must not depend on the callee's own memory versions in complex ways.
                let ok = sum.returns.iter().chain(sum.mstores.iter().flat_map(|(a, b)| [a, b])).all(|e| expr::size(*e) <= 64 && !expr::contains(*e, &|x| matches!(x, Node::Var(_) | Node::IntRet(..) | Node::CallResult(_) | Node::Unknown(_))));
                return if ok { Some(sum) } else { None };
            }
            Term::Jump(t) => n = *t,
            Term::Branch { t, f, .. } => {
                // Follow the non-reverting side if the other only reverts.
                let rev = |x: usize| matches!(l.nodes[x].term, Term::Revert { .. } | Term::Invalid | Term::Infeasible) && l.nodes[x].stmts.iter().all(|s| matches!(s, Stmt::MStore { .. }));
                match t {
                    Some(t) if rev(*t) && !rev(*f) => n = *f,
                    Some(t) if rev(*f) && !rev(*t) => n = *t,
                    None => n = *f,
                    _ => return None,
                }
            }
            _ => return None,
        }
    }
}

/// Memory writes whose only purpose was to feed a hash, log, return, revert or call payload that
/// was decoded: they are dropped from the output as encoding noise.
#[derive(Default)]
struct Hidden {
    set: std::cell::RefCell<HashSet<(usize, usize)>>,
}

#[derive(Clone)]
struct Entry {
    state: State,
    /// Which stack positions (from the bottom of the entry stack) are phis.
    phis: Vec<bool>,
}

impl<'a> Lifter<'a> {
    pub fn lift(&self, unit: &Unit, initial: Option<(Vec<ExprId>, bool)>) -> Lifted {
        let (init_stack, fresh) = initial.unwrap_or((Vec::new(), self.root));
        let state = State { stack: init_stack, args_used: 0, mem: Mem::new(fresh), storage: Vec::new(), version: 0, sgen: 0, called: !fresh };
        self.lift_from(unit, state)
    }

    /// Entry state of a lifted node, to lift a sub-region starting there separately.
    pub fn entry_state_of(l: &Lifted, unit_node: usize) -> Option<State> {
        l.entry_states.get(unit_node).cloned().flatten()
    }

    pub fn lift_from(&self, unit: &Unit, init: State) -> Lifted {
        let n = unit.nodes.len();
        let mut entries: Vec<Option<Entry>> = vec![None; n];
        let mut lnodes: Vec<Option<LNode>> = vec![None; n];
        let mut exit_states: Vec<Option<State>> = vec![None; n];
        let mut runs = vec![0usize; n];
        let mut phi_ids: HashMap<(usize, usize), ExprId> = HashMap::new();
        let mut next_var: u32 = 0;
        let mut work: VecDeque<usize> = VecDeque::new();
        let mut queued = vec![false; n];
        let mut reprocess_count = 0usize;

        let hidden = Hidden::default();
        let init_len = init.stack.len();
        entries[unit.entry] = Some(Entry { state: init, phis: vec![false; init_len] });
        work.push_back(unit.entry);
        queued[unit.entry] = true;
        let mut max_args = 0usize;

        while let Some(nid) = work.pop_front() {
            queued[nid] = false;
            runs[nid] += 1;
            if runs[nid] > 24 {
                continue;
            }
            if runs[nid] > 1 {
                reprocess_count += 1;
            }
            let entry = entries[nid].clone().unwrap();
            let (lnode, exit) = self.run_node(unit, nid, &entry.state, &hidden);
            max_args = max_args.max(exit.args_used);
            let succs: Vec<usize> = lnode.succs.clone();
            lnodes[nid] = Some(lnode);
            exit_states[nid] = Some(exit.clone());
            for s in succs {
                let single_pred = unit.nodes[s].preds.len() <= 1;
                let changed = match &mut entries[s] {
                    None => {
                        entries[s] = Some(Entry { phis: vec![false; exit.stack.len()], state: State { stack: exit.stack.clone(), args_used: exit.args_used, mem: exit.mem.clone(), storage: exit.storage.clone(), version: 0, sgen: exit.sgen, called: exit.called } });
                        true
                    }
                    Some(e) if single_pred => {
                        // One predecessor: no phi, just take the latest state.
                        let new_state = State { stack: exit.stack.clone(), args_used: exit.args_used.max(e.state.args_used), mem: exit.mem.clone(), storage: exit.storage.clone(), version: 0, sgen: exit.sgen, called: exit.called };
                        let changed = e.state.stack != new_state.stack || e.state.mem.writes != new_state.mem.writes || e.state.mem.fresh != new_state.mem.fresh || e.state.mem.gen != new_state.mem.gen || e.state.storage != new_state.storage || e.state.sgen != new_state.sgen;
                        e.state = new_state;
                        e.phis = vec![false; e.state.stack.len()];
                        changed
                    }
                    Some(e) => merge_into(e, &exit, s, &mut phi_ids, &mut next_var),
                };
                if changed && !queued[s] {
                    queued[s] = true;
                    work.push_back(s);
                }
            }
        }

        // Finalise: edge assignments and node list.
        let hidden_set = hidden.set.borrow().clone();
        let mut nodes: Vec<LNode> = Vec::new();
        let mut map: HashMap<usize, usize> = HashMap::new();
        for (i, ln) in lnodes.iter().enumerate() {
            if let Some(ln) = ln {
                map.insert(i, nodes.len());
                let mut ln = ln.clone();
                ln.entry_stack = entries[i].as_ref().map(|e| e.state.stack.clone()).unwrap_or_default();
                // Drop encoding-only memory writes and free-memory-pointer bookkeeping (display
                // only; the oracle keeps every statement).
                if !self.oracle {
                    let mut idx = 0usize;
                    ln.stmts.retain(|s| {
                        let keep = match s {
                            Stmt::MStore { off, .. } => !(hidden_set.contains(&(i, idx)) || expr::as_const(*off) == Some(U256::from_u64(0x40))),
                            _ => true,
                        };
                        idx += 1;
                        keep
                    });
                }
                nodes.push(ln);
            }
        }
        // Remap ids.
        for nd in nodes.iter_mut() {
            nd.id = map[&nd.id];
            nd.succs = nd.succs.iter().filter_map(|s| map.get(s).copied()).collect();
            nd.term = remap_term(&nd.term, &map);
        }
        let mut edge_assigns: HashMap<(usize, usize), Vec<(ExprId, ExprId)>> = HashMap::new();
        for (i, ln) in lnodes.iter().enumerate() {
            let Some(ln) = ln else { continue };
            let from = map[&i];
            let exit = exit_states[i].as_ref().unwrap();
            for s in &ln.succs {
                let Some(&to) = map.get(s) else { continue };
                let entry = entries[*s].as_ref().unwrap();
                let mut assigns = Vec::new();
                let el = entry.state.stack.len();
                let xl = exit.stack.len();
                for (k, is_phi) in entry.phis.iter().enumerate() {
                    if !*is_phi {
                        continue;
                    }
                    // Align from the top: entry position k (from bottom) corresponds to exit position
                    let from_top = el - 1 - k;
                    let var = entry.state.stack[k];
                    let val = if from_top < xl { exit.stack[xl - 1 - from_top] } else { expr::intern(Node::Unknown(expr::next_seq())) };
                    if val != var {
                        assigns.push((var, val));
                    }
                }
                if !assigns.is_empty() {
                    edge_assigns.insert((from, to), assigns);
                }
            }
        }
        // Dead phi elimination: copies to variables that nothing reads are dropped (iterate, since
        // a phi may only feed another dead phi).
        loop {
            let mut used: HashSet<ExprId> = HashSet::new();
            let collect = |e: ExprId, used: &mut HashSet<ExprId>| {
                let mut stack = vec![e];
                let mut seen = HashSet::new();
                while let Some(x) = stack.pop() {
                    if !seen.insert(x) || seen.len() > 100_000 {
                        continue;
                    }
                    if matches!(expr::node(x), Node::Var(_)) {
                        used.insert(x);
                    }
                    stack.extend(expr::children(x));
                }
            };
            for nd in &nodes {
                for e in node_exprs(nd) {
                    collect(e, &mut used);
                }
            }
            for v in edge_assigns.values() {
                for (_, val) in v {
                    collect(*val, &mut used);
                }
            }
            let before: usize = edge_assigns.values().map(|v| v.len()).sum();
            for v in edge_assigns.values_mut() {
                // Copies of an undefined value carry no information.
                v.retain(|(var, val)| used.contains(var) && !matches!(expr::node(*val), Node::Unknown(_)));
            }
            edge_assigns.retain(|_, v| !v.is_empty());
            let after: usize = edge_assigns.values().map(|v| v.len()).sum();
            if after == before {
                break;
            }
        }
        // preds
        let mut preds: Vec<Vec<usize>> = vec![Vec::new(); nodes.len()];
        for nd in &nodes {
            for s in &nd.succs {
                if !preds[*s].contains(&nd.id) {
                    preds[*s].push(nd.id);
                }
            }
        }
        for nd in nodes.iter_mut() {
            nd.preds = preds[nd.id].clone();
        }
        let ret_slot = unit.nodes.iter().find_map(|n| match n.returns_via {
            Some(AVal::Slot(k)) => Some(k as u32),
            _ => None,
        });
        let entry_states: Vec<Option<State>> = entries.iter().map(|e| e.as_ref().map(|e| e.state.clone())).collect();
        Lifted { nodes, entry: map[&unit.entry], edge_assigns, n_args: max_args, reprocess_count, ret_slot, entry_states, node_map: map }
    }

    /// Execute one node from its entry state.
    fn run_node(&self, unit: &Unit, nid: usize, entry: &State, hidden: &Hidden) -> (LNode, State) {
        let prog = self.prog;
        let un = &unit.nodes[nid];
        let blk = &prog.blocks[un.block];
        let mut st = entry.clone();
        st.version = st.mem.gen;
        let mut stmts: Vec<Stmt> = Vec::new();
        let mut term: Option<Term> = None;
        let mut underflow = false;
        let root = self.root && unit.entry_block == 0 && false; // underflow tolerance: Args are fine
        let _ = root;
        let seq_base = (nid as u32) << 10;
        let mut seq_ctr = 0u32;
        let next_version = |st: &mut State| {
            st.mem.tick();
            st.version = st.mem.gen;
            st.version
        };

        let succ_by_kind = |kinds: &[Edge]| -> Vec<usize> { un.succs.iter().filter(|(_, k)| kinds.contains(k)).map(|(s, _)| *s).collect() };

        if un.infeasible {
            let ln = LNode { id: nid, block: un.block, pc: blk.start, stmts: vec![], term: Term::Infeasible, preds: vec![], succs: vec![], entry_stack: vec![], exit_stack: vec![] };
            return (ln, st);
        }

        for ins in prog.block_insns(blk) {
            let o = ins.opcode;
            macro_rules! pop {
                () => {
                    st.pop(false, &mut underflow)
                };
            }
            match o {
                _ if op::is_push(o) => st.stack.push(konst(ins.imm.unwrap_or(U256::ZERO))),
                _ if op::is_dup(o) => {
                    let n = (o - 0x7f) as usize;
                    let v = st.peek(n, false, &mut underflow);
                    st.stack.push(v);
                }
                _ if op::is_swap(o) => {
                    let n = (o - 0x8f) as usize;
                    st.peek(n + 1, false, &mut underflow);
                    let l = st.stack.len();
                    st.stack.swap(l - 1, l - 1 - n);
                }
                op::POP => {
                    let v = pop!();
                    if matches!(expr::node(v), Node::CallResult(_)) {
                        stmts.push(Stmt::Drop(v));
                    }
                }
                op::JUMPDEST => {}
                op::PC => st.stack.push(konst_u64(ins.pc as u64)),
                op::MSIZE | op::GAS => st.stack.push(expr::env_seq(o)),
                op::RETURNDATASIZE => {
                    // Zero in a fresh frame until the first call.
                    st.stack.push(if st.called { expr::env(o) } else { konst(U256::ZERO) });
                }
                op::ADDRESS | op::ORIGIN | op::CALLER | op::CALLVALUE | op::CALLDATASIZE | op::CODESIZE | op::GASPRICE | op::COINBASE | op::TIMESTAMP | op::NUMBER | op::PREVRANDAO | op::GASLIMIT | op::CHAINID | op::SELFBALANCE | op::BASEFEE | op::BLOBBASEFEE => {
                    st.stack.push(expr::env(o));
                }
                op::CALLDATALOAD => {
                    let off = pop!();
                    st.stack.push(expr::calldataload(off));
                }
                op::BALANCE | op::EXTCODESIZE | op::EXTCODEHASH | op::BLOCKHASH | op::BLOBHASH => {
                    let a = pop!();
                    st.stack.push(expr::intern(Node::Op(o, vec![a])));
                }
                op::ISZERO | op::NOT => {
                    let a = pop!();
                    st.stack.push(op1(o, a));
                }
                op::ADD | op::MUL | op::SUB | op::DIV | op::SDIV | op::MOD | op::SMOD | op::EXP | op::SIGNEXTEND | op::LT | op::GT | op::SLT | op::SGT | op::EQ | op::AND | op::OR | op::XOR | op::BYTE | op::SHL | op::SHR | op::SAR => {
                    let a = pop!();
                    let b = pop!();
                    st.stack.push(op2(o, a, b));
                }
                op::ADDMOD | op::MULMOD => {
                    let a = pop!();
                    let b = pop!();
                    let c = pop!();
                    st.stack.push(op3(o, a, b, c));
                }
                op::KECCAK256 => {
                    let off = pop!();
                    let len = pop!();
                    let v = match expr::as_const(len).and_then(|l| l.as_usize()) {
                        Some(l) if l <= 8192 => match st.mem.read_region(off, l as u64, st.version) {
                            Some((words, tail)) => {
                                hidden.set.borrow_mut().extend(st.mem.consumers(off, l as u64));
                                expr::intern(Node::Keccak(words, tail))
                            }
                            None => expr::intern(Node::KeccakMem(off, len, st.mem.version_for(off, l as u64))),
                        },
                        // Symbolic length: anything from `off` on may be covered.
                        _ => expr::intern(Node::KeccakMem(off, len, st.mem.version_for(off, u64::MAX / 4))),
                    };
                    st.stack.push(v);
                }
                op::MLOAD => {
                    let off = pop!();
                    let v = st.mem.load_word(off, st.version);
                    st.stack.push(v);
                }
                op::MSTORE | op::MSTORE8 => {
                    let off = pop!();
                    let val = pop!();
                    let origin = Some((nid, stmts.len()));
                    if o == op::MSTORE {
                        st.mem.store_from(off, Some(32), MVal::Word(val), origin);
                        stmts.push(Stmt::MStore { off, val, width: 32 });
                    } else {
                        let b = op2(op::AND, val, konst_u64(0xff));
                        st.mem.store_from(off, Some(1), MVal::Byte(b), origin);
                        stmts.push(Stmt::MStore { off, val: b, width: 1 });
                    }
                    next_version(&mut st);
                }
                op::SLOAD | op::TLOAD => {
                    let key = pop!();
                    let transient = o == op::TLOAD;
                    let cached = st.storage.iter().rev().find(|(k, _, t)| *k == key && *t == transient).map(|(_, v, _)| *v);
                    let v = cached.unwrap_or_else(|| expr::intern(Node::SLoad(key, transient, st.sgen)));
                    st.stack.push(v);
                }
                op::SSTORE | op::TSTORE => {
                    let key = pop!();
                    let val = pop!();
                    let transient = o == op::TSTORE;
                    // A write to an unknown key may alias any cached key: keep only exact matches.
                    st.storage.retain(|(k, _, t)| *t != transient || *k != key);
                    if expr::is_const(key) {
                        st.storage.retain(|(k, _, t)| *t != transient || expr::is_const(*k));
                    } else {
                        st.storage.retain(|(_, _, t)| *t != transient);
                    }
                    st.storage.push((key, val, transient));
                    st.sgen += 1;
                    stmts.push(Stmt::SStore { key, val, transient });
                }
                op::JUMP => {
                    let _target = pop!();
                    if self.oracle || un.computed_cut {
                        term = Some(Term::Unresolved(_target));
                        break;
                    }
                    // Resolved by the unit: call, return, jump or switch.
                    if let Some(call) = &un.call {
                        term = Some(self.internal_call(unit, un, call, &mut st, &mut stmts, seq_base + seq_ctr, &mut underflow));
                        seq_ctr += 1;
                    } else if let Some(via) = un.returns_via {
                        // Values equal to the return address itself (solc < 0.5 leaves it for the
                        // caller to pop) are not results.
                        let ret_arg = match via {
                            AVal::Slot(k) => Some(expr::arg(k as u32)),
                            _ => None,
                        };
                        let vals: Vec<ExprId> = st.stack.iter().copied().filter(|v| Some(*v) != ret_arg).collect();
                        term = Some(Term::InternalReturn(vals));
                    } else {
                        let targets = succ_by_kind(&[Edge::Jump]);
                        term = Some(match targets.len() {
                            0 => {
                                if un.unresolved {
                                    Term::Unresolved(_target)
                                } else {
                                    Term::Infeasible
                                }
                            }
                            1 => Term::Jump(targets[0]),
                            _ => Term::Switch { target: _target, cases: targets },
                        });
                    }
                    break;
                }
                op::JUMPI => {
                    let _target = pop!();
                    let cond = pop!();
                    if self.oracle {
                        term = Some(Term::CondJump { cond, target: _target });
                        break;
                    }
                    let ts = succ_by_kind(&[Edge::True]);
                    let fs = succ_by_kind(&[Edge::False]);
                    let tnode = ts.first().copied();
                    let fnode = fs.first().copied();
                    term = Some(if ts.len() > 1 {
                        Term::Switch { target: _target, cases: ts.iter().copied().chain(fnode.into_iter()).collect() }
                    } else {
                        match (expr::as_const(cond), tnode, fnode) {
                            (Some(c), Some(t), _) if !c.is_zero() => Term::Jump(t),
                            (Some(c), None, _) if !c.is_zero() => Term::Infeasible,
                            (Some(_), _, Some(f)) => Term::Jump(f),
                            (Some(_), _, None) => Term::Infeasible,
                            (None, Some(t), Some(f)) => Term::Branch { cond, t: Some(t), f },
                            (None, None, Some(f)) => Term::Branch { cond, t: None, f },
                            (None, Some(t), None) => Term::Jump(t),
                            (None, None, None) => Term::Infeasible,
                        }
                    });
                    break;
                }
                op::CALLDATACOPY | op::RETURNDATACOPY | op::MCOPY | op::CODECOPY => {
                    let dest = pop!();
                    let src = pop!();
                    let len = pop!();
                    let l = expr::as_const(len).and_then(|v| v.as_usize()).map(|v| v as u64);
                    if o == op::MCOPY {
                        // Copy known words when possible.
                        if let Some(l) = l {
                            if let Some((words, tail)) = st.mem.read_region(src, l, st.version) {
                                let mut i = 0u64;
                                for (k, w) in words.iter().enumerate() {
                                    let is_tail = tail > 0 && k == words.len() - 1;
                                    if !is_tail {
                                        st.mem.store(expr::add_const(dest, U256::from(i)), Some(32), MVal::Word(*w));
                                        i += 32;
                                    }
                                }
                                if tail > 0 {
                                    st.mem.store(expr::add_const(dest, U256::from(i)), Some(tail as u64), MVal::Copy(o, src, None));
                                }
                            } else {
                                st.mem.store(dest, Some(l), MVal::Copy(o, src, None));
                            }
                        } else {
                            st.mem.store(dest, None, MVal::Copy(o, src, None));
                        }
                    } else if o == op::CODECOPY {
                        // Constant code regions become known words.
                        match (expr::as_const(src).and_then(|v| v.as_usize()), l) {
                            (Some(s), Some(l)) if l <= 4096 => {
                                let mut i = 0u64;
                                while i < l {
                                    let n = (l - i).min(32) as usize;
                                    let mut buf = [0u8; 32];
                                    for j in 0..n {
                                        buf[j] = prog.code.get(s + i as usize + j).copied().unwrap_or(0);
                                    }
                                    if n == 32 {
                                        st.mem.store(expr::add_const(dest, U256::from(i)), Some(32), MVal::Word(konst(U256::from_be_bytes(&buf))));
                                    } else {
                                        // Partial tail word: store as bytes.
                                        for j in 0..n {
                                            st.mem.store(expr::add_const(dest, U256::from(i + j as u64)), Some(1), MVal::Byte(konst_u64(buf[j] as u64)));
                                        }
                                    }
                                    i += 32;
                                }
                            }
                            _ => st.mem.store(dest, l, MVal::Copy(o, src, None)),
                        }
                    } else {
                        st.mem.store(dest, l, MVal::Copy(o, src, None));
                    }
                    next_version(&mut st);
                    stmts.push(Stmt::Copy { kind: o, dest, src, len, addr: None });
                }
                op::EXTCODECOPY => {
                    let addr = pop!();
                    let dest = pop!();
                    let src = pop!();
                    let len = pop!();
                    let l = expr::as_const(len).and_then(|v| v.as_usize()).map(|v| v as u64);
                    st.mem.store(dest, l, MVal::Copy(o, src, Some(addr)));
                    next_version(&mut st);
                    stmts.push(Stmt::Copy { kind: o, dest, src, len, addr: Some(addr) });
                }
                op::LOG0..=op::LOG4 => {
                    let off = pop!();
                    let len = pop!();
                    let n = (o - op::LOG0) as usize;
                    let mut topics = Vec::new();
                    for _ in 0..n {
                        topics.push(pop!());
                    }
                    let data = expr::as_const(len).and_then(|l| l.as_usize()).and_then(|l| st.mem.read_region(off, l as u64, st.version)).map(|(w, _)| w);
                    if data.is_some() {
                        hidden.set.borrow_mut().extend(st.mem.consumers(off, expr::as_const(len).unwrap().low_u64()));
                    }
                    stmts.push(Stmt::Log { off, len, topics, data });
                }
                op::CALL | op::CALLCODE | op::DELEGATECALL | op::STATICCALL => {
                    let gas = pop!();
                    let addr = pop!();
                    let value = if o == op::CALL || o == op::CALLCODE { Some(pop!()) } else { None };
                    let in_off = pop!();
                    let in_len = pop!();
                    let out_off = pop!();
                    let out_len = pop!();
                    let seq = seq_base + seq_ctr;
                    seq_ctr += 1;
                    let input = expr::as_const(in_len).and_then(|l| l.as_usize()).and_then(|l| st.mem.read_region(in_off, l as u64, st.version)).map(|(w, _)| w);
                    if input.is_some() {
                        hidden.set.borrow_mut().extend(st.mem.consumers(in_off, expr::as_const(in_len).unwrap().low_u64()));
                    }
                    let result = expr::intern(Node::CallResult(seq));
                    // Output region: known to be return data of this call.
                    let ol = expr::as_const(out_len).and_then(|v| v.as_usize()).map(|v| v as u64);
                    if ol != Some(0) {
                        st.mem.store(out_off, ol, MVal::CallOut(seq));
                    }
                    next_version(&mut st);
                    // Storage may change during an external call (reentrancy / callee effects).
                    if o != op::STATICCALL {
                        st.storage.clear();
                        st.sgen += 1;
                    }
                    stmts.push(Stmt::Call { seq, kind: o, gas, addr, value, in_off, in_len, out_off, out_len, input, result });
                    st.stack.push(result);
                    st.called = true;
                }
                op::CREATE | op::CREATE2 => {
                    let value = pop!();
                    let off = pop!();
                    let len = pop!();
                    let salt = if o == op::CREATE2 { Some(pop!()) } else { None };
                    let seq = seq_base + seq_ctr;
                    seq_ctr += 1;
                    let init = expr::as_const(len).and_then(|l| l.as_usize()).and_then(|l| st.mem.read_region(off, l as u64, st.version)).map(|(w, _)| w);
                    let result = expr::intern(Node::CreateResult(seq));
                    st.storage.clear();
                    st.sgen += 1;
                    next_version(&mut st);
                    stmts.push(Stmt::Create { seq, kind: o, value, off, len, salt, result, init });
                    st.stack.push(result);
                    st.called = true;
                }
                op::RETURN | op::REVERT => {
                    let off = pop!();
                    let len = pop!();
                    let data = expr::as_const(len).and_then(|l| l.as_usize()).and_then(|l| st.mem.read_region(off, l as u64, st.version)).map(|(w, _)| w);
                    if data.is_some() {
                        hidden.set.borrow_mut().extend(st.mem.consumers(off, expr::as_const(len).unwrap().low_u64()));
                    }
                    term = Some(if o == op::RETURN { Term::Return { off, len, data } } else { Term::Revert { off, len, data } });
                    break;
                }
                op::STOP => {
                    term = Some(Term::Stop);
                    break;
                }
                op::SELFDESTRUCT => {
                    let a = pop!();
                    term = Some(Term::SelfDestruct(a));
                    break;
                }
                op::INVALID => {
                    term = Some(Term::Invalid);
                    break;
                }
                _ => {
                    // Unknown opcode: the EVM halts with an exception.
                    term = Some(Term::Invalid);
                    break;
                }
            }
        }
        let term = term.unwrap_or_else(|| {
            let f = succ_by_kind(&[Edge::Fallthrough]);
            match f.first() {
                Some(n) => Term::Jump(*n),
                None => Term::Stop,
            }
        });
        let succs = term_succs(&term);
        let ln = LNode { id: nid, block: un.block, pc: blk.start, stmts, term, preds: vec![], succs, entry_stack: vec![], exit_stack: st.stack.clone() };
        (ln, st)
    }

    fn internal_call(&self, _unit: &Unit, un: &crate::cfg::UNode, call: &crate::cfg::CallInfo, st: &mut State, stmts: &mut Vec<Stmt>, seq: u32, underflow: &mut bool) -> Term {
        // Stack now (target already popped): position 0 is the top.
        let consumed = call.consumed as usize;
        // Materialise enough entries.
        if consumed > 0 {
            st.peek(consumed, false, underflow);
        }
        let l = st.stack.len();
        let pre: Vec<ExprId> = st.stack.clone();
        let at = |i: usize| -> ExprId {
            if i < l {
                pre[l - 1 - i]
            } else {
                expr::intern(Node::Unknown(expr::next_seq()))
            }
        };
        let ret_slot = call.ret_slot.map(|r| r as usize);
        let mut args: Vec<ExprId> = Vec::new();
        for i in (0..consumed).rev() {
            if Some(i) == ret_slot {
                continue;
            }
            args.push(at(i));
        }
        // Simple callee: substitute its effects directly.
        let summary = self.summaries.get(&call.callee);
        let subst = |e: ExprId| -> ExprId {
            let mut memo = HashMap::new();
            expr::substitute(e, &|n| if let Node::Arg(i) = n { Some(at(*i as usize)) } else { None }, &mut memo)
        };
        if let Some(sum) = summary {
            if let Some((off, len, data)) = &sum.reverts {
                // The helper always reverts: this call site is a revert.
                for (o, v) in &sum.mstores {
                    st.mem.store(subst(*o), Some(32), MVal::Word(subst(*v)));
                }
                let data = data.as_ref().map(|d| d.iter().map(|e| subst(*e)).collect());
                return Term::Revert { off: subst(*off), len: subst(*len), data };
            }
        }
        let unknown_pushed = call.pushed.iter().filter(|v| !matches!(v, AVal::Slot(_) | AVal::Const(_) | AVal::Pc(_))).count();
        let direct_returns: Option<Vec<ExprId>> = summary.filter(|s| s.returns.len() == unknown_pushed).map(|s| s.returns.iter().map(|e| subst(*e)).collect());
        let mut results = Vec::new();
        let mut j = 0u16;
        let mut pushed_vals = Vec::new();
        for v in &call.pushed {
            let e = match v {
                AVal::Slot(i) => at(*i as usize),
                AVal::Const(c) | AVal::Pc(c) => konst(*c),
                _ => {
                    let r = match &direct_returns {
                        Some(d) => d[j as usize],
                        None => expr::intern(Node::IntRet(seq, j)),
                    };
                    j += 1;
                    results.push(r);
                    r
                }
            };
            pushed_vals.push(e);
        }
        for _ in 0..consumed.min(st.stack.len()) {
            st.stack.pop();
        }
        st.stack.extend(pushed_vals);
        match summary {
            Some(sum) => {
                // Replay the callee's memory writes; storage is untouched unless it has side effects.
                for (off, val) in &sum.mstores {
                    let (o, v) = (subst(*off), subst(*val));
                    st.mem.store(o, Some(32), MVal::Word(v));
                }
                if sum.side_effects {
                    st.storage.clear();
                    st.sgen += 1;
                }
            }
            None => {
                // The callee may have written memory and storage, and may have made calls.
                st.mem.clobber();
                st.storage.clear();
                st.sgen += 1;
                st.called = true;
            }
        }
        let inlined = direct_returns.is_some();
        // A fully inlined pure helper (ABI decoder/encoder, getter) leaves no statement behind.
        let pure_inlined = inlined && summary.map_or(false, |s| s.mstores.is_empty() && !s.side_effects);
        if !pure_inlined {
            stmts.push(Stmt::Internal { seq, callee: call.callee, args, results: if inlined { vec![] } else { results } });
        }
        let conts: Vec<usize> = un.succs.iter().filter(|(_, k)| *k == Edge::Return).map(|(s, _)| *s).collect();
        match conts.len() {
            0 => Term::Infeasible,
            1 => Term::Jump(conts[0]),
            _ => Term::Switch { target: konst(U256::ZERO), cases: conts },
        }
    }
}

fn term_succs(t: &Term) -> Vec<usize> {
    match t {
        Term::Jump(n) => vec![*n],
        Term::Branch { t, f, .. } => {
            let mut v = Vec::new();
            if let Some(t) = t {
                v.push(*t);
            }
            if !v.contains(f) {
                v.push(*f);
            }
            v
        }
        Term::Switch { cases, .. } => {
            let mut v: Vec<usize> = Vec::new();
            for c in cases {
                if !v.contains(c) {
                    v.push(*c);
                }
            }
            v
        }
        _ => vec![],
    }
}

fn remap_term(t: &Term, map: &HashMap<usize, usize>) -> Term {
    let m = |x: &usize| map.get(x).copied().unwrap_or(*x);
    match t {
        Term::Jump(n) => Term::Jump(m(n)),
        Term::Branch { cond, t, f } => Term::Branch { cond: *cond, t: t.as_ref().map(m), f: m(f) },
        Term::Switch { target, cases } => Term::Switch { target: *target, cases: cases.iter().map(m).collect() },
        other => other.clone(),
    }
}

/// Merge an exit state into a successor's entry. Returns true if the entry changed.
fn merge_into(e: &mut Entry, exit: &State, node: usize, phi_ids: &mut HashMap<(usize, usize), ExprId>, next_var: &mut u32) -> bool {
    let mut changed = false;
    let el = e.state.stack.len();
    let xl = exit.stack.len();
    // Align from the top. If the exit stack is deeper, extend the entry at the bottom with phis.
    if xl > el {
        let extra = xl - el;
        let mut new_bottom = Vec::with_capacity(extra);
        let mut new_phis = Vec::with_capacity(extra);
        for i in 0..extra {
            // Position from top for these: el + (extra-1-i)... simpler: key by position from top.
            let from_top = xl - 1 - i;
            let var = *phi_ids.entry((node, from_top)).or_insert_with(|| {
                *next_var += 1;
                expr::var(((node as u32) << 10) | (*next_var & 0x3ff))
            });
            new_bottom.push(var);
            new_phis.push(true);
        }
        // new_bottom currently ordered deepest-first? i=0 is the deepest (from_top largest). Yes.
        let mut stack = new_bottom;
        stack.extend(e.state.stack.iter().copied());
        let mut phis = new_phis;
        phis.extend(e.phis.iter().copied());
        e.state.stack = stack;
        e.phis = phis;
        changed = true;
    }
    let el = e.state.stack.len();
    for k in 0..el {
        let from_top = el - 1 - k;
        let exit_val = if from_top < xl { Some(exit.stack[xl - 1 - from_top]) } else { None };
        if e.phis[k] {
            continue;
        }
        if exit_val != Some(e.state.stack[k]) {
            let var = *phi_ids.entry((node, from_top)).or_insert_with(|| {
                *next_var += 1;
                expr::var(((node as u32) << 10) | (*next_var & 0x3ff))
            });
            e.state.stack[k] = var;
            e.phis[k] = true;
            changed = true;
        }
    }
    if e.state.mem.intersect(&exit.mem) {
        changed = true;
    }
    let before = e.state.storage.len();
    e.state.storage.retain(|w| exit.storage.contains(w));
    if e.state.storage.len() != before {
        changed = true;
    }
    if exit.args_used > e.state.args_used {
        e.state.args_used = exit.args_used;
    }
    if exit.sgen != e.state.sgen {
        e.state.sgen = e.state.sgen.max(exit.sgen) + 1;
        changed = true;
    }
    if exit.called && !e.state.called {
        e.state.called = true;
        changed = true;
    }
    changed
}

/// All expressions referenced by a node's statements and terminator (for analyses).
pub fn node_exprs(n: &LNode) -> Vec<ExprId> {
    let mut v = Vec::new();
    for s in &n.stmts {
        match s {
            Stmt::Assign { var, value } => {
                v.push(*var);
                v.push(*value);
            }
            Stmt::MStore { off, val, .. } => {
                v.push(*off);
                v.push(*val);
            }
            Stmt::SStore { key, val, .. } => {
                v.push(*key);
                v.push(*val);
            }
            Stmt::Log { off, len, topics, data } => {
                v.push(*off);
                v.push(*len);
                v.extend(topics.iter().copied());
                if let Some(d) = data {
                    v.extend(d.iter().copied());
                }
            }
            Stmt::Call { gas, addr, value, in_off, in_len, out_off, out_len, input, .. } => {
                v.push(*gas);
                v.push(*addr);
                if let Some(x) = value {
                    v.push(*x);
                }
                v.extend([*in_off, *in_len, *out_off, *out_len]);
                if let Some(d) = input {
                    v.extend(d.iter().copied());
                }
            }
            Stmt::Create { value, off, len, salt, init, .. } => {
                v.extend([*value, *off, *len]);
                if let Some(s) = salt {
                    v.push(*s);
                }
                if let Some(d) = init {
                    v.extend(d.iter().copied());
                }
            }
            Stmt::Copy { dest, src, len, addr, .. } => {
                v.extend([*dest, *src, *len]);
                if let Some(a) = addr {
                    v.push(*a);
                }
            }
            Stmt::Internal { args, .. } => v.extend(args.iter().copied()),
            Stmt::Drop(e) => v.push(*e),
        }
    }
    match &n.term {
        Term::Branch { cond, .. } => v.push(*cond),
        Term::Switch { target, .. } => v.push(*target),
        Term::Return { off, len, data } | Term::Revert { off, len, data } => {
            v.push(*off);
            v.push(*len);
            if let Some(d) = data {
                v.extend(d.iter().copied());
            }
        }
        Term::SelfDestruct(a) => v.push(*a),
        Term::InternalReturn(vals) => v.extend(vals.iter().copied()),
        Term::Unresolved(t) => v.push(*t),
        Term::CondJump { cond, target } => {
            v.push(*cond);
            v.push(*target);
        }
        _ => {}
    }
    v
}

/// Bits a computed jump target may have set, from the shape of its expression (`x & 0x3ff0`,
/// `y << 6`, `byte(..) * 64`): the set of JUMPDESTs compatible with that pattern is the set of
/// possible targets. `None` when the expression gives no usable constraint.
pub fn jump_target_bits(e: ExprId) -> Option<U256> {
    match expr::node(e) {
        Node::Const(c) => Some(c),
        Node::Op(op::AND, v) => {
            let (a, b) = (jump_target_bits(v[0]), jump_target_bits(v[1]));
            match (a, b) {
                (Some(x), Some(y)) => Some(x & y),
                (Some(x), None) | (None, Some(x)) => Some(x),
                _ => None,
            }
        }
        Node::Op(op::OR, v) | Node::Op(op::XOR, v) | Node::Op(op::ADD, v) => {
            let a = jump_target_bits(v[0])?;
            let b = jump_target_bits(v[1])?;
            // ADD may carry; be conservative by allowing all bits up to the sum's width.
            if matches!(expr::node(e), Node::Op(op::ADD, _)) {
                let bits = a.bits().max(b.bits()) + 1;
                Some(expr::mask_bits(bits))
            } else {
                Some(a | b)
            }
        }
        Node::Op(op::SHL, v) => {
            let k = expr::as_const(v[0])?;
            if k >= U256::from_u64(256) {
                return Some(U256::ZERO);
            }
            Some(jump_target_bits(v[1])?.shl(k.low_u64() as u32))
        }
        Node::Op(op::MUL, v) => {
            let (x, c) = if let Some(c) = expr::as_const(v[1]) { (v[0], c) } else { (v[1], expr::as_const(v[0])?) };
            if !c.is_power_of_two() {
                return None;
            }
            Some(jump_target_bits(x)?.shl(c.trailing_zeros()))
        }
        Node::Op(op::SHR, v) => {
            let k = expr::as_const(v[0])?;
            if k >= U256::from_u64(256) {
                return Some(U256::ZERO);
            }
            Some(jump_target_bits(v[1])?.shr(k.low_u64() as u32))
        }
        Node::Op(op::BYTE, _) => Some(U256::from_u64(0xff)),
        Node::Op(op::DIV, v) => {
            let c = expr::as_const(v[1])?;
            if !c.is_power_of_two() {
                return None;
            }
            Some(jump_target_bits(v[0])?.shr(c.trailing_zeros()))
        }
        _ => {
            let b = expr::value_bits(e);
            if b < 256 {
                Some(expr::mask_bits(b))
            } else {
                Some(U256::MAX)
            }
        }
    }
}

/// Leaves of an expression that are not constants (unknown inputs).
pub fn unknown_leaves(e: ExprId) -> Vec<ExprId> {
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 10_000 {
            continue;
        }
        match expr::node(x) {
            Node::Const(_) => {}
            Node::Op(_, _) => stack.extend(expr::children(x)),
            _ => out.push(x),
        }
    }
    out
}

/// Candidate code addresses for a computed jump target: when the expression has a single
/// unknown input, substitute a range of small values, powers of two and masks for it and keep the
/// results that are jump destinations (exact for shift-selected targets and calldata-byte
/// dispatchers); otherwise, or additionally, every destination compatible with the bit pattern.
pub fn jump_candidates(e: ExprId, jumpdests: &HashSet<usize>, code_len: usize) -> Vec<usize> {
    let mut out: HashSet<usize> = HashSet::new();
    let leaves = unknown_leaves(e);
    // A bare stack input (`Arg`) is a return address or a caller-provided pointer, never a
    // dispatcher index: only calldata/memory/environment-derived inputs are enumerated.
    if leaves.len() == 1 && !matches!(expr::node(leaves[0]), Node::Arg(_) | Node::Var(_) | Node::IntRet(..) | Node::Unknown(_)) {
        let leaf = leaves[0];
        let mut samples: Vec<U256> = (0..=1024u64).map(U256::from_u64).collect();
        for k in 0..256u32 {
            samples.push(U256::ONE.shl(k));
            samples.push(expr::mask_bits(k));
        }
        samples.push(U256::MAX);
        for v in samples {
            let mut memo = HashMap::new();
            let r = expr::substitute(e, &|n| if std::ptr::eq(n, n) && expr::intern(n.clone()) == leaf { Some(konst(v)) } else { None }, &mut memo);
            if let Some(c) = expr::as_const(r) {
                if let Some(pc) = c.as_usize() {
                    if pc < code_len && jumpdests.contains(&pc) {
                        out.insert(pc);
                    }
                }
            }
        }
    }
    let bare_stack = matches!(expr::node(e), Node::Arg(_) | Node::Var(_));
    if let (Some(bits), false) = (jump_target_bits(e), bare_stack) {
        if bits != U256::MAX {
            for &pc in jumpdests {
                if pc < code_len && (U256::from(pc) & !bits).is_zero() {
                    out.insert(pc);
                }
            }
        }
    }
    let mut v: Vec<usize> = out.into_iter().collect();
    v.sort_unstable();
    v
}

/// Reachable set from the entry.
pub fn reachable(l: &Lifted) -> HashSet<usize> {
    let mut seen = HashSet::new();
    let mut stack = vec![l.entry];
    while let Some(n) = stack.pop() {
        if !seen.insert(n) {
            continue;
        }
        for s in &l.nodes[n].succs {
            stack.push(*s);
        }
    }
    seen
}
