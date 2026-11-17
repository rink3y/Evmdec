use crate::cfg::{AVal, Edge, Program, Unit};
use crate::expr::{self, kind, konst, konst_u64, op1, op2, op3, ExprId, Node};
use crate::opcode as op;
use crate::u256::U256;
use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    Assign {
        var: ExprId,
        value: ExprId,
    },
    MStore {
        off: ExprId,
        val: ExprId,
        width: u8,
        gen: u32,
    },
    SStore {
        key: ExprId,
        val: ExprId,
        transient: bool,
        gen: u32,
    },
    Log {
        off: ExprId,
        len: ExprId,
        topics: Vec<ExprId>,
        data: Option<Vec<ExprId>>,
    },
    Call {
        seq: u32,
        kind: u8,
        gas: ExprId,
        addr: ExprId,
        value: Option<ExprId>,
        in_off: ExprId,
        in_len: ExprId,
        out_off: ExprId,
        out_len: ExprId,
        input: Option<Vec<ExprId>>,
        input_head: Vec<ExprId>,
        layout: Option<Vec<(ExprId, u8)>>,
        args: Option<Vec<Arg>>,
        result: ExprId,
        gen: Option<u32>,
    },
    Create {
        seq: u32,
        kind: u8,
        value: ExprId,
        off: ExprId,
        len: ExprId,
        salt: Option<ExprId>,
        result: ExprId,
        init: Option<Vec<ExprId>>,
        gen: u32,
    },
    Copy {
        kind: u8,
        dest: ExprId,
        src: ExprId,
        len: ExprId,
        addr: Option<ExprId>,
        gen: u32,
    },
    Internal {
        seq: u32,
        callee: usize,
        args: Vec<ExprId>,
        results: Vec<ExprId>,
        gen: Option<u32>,
    },
    Drop(ExprId),
    Require {
        cond: ExprId,
        data: Option<Vec<ExprId>>,
        invalid: bool,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Arg {
    Word(ExprId),
    Bytes(u64, Vec<ExprId>),
    List(Vec<ExprId>),
    Copied { kind: u8, src: ExprId, len: ExprId },
}

impl Arg {
    #[must_use]
    pub fn exprs(&self) -> Vec<ExprId> {
        match self {
            Arg::Word(e) => vec![*e],
            Arg::Bytes(_, words) | Arg::List(words) => words.clone(),
            Arg::Copied { src, len, .. } => vec![*src, *len],
        }
    }

    #[must_use]
    pub fn map(&self, f: &dyn Fn(ExprId) -> ExprId) -> Arg {
        let all = |words: &[ExprId]| words.iter().map(|e| f(*e)).collect();
        match self {
            Arg::Word(e) => Arg::Word(f(*e)),
            Arg::Bytes(len, words) => Arg::Bytes(*len, all(words)),
            Arg::List(words) => Arg::List(all(words)),
            Arg::Copied { kind, src, len } => Arg::Copied {
                kind: *kind,
                src: f(*src),
                len: f(*len),
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Jump(usize),
    Branch {
        cond: ExprId,
        t: Option<usize>,
        f: usize,
    },
    Switch {
        target: ExprId,
        cases: Vec<usize>,
    },
    Return {
        off: ExprId,
        len: ExprId,
        data: Option<Vec<ExprId>>,
    },
    ReturnDyn {
        ptr: ExprId,
    },
    Revert {
        off: ExprId,
        len: ExprId,
        data: Option<Vec<ExprId>>,
    },
    Stop,
    Invalid,
    SelfDestruct(ExprId),
    InternalReturn(Vec<ExprId>),
    Unresolved(ExprId),
    CondJump {
        cond: ExprId,
        target: ExprId,
    },
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
    pub entry_stack: Vec<ExprId>,
    pub exit_stack: Vec<ExprId>,
    pub sgen: u32,
    pub mgen: u32,
}

#[derive(Clone, Debug)]
pub struct Lifted {
    pub nodes: Vec<LNode>,
    pub entry: usize,
    pub edge_assigns: HashMap<(usize, usize), Vec<(ExprId, ExprId)>>,
    pub n_args: usize,
    pub reprocess_count: usize,
    pub ret_slot: Option<u32>,
    pub(crate) entry_states: Vec<Option<State>>,
    pub node_map: HashMap<usize, usize>,
    pub entry_loads: MemoryReads,
    pub mem_writes: MemoryWrites,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum MVal {
    Word(ExprId),
    Byte(ExprId),
    Copy(u8, ExprId, Option<ExprId>),
    CallOut(u32, u32),
    Zero,
    Unknown,
}

type Origin = (usize, usize);
type Parts = Vec<(usize, Arg)>;

#[derive(Clone, Debug, PartialEq, Eq)]
struct MemWrite {
    base: Option<ExprId>,
    off: u64,
    len: Option<u64>,
    val: MVal,
    origin: Option<(usize, usize)>,
    gen: u32,
    span: Option<ExprId>,
    most: Option<u64>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MemoryReads {
    ranges: BTreeSet<(u64, u64)>,
    open_from: Option<u64>,
    indexed: BTreeSet<u64>,
}

impl MemoryReads {
    #[must_use]
    pub fn everything() -> MemoryReads {
        MemoryReads {
            open_from: Some(0),
            ..MemoryReads::default()
        }
    }

    #[must_use]
    pub fn with_indices(mut self, checked: bool) -> MemoryReads {
        let lowest = std::mem::take(&mut self.indexed).into_iter().next();
        if let (Some(base), false) = (lowest, checked) {
            self.open_from = Some(self.open_from.map_or(base, |o| o.min(base)));
        }
        self
    }

    pub fn add(&mut self, other: &MemoryReads) -> bool {
        let before = (self.ranges.len(), self.open_from);
        self.ranges.extend(other.ranges.iter().copied());
        self.open_from = match (self.open_from, other.open_from) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        };
        before != (self.ranges.len(), self.open_from)
    }

    fn open(&mut self, from: ExprId) {
        let (rest, at) = expr::split_offset(from);
        let wraps = rest.is_some_and(|r| {
            expr::contains(r, &|n| match n {
                Node::Op(op::SUB | op::NOT | op::SIGNEXTEND | op::SDIV | op::SMOD, _) => true,
                Node::Const(c) => c.bits() > 64,
                _ => false,
            })
        });
        let base = match at.fits_u64() && !wraps {
            true => at.low_u64(),
            false => 0,
        };
        self.open_from = Some(self.open_from.map_or(base, |o| o.min(base)));
    }

    fn range(&mut self, off: ExprId, len: ExprId) {
        match (expr::as_const(off), expr::as_const(len)) {
            (_, Some(l)) if l.is_zero() => {}
            (Some(o), Some(l)) if o.fits_u64() && l.fits_u64() => {
                let start = o.low_u64();
                self.ranges
                    .insert((start, start.saturating_add(l.low_u64())));
            }
            _ => self.open(off),
        }
    }

    fn note(&mut self, off: ExprId, n: u64, written: &BTreeSet<(u64, u64)>) {
        match expr::as_const(off).filter(|c| c.fits_u64()) {
            Some(c) => {
                let (lo, hi) = (c.low_u64(), c.low_u64().saturating_add(n));
                if !covers(written, lo, hi) {
                    self.ranges.insert((lo, hi));
                }
            }
            None => {
                let (rest, at) = expr::split_offset(off);
                let scaled = rest.is_some_and(|r| match expr::node(r) {
                    Node::Op(op::MUL, v) => v
                        .iter()
                        .any(|x| expr::as_const(*x) == Some(U256::from_u64(32))),
                    Node::Op(op::SHL, v) => expr::as_const(v[0]) == Some(U256::from_u64(5)),
                    _ => false,
                });
                let base = at.fits_u64().then(|| at.low_u64());
                match base.filter(|b| scaled && written.iter().any(|(lo, _)| lo == b)) {
                    Some(b) => {
                        self.indexed.insert(b);
                    }
                    None => self.open(off),
                }
            }
        }
    }

    pub fn add_outside(&mut self, other: &MemoryReads, written: &BTreeSet<(u64, u64)>) -> bool {
        let before = (self.ranges.len(), self.open_from);
        for (lo, hi) in &other.ranges {
            if !covers(written, *lo, *hi) {
                self.ranges.insert((*lo, *hi));
            }
        }
        if let Some(from) = other.open_from {
            self.open_from = Some(self.open_from.map_or(from, |o| o.min(from)));
        }
        before != (self.ranges.len(), self.open_from)
    }

    pub fn range_outside(&mut self, off: ExprId, len: ExprId, written: &BTreeSet<(u64, u64)>) {
        let mut own = MemoryReads::default();
        own.range(off, len);
        self.add_outside(&own, written);
    }

    pub fn exprs(&mut self, roots: impl IntoIterator<Item = ExprId>) {
        let mut seen: HashSet<ExprId> = HashSet::new();
        let mut pending: Vec<ExprId> = roots.into_iter().collect();
        while let Some(e) = pending.pop() {
            if !seen.insert(e) {
                continue;
            }
            if seen.len() > 50_000 {
                self.open_from = Some(0);
                return;
            }
            match expr::node(e) {
                Node::MLoad(at, _) => self.range(at, expr::konst_u64(32)),
                Node::KeccakMem(off, len, _) => self.range(off, len),
                Node::CopiedWord(op::MCOPY, src, _) => self.open(src),
                _ => {}
            }
            pending.extend(expr::children(e));
        }
    }

    pub fn stmt<'a>(&mut self, s: &Stmt, callee: &impl Fn(usize) -> Option<&'a MemoryReads>) {
        match s {
            Stmt::Call {
                in_off,
                in_len,
                input: None,
                ..
            } => self.range(*in_off, *in_len),
            Stmt::Log {
                off,
                len,
                data: None,
                ..
            }
            | Stmt::Create {
                off,
                len,
                init: None,
                ..
            } => self.range(*off, *len),
            Stmt::Copy {
                kind: op::MCOPY,
                src,
                len,
                ..
            } => self.range(*src, *len),
            Stmt::Internal { callee: pc, .. } => match callee(*pc) {
                Some(reads) => {
                    self.add(reads);
                }
                None => self.open_from = Some(0),
            },
            _ => {}
        }
        self.exprs(stmt_exprs(s));
    }

    pub fn term(&mut self, t: &Term, returns_to_reader: bool) {
        match t {
            Term::Return {
                off,
                len,
                data: None,
            }
            | Term::Revert {
                off,
                len,
                data: None,
            } => self.range(*off, *len),
            Term::ReturnDyn { ptr } => self.open(*ptr),
            Term::InternalReturn(_) if returns_to_reader => self.open_from = Some(0),
            Term::Unresolved(_) | Term::Switch { .. } => self.open_from = Some(0),
            _ => {}
        }
        self.exprs(term_exprs(t));
    }

    #[must_use]
    pub fn reads(&self, addr: u64, len: u64) -> bool {
        let end = addr.saturating_add(len);
        self.open_from.is_some_and(|from| end > from)
            || self.ranges.iter().any(|(lo, hi)| addr < *hi && end > *lo)
    }
}

impl Lifted {
    #[must_use]
    pub fn entry_reads<'a>(
        &self,
        checked_indices: bool,
        callee: &impl Fn(usize) -> Option<&'a MemoryReads>,
    ) -> MemoryReads {
        let mut reads = self.entry_loads.clone().with_indices(checked_indices);
        let mut written_in: Vec<Option<BTreeSet<(u64, u64)>>> = vec![None; self.nodes.len()];
        written_in[self.entry] = Some(BTreeSet::new());
        let mut work = vec![self.entry];
        while let Some(n) = work.pop() {
            let Some(mut written) = written_in[n].clone() else {
                continue;
            };
            let nd = &self.nodes[n];
            let mut copied: Vec<(ExprId, ExprId)> = Vec::new();
            for s in &nd.stmts {
                match s {
                    Stmt::Call {
                        in_off: off,
                        in_len: len,
                        input: None,
                        ..
                    }
                    | Stmt::Log {
                        off,
                        len,
                        data: None,
                        ..
                    }
                    | Stmt::Create {
                        off,
                        len,
                        init: None,
                        ..
                    }
                    | Stmt::Copy {
                        kind: op::MCOPY,
                        src: off,
                        len,
                        ..
                    } if !copied.contains(&(*off, *len)) => {
                        reads.range_outside(*off, *len, &written);
                    }
                    Stmt::Internal { callee: pc, .. } => match callee(*pc) {
                        Some(theirs) => {
                            reads.add_outside(theirs, &written);
                        }
                        None => return MemoryReads::everything(),
                    },
                    _ => {}
                }
                match s {
                    Stmt::MStore { off, width, .. } => {
                        if let Some(c) = expr::as_const(*off).filter(|c| c.fits_u64()) {
                            let lo = c.low_u64();
                            written.insert((lo, lo.saturating_add(u64::from(*width))));
                        }
                    }
                    Stmt::Copy { dest, len, .. } => {
                        let fixed = expr::as_const(*dest)
                            .filter(|c| c.fits_u64())
                            .zip(expr::as_const(*len).filter(|c| c.fits_u64()));
                        match fixed {
                            Some((d, l)) => {
                                let lo = d.low_u64();
                                written.insert((lo, lo.saturating_add(l.low_u64())));
                            }
                            None => copied.push((*dest, *len)),
                        }
                    }
                    _ => {}
                }
            }
            match &nd.term {
                Term::Return {
                    off,
                    len,
                    data: None,
                }
                | Term::Revert {
                    off,
                    len,
                    data: None,
                } if !copied.contains(&(*off, *len)) => reads.range_outside(*off, *len, &written),
                Term::ReturnDyn { ptr } => reads.open(*ptr),
                Term::Unresolved(_) | Term::Switch { .. } => return MemoryReads::everything(),
                _ => {}
            }
            for succ in &nd.succs {
                let merged = match &written_in[*succ] {
                    None => written.clone(),
                    Some(theirs) => theirs.intersection(&written).copied().collect(),
                };
                if written_in[*succ].as_ref() != Some(&merged) {
                    written_in[*succ] = Some(merged);
                    work.push(*succ);
                }
            }
        }
        reads
    }
}

#[must_use]
pub fn covers(written: &BTreeSet<(u64, u64)>, lo: u64, hi: u64) -> bool {
    let mut at = lo;
    while at < hi {
        let next = written
            .iter()
            .filter(|(a, b)| *a <= at && *b > at)
            .map(|(_, b)| *b)
            .max();
        match next {
            Some(b) => at = b,
            None => return false,
        }
    }
    true
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MemoryWrites {
    ranges: BTreeSet<(u64, u64)>,
    anywhere: bool,
}

impl MemoryWrites {
    #[must_use]
    pub fn leaves_free_pointer(&self) -> bool {
        let end = FREE_POINTER + 32;
        !self
            .ranges
            .iter()
            .any(|(lo, hi)| *lo < end && *hi > FREE_POINTER)
    }

    #[must_use]
    pub fn fixed(&self) -> Option<Vec<(u64, u64)>> {
        if self.anywhere {
            return None;
        }
        let mut merged: Vec<(u64, u64)> = Vec::new();
        for (lo, hi) in &self.ranges {
            match merged.last_mut() {
                Some(last) if *lo <= last.1 => last.1 = last.1.max(*hi),
                _ => merged.push((*lo, *hi)),
            }
        }
        Some(merged)
    }
}

#[derive(Clone, Debug)]
struct Mem {
    writes: Vec<MemWrite>,
    fresh: bool,
    // An unknown read carries the generation of the last write that may alias it.
    // The oracle relies on this.
    gen: u32,
    clobber_gen: u32,
    written: BTreeSet<(u64, u64)>,
    entry_loads: Rc<RefCell<MemoryReads>>,
    touched: Rc<RefCell<MemoryWrites>>,
    pointer_named: bool,
    // Writes made before this version may be missing from the list.
    wiped: u32,
    sized: Vec<(u32, u64)>,
    capped: Vec<(ExprId, u32)>,
    below: Vec<(ExprId, u64)>,
}

const BIG: u64 = 1 << 40;

// Stands where a byte's place in its word goes, for a byte no value is known for.
const NOT_KNOWN: u64 = u64::MAX;

const MERGED_RETURN: u32 = 1 << 31;

pub const SEQ_BITS: u32 = 14;

// Must be stable across the rounds a node is lifted in, and never zero.
// A node or an index too large for its bits gets the stamp of an unknown call,
// which is never taken to be the same as another.
pub fn call_stamp(node: usize, index: usize) -> u32 {
    let nodes = (1usize << (31 - SEQ_BITS)) - 1;
    if node >= nodes || index >= 1 << SEQ_BITS {
        return MERGED_RETURN | node as u32;
    }
    ((node as u32) << SEQ_BITS | index as u32) + 1
}

// Past this the oldest writes are forgotten.
// With them goes the knowledge that untouched memory is zero.
const MAX_TRACKED_WRITES: usize = 256;

pub const FREE_POINTER: u64 = 0x40;

fn norm_offset(e: ExprId) -> (Option<ExprId>, u64) {
    let (b, d) = expr::split_offset(e);
    if d.fits_u64() && d.low_u64() < BIG {
        (b, d.low_u64())
    } else {
        (Some(e), 0)
    }
}

fn wild_base(b: ExprId) -> bool {
    expr::holds(b, !(kind::CONST | kind::OP | kind::MLOAD))
}

const FIRST_BLOCK: u64 = 0x80;

/* An address that cannot reach the first allocated block is no pointer into one. It picks
one of the words at fixed places below, so it is held to the range it can take. */
fn scratch_index(base: ExprId) -> Option<u64> {
    let most = expr::may_bits(base);
    (most.fits_u64() && most.low_u64() < FIRST_BLOCK).then(|| most.low_u64())
}

fn rounded_down(sum: ExprId, low: ExprId) -> Option<Vec<ExprId>> {
    let Node::Op(op::AND, m) = expr::node(low) else {
        return None;
    };
    let [a, b] = m[..] else {
        return None;
    };
    let term = match (expr::is_const(a), expr::is_const(b)) {
        (true, false) => b,
        (false, true) => a,
        _ => return None,
    };
    let mut terms = Vec::new();
    let mut stack = vec![sum];
    while let Some(x) = stack.pop() {
        match expr::node(x) {
            Node::Op(op::ADD, v) => stack.extend(v),
            _ => terms.push(x),
        }
    }
    let at = terms.iter().position(|t| *t == term)?;
    terms.remove(at);
    Some(terms)
}

/* Sound only because an unknown pointer is unsigned and memory never wraps.
So p + k lies at or above k. It also never points into the scratch area below 0x80.
Code that keeps no free pointer has no blocks of its own to point into. There a computed
address is an index into the words at fixed places, so it counts as unknown. */
fn may_alias(
    wb: Option<ExprId>,
    woff: u64,
    wlen: Option<u64>,
    rb: Option<ExprId>,
    roff: u64,
    rlen: u64,
    allocates: bool,
) -> bool {
    let unknown = |b: ExprId| !allocates || wild_base(b);
    let w_wild = wb.is_some_and(unknown);
    let r_wild = rb.is_some_and(unknown);
    let above = |wild: ExprId, fixed: ExprId| -> Option<u64> {
        let mut terms = Vec::new();
        let mut stack = vec![wild];
        while let Some(x) = stack.pop() {
            match expr::node(x) {
                Node::Op(o, v) if o == op::ADD => {
                    stack.push(v[0]);
                    stack.push(v[1]);
                }
                // A sum less the low bits of one of its terms is still at or above the rest.
                Node::Op(o, v) if o == op::SUB => match rounded_down(v[0], v[1]) {
                    Some(rest) => stack.extend(rest),
                    None => terms.push(x),
                },
                _ => terms.push(x),
            }
        }
        let same = |a: ExprId, b: ExprId| {
            a == b
                || matches!((expr::node(a), expr::node(b)), (Node::MLoad(x, _), Node::MLoad(y, _)) if x == y)
        };
        if !terms.iter().any(|t| same(*t, fixed)) {
            return None;
        }
        let mut k: u64 = 0;
        let mut seen_fixed = false;
        for t in terms {
            if !seen_fixed && same(t, fixed) {
                seen_fixed = true;
                continue;
            }
            if let Some(c) = expr::as_const(t) {
                if !c.fits_u64() || c.low_u64() >= BIG {
                    return None;
                }
                k = k.saturating_add(c.low_u64());
            } else if !unknown(t) {
                return None;
            }
        }
        Some(k)
    };
    if w_wild {
        let Some(rbase) = rb else {
            return (!allocates || roff >= 0x80) && roff + rlen > woff;
        };
        if let (false, Some(wbase)) = (r_wild, wb) {
            if let Some(k) = above(wbase, rbase) {
                return roff + rlen > woff + k;
            }
        }
        return true;
    }
    if r_wild {
        let Some(wbase) = wb else {
            return (!allocates || woff >= 0x80) && wlen.is_none_or(|l| woff + l > roff);
        };
        if let Some(rbase) = rb {
            if let Some(k) = above(rbase, wbase) {
                return wlen.is_none_or(|l| woff + l > roff + k);
            }
        }
        return true;
    }
    false
}

impl Mem {
    fn new(fresh: bool, pointer_named: bool) -> Mem {
        Mem {
            pointer_named,
            wiped: 0,
            sized: Vec::new(),
            capped: Vec::new(),
            below: Vec::new(),
            writes: Vec::new(),
            fresh,
            gen: 0,
            clobber_gen: 0,
            written: BTreeSet::new(),
            entry_loads: Rc::default(),
            touched: Rc::default(),
        }
    }

    fn note_load(&self, off: ExprId, n: u64) {
        self.entry_loads.borrow_mut().note(off, n, &self.written);
    }

    fn note_range(&self, off: ExprId, len: ExprId) {
        self.entry_loads
            .borrow_mut()
            .range_outside(off, len, &self.written);
    }

    fn tick(&mut self) {
        self.gen += 1;
    }

    fn version_for(&self, off: ExprId, n: u64) -> u32 {
        let (base, d) = norm_offset(off);
        let mut v = self.clobber_gen;
        for w in &self.writes {
            if w.base != base {
                // A write through another pointer may land on the same bytes.
                // Without the new version two reads around it would count as equal.
                if self.reaches(w, base, d, n) {
                    v = v.max(w.gen);
                }
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

    /* Where the code keeps its variables at fixed places, a write through a computed address
    may have reached one of them. What a computed address read is taken to be apart from
    the places written after it, as two blocks the code allocated are. Only a write
    through that same address counts there. */
    fn written_since(&self, off: ExprId, n: u64, version: u32) -> bool {
        let (base, d) = norm_offset(off);
        let index = |b: Option<ExprId>| b.and_then(scratch_index).is_some();
        let over = |w: &MemWrite| match w.base == base {
            true => d.saturating_add(n) > w.off && w.len.is_none_or(|l| d < w.off + l),
            false => {
                let fixed = !self.pointer_named && base.is_none();
                (fixed || index(w.base) || index(base)) && self.reaches(w, base, d, n)
            }
        };
        version < self.wiped || self.writes.iter().any(|w| w.gen > version && over(w))
    }

    /* A stored value prints the memory it read by where that memory is. Once such a place
    is written again the value would print as the new word, so it is no longer handed to a
    read of the place it was stored at. A read of the free pointer has a name of its own. */
    fn current(&self, value: ExprId) -> bool {
        let reads = kind::MLOAD | kind::KECCAK_MEM | kind::COPIED_WORD;
        let mut seen: HashSet<ExprId> = HashSet::new();
        let mut pending = vec![value];
        while let Some(e) = pending.pop() {
            if !expr::holds(e, reads) || !seen.insert(e) {
                continue;
            }
            if seen.len() > 4096 {
                return false;
            }
            // Of a copied word cut down to its first bytes only those bytes have to stand.
            let cut = match expr::node(e) {
                Node::Op(op::SHR, v) => match (expr::as_const(v[0]), expr::node(v[1])) {
                    (Some(by), Node::CopiedWord(op::MCOPY, at, version)) if by.fits_u64() => {
                        let kept = 32u64.checked_sub(by.low_u64().div_ceil(8));
                        kept.map(|bytes| (at, bytes, version))
                    }
                    _ => None,
                },
                _ => None,
            };
            if let Some((at, bytes, version)) = cut {
                if self.written_since(at, bytes, version) {
                    return false;
                }
                pending.push(at);
                continue;
            }
            let unchanged = match expr::node(e) {
                Node::MLoad(at, _) if self.pointer_named && at == konst_u64(FREE_POINTER) => true,
                Node::MLoad(at, version) | Node::CopiedWord(op::MCOPY, at, version) => {
                    !self.written_since(at, 32, version)
                }
                Node::KeccakMem(off, len, version) => {
                    let len = expr::as_const(len).and_then(|l| l.as_usize());
                    let len = len
                        .filter(|l| *l <= 8192)
                        .map_or(u64::MAX / 4, |l| l as u64);
                    !self.written_since(off, len, version)
                }
                _ => true,
            };
            if !unchanged {
                return false;
            }
            pending.extend(expr::children(e));
        }
        true
    }

    fn most(&self, base: ExprId) -> Option<u64> {
        let tested = |e: ExprId| {
            let known = self.below.iter().filter(|(x, _)| *x == e);
            known.map(|(_, n)| *n).min().map(|n| n - 1)
        };
        let fixed = |e: ExprId| {
            expr::as_const(e)
                .filter(|c| c.fits_u64())
                .map(|c| c.low_u64())
        };
        tested(base).or_else(|| match expr::node(base) {
            Node::Op(op::MUL, v) => [(v[0], v[1]), (v[1], v[0])]
                .into_iter()
                .find_map(|(i, by)| tested(i)?.checked_mul(fixed(by)?)),
            Node::Op(op::SHL, v) => {
                let by = fixed(v[0]).filter(|by| *by < 32)?;
                Some(tested(v[1])? << by)
            }
            _ => None,
        })
    }

    // An address made from an index the code tested stays within what the index can reach.
    fn reaches(&self, w: &MemWrite, base: Option<ExprId>, d: u64, n: u64) -> bool {
        if self.pointer_named && (w.base.is_some() || base.is_some()) {
            let (terms, fixed) = base.map(summed).unwrap_or_default();
            let (read, written) = ((terms, fixed.wrapping_add(U256::from(d))), place(w));
            let past = ahead(&written, &read).is_some_and(|gap| gap >= n);
            let short = w.len.zip(ahead(&read, &written));
            if past || short.is_some_and(|(len, gap)| gap >= len) {
                return false;
            }
        }
        let (w_index, r_index) = (w.base.and_then(scratch_index), base.and_then(scratch_index));
        if w_index.is_some() || r_index.is_some() {
            let unknown = |b: ExprId| !self.pointer_named || wild_base(b);
            let span = |b: Option<ExprId>, index: Option<u64>, off: u64, len: Option<u64>| {
                let reach = match (b, index) {
                    (None, _) => Some(0),
                    (Some(_), most) => most,
                };
                reach.map(|most| (off, len.map(|l| off.saturating_add(most).saturating_add(l))))
            };
            let write = span(w.base, w_index, w.off, w.len);
            let read = span(base, r_index, d, Some(n));
            return match (write, read) {
                (Some((ws, we)), Some((rs, re))) => {
                    we.is_none_or(|end| rs < end) && re.is_none_or(|end| ws < end)
                }
                (Some((_, end)), None) => {
                    base.is_some_and(unknown) || end.is_none_or(|end| end > FIRST_BLOCK)
                }
                (None, Some((_, end))) => {
                    w.base.is_some_and(unknown) || end.is_none_or(|end| end > FIRST_BLOCK)
                }
                (None, None) => true,
            };
        }
        if !may_alias(w.base, w.off, w.len, base, d, n, self.pointer_named) {
            return false;
        }
        let write_end = match w.base {
            None => w.len.map(|l| w.off.saturating_add(l)),
            Some(_) => {
                let reach = w.most.zip(w.len);
                reach.map(|(m, l)| w.off.saturating_add(m).saturating_add(l))
            }
        };
        let read_end = match base {
            None => Some(d.saturating_add(n)),
            Some(b) => self.most(b).map(|m| d.saturating_add(m).saturating_add(n)),
        };
        !(write_end.is_some_and(|end| end <= d) || read_end.is_some_and(|end| end <= w.off))
    }

    fn at_most_answer(&self, value: ExprId, stamp: u32) -> bool {
        let tested = |c: U256| {
            let reached = |(at, len): &(u32, u64)| *at == stamp && U256::from(*len) >= c;
            self.sized.iter().any(reached)
        };
        answer_stamp(value) == Some(stamp)
            || self.capped.contains(&(value, stamp))
            || expr::as_const(value).is_some_and(tested)
    }

    fn whole_word(&self, off: ExprId) -> Option<ExprId> {
        let word = self.load_bytes(off, 32, 0)?;
        let again = |n: &Node| matches!(n, Node::MLoad(at, _) if *at == off);
        (!expr::contains(word, &again)).then_some(word)
    }

    /* A word of the head that is a multiple of 32 past it may point at a part of dynamic
    length or may be a number. It is taken for a pointer only when a length stands there,
    the bytes that follow it are known, and the parts end where the next one starts or
    where the call data ends. Anything else leaves the call as the writes that built it. */
    fn call_args(&self, in_off: ExprId, in_len: ExprId) -> Option<(Vec<Arg>, Vec<Origin>)> {
        let at = |k: u64| expr::add_const(in_off, U256::from(4 + k));
        let offset = |w: ExprId, past: u64| {
            let c = expr::as_const(w).filter(|c| c.fits_u64())?.low_u64();
            (c.is_multiple_of(32) && c > past && c <= 32 * 64).then_some(c)
        };
        let mut head: Vec<ExprId> = Vec::new();
        let mut ends: Option<u64> = None;
        while ends != Some(32 * head.len() as u64) {
            let k = 32 * head.len() as u64;
            let word = self.whole_word(at(k)).filter(|_| head.len() < 64)?;
            if let Some(c) = offset(word, k) {
                ends = Some(ends.map_or(c, |e| e.min(c)));
            }
            head.push(word);
        }
        let head_end = ends?;
        let mut tails: Vec<(usize, u64)> = (0..head.len())
            .filter_map(|i| Some((i, offset(head[i], head_end - 32)?)))
            .collect();
        tails.sort_by_key(|(_, start)| *start);
        let mut args: Vec<Arg> = head.iter().map(|w| Arg::Word(*w)).collect();
        let mut built = self.consumers(in_off, 4 + head_end);
        for (which, (i, start)) in tails.iter().enumerate() {
            let next = tails.get(which + 1).map(|(_, s)| *s);
            let len = self.whole_word(at(*start))?;
            built.extend(self.consumers(at(*start), 32));
            let data = start + 32;
            let fixed = expr::as_const(len).filter(|c| c.fits_u64());
            let Some(count) = fixed.map(|c| c.low_u64()).filter(|c| *c <= 4096) else {
                // After a part of a length the code works out none has a fixed place.
                if next.is_some() {
                    return None;
                }
                let (parts, made) = self.copied_parts(in_off, in_len, &head, (*i, *start, len))?;
                built.extend(made);
                for (at, part) in parts {
                    args[at] = part;
                }
                continue;
            };
            let words = |n: u64| -> Option<Vec<ExprId>> {
                (0..n).map(|j| self.whole_word(at(data + 32 * j))).collect()
            };
            let last = |end: u64| match next {
                Some(start) => start == end,
                None => expr::as_const(in_len) == Some(U256::from(4 + end)),
            };
            let as_bytes = data + 32 * count.div_ceil(32);
            let as_list = data + 32 * count;
            let part = if last(as_bytes) && (count > 32 || !last(as_list)) {
                Arg::Bytes(count, words(count.div_ceil(32))?)
            } else if last(as_list) {
                let words = words(count)?;
                let text = |w: &ExprId| {
                    expr::as_const(*w).is_some_and(|c| (c & expr::mask_bits(248)).is_zero())
                };
                match count <= 1 && words.iter().all(text) {
                    true => Arg::Bytes(count, words),
                    false => Arg::List(words),
                }
            } else {
                return None;
            };
            let end = match part {
                Arg::Bytes(..) => as_bytes,
                _ => as_list,
            };
            built.extend(self.consumers(at(data), end - data));
            args[*i] = part;
        }
        Some((args, built))
    }

    fn held_length(&self, len: ExprId) -> Option<u64> {
        let Node::MLoad(at, _) = expr::node(len) else {
            return None;
        };
        let held = self.whole_word(at).and_then(expr::as_const)?;
        Some(held.low_u64()).filter(|c| held.fits_u64() && *c <= 4096)
    }

    fn bytes_now(&self, kind: u8, src: ExprId, len: ExprId) -> Option<Arg> {
        let count = self.held_length(len)?;
        let word = |j: u64| self.whole_word(expr::add_const(src, U256::from(32 * j)));
        let words: Option<Vec<ExprId>> = (0..count.div_ceil(32)).map(word).collect();
        (kind == op::MCOPY).then_some(Arg::Bytes(count, words?))
    }

    fn copied_part(&self, data: ExprId, len: ExprId) -> Option<(&MemWrite, Option<Origin>)> {
        let (base, d) = norm_offset(data);
        let start = summed(data);
        let ends = [len, round_up(len)].map(|l| summed(op2(op::ADD, data, l)));
        let copied = |w: &MemWrite| place(w) == start && matches!(w.val, MVal::Copy(..));
        let at = self.writes.iter().rposition(copied)?;
        let copy = &self.writes[at];
        if !copy.span.is_some_and(|s| s == len || s == round_up(len)) {
            return None;
        }
        let mut padding = None;
        for later in &self.writes[at + 1..] {
            let zero = later.val == MVal::Word(konst(U256::ZERO));
            let reach = u64::MAX / 4;
            let over = match later.base == base {
                true => later.len.is_none_or(|l| later.off + l > d),
                false => self.reaches(later, base, d, reach),
            };
            /* An address is a sum of terms that are never negative. A store that many
            bytes below where the copy starts, or at or past where it ends, left the
            copied bytes alone, whatever the terms are. */
            let at = place(later);
            let below = later.len.zip(ahead(&start, &at));
            let apart = below.is_some_and(|(l, gap)| gap >= l)
                || ends.iter().any(|end| ahead(&at, end).is_some());
            if ends.contains(&at) && zero {
                padding = later.origin;
            } else if over && !apart {
                return None;
            }
        }
        Some((copy, padding))
    }

    fn word_at(&self, addr: ExprId) -> Option<(ExprId, Option<Origin>)> {
        let wanted = summed(addr);
        let at = self.writes.iter().rposition(|w| place(w) == wanted)?;
        let (MVal::Word(word), Some(32)) = (&self.writes[at].val, self.writes[at].len) else {
            return None;
        };
        let clear = |later: &MemWrite| {
            let at = place(later);
            let below = later.len.zip(ahead(&wanted, &at));
            below.is_some_and(|(l, gap)| gap >= l)
                || ahead(&at, &wanted).is_some_and(|gap| gap >= 32)
        };
        let kept = self.writes[at + 1..].iter().all(clear) && self.current(*word);
        kept.then_some((*word, self.writes[at].origin))
    }

    /* Parts of a length the code works out have no fixed place. Each starts where the one
    before it ends, and a word of the head says so. The last ends where the call data
    does. */
    fn copied_parts(
        &self,
        in_off: ExprId,
        in_len: ExprId,
        head: &[ExprId],
        first: (usize, u64, ExprId),
    ) -> Option<(Parts, Vec<Origin>)> {
        let at = |from_head: ExprId| {
            op2(
                op::ADD,
                expr::add_const(in_off, U256::from(4u64)),
                from_head,
            )
        };
        let (mut index, start, mut len) = first;
        let mut start = konst_u64(start);
        let mut parts: Parts = Vec::new();
        let mut built: Vec<Origin> = Vec::new();
        while parts.len() < head.len() {
            let data = expr::add_const(start, U256::from(32u64));
            let (copy, padding) = self.copied_part(at(data), len)?;
            let MVal::Copy(kind, src, None) = copy.val else {
                return None;
            };
            // Where the length is known, a store past the bytes copied did not change them.
            let copied = self.held_length(len).unwrap_or(u64::MAX / 4);
            if kind == op::MCOPY && self.written_since(src, copied, copy.gen) {
                return None;
            }
            built.extend(copy.origin);
            built.extend(padding);
            let known = self.bytes_now(kind, src, len);
            parts.push((index, known.unwrap_or(Arg::Copied { kind, src, len })));
            let ends = [len, round_up(len)].map(|l| op2(op::ADD, data, l));
            let whole =
                |end: &ExprId| summed(expr::add_const(*end, U256::from(4u64))) == summed(in_len);
            if ends.iter().any(whole) {
                return Some((parts, built));
            }
            let taken = |j: &usize| parts.iter().any(|(i, _)| i == j);
            let next = (0..head.len())
                .filter(|j| !taken(j) && !expr::is_const(head[*j]))
                .find_map(|j| {
                    Some((
                        j,
                        *ends.iter().find(|end| summed(**end) == summed(head[j]))?,
                    ))
                })?;
            let (word, origin) = self.word_at(at(next.1))?;
            built.extend(origin);
            (index, start, len) = (next.0, next.1, word);
        }
        None
    }

    fn store(&mut self, off: ExprId, len: Option<u64>, val: MVal) {
        self.store_from(off, len, val, None)
    }

    fn store_from(
        &mut self,
        off: ExprId,
        len: Option<u64>,
        val: MVal,
        origin: Option<(usize, usize)>,
    ) {
        let (base, d) = norm_offset(off);
        match (base, len) {
            (None, Some(l)) => {
                let range = (d, d.saturating_add(l));
                self.touched.borrow_mut().ranges.insert(range);
                if !matches!(val, MVal::Unknown) {
                    self.written.insert(range);
                }
            }
            _ => self.touched.borrow_mut().anywhere = true,
        }
        if let Some(l) = len {
            self.writes.retain(|w| {
                !(w.base == base && w.len.is_some_and(|wl| w.off >= d && w.off + wl <= d + l))
            });
        }
        if self.writes.len() > MAX_TRACKED_WRITES {
            self.writes.drain(..64);
            self.fresh = false;
            self.clobber_gen = self.gen + 1;
            self.wiped = self.clobber_gen;
        }
        self.writes.push(MemWrite {
            base,
            off: d,
            len,
            val,
            origin,
            gen: self.gen + 1,
            span: None,
            most: base.and_then(|b| self.most(b)),
        });
    }

    fn store_copy(&mut self, dest: ExprId, len: ExprId, val: MVal, origin: Option<(usize, usize)>) {
        self.store_from(dest, const_len(len), val, origin);
        if let Some(copy) = self.writes.last_mut() {
            copy.span = Some(len);
        }
    }

    fn consumers(&self, off: ExprId, n: u64) -> Vec<(usize, usize)> {
        let (base, d) = norm_offset(off);
        let mut out = Vec::new();
        for w in self.writes.iter().rev() {
            if w.base != base {
                continue;
            }
            let Some(wl) = w.len else {
                match w.off >= d + n {
                    true => continue,
                    false => break,
                }
            };
            // A copy stays a statement unless the call it was made for prints it.
            if w.off < d + n && d < w.off + wl && !matches!(w.val, MVal::Copy(..)) {
                if let Some(o) = w.origin {
                    out.push(o);
                }
            }
        }
        out
    }

    fn clobber(&mut self) {
        self.touched.borrow_mut().anywhere = true;
        self.writes.clear();
        self.fresh = false;
        self.gen += 1;
        self.clobber_gen = self.gen;
        /* A helper of code that allocates is taken to leave alone what its caller read
        through a pointer, as a value its caller kept on the stack is. */
        if !self.pointer_named {
            self.wiped = self.gen;
        }
    }

    fn load_bytes(&self, off: ExprId, n: u64, _version: u32) -> Option<ExprId> {
        self.stored_bytes(off, n).filter(|v| self.current(*v))
    }

    fn stored_bytes(&self, off: ExprId, n: u64) -> Option<ExprId> {
        let (base, d) = norm_offset(off);
        let mut pieces: Vec<Option<(ExprId, u64)>> = vec![None; n as usize];
        let mut copy_hit: Option<(u8, ExprId, Option<ExprId>, u64, u32)> = None;
        let mut covered = 0usize;
        for w in self.writes.iter().rev() {
            if covered == n as usize {
                break;
            }
            if w.base != base {
                if self.reaches(w, base, d, n) {
                    return None;
                }
                continue;
            }
            let Some(wl) = w.len else {
                if d + n <= w.off {
                    continue;
                }
                if w.off <= d {
                    return None;
                }
                /* A write of a length the code works out starts inside the bytes read.
                From there on they are not known. The bytes before it still are. */
                for b in w.off..d + n {
                    let i = (b - d) as usize;
                    if pieces[i].is_none() {
                        pieces[i] = Some((konst(U256::ZERO), NOT_KNOWN));
                        covered += 1;
                    }
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
                MVal::Zero => {
                    for b in lo..hi {
                        let i = (b - d) as usize;
                        if pieces[i].is_none() {
                            pieces[i] = Some((konst(U256::ZERO), b - d));
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
                    if lo == d && hi == d + n && covered == 0 {
                        copy_hit = Some((*k, *src, *addr, d - w.off, w.gen));
                        covered = n as usize;
                        break;
                    }
                    return None;
                }
                /* A call writes no more than it was answered with. Past the end of a short
                answer the word keeps what it held, so it is the answer only where the
                code tested the answer to be long enough. */
                MVal::CallOut(seq, stamp) => {
                    let reached = |(at, len): &(u32, u64)| at == stamp && *len >= hi - w.off;
                    let whole = self.sized.iter().any(reached);
                    if lo == d && hi == d + n && covered == 0 && whole {
                        let seq = *seq;
                        let word = expr::intern(Node::ReturnData(seq, konst_u64(d - w.off)));
                        return Some(if n == 32 {
                            word
                        } else {
                            op2(op::SHR, konst_u64(8 * (32 - n)), word)
                        });
                    }
                    return None;
                }
                MVal::Unknown => return None,
            }
        }
        if let Some((k, src, addr, delta, wgen)) = copy_hit {
            let at = expr::add_const(src, U256::from(delta));
            let answered = addr
                .and_then(expr::as_const)
                .filter(|_| k == op::RETURNDATACOPY);
            let word = expr::intern(match answered {
                Some(seq) => Node::ReturnData(seq.low_u64() as u32, at),
                None => Node::CopiedWord(k, at, wgen),
            });
            return Some(if n == 32 {
                word
            } else {
                op2(op::SHR, konst_u64(8 * (32 - n)), word)
            });
        }
        let mut unknown_mask = U256::ZERO;
        let cut = pieces.iter().flatten().any(|(_, at)| *at == NOT_KNOWN);
        for piece in pieces.iter_mut() {
            if piece.is_some_and(|(_, at)| at == NOT_KNOWN) {
                *piece = None;
                covered -= 1;
            }
        }
        if covered < n as usize {
            let zero_ok = self.fresh && !base.is_some_and(wild_base) && !cut;
            if !zero_ok {
                if covered == 0 {
                    return None;
                }
                for (j, p) in pieces.iter().enumerate() {
                    if p.is_none() {
                        unknown_mask =
                            unknown_mask | (expr::mask_bits(8) << (8 * (n as u32 - 1 - j as u32)));
                    }
                }
            }
        }
        if n == 32 {
            if let Some((v, 0)) = pieces[0] {
                if pieces
                    .iter()
                    .enumerate()
                    .all(|(i, p)| *p == Some((v, i as u64)))
                {
                    return Some(v);
                }
            }
        }
        let mut acc: Option<ExprId> = None;
        let mut j = 0usize;
        while j < n as usize {
            match pieces[j] {
                None => {
                    j += 1;
                }
                Some((v, bi)) => {
                    let mut run = 1usize;
                    while j + run < n as usize {
                        match pieces[j + run] {
                            Some((v2, bi2)) if v2 == v && bi2 == bi + run as u64 => run += 1,
                            _ => break,
                        }
                    }
                    let shr = 8 * (32 - (bi + run as u64));
                    let mut piece = if shr > 0 {
                        op2(op::SHR, konst_u64(shr), v)
                    } else {
                        v
                    };
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
        let known = acc.unwrap_or_else(|| konst(U256::ZERO));
        if unknown_mask.is_zero() {
            return Some(known);
        }
        self.note_load(off, n);
        let word = expr::intern(Node::MLoad(off, self.version_for(off, n)));
        let unknown = if n == 32 {
            word
        } else {
            op2(op::SHR, konst_u64(8 * (32 - n)), word)
        };
        Some(op2(
            op::OR,
            op2(op::AND, unknown, konst(unknown_mask)),
            known,
        ))
    }

    fn free_pointer_now(&self) -> ExprId {
        let at = konst_u64(FREE_POINTER);
        self.load_bytes(at, 32, 0)
            .unwrap_or_else(|| expr::intern(Node::MLoad(at, self.version_for(at, 32))))
    }

    /* The free pointer is read far more often than it is written. Where its value is
    known to be the one it had, saying so keeps one name for one buffer. This is not a
    write the code makes, so it is not counted as one. */
    fn keep_free_pointer(&mut self, value: ExprId) {
        if self.free_pointer_now() == value {
            return;
        }
        self.writes
            .retain(|w| !(w.base.is_none() && w.off == FREE_POINTER && w.len == Some(32)));
        self.writes.push(MemWrite {
            base: None,
            off: FREE_POINTER,
            len: Some(32),
            val: MVal::Word(value),
            origin: None,
            gen: self.gen,
            span: None,
            most: None,
        });
    }

    fn load_word(&self, off: ExprId, version: u32) -> ExprId {
        match self.load_bytes(off, 32, version) {
            Some(v) => v,
            None => {
                self.note_load(off, 32);
                expr::intern(Node::MLoad(off, self.version_for(off, 32)))
            }
        }
    }

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
            words.push(self.load_bytes(
                expr::add_const(off, U256::from(i)),
                tail as u64,
                version,
            )?);
        }
        Some((words, tail))
    }

    /* Words read at every 32 bytes cut across writes that do not start on those bounds.
    Following the writes gives each stored value whole. A region made of whole words
    gives nothing, because the words already say it. */
    fn read_pieces(&self, off: ExprId, len: u64) -> Option<Vec<(ExprId, u8)>> {
        if len > 8192 {
            return None;
        }
        let (base, d) = norm_offset(off);
        let mut bytes: Vec<Option<(ExprId, u64)>> = vec![None; len as usize];
        let mut missing = bytes.len();
        for w in self.writes.iter().rev() {
            if missing == 0 {
                break;
            }
            if w.base != base {
                if self.reaches(w, base, d, len) {
                    return None;
                }
                continue;
            }
            let end = w.off.saturating_add(w.len.unwrap_or(u64::MAX));
            let open =
                (w.off.max(d)..end.min(d + len)).filter(|b| bytes[(b - d) as usize].is_none());
            let open: Vec<u64> = open.collect();
            let stored = match (&w.val, w.len) {
                (MVal::Word(v), Some(32)) => *v,
                (MVal::Byte(v), Some(1)) => op2(op::SHL, konst_u64(248), *v),
                (MVal::Zero, Some(_)) => konst(U256::ZERO),
                _ if open.is_empty() => continue,
                _ => return None,
            };
            // Zeros have no word of their own, so they are cut where the words read are.
            let within = |b: u64| match w.val {
                MVal::Zero => (b - d) % 32,
                _ => b - w.off,
            };
            for b in open {
                bytes[(b - d) as usize] = Some((stored, within(b)));
                missing -= 1;
            }
        }
        let bytes: Vec<(ExprId, u64)> = bytes.into_iter().collect::<Option<_>>()?;
        let mut pieces = Vec::new();
        let mut at = 0;
        while at < bytes.len() {
            let (v, first) = bytes[at];
            let run = bytes[at..]
                .iter()
                .zip(first..)
                .take_while(|((v2, i2), i)| *v2 == v && i2 == i)
                .count();
            let low = op2(op::SHR, konst_u64(8 * (32 - first - run as u64)), v);
            let part = op2(op::AND, low, konst(expr::mask_bits(8 * run as u32)));
            pieces.push((part, run as u8));
            at += run;
        }
        let whole = pieces.iter().all(|(_, width)| *width == 32);
        (!whole && pieces.iter().all(|(part, _)| self.current(*part))).then_some(pieces)
    }

    fn read_region_lossy(&self, off: ExprId, len: u64, version: u32) -> Option<Vec<ExprId>> {
        if len == 0 || !len.is_multiple_of(32) || len > 8 * 32 {
            return None;
        }
        let words: Vec<ExprId> = (0..len / 32)
            .map(|i| self.load_word(expr::add_const(off, U256::from(i * 32)), version))
            .collect();
        if words
            .iter()
            .all(|w| matches!(expr::node(*w), Node::MLoad(..)))
        {
            return None;
        }
        Some(words)
    }

    fn forget_all(&mut self, stable: u32) {
        self.writes.clear();
        self.written.clear();
        self.fresh = false;
        self.gen = merged_version(self.gen, self.gen, stable);
        self.clobber_gen = self.gen;
        self.wiped = self.gen;
    }

    fn intersect(&mut self, other: &Mem, stable: u32) -> bool {
        let fresh_before = self.fresh;
        let gen_before = self.gen;
        let same = |a: &MemWrite, b: &MemWrite| {
            a.base == b.base
                && a.off == b.off
                && a.len == b.len
                && a.val == b.val
                && a.span == b.span
                && a.most == b.most
        };
        let identical = self.gen == other.gen
            && self.wiped == other.wiped
            && self.sized == other.sized
            && self.capped == other.capped
            && self.below == other.below
            && self.clobber_gen == other.clobber_gen
            && self.fresh == other.fresh
            && self.written == other.written
            && self.writes.len() == other.writes.len()
            && self
                .writes
                .iter()
                .zip(&other.writes)
                .all(|(a, b)| a.gen == b.gen && same(a, b));
        if identical {
            return false;
        }
        let pointer = self.free_pointer_now();
        let pointer = (pointer == other.free_pointer_now()).then_some(pointer);
        type Place = (Option<ExprId>, u64, Option<u64>);
        let place = |w: &MemWrite| -> Place { (w.base, w.off, w.len) };
        let by_place = |writes: &[MemWrite]| {
            let mut index: HashMap<Place, Vec<usize>> = HashMap::new();
            for (i, w) in writes.iter().enumerate() {
                index.entry(place(w)).or_default().push(i);
            }
            index
        };
        let (mine, theirs) = (by_place(&self.writes), by_place(&other.writes));
        let at = |index: &HashMap<Place, Vec<usize>>, writes: &[MemWrite], w: &MemWrite| {
            let there = index.get(&place(w)).map(Vec::as_slice).unwrap_or(&[]);
            let agrees = there.iter().any(|i| writes[*i].val == w.val);
            let latest = there.iter().map(|i| writes[*i].gen).max();
            (agrees, latest)
        };
        let mut merged: Vec<MemWrite> = Vec::new();
        let mut kept: Vec<(usize, usize)> = Vec::new();
        for w in &self.writes {
            let (agrees, latest) = at(&theirs, &other.writes, w);
            if agrees {
                let there = theirs.get(&place(w)).map(Vec::as_slice).unwrap_or(&[]);
                let same = there.iter().rev().find(|i| other.writes[**i].val == w.val);
                kept.extend(same.map(|i| (merged.len(), *i)));
                merged.push(w.clone());
            } else {
                merged.push(MemWrite {
                    val: MVal::Unknown,
                    origin: None,
                    gen: w.gen.max(latest.unwrap_or(0)),
                    ..w.clone()
                });
            }
        }
        // Two writes that overlap leave the bytes of whichever came last. Both sides made
        // the same two writes, but in a different order, so the shared bytes differ.
        if kept.windows(2).any(|pair| pair[0].1 > pair[1].1) {
            let overlap = |a: &MemWrite, b: &MemWrite| {
                let end = |w: &MemWrite| w.len.map_or(u64::MAX, |l| w.off.saturating_add(l));
                a.base == b.base && a.off < end(b) && b.off < end(a)
            };
            let mut unsure: HashSet<usize> = HashSet::new();
            for (i, (first, theirs_first)) in kept.iter().enumerate() {
                for (second, theirs_second) in &kept[i + 1..] {
                    if theirs_first > theirs_second && overlap(&merged[*first], &merged[*second]) {
                        unsure.extend([*first, *second]);
                    }
                }
            }
            for i in unsure {
                merged[i].val = MVal::Unknown;
                merged[i].origin = None;
            }
        }
        /* A write only the other side made goes where that side made it, counted by the
        writes both sides share. At the end of the list it would hide a shared write that
        came after it, from a read of bytes it may or may not have reached. */
        let ordered = kept.windows(2).all(|pair| pair[0].1 < pair[1].1);
        let mut placed: HashSet<Place> = mine.keys().copied().collect();
        let mut ahead: HashMap<usize, Vec<MemWrite>> = HashMap::new();
        let mut last: Vec<MemWrite> = Vec::new();
        for (theirs_at, o) in other.writes.iter().enumerate() {
            let (agrees, _) = at(&mine, &self.writes, o);
            if !agrees && placed.insert(place(o)) {
                let unknown = MemWrite {
                    val: MVal::Unknown,
                    origin: None,
                    ..o.clone()
                };
                let next = kept.iter().find(|(_, shared)| *shared > theirs_at);
                match next.filter(|_| ordered) {
                    Some((at, _)) => ahead.entry(*at).or_default().push(unknown),
                    None => last.push(unknown),
                }
            }
        }
        if !ahead.is_empty() {
            let mut all = Vec::with_capacity(merged.len() + last.len());
            for (i, w) in merged.into_iter().enumerate() {
                all.extend(ahead.remove(&i).unwrap_or_default());
                all.push(w);
            }
            merged = all;
        }
        merged.extend(last);
        let overflow = merged.len().saturating_sub(MAX_TRACKED_WRITES);
        merged.drain(..overflow);
        let before = std::mem::replace(&mut self.writes, merged);
        let written_before = self.written.len();
        self.written.retain(|r| other.written.contains(r));
        self.fresh &= other.fresh && overflow == 0;
        let wiped_before = self.wiped;
        let sized_before = self.sized.len();
        let tested = |(at, len): &(u32, u64)| {
            let theirs = other.sized.iter().filter(|(a, _)| a == at).map(|(_, l)| *l);
            theirs.max().map(|l| (*at, l.min(*len)))
        };
        self.sized = self.sized.iter().filter_map(tested).collect();
        self.capped.retain(|c| other.capped.contains(c));
        let bounds_before = self.below.len();
        let bounded = |(e, n): &(ExprId, u64)| {
            let theirs = other.below.iter().filter(|(x, _)| x == e).map(|(_, m)| *m);
            theirs.min().map(|m| (*e, m.max(*n)))
        };
        self.below = self.below.iter().filter_map(bounded).collect();
        let lost = overflow > 0 || other.wiped != self.wiped;
        if lost || other.gen != self.gen || other.clobber_gen != self.clobber_gen {
            self.gen = merged_version(self.gen, other.gen, stable);
            self.clobber_gen = self.gen;
            // A write that is unknown after the merge is unknown as of the merge.
            // Left with the version of a later round it would outrank a store made after.
            for w in &mut self.writes {
                if matches!(w.val, MVal::Unknown) {
                    w.gen = w.gen.min(self.gen);
                }
            }
            /* The two sides count apart, so a version one of them lost its writes at
            says nothing about the other. */
            if lost {
                self.wiped = self.gen;
            }
        }
        if let Some(pointer) = pointer {
            self.keep_free_pointer(pointer);
        }
        let changed_writes = before.len() != self.writes.len()
            || before.iter().zip(&self.writes).any(|(a, b)| !same(a, b))
            || self.written.len() != written_before;
        changed_writes
            || fresh_before != self.fresh
            || gen_before != self.gen
            || wiped_before != self.wiped
            || sized_before != self.sized.len()
            || bounds_before != self.below.len()
    }
}

fn tested_below(cond: ExprId, holds: bool) -> Option<(ExprId, u64)> {
    let fixed = |e: ExprId| {
        expr::as_const(e)
            .filter(|c| c.fits_u64() && c.low_u64() < 1 << 32)
            .map(|c| c.low_u64())
    };
    let Node::Op(o, v) = expr::node(cond) else {
        return None;
    };
    let (value, below) = match (o, holds) {
        (op::ISZERO, _) => return tested_below(v[0], !holds),
        (op::LT, true) => (v[0], fixed(v[1])?),
        (op::GT, true) => (v[1], fixed(v[0])?),
        (op::LT, false) => (v[1], fixed(v[0])? + 1),
        (op::GT, false) => (v[0], fixed(v[1])? + 1),
        (op::EQ, true) => match (fixed(v[0]), fixed(v[1])) {
            (Some(c), None) => (v[1], c + 1),
            (None, Some(c)) => (v[0], c + 1),
            _ => return None,
        },
        _ => return None,
    };
    (below > 0 && !expr::is_const(value)).then_some((value, below))
}

fn answer_stamp(e: ExprId) -> Option<u32> {
    match expr::node(e) {
        Node::Env(op::RETURNDATASIZE, stamp) => Some(stamp),
        _ => None,
    }
}

fn answer_length(cond: ExprId, holds: bool, capped: &[(ExprId, u32)]) -> Option<(u32, u64)> {
    let cap = |e: ExprId| capped.iter().find(|(v, _)| *v == e).map(|(_, at)| *at);
    let size = |e: ExprId| answer_stamp(e).or_else(|| cap(e));
    let fixed = |e: ExprId| {
        expr::as_const(e)
            .filter(|c| c.fits_u64())
            .map(|c| c.low_u64())
    };
    let Node::Op(o, v) = expr::node(cond) else {
        return None;
    };
    match (o, holds) {
        (op::ISZERO, _) => answer_length(v[0], !holds, capped),
        (op::LT | op::SLT, false) | (op::GT | op::SGT, true) => {
            let least = fixed(v[1])?.checked_add(u64::from(holds))?;
            Some((size(v[0])?, least))
        }
        (op::LT | op::SLT, true) | (op::GT | op::SGT, false) => {
            let least = fixed(v[0])?.checked_add(u64::from(holds))?;
            Some((size(v[1])?, least))
        }
        (op::EQ, true) => {
            let at = size(v[0]).or(size(v[1]))?;
            Some((at, fixed(v[0]).or(fixed(v[1]))?))
        }
        _ => None,
    }
}

#[derive(Clone, Debug)]
pub struct State {
    stack: Vec<ExprId>,
    args_used: usize,
    mem: Mem,
    storage: Vec<(ExprId, ExprId, bool)>,
    version: u32,
    sgen: u32,
    called: bool,
    returned: u32,
}

impl State {
    fn learn(&mut self, cond: ExprId, holds: bool) {
        if let Some((at, len)) = answer_length(cond, holds, &self.mem.capped) {
            if !self.mem.sized.contains(&(at, len)) {
                self.mem.sized.push((at, len));
            }
        }
        if let Some(bound) = tested_below(cond, holds) {
            if !self.mem.below.contains(&bound) && self.mem.below.len() < 64 {
                self.mem.below.push(bound);
            }
        }
    }

    fn pop(&mut self) -> ExprId {
        match self.stack.pop() {
            Some(v) => v,
            None => {
                let v = expr::arg(self.args_used as u32);
                self.args_used += 1;
                v
            }
        }
    }
    fn peek(&mut self, n: usize) -> ExprId {
        while self.stack.len() < n {
            let v = expr::arg(self.args_used as u32);
            self.args_used += 1;
            self.stack.insert(0, v);
        }
        self.stack[self.stack.len() - n]
    }
}

#[derive(Debug)]
pub struct Lifter<'a> {
    pub prog: &'a Program,
    pub root: bool,
    pub summaries: HashMap<usize, CalleeSummary>,
    pub footprints: HashMap<usize, MemoryWrites>,
    pub pointer_keepers: HashSet<usize>,
    pub memory_readers: HashSet<usize>,
    pub free_pointer: bool,
    pub oracle: bool,
    pub copy_loops: RefCell<HashMap<(usize, usize), CopyLoop>>,
}

#[derive(Clone, Debug)]
pub struct CopyLoop {
    pub entry: usize,
    pub latch: usize,
    pub body: usize,
    pub exit: usize,
    pub shape: CopyShape,
}

#[derive(Clone, Debug)]
pub enum CopyShape {
    Index { slot: usize, rotated: bool },
    Countdown { n: usize, d: usize, s: usize },
}

#[derive(Clone, Debug, Default)]
pub struct CalleeSummary {
    pub returns: Vec<ExprId>,
    pub mstores: Vec<(ExprId, ExprId)>,
    pub side_effects: bool,
    pub reverts: Option<(ExprId, ExprId, Option<Vec<ExprId>>)>,
    pub guards: Vec<(ExprId, Option<Vec<ExprId>>, bool)>,
    pub stores_and_copies_before: Vec<(usize, usize)>,
    pub copies: Vec<(ExprId, ExprId, ExprId)>,
    pub maybe_mstores: Vec<ExprId>,
    pub hashes: Vec<(ExprId, usize, usize)>,
    pub stores_before_copy: Vec<usize>,
    pub store_gens: Vec<u32>,
}

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
                Stmt::MStore {
                    off,
                    val,
                    width: 32,
                    gen,
                } => {
                    sum.mstores.push((*off, *val));
                    sum.store_gens.push(*gen);
                }
                Stmt::MStore { .. } => return None,
                Stmt::Copy {
                    kind: op::MCOPY,
                    dest,
                    src,
                    len,
                    ..
                } => {
                    sum.stores_before_copy.push(sum.mstores.len());
                    sum.copies.push((*dest, *src, *len));
                }
                Stmt::Copy { .. }
                | Stmt::Internal { .. }
                | Stmt::Call { .. }
                | Stmt::Create { .. } => return None,
                Stmt::SStore { .. } | Stmt::Log { .. } => sum.side_effects = true,
                Stmt::Require {
                    cond,
                    data,
                    invalid,
                } => {
                    sum.stores_and_copies_before
                        .push((sum.mstores.len(), sum.copies.len()));
                    sum.guards.push((*cond, data.clone(), *invalid));
                }
                Stmt::Drop(e) if matches!(expr::node(*e), Node::KeccakMem(..)) => {
                    sum.hashes.push((*e, sum.mstores.len(), sum.copies.len()));
                }
                Stmt::Assign { .. } | Stmt::Drop(_) => {}
            }
        }
        match &nd.term {
            Term::Revert { off, len, data } if seen.len() <= 4 => {
                sum.reverts = Some((*off, *len, data.clone()));
                return Some(sum);
            }
            Term::InternalReturn(vals) => {
                sum.returns = vals.clone();
                let simple = |e: &ExprId| {
                    expr::size(*e) <= 64
                        && !expr::contains(*e, &|x| {
                            matches!(
                                x,
                                Node::Var(_)
                                    | Node::IntRet(..)
                                    | Node::CallResult(_)
                                    | Node::Unknown(_)
                            )
                        })
                };
                let ok = sum
                    .returns
                    .iter()
                    .chain(sum.mstores.iter().flat_map(|(a, b)| [a, b]))
                    .chain(sum.copies.iter().flat_map(|(a, b, c)| [a, b, c]))
                    .all(simple)
                    && sum.guards.iter().all(|(c, d, _)| {
                        simple(c) && d.as_ref().is_none_or(|d| d.iter().all(simple))
                    });
                return if ok { Some(sum) } else { None };
            }
            Term::Jump(t) => n = *t,
            Term::Branch { cond, t, f } => {
                if *t == Some(*f) {
                    n = *f;
                    continue;
                }
                if let Some(t) = t {
                    #[derive(PartialEq)]
                    enum ArmEnd {
                        Join(usize),
                        Ret(Vec<ExprId>),
                    }
                    let arm = |x: usize| -> Option<(Vec<ExprId>, ArmEnd)> {
                        let nd = &l.nodes[x];
                        let mut offs = Vec::new();
                        for s in &nd.stmts {
                            match s {
                                Stmt::MStore { off, width: 32, .. } => offs.push(*off),
                                _ => return None,
                            }
                        }
                        match &nd.term {
                            Term::Jump(j) => Some((offs, ArmEnd::Join(*j))),
                            Term::InternalReturn(vals) if offs.len() <= 2 => {
                                Some((offs, ArmEnd::Ret(vals.clone())))
                            }
                            _ => None,
                        }
                    };
                    let end_of = |x: usize| -> (Vec<ExprId>, ArmEnd) {
                        arm(x).unwrap_or((Vec::new(), ArmEnd::Join(x)))
                    };
                    let (ot, et) = end_of(*t);
                    let (of, ef) = end_of(*f);
                    if et == ef && (ot.len() + of.len()) <= 4 {
                        match et {
                            ArmEnd::Join(j) if j != *t || j != *f => {
                                sum.maybe_mstores.extend(ot);
                                sum.maybe_mstores.extend(of);
                                n = j;
                                continue;
                            }
                            ArmEnd::Ret(vals) => {
                                sum.maybe_mstores.extend(ot);
                                sum.maybe_mstores.extend(of);
                                sum.returns = vals;
                                let simple = |e: &ExprId| {
                                    expr::size(*e) <= 64
                                        && !expr::contains(*e, &|x| {
                                            matches!(
                                                x,
                                                Node::Var(_)
                                                    | Node::IntRet(..)
                                                    | Node::CallResult(_)
                                                    | Node::Unknown(_)
                                            )
                                        })
                                };
                                let ok = sum
                                    .returns
                                    .iter()
                                    .chain(sum.mstores.iter().flat_map(|(a, b)| [a, b]))
                                    .chain(sum.copies.iter().flat_map(|(a, b, c)| [a, b, c]))
                                    .chain(sum.maybe_mstores.iter())
                                    .all(simple)
                                    && sum.guards.iter().all(|(c, d, _)| {
                                        simple(c) && d.as_ref().is_none_or(|d| d.iter().all(simple))
                                    });
                                return if ok { Some(sum) } else { None };
                            }
                            _ => {}
                        }
                    }
                }
                let follow = |mut x: usize| -> Option<usize> {
                    let mut hops = 0;
                    loop {
                        let nd = &l.nodes[x];
                        if !nd.stmts.iter().all(|s| matches!(s, Stmt::MStore { .. })) {
                            return None;
                        }
                        match &nd.term {
                            Term::Revert { .. } | Term::Invalid | Term::Infeasible => {
                                return Some(x)
                            }
                            Term::Jump(j) if hops < 4 => {
                                x = *j;
                                hops += 1;
                            }
                            _ => return None,
                        }
                    }
                };
                let rev = |x: usize| follow(x).is_some();
                let payload = |x: usize| -> (Option<Vec<ExprId>>, bool) {
                    match follow(x).map(|y| &l.nodes[y].term) {
                        Some(Term::Revert { data, .. }) => (data.clone(), false),
                        Some(Term::Invalid) => (None, true),
                        _ => (None, false),
                    }
                };
                match t {
                    Some(t) if rev(*t) && !rev(*f) => {
                        let (d, inv) = payload(*t);
                        sum.stores_and_copies_before
                            .push((sum.mstores.len(), sum.copies.len()));
                        sum.guards.push((op1(op::ISZERO, *cond), d, inv));
                        n = *f;
                    }
                    Some(t) if rev(*f) && !rev(*t) => {
                        let (d, inv) = payload(*f);
                        sum.stores_and_copies_before
                            .push((sum.mstores.len(), sum.copies.len()));
                        sum.guards.push((*cond, d, inv));
                        n = *t;
                    }
                    None => {
                        sum.stores_and_copies_before
                            .push((sum.mstores.len(), sum.copies.len()));
                        sum.guards.push((op1(op::ISZERO, *cond), None, true));
                        n = *f;
                    }
                    _ => return None,
                }
            }
            _ => return None,
        }
    }
}

#[derive(Default)]
struct Hidden {
    // Cleared each time the node is re-run.
    // A decode that only succeeded on an early run must not hide stores for good.
    by_node: RefCell<HashMap<usize, HashSet<(usize, usize)>>>,
    // For each node, how many earlier nodes of the unit run the same block.
    copies: Vec<u32>,
}

const COPY_BITS: u32 = 6;

// A call is numbered by where it stands in the code, so the number means the same call
// in a helper and in every function that helper is folded into. Numbering by node made
// the first call of a function and the first call of its helper the same call.
fn site_seq(pc: usize, copy: u32) -> u32 {
    (pc as u32) << COPY_BITS | copy.min((1 << COPY_BITS) - 1)
}

// The same call seen in two copies of its block is still one place in the code.
pub fn call_site(seq: u32) -> u32 {
    seq >> COPY_BITS
}

fn copy_ordinals(unit: &Unit) -> Vec<u32> {
    let mut seen: HashMap<usize, u32> = HashMap::new();
    unit.nodes
        .iter()
        .map(|n| {
            let count = seen.entry(n.block).or_insert(0);
            *count += 1;
            *count - 1
        })
        .collect()
}

impl Hidden {
    fn begin(&self, consumer: usize) {
        self.by_node.borrow_mut().remove(&consumer);
    }
    fn add(&self, consumer: usize, origins: Vec<(usize, usize)>) {
        self.by_node
            .borrow_mut()
            .entry(consumer)
            .or_default()
            .extend(origins);
    }
    fn all(&self) -> HashSet<(usize, usize)> {
        self.by_node.borrow().values().flatten().copied().collect()
    }
}

#[derive(Clone)]
struct Entry {
    state: State,
    phis: Vec<bool>,
    widened: bool,
}

impl<'a> Lifter<'a> {
    pub fn lift(&self, unit: &Unit, initial: Option<(Vec<ExprId>, bool)>) -> Lifted {
        let (init_stack, fresh) = initial.unwrap_or((Vec::new(), self.root));
        let state = State {
            stack: init_stack,
            args_used: 0,
            mem: Mem::new(fresh, self.free_pointer),
            storage: Vec::new(),
            version: 0,
            sgen: 0,
            called: !fresh,
            returned: 0,
        };
        self.lift_from(unit, state)
    }

    pub fn lift_summarizing(&self, unit: &Unit, initial: Option<(Vec<ExprId>, bool)>) -> Lifted {
        let l = self.lift(unit, initial.clone());
        let loops = crate::idiom::copy_loops(&l);
        if loops.is_empty() || self.oracle {
            return l;
        }
        for cl in loops {
            self.copy_loops
                .borrow_mut()
                .insert((unit.entry_block, cl.entry), cl);
        }
        self.lift(unit, initial)
    }

    pub fn lift_from_summarizing(&self, unit: &Unit, init: State) -> Lifted {
        let l = self.lift_from(unit, init.clone());
        let loops = crate::idiom::copy_loops(&l);
        if loops.is_empty() || self.oracle {
            return l;
        }
        for cl in loops {
            self.copy_loops
                .borrow_mut()
                .insert((unit.entry_block, cl.entry), cl);
        }
        self.lift_from(unit, init)
    }

    pub fn entry_state_of(l: &Lifted, unit_node: usize) -> Option<State> {
        l.entry_states.get(unit_node).cloned().flatten()
    }

    // Terminates because phis only grow and memory knowledge only shrinks.
    pub fn lift_from(&self, unit: &Unit, init: State) -> Lifted {
        let entry_loads = init.mem.entry_loads.clone();
        let touched = init.mem.touched.clone();
        let n = unit.nodes.len();
        let mut entries: Vec<Option<Entry>> = vec![None; n];
        let mut lnodes: Vec<Option<LNode>> = vec![None; n];
        let mut exit_states: Vec<Option<State>> = vec![None; n];
        let mut runs = vec![0usize; n];
        let mut unsettled = vec![0usize; n];
        let mut phi_ids: HashMap<(usize, usize), ExprId> = HashMap::new();
        let mut work: VecDeque<usize> = VecDeque::new();
        let mut queued = vec![false; n];
        let mut reprocess_count = 0usize;

        let stable = stable_versions(unit);
        let hidden = Hidden {
            copies: copy_ordinals(unit),
            ..Hidden::default()
        };
        let init_len = init.stack.len();
        let (init_stack, init_args) = (init.stack.clone(), init.args_used);
        entries[unit.entry] = Some(Entry {
            state: init,
            phis: vec![false; init_len],
            widened: false,
        });
        work.push_back(unit.entry);
        queued[unit.entry] = true;
        let mut max_args = 0usize;

        while let Some(nid) = work.pop_front() {
            crate::clock::check();
            queued[nid] = false;
            runs[nid] += 1;
            let widened = entries[nid].as_ref().is_some_and(|e| e.widened);
            let allowed = match widened {
                true => MAX_RUNS_PER_NODE + 8,
                false => MAX_RUNS_PER_NODE,
            };
            if runs[nid] > allowed {
                continue;
            }
            if runs[nid] > 1 {
                reprocess_count += 1;
            }
            // Some loops need one round per word they move. Stopping at the limit kept
            // what the earlier rounds still believed, which is not true for later passes.
            // Giving up every belief about memory and storage first is always true.
            // A node whose beliefs have settled and whose stack alone still changes keeps them.
            if runs[nid] == MAX_RUNS_PER_NODE && unsettled[nid] + 2 >= runs[nid] {
                let e = entries[nid]
                    .as_mut()
                    .expect("a scheduled node has an entry state");
                e.widened = true;
                e.state.mem.forget_all(stable[nid]);
                e.state.storage.clear();
                e.state.sgen = merged_version(e.state.sgen, e.state.sgen, stable[nid]);
            }
            let entry = entries[nid]
                .clone()
                .expect("a scheduled node has an entry state");
            let (mut lnode, exit) = self.run_node(unit, nid, &entry.state, &hidden);
            max_args = max_args.max(exit.args_used);
            let loops = self.copy_loops.borrow();
            let mut redirect: Vec<(usize, usize)> = Vec::new();
            let mut succ_state: HashMap<usize, State> = HashMap::new();
            for s in lnode.succs.clone() {
                if let Some(cl) = loops.get(&(unit.entry_block, s)) {
                    if nid != cl.body && nid != cl.latch {
                        let placed = Some((nid, lnode.stmts.len()));
                        let summary = self.summarize_copy_loop(unit, cl, &exit, &hidden, placed);
                        if let Some((stmt, after)) = summary {
                            lnode.stmts.push(stmt);
                            redirect.push((s, cl.exit));
                            succ_state.insert(cl.exit, after);
                        }
                    }
                }
            }
            drop(loops);
            if !redirect.is_empty() {
                let m: HashMap<usize, usize> = redirect.iter().copied().collect();
                lnode.succs = lnode.succs.iter().map(|s| *m.get(s).unwrap_or(s)).collect();
                lnode.term = remap_term(&lnode.term, &m);
            }
            let succs: Vec<usize> = lnode.succs.clone();
            let tested = match &lnode.term {
                Term::Branch { cond, t, f } if *t != Some(*f) => Some((*cond, *t, *f)),
                _ => None,
            };
            lnodes[nid] = Some(lnode);
            exit_states[nid] = Some(exit.clone());
            let exit_all = exit;
            for s in succs {
                let mut exit = succ_state.get(&s).unwrap_or(&exit_all).clone();
                if let Some((cond, t, f)) = tested {
                    if t == Some(s) || f == s {
                        exit.learn(cond, t == Some(s));
                    }
                }
                // The entry is also reached from the caller.
                let single_pred = unit.nodes[s].preds.len() <= 1 && s != unit.entry;
                let changed = match &mut entries[s] {
                    None => {
                        entries[s] = Some(Entry {
                            widened: false,
                            phis: vec![false; exit.stack.len()],
                            state: State {
                                stack: exit.stack.clone(),
                                args_used: exit.args_used,
                                mem: exit.mem.clone(),
                                storage: exit.storage.clone(),
                                version: 0,
                                sgen: exit.sgen,
                                called: exit.called,
                                returned: exit.returned,
                            },
                        });
                        true
                    }
                    Some(e) if single_pred => {
                        let new_state = State {
                            stack: exit.stack.clone(),
                            args_used: exit.args_used.max(e.state.args_used),
                            mem: exit.mem.clone(),
                            storage: exit.storage.clone(),
                            version: 0,
                            sgen: exit.sgen,
                            called: exit.called,
                            returned: exit.returned,
                        };
                        let changed = e.state.stack != new_state.stack
                            || e.state.mem.writes != new_state.mem.writes
                            || e.state.mem.fresh != new_state.mem.fresh
                            || e.state.mem.gen != new_state.mem.gen
                            || e.state.mem.wiped != new_state.mem.wiped
                            || e.state.mem.sized != new_state.mem.sized
                            || e.state.mem.capped != new_state.mem.capped
                            || e.state.mem.below != new_state.mem.below
                            || e.state.storage != new_state.storage
                            || e.state.sgen != new_state.sgen
                            || e.state.returned != new_state.returned;
                        e.state = new_state;
                        e.phis = vec![false; e.state.stack.len()];
                        changed
                    }
                    Some(e) => {
                        let before = (e.state.mem.gen, e.state.sgen, e.state.storage.len());
                        let known = e.state.mem.writes.clone();
                        let changed = merge_into(e, &exit, s, stable[s], &mut phi_ids);
                        let after = (e.state.mem.gen, e.state.sgen, e.state.storage.len());
                        if before != after || known != e.state.mem.writes {
                            unsettled[s] = runs[s];
                        }
                        changed
                    }
                };
                if changed && !queued[s] {
                    queued[s] = true;
                    work.push_back(s);
                }
            }
        }

        let hidden_set = without_still_read(&lnodes, hidden.all(), &self.memory_readers);
        let mut nodes: Vec<LNode> = Vec::new();
        let mut map: HashMap<usize, usize> = HashMap::new();
        for (i, ln) in lnodes.iter().enumerate() {
            if let Some(ln) = ln {
                map.insert(i, nodes.len());
                let mut ln = ln.clone();
                ln.entry_stack = entries[i]
                    .as_ref()
                    .map(|e| e.state.stack.clone())
                    .unwrap_or_default();
                if !self.oracle && std::env::var("EVMDEC_SHOW_HIDDEN").is_err() {
                    let mut idx = 0usize;
                    ln.stmts.retain(|s| {
                        let keep = match s {
                            Stmt::MStore { .. } | Stmt::Copy { .. } => {
                                !hidden_set.contains(&(i, idx))
                            }
                            _ => true,
                        };
                        idx += 1;
                        keep
                    });
                }
                nodes.push(ln);
            }
        }
        for nd in nodes.iter_mut() {
            nd.id = map[&nd.id];
            nd.succs = nd
                .succs
                .iter()
                .filter_map(|s| map.get(s).copied())
                .collect();
            nd.term = remap_term(&nd.term, &map);
        }
        /* Below its own values a helper finds what its caller pushed. The main unit starts
        on an empty stack. A place past every argument the helper takes is only reached
        where a loop leaves the stack uneven. */
        let reaching = |entry: &Entry, stack: &[ExprId], args_used: usize| {
            let (el, xl) = (entry.state.stack.len(), stack.len());
            let mut assigns = Vec::new();
            for (k, var) in entry.state.stack.iter().enumerate() {
                let from_top = el - 1 - k;
                let below = args_used + from_top.saturating_sub(xl);
                let val = if from_top < xl {
                    stack[xl - 1 - from_top]
                } else if !self.root && below < max_args {
                    expr::arg(below as u32)
                } else {
                    expr::intern(Node::Unknown(expr::next_seq()))
                };
                if entry.phis[k] && val != *var {
                    assigns.push((*var, val));
                }
            }
            assigns
        };
        let mut edge_assigns: HashMap<(usize, usize), Vec<(ExprId, ExprId)>> = HashMap::new();
        for (i, ln) in lnodes.iter().enumerate() {
            let Some(ln) = ln else { continue };
            let from = map[&i];
            let exit = exit_states[i]
                .as_ref()
                .expect("a lifted node has an exit state");
            for s in &ln.succs {
                let Some(&to) = map.get(s) else { continue };
                let entry = entries[*s]
                    .as_ref()
                    .expect("a successor of a lifted node has an entry state");
                let assigns = reaching(entry, &exit.stack, exit.args_used);
                if !assigns.is_empty() {
                    edge_assigns.insert((from, to), assigns);
                }
            }
        }
        /* A helper that starts on a loop is entered from its caller and from the end of the
        loop. What it starts with is assigned on a node of its own, ahead of the loop. */
        let first = map[&unit.entry];
        let mut entry = first;
        let start = entries[unit.entry]
            .as_ref()
            .map_or(Vec::new(), |e| reaching(e, &init_stack, init_args));
        if !start.is_empty() {
            entry = nodes.len();
            nodes.push(LNode {
                id: entry,
                term: Term::Jump(first),
                succs: vec![first],
                stmts: Vec::new(),
                preds: Vec::new(),
                entry_stack: Vec::new(),
                exit_stack: Vec::new(),
                ..nodes[first]
            });
            edge_assigns.insert((entry, first), start);
        }
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
                v.retain(|(var, val)| {
                    used.contains(var) && !matches!(expr::node(*val), Node::Unknown(_))
                });
            }
            edge_assigns.retain(|_, v| !v.is_empty());
            let after: usize = edge_assigns.values().map(|v| v.len()).sum();
            if after == before {
                break;
            }
        }
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
        /* A call takes the first way out of its helper. The helper's own return address
        is the one that way out jumps to. */
        let vias = unit.exits.iter().map(|e| Some(e.via));
        let ret_slot = vias
            .chain(unit.nodes.iter().map(|n| n.returns_via))
            .find_map(|via| match via {
                Some(AVal::Slot(k)) => Some(k as u32),
                _ => None,
            });
        let entry_states: Vec<Option<State>> = entries
            .iter()
            .map(|e| e.as_ref().map(|e| e.state.clone()))
            .collect();
        let entry_loads = entry_loads.borrow().clone();
        let mut mem_writes = touched.borrow().clone();
        mem_writes.anywhere |= nodes
            .iter()
            .any(|nd| matches!(nd.term, Term::Unresolved(_) | Term::Switch { .. }));
        Lifted {
            nodes,
            entry,
            edge_assigns,
            n_args: max_args,
            reprocess_count,
            ret_slot,
            entry_states,
            node_map: map,
            entry_loads,
            mem_writes,
        }
    }

    fn summarize_copy_loop(
        &self,
        unit: &Unit,
        cl: &CopyLoop,
        entering: &State,
        hidden: &Hidden,
        placed: Option<(usize, usize)>,
    ) -> Option<(Stmt, State)> {
        let top = entering.stack.len();
        let at = |st: &State, slot: usize| -> Option<ExprId> {
            if slot < st.stack.len() {
                Some(st.stack[st.stack.len() - 1 - slot])
            } else {
                None
            }
        };
        let round_up = |e: ExprId| {
            op2(
                op::AND,
                expr::add_const(e, U256::from_u64(31)),
                konst(!U256::from_u64(31)),
            )
        };
        match &cl.shape {
            CopyShape::Index { slot, rotated } => {
                let i0 = at(entering, *slot)?;
                let marker = expr::intern(Node::Unknown(expr::next_seq()));
                let mut probe = entering.clone();
                probe.stack[top - 1 - *slot] = marker;
                let (off, src, cond) = if *rotated {
                    let (bn, after_body) = self.run_node(unit, cl.body, &probe, hidden);
                    let Some(Stmt::MStore {
                        off,
                        val,
                        width: 32,
                        ..
                    }) = bn.stmts.iter().find(|s| matches!(s, Stmt::MStore { .. }))
                    else {
                        return None;
                    };
                    let Node::MLoad(src, _) = expr::node(*val) else {
                        return None;
                    };
                    let (ln, _) = if cl.latch == cl.body {
                        (bn.clone(), after_body.clone())
                    } else {
                        self.run_node(unit, cl.latch, &after_body, hidden)
                    };
                    let Term::Branch { cond, .. } = &ln.term else {
                        return None;
                    };
                    (*off, src, *cond)
                } else {
                    let (xn, after_x) = self.run_node(unit, cl.latch, &probe, hidden);
                    let Term::Branch { cond, .. } = &xn.term else {
                        return None;
                    };
                    let (bn, _) = self.run_node(unit, cl.body, &after_x, hidden);
                    let Some(Stmt::MStore {
                        off,
                        val,
                        width: 32,
                        ..
                    }) = bn.stmts.iter().find(|s| matches!(s, Stmt::MStore { .. }))
                    else {
                        return None;
                    };
                    let Node::MLoad(src, _) = expr::node(*val) else {
                        return None;
                    };
                    (*off, src, *cond)
                };
                let mut memo = HashMap::new();
                let unmark = |e: ExprId, memo: &mut HashMap<ExprId, ExprId>| {
                    expr::substitute(
                        e,
                        &|n| {
                            if matches!(n, Node::Unknown(_)) && expr::intern(n.clone()) == marker {
                                Some(i0)
                            } else {
                                None
                            }
                        },
                        memo,
                    )
                };
                let len = loop_bound(cond)?;
                if expr::contains(len, &|n| matches!(n, Node::Unknown(_))) {
                    return None;
                }
                let (dst0, src0) = (unmark(off, &mut memo), unmark(src, &mut memo));
                let count = if expr::as_const(i0) == Some(U256::ZERO) {
                    round_up(len)
                } else {
                    round_up(op2(op::SUB, len, i0))
                };
                let mut st = entering.clone();
                apply_mcopy(&mut st, dst0, src0, count, placed);
                let stmt = Stmt::Copy {
                    kind: op::MCOPY,
                    dest: dst0,
                    src: src0,
                    len: count,
                    addr: None,
                    gen: st.mem.gen,
                };
                let last = op2(op::SUB, op2(op::ADD, i0, count), konst_u64(32));
                let final_i = if *rotated {
                    last
                } else {
                    op2(op::ADD, i0, count)
                };
                st.stack[top - 1 - *slot] = final_i;
                let after = if *rotated {
                    let (_, s1) = self.run_node(unit, cl.body, &st, hidden);
                    if cl.latch == cl.body {
                        s1
                    } else {
                        self.run_node(unit, cl.latch, &s1, hidden).1
                    }
                } else {
                    self.run_node(unit, cl.latch, &st, hidden).1
                };
                Some((stmt, after))
            }
            CopyShape::Countdown { n, d, s } => {
                let (len, dst, src) = (at(entering, *n)?, at(entering, *d)?, at(entering, *s)?);
                let whole = op2(op::AND, len, konst(!U256::from_u64(31)));
                let mut st = entering.clone();
                apply_mcopy(&mut st, dst, src, whole, placed);
                st.stack[top - 1 - *n] = op2(op::AND, len, konst_u64(31));
                st.stack[top - 1 - *d] = op2(op::ADD, dst, whole);
                st.stack[top - 1 - *s] = op2(op::ADD, src, whole);
                let after = self.run_node(unit, cl.latch, &st, hidden).1;
                Some((
                    Stmt::Copy {
                        kind: op::MCOPY,
                        dest: dst,
                        src,
                        len: whole,
                        addr: None,
                        gen: st.mem.gen,
                    },
                    after,
                ))
            }
        }
    }

    fn run_node(&self, unit: &Unit, nid: usize, entry: &State, hidden: &Hidden) -> (LNode, State) {
        let prog = self.prog;
        let un = &unit.nodes[nid];
        let blk = &prog.blocks[un.block];
        hidden.begin(nid);
        let mut st = entry.clone();
        st.version = st.mem.gen;
        let mut stmts: Vec<Stmt> = Vec::new();
        let mut term: Option<Term> = None;
        let seq_base = (nid as u32) << SEQ_BITS;
        let mut seq_ctr = 0u32;
        // The oracle lifts one node per step, so there the step is the number.
        let copy = hidden.copies.get(nid).copied().filter(|_| !self.oracle);
        let seq_at = |pc: usize, count: u32| match copy {
            Some(copy) => site_seq(pc, copy),
            None => seq_base + count,
        };
        let next_version = |st: &mut State| {
            st.mem.tick();
            st.version = st.mem.gen;
            st.version
        };

        let succ_by_kind = |kinds: &[Edge]| -> Vec<usize> {
            un.succs
                .iter()
                .filter(|(_, k)| kinds.contains(k))
                .map(|(s, _)| *s)
                .collect()
        };

        if un.infeasible {
            let ln = LNode {
                id: nid,
                block: un.block,
                pc: blk.start,
                stmts: vec![],
                term: Term::Infeasible,
                preds: vec![],
                succs: vec![],
                entry_stack: vec![],
                exit_stack: vec![],
                sgen: entry.sgen,
                mgen: entry.mem.gen,
            };
            return (ln, st);
        }

        for ins in prog.block_insns(blk) {
            crate::clock::check();
            let o = ins.opcode;
            macro_rules! pop {
                () => {
                    st.pop()
                };
            }
            match o {
                _ if op::is_push(o) => st.stack.push(konst(ins.imm.unwrap_or(U256::ZERO))),
                _ if op::is_dup(o) => {
                    let n = (o - 0x7f) as usize;
                    let v = st.peek(n);
                    st.stack.push(v);
                }
                _ if op::is_swap(o) => {
                    let n = (o - 0x8f) as usize;
                    st.peek(n + 1);
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
                op::MSIZE => st.stack.push(expr::env_seq(o)),
                op::GAS => {
                    let left = expr::env_seq(o);
                    /* The gas left is read here and may be used much later. The mark
                    lets the text name it where it was read. The oracle counts reads by
                    the values that are used, so it gets none. */
                    if !self.oracle {
                        stmts.push(Stmt::Drop(left));
                    }
                    st.stack.push(left);
                }
                op::RETURNDATASIZE => {
                    st.stack.push(if st.called {
                        expr::intern(Node::Env(o, st.returned))
                    } else {
                        konst(U256::ZERO)
                    });
                }
                op::ADDRESS
                | op::ORIGIN
                | op::CALLER
                | op::CALLVALUE
                | op::CALLDATASIZE
                | op::CODESIZE
                | op::GASPRICE
                | op::COINBASE
                | op::TIMESTAMP
                | op::NUMBER
                | op::PREVRANDAO
                | op::GASLIMIT
                | op::CHAINID
                | op::BASEFEE
                | op::BLOBBASEFEE => {
                    st.stack.push(expr::env(o));
                }
                op::SELFBALANCE => {
                    st.stack
                        .push(expr::intern(Node::Env(op::SELFBALANCE, st.sgen)));
                }
                op::CALLDATALOAD => {
                    let off = pop!();
                    st.stack.push(expr::calldataload(off));
                }
                op::BALANCE | op::EXTCODESIZE | op::EXTCODEHASH | op::BLOCKHASH | op::BLOBHASH => {
                    let a = pop!();
                    let own =
                        o == op::BALANCE && matches!(expr::node(a), Node::Env(op::ADDRESS, _));
                    // A call or a create can change another account's balance and code.
                    // The stamp keeps a read made after one apart from a read made before.
                    let changes = matches!(o, op::BALANCE | op::EXTCODESIZE | op::EXTCODEHASH);
                    st.stack.push(if own {
                        expr::intern(Node::Env(op::SELFBALANCE, st.sgen))
                    } else if changes && st.sgen > 0 {
                        expr::intern(Node::Op(o, vec![a, konst_u64(u64::from(st.sgen))]))
                    } else {
                        expr::intern(Node::Op(o, vec![a]))
                    });
                }
                op::ISZERO | op::NOT | op::CLZ => {
                    let a = pop!();
                    st.stack.push(op1(o, a));
                }
                op::ADD
                | op::MUL
                | op::SUB
                | op::DIV
                | op::SDIV
                | op::MOD
                | op::SMOD
                | op::EXP
                | op::SIGNEXTEND
                | op::LT
                | op::GT
                | op::SLT
                | op::SGT
                | op::EQ
                | op::AND
                | op::OR
                | op::XOR
                | op::BYTE
                | op::SHL
                | op::SHR
                | op::SAR => {
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
                        Some(l) if l <= 8192 => match st.mem.read_region(off, l as u64, st.version)
                        {
                            Some((words, tail)) => {
                                hidden.add(nid, st.mem.consumers(off, l as u64));
                                match fold_keccak(&words, tail) {
                                    Some(h) => konst(h),
                                    None => {
                                        let hash = expr::intern(Node::Keccak(words, tail));
                                        if let Some(pieces) = st.mem.read_pieces(off, l as u64) {
                                            expr::set_pieces(hash, pieces);
                                        }
                                        hash
                                    }
                                }
                            }
                            None => {
                                st.mem.note_range(off, len);
                                expr::intern(Node::KeccakMem(
                                    off,
                                    len,
                                    st.mem.version_for(off, l as u64),
                                ))
                            }
                        },
                        _ => {
                            st.mem.note_range(off, len);
                            expr::intern(Node::KeccakMem(
                                off,
                                len,
                                st.mem.version_for(off, u64::MAX / 4),
                            ))
                        }
                    };
                    /* A hash of memory nothing is known of is taken here and may be used
                    after that memory is written again. The mark lets the text name it
                    where it was taken. The oracle reads memory by its version. */
                    if !self.oracle && matches!(expr::node(v), Node::KeccakMem(..)) {
                        stmts.push(Stmt::Drop(v));
                    }
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
                    let gen = st.mem.gen + 1;
                    if o == op::MSTORE {
                        st.mem.store_from(off, Some(32), MVal::Word(val), origin);
                        stmts.push(Stmt::MStore {
                            off,
                            val,
                            width: 32,
                            gen,
                        });
                    } else {
                        let b = op2(op::AND, val, konst_u64(0xff));
                        st.mem.store_from(off, Some(1), MVal::Byte(b), origin);
                        stmts.push(Stmt::MStore {
                            off,
                            val: b,
                            width: 1,
                            gen,
                        });
                    }
                    next_version(&mut st);
                }
                op::SLOAD | op::TLOAD => {
                    let key = pop!();
                    let transient = o == op::TLOAD;
                    let cached = st
                        .storage
                        .iter()
                        .rev()
                        .find(|(k, _, t)| *k == key && *t == transient)
                        .map(|(_, v, _)| *v);
                    let v = cached
                        .unwrap_or_else(|| expr::intern(Node::SLoad(key, transient, st.sgen)));
                    st.stack.push(v);
                }
                op::SSTORE | op::TSTORE => {
                    let key = pop!();
                    let val = pop!();
                    let transient = o == op::TSTORE;
                    st.storage.retain(|(k, _, t)| *t != transient || *k != key);
                    if expr::is_const(key) {
                        st.storage
                            .retain(|(k, _, t)| *t != transient || expr::is_const(*k));
                    } else {
                        st.storage.retain(|(_, _, t)| *t != transient);
                    }
                    st.storage.push((key, val, transient));
                    let gen = st.sgen;
                    st.sgen += 1;
                    stmts.push(Stmt::SStore {
                        key,
                        val,
                        transient,
                        gen,
                    });
                }
                op::JUMP => {
                    let _target = pop!();
                    let nowhere = expr::as_const(_target).is_some_and(|c| {
                        c.as_usize()
                            .and_then(|pc| self.prog.target_block(pc))
                            .is_none()
                    });
                    if nowhere && !self.oracle {
                        let zero = konst(U256::ZERO);
                        term = Some(Term::Revert {
                            off: zero,
                            len: zero,
                            data: Some(Vec::new()),
                        });
                        break;
                    }
                    if self.oracle || un.computed_cut {
                        term = Some(Term::Unresolved(_target));
                        break;
                    }
                    if let Some(call) = &un.call {
                        term = Some(self.internal_call(
                            unit,
                            un,
                            call,
                            &mut st,
                            &mut stmts,
                            seq_at(ins.pc, seq_ctr),
                        ));
                    } else if let Some(via) = un.returns_via {
                        let ret_arg = match via {
                            AVal::Slot(k) => Some(expr::arg(k as u32)),
                            _ => None,
                        };
                        let shape = unit
                            .exits
                            .iter()
                            .find(|e| e.via == via && e.pushed.len() == st.stack.len());
                        let vals: Vec<ExprId> = match shape {
                            Some(exit) => st
                                .stack
                                .iter()
                                .zip(&exit.pushed)
                                .filter(|(_, pushed)| !pushed.passes_through())
                                .map(|(v, _)| *v)
                                .collect(),
                            None => st
                                .stack
                                .iter()
                                .copied()
                                .filter(|v| Some(*v) != ret_arg)
                                .collect(),
                        };
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
                            _ => Term::Switch {
                                target: _target,
                                cases: targets,
                            },
                        });
                    }
                    break;
                }
                op::JUMPI => {
                    let _target = pop!();
                    let cond = pop!();
                    if self.oracle {
                        term = Some(Term::CondJump {
                            cond,
                            target: _target,
                        });
                        break;
                    }
                    let ts = succ_by_kind(&[Edge::True]);
                    let fs = succ_by_kind(&[Edge::False]);
                    let tnode = ts.first().copied();
                    let fnode = fs.first().copied();
                    term = Some(if ts.len() > 1 {
                        Term::Switch {
                            target: _target,
                            cases: ts.iter().copied().chain(fnode).collect(),
                        }
                    } else {
                        match (expr::as_const(cond), tnode, fnode) {
                            (Some(c), Some(t), _) if !c.is_zero() => Term::Jump(t),
                            (Some(c), None, _) if !c.is_zero() => Term::Infeasible,
                            (Some(_), _, Some(f)) => Term::Jump(f),
                            (Some(_), _, None) => Term::Infeasible,
                            (None, Some(t), Some(f)) => Term::Branch {
                                cond,
                                t: Some(t),
                                f,
                            },
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
                    let l = expr::as_const(len)
                        .and_then(|v| v.as_usize())
                        .map(|v| v as u64);
                    let gen = st.mem.gen + 1;
                    if o == op::MCOPY {
                        apply_mcopy(&mut st, dest, src, len, Some((nid, stmts.len())));
                    } else if o == op::CODECOPY {
                        match (expr::as_const(src).and_then(|v| v.as_usize()), l) {
                            (Some(s), Some(l)) if l <= 4096 => {
                                let mut i = 0u64;
                                while i < l {
                                    let n = (l - i).min(32) as usize;
                                    let mut buf = [0u8; 32];
                                    for (j, out) in buf.iter_mut().enumerate().take(n) {
                                        let at = s.checked_add(i as usize + j);
                                        *out =
                                            at.and_then(|a| prog.code.get(a)).copied().unwrap_or(0);
                                    }
                                    if n == 32 {
                                        st.mem.store(
                                            expr::add_const(dest, U256::from(i)),
                                            Some(32),
                                            MVal::Word(konst(U256::from_be_bytes(&buf))),
                                        );
                                    } else {
                                        for (j, byte) in buf.iter().enumerate().take(n) {
                                            st.mem.store(
                                                expr::add_const(dest, U256::from(i + j as u64)),
                                                Some(1),
                                                MVal::Byte(konst_u64(*byte as u64)),
                                            );
                                        }
                                    }
                                    i += 32;
                                }
                            }
                            _ => st.mem.store(dest, l, MVal::Copy(o, src, None)),
                        }
                    } else if let (true, Some(l)) = (past_call_data(o, src), l) {
                        // Past the end of the call data every byte reads as zero.
                        let origin = Some((nid, stmts.len()));
                        st.mem.store_from(dest, Some(l), MVal::Zero, origin);
                    } else {
                        let origin = Some((nid, stmts.len()));
                        st.mem
                            .store_copy(dest, len, MVal::Copy(o, src, None), origin);
                    }
                    next_version(&mut st);
                    stmts.push(Stmt::Copy {
                        kind: o,
                        dest,
                        src,
                        len,
                        addr: None,
                        gen,
                    });
                }
                op::EXTCODECOPY => {
                    let addr = pop!();
                    let dest = pop!();
                    let src = pop!();
                    let len = pop!();
                    let l = expr::as_const(len)
                        .and_then(|v| v.as_usize())
                        .map(|v| v as u64);
                    st.mem.store(dest, l, MVal::Copy(o, src, Some(addr)));
                    let gen = next_version(&mut st);
                    stmts.push(Stmt::Copy {
                        kind: o,
                        dest,
                        src,
                        len,
                        addr: Some(addr),
                        gen,
                    });
                }
                op::LOG0..=op::LOG4 => {
                    let off = pop!();
                    let len = pop!();
                    let n = (o - op::LOG0) as usize;
                    let mut topics = Vec::new();
                    for _ in 0..n {
                        topics.push(pop!());
                    }
                    let data = expr::as_const(len)
                        .and_then(|l| l.as_usize())
                        .and_then(|l| st.mem.read_region(off, l as u64, st.version))
                        .map(|(w, _)| w);
                    if let (Some(_), Some(l)) = (&data, expr::as_const(len)) {
                        hidden.add(nid, st.mem.consumers(off, l.low_u64()));
                    }
                    stmts.push(Stmt::Log {
                        off,
                        len,
                        topics,
                        data,
                    });
                }
                op::CALL | op::CALLCODE | op::DELEGATECALL | op::STATICCALL => {
                    let gas = pop!();
                    let addr = pop!();
                    let value = if o == op::CALL || o == op::CALLCODE {
                        Some(pop!())
                    } else {
                        None
                    };
                    let in_off = pop!();
                    let in_len = pop!();
                    let out_off = pop!();
                    let out_len = pop!();
                    /* Gas read only to be handed to this call needs no name, and the
                    mark would stand between the call and the writes that built its data. */
                    if let Some(Stmt::Drop(left)) = stmts.last() {
                        let read = expr::node(*left);
                        let kept = st.stack.iter().any(|e| expr::contains(*e, &|n| *n == read));
                        if matches!(read, Node::Env(op::GAS, _)) && !kept {
                            stmts.pop();
                        }
                    }
                    let seq = seq_at(ins.pc, seq_ctr);
                    seq_ctr += 1;
                    let input = expr::as_const(in_len)
                        .and_then(|l| l.as_usize())
                        .and_then(|l| st.mem.read_region(in_off, l as u64, st.version))
                        .map(|(w, _)| w);
                    if let (Some(_), Some(l)) = (&input, expr::as_const(in_len)) {
                        hidden.add(nid, st.mem.consumers(in_off, l.low_u64()));
                    }
                    let layout = expr::as_const(in_len)
                        .and_then(|l| l.as_usize())
                        .and_then(|l| st.mem.read_pieces(in_off, l as u64));
                    let decoded = match self.oracle {
                        false => st.mem.call_args(in_off, in_len),
                        true => None,
                    };
                    let args = decoded.map(|(args, built)| {
                        hidden.add(nid, built);
                        args
                    });
                    let result = expr::intern(Node::CallResult(seq));
                    let input_head: Vec<ExprId> = if expr::as_const(in_len) == Some(U256::ZERO) {
                        Vec::new()
                    } else {
                        (0..4)
                            .map(|i| {
                                st.mem.load_word(
                                    expr::add_const(in_off, U256::from_u64(32 * i)),
                                    st.version,
                                )
                            })
                            .collect()
                    };
                    let ol = expr::as_const(out_len)
                        .and_then(|v| v.as_usize())
                        .map(|v| v as u64);
                    let il = expr::as_const(in_len)
                        .and_then(|v| v.as_usize())
                        .map(|v| v as u64);
                    let identity = expr::as_const(addr) == Some(U256::from_u64(4))
                        && (o == op::STATICCALL || o == op::CALL);
                    let fits = matches!((ol, il), (Some(o), Some(i)) if 0 < o && o <= i);
                    let copies = identity && (fits || (ol.is_none() && out_len == in_len));
                    let copied = st.mem.gen + 1;
                    let shown = copies && !self.oracle;
                    let answered = call_stamp(nid, stmts.len() + 1 + usize::from(shown));
                    if copies || (identity && ol == Some(0)) {
                        apply_mcopy(&mut st, out_off, in_off, out_len, None);
                    } else if ol != Some(0) {
                        st.mem.store(out_off, ol, MVal::CallOut(seq, answered));
                    }
                    next_version(&mut st);
                    let gen = (o != op::STATICCALL).then_some(st.sgen);
                    if o != op::STATICCALL {
                        st.storage.clear();
                        st.sgen += 1;
                    }
                    stmts.push(Stmt::Call {
                        seq,
                        kind: o,
                        gas,
                        addr,
                        value,
                        in_off,
                        in_len,
                        out_off,
                        out_len,
                        input,
                        input_head,
                        layout,
                        args,
                        result,
                        gen,
                    });
                    /* The identity built-in is how code before MCOPY copies memory. The
                    copy is what later reads of the output see, so it is a statement. */
                    if shown {
                        stmts.push(Stmt::Copy {
                            kind: op::MCOPY,
                            dest: out_off,
                            src: in_off,
                            len: out_len,
                            addr: None,
                            gen: copied,
                        });
                    }
                    st.stack.push(result);
                    st.called = true;
                    st.returned = answered;
                }
                op::CREATE | op::CREATE2 => {
                    let value = pop!();
                    let off = pop!();
                    let len = pop!();
                    let salt = if o == op::CREATE2 { Some(pop!()) } else { None };
                    let seq = seq_at(ins.pc, seq_ctr);
                    seq_ctr += 1;
                    let init = expr::as_const(len)
                        .and_then(|l| l.as_usize())
                        .and_then(|l| st.mem.read_region(off, l as u64, st.version))
                        .map(|(w, _)| w);
                    let result = expr::intern(Node::CreateResult(seq));
                    let gen = st.sgen;
                    st.storage.clear();
                    st.sgen += 1;
                    next_version(&mut st);
                    stmts.push(Stmt::Create {
                        seq,
                        kind: o,
                        value,
                        off,
                        len,
                        salt,
                        result,
                        init,
                        gen,
                    });
                    st.stack.push(result);
                    st.called = true;
                    st.returned = call_stamp(nid, stmts.len());
                }
                op::RETURN | op::REVERT => {
                    let off = pop!();
                    let len = pop!();
                    let mut data = expr::as_const(len)
                        .and_then(|l| l.as_usize())
                        .and_then(|l| st.mem.read_region(off, l as u64, st.version))
                        .map(|(w, _)| w);
                    if let (Some(_), Some(l)) = (&data, expr::as_const(len)) {
                        hidden.add(nid, st.mem.consumers(off, l.low_u64()));
                    } else if o == op::RETURN && !self.oracle {
                        data = expr::as_const(len)
                            .and_then(|l| l.as_usize())
                            .and_then(|l| st.mem.read_region_lossy(off, l as u64, st.version));
                    }
                    term = Some(if o == op::RETURN {
                        Term::Return { off, len, data }
                    } else {
                        Term::Revert { off, len, data }
                    });
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
        let ln = LNode {
            id: nid,
            block: un.block,
            pc: blk.start,
            stmts,
            term,
            preds: vec![],
            succs,
            entry_stack: vec![],
            exit_stack: st.stack.clone(),
            sgen: entry.sgen,
            mgen: entry.mem.gen,
        };
        (ln, st)
    }

    #[allow(
        clippy::too_many_arguments,
        reason = "the lifter state, call site and summaries are all needed to bind one call"
    )]
    fn internal_call(
        &self,
        _unit: &Unit,
        un: &crate::cfg::UNode,
        call: &crate::cfg::CallInfo,
        st: &mut State,
        stmts: &mut Vec<Stmt>,
        seq: u32,
    ) -> Term {
        let consumed = call.consumed as usize;
        if consumed > 0 {
            st.peek(consumed);
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
        let summary = self.summaries.get(&call.callee);
        let free_pointer = konst(U256::from_u64(FREE_POINTER));
        let free_now = st.mem.load_word(free_pointer, st.version);
        let entering = Entering {
            at: &at,
            free_now,
            mem: st.mem.clone(),
            gen: st.mem.gen,
            sgen: st.sgen,
            stores: summary.map_or_else(Vec::new, |s| {
                let offs = s.mstores.iter().map(|(off, _)| *off);
                offs.zip(s.store_gens.iter().copied()).collect()
            }),
        };
        let subst = |e: ExprId| -> ExprId { entered(e, &entering) };
        if let Some(sum) = summary {
            if let Some((off, len, data)) = &sum.reverts {
                for (o, v) in &sum.mstores {
                    st.mem.store(subst(*o), Some(32), MVal::Word(subst(*v)));
                }
                let data = data.as_ref().map(|d| d.iter().map(|e| subst(*e)).collect());
                return Term::Revert {
                    off: subst(*off),
                    len: subst(*len),
                    data,
                };
            }
        }
        let unknown_pushed = call.pushed.iter().filter(|v| !v.passes_through()).count();
        let by_position = summary.is_some_and(|s| s.returns.len() == call.pushed.len());
        // What a folded helper tested holds for the values it hands back.
        let folded = summary
            .filter(|s| by_position || s.returns.len() == unknown_pushed)
            .filter(|s| !s.side_effects);
        for (cond, _, _) in folded.map_or(&[][..], |s| s.guards.as_slice()) {
            st.learn(subst(*cond), true);
        }
        /* What the caller read and handed in was read when the caller read it. Read again
        here, a word the caller wrote since, such as the free pointer, would stand in. */
        let mut handed: HashSet<ExprId> = HashSet::new();
        let mut pending: Vec<ExprId> = (0..consumed).map(&at).collect();
        while let Some(x) = pending.pop() {
            if expr::holds(x, kind::MLOAD) && handed.insert(x) {
                pending.extend(expr::children(x));
            }
        }
        let resolve = |e: ExprId| -> ExprId {
            let mut memo = HashMap::new();
            expr::substitute(
                e,
                &|n| {
                    let Node::MLoad(a, _) = n else {
                        return None;
                    };
                    let read = expr::intern(n.clone());
                    if handed.contains(&read) {
                        return Some(read);
                    }
                    /* A read that is still a read of the same place has gained
                    nothing. Its caller made it, and with a new stamp it would be
                    another value than the one the helper tested. It stays whole. The
                    place it read is not looked up again either. */
                    let now = st.mem.load_word(*a, st.version);
                    let same = matches!(expr::node(now), Node::MLoad(at, _) if at == *a);
                    Some(match same {
                        true => expr::intern(n.clone()),
                        false => now,
                    })
                },
                &mut memo,
            )
        };
        let reads_caller = summary.is_some_and(|s| {
            s.mstores.is_empty() && s.copies.is_empty() && s.maybe_mstores.is_empty()
        });
        let direct_returns: Option<Vec<ExprId>> = summary
            .filter(|s| by_position || s.returns.len() == unknown_pushed)
            .map(|s| {
                s.returns
                    .iter()
                    .map(|e| {
                        if reads_caller {
                            resolve(subst(*e))
                        } else {
                            subst(*e)
                        }
                    })
                    .collect()
            });
        let mut results = Vec::new();
        let mut j = 0u16;
        let mut pushed_vals = Vec::new();
        for (idx, v) in call.pushed.iter().enumerate() {
            let e = match v {
                AVal::Slot(i) => at(*i as usize),
                AVal::Const(c) | AVal::Pc(c) => {
                    j += 1;
                    results.push(konst(*c));
                    konst(*c)
                }
                _ => {
                    let r = match &direct_returns {
                        Some(d) => d[if by_position { idx } else { j as usize }],
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
        let inlined = direct_returns.is_some();
        let transparent = inlined && summary.is_some_and(|s| !s.side_effects);
        let gen_before = st.sgen;
        /* A test the helper made before a store reads what memory held before it. The
        tests are stated where the helper made them, or one would read as coming after
        a store or a copy it came before. */
        let tests = |stmts: &mut Vec<Stmt>, made: (usize, usize)| {
            let Some(sum) = summary.filter(|_| transparent) else {
                return;
            };
            for (i, (cond, data, invalid)) in sum.guards.iter().enumerate() {
                if sum.stores_and_copies_before.get(i) != Some(&made) {
                    continue;
                }
                let cond = subst(*cond);
                if expr::as_const(cond).is_some_and(|c| !c.is_zero()) {
                    continue;
                }
                let data = data.as_ref().map(|d| d.iter().map(|e| subst(*e)).collect());
                stmts.push(Stmt::Require {
                    cond,
                    data,
                    invalid: *invalid,
                });
            }
        };
        /* A hash the helper took reads the memory of the place it took it at. The mark
        stands there among the helper's stores, so the text can name the hash before a
        later store changes what it was taken over. */
        let mut marks: Vec<((usize, usize), ExprId)> = Vec::new();
        for (hash, stores, copies) in summary.map_or(&[][..], |s| s.hashes.as_slice()) {
            let hash = match reads_caller {
                true => resolve(subst(*hash)),
                false => subst(*hash),
            };
            let taken = matches!(expr::node(hash), Node::KeccakMem(..));
            if taken && transparent && !self.oracle {
                marks.push(((*stores, *copies), hash));
            }
        }
        let hashed = |stmts: &mut Vec<Stmt>, made: (usize, usize)| {
            let here = marks.iter().filter(|(at, _)| *at == made);
            stmts.extend(here.map(|(_, hash)| Stmt::Drop(*hash)));
        };
        match summary {
            Some(sum) => {
                /* Stores and copies are made in the helper's order. Where two of them
                overlap, the bytes left are those of the later one. */
                let mut copied = 0;
                for stored in 0..=sum.mstores.len() {
                    while sum.stores_before_copy.get(copied) == Some(&stored) {
                        tests(stmts, (stored, copied));
                        hashed(stmts, (stored, copied));
                        let (dest, src, len) = sum.copies[copied];
                        let (d, s2, l2) = (subst(dest), subst(src), subst(len));
                        // A copy of no bytes does nothing.
                        let stated = transparent && expr::as_const(l2) != Some(U256::ZERO);
                        if stated {
                            stmts.push(Stmt::Copy {
                                kind: op::MCOPY,
                                dest: d,
                                src: s2,
                                len: l2,
                                addr: None,
                                gen: st.mem.gen + 1,
                            });
                        }
                        let shown = stated.then(|| (un.id, stmts.len() - 1));
                        apply_mcopy(st, d, s2, l2, shown);
                        copied += 1;
                    }
                    tests(stmts, (stored, copied));
                    hashed(stmts, (stored, copied));
                    let Some((off, val)) = sum.mstores.get(stored) else {
                        break;
                    };
                    let (o, v) = (subst(*off), subst(*val));
                    if transparent {
                        let origin = Some((un.id, stmts.len()));
                        let gen = st.mem.gen + 1;
                        st.mem.store_from(o, Some(32), MVal::Word(v), origin);
                        stmts.push(Stmt::MStore {
                            off: o,
                            val: v,
                            width: 32,
                            gen,
                        });
                    } else {
                        st.mem.store(o, Some(32), MVal::Word(v));
                    }
                }
                for off in &sum.maybe_mstores {
                    st.mem.store(subst(*off), Some(32), MVal::Unknown);
                }
                if transparent && !sum.mstores.is_empty() {
                    st.mem.tick();
                    st.version = st.mem.gen;
                }
                if sum.side_effects {
                    st.storage.clear();
                    st.sgen += 1;
                }
            }
            None => {
                let fixed = self
                    .footprints
                    .get(&call.callee)
                    .and_then(MemoryWrites::fixed);
                match fixed {
                    Some(ranges) => {
                        for (lo, hi) in ranges {
                            st.mem.store(konst_u64(lo), Some(hi - lo), MVal::Unknown);
                        }
                        st.mem.tick();
                        st.version = st.mem.gen;
                    }
                    None => {
                        st.mem.clobber();
                        if self.pointer_keepers.contains(&call.callee) {
                            st.mem.keep_free_pointer(free_now);
                        } else {
                            let word = (FREE_POINTER, FREE_POINTER + 32);
                            st.mem.touched.borrow_mut().ranges.insert(word);
                        }
                    }
                }
                st.storage.clear();
                st.sgen += 1;
                st.called = true;
                st.returned = call_stamp(un.id, stmts.len());
            }
        }
        if !transparent {
            stmts.push(Stmt::Internal {
                seq,
                callee: self.prog.blocks[call.callee].start,
                args,
                results: if inlined { vec![] } else { results },
                gen: (st.sgen != gen_before).then_some(gen_before),
            });
        }
        let conts: Vec<usize> = un
            .succs
            .iter()
            .filter(|(_, k)| *k == Edge::Return)
            .map(|(s, _)| *s)
            .collect();
        match conts.len() {
            0 => Term::Infeasible,
            1 => Term::Jump(conts[0]),
            _ => Term::Switch {
                target: konst(U256::ZERO),
                cases: conts,
            },
        }
    }
}

// A term taken away again is gone, which is how an end less a start gives a length.
fn summed(e: ExprId) -> (Vec<(ExprId, i64)>, U256) {
    let mut terms: HashMap<ExprId, i64> = HashMap::new();
    let mut fixed = U256::ZERO;
    let mut pending = vec![(e, 1i64)];
    while let Some((x, sign)) = pending.pop() {
        match expr::node(x) {
            Node::Op(op::ADD, v) => pending.extend(v.into_iter().map(|t| (t, sign))),
            Node::Op(op::SUB, v) => pending.extend([(v[0], sign), (v[1], -sign)]),
            Node::Const(c) if sign > 0 => fixed = fixed.wrapping_add(c),
            Node::Const(c) => fixed = fixed.wrapping_sub(c),
            _ => *terms.entry(x).or_insert(0) += sign,
        }
    }
    let mut terms: Vec<(ExprId, i64)> = terms.into_iter().filter(|(_, n)| *n != 0).collect();
    terms.sort_unstable();
    (terms, fixed)
}

struct Entering<'a> {
    at: &'a dyn Fn(usize) -> ExprId,
    free_now: ExprId,
    mem: Mem,
    gen: u32,
    sgen: u32,
    stores: Vec<(ExprId, u32)>,
}

// What a folded helper read from memory before it wrote any is what its caller's held.
fn entered(e: ExprId, with: &Entering) -> ExprId {
    let free_pointer = konst_u64(FREE_POINTER);
    let marks: RefCell<Vec<(ExprId, ExprId)>> = RefCell::default();
    let after: RefCell<Vec<(ExprId, ExprId)>> = RefCell::default();
    /* A read of a word the helper stored itself comes after that store. Stamped as if
    made on entry it would seem to come before it. The helper's stores all take the
    version just past entry, so the read takes that one too. */
    let stored_before = |at: ExprId, v: u32| with.stores.iter().any(|(o, g)| *o == at && *g <= v);
    let mark = |n: &Node| match n {
        Node::MLoad(at, 0) if *at != free_pointer => {
            let mark = expr::intern(Node::Unknown(expr::next_seq()));
            marks.borrow_mut().push((mark, *at));
            Some(mark)
        }
        Node::MLoad(at, v) if *at != free_pointer && stored_before(*at, *v) => {
            let mark = expr::intern(Node::Unknown(expr::next_seq()));
            after.borrow_mut().push((mark, *at));
            Some(mark)
        }
        _ => None,
    };
    let marked = expr::substitute(e, &mark, &mut HashMap::new());
    // Restamping comes first. It would take the caller's own reads for the helper's.
    let restamped = expr::restamp(marked, with.gen, with.sgen, &mut HashMap::new());
    let mut reads: HashMap<ExprId, ExprId> = marks
        .into_inner()
        .into_iter()
        .map(|(mark, at)| (mark, with.mem.load_word(entered(at, with), 0)))
        .collect();
    for (mark, at) in after.into_inner() {
        let read = Node::MLoad(entered(at, with), with.gen + 1);
        reads.insert(mark, expr::intern(read));
    }
    let said = |n: &Node| match n {
        Node::Arg(i) => Some((with.at)(*i as usize)),
        Node::MLoad(at, _) if *at == free_pointer => Some(with.free_now),
        Node::Unknown(_) => reads.get(&expr::intern(n.clone())).copied(),
        _ => None,
    };
    expr::substitute(restamped, &said, &mut HashMap::new())
}

type Place = (Vec<(ExprId, i64)>, U256);

fn place(w: &MemWrite) -> Place {
    let (terms, fixed) = w.base.map(summed).unwrap_or_default();
    (terms, fixed.wrapping_add(U256::from(w.off)))
}

/* How far the first place lies past the second, when no term can bring it below. A term
counts up from zero unless it is made the way code writes a negative number. */
fn ahead(a: &Place, b: &Place) -> Option<u64> {
    let mut terms: HashMap<ExprId, i64> = a.0.iter().copied().collect();
    for (term, times) in &b.0 {
        *terms.entry(*term).or_insert(0) -= times;
    }
    let negative = |term: &ExprId| match expr::node(*term) {
        Node::Op(op::NOT | op::SIGNEXTEND | op::SDIV | op::SMOD | op::SAR, _) => true,
        Node::Op(op::MUL, v) => v
            .iter()
            .any(|x| expr::as_const(*x).is_some_and(|c| c.bits() > 64)),
        _ => false,
    };
    let up = terms
        .iter()
        .all(|(term, times)| *times == 0 || (*times > 0 && !negative(term)));
    let gap = a.1.wrapping_sub(b.1);
    (up && gap.fits_u64() && gap.low_u64() < BIG).then(|| gap.low_u64())
}

fn round_up(len: ExprId) -> ExprId {
    op2(
        op::AND,
        expr::add_const(len, U256::from_u64(31)),
        konst(!U256::from_u64(31)),
    )
}

fn past_call_data(kind: u8, src: ExprId) -> bool {
    kind == op::CALLDATACOPY && src == expr::env(op::CALLDATASIZE)
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

type Span = (Option<ExprId>, u64, u64);
type Whole = (ExprId, ExprId);
type RawRead = (ExprId, Option<ExprId>, Option<u32>);

fn span(off: ExprId, len: Option<u64>) -> Option<Span> {
    let (base, at) = expr::split_offset(off);
    let at = at.fits_u64().then(|| at.low_u64())?;
    Some((base, at, len.map_or(u64::MAX, |l| at.saturating_add(l))))
}

fn const_len(len: ExprId) -> Option<u64> {
    expr::as_const(len)
        .filter(U256::fits_u64)
        .map(|l| l.low_u64())
}

fn raw_reads(stmts: &[Stmt], term: &Term, readers: &HashSet<usize>) -> Vec<RawRead> {
    let mut reads = Vec::new();
    let word = Some(konst_u64(32));
    let loads = |e: ExprId, reads: &mut Vec<RawRead>| {
        if !expr::holds(e, kind::MLOAD | kind::KECCAK_MEM) {
            return;
        }
        let mut seen = HashSet::new();
        let mut stack = vec![e];
        while let Some(x) = stack.pop() {
            if !seen.insert(x) || seen.len() > 2000 {
                continue;
            }
            match expr::node(x) {
                Node::MLoad(at, version) => reads.push((at, word, Some(version))),
                Node::KeccakMem(at, len, version) => reads.push((at, Some(len), Some(version))),
                _ => {}
            }
            stack.extend(expr::children(x));
        }
    };
    for s in stmts {
        match s {
            Stmt::Log {
                off,
                len,
                data: None,
                ..
            } => reads.push((*off, Some(*len), None)),
            Stmt::Call {
                args: Some(args), ..
            } => {
                for arg in args {
                    if let Arg::Copied {
                        kind: op::MCOPY,
                        src,
                        len,
                    } = arg
                    {
                        reads.push((*src, Some(*len), None));
                    }
                }
            }
            /* The text gives the selector and the arguments it could read off the head.
            What follows them is read raw, and so is all of it when the head starts with
            no selector and the call prints as the memory it reads. */
            Stmt::Call {
                in_off,
                in_len,
                input: None,
                input_head,
                ..
            } => match crate::emit::call_head(input_head, *in_off) {
                Some((_, args)) => {
                    let given = U256::from(4 + 32 * args.len());
                    reads.push((expr::add_const(*in_off, given), None, None));
                }
                None => reads.push((*in_off, Some(*in_len), None)),
            },
            Stmt::Create {
                off,
                len,
                init: None,
                ..
            } => reads.push((*off, Some(*len), None)),
            Stmt::Copy {
                kind: op::MCOPY,
                src,
                len,
                ..
            } => reads.push((*src, Some(*len), None)),
            /* A helper that reads memory through a pointer may read from any place it is
            handed. A small number is a flag or a count, not a place. */
            Stmt::Internal { callee, args, .. } if readers.contains(callee) => {
                let place = |a: &&ExprId| expr::as_const(**a).is_none_or(|c| c.bits() > 6);
                reads.extend(args.iter().filter(place).map(|a| (*a, None, None)))
            }
            _ => {}
        }
        for e in stmt_exprs(s) {
            loads(e, &mut reads);
        }
    }
    match term {
        Term::Return {
            off,
            len,
            data: None,
        }
        | Term::Revert {
            off,
            len,
            data: None,
        } => {
            reads.push((*off, Some(*len), None));
        }
        _ => {}
    }
    for e in term_exprs(term) {
        loads(e, &mut reads);
    }
    reads
}

// A store is hidden when something decoded it, such as a hash that printed its input.
// A later read of the same bytes that was not decoded still needs to see the store,
// unless a write on the way to that read has already replaced the bytes it reads.
fn without_still_read(
    lnodes: &[Option<LNode>],
    hidden: HashSet<(usize, usize)>,
    readers: &HashSet<usize>,
) -> HashSet<(usize, usize)> {
    if hidden.is_empty() {
        return hidden;
    }
    let reads_any = |ln: &LNode| !raw_reads(&ln.stmts, &ln.term, readers).is_empty();
    if !lnodes.iter().flatten().any(reads_any) {
        return hidden;
    }
    let written = |s: &Stmt| -> Option<Span> {
        match s {
            Stmt::MStore { off, width, .. } => span(*off, Some(u64::from(*width))),
            Stmt::Call {
                out_off, out_len, ..
            } => span(*out_off, Some(const_len(*out_len)?)),
            Stmt::Copy { dest, len, .. } => span(*dest, Some(const_len(*len)?)),
            _ => None,
        }
    };
    // Several writes side by side cover a range together.
    let inside = |(base, lo, hi): Span, over: &[Span]| {
        let mut parts: Vec<(u64, u64)> = over
            .iter()
            .filter(|(b, l, h)| *b == base && *l < hi && lo < *h)
            .map(|(_, l, h)| (*l, *h))
            .collect();
        parts.sort_unstable();
        let mut reached = lo;
        for (l, h) in parts {
            if l > reached {
                break;
            }
            reached = reached.max(h);
        }
        reached >= hi
    };
    // The first value says a read of the store's bytes was met. The second says the walk
    // goes on past these statements.
    let scan = |(node, from): (usize, usize),
                gone: &HashSet<(usize, usize)>,
                (store, made): (Span, u32),
                over: &mut Vec<Span>|
     -> (bool, bool) {
        let Some(ln) = &lnodes[node] else {
            return (false, false);
        };
        let (stmts, term) = (&ln.stmts[from..], &ln.term);
        let seen = |reads: Vec<RawRead>, over: &[Span], same: &[Whole]| {
            reads.into_iter().any(|(off, len, version)| {
                // A read stamped before the store was made does not see it.
                if version.is_some_and(|v| v < made) {
                    return false;
                }
                // A read of exactly what a copy just wrote sees the copy and nothing older.
                if len.is_some_and(|len| same.contains(&(off, len))) {
                    return false;
                }
                let Some((base, lo, hi)) = span(off, len.map_or(Some(u64::MAX), const_len)) else {
                    return false;
                };
                let part = (base, lo.max(store.1), hi.min(store.2));
                base == store.0 && part.1 < part.2 && !inside(part, over)
            })
        };
        let mut same: Vec<Whole> = Vec::new();
        for (i, s) in stmts.iter().enumerate() {
            // A copy that is left out reads nothing. The call that prints it reads for it.
            let left_out = matches!(s, Stmt::Copy { .. }) && gone.contains(&(node, from + i));
            let reads = match left_out {
                true => Vec::new(),
                false => raw_reads(&stmts[i..=i], &Term::Stop, readers),
            };
            if seen(reads, over, &same) {
                return (true, false);
            }
            over.extend(written(s));
            match s {
                Stmt::Copy { dest, len, .. } => same.push((*dest, *len)),
                Stmt::Call {
                    out_off, out_len, ..
                } => same.push((*out_off, *out_len)),
                _ => {}
            }
            if inside(store, over) {
                return (false, false);
            }
        }
        (seen(raw_reads(&[], term, readers), over, &same), true)
    };
    let stays = |(node, index): &(usize, usize), gone: &HashSet<(usize, usize)>| {
        let Some(ln) = &lnodes[*node] else {
            return true;
        };
        let (off, width, gen) = match ln.stmts.get(*index) {
            Some(Stmt::MStore {
                off, width, gen, ..
            }) => (*off, Some(u64::from(*width)), *gen),
            Some(Stmt::Copy { dest, len, gen, .. }) => (*dest, const_len(*len), *gen),
            _ => return true,
        };
        let Some(store) = span(off, width) else {
            return true;
        };
        let store = (store, gen);
        let mut over = Vec::new();
        let (read, on) = scan((*node, index + 1), gone, store, &mut over);
        if read || !on {
            return !read;
        }
        let mut seen = HashSet::new();
        let mut stack: Vec<(usize, Vec<Span>)> =
            ln.succs.iter().map(|s| (*s, over.clone())).collect();
        while let Some((x, mut over)) = stack.pop() {
            if !seen.insert(x) || seen.len() > MAX_NODES_AFTER_STORE {
                continue;
            }
            let Some(next) = &lnodes[x] else {
                continue;
            };
            let (read, on) = scan((x, 0), gone, store, &mut over);
            if read {
                return false;
            }
            if on {
                stack.extend(next.succs.iter().map(|s| (*s, over.clone())));
            }
        }
        true
    };
    // A store that stays is read again by what it was thought to be left out for.
    let mut gone = hidden;
    loop {
        let kept: HashSet<(usize, usize)> =
            gone.iter().filter(|at| stays(at, &gone)).copied().collect();
        if kept.len() == gone.len() {
            return kept;
        }
        gone = kept;
    }
}

const MAX_NODES_AFTER_STORE: usize = 512;

// A version taken at a merge has to be the same every time the node is merged, or a loop
// that writes memory or storage raises it on every round and never settles. It also has
// to be above every version that reaches the node along a forward edge. Nodes are ranked
// in reverse postorder and each rank owns a range, which gives both.
const VERSIONS_PER_NODE: u32 = 1 << 14;
const MAX_RUNS_PER_NODE: usize = 24;

fn stable_versions(unit: &Unit) -> Vec<u32> {
    let n = unit.nodes.len();
    let mut order = Vec::with_capacity(n);
    let mut seen = vec![false; n];
    let mut stack: Vec<(usize, usize)> = vec![(unit.entry, 0)];
    seen[unit.entry] = true;
    while let Some((x, next)) = stack.last().copied() {
        let Some((s, _)) = unit.nodes[x].succs.get(next).copied() else {
            order.push(x);
            stack.pop();
            continue;
        };
        stack.last_mut().expect("just read").1 += 1;
        if !seen[s] {
            seen[s] = true;
            stack.push((s, 0));
        }
    }
    let mut stable = vec![u32::MAX; n];
    for (rank, node) in order.iter().rev().enumerate() {
        stable[*node] = (rank as u32 + 1).saturating_mul(VERSIONS_PER_NODE);
    }
    stable
}

// What reaches a node along a forward edge is below the node's stable version, so only a
// back edge can bring a higher one, and that one is a later pass over the same node.
// An entry already past its stable version came from a block with more writes than a
// rank's range, and then the old rule of one above both is the safe one.
fn merged_version(mine: u32, theirs: u32, stable: u32) -> u32 {
    if mine <= stable {
        stable
    } else {
        mine.max(theirs) + 1
    }
}

// The id is made from the place the variable stands for. A running count packed into a
// few bits came round again after enough merges and gave two places one variable.
fn merge_var(node: usize, from_top: usize) -> ExprId {
    match u32::try_from(from_top) {
        Ok(depth) if depth < 1 << 10 && node < 1 << 22 => expr::var(((node as u32) << 10) | depth),
        _ => expr::intern(Node::Unknown(expr::next_seq())),
    }
}

fn merge_into(
    e: &mut Entry,
    exit: &State,
    node: usize,
    stable: u32,
    phi_ids: &mut HashMap<(usize, usize), ExprId>,
) -> bool {
    let mut changed = false;
    let el = e.state.stack.len();
    let xl = exit.stack.len();
    if xl > el {
        let extra = xl - el;
        let as_args: Vec<ExprId> = (0..extra)
            .map(|i| {
                let from_top = xl - 1 - i;
                expr::arg((e.state.args_used + (from_top - el)) as u32)
            })
            .collect();
        let exit_matches = as_args.iter().enumerate().all(|(i, a)| exit.stack[i] == *a);
        let mut new_bottom = Vec::with_capacity(extra);
        let mut new_phis = Vec::with_capacity(extra);
        for (i, a) in as_args.iter().enumerate() {
            if exit_matches {
                new_bottom.push(*a);
                new_phis.push(false);
            } else {
                let from_top = xl - 1 - i;
                let var = *phi_ids
                    .entry((node, from_top))
                    .or_insert_with(|| merge_var(node, from_top));
                new_bottom.push(var);
                new_phis.push(true);
            }
        }
        if exit_matches {
            e.state.args_used += extra;
        }
        let mut stack = new_bottom;
        stack.extend(e.state.stack.iter().copied());
        let mut phis = new_phis;
        phis.extend(e.phis.iter().copied());
        e.state.stack = stack;
        e.phis = phis;
        changed = true;
    }
    let el = e.state.stack.len();
    let mut caps: Vec<(ExprId, u32)> = Vec::new();
    let mut uncapped: Vec<ExprId> = Vec::new();
    for k in 0..el {
        let from_top = el - 1 - k;
        let exit_val = if from_top < xl {
            exit.stack[xl - 1 - from_top]
        } else {
            expr::arg((exit.args_used + from_top - xl) as u32)
        };
        let old = e.state.stack[k];
        if e.phis[k] {
            let cap = e.state.mem.capped.iter().find(|(v, _)| *v == old);
            if let Some((_, stamp)) = cap.copied() {
                match exit_val == old || exit.mem.at_most_answer(exit_val, stamp) {
                    true => caps.push((old, stamp)),
                    false => uncapped.push(old),
                }
            }
            continue;
        }
        if exit_val != old {
            let var = *phi_ids
                .entry((node, from_top))
                .or_insert_with(|| merge_var(node, from_top));
            let stamp = answer_stamp(old).or(answer_stamp(exit_val));
            let below = |stamp: &u32| {
                e.state.mem.at_most_answer(old, *stamp) && exit.mem.at_most_answer(exit_val, *stamp)
            };
            caps.extend(stamp.filter(below).map(|stamp| (var, stamp)));
            e.state.stack[k] = var;
            e.phis[k] = true;
            changed = true;
        }
    }
    let capped = e.state.mem.capped.clone();
    if !e.widened && e.state.mem.intersect(&exit.mem, stable) {
        changed = true;
    }
    /* The smaller of a length and a number is how code bounds what it copies of an answer.
    A value merged here from that length and from numbers the length was tested to reach
    is no more than the length on every way in. */
    let merged = &mut e.state.mem.capped;
    merged.retain(|(var, _)| !uncapped.contains(var));
    for cap in caps {
        if !merged.contains(&cap) {
            merged.push(cap);
        }
    }
    changed |= *merged != capped;
    let before = e.state.storage.len();
    e.state.storage.retain(|w| exit.storage.contains(w));
    if e.state.storage.len() != before {
        changed = true;
    }
    if exit.args_used > e.state.args_used {
        e.state.args_used = exit.args_used;
    }
    if exit.sgen != e.state.sgen && !e.widened {
        let merged = merged_version(e.state.sgen, exit.sgen, stable);
        changed |= merged != e.state.sgen;
        e.state.sgen = merged;
    }
    let merged_return = match exit.returned == e.state.returned {
        true => exit.returned,
        false => MERGED_RETURN | node as u32,
    };
    if merged_return != e.state.returned {
        e.state.returned = merged_return;
        changed = true;
    }
    if exit.called && !e.state.called {
        e.state.called = true;
        changed = true;
    }
    changed
}

fn loop_bound(cond: ExprId) -> Option<ExprId> {
    match expr::node(cond) {
        Node::Op(op::LT, v) => Some(v[1]),
        Node::Op(op::GT, v) => Some(v[0]),
        Node::Op(op::ISZERO, v) => loop_bound(v[0]),
        _ => None,
    }
}

fn fold_keccak(words: &[ExprId], tail: u8) -> Option<U256> {
    let mut bytes = Vec::with_capacity(words.len() * 32);
    for (i, w) in words.iter().enumerate() {
        let c = expr::as_const(*w)?;
        let b = c.to_be_bytes();
        if tail > 0 && i == words.len() - 1 {
            bytes.extend_from_slice(&b[32 - tail as usize..]);
        } else {
            bytes.extend_from_slice(&b);
        }
    }
    Some(U256::from_be_bytes(&crate::keccak::keccak256(&bytes)))
}

fn apply_mcopy(
    st: &mut State,
    dest: ExprId,
    src: ExprId,
    len: ExprId,
    origin: Option<(usize, usize)>,
) {
    let l = expr::as_const(len)
        .and_then(|v| v.as_usize())
        .map(|v| v as u64);
    if let Some(l) = l {
        if let Some((words, tail)) = st.mem.read_region(src, l, st.version) {
            let mut i = 0u64;
            for (k, w) in words.iter().enumerate() {
                let is_tail = tail > 0 && k == words.len() - 1;
                if !is_tail {
                    st.mem.store(
                        expr::add_const(dest, U256::from(i)),
                        Some(32),
                        MVal::Word(*w),
                    );
                    i += 32;
                }
            }
            if tail > 0 {
                st.mem.store(
                    expr::add_const(dest, U256::from(i)),
                    Some(tail as u64),
                    MVal::Copy(op::MCOPY, expr::add_const(src, U256::from(i)), None),
                );
            }
        } else {
            st.mem
                .store_copy(dest, len, MVal::Copy(op::MCOPY, src, None), origin);
        }
    } else {
        st.mem
            .store_copy(dest, len, MVal::Copy(op::MCOPY, src, None), origin);
    }
    st.mem.tick();
    st.version = st.mem.gen;
}

impl Lifted {
    #[must_use]
    pub fn reads_through_pointers(&self) -> bool {
        self.entry_loads.open_from.is_some()
    }

    #[must_use]
    pub fn entry_free_pointer(&self) -> Option<ExprId> {
        let unit_entry = self
            .node_map
            .iter()
            .find(|(_, lifted)| **lifted == self.entry)
            .map(|(unit, _)| *unit)?;
        let state = self.entry_states.get(unit_entry)?.as_ref()?;
        Some(
            state
                .mem
                .load_word(konst(U256::from_u64(FREE_POINTER)), state.version),
        )
    }
}

pub fn always_reverts(l: &Lifted, start: usize) -> bool {
    let mut seen = HashSet::new();
    let mut stack = vec![start];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 2000 {
            continue;
        }
        match &l.nodes[x].term {
            Term::Revert { .. } | Term::Invalid => {}
            Term::Return { .. }
            | Term::ReturnDyn { .. }
            | Term::Stop
            | Term::InternalReturn(_)
            | Term::SelfDestruct(_)
            | Term::Unresolved(_) => return false,
            _ => stack.extend(l.nodes[x].succs.iter().copied()),
        }
    }
    true
}

pub fn map_stmt(s: &Stmt, f: &dyn Fn(ExprId) -> ExprId) -> Stmt {
    let fv = |v: &Vec<ExprId>| v.iter().map(|e| f(*e)).collect::<Vec<_>>();
    let fo = |v: &Option<Vec<ExprId>>| v.as_ref().map(fv);
    match s {
        Stmt::Assign { var, value } => Stmt::Assign {
            var: f(*var),
            value: f(*value),
        },
        Stmt::MStore {
            off,
            val,
            width,
            gen,
        } => Stmt::MStore {
            off: f(*off),
            val: f(*val),
            width: *width,
            gen: *gen,
        },
        Stmt::SStore {
            key,
            val,
            transient,
            gen,
        } => Stmt::SStore {
            key: f(*key),
            val: f(*val),
            transient: *transient,
            gen: *gen,
        },
        Stmt::Log {
            off,
            len,
            topics,
            data,
        } => Stmt::Log {
            off: f(*off),
            len: f(*len),
            topics: fv(topics),
            data: fo(data),
        },
        Stmt::Call {
            seq,
            kind,
            gas,
            addr,
            value,
            in_off,
            in_len,
            out_off,
            out_len,
            input,
            input_head,
            layout,
            args,
            result,
            gen,
        } => Stmt::Call {
            seq: *seq,
            kind: *kind,
            gas: f(*gas),
            addr: f(*addr),
            value: value.map(f),
            in_off: f(*in_off),
            in_len: f(*in_len),
            out_off: f(*out_off),
            out_len: f(*out_len),
            input: fo(input),
            input_head: fv(input_head),
            layout: layout
                .as_ref()
                .map(|l| l.iter().map(|(e, width)| (f(*e), *width)).collect()),
            args: args
                .as_ref()
                .map(|all| all.iter().map(|a| a.map(f)).collect()),
            result: f(*result),
            gen: *gen,
        },
        Stmt::Create {
            seq,
            kind,
            value,
            off,
            len,
            salt,
            result,
            init,
            gen,
        } => Stmt::Create {
            seq: *seq,
            kind: *kind,
            value: f(*value),
            off: f(*off),
            len: f(*len),
            salt: salt.map(f),
            result: f(*result),
            init: fo(init),
            gen: *gen,
        },
        Stmt::Copy {
            kind,
            dest,
            src,
            len,
            addr,
            gen,
        } => Stmt::Copy {
            kind: *kind,
            dest: f(*dest),
            src: f(*src),
            len: f(*len),
            addr: addr.map(f),
            gen: *gen,
        },
        Stmt::Internal {
            seq,
            callee,
            args,
            results,
            gen,
        } => Stmt::Internal {
            seq: *seq,
            callee: *callee,
            args: fv(args),
            results: fv(results),
            gen: *gen,
        },
        Stmt::Drop(e) => Stmt::Drop(f(*e)),
        Stmt::Require {
            cond,
            data,
            invalid,
        } => Stmt::Require {
            cond: f(*cond),
            data: fo(data),
            invalid: *invalid,
        },
    }
}

pub fn map_term(t: &Term, f: &dyn Fn(ExprId) -> ExprId) -> Term {
    let fv = |v: &Vec<ExprId>| v.iter().map(|e| f(*e)).collect::<Vec<_>>();
    match t {
        Term::Jump(x) => Term::Jump(*x),
        Term::Branch { cond, t, f: fl } => Term::Branch {
            cond: f(*cond),
            t: *t,
            f: *fl,
        },
        Term::Switch { target, cases } => Term::Switch {
            target: f(*target),
            cases: cases.clone(),
        },
        Term::Return { off, len, data } => Term::Return {
            off: f(*off),
            len: f(*len),
            data: data.as_ref().map(fv),
        },
        Term::ReturnDyn { ptr } => Term::ReturnDyn { ptr: f(*ptr) },
        Term::Revert { off, len, data } => Term::Revert {
            off: f(*off),
            len: f(*len),
            data: data.as_ref().map(fv),
        },
        Term::Stop => Term::Stop,
        Term::Invalid => Term::Invalid,
        Term::SelfDestruct(a) => Term::SelfDestruct(f(*a)),
        Term::InternalReturn(vals) => Term::InternalReturn(fv(vals)),
        Term::Unresolved(x) => Term::Unresolved(f(*x)),
        Term::CondJump { cond, target } => Term::CondJump {
            cond: f(*cond),
            target: f(*target),
        },
        Term::Infeasible => Term::Infeasible,
    }
}

pub fn node_exprs(n: &LNode) -> Vec<ExprId> {
    let mut v: Vec<ExprId> = n.stmts.iter().flat_map(stmt_exprs).collect();
    v.extend(term_exprs(&n.term));
    v
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Root {
    pub expr: ExprId,
    // A mask or shift at the root of a payload word is encoding, not a type.
    pub payload: bool,
}

pub fn roots(n: &LNode) -> Vec<Root> {
    let payload: HashSet<ExprId> = payload_exprs(n).into_iter().collect();
    node_exprs(n)
        .into_iter()
        .map(|expr| Root {
            expr,
            payload: payload.contains(&expr),
        })
        .collect()
}

pub fn payload_exprs(n: &LNode) -> Vec<ExprId> {
    let mut v = Vec::new();
    for s in &n.stmts {
        match s {
            Stmt::Call {
                input,
                input_head,
                layout,
                args,
                ..
            } => {
                v.extend(input_head.iter().copied());
                v.extend(args.iter().flatten().flat_map(Arg::exprs));
                match (input, layout) {
                    (Some(d), _) => v.extend(d.iter().copied()),
                    (None, Some(pieces)) => v.extend(pieces.iter().map(|(e, _)| *e)),
                    (None, None) => {}
                }
            }
            Stmt::Log { data: Some(d), .. }
            | Stmt::Create { init: Some(d), .. }
            | Stmt::Require { data: Some(d), .. } => v.extend(d.iter().copied()),
            _ => {}
        }
    }
    if let Term::Revert { data: Some(d), .. } = &n.term {
        v.extend(d.iter().copied());
    }
    v
}

pub fn stmt_exprs(s: &Stmt) -> Vec<ExprId> {
    let mut v = Vec::new();
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
        Stmt::Log {
            off,
            len,
            topics,
            data,
        } => {
            v.push(*off);
            v.push(*len);
            v.extend(topics.iter().copied());
            if let Some(d) = data {
                v.extend(d.iter().copied());
            }
        }
        Stmt::Call {
            gas,
            addr,
            value,
            in_off,
            in_len,
            out_off,
            out_len,
            input,
            layout,
            args,
            ..
        } => {
            v.extend(args.iter().flatten().flat_map(Arg::exprs));
            v.push(*gas);
            v.push(*addr);
            if let Some(x) = value {
                v.push(*x);
            }
            v.extend([*in_off, *in_len, *out_off, *out_len]);
            // The pieces say again what the words say, so they are listed only without them.
            match (input, layout) {
                (Some(d), _) => v.extend(d.iter().copied()),
                (None, Some(pieces)) => v.extend(pieces.iter().map(|(e, _)| *e)),
                (None, None) => {}
            }
        }
        Stmt::Create {
            value,
            off,
            len,
            salt,
            init,
            ..
        } => {
            v.extend([*value, *off, *len]);
            if let Some(s) = salt {
                v.push(*s);
            }
            if let Some(d) = init {
                v.extend(d.iter().copied());
            }
        }
        Stmt::Copy {
            dest,
            src,
            len,
            addr,
            ..
        } => {
            v.extend([*dest, *src, *len]);
            if let Some(a) = addr {
                v.push(*a);
            }
        }
        Stmt::Internal { args, .. } => v.extend(args.iter().copied()),
        Stmt::Drop(e) => v.push(*e),
        Stmt::Require { cond, data, .. } => {
            v.push(*cond);
            if let Some(d) = data {
                v.extend(d.iter().copied());
            }
        }
    }
    v
}

pub fn term_exprs(t: &Term) -> Vec<ExprId> {
    let mut v = Vec::new();
    match t {
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
        Term::ReturnDyn { ptr } => v.push(*ptr),
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

pub fn jump_target_bits(e: ExprId) -> Option<U256> {
    target_bits(e, &mut HashMap::new())
}

// An expression is shared, so without the memo a value used on both sides of
// each of n operators would be walked 2^n times.
fn target_bits(e: ExprId, memo: &mut HashMap<ExprId, Option<U256>>) -> Option<U256> {
    if let Some(known) = memo.get(&e) {
        return *known;
    }
    let out = target_bits_of(e, memo);
    memo.insert(e, out);
    out
}

fn target_bits_of(e: ExprId, memo: &mut HashMap<ExprId, Option<U256>>) -> Option<U256> {
    match expr::node(e) {
        Node::Const(c) => Some(c),
        Node::Op(op::AND, v) => {
            let (a, b) = (target_bits(v[0], memo), target_bits(v[1], memo));
            match (a, b) {
                (Some(x), Some(y)) => Some(x & y),
                (Some(x), None) | (None, Some(x)) => Some(x),
                _ => None,
            }
        }
        Node::Op(op::OR, v) | Node::Op(op::XOR, v) | Node::Op(op::ADD, v) => {
            let a = target_bits(v[0], memo)?;
            let b = target_bits(v[1], memo)?;
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
            Some(target_bits(v[1], memo)? << k.low_u64() as u32)
        }
        Node::Op(op::MUL, v) => {
            let (x, c) = if let Some(c) = expr::as_const(v[1]) {
                (v[0], c)
            } else {
                (v[1], expr::as_const(v[0])?)
            };
            if !c.is_power_of_two() {
                return None;
            }
            Some(target_bits(x, memo)? << c.trailing_zeros())
        }
        Node::Op(op::SHR, v) => {
            let k = expr::as_const(v[0])?;
            if k >= U256::from_u64(256) {
                return Some(U256::ZERO);
            }
            Some(target_bits(v[1], memo)? >> k.low_u64() as u32)
        }
        Node::Op(op::BYTE, _) => Some(U256::from_u64(0xff)),
        Node::Op(op::DIV, v) => {
            let c = expr::as_const(v[1])?;
            if !c.is_power_of_two() {
                return None;
            }
            Some(target_bits(v[0], memo)? >> c.trailing_zeros())
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

pub fn jump_candidates(e: ExprId, jumpdests: &HashSet<usize>, code_len: usize) -> Vec<usize> {
    let mut out: HashSet<usize> = HashSet::new();
    let leaves = unknown_leaves(e);
    if leaves.len() == 1
        && !matches!(
            expr::node(leaves[0]),
            Node::Arg(_) | Node::Var(_) | Node::IntRet(..) | Node::Unknown(_)
        )
    {
        let leaf = leaves[0];
        let mut samples: Vec<U256> = (0..=1024u64).map(U256::from_u64).collect();
        for k in 0..256u32 {
            samples.push(U256::ONE << k);
            samples.push(expr::mask_bits(k));
        }
        samples.push(U256::MAX);
        for v in samples {
            let mut memo = HashMap::new();
            let r = expr::substitute(
                e,
                &|n| {
                    if std::ptr::eq(n, n) && expr::intern(n.clone()) == leaf {
                        Some(konst(v))
                    } else {
                        None
                    }
                },
                &mut memo,
            );
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

// Kept as a loop. One call per node ran out of stack on a long chain of blocks.
pub fn reverse_postorder(l: &Lifted) -> Vec<usize> {
    let mut order = Vec::new();
    let mut seen = HashSet::from([l.entry]);
    let mut stack: Vec<(usize, usize)> = vec![(l.entry, 0)];
    while let Some((x, next)) = stack.last().copied() {
        let Some(s) = l.nodes[x].succs.get(next).copied() else {
            order.push(x);
            stack.pop();
            continue;
        };
        stack.last_mut().expect("just read").1 += 1;
        if seen.insert(s) {
            stack.push((s, 0));
        }
    }
    order.reverse();
    order
}

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decompile::{decompile, Options};

    fn statements(code_hex: &str) -> Vec<Stmt> {
        let code = crate::hex::decode(code_hex).expect("hex");
        let c = decompile(&code, &Options::default());
        let lifted = c.functions.iter().find_map(|f| f.lifted.as_ref());
        let nodes = &lifted.expect("the code is lifted").nodes;
        nodes.iter().flat_map(|n| n.stmts.clone()).collect()
    }

    fn stored(stmts: &[Stmt]) -> Vec<ExprId> {
        let values = stmts.iter().filter_map(|s| match s {
            Stmt::SStore { val, .. } => Some(*val),
            _ => None,
        });
        values.collect()
    }

    #[test]
    fn an_answer_longer_than_any_length_names_no_length() {
        let size = expr::intern(Node::Env(op::RETURNDATASIZE, 1));
        let longer = expr::op2(op::GT, size, expr::konst_u64(u64::MAX));
        assert_eq!(answer_length(longer, true, &[]), None);
        assert_eq!(answer_length(longer, false, &[]), None);
    }

    #[test]
    fn a_memory_copy_is_lifted_as_a_copy_of_its_kind() {
        let stmts = statements("6020600060405e00");
        let copy = stmts.iter().find_map(|s| match s {
            Stmt::Copy { kind, len, .. } => Some((*kind, expr::as_const(*len))),
            _ => None,
        });
        assert_eq!(copy, Some((op::MCOPY, Some(U256::from_u64(0x20)))));
    }

    #[test]
    fn a_balance_read_after_a_call_is_not_the_one_read_before_it() {
        let stmts = statements("3031600055600080808080335af1503031600155");
        let values = stored(&stmts);
        assert_eq!(values.len(), 2);
        assert_ne!(values[0], values[1]);
    }

    #[test]
    fn a_balance_read_twice_with_nothing_between_is_one_value() {
        let values = stored(&statements("30313031600055600155"));
        assert_eq!(values.len(), 2);
        assert_eq!(values[0], values[1]);
    }

    #[test]
    fn two_calls_at_two_places_have_two_numbers() {
        let stmts = statements("600080808080335af150600080808080335af15000");
        let sites: Vec<u32> = stmts
            .iter()
            .filter_map(|s| match s {
                Stmt::Call { seq, .. } => Some(call_site(*seq)),
                _ => None,
            })
            .collect();
        assert_eq!(sites.len(), 2);
        assert_ne!(sites[0], sites[1]);
    }
}
