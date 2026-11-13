use crate::cfg::{AState, AVal, Edge, Program, UNode, Unit};
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
    CallOut(u32),
    Unknown,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct MemWrite {
    base: Option<ExprId>,
    off: u64,
    len: Option<u64>,
    val: MVal,
    origin: Option<(usize, usize)>,
    gen: u32,
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
    single_run: bool,
}

const BIG: u64 = 1 << 40;

const MERGED_RETURN: u32 = 1 << 31;

// Must be stable across the rounds a node is lifted in, and never zero.
fn call_stamp(node: usize, index: usize) -> u32 {
    ((node as u32) << 10 | (index as u32 & 0x3ff)).wrapping_add(1) & !MERGED_RETURN
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

// Sound only because an unknown pointer is unsigned and memory never wraps.
// So p + k lies at or above k. It also never points into the scratch area below 0x80.
fn may_alias(
    wb: Option<ExprId>,
    woff: u64,
    wlen: Option<u64>,
    rb: Option<ExprId>,
    roff: u64,
    rlen: u64,
) -> bool {
    let w_wild = wb.is_some_and(wild_base);
    let r_wild = rb.is_some_and(wild_base);
    let above = |wild: ExprId, fixed: ExprId| -> Option<u64> {
        let mut terms = Vec::new();
        let mut stack = vec![wild];
        while let Some(x) = stack.pop() {
            match expr::node(x) {
                Node::Op(o, v) if o == op::ADD => {
                    stack.push(v[0]);
                    stack.push(v[1]);
                }
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
            } else if !wild_base(t) {
                return None;
            }
        }
        Some(k)
    };
    if w_wild {
        let Some(rbase) = rb else {
            return roff >= 0x80 && roff + rlen > woff;
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
            return woff >= 0x80 && wlen.is_none_or(|l| woff + l > roff);
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
    fn new(fresh: bool) -> Mem {
        Mem {
            writes: Vec::new(),
            fresh,
            gen: 0,
            clobber_gen: 0,
            written: BTreeSet::new(),
            entry_loads: Rc::default(),
            touched: Rc::default(),
            single_run: false,
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
        }
        self.writes.push(MemWrite {
            base,
            off: d,
            len,
            val,
            origin,
            gen: self.gen + 1,
        });
    }

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

    fn clobber(&mut self) {
        self.touched.borrow_mut().anywhere = true;
        self.writes.clear();
        self.fresh = false;
        self.gen += 1;
        self.clobber_gen = self.gen;
    }

    fn load_bytes(&self, off: ExprId, n: u64, version: u32) -> Option<ExprId> {
        let (base, d) = norm_offset(off);
        let mut pieces: Vec<Option<(ExprId, u64)>> = vec![None; n as usize];
        let mut copy_hit: Option<(u8, ExprId, Option<ExprId>, u64, u32)> = None;
        let mut covered = 0usize;
        for w in self.writes.iter().rev() {
            if covered == n as usize {
                break;
            }
            if w.base != base {
                // One run cannot tell where an input-sized offset lands.
                // It is taken to miss a fixed address and the re-run catches a wrong guess.
                let guessed = self.single_run && base.is_none() && w.base.is_some();
                if !guessed && may_alias(w.base, w.off, w.len, base, d, n) {
                    return None;
                }
                continue;
            }
            let Some(wl) = w.len else {
                if d + n <= w.off {
                    continue;
                }
                // A read past the copied length is a wrong guess here.
                // Every answer built on it is run again on the bytecode.
                if let (true, 0, MVal::Copy(k, src, addr)) = (self.single_run, covered, &w.val) {
                    if d >= w.off {
                        copy_hit = Some((*k, *src, *addr, d - w.off, w.gen));
                        break;
                    }
                }
                return None;
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
        let _ = version;
        if let Some((k, src, _addr, delta, wgen)) = copy_hit {
            let word = expr::intern(Node::CopiedWord(
                k,
                expr::add_const(src, U256::from(delta)),
                wgen,
            ));
            return Some(if n == 32 {
                word
            } else {
                op2(op::SHR, konst_u64(8 * (32 - n)), word)
            });
        }
        let mut unknown_mask = U256::ZERO;
        if covered < n as usize {
            let zero_ok = self.fresh && !base.is_some_and(wild_base);
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

    fn intersect(&mut self, other: &Mem) -> bool {
        let fresh_before = self.fresh;
        let gen_before = self.gen;
        let same = |a: &MemWrite, b: &MemWrite| {
            a.base == b.base && a.off == b.off && a.len == b.len && a.val == b.val
        };
        let identical = self.gen == other.gen
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
        for w in &self.writes {
            let (agrees, latest) = at(&theirs, &other.writes, w);
            if agrees {
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
        let mut placed: HashSet<Place> = mine.keys().copied().collect();
        for o in &other.writes {
            let (agrees, _) = at(&mine, &self.writes, o);
            if !agrees && placed.insert(place(o)) {
                merged.push(MemWrite {
                    val: MVal::Unknown,
                    origin: None,
                    ..o.clone()
                });
            }
        }
        let overflow = merged.len().saturating_sub(MAX_TRACKED_WRITES);
        merged.drain(..overflow);
        let changed_writes = merged.len() != self.writes.len()
            || merged
                .iter()
                .zip(self.writes.iter())
                .any(|(a, b)| !(same(a, b)));
        self.writes = merged;
        let written_before = self.written.len();
        self.written.retain(|r| other.written.contains(r));
        let changed_writes = changed_writes || self.written.len() != written_before;
        self.fresh &= other.fresh && overflow == 0;
        if overflow > 0 || other.gen != self.gen || other.clobber_gen != self.clobber_gen {
            self.gen = self.gen.max(other.gen) + 1;
            self.clobber_gen = self.gen;
        }
        changed_writes || fresh_before != self.fresh || gen_before != self.gen
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

#[derive(Debug)]
pub struct Lifter<'a> {
    pub prog: &'a Program,
    pub root: bool,
    pub summaries: HashMap<usize, CalleeSummary>,
    pub footprints: HashMap<usize, MemoryWrites>,
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
    pub copies: Vec<(ExprId, ExprId, ExprId)>,
    pub maybe_mstores: Vec<ExprId>,
}

fn fail_summary(code: u32) -> Option<CalleeSummary> {
    if std::env::var("EVMDEC_DEBUG_SUMMARY").is_ok() {
        eprintln!("[summary] not summarisable (reason {})", code);
    }
    None
}

pub fn summarize(l: &Lifted) -> Option<CalleeSummary> {
    let mut n = l.entry;
    let mut seen = HashSet::new();
    let mut sum = CalleeSummary::default();
    loop {
        if !seen.insert(n) || seen.len() > 64 {
            return fail_summary(1);
        }
        let nd = &l.nodes[n];
        for s in &nd.stmts {
            match s {
                Stmt::MStore {
                    off,
                    val,
                    width: 32,
                    ..
                } => sum.mstores.push((*off, *val)),
                Stmt::MStore { .. } => return fail_summary(201),
                Stmt::Copy {
                    kind: op::MCOPY,
                    dest,
                    src,
                    len,
                    ..
                } => sum.copies.push((*dest, *src, *len)),
                Stmt::Copy { .. }
                | Stmt::Internal { .. }
                | Stmt::Call { .. }
                | Stmt::Create { .. } => return fail_summary(202),
                Stmt::SStore { .. } | Stmt::Log { .. } => sum.side_effects = true,
                Stmt::Require {
                    cond,
                    data,
                    invalid,
                } => sum.guards.push((*cond, data.clone(), *invalid)),
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
                return if ok { Some(sum) } else { fail_summary(100) };
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
                                return if ok { Some(sum) } else { fail_summary(100) };
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
                        sum.guards.push((op1(op::ISZERO, *cond), d, inv));
                        n = *f;
                    }
                    Some(t) if rev(*f) && !rev(*t) => {
                        let (d, inv) = payload(*f);
                        sum.guards.push((*cond, d, inv));
                        n = *t;
                    }
                    None => {
                        sum.guards.push((op1(op::ISZERO, *cond), None, true));
                        n = *f;
                    }
                    _ => return fail_summary(204),
                }
            }
            _ => return fail_summary(205),
        }
    }
}

#[derive(Default)]
struct Hidden {
    // Cleared each time the node is re-run.
    // A decode that only succeeded on an early run must not hide stores for good.
    by_node: RefCell<HashMap<usize, HashSet<(usize, usize)>>>,
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
}

impl<'a> Lifter<'a> {
    pub fn lift(&self, unit: &Unit, initial: Option<(Vec<ExprId>, bool)>) -> Lifted {
        let (init_stack, fresh) = initial.unwrap_or((Vec::new(), self.root));
        let state = State {
            stack: init_stack,
            args_used: 0,
            mem: Mem::new(fresh),
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
        if std::env::var("EVMDEC_DEBUG_LOOPS").is_ok() {
            eprintln!(
                "[loops] unit entry block {} ({:#x}): {} copy loop(s) {:?}",
                unit.entry_block,
                self.prog.blocks[unit.entry_block].start,
                loops.len(),
                loops
                    .iter()
                    .map(|c| (c.entry, c.latch, c.body, c.exit))
                    .collect::<Vec<_>>()
            );
        }
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

    pub fn lift_trace(&self, blocks: &[usize]) -> Vec<LNode> {
        let unit = Unit {
            entry_block: blocks.first().copied().unwrap_or(0),
            nodes: blocks
                .iter()
                .enumerate()
                .map(|(id, block)| UNode {
                    id,
                    block: *block,
                    entry: AState::new(),
                    succs: vec![],
                    preds: vec![],
                    call: None,
                    returns_via: None,
                    unresolved: true,
                    infeasible: false,
                    computed_cut: false,
                })
                .collect(),
            entry: 0,
            budget_exhausted: false,
        };
        let mut state = State {
            stack: Vec::new(),
            args_used: 0,
            mem: Mem::new(true),
            storage: Vec::new(),
            version: 0,
            sgen: 0,
            called: false,
            returned: 0,
        };
        state.mem.single_run = true;
        let hidden = Hidden::default();
        let mut out = Vec::with_capacity(blocks.len());
        for id in 0..blocks.len() {
            let (node, next) = self.run_node(&unit, id, &state, &hidden);
            state = next;
            out.push(node);
        }
        out
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
        let mut phi_ids: HashMap<(usize, usize), ExprId> = HashMap::new();
        let mut next_var: u32 = 0;
        let mut work: VecDeque<usize> = VecDeque::new();
        let mut queued = vec![false; n];
        let mut reprocess_count = 0usize;

        let hidden = Hidden::default();
        let init_len = init.stack.len();
        entries[unit.entry] = Some(Entry {
            state: init,
            phis: vec![false; init_len],
        });
        work.push_back(unit.entry);
        queued[unit.entry] = true;
        let mut max_args = 0usize;

        while let Some(nid) = work.pop_front() {
            crate::clock::check();
            queued[nid] = false;
            runs[nid] += 1;
            if runs[nid] > 24 {
                continue;
            }
            if runs[nid] > 1 {
                reprocess_count += 1;
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
                        if let Some((stmt, after)) =
                            self.summarize_copy_loop(unit, cl, &exit, &hidden)
                        {
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
            lnodes[nid] = Some(lnode);
            exit_states[nid] = Some(exit.clone());
            let exit_all = exit;
            for s in succs {
                let exit = succ_state.get(&s).unwrap_or(&exit_all).clone();
                let single_pred = unit.nodes[s].preds.len() <= 1;
                let changed = match &mut entries[s] {
                    None => {
                        entries[s] = Some(Entry {
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
                            || e.state.storage != new_state.storage
                            || e.state.sgen != new_state.sgen
                            || e.state.returned != new_state.returned;
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

        let hidden_set = hidden.all();
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
                            Stmt::MStore { .. } => !hidden_set.contains(&(i, idx)),
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
                let mut assigns = Vec::new();
                let el = entry.state.stack.len();
                let xl = exit.stack.len();
                for (k, is_phi) in entry.phis.iter().enumerate() {
                    if !*is_phi {
                        continue;
                    }
                    let from_top = el - 1 - k;
                    let var = entry.state.stack[k];
                    let val = if from_top < xl {
                        exit.stack[xl - 1 - from_top]
                    } else {
                        expr::intern(Node::Unknown(expr::next_seq()))
                    };
                    if val != var {
                        assigns.push((var, val));
                    }
                }
                if !assigns.is_empty() {
                    edge_assigns.insert((from, to), assigns);
                }
            }
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
        let ret_slot = unit.nodes.iter().find_map(|n| match n.returns_via {
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
            entry: map[&unit.entry],
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
                apply_mcopy(&mut st, dst0, src0, count);
                let stmt = Stmt::Copy {
                    kind: op::MCOPY,
                    dest: dst0,
                    src: src0,
                    len: count,
                    addr: None,
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
                apply_mcopy(&mut st, dst, src, whole);
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
        let mut underflow = false;
        let seq_base = (nid as u32) << 10;
        let mut seq_ctr = 0u32;
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
            };
            return (ln, st);
        }

        for ins in prog.block_insns(blk) {
            crate::clock::check();
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
                    st.stack.push(if own {
                        expr::intern(Node::Env(op::SELFBALANCE, st.sgen))
                    } else {
                        expr::intern(Node::Op(o, vec![a]))
                    });
                }
                op::ISZERO | op::NOT => {
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
                                    None => expr::intern(Node::Keccak(words, tail)),
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
                    st.stack.push(v);
                }
                op::MLOAD => {
                    let off = pop!();
                    let v = st.mem.load_word(off, st.version);
                    if std::env::var("EVMDEC_DEBUG_LOAD").is_ok_and(|w| w == ins.pc.to_string()) {
                        eprintln!(
                            "MLOAD pc={} off={:?} norm={:?} -> {:?}",
                            ins.pc,
                            expr::node(off),
                            norm_offset(off),
                            expr::node(v)
                        );
                        for w in &st.mem.writes {
                            eprintln!(
                                "  write base={:?} off={} len={:?} val={} gen={}",
                                w.base.map(expr::node),
                                w.off,
                                w.len,
                                match &w.val {
                                    MVal::Word(_) => "word",
                                    MVal::Byte(_) => "byte",
                                    MVal::Copy(..) => "copy",
                                    MVal::CallOut(_) => "callout",
                                    MVal::Unknown => "unknown",
                                },
                                w.gen
                            );
                        }
                    }
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
                            seq_base + seq_ctr,
                            &mut underflow,
                        ));
                    } else if let Some(via) = un.returns_via {
                        let ret_arg = match via {
                            AVal::Slot(k) => Some(expr::arg(k as u32)),
                            _ => None,
                        };
                        let vals: Vec<ExprId> = st
                            .stack
                            .iter()
                            .copied()
                            .filter(|v| Some(*v) != ret_arg)
                            .collect();
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
                    if o == op::MCOPY {
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
                                        MVal::Copy(o, src, None),
                                    );
                                }
                            } else {
                                st.mem.store(dest, Some(l), MVal::Copy(o, src, None));
                            }
                        } else {
                            st.mem.store(dest, None, MVal::Copy(o, src, None));
                        }
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
                    } else {
                        st.mem.store(dest, l, MVal::Copy(o, src, None));
                    }
                    next_version(&mut st);
                    stmts.push(Stmt::Copy {
                        kind: o,
                        dest,
                        src,
                        len,
                        addr: None,
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
                    next_version(&mut st);
                    stmts.push(Stmt::Copy {
                        kind: o,
                        dest,
                        src,
                        len,
                        addr: Some(addr),
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
                    let seq = seq_base + seq_ctr;
                    seq_ctr += 1;
                    let input = expr::as_const(in_len)
                        .and_then(|l| l.as_usize())
                        .and_then(|l| st.mem.read_region(in_off, l as u64, st.version))
                        .map(|(w, _)| w);
                    if let (Some(_), Some(l)) = (&input, expr::as_const(in_len)) {
                        hidden.add(nid, st.mem.consumers(in_off, l.low_u64()));
                    }
                    let result = expr::intern(Node::CallResult(seq));
                    if let Ok(want) = std::env::var("EVMDEC_DEBUG_HEAD") {
                        if want == "all" || want == ins.pc.to_string() {
                            eprintln!(
                                "CALL pc={} in_off={:?} norm={:?} version={} gen={} clobber={}",
                                ins.pc,
                                expr::node(in_off),
                                norm_offset(in_off),
                                st.version,
                                st.mem.gen,
                                st.mem.clobber_gen
                            );
                            for w in &st.mem.writes {
                                eprintln!(
                                    "  write base={:?} off={} len={:?} val={} gen={}",
                                    w.base.map(expr::node),
                                    w.off,
                                    w.len,
                                    match &w.val {
                                        MVal::Word(_) => "word",
                                        MVal::Byte(_) => "byte",
                                        MVal::Copy(..) => "copy",
                                        MVal::CallOut(_) => "callout",
                                        MVal::Unknown => "unknown",
                                    },
                                    w.gen
                                );
                            }
                        }
                    }
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
                    if identity && matches!((ol, il), (Some(o), Some(i)) if o <= i) {
                        apply_mcopy(&mut st, out_off, in_off, out_len);
                    } else if ol != Some(0) {
                        st.mem.store(out_off, ol, MVal::CallOut(seq));
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
                        result,
                        gen,
                    });
                    st.stack.push(result);
                    st.called = true;
                    st.returned = call_stamp(nid, stmts.len());
                }
                op::CREATE | op::CREATE2 => {
                    let value = pop!();
                    let off = pop!();
                    let len = pop!();
                    let salt = if o == op::CREATE2 { Some(pop!()) } else { None };
                    let seq = seq_base + seq_ctr;
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
        underflow: &mut bool,
    ) -> Term {
        let consumed = call.consumed as usize;
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
        let summary = self.summaries.get(&call.callee);
        let free_pointer = konst(U256::from_u64(FREE_POINTER));
        let free_now = st.mem.load_word(free_pointer, st.version);
        let entry_gen = st.mem.gen;
        let subst = |e: ExprId| -> ExprId {
            let restamped = expr::restamp_memory(e, entry_gen, &mut HashMap::new());
            let mut memo = HashMap::new();
            expr::substitute(
                restamped,
                &|n| match n {
                    Node::Arg(i) => Some(at(*i as usize)),
                    Node::MLoad(a, _) if *a == free_pointer => Some(free_now),
                    _ => None,
                },
                &mut memo,
            )
        };
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
        let unknown_pushed = call
            .pushed
            .iter()
            .filter(|v| !matches!(v, AVal::Slot(_) | AVal::Const(_) | AVal::Pc(_)))
            .count();
        let by_position = summary.is_some_and(|s| s.returns.len() == call.pushed.len());
        let resolve = |e: ExprId| -> ExprId {
            let mut memo = HashMap::new();
            expr::substitute(
                e,
                &|n| {
                    if let Node::MLoad(a, _) = n {
                        Some(st.mem.load_word(*a, st.version))
                    } else {
                        None
                    }
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
                AVal::Const(c) | AVal::Pc(c) => konst(*c),
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
        match summary {
            Some(sum) => {
                for (off, val) in &sum.mstores {
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
                for (dest, src, len) in &sum.copies {
                    let (d, s2, l2) = (subst(*dest), subst(*src), subst(*len));
                    if transparent {
                        stmts.push(Stmt::Copy {
                            kind: op::MCOPY,
                            dest: d,
                            src: s2,
                            len: l2,
                            addr: None,
                        });
                    }
                    apply_mcopy(st, d, s2, l2);
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
                    None => st.mem.clobber(),
                }
                st.storage.clear();
                st.sgen += 1;
                st.called = true;
                st.returned = call_stamp(un.id, stmts.len());
            }
        }
        if transparent {
            for (cond, data, invalid) in summary.map(|s| s.guards.as_slice()).unwrap_or(&[]) {
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
        } else {
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

fn merge_into(
    e: &mut Entry,
    exit: &State,
    node: usize,
    phi_ids: &mut HashMap<(usize, usize), ExprId>,
    next_var: &mut u32,
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
                let var = *phi_ids.entry((node, from_top)).or_insert_with(|| {
                    *next_var += 1;
                    expr::var(((node as u32) << 10) | (*next_var & 0x3ff))
                });
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
    for k in 0..el {
        let from_top = el - 1 - k;
        let exit_val = if from_top < xl {
            Some(exit.stack[xl - 1 - from_top])
        } else {
            None
        };
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

#[derive(Clone, Debug)]
pub struct MemView {
    mem: Mem,
    version: u32,
}

impl Default for MemView {
    fn default() -> Self {
        Self::new()
    }
}

impl MemView {
    pub fn new() -> MemView {
        MemView {
            mem: Mem::new(false),
            version: 0,
        }
    }
    pub fn new_fresh() -> MemView {
        MemView {
            mem: Mem::new(true),
            version: 0,
        }
    }
    pub fn unfresh(&mut self) {
        self.mem.fresh = false;
    }
    pub fn unknown(&mut self, off: ExprId, len: Option<u64>) {
        self.mem.store(off, len, MVal::Unknown);
        self.mem.tick();
        self.version = self.mem.gen;
    }
    pub fn store(&mut self, off: ExprId, val: ExprId) {
        self.mem.store(off, Some(32), MVal::Word(val));
        self.mem.tick();
        self.version = self.mem.gen;
    }
    pub fn copy(&mut self, dest: ExprId, src: ExprId, len: ExprId) {
        let mut st = State {
            stack: Vec::new(),
            args_used: 0,
            mem: std::mem::replace(&mut self.mem, Mem::new(false)),
            storage: Vec::new(),
            version: self.version,
            sgen: 0,
            called: false,
            returned: 0,
        };
        apply_mcopy(&mut st, dest, src, len);
        self.mem = st.mem;
        self.version = st.version;
    }
    pub fn load(&self, off: ExprId) -> Option<ExprId> {
        let w = self.mem.load_bytes(off, 32, self.version)?;
        if expr::contains(w, &|n| matches!(n, Node::MLoad(..))) {
            None
        } else {
            Some(w)
        }
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

fn apply_mcopy(st: &mut State, dest: ExprId, src: ExprId, len: ExprId) {
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
                    MVal::Copy(op::MCOPY, src, None),
                );
            }
        } else {
            st.mem
                .store(dest, Some(l), MVal::Copy(op::MCOPY, src, None));
        }
    } else {
        st.mem.store(dest, None, MVal::Copy(op::MCOPY, src, None));
    }
    st.mem.tick();
    st.version = st.mem.gen;
}

impl Lifted {
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
        } => Stmt::Copy {
            kind: *kind,
            dest: f(*dest),
            src: f(*src),
            len: f(*len),
            addr: addr.map(f),
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
                input, input_head, ..
            } => {
                v.extend(input_head.iter().copied());
                if let Some(d) = input {
                    v.extend(d.iter().copied());
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
            ..
        } => {
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
