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
use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::rc::Rc;

/// A side-effecting statement of a lifted node.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    /// `var = value` (phi copies live on edges; this is for explicit temporaries).
    Assign {
        /// The `Var` being assigned.
        var: ExprId,
        /// Expression assigned to `var`.
        value: ExprId,
    },
    /// Memory store (`MSTORE` or `MSTORE8`).
    MStore {
        /// Memory offset written.
        off: ExprId,
        /// Value stored (already masked to one byte for `MSTORE8`).
        val: ExprId,
        /// Width in bytes: 32 for `MSTORE`, 1 for `MSTORE8`.
        width: u8,
        /// Memory generation this write starts: an unresolved load of the same address stamped
        /// below it read what the write replaces. Zero for a store the lifter did not execute.
        gen: u32,
    },
    /// Storage store (`SSTORE`, or `TSTORE` when `transient`).
    SStore {
        /// Storage slot written.
        key: ExprId,
        /// Value stored.
        val: ExprId,
        /// Transient storage (`TSTORE`) rather than persistent storage.
        transient: bool,
        /// Storage generation before this write: an `SLoad` of the same slot whose generation is
        /// at most this read the value the write replaces.
        gen: u32,
    },
    /// Event emission (`LOG0`..`LOG4`).
    Log {
        /// Memory offset of the event data.
        off: ExprId,
        /// Length of the event data in bytes.
        len: ExprId,
        /// Topic expressions, in opcode order.
        topics: Vec<ExprId>,
        /// Event data words, when `len` is constant and every byte is known.
        data: Option<Vec<ExprId>>,
    },
    /// `input_head` holds the first memory words of the payload (the selector lives in the top
    /// four bytes of the first) even when the whole payload could not be decoded into `input`.
    Call {
        /// Sequence number identifying this call (`CallResult`/`ReturnData` refer to it).
        seq: u32,
        /// Opcode: `CALL`, `CALLCODE`, `DELEGATECALL` or `STATICCALL`.
        kind: u8,
        /// Gas forwarded to the callee.
        gas: ExprId,
        /// Callee address.
        addr: ExprId,
        /// Wei sent; `None` for `DELEGATECALL`/`STATICCALL`, which carry no value.
        value: Option<ExprId>,
        /// Memory offset of the input payload.
        in_off: ExprId,
        /// Length of the input payload in bytes.
        in_len: ExprId,
        /// Memory offset the return data is copied to.
        out_off: ExprId,
        /// Number of return-data bytes copied to `out_off`.
        out_len: ExprId,
        /// Input payload words, when `in_len` is constant and every byte is known.
        input: Option<Vec<ExprId>>,
        /// Leading payload words, available even when `input` is `None`.
        input_head: Vec<ExprId>,
        /// The `CallResult(seq)` expression pushed as the success flag.
        result: ExprId,
        /// Storage generation before the call when the call advances it (every call but
        /// `STATICCALL`): loads of that generation or older read values from before the call.
        gen: Option<u32>,
    },
    /// Contract creation (`CREATE` or `CREATE2`).
    Create {
        /// Sequence number identifying this creation (`CreateResult` refers to it).
        seq: u32,
        /// Opcode: `CREATE` or `CREATE2`.
        kind: u8,
        /// Wei endowed to the new contract.
        value: ExprId,
        /// Memory offset of the init code.
        off: ExprId,
        /// Length of the init code in bytes.
        len: ExprId,
        /// Salt for `CREATE2`; `None` for `CREATE`.
        salt: Option<ExprId>,
        /// The `CreateResult(seq)` expression pushed as the new contract's address.
        result: ExprId,
        /// Init code words, when `len` is constant and every byte is known.
        init: Option<Vec<ExprId>>,
        /// Storage generation before the creation (which always advances it).
        gen: u32,
    },
    /// CALLDATACOPY / CODECOPY / RETURNDATACOPY / EXTCODECOPY / MCOPY.
    Copy {
        /// The copying opcode.
        kind: u8,
        /// Destination memory offset.
        dest: ExprId,
        /// Source offset in calldata, code, return data, external code or memory (per `kind`).
        src: ExprId,
        /// Number of bytes copied.
        len: ExprId,
        /// Address whose code is copied; `EXTCODECOPY` only.
        addr: Option<ExprId>,
    },
    /// Call of the internal function (another unit) whose entry is at pc `callee`.
    Internal {
        /// Sequence number identifying this call (`IntRet` refers to it).
        seq: u32,
        /// Program counter of the callee's entry block.
        callee: usize,
        /// Argument expressions (deepest first), excluding the return address.
        args: Vec<ExprId>,
        /// Values the call leaves on the stack; empty when the callee was inlined.
        results: Vec<ExprId>,
        /// Storage generation before the call when the callee has side effects (it then
        /// advances the generation like an external call).
        gen: Option<u32>,
    },
    /// Explicit `POP` of a value that had side effects (a call result that is ignored).
    Drop(ExprId),
    /// A guard taken over from an inlined helper: execution continues only if `cond` holds,
    /// otherwise the helper reverted with `data` (decoded payload words), or hit INVALID.
    Require {
        /// Condition that must hold for execution to continue.
        cond: ExprId,
        /// Decoded revert payload words of the failing side, when known.
        data: Option<Vec<ExprId>>,
        /// The failing side hit `INVALID` (an assert) rather than reverting.
        invalid: bool,
    },
}

/// How control leaves a lifted node.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    /// Unconditional jump to the lifted node.
    Jump(usize),
    /// `t == None`: the true branch jumps to an invalid destination (reverts).
    Branch {
        /// Branch condition; the true branch is taken when it is non-zero.
        cond: ExprId,
        /// Lifted node of the true branch; `None` when it is an invalid destination.
        t: Option<usize>,
        /// Lifted node of the false branch.
        f: usize,
    },
    /// Computed jump with several possible targets.
    Switch {
        /// The jump target expression dispatched on.
        target: ExprId,
        /// Lifted nodes the jump may reach.
        cases: Vec<usize>,
    },
    /// `RETURN` of `len` bytes of memory at `off`.
    Return {
        /// Memory offset of the returned data.
        off: ExprId,
        /// Length of the returned data in bytes.
        len: ExprId,
        /// Returned words, when `len` is constant (outside oracle mode, unknown words are allowed).
        data: Option<Vec<ExprId>>,
    },
    /// Return of one dynamic `bytes`/`string` value held in memory at `ptr` (length word first),
    /// recognised from the compiler's encoding boilerplate.
    ReturnDyn {
        /// Memory pointer to the length word of the returned value.
        ptr: ExprId,
    },
    /// `REVERT` with `len` bytes of memory at `off`.
    Revert {
        /// Memory offset of the revert payload.
        off: ExprId,
        /// Length of the revert payload in bytes.
        len: ExprId,
        /// Payload words, when `len` is constant and every byte is known.
        data: Option<Vec<ExprId>>,
    },
    /// `STOP`: halt successfully without return data.
    Stop,
    /// `INVALID`, or an unknown opcode: exceptional halt.
    Invalid,
    /// `SELFDESTRUCT` sending the balance to the given address.
    SelfDestruct(ExprId),
    /// Return from an internal function unit with these values (deepest first).
    InternalReturn(Vec<ExprId>),
    /// Jump whose target could not be resolved.
    Unresolved(ExprId),
    /// Oracle mode only: a JUMPI with its condition and target expressions.
    CondJump {
        /// Condition of the jump.
        cond: ExprId,
        /// Target expression of the jump.
        target: ExprId,
    },
    /// A branch to an invalid jump destination, or stack underflow in a real frame.
    Infeasible,
}

/// A lifted node: the statements and terminator produced by executing one unit node.
#[derive(Clone, Debug)]
pub struct LNode {
    /// Index of this node in `Lifted::nodes`.
    pub id: usize,
    /// Basic block (index into `Program::blocks`) the node executes.
    pub block: usize,
    /// Program counter where that block starts.
    pub pc: usize,
    /// Statements in execution order.
    pub stmts: Vec<Stmt>,
    /// How control leaves the node.
    pub term: Term,
    /// Lifted node ids of the predecessors.
    pub preds: Vec<usize>,
    /// Lifted node ids of the successors, as given by `term`.
    pub succs: Vec<usize>,
    /// Entry stack expressions (deepest first). Phi slots hold `Var`s.
    pub entry_stack: Vec<ExprId>,
    /// Stack expressions on leaving the node (deepest first).
    pub exit_stack: Vec<ExprId>,
}

/// The result of lifting one unit: an expression-level control-flow graph.
#[derive(Clone, Debug)]
pub struct Lifted {
    /// Lifted nodes, indexed by `LNode::id`.
    pub nodes: Vec<LNode>,
    /// Id of the entry node.
    pub entry: usize,
    /// Phi copies to perform when taking edge (from, to): `(var, value)`.
    pub edge_assigns: HashMap<(usize, usize), Vec<(ExprId, ExprId)>>,
    /// Number of entry-stack arguments the unit consumes (`Arg(0..n)`).
    pub n_args: usize,
    /// Number of node re-runs performed to reach the fixpoint.
    pub reprocess_count: usize,
    /// Stack slot (from the top at entry) holding the return address, for internal units.
    pub ret_slot: Option<u32>,
    /// Entry state of every node (indexed by the *unit* node id), for re-lifting sub-regions.
    pub(crate) entry_states: Vec<Option<State>>,
    /// Map from unit node id to lifted node id.
    pub node_map: HashMap<usize, usize>,
    /// The unresolved loads that may see memory as the caller left it: loads of bytes the unit
    /// had not itself written on every path by then.
    pub entry_loads: MemoryReads,
    /// What the unit may write to memory, the internal functions it calls included.
    pub mem_writes: MemoryWrites,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum MVal {
    Word(ExprId),
    Byte(ExprId),
    /// Copied region: opcode, source offset expression, external address (EXTCODECOPY).
    Copy(u8, ExprId, Option<ExprId>),
    /// Output region of call `seq`.
    CallOut(u32),
    /// Bytes whose value differs between merged predecessors: a read hitting them is unknown.
    Unknown,
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

/// The memory some code may read without the lifter knowing the value: loads that store
/// forwarding did not resolve, and byte ranges handed to a call, a log, a hash, a copy or a
/// return whose words are not all known. Byte ranges with constant bounds, and optionally
/// everything from an address up.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MemoryReads {
    ranges: BTreeSet<(u64, u64)>,
    open_from: Option<u64>,
    /// Addresses read through a word-scaled index, `base + 32 * i`, where the reader had
    /// already written the word at `base`: an element of a list the reader itself filled, if
    /// its indices stay inside the list.
    indexed: BTreeSet<u64>,
}

impl MemoryReads {
    /// Every address.
    #[must_use]
    pub fn everything() -> MemoryReads {
        MemoryReads {
            open_from: Some(0),
            ..MemoryReads::default()
        }
    }

    /// Settle the indexed reads: dropped when the compiler checks every index against the
    /// length of the list (Vyper has no unchecked access), else open-ended from their base.
    #[must_use]
    pub fn with_indices(mut self, checked: bool) -> MemoryReads {
        let lowest = std::mem::take(&mut self.indexed).into_iter().next();
        if let (Some(base), false) = (lowest, checked) {
            self.open_from = Some(self.open_from.map_or(base, |o| o.min(base)));
        }
        self
    }

    /// Add what `other` reads; says whether anything was new.
    pub fn add(&mut self, other: &MemoryReads) -> bool {
        let before = (self.ranges.len(), self.open_from);
        self.ranges.extend(other.ranges.iter().copied());
        self.open_from = match (self.open_from, other.open_from) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        };
        before != (self.ranges.len(), self.open_from)
    }

    /// A read at an address that is not constant: everything from its constant part up, or
    /// everything when the rest of the address could wrap below it.
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

    /// Add a read of `n` bytes at `off`, unless `written` already holds all of them.
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

    /// Add what `other` reads outside the byte ranges in `written`.
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

    /// Add a read of the `len` bytes at `off`, unless `written` already holds all of them.
    pub fn range_outside(&mut self, off: ExprId, len: ExprId, written: &BTreeSet<(u64, u64)>) {
        let mut own = MemoryReads::default();
        own.range(off, len);
        self.add_outside(&own, written);
    }

    /// Add the unresolved loads inside the expressions `roots`.
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

    /// Add what the statement `s` reads. `callee` gives what an internal function reads, by
    /// entry pc; an unknown one reads everything.
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

    /// Add what the terminator `t` reads. A return to an internal caller reads everything when
    /// `returns_to_reader` is set: the caller may read whatever this function wrote.
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

    /// May any of the `len` bytes at `addr` be read?
    #[must_use]
    pub fn reads(&self, addr: u64, len: u64) -> bool {
        let end = addr.saturating_add(len);
        self.open_from.is_some_and(|from| end > from)
            || self.ranges.iter().any(|(lo, hi)| addr < *hi && end > *lo)
    }
}

impl Lifted {
    /// What the unit may read of memory as its caller left it: the loads the lifter saw before
    /// the unit had written their bytes on every path, plus the byte ranges it hands to calls,
    /// logs, copies and reverts and what the internal functions it calls read, in each case
    /// outside what its own statements have certainly written by then. `callee` gives the same
    /// for an internal function by entry pc; an unknown one reads everything.
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

/// Do the byte ranges in `written` hold every byte of `lo..hi`?
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

/// The memory some code may write: constant byte ranges, or anything at all once a write's
/// address or length is not constant or control leaves for code that was not recovered.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MemoryWrites {
    ranges: BTreeSet<(u64, u64)>,
    anywhere: bool,
}

impl MemoryWrites {
    /// The constant byte ranges written, merged where they touch, when every write is to one.
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
    /// Untouched bytes read as zero (true at the start of a call frame).
    fresh: bool,
    /// Memory generation: advanced once per memory-writing statement. An unknown read is
    /// stamped with the generation of the last write that may alias it, so `mem[x]` denotes the
    /// memory at a precise program point (the oracle relies on this) while unrelated writes in
    /// between do not change the expression.
    gen: u32,
    /// Generation after the last event that may have changed arbitrary memory (clobber, forgotten writes).
    clobber_gen: u32,
    /// Constant byte ranges written on every path since the unit was entered.
    written: BTreeSet<(u64, u64)>,
    /// The unresolved loads that may see memory as it was when the unit was entered: those of
    /// bytes not yet in `written`. Shared by every state of one lift.
    entry_loads: Rc<RefCell<MemoryReads>>,
    /// Everything written through this view. Shared by every state of one lift.
    touched: Rc<RefCell<MemoryWrites>>,
}

const BIG: u64 = 1 << 40;

/// Marks the return data of a block reached from paths whose last calls differ.
const MERGED_RETURN: u32 = 1 << 31;

/// A stamp for the return data the call at statement `index` of node `node` leaves: stable
/// across the rounds the node is lifted in, and never zero.
fn call_stamp(node: usize, index: usize) -> u32 {
    ((node as u32) << 10 | (index as u32 & 0x3ff)).wrapping_add(1) & !MERGED_RETURN
}

/// The most memory writes a state keeps. Past it the oldest are forgotten, and with them the
/// knowledge that untouched memory is zero.
const MAX_TRACKED_WRITES: usize = 256;

/// The memory slot solc keeps its free memory pointer in.
pub const FREE_POINTER: u64 = 0x40;

/// Normalise an offset into `(base, delta)` with a small delta.
fn norm_offset(e: ExprId) -> (Option<ExprId>, u64) {
    let (b, d) = expr::split_offset(e);
    if d.fits_u64() && d.low_u64() < BIG {
        (b, d.low_u64())
    } else {
        (Some(e), 0)
    }
}

/// A memory base that may equal any address: it holds a loop variable, argument, call result
/// or other unknown rather than free-memory-pointer arithmetic.
fn wild_base(b: ExprId) -> bool {
    expr::contains(b, &|x| {
        !matches!(x, Node::Const(_) | Node::Op(..) | Node::MLoad(..))
    })
}

/// Could a write through base `wb` (`woff`, `wlen` bytes) alias a read through base `rb`
/// (`roff`, `rlen` bytes) when the bases differ? Only when one side is an unknown pointer.
/// Such a pointer is unsigned and memory never wraps, so `p + k` lies at or above `k`; it also
/// never points into the scratch area below 0x80.
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
        }
    }

    /// Record an unresolved read of `n` bytes at `off`.
    fn note_load(&self, off: ExprId, n: u64) {
        self.entry_loads.borrow_mut().note(off, n, &self.written);
    }

    /// Record an unresolved read of the `len` bytes at `off`.
    fn note_range(&self, off: ExprId, len: ExprId) {
        self.entry_loads
            .borrow_mut()
            .range_outside(off, len, &self.written);
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
        self.touched.borrow_mut().anywhere = true;
        self.writes.clear();
        self.fresh = false;
        self.gen += 1;
        self.clobber_gen = self.gen;
    }

    /// Read `n` bytes (n <= 32) at `off` as a word (right-aligned), if known.
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
                if may_alias(w.base, w.off, w.len, base, d, n) {
                    return None;
                }
                continue;
            }
            let Some(wl) = w.len else {
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
            words.push(self.load_bytes(
                expr::add_const(off, U256::from(i)),
                tail as u64,
                version,
            )?);
        }
        Some((words, tail))
    }

    /// Words of a small region, with unknown words left as memory reads, provided at least one
    /// word is known (so that a return of `(32, len, <copied data>)` keeps its decoded head).
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

    /// Intersection with another memory (merge point).
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

/// Symbolic execution state at a program point: stack, memory and storage knowledge.
///
/// Opaque to callers; obtained from `Lifter::entry_state_of` to re-lift a sub-region.
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
    /// Which call last set the return data: the return-data size read before a call and the
    /// one read after it are different values. Zero until a call happens.
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

/// Lifts the units of a program into `Lifted` graphs.
#[derive(Debug)]
pub struct Lifter<'a> {
    /// The program whose units are lifted.
    pub prog: &'a Program,
    /// Root frame semantics (main unit): empty stack, zero memory.
    pub root: bool,
    /// Effect summaries of simple internal functions, by entry block.
    pub summaries: HashMap<usize, CalleeSummary>,
    /// What each internal function may write to memory, by entry block; one that is absent may
    /// write anywhere.
    pub footprints: HashMap<usize, MemoryWrites>,
    /// Oracle mode: keep jump target/condition expressions instead of resolving successors.
    pub oracle: bool,
    /// Word-copy loops recognised on a first lift, keyed by (unit entry block, unit header node):
    /// on the next lift of that unit the loop is replaced by one memory copy.
    pub copy_loops: RefCell<HashMap<(usize, usize), CopyLoop>>,
}

/// A loop that copies memory word by word, summarised as one copy (unit node ids).
#[derive(Clone, Debug)]
pub struct CopyLoop {
    /// Node the pre-header enters (the condition node for a while-loop, the body for a rotated
    /// do-while loop).
    pub entry: usize,
    /// Node holding the loop condition.
    pub latch: usize,
    /// Node holding the copying store; equal to `latch` for a self-looping body.
    pub body: usize,
    /// Node control reaches once the loop finishes.
    pub exit: usize,
    /// Which copy-loop idiom this is and where its variables live on the stack.
    pub shape: CopyShape,
}

/// The recognised form of a word-copy loop.
#[derive(Clone, Debug)]
pub enum CopyShape {
    /// `mem[dst + i] = mem[src + i]` with `i += 32`: the counter is stack slot `slot` (from the
    /// top of the stack entering `entry`). `rotated`: the body runs first and the test
    /// `i + 32 < len` follows, so the counter leaves the loop at the last index copied.
    Index {
        /// Stack slot of the counter (from the top of the stack entering `entry`).
        slot: usize,
        /// The body runs before the test, so the counter leaves the loop at the last
        /// index copied.
        rotated: bool,
    },
    /// `while (n >= 32) { mem[d] = mem[s]; n -= 32; d += 32; s += 32 }` with the three
    /// variables in stack slots (from the top) `n`, `d`, `s` entering the condition node.
    Countdown {
        /// Stack slot (from the top) of the remaining byte count.
        n: usize,
        /// Stack slot (from the top) of the destination pointer.
        d: usize,
        /// Stack slot (from the top) of the source pointer.
        s: usize,
    },
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
    /// Conditions that must hold on the summarised path (the other side of each branch reverts),
    /// with the revert payload of the failing side and whether it is an INVALID (assert).
    pub guards: Vec<(ExprId, Option<Vec<ExprId>>, bool)>,
    /// Memory-to-memory copies `(dest, src, len)` in order (from summarised copy loops).
    pub copies: Vec<(ExprId, ExprId, ExprId)>,
    /// Word offsets written on only some paths (padding stores): unknown after the call.
    pub maybe_mstores: Vec<ExprId>,
}

/// Record why a unit could not be summarised (with `EVMDEC_DEBUG_SUMMARY`) and yield `None`.
fn fail_summary(code: u32) -> Option<CalleeSummary> {
    if std::env::var("EVMDEC_DEBUG_SUMMARY").is_ok() {
        eprintln!("[summary] not summarisable (reason {})", code);
    }
    None
}

/// Compute a `CalleeSummary` from a lifted internal function, if it is simple enough.
///
/// Returns `None` for anything with loops, calls, non-word memory stores or several return
/// paths (`EVMDEC_DEBUG_SUMMARY` prints the reason code).
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

/// Memory writes whose only purpose was to feed a hash, log, return, revert or call payload that
/// was decoded: they are dropped from the output as encoding noise.
#[derive(Default)]
struct Hidden {
    /// Per consuming node (cleared each time that node is re-run, so that a decode that only
    /// succeeded on an early, single-predecessor run does not hide stores for good).
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
    /// Which stack positions (from the bottom of the entry stack) are phis.
    phis: Vec<bool>,
}

impl<'a> Lifter<'a> {
    /// Lift `unit` starting from `initial` (entry stack, deepest first, and whether memory is
    /// fresh); by default an empty stack with fresh memory exactly in root mode.
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

    /// Lift, then lift again with every word-copy loop of the unit summarised as one copy.
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

    /// Like [`lift_summarizing`](Self::lift_summarizing), starting from an explicit entry state.
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

    /// Entry state of a lifted node, to lift a sub-region starting there separately.
    pub fn entry_state_of(l: &Lifted, unit_node: usize) -> Option<State> {
        l.entry_states.get(unit_node).cloned().flatten()
    }

    /// Lift `unit` starting from the entry state `init`, iterating to a fixpoint.
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

    /// Execute one node from its entry state.
    /// Replace a recognised copy loop entered with state `entering` by one memory copy: returns
    /// the statement to show and the state that reaches the loop's exit.
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
                                        *out =
                                            prog.code.get(s + i as usize + j).copied().unwrap_or(0);
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

/// Merge an exit state into a successor's entry. Returns true if the entry changed.
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

/// All expressions referenced by a node's statements and terminator (for analyses).
/// Split a loop condition into the bound: `LT(i, len)` / `GT(len, i)` and `ISZERO` of either.
fn loop_bound(cond: ExprId) -> Option<ExprId> {
    match expr::node(cond) {
        Node::Op(op::LT, v) => Some(v[1]),
        Node::Op(op::GT, v) => Some(v[0]),
        Node::Op(op::ISZERO, v) => loop_bound(v[0]),
        _ => None,
    }
}

/// A sequential memory model for analyses that replay statements in order.
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
    /// A view whose unwritten bytes are unknown.
    pub fn new() -> MemView {
        MemView {
            mem: Mem::new(false),
            version: 0,
        }
    }
    /// A view of the memory of a freshly entered call frame: never-written bytes read as zero.
    pub fn new_fresh() -> MemView {
        MemView {
            mem: Mem::new(true),
            version: 0,
        }
    }
    /// Stop treating unwritten bytes as zero (unknown writes may have happened).
    pub fn unfresh(&mut self) {
        self.mem.fresh = false;
    }
    /// `len` bytes at `off` (symbolic length when `None`) now hold unknown values.
    pub fn unknown(&mut self, off: ExprId, len: Option<u64>) {
        self.mem.store(off, len, MVal::Unknown);
        self.mem.tick();
        self.version = self.mem.gen;
    }
    /// Store the 32-byte word `val` at `off`.
    pub fn store(&mut self, off: ExprId, val: ExprId) {
        self.mem.store(off, Some(32), MVal::Word(val));
        self.mem.tick();
        self.version = self.mem.gen;
    }
    /// Copy `len` bytes of memory from `src` to `dest` (`MCOPY` semantics).
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
    /// The word at `off` if every byte of it is known.
    pub fn load(&self, off: ExprId) -> Option<ExprId> {
        let w = self.mem.load_bytes(off, 32, self.version)?;
        if expr::contains(w, &|n| matches!(n, Node::MLoad(..))) {
            None
        } else {
            Some(w)
        }
    }
}

/// keccak256 of a region whose words are all constants (the last `tail` bytes right-aligned).
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

/// Copy `len` bytes of memory from `src` to `dest` in `st`: known words are copied as words,
/// the rest as an opaque copy.
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
    /// The value of the free memory pointer when the unit is entered: a constant when the
    /// dispatcher has just set it, otherwise the load of its slot.
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

/// Every path from `start` ends in a revert or an invalid opcode.
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

/// Apply `f` to every expression of a statement.
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

/// Apply `f` to every expression of a terminator.
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

/// Every expression referenced by the statements and terminator of `n` (not its stacks).
pub fn node_exprs(n: &LNode) -> Vec<ExprId> {
    let mut v: Vec<ExprId> = n.stmts.iter().flat_map(stmt_exprs).collect();
    v.extend(term_exprs(&n.term));
    v
}

/// An expression root of a node, tagged with whether it is a word of an ABI-encoded payload.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Root {
    /// The expression.
    pub expr: ExprId,
    /// A payload word (call input, event data, init code, revert data): pieces of values packed
    /// at 4-byte offsets, so a mask or shift found at its root is encoding, not a type.
    pub payload: bool,
}

/// Every expression root of a node, tagged (see [`Root`]).
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

/// The expression roots of a node that are words of an ABI-encoded payload (call input, event
/// data, init code, revert data).
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

/// Every expression referenced by one statement (assignment targets included).
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

/// Every expression referenced by a terminator.
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
            Some(jump_target_bits(v[1])? << k.low_u64() as u32)
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
            Some(jump_target_bits(x)? << c.trailing_zeros())
        }
        Node::Op(op::SHR, v) => {
            let k = expr::as_const(v[0])?;
            if k >= U256::from_u64(256) {
                return Some(U256::ZERO);
            }
            Some(jump_target_bits(v[1])? >> k.low_u64() as u32)
        }
        Node::Op(op::BYTE, _) => Some(U256::from_u64(0xff)),
        Node::Op(op::DIV, v) => {
            let c = expr::as_const(v[1])?;
            if !c.is_power_of_two() {
                return None;
            }
            Some(jump_target_bits(v[0])? >> c.trailing_zeros())
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
