//! Basic blocks and compositional control-flow recovery.
//!
//! Jump targets in EVM code are stack values. We recover them with a *summary* analysis: every
//! block is executed abstractly from a symbolic entry stack (`Slot(i)` is the i-th entry below
//! the top at entry, `Mem(o)` the memory word at `o` at entry) and the result describes how
//! control leaves the region reachable from it: a return through some slot/memory token, a halt,
//! or an unresolved jump, together with the net stack effect. A jump to a constant target is
//! resolved by composing the target's summary; when the target's return token evaluates to a
//! constant code address at the call site, the jump is an internal call and the constant is the
//! continuation. This keeps the analysis linear in the number of call sites (no product of
//! nested contexts) and recovers internal functions with their argument and return counts.
//!
//! `Unit`s are the explicit graphs the lifter consumes: one for the public entry (dispatcher and
//! external function bodies), one per internal function, one per orphan block.

use crate::disasm::{self, Instruction};
use crate::opcode as op;
use crate::u256::U256;
use serde::Serialize;
use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::rc::Rc;

/// A maximal straight-line run of instructions, ending at a terminator or before a JUMPDEST.
#[derive(Clone, Debug, Serialize)]
pub struct Block {
    /// Index of this block in `Program::blocks`.
    pub id: usize,
    /// Byte offset of the first instruction.
    pub start: usize,
    /// Exclusive byte end.
    pub end: usize,
    /// Index range into `Program::insns`.
    pub first: usize,
    /// Index of the last instruction in `Program::insns` (inclusive).
    pub last: usize,
    /// Opcode of the last instruction.
    pub terminator: u8,
    /// Starts with JUMPDEST.
    pub is_jumpdest: bool,
}

/// Disassembled runtime code split into basic blocks.
#[derive(Debug)]
pub struct Program {
    /// Raw bytecode.
    pub code: Vec<u8>,
    /// Instructions in code order.
    pub insns: Vec<Instruction>,
    /// Basic blocks in code order.
    pub blocks: Vec<Block>,
    /// Block id by start byte offset.
    pub block_at_pc: BTreeMap<usize, usize>,
    /// Byte offsets of every JUMPDEST (the valid jump targets).
    pub jumpdests: HashSet<usize>,
    /// Candidate targets of computed jumps (block id -> target blocks), derived from the shape of
    /// the target expression (alignment masks, shifts): hand-written dispatchers that jump to
    /// `calldata[i] & 0x3ff0`-style addresses.
    pub computed_jumps: HashMap<usize, Vec<usize>>,
}

impl Program {
    /// Disassemble `code` and split it into blocks at terminators and JUMPDESTs.
    pub fn new(code: Vec<u8>) -> Program {
        let insns = disasm::disassemble(&code);
        let jumpdests: HashSet<usize> = disasm::jumpdests(&code).into_iter().collect();
        let mut blocks = Vec::new();
        let mut block_at_pc = BTreeMap::new();
        let mut i = 0;
        while i < insns.len() {
            let first = i;
            let mut j = i;
            loop {
                let o = insns[j].opcode;
                if op::is_terminator(o)
                    || j + 1 >= insns.len()
                    || insns[j + 1].opcode == op::JUMPDEST
                {
                    break;
                }
                j += 1;
            }
            let id = blocks.len();
            let b = Block {
                id,
                start: insns[first].pc,
                end: insns[j].pc + insns[j].size,
                first,
                last: j,
                terminator: insns[j].opcode,
                is_jumpdest: insns[first].opcode == op::JUMPDEST,
            };
            block_at_pc.insert(b.start, id);
            blocks.push(b);
            i = j + 1;
        }
        Program {
            code,
            insns,
            blocks,
            block_at_pc,
            jumpdests,
            computed_jumps: HashMap::new(),
        }
    }

    /// Can the EVM ever enter this block? Only the entry, JUMPDEST-started blocks and the
    /// fall-through of a JUMPI can be executed; bytes after a terminator without a JUMPDEST are
    /// data or dead by construction.
    pub fn is_potential_code(&self, b: usize) -> bool {
        let blk = &self.blocks[b];
        blk.start == 0
            || blk.is_jumpdest
            || (b > 0 && self.blocks[b - 1].terminator == op::JUMPI)
            || (b > 0 && !op::is_terminator(self.blocks[b - 1].terminator))
    }

    /// Instructions of block `b`.
    pub fn block_insns(&self, b: &Block) -> &[Instruction] {
        &self.insns[b.first..=b.last]
    }

    /// Block index of a valid jump target.
    pub fn target_block(&self, pc: usize) -> Option<usize> {
        if self.jumpdests.contains(&pc) {
            self.block_at_pc.get(&pc).copied()
        } else {
            None
        }
    }

    /// Block following `b` in code order, if any.
    pub fn next_block(&self, b: usize) -> Option<usize> {
        if b + 1 < self.blocks.len() {
            Some(b + 1)
        } else {
            None
        }
    }

    /// Block containing `pc`.
    pub fn block_containing(&self, pc: usize) -> Option<usize> {
        self.block_at_pc
            .range(..=pc)
            .next_back()
            .map(|(_, b)| *b)
            .filter(|b| self.blocks[*b].end > pc)
    }
}

/// Abstract value for control-flow recovery.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum AVal {
    /// A known constant.
    Const(U256),
    /// A constant derived from `PC` (Vyper < 0.3 computes return addresses as `PC + k`).
    Pc(U256),
    /// The i-th stack entry below the top at the entry of the region being analysed.
    Slot(u16),
    /// The memory word at a constant offset at the entry of the region being analysed.
    Mem(u32),
    /// Some value derived from a constant code region copied into memory (a jump table entry).
    Table,
    /// Anything else.
    Unk,
}

impl AVal {
    /// The constant value, if known (plain or `PC`-derived).
    pub fn konst(&self) -> Option<U256> {
        match self {
            AVal::Const(c) | AVal::Pc(c) => Some(*c),
            _ => None,
        }
    }
    fn is_token(&self) -> bool {
        matches!(self, AVal::Slot(_) | AVal::Mem(_))
    }
}

#[derive(Clone)]
// The three maps are shared between the states of a walk and only replaced on write
// (`Rc::make_mut`), so cloning a state at every branch stays cheap.
struct AMem {
    /// Known 32-byte words at constant offsets (word writes only).
    words: Rc<BTreeMap<u32, AVal>>,
    /// Known bytes (from CODECOPY and constant stores) for jump-table recovery.
    bytes: Rc<Vec<Option<u8>>>,
    /// Code regions copied into memory: (mem dest, code offset, len).
    regions: Rc<Vec<(usize, usize, usize)>>,
    /// Some write with an unknown offset happened (entry-relative `Mem` tokens are no longer valid).
    clobbered: bool,
}

const MAX_AMEM: usize = 1 << 16;

impl AMem {
    fn new() -> AMem {
        AMem {
            words: Rc::new(BTreeMap::new()),
            bytes: Rc::new(Vec::new()),
            regions: Rc::new(Vec::new()),
            clobbered: false,
        }
    }
    fn write_bytes(&mut self, off: usize, data: &[Option<u8>]) {
        if off > MAX_AMEM || data.is_empty() {
            return;
        }
        let end = (off + data.len()).min(MAX_AMEM);
        let v = Rc::make_mut(&mut self.bytes);
        if v.len() < end {
            v.resize(end, None);
        }
        for (i, b) in data.iter().enumerate() {
            if off + i < end {
                v[off + i] = *b;
            }
        }
    }
    fn store_word(&mut self, off: usize, val: AVal) {
        if off > MAX_AMEM {
            return;
        }
        // Invalidate overlapping words.
        let w = Rc::make_mut(&mut self.words);
        let lo = off.saturating_sub(31) as u32;
        let keys: Vec<u32> = w.range(lo..=(off as u32 + 31)).map(|(k, _)| *k).collect();
        for k in keys {
            w.remove(&k);
        }
        w.insert(off as u32, val);
        match val.konst() {
            Some(c) => {
                let b = c.to_be_bytes();
                self.write_bytes(off, &b.iter().map(|x| Some(*x)).collect::<Vec<_>>());
            }
            None => self.write_bytes(off, &[None; 32]),
        }
    }
    fn store_byte(&mut self, off: usize, val: Option<u8>) {
        if off > MAX_AMEM {
            return;
        }
        let w = Rc::make_mut(&mut self.words);
        let lo = off.saturating_sub(31) as u32;
        let keys: Vec<u32> = w.range(lo..=(off as u32)).map(|(k, _)| *k).collect();
        for k in keys {
            w.remove(&k);
        }
        self.write_bytes(off, &[val]);
    }
    fn clear(&mut self, off: usize, len: usize) {
        if off > MAX_AMEM || len == 0 {
            return;
        }
        let end = off.saturating_add(len).min(MAX_AMEM);
        let w = Rc::make_mut(&mut self.words);
        let lo = off.saturating_sub(31) as u32;
        let keys: Vec<u32> = w.range(lo..end as u32).map(|(k, _)| *k).collect();
        for k in keys {
            w.remove(&k);
        }
        let v = Rc::make_mut(&mut self.bytes);
        for i in off..end.min(v.len()) {
            v[i] = None;
        }
    }
    fn load_word(&self, off: usize) -> Option<AVal> {
        if let Some(v) = self.words.get(&(off as u32)) {
            return Some(*v);
        }
        if off + 32 <= self.bytes.len() {
            let mut buf = [0u8; 32];
            for (i, out) in buf.iter_mut().enumerate() {
                *out = self.bytes[off + i]?;
            }
            return Some(AVal::Const(U256::from_be_bytes(&buf)));
        }
        None
    }
}

/// Abstract machine state during a walk.
#[derive(Clone)]
pub struct AState {
    /// Explicit part of the stack (top at the end). Entries below it are `Slot(consumed..)`.
    pub stack: Vec<AVal>,
    /// How many entry slots have been popped (materialised) so far.
    pub consumed: u16,
    mem: AMem,
    /// A real call frame: the entry stack is empty and memory is zero, so popping below the
    /// explicit stack is infeasible (the EVM would have reverted) and untouched memory reads 0.
    pub root: bool,
}

impl Default for AState {
    fn default() -> Self {
        Self::new()
    }
}

impl AState {
    /// State at the entry of a region: every stack entry and memory word is a symbolic token.
    pub fn new() -> AState {
        AState {
            stack: Vec::new(),
            consumed: 0,
            mem: AMem::new(),
            root: false,
        }
    }
    /// State at the start of a real call frame (pc 0 of a runtime): empty stack, zero memory.
    pub fn root() -> AState {
        AState {
            stack: Vec::new(),
            consumed: 0,
            mem: AMem::new(),
            root: true,
        }
    }
    /// The path popped below the stack a real frame started with.
    pub fn underflowed(&self) -> bool {
        self.root && self.consumed > 0
    }
    /// Entry stack of a region: everything is a slot.
    fn pop(&mut self) -> AVal {
        match self.stack.pop() {
            Some(v) => v,
            None => {
                if self.consumed >= 1023 {
                    return AVal::Unk;
                }
                let v = AVal::Slot(self.consumed);
                self.consumed += 1;
                v
            }
        }
    }
    fn peek(&mut self, n: usize) -> AVal {
        // n = 1 is the top.
        while self.stack.len() < n {
            if self.consumed >= 1023 {
                return AVal::Unk;
            }
            self.stack.insert(0, AVal::Slot(self.consumed));
            self.consumed += 1;
        }
        self.stack[self.stack.len() - n]
    }
    fn push(&mut self, v: AVal) {
        if self.stack.len() < 1024 {
            self.stack.push(v);
        }
    }
    /// Value of the i-th entry below the top (0 = top), materialising slots as needed.
    pub fn at(&mut self, i: usize) -> AVal {
        self.peek(i + 1)
    }

    /// Identity of a node within a unit walk: positions of code addresses and tokens.
    fn sig(&self, prog: &Program) -> Sig {
        let mut items = Vec::new();
        for (i, v) in self.stack.iter().rev().enumerate() {
            match v {
                AVal::Const(c) | AVal::Pc(c) => {
                    if let Some(pc) = c.as_usize() {
                        if prog.jumpdests.contains(&pc) {
                            items.push((i as u16, SigVal::Jd(pc as u32)));
                        }
                    }
                }
                AVal::Slot(s) => items.push((i as u16, SigVal::Slot(*s))),
                AVal::Mem(m) => items.push((i as u16, SigVal::Mem(*m))),
                _ => {}
            }
        }
        let mut mem = Vec::new();
        for (o, v) in self.mem.words.iter() {
            match v {
                AVal::Const(c) | AVal::Pc(c) => {
                    if let Some(pc) = c.as_usize() {
                        if prog.jumpdests.contains(&pc) && matches!(v, AVal::Pc(_)) {
                            mem.push((*o, SigVal::Jd(pc as u32)));
                        }
                    }
                }
                AVal::Slot(s) => mem.push((*o, SigVal::Slot(*s))),
                AVal::Mem(m) => mem.push((*o, SigVal::Mem(*m))),
                _ => {}
            }
        }
        Sig { items, mem }
    }
}

impl std::fmt::Debug for AState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "AState(stack={:?}, consumed={})",
            self.stack, self.consumed
        )
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum SigVal {
    Jd(u32),
    Slot(u16),
    Mem(u32),
}

/// Identity of a node within a unit walk: the positions of code addresses and entry tokens on
/// the stack and in memory. Two states with the same `Sig` at the same block are one node.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Sig {
    items: Vec<(u16, SigVal)>,
    mem: Vec<(u32, SigVal)>,
}

/// How control leaves a block.
#[derive(Clone, Debug)]
pub enum Flow {
    /// Jump to constant targets (one for JUMP, several for a jump table).
    Jump(Vec<usize>),
    /// Conditional: true targets (constant) and fall-through block.
    Branch {
        /// Constant targets taken when the condition is non-zero.
        targets: Vec<usize>,
        /// Block executed when the condition is zero, if any.
        fallthrough: Option<usize>,
    },
    /// JUMP to a value that is not a constant: a return through `token` (Slot/Mem) or unknown.
    Return(AVal),
    /// No terminator: execution continues into the given block.
    Fallthrough(usize),
    /// Execution ends here; carries the terminating opcode (STOP, RETURN, REVERT, INVALID, ...).
    Halt(u8),
    /// JUMPI whose target is not constant; fall-through is still possible.
    BranchUnresolved {
        /// The non-constant jump target.
        target: AVal,
        /// Block executed when the condition is zero, if any.
        fallthrough: Option<usize>,
    },
}

/// Whether a walk takes the candidates of a computed jump (one whose target is not a constant).
///
/// Orphan units ignore them so that the unreachable handlers of a jump-table dispatcher do not
/// each re-explore the whole program.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ComputedJumps {
    /// Follow every resolved candidate target.
    Follow,
    /// Stop at computed jumps.
    Ignore,
}

/// Outcome of abstractly executing one block.
#[derive(Debug)]
pub struct BlockExit {
    /// Abstract state at the end of the block.
    pub state: AState,
    /// How control leaves the block.
    pub flow: Flow,
    /// Memory word offsets written with constant offsets.
    pub mem_written: Vec<u32>,
    /// Some memory write in the block had an unknown offset.
    pub mem_clobbered: bool,
}

fn fold_const2(o: u8, a: U256, b: U256) -> Option<U256> {
    Some(match o {
        op::AND => a & b,
        op::OR => a | b,
        op::XOR => a ^ b,
        op::SHL => {
            if a >= U256::from_u64(256) {
                U256::ZERO
            } else {
                b << a.low_u64() as u32
            }
        }
        op::SHR => {
            if a >= U256::from_u64(256) {
                U256::ZERO
            } else {
                b >> a.low_u64() as u32
            }
        }
        op::BYTE => U256::byte(a, b),
        op::DIV if b.is_power_of_two() => a / b,
        op::MUL if b.is_power_of_two() || a.is_power_of_two() => a.wrapping_mul(b),
        op::EXP if a == U256::from_u64(2) => a.pow(b),
        _ => return None,
    })
}

fn to_usize(v: AVal) -> Option<usize> {
    v.konst().and_then(|c| c.as_usize())
}

/// Abstractly execute block `b` from `state`. Never fails.
pub fn exec_block(prog: &Program, b: &Block, state: &AState) -> BlockExit {
    let mut st = state.clone();
    let mut mem_written = Vec::new();
    let mut mem_clobbered = false;
    let mut flow: Option<Flow> = None;
    let insns = prog.block_insns(b);
    for ins in insns {
        let o = ins.opcode;
        match o {
            _ if op::is_push(o) => st.push(AVal::Const(ins.imm.unwrap_or(U256::ZERO))),
            _ if op::is_dup(o) => {
                let n = (o - 0x7f) as usize;
                let v = st.peek(n);
                st.push(v);
            }
            _ if op::is_swap(o) => {
                let n = (o - 0x8f) as usize;
                st.peek(n + 1);
                let l = st.stack.len();
                st.stack.swap(l - 1, l - 1 - n);
            }
            op::POP => {
                st.pop();
            }
            op::JUMPDEST => {}
            op::PC => st.push(AVal::Pc(U256::from(ins.pc))),
            op::JUMP => {
                let t = st.pop();
                flow = Some(match t {
                    AVal::Const(c) | AVal::Pc(c) => Flow::Jump(
                        c.as_usize()
                            .and_then(|pc| prog.target_block(pc))
                            .into_iter()
                            .collect(),
                    ),
                    AVal::Table => Flow::Jump(
                        table_targets(prog, &st.mem)
                            .into_iter()
                            .filter_map(|pc| prog.target_block(pc))
                            .collect(),
                    ),
                    AVal::Unk if prog.computed_jumps.contains_key(&b.id) => {
                        Flow::Jump(prog.computed_jumps[&b.id].clone())
                    }
                    v => Flow::Return(v),
                });
                break;
            }
            op::JUMPI => {
                let t = st.pop();
                let _cond = st.pop();
                let fallthrough = prog.next_block(b.id);
                flow = Some(match t {
                    AVal::Const(c) | AVal::Pc(c) => Flow::Branch {
                        targets: c
                            .as_usize()
                            .and_then(|pc| prog.target_block(pc))
                            .into_iter()
                            .collect(),
                        fallthrough,
                    },
                    AVal::Table => Flow::Branch {
                        targets: table_targets(prog, &st.mem)
                            .into_iter()
                            .filter_map(|pc| prog.target_block(pc))
                            .collect(),
                        fallthrough,
                    },
                    AVal::Unk if prog.computed_jumps.contains_key(&b.id) => Flow::Branch {
                        targets: prog.computed_jumps[&b.id].clone(),
                        fallthrough,
                    },
                    v => Flow::BranchUnresolved {
                        target: v,
                        fallthrough,
                    },
                });
                break;
            }
            op::MLOAD => {
                let off = st.pop();
                let v = match to_usize(off) {
                    Some(o) if o < MAX_AMEM => match st.mem.load_word(o) {
                        Some(v) => v,
                        None => {
                            if !st.mem.regions.is_empty() {
                                AVal::Table
                            } else if st.root && !st.mem.clobbered {
                                AVal::Const(U256::ZERO)
                            } else if o % 32 == 0 {
                                // Optimistic even after writes to unknown offsets: compilers keep
                                // return addresses in dedicated slots, and targets are validated.
                                AVal::Mem(o as u32)
                            } else {
                                AVal::Unk
                            }
                        }
                    },
                    _ => {
                        if st.mem.regions.is_empty() {
                            AVal::Unk
                        } else {
                            AVal::Table
                        }
                    }
                };
                st.push(v);
            }
            op::MSTORE | op::MSTORE8 => {
                let off = st.pop();
                let val = st.pop();
                match to_usize(off) {
                    Some(o) if o < MAX_AMEM => {
                        if ins.opcode == op::MSTORE {
                            st.mem.store_word(o, val);
                            mem_written.push(o as u32);
                        } else {
                            st.mem
                                .store_byte(o, val.konst().map(|c| c.to_be_bytes()[31]));
                            mem_written.push((o - o % 32) as u32);
                        }
                    }
                    _ => {
                        // Unknown offset: entry-relative memory tokens are no longer trustworthy,
                        // but known constants are kept (targets are validated against JUMPDESTs).
                        st.mem.clobbered = true;
                        mem_clobbered = true;
                    }
                }
            }
            op::CODECOPY => {
                let dest = st.pop();
                let src = st.pop();
                let len = st.pop();
                match (to_usize(dest), to_usize(src), to_usize(len)) {
                    (Some(d), Some(s), Some(l)) if d < MAX_AMEM && l <= MAX_AMEM => {
                        let data: Vec<Option<u8>> = (0..l)
                            .map(|i| {
                                Some(
                                    s.checked_add(i)
                                        .and_then(|p| prog.code.get(p).copied())
                                        .unwrap_or(0),
                                )
                            })
                            .collect();
                        st.mem.clear(d, l);
                        st.mem.write_bytes(d, &data);
                        if s < prog.code.len() && l >= 2 {
                            Rc::make_mut(&mut st.mem.regions).push((d, s, l));
                        }
                        mem_written.push((d - d % 32) as u32);
                    }
                    (Some(d), _, Some(l)) => {
                        st.mem.clear(d, l);
                        mem_written.push((d - d % 32) as u32);
                    }
                    _ => {
                        st.mem.clobbered = true;
                        mem_clobbered = true;
                    }
                }
            }
            op::CALLDATACOPY | op::RETURNDATACOPY | op::MCOPY => {
                let dest = st.pop();
                let _src = st.pop();
                let len = st.pop();
                match (to_usize(dest), to_usize(len)) {
                    (Some(d), Some(l)) => {
                        st.mem.clear(d, l);
                        mem_written.push((d - d % 32) as u32);
                    }
                    _ => {
                        st.mem.clobbered = true;
                        mem_clobbered = true;
                    }
                }
            }
            op::EXTCODECOPY => {
                let _addr = st.pop();
                let dest = st.pop();
                let _src = st.pop();
                let len = st.pop();
                match (to_usize(dest), to_usize(len)) {
                    (Some(d), Some(l)) => {
                        st.mem.clear(d, l);
                        mem_written.push((d - d % 32) as u32);
                    }
                    _ => {
                        st.mem.clobbered = true;
                        mem_clobbered = true;
                    }
                }
            }
            op::CALL | op::CALLCODE | op::DELEGATECALL | op::STATICCALL => {
                let n = if o == op::CALL || o == op::CALLCODE {
                    7
                } else {
                    6
                };
                let mut args = Vec::new();
                for _ in 0..n {
                    args.push(st.pop());
                }
                let out_off = args[n - 2];
                let out_len = args[n - 1];
                match (to_usize(out_off), to_usize(out_len)) {
                    (Some(d), Some(l)) => {
                        st.mem.clear(d, l);
                        if l > 0 {
                            mem_written.push((d - d % 32) as u32);
                        }
                    }
                    _ => {
                        st.mem.clobbered = true;
                        mem_clobbered = true;
                    }
                }
                st.push(AVal::Unk);
            }
            _ => {
                let info = op::info(o);
                let (pops, pushes) = info
                    .map(|i| (i.pops as usize, i.pushes as usize))
                    .unwrap_or((0, 0));
                let mut args = Vec::with_capacity(pops);
                for _ in 0..pops {
                    args.push(st.pop());
                }
                if pushes == 1 {
                    let v = match (pops, o) {
                        (2, _) => match (args[0], args[1]) {
                            (AVal::Pc(a), AVal::Const(b))
                            | (AVal::Const(a), AVal::Pc(b))
                            | (AVal::Pc(a), AVal::Pc(b))
                                if matches!(o, op::ADD | op::SUB) =>
                            {
                                AVal::Pc(if o == op::ADD {
                                    a.wrapping_add(b)
                                } else {
                                    a.wrapping_sub(b)
                                })
                            }
                            (AVal::Const(a), AVal::Const(b)) if matches!(o, op::ADD | op::SUB) => {
                                // Folded only when the result is a code address, so loop counters stay unknown.
                                let r = if o == op::ADD {
                                    a.wrapping_add(b)
                                } else {
                                    a.wrapping_sub(b)
                                };
                                if r.as_usize().is_some_and(|pc| prog.jumpdests.contains(&pc)) {
                                    AVal::Const(r)
                                } else {
                                    AVal::Unk
                                }
                            }
                            (AVal::Const(a), AVal::Const(b)) => {
                                fold_const2(o, a, b).map(AVal::Const).unwrap_or(AVal::Unk)
                            }
                            (AVal::Table, _) | (_, AVal::Table)
                                if matches!(
                                    o,
                                    op::AND
                                        | op::OR
                                        | op::XOR
                                        | op::SHL
                                        | op::SHR
                                        | op::SAR
                                        | op::BYTE
                                        | op::DIV
                                        | op::MOD
                                        | op::ADD
                                        | op::SUB
                                        | op::MUL
                                ) =>
                            {
                                AVal::Table
                            }
                            _ => AVal::Unk,
                        },
                        (1, op::NOT) => match args[0] {
                            AVal::Const(a) => AVal::Const(!a),
                            AVal::Table => AVal::Table,
                            _ => AVal::Unk,
                        },
                        _ => AVal::Unk,
                    };
                    st.push(v);
                }
                if op::is_halt(o) {
                    flow = Some(Flow::Halt(o));
                    break;
                }
            }
        }
    }
    let flow = flow.unwrap_or_else(|| match prog.next_block(b.id) {
        Some(nb) => Flow::Fallthrough(nb),
        None => Flow::Halt(op::STOP),
    });
    BlockExit {
        state: st,
        flow,
        mem_written,
        mem_clobbered,
    }
}

/// Every plausible 2-byte big-endian jump destination inside the code regions copied into memory.
fn table_targets(prog: &Program, mem: &AMem) -> Vec<usize> {
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    for &(_, src, len) in mem.regions.iter() {
        let end = (src + len).min(prog.code.len());
        if end < src + 2 {
            continue;
        }
        for i in src..end - 1 {
            let pc = ((prog.code[i] as usize) << 8) | prog.code[i + 1] as usize;
            if prog.jumpdests.contains(&pc) && seen.insert(pc) {
                out.push(pc);
            }
        }
        if out.len() > 4096 {
            break;
        }
    }
    out
}

// ---------------------------------------------------------------------------------------------
// Summaries
// ---------------------------------------------------------------------------------------------

/// One way control can leave the region reachable from a block, with its net stack effect.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Exit {
    /// Return token (Slot/Mem) through which the JUMP leaves, or `Unk`.
    pub via: AVal,
    /// Entry stack slots consumed on the way to this exit.
    pub consumed: u16,
    /// Stack left above the remaining entry slots at the exit (top last).
    pub pushed: Vec<AVal>,
}

/// How control can leave the region reachable from a block (see the module docs).
#[derive(Clone, Debug, Default)]
pub struct Summary {
    /// Ways of leaving the region through a non-constant JUMP (at most `MAX_EXITS`).
    pub exits: Vec<Exit>,
    /// Some path halts (STOP/RETURN/REVERT/...) instead of exiting.
    pub may_halt: bool,
    /// Some jump in the region could not be resolved, or the walk ran out of budget.
    pub unresolved: bool,
    /// Memory words (constant offsets) that may be written before any exit.
    pub mem_written: Vec<u32>,
    /// Some path writes memory at an unknown offset before an exit.
    pub mem_clobbered: bool,
    /// Blocks reachable within the region (for coverage accounting).
    pub blocks: Vec<usize>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Memo {
    Pending,
    Provisional(u32),
    Complete,
}

/// Summary analysis over a `Program`: memoised block summaries and the internal-call targets
/// they reveal.
pub struct Analysis<'a> {
    /// The program being analysed.
    pub prog: &'a Program,
    // Memo tables and counters live behind `RefCell` because the walk recurses through `&self`
    // (summaries of callees are computed on demand while a caller is being walked).
    summaries: RefCell<Vec<Summary>>,
    memo: RefCell<Vec<Option<Memo>>>,
    stack_depth: RefCell<usize>,
    /// Blocks used as internal-call targets with a constant continuation.
    pub call_targets: RefCell<HashSet<usize>>,
    /// Abstract instructions executed so far (bounded by `MAX_STEPS`).
    pub steps: RefCell<usize>,
    /// Set once a step or recursion budget was hit; results are then incomplete.
    pub budget_exhausted: RefCell<bool>,
}

const MAX_EXITS: usize = 24;
/// Total nodes across all orphan units (unreached code is decompiled best-effort).
const MAX_ORPHAN_NODES: usize = 60_000;
/// Distinct contexts a single block may have inside one unit walk. Loops that push or pop a
/// stack entry per iteration (Vyper buffer copies) would otherwise create a node per iteration.
const MAX_BLOCK_CONTEXTS: usize = 12;
const MAX_WALK_NODES: usize = 6000;
const MAX_STEPS: usize = 3_000_000;
const MAX_RECURSION: usize = 3000;
const MAX_PROVISIONAL_RECOMPUTES: u32 = 6;

/// Substitute tokens of `v` (relative to a callee's entry) with the values of `st` (the caller's
/// state at the call), materialising slots as needed.
fn resolve(v: AVal, st: &mut AState) -> AVal {
    match v {
        AVal::Slot(i) => st.at(i as usize),
        AVal::Mem(o) => match st.mem.load_word(o as usize) {
            Some(x) => x,
            None => {
                if st.root && !st.mem.clobbered {
                    AVal::Const(U256::ZERO)
                } else {
                    AVal::Mem(o)
                }
            }
        },
        other => other,
    }
}

/// Apply an exit's stack effect to the caller state.
fn apply_exit(ex: &Exit, st: &mut AState) {
    // Materialise and remove `consumed` entries, then push `pushed` resolved against the pre-pop stack.
    let mut pre = st.clone();
    let resolved: Vec<AVal> = ex.pushed.iter().map(|v| resolve(*v, &mut pre)).collect();
    // pre may have materialised more slots; adopt them
    *st = pre;
    for _ in 0..ex.consumed {
        st.pop();
    }
    for v in resolved {
        st.push(v);
    }
}

fn join_vals(a: AVal, b: AVal) -> AVal {
    if a == b {
        a
    } else {
        AVal::Unk
    }
}

fn add_exit(exits: &mut Vec<Exit>, ex: Exit) -> bool {
    // Merge with an exit of the same shape (same via, consumed, pushed length).
    for e in exits.iter_mut() {
        if e.via == ex.via && e.consumed == ex.consumed && e.pushed.len() == ex.pushed.len() {
            let mut changed = false;
            for (x, y) in e.pushed.iter_mut().zip(&ex.pushed) {
                let j = join_vals(*x, *y);
                if j != *x {
                    *x = j;
                    changed = true;
                }
            }
            return changed;
        }
    }
    if exits.len() >= MAX_EXITS {
        return false;
    }
    exits.push(ex);
    true
}

impl<'a> Analysis<'a> {
    /// Analysis of `prog` with empty memo tables.
    pub fn new(prog: &'a Program) -> Analysis<'a> {
        Analysis {
            prog,
            summaries: RefCell::new(vec![Summary::default(); prog.blocks.len()]),
            memo: RefCell::new(vec![None; prog.blocks.len()]),
            stack_depth: RefCell::new(0),
            call_targets: RefCell::new(HashSet::new()),
            steps: RefCell::new(0),
            budget_exhausted: RefCell::new(false),
        }
    }

    /// Summary of the region reachable from block `b`, computed and memoised on demand.
    pub fn summary(&self, b: usize) -> Summary {
        let m = self.memo.borrow()[b];
        match m {
            Some(Memo::Complete) | Some(Memo::Pending) => {
                return self.summaries.borrow()[b].clone()
            }
            Some(Memo::Provisional(n)) if n >= MAX_PROVISIONAL_RECOMPUTES => {
                return self.summaries.borrow()[b].clone()
            }
            _ => {}
        }
        if *self.stack_depth.borrow() > MAX_RECURSION || *self.steps.borrow() > MAX_STEPS {
            *self.budget_exhausted.borrow_mut() = true;
            return self.summaries.borrow()[b].clone();
        }
        let prev_memo = m;
        self.memo.borrow_mut()[b] = Some(Memo::Pending);
        *self.stack_depth.borrow_mut() += 1;
        let mut iterations = 0;
        let mut depends_on_pending = false;
        loop {
            iterations += 1;
            let (summary, dep) = self.walk_summary(b);
            depends_on_pending |= dep;
            let changed = {
                let mut s = self.summaries.borrow_mut();
                let old = &s[b];
                let changed = old.exits != summary.exits
                    || old.may_halt != summary.may_halt
                    || old.unresolved != summary.unresolved
                    || old.mem_clobbered != summary.mem_clobbered
                    || old.mem_written != summary.mem_written
                    || old.blocks != summary.blocks;
                s[b] = summary;
                changed
            };
            // A self-dependent region (loop) iterates to a fixpoint; otherwise one pass suffices.
            if !changed || !dep || iterations >= 8 {
                break;
            }
        }
        *self.stack_depth.borrow_mut() -= 1;
        let new_memo = if depends_on_pending {
            let n = match prev_memo {
                Some(Memo::Provisional(n)) => n + 1,
                _ => 0,
            };
            Memo::Provisional(n)
        } else {
            Memo::Complete
        };
        self.memo.borrow_mut()[b] = Some(new_memo);
        self.summaries.borrow()[b].clone()
    }

    /// Is `b` currently being computed (part of a cycle through the caller)?
    fn is_pending(&self, b: usize) -> bool {
        matches!(self.memo.borrow()[b], Some(Memo::Pending))
    }

    /// Walk the region from `b` with a symbolic entry stack and collect its exits.
    fn walk_summary(&self, b: usize) -> (Summary, bool) {
        let prog = self.prog;
        let mut summary = Summary::default();
        let mut depends_on_pending = false;
        let mut seen: HashMap<(usize, Sig), ()> = HashMap::new();
        let mut blocks_seen: HashSet<usize> = HashSet::new();
        let mut per_block: HashMap<usize, usize> = HashMap::new();
        let mut work: VecDeque<(usize, AState)> = VecDeque::new();
        work.push_back((b, AState::new()));
        let mut mem_written: HashSet<u32> = HashSet::new();
        while let Some((blk, st)) = work.pop_front() {
            *self.steps.borrow_mut() += 1;
            if seen.len() > MAX_WALK_NODES || *self.steps.borrow() > MAX_STEPS {
                *self.budget_exhausted.borrow_mut() = true;
                summary.unresolved = true;
                break;
            }
            let key = (blk, st.sig(prog));
            if seen.contains_key(&key) {
                continue;
            }
            let cnt = per_block.entry(blk).or_insert(0);
            if *cnt >= MAX_BLOCK_CONTEXTS {
                continue;
            }
            *cnt += 1;
            seen.insert(key, ());
            blocks_seen.insert(blk);
            let exit = exec_block(prog, &prog.blocks[blk], &st);
            mem_written.extend(exit.mem_written.iter().copied());
            summary.mem_clobbered |= exit.mem_clobbered;
            let st = exit.state;
            let follow_consts = |targets: &[usize],
                                 st: &AState,
                                 work: &mut VecDeque<(usize, AState)>,
                                 summary: &mut Summary,
                                 depends: &mut bool,
                                 mem_written: &mut HashSet<u32>| {
                for &t in targets {
                    if t == b {
                        // Back to our own entry: a loop over the region. The exits of the
                        // continuation are our own exits composed with the current effect.
                        *depends = true;
                        let cur = self.summaries.borrow()[b].clone();
                        for ex in &cur.exits {
                            let mut s2 = st.clone();
                            let via = resolve(ex.via, &mut s2);
                            apply_exit(ex, &mut s2);
                            self.record_exit(summary, via, &s2, work);
                        }
                        summary.may_halt |= cur.may_halt;
                        continue;
                    }
                    if self.is_pending(t) {
                        *depends = true;
                    }
                    let sub = self.summary(t);
                    if matches!(
                        self.memo.borrow()[t],
                        Some(Memo::Pending) | Some(Memo::Provisional(_))
                    ) {
                        *depends = true;
                    }
                    summary.may_halt |= sub.may_halt;
                    summary.unresolved |= sub.unresolved;
                    summary.mem_clobbered |= sub.mem_clobbered;
                    mem_written.extend(sub.mem_written.iter().copied());
                    for ex in &sub.exits {
                        let mut s2 = st.clone();
                        let via = resolve(ex.via, &mut s2);
                        apply_exit(ex, &mut s2);
                        if let Some(pc) = to_usize(via) {
                            // Internal call: continue at the constant continuation.
                            if let Some(cb) = prog.target_block(pc) {
                                self.call_targets.borrow_mut().insert(t);
                                work.push_back((cb, s2));
                            }
                        } else {
                            self.record_exit(summary, via, &s2, work);
                        }
                    }
                }
            };
            match exit.flow {
                Flow::Jump(ref targets) => follow_consts(
                    targets,
                    &st,
                    &mut work,
                    &mut summary,
                    &mut depends_on_pending,
                    &mut mem_written,
                ),
                Flow::Branch {
                    ref targets,
                    fallthrough,
                } => {
                    follow_consts(
                        targets,
                        &st,
                        &mut work,
                        &mut summary,
                        &mut depends_on_pending,
                        &mut mem_written,
                    );
                    if let Some(f) = fallthrough {
                        work.push_back((f, st.clone()));
                    }
                }
                Flow::Fallthrough(f) => work.push_back((f, st.clone())),
                Flow::Return(v) => {
                    // `v` is already relative to this region's entry.
                    self.record_exit(&mut summary, v, &st, &mut work);
                }
                Flow::BranchUnresolved { fallthrough, .. } => {
                    summary.unresolved = true;
                    if let Some(f) = fallthrough {
                        work.push_back((f, st.clone()));
                    }
                }
                Flow::Halt(_) => summary.may_halt = true,
            }
        }
        summary.blocks = blocks_seen.into_iter().collect();
        summary.blocks.sort_unstable();
        summary.mem_written = mem_written.into_iter().collect();
        summary.mem_written.sort_unstable();
        (summary, depends_on_pending)
    }

    fn record_exit(
        &self,
        summary: &mut Summary,
        via: AVal,
        st: &AState,
        work: &mut VecDeque<(usize, AState)>,
    ) {
        if let Some(pc) = to_usize(via) {
            // A constant produced inside the region (e.g. a loop whose continuation resolved).
            if let Some(cb) = self.prog.target_block(pc) {
                work.push_back((cb, st.clone()));
            }
            return;
        }
        if via.is_token() {
            add_exit(
                &mut summary.exits,
                Exit {
                    via,
                    consumed: st.consumed,
                    pushed: st.stack.clone(),
                },
            );
        } else {
            summary.unresolved = true;
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Units: explicit graphs for the lifter
// ---------------------------------------------------------------------------------------------

/// Kind of a successor edge in a `Unit`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum Edge {
    /// The block has no terminator and continues into the next one.
    Fallthrough,
    /// Unconditional JUMP to a resolved target.
    Jump,
    /// JUMPI taken.
    True,
    /// JUMPI not taken (fall-through).
    False,
    /// Continuation after an internal call returns.
    Return,
}

/// An internal call made by the JUMP at the end of a node.
#[derive(Clone, Debug)]
pub struct CallInfo {
    /// Entry block of the called function.
    pub callee: usize,
    /// Stack entries consumed by the callee (including the return address).
    pub consumed: u16,
    /// Values pushed by the callee (relative to the caller's stack before the call).
    pub pushed: Vec<AVal>,
    /// Index (from the top, after popping the target) of the return address.
    pub ret_slot: Option<u16>,
}

/// A block in a specific stack context: one node of a `Unit` graph.
#[derive(Clone, Debug)]
pub struct UNode {
    /// Index of this node in `Unit::nodes`.
    pub id: usize,
    /// The basic block this node executes.
    pub block: usize,
    /// Abstract state at the start of the block in this context.
    pub entry: AState,
    /// Successor nodes with the kind of edge leading to each.
    pub succs: Vec<(usize, Edge)>,
    /// Predecessor node ids.
    pub preds: Vec<usize>,
    /// Set when the block's JUMP is an internal call: the continuation nodes are `Return` succs.
    pub call: Option<CallInfo>,
    /// The block ends by returning from this unit through a token (Slot/Mem).
    pub returns_via: Option<AVal>,
    /// The block's jump target could not be resolved to code.
    pub unresolved: bool,
    /// The path into this node underflows the real frame's stack and cannot execute.
    pub infeasible: bool,
    /// A computed jump that this (orphan) unit does not follow; its targets are shown where the
    /// main unit dispatches on it.
    pub computed_cut: bool,
}

/// Explicit control-flow graph of one region (public entry, internal function or orphan block).
#[derive(Clone, Debug)]
pub struct Unit {
    /// Basic block the unit starts at.
    pub entry_block: usize,
    /// Nodes indexed by `UNode::id`.
    pub nodes: Vec<UNode>,
    /// Id of the entry node.
    pub entry: usize,
    /// The walk hit a node or context limit and the graph is incomplete.
    pub budget_exhausted: bool,
}

impl<'a> Analysis<'a> {
    /// Build the explicit graph for the region starting at `entry_block` with `entry_state`.
    pub fn build_unit(&self, entry_block: usize, entry_state: AState) -> Unit {
        self.build_unit_opts(
            entry_block,
            entry_state,
            ComputedJumps::Follow,
            MAX_WALK_NODES * 4,
        )
    }

    /// Like [`build_unit`](Self::build_unit) with an explicit computed-jump policy and node
    /// budget.
    pub fn build_unit_opts(
        &self,
        entry_block: usize,
        entry_state: AState,
        computed: ComputedJumps,
        max_nodes: usize,
    ) -> Unit {
        let follow_computed = computed == ComputedJumps::Follow;
        let prog = self.prog;
        let mut nodes: Vec<UNode> = Vec::new();
        let mut index: HashMap<(usize, Sig), usize> = HashMap::new();
        let mut work: VecDeque<usize> = VecDeque::new();
        let mut budget_exhausted = false;
        let mut per_block: HashMap<usize, Vec<usize>> = HashMap::new();
        let mut intern = |blk: usize,
                          st: &AState,
                          nodes: &mut Vec<UNode>,
                          index: &mut HashMap<(usize, Sig), usize>,
                          work: &mut VecDeque<usize>|
         -> usize {
            let key = (blk, st.sig(prog));
            if let Some(&id) = index.get(&key) {
                return id;
            }
            let list = per_block.entry(blk).or_default();
            if list.len() >= MAX_BLOCK_CONTEXTS {
                // Context limit: fold into the first node of this block.
                return list[0];
            }
            let id = nodes.len();
            list.push(id);
            nodes.push(UNode {
                id,
                block: blk,
                entry: st.clone(),
                succs: vec![],
                preds: vec![],
                call: None,
                returns_via: None,
                unresolved: false,
                infeasible: false,
                computed_cut: false,
            });
            index.insert(key, id);
            work.push_back(id);
            id
        };
        let entry = intern(entry_block, &entry_state, &mut nodes, &mut index, &mut work);
        while let Some(n) = work.pop_front() {
            if nodes.len() > max_nodes {
                budget_exhausted = true;
                break;
            }
            let blk = nodes[n].block;
            let st = nodes[n].entry.clone();
            let mut exit = exec_block(prog, &prog.blocks[blk], &st);
            let mut cut = false;
            if !follow_computed && prog.computed_jumps.contains_key(&blk) {
                match exit.flow {
                    Flow::Jump(_) => {
                        exit.flow = Flow::Halt(op::JUMP);
                        cut = true;
                    }
                    Flow::Branch { fallthrough, .. } => {
                        exit.flow = Flow::Branch {
                            targets: vec![],
                            fallthrough,
                        };
                        cut = true;
                    }
                    _ => {}
                }
            }
            nodes[n].computed_cut = cut;
            let st = exit.state;
            if st.underflowed() {
                // Infeasible path in a real frame (stack underflow): no successors.
                nodes[n].infeasible = true;
                continue;
            }
            let mut succs: Vec<(usize, Edge)> = Vec::new();
            let mut resolve_targets =
                |targets: &[usize],
                 kind: Edge,
                 st: &AState,
                 nodes: &mut Vec<UNode>,
                 index: &mut HashMap<(usize, Sig), usize>,
                 work: &mut VecDeque<usize>,
                 succs: &mut Vec<(usize, Edge)>,
                 call: &mut Option<CallInfo>| {
                    for &t in targets {
                        // Is this an internal call? Only JUMPs (not JUMPIs) can be calls.
                        if kind == Edge::Jump {
                            let sub = self.summary(t);
                            let mut call_conts: Vec<(usize, Exit, AVal)> = Vec::new();
                            for ex in &sub.exits {
                                let mut s2 = st.clone();
                                let via = resolve(ex.via, &mut s2);
                                if let Some(pc) = to_usize(via) {
                                    if let Some(cb) = prog.target_block(pc) {
                                        call_conts.push((cb, ex.clone(), ex.via));
                                    }
                                }
                            }
                            if !call_conts.is_empty() {
                                let ex0 = &call_conts[0].1;
                                let ret_slot = match call_conts[0].2 {
                                    AVal::Slot(i) => Some(i),
                                    _ => None,
                                };
                                *call = Some(CallInfo {
                                    callee: t,
                                    consumed: ex0.consumed,
                                    pushed: ex0.pushed.clone(),
                                    ret_slot,
                                });
                                for (cb, ex, _) in &call_conts {
                                    let mut s2 = st.clone();
                                    apply_exit(ex, &mut s2);
                                    // The callee may have written memory: forget those words.
                                    for &o in &sub.mem_written {
                                        Rc::make_mut(&mut s2.mem.words).remove(&o);
                                    }
                                    if sub.mem_clobbered {
                                        s2.mem.clobbered = true;
                                    }
                                    let id = intern(*cb, &s2, nodes, index, work);
                                    if !succs.contains(&(id, Edge::Return)) {
                                        succs.push((id, Edge::Return));
                                    }
                                }
                                continue;
                            }
                        }
                        let id = intern(t, st, nodes, index, work);
                        if !succs.contains(&(id, kind)) {
                            succs.push((id, kind));
                        }
                    }
                };
            let mut call = None;
            match exit.flow {
                Flow::Jump(ref targets) => {
                    if targets.is_empty() {
                        nodes[n].unresolved = true;
                    }
                    resolve_targets(
                        targets,
                        Edge::Jump,
                        &st,
                        &mut nodes,
                        &mut index,
                        &mut work,
                        &mut succs,
                        &mut call,
                    )
                }
                Flow::Branch {
                    ref targets,
                    fallthrough,
                } => {
                    resolve_targets(
                        targets,
                        Edge::True,
                        &st,
                        &mut nodes,
                        &mut index,
                        &mut work,
                        &mut succs,
                        &mut call,
                    );
                    if let Some(f) = fallthrough {
                        let id = intern(f, &st, &mut nodes, &mut index, &mut work);
                        succs.push((id, Edge::False));
                    }
                }
                Flow::Fallthrough(f) => {
                    let id = intern(f, &st, &mut nodes, &mut index, &mut work);
                    succs.push((id, Edge::Fallthrough));
                }
                Flow::Return(via) => {
                    if let Some(pc) = to_usize(via) {
                        if let Some(cb) = prog.target_block(pc) {
                            let id = intern(cb, &st, &mut nodes, &mut index, &mut work);
                            succs.push((id, Edge::Jump));
                        } else {
                            nodes[n].unresolved = true;
                        }
                    } else if via.is_token() {
                        nodes[n].returns_via = Some(via);
                    } else {
                        nodes[n].unresolved = true;
                    }
                }
                Flow::BranchUnresolved { fallthrough, .. } => {
                    nodes[n].unresolved = true;
                    if let Some(f) = fallthrough {
                        let id = intern(f, &st, &mut nodes, &mut index, &mut work);
                        succs.push((id, Edge::False));
                    }
                }
                Flow::Halt(_) => {}
            }
            nodes[n].call = call;
            for (s, _) in &succs {
                if !nodes[*s].preds.contains(&n) {
                    nodes[*s].preds.push(n);
                }
            }
            nodes[n].succs = succs;
        }
        Unit {
            entry_block,
            nodes,
            entry,
            budget_exhausted,
        }
    }
}

impl Unit {
    /// The sub-unit reachable from node `entry` (ids remapped), for lifting a region separately.
    pub fn slice(&self, entry: usize) -> (Unit, HashMap<usize, usize>) {
        let mut order = Vec::new();
        let mut seen = HashSet::new();
        let mut q = VecDeque::new();
        q.push_back(entry);
        while let Some(x) = q.pop_front() {
            if !seen.insert(x) {
                continue;
            }
            order.push(x);
            for (s, _) in &self.nodes[x].succs {
                q.push_back(*s);
            }
        }
        let map: HashMap<usize, usize> = order.iter().enumerate().map(|(i, n)| (*n, i)).collect();
        let mut nodes = Vec::new();
        for &old in &order {
            let mut nd = self.nodes[old].clone();
            nd.id = map[&old];
            nd.succs = nd.succs.iter().map(|(s, k)| (map[s], *k)).collect();
            nd.preds = nd
                .preds
                .iter()
                .filter_map(|p| map.get(p).copied())
                .collect();
            nodes.push(nd);
        }
        (
            Unit {
                entry_block: self.nodes[entry].block,
                nodes,
                entry: 0,
                budget_exhausted: self.budget_exhausted,
            },
            map,
        )
    }
}

/// Whole-program recovery result.
#[derive(Debug)]
pub struct Recovered {
    /// The public entry: dispatcher and external function bodies.
    pub main: Unit,
    /// Internal functions: entry block -> unit.
    pub functions: BTreeMap<usize, Unit>,
    /// Orphan regions (blocks reached by nothing), by entry block.
    pub orphans: BTreeMap<usize, Unit>,
    /// End offsets of blocks whose jump could not be resolved, sorted and deduplicated.
    pub unresolved_jumps: Vec<usize>,
    /// Some walk or summary ran out of budget; the result is incomplete.
    pub budget_exhausted: bool,
}

/// Recover the control flow of a whole runtime.
pub fn recover(prog: &Program, code_end: usize) -> Recovered {
    let an = Analysis::new(prog);
    if prog.blocks.is_empty() {
        return Recovered {
            main: Unit {
                entry_block: 0,
                nodes: vec![],
                entry: 0,
                budget_exhausted: false,
            },
            functions: BTreeMap::new(),
            orphans: BTreeMap::new(),
            unresolved_jumps: vec![],
            budget_exhausted: false,
        };
    }
    let _ = an.summary(0);
    let main = an.build_unit(0, AState::root());
    let mut functions = BTreeMap::new();
    // Internal functions: call targets discovered while building units, transitively.
    let mut pending: Vec<usize> = an.call_targets.borrow().iter().copied().collect();
    pending.sort_unstable();
    let mut done: HashSet<usize> = HashSet::new();
    while let Some(f) = pending.pop() {
        if !done.insert(f) {
            continue;
        }
        let unit = an.build_unit(f, AState::new());
        for n in &unit.nodes {
            if let Some(c) = &n.call {
                if !done.contains(&c.callee) {
                    pending.push(c.callee);
                }
            }
        }
        functions.insert(f, unit);
    }
    // Also units for call targets referenced from main
    for n in &main.nodes {
        if let Some(c) = &n.call {
            if !done.contains(&c.callee) {
                done.insert(c.callee);
                let unit = an.build_unit(c.callee, AState::new());
                functions.insert(c.callee, unit);
            }
        }
    }
    // Coverage: which blocks appear in some unit.
    let mut covered: HashSet<usize> = HashSet::new();
    for n in &main.nodes {
        covered.insert(n.block);
    }
    for u in functions.values() {
        for n in &u.nodes {
            covered.insert(n.block);
        }
    }
    let mut orphans = BTreeMap::new();
    let mut unresolved = Vec::new();
    let mut orphan_nodes = 0usize;
    for b in &prog.blocks {
        if b.start >= code_end {
            break;
        }
        if !covered.contains(&b.id) && b.is_jumpdest {
            if orphan_nodes > MAX_ORPHAN_NODES {
                // Budget: remaining unreached blocks stay uncovered (reported in the statistics).
                break;
            }
            let unit =
                an.build_unit_opts(b.id, AState::new(), ComputedJumps::Ignore, MAX_WALK_NODES);
            orphan_nodes += unit.nodes.len();
            for n in &unit.nodes {
                covered.insert(n.block);
            }
            orphans.insert(b.id, unit);
        }
    }
    for u in std::iter::once(&main)
        .chain(functions.values())
        .chain(orphans.values())
    {
        for n in &u.nodes {
            if n.unresolved {
                unresolved.push(prog.blocks[n.block].end);
            }
        }
    }
    unresolved.sort_unstable();
    unresolved.dedup();
    let budget = *an.budget_exhausted.borrow()
        || main.budget_exhausted
        || functions.values().any(|u| u.budget_exhausted);
    Recovered {
        main,
        functions,
        orphans,
        unresolved_jumps: unresolved,
        budget_exhausted: budget,
    }
}
