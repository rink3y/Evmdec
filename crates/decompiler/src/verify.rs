//! Block-level lifting oracle.
//!
//! Every basic block is executed from random states twice: by the concrete interpreter
//! (`interp`) and by evaluating the lifted statements (`lift`) with the same inputs. The exit
//! stack, memory, storage writes, logs, calls and the control decision must agree. This checks the
//! lifter and the expression simplifier on the whole program, reachable or not.

use crate::cfg::{AState, Program, UNode, Unit};
use crate::expr::{self, ExprId, Node};
use crate::interp::{Host, Machine, Outcome, Rng};
use crate::keccak;
use crate::lift::{Lifter, Stmt, Term};
use crate::opcode as op;
use crate::u256::U256;
use serde::Serialize;
use std::collections::HashMap;

/// Totals of one verification pass, per run and per block.
#[derive(Clone, Debug, Default, Serialize)]
pub struct VerifyStats {
    /// Basic blocks in the program.
    pub blocks: usize,
    /// Runs in which the reference interpreter completed the block.
    pub runs: usize,
    /// Runs in which both sides agreed.
    pub agree: usize,
    /// Runs in which the two sides diverged.
    pub mismatch: usize,
    /// Runs that proved nothing (unsupported terminator, memory aliasing between symbolic bases,
    /// or a block for which no executable state was ever found).
    pub inconclusive: usize,
    /// Instructions in blocks whose every run agreed.
    pub instructions_total: usize,
    /// Instructions in verified blocks.
    pub instructions_verified: usize,
    /// Blocks with at least one agreeing run and no mismatch.
    pub blocks_verified: usize,
    /// Blocks with at least one mismatching run.
    pub blocks_mismatched: usize,
    /// Blocks with neither an agreeing nor a mismatching run.
    pub blocks_inconclusive: usize,
    /// Number of inconclusive runs per reason.
    pub inconclusive_reasons: HashMap<String, usize>,
    /// Descriptions of the first mismatches found (at most 50), with the block's start offset.
    pub mismatches: Vec<String>,
}

/// Concrete memory ranges touched through a symbolic base, for the aliasing check.
#[derive(Default)]
struct Accesses {
    /// (base expression or None for constants, start, end)
    ranges: Vec<(Option<ExprId>, u64, u64)>,
}

impl Accesses {
    fn note(&mut self, off: ExprId, start: U256, len: usize) {
        if len == 0 {
            return;
        }
        let (base, _) = crate::expr::split_offset(off);
        if let Some(s) = start.as_usize() {
            self.ranges.push((base, s as u64, s as u64 + len as u64));
        }
    }
    /// Two accesses with different symbolic bases overlapping concretely: the lifter's
    /// no-alias assumption does not hold for this input.
    fn aliased(&self) -> bool {
        for (i, a) in self.ranges.iter().enumerate() {
            for b in &self.ranges[i + 1..] {
                if a.0 != b.0 && a.1 < b.2 && b.1 < a.2 {
                    return true;
                }
            }
        }
        false
    }
}

struct Eval<'a> {
    host: &'a Host,
    stack0: Vec<U256>,
    mem_snapshots: Vec<Vec<u8>>,
    stor_snapshots: Vec<HashMap<U256, U256>>,
    tstor_snapshots: Vec<HashMap<U256, U256>>,
    calls: Vec<(bool, Vec<u8>)>,
    creates: Vec<U256>,
    gas_obs: Vec<U256>,
    msize_obs: Vec<U256>,
    /// Sequence number of each GAS / MSIZE node in program order (rank = observation index).
    gas_rank: HashMap<u32, usize>,
    msize_rank: HashMap<u32, usize>,
    code: &'a [u8],
    returndata: Vec<u8>,
    inconclusive: Option<String>,
}

impl<'a> Eval<'a> {
    fn mem_at(&self, gen: u32) -> &Vec<u8> {
        let i = (gen as usize).min(self.mem_snapshots.len() - 1);
        &self.mem_snapshots[i]
    }
    fn read_word(buf: &[u8], off: U256) -> U256 {
        let mut b = [0u8; 32];
        if let Some(o) = off.as_usize() {
            for (i, out) in b.iter_mut().enumerate() {
                if let Some(x) = buf.get(o.saturating_add(i)) {
                    *out = *x;
                }
            }
        }
        U256::from_be_bytes(&b)
    }
    fn eval(&mut self, e: ExprId, memo: &mut HashMap<ExprId, U256>) -> U256 {
        if let Some(v) = memo.get(&e) {
            return *v;
        }
        let v = match expr::node(e) {
            Node::Const(c) => c,
            Node::Arg(i) => {
                let i = i as usize;
                if i < self.stack0.len() {
                    self.stack0[self.stack0.len() - 1 - i]
                } else {
                    self.inconclusive = Some("stack underflow".into());
                    U256::ZERO
                }
            }
            Node::Env(o, seq) => match o {
                op::ADDRESS => self.host.address,
                op::ORIGIN => self.host.origin,
                op::CALLER => self.host.caller,
                op::CALLVALUE => self.host.callvalue,
                op::CALLDATASIZE => U256::from(self.host.calldata.len()),
                op::CODESIZE => U256::from(self.code.len()),
                op::GASPRICE => self.host.gasprice,
                op::RETURNDATASIZE => U256::from(self.returndata.len()),
                op::COINBASE => self.host.coinbase,
                op::TIMESTAMP => self.host.timestamp,
                op::NUMBER => self.host.number,
                op::PREVRANDAO => self.host.prevrandao,
                op::GASLIMIT => self.host.gaslimit,
                op::CHAINID => self.host.chainid,
                op::SELFBALANCE => self.host.selfbalance,
                op::BASEFEE => self.host.basefee,
                op::BLOBBASEFEE => self.host.blobbasefee,
                op::GAS => {
                    let v = self
                        .gas_rank
                        .get(&seq)
                        .and_then(|i| self.gas_obs.get(*i))
                        .copied();
                    v.unwrap_or_else(|| {
                        self.inconclusive = Some("gas observation".into());
                        U256::ZERO
                    })
                }
                op::MSIZE => {
                    let v = self
                        .msize_rank
                        .get(&seq)
                        .and_then(|i| self.msize_obs.get(*i))
                        .copied();
                    v.unwrap_or_else(|| {
                        self.inconclusive = Some("msize observation".into());
                        U256::ZERO
                    })
                }
                _ => {
                    self.inconclusive = Some(format!("env {}", op::name(o)));
                    U256::ZERO
                }
            },
            Node::CallDataLoad(off) => {
                let o = self.eval(off, memo);
                Self::read_word(&self.host.calldata, o)
            }
            Node::MLoad(off, gen) => {
                let o = self.eval(off, memo);
                Self::read_word(self.mem_at(gen), o)
            }
            Node::SLoad(key, transient, sgen) => {
                let k = self.eval(key, memo);
                let snaps = if transient {
                    &self.tstor_snapshots
                } else {
                    &self.stor_snapshots
                };
                let i = (sgen as usize).min(snaps.len() - 1);
                match snaps[i].get(&k) {
                    Some(v) => *v,
                    None => {
                        if transient {
                            U256::ZERO
                        } else {
                            self.host.storage(k)
                        }
                    }
                }
            }
            Node::Keccak(words, tail) => {
                let mut bytes = Vec::new();
                for (i, w) in words.iter().enumerate() {
                    let v = self.eval(*w, memo).to_be_bytes();
                    if tail > 0 && i == words.len() - 1 {
                        bytes.extend_from_slice(&v[32 - tail as usize..]);
                    } else {
                        bytes.extend_from_slice(&v);
                    }
                }
                U256::from_be_bytes(&keccak::keccak256(&bytes))
            }
            Node::KeccakMem(off, len, gen) => {
                let o = self.eval(off, memo);
                let l = self.eval(len, memo);
                let mem = self.mem_at(gen).clone();
                let n = l.as_usize().unwrap_or(usize::MAX);
                if n > (1 << 24) {
                    self.inconclusive = Some("keccak length".into());
                    U256::ZERO
                } else {
                    let mut buf = vec![0u8; n];
                    if let Some(o) = o.as_usize() {
                        for (i, out) in buf.iter_mut().enumerate() {
                            if let Some(x) = mem.get(o.saturating_add(i)) {
                                *out = *x;
                            }
                        }
                    }
                    U256::from_be_bytes(&keccak::keccak256(&buf))
                }
            }
            Node::CallResult(seq) => match self.calls.get(call_index(seq)) {
                Some((ok, _)) => U256::from(*ok),
                None => {
                    self.inconclusive = Some("call result index".into());
                    U256::ZERO
                }
            },
            Node::CreateResult(seq) => match self.creates.get(call_index(seq)) {
                Some(a) => *a,
                None => {
                    self.inconclusive = Some("create result index".into());
                    U256::ZERO
                }
            },
            Node::ReturnData(seq, off) => {
                let o = self.eval(off, memo);
                match self.calls.get(call_index(seq)) {
                    Some((_, data)) => {
                        // The lifter models the out region as return data: bytes beyond the actual
                        // return data are *not* written by the EVM (old memory stays), so this is only
                        // exact when the data covers the read.
                        if o.as_usize().is_none_or(|o| o + 32 > data.len()) {
                            self.inconclusive = Some("returndata shorter than out region".into());
                        }
                        Self::read_word(data, o)
                    }
                    None => {
                        self.inconclusive = Some("returndata index".into());
                        U256::ZERO
                    }
                }
            }
            Node::CopiedWord(kind, src, gen) => {
                let s = self.eval(src, memo);
                match kind {
                    op::CALLDATACOPY => Self::read_word(&self.host.calldata, s),
                    op::CODECOPY => Self::read_word(self.code, s),
                    op::RETURNDATACOPY => Self::read_word(&self.returndata, s),
                    op::MCOPY => Self::read_word(self.mem_at(gen), s),
                    _ => {
                        self.inconclusive = Some("extcodecopy word".into());
                        U256::ZERO
                    }
                }
            }
            Node::Var(_) | Node::IntRet(..) | Node::Unknown(_) => {
                self.inconclusive = Some("unexpected variable".into());
                U256::ZERO
            }
            Node::Op(o, v) => {
                let a: Vec<U256> = v.iter().map(|x| self.eval(*x, memo)).collect();
                match (o, a.len()) {
                    (op::ISZERO, 1) => U256::from(a[0].is_zero()),
                    (op::NOT, 1) => !a[0],
                    (op::BALANCE, 1) => {
                        if a[0] == self.host.address {
                            self.host.selfbalance
                        } else {
                            self.host.balance(a[0])
                        }
                    }
                    (op::EXTCODESIZE, 1) => {
                        if a[0] == self.host.address {
                            U256::from(self.code.len())
                        } else {
                            self.host.extcodesize(a[0])
                        }
                    }
                    (op::EXTCODEHASH, 1) => self.host.extcodehash(a[0]),
                    (op::BLOCKHASH, 1) => self.host.blockhash(a[0]),
                    (op::BLOBHASH, 1) => self.host.blobhash(a[0]),
                    (op::ADD, 2) => a[0].wrapping_add(a[1]),
                    (op::MUL, 2) => a[0].wrapping_mul(a[1]),
                    (op::SUB, 2) => a[0].wrapping_sub(a[1]),
                    (op::DIV, 2) => a[0] / a[1],
                    (op::SDIV, 2) => a[0].sdiv(a[1]),
                    (op::MOD, 2) => a[0] % a[1],
                    (op::SMOD, 2) => a[0].smod(a[1]),
                    (op::EXP, 2) => a[0].pow(a[1]),
                    (op::SIGNEXTEND, 2) => U256::signextend(a[0], a[1]),
                    (op::LT, 2) => U256::from(a[0] < a[1]),
                    (op::GT, 2) => U256::from(a[0] > a[1]),
                    (op::SLT, 2) => U256::from(a[0].scmp(&a[1]) == std::cmp::Ordering::Less),
                    (op::SGT, 2) => U256::from(a[0].scmp(&a[1]) == std::cmp::Ordering::Greater),
                    (op::EQ, 2) => U256::from(a[0] == a[1]),
                    (op::AND, 2) => a[0] & a[1],
                    (op::OR, 2) => a[0] | a[1],
                    (op::XOR, 2) => a[0] ^ a[1],
                    (op::BYTE, 2) => U256::byte(a[0], a[1]),
                    (op::SHL, 2) => {
                        if a[0] >= U256::from_u64(256) {
                            U256::ZERO
                        } else {
                            a[1] << a[0].low_u64() as u32
                        }
                    }
                    (op::SHR, 2) => {
                        if a[0] >= U256::from_u64(256) {
                            U256::ZERO
                        } else {
                            a[1] >> a[0].low_u64() as u32
                        }
                    }
                    (op::SAR, 2) => {
                        if a[0] >= U256::from_u64(256) {
                            if a[1].is_negative() {
                                U256::MAX
                            } else {
                                U256::ZERO
                            }
                        } else {
                            a[1].sar(a[0].low_u64() as u32)
                        }
                    }
                    (op::ADDMOD, 3) => a[0].addmod(a[1], a[2]),
                    (op::MULMOD, 3) => a[0].mulmod(a[1], a[2]),
                    _ => {
                        self.inconclusive = Some(format!("op {}", op::name(o)));
                        U256::ZERO
                    }
                }
            }
        };
        memo.insert(e, v);
        v
    }
}

/// The lifter numbers calls as `seq_base + k`; in a single-node unit the base is 0.
fn call_index(seq: u32) -> usize {
    (seq & 0x3ff) as usize
}

fn write_mem(mem: &mut Vec<u8>, off: U256, data: &[u8]) -> bool {
    if data.is_empty() {
        return true;
    }
    let Some(o) = off.as_usize().filter(|o| *o < (1 << 26)) else {
        return false;
    };
    let end = o + data.len();
    let rounded = end.div_ceil(32) * 32;
    if rounded > mem.len() {
        mem.resize(rounded, 0);
    }
    mem[o..end].copy_from_slice(data);
    true
}

fn expand_mem(mem: &mut Vec<u8>, off: U256, len: usize) {
    if len == 0 {
        return;
    }
    if let Some(o) = off.as_usize() {
        let rounded = (o + len).div_ceil(32) * 32;
        if rounded > mem.len() {
            mem.resize(rounded, 0);
        }
    }
}

fn copy_from(src: &[u8], s: U256, n: usize) -> Vec<u8> {
    let mut buf = vec![0u8; n];
    if let Some(s) = s.as_usize() {
        for (i, out) in buf.iter_mut().enumerate() {
            if let Some(b) = src.get(s.saturating_add(i)) {
                *out = *b;
            }
        }
    }
    buf
}

/// Required stack depth of a block (how many entries it pops below what it pushes).
fn required_depth(prog: &Program, b: usize) -> usize {
    let mut depth: i64 = 0;
    let mut min: i64 = 0;
    for ins in prog.block_insns(&prog.blocks[b]) {
        let o = ins.opcode;
        let (pops, pushes) = if op::is_dup(o) {
            ((o - 0x7f) as i64, (o - 0x7e) as i64)
        } else if op::is_swap(o) {
            ((o - 0x8e) as i64, (o - 0x8e) as i64)
        } else {
            op::info(o)
                .map(|i| (i.pops as i64, i.pushes as i64))
                .unwrap_or((0, 0))
        };
        depth -= pops;
        min = min.min(depth);
        depth += pushes;
    }
    (-min) as usize
}

/// Parameters of a verification pass.
#[derive(Clone, Debug)]
pub struct VerifyOptions {
    /// Completed reference runs wanted per block; up to ten times as many states are tried.
    pub runs: usize,
    /// Seed of the random states, making a pass reproducible.
    pub seed: u64,
    /// Print each mismatch with the block's lifted statements and exit stack to stderr.
    pub verbose: bool,
}

/// Lifts every block of `code` in isolation and compares it against the interpreter on random
/// states, returning the totals.
pub fn verify(code: &[u8], opts: &VerifyOptions) -> VerifyStats {
    let prog = Program::new(code.to_vec());
    let lifter = Lifter {
        prog: &prog,
        root: false,
        summaries: HashMap::new(),
        oracle: true,
        copy_loops: Default::default(),
    };
    let mut stats = VerifyStats::default();
    let mut rng = Rng::new(opts.seed);
    for b in &prog.blocks {
        stats.blocks += 1;
        let n_ins = b.last - b.first + 1;
        stats.instructions_total += n_ins;
        // Lift the block alone with an unknown entry stack.
        let unit = Unit {
            entry_block: b.id,
            nodes: vec![UNode {
                id: 0,
                block: b.id,
                entry: AState::new(),
                succs: vec![],
                preds: vec![],
                call: None,
                returns_via: None,
                unresolved: true,
                infeasible: false,
                computed_cut: false,
            }],
            entry: 0,
            budget_exhausted: false,
        };
        let lifted = lifter.lift(&unit, None);
        let ln = &lifted.nodes[0];
        let need = required_depth(&prog, b.id).max(lifted.n_args);
        let mut block_ok = true;
        let mut block_inconclusive = false;
        let mut block_agree = 0usize;
        let mut attempts = 0;
        let mut completed = 0;
        let max_attempts = opts.runs * 10;
        while completed < opts.runs && attempts < max_attempts {
            attempts += 1;
            let host = Host::random(&mut rng);
            let depth = need + rng.below(4) as usize;
            // Input phases: mixed random values first; after repeated infeasible states (huge
            // memory offsets) small word-aligned values; then widely spread values so that
            // differently-based memory accesses cannot alias.
            let phase = if attempts <= opts.runs * 2 {
                0
            } else if attempts <= opts.runs * 5 {
                1
            } else {
                2
            };
            let stack0: Vec<U256> = (0..depth)
                .map(|i| match phase {
                    0 => rng.value(),
                    1 => U256::from_u64(32 * rng.below(64)),
                    _ => U256::from_u64(0x2000 * (i as u64 + 1) + 32 * rng.below(8)),
                })
                .collect();
            // Initial memory: mostly plausible word-aligned pointers/small numbers, some random words.
            let mem_words = (rng.below(8) as usize + 1) * 4;
            let mut mem0: Vec<u8> = Vec::with_capacity(mem_words * 32);
            for w in 0..mem_words {
                let word = if phase == 0 && rng.below(3) == 0 {
                    rng.word()
                } else if phase == 2 {
                    U256::from_u64(0x2000 * (w as u64 + 40) + 32 * rng.below(8))
                } else {
                    U256::from_u64(0x80 + 32 * rng.below(64))
                };
                mem0.extend_from_slice(&word.to_be_bytes());
            }
            // Reference run.
            let mut m = Machine::new(code, &host);
            m.stack = stack0.clone();
            m.memory = mem0.clone();
            let rd_len = rng.below(70) as usize;
            m.returndata = rng.bytes(rd_len);
            let returndata0 = m.returndata.clone();
            let outcome = m.run_block(b.start, b.end);
            if let Outcome::Exception(reason) = &outcome {
                // The block cannot execute from this state (e.g. a random stack value used as a huge
                // memory offset): draw another state. Counted only if no state ever works.
                if attempts >= max_attempts && completed == 0 {
                    stats.inconclusive += 1;
                    block_inconclusive = true;
                    *stats
                        .inconclusive_reasons
                        .entry(format!("reference exception: {}", reason))
                        .or_default() += 1;
                }
                continue;
            }
            completed += 1;
            stats.runs += 1;
            // Lifted run.
            // GAS / MSIZE nodes carry increasing sequence numbers in program order; map their
            // rank to the interpreter's observation order.
            let (gas_rank, msize_rank) = {
                let mut gas: Vec<u32> = Vec::new();
                let mut msz: Vec<u32> = Vec::new();
                let mut seen = std::collections::HashSet::new();
                let mut stack: Vec<ExprId> = crate::lift::node_exprs(ln);
                stack.extend(ln.exit_stack.iter().copied());
                while let Some(x) = stack.pop() {
                    if !seen.insert(x) {
                        continue;
                    }
                    match expr::node(x) {
                        Node::Env(op::GAS, s) => gas.push(s),
                        Node::Env(op::MSIZE, s) => msz.push(s),
                        _ => {}
                    }
                    stack.extend(expr::children(x));
                }
                gas.sort_unstable();
                gas.dedup();
                msz.sort_unstable();
                msz.dedup();
                (
                    gas.iter()
                        .enumerate()
                        .map(|(i, s)| (*s, i))
                        .collect::<HashMap<u32, usize>>(),
                    msz.iter()
                        .enumerate()
                        .map(|(i, s)| (*s, i))
                        .collect::<HashMap<u32, usize>>(),
                )
            };
            let mut ev = Eval {
                host: &host,
                stack0: stack0.clone(),
                mem_snapshots: vec![mem0.clone()],
                stor_snapshots: vec![HashMap::new()],
                tstor_snapshots: vec![HashMap::new()],
                calls: Vec::new(),
                creates: Vec::new(),
                gas_obs: m.gas_obs.clone(),
                msize_obs: m.msize_obs.clone(),
                gas_rank,
                msize_rank,
                code,
                returndata: returndata0.clone(),
                inconclusive: None,
            };
            let mut memo: HashMap<ExprId, U256> = HashMap::new();
            let mut mem = mem0.clone();
            let mut storage: HashMap<U256, U256> = HashMap::new();
            let mut transient: HashMap<U256, U256> = HashMap::new();
            let mut logs = Vec::new();
            let mut calls = Vec::new();
            let mut creates = Vec::new();
            let mut diverged: Option<String> = None;
            let mut acc = Accesses::default();
            // Statements in order. The lifter advances the memory generation on every write.
            for s in &ln.stmts {
                match s {
                    Stmt::MStore { off, val, width } => {
                        let o = ev.eval(*off, &mut memo);
                        let v = ev.eval(*val, &mut memo);
                        let bytes = v.to_be_bytes();
                        let data: &[u8] = if *width == 32 {
                            &bytes[..]
                        } else {
                            &bytes[31..]
                        };
                        acc.note(*off, o, data.len());
                        if !write_mem(&mut mem, o, data) {
                            ev.inconclusive = Some("memory offset".into());
                        }
                        ev.mem_snapshots.push(mem.clone());
                    }
                    Stmt::SStore {
                        key,
                        val,
                        transient: t,
                    } => {
                        let k = ev.eval(*key, &mut memo);
                        let v = ev.eval(*val, &mut memo);
                        if *t {
                            transient.insert(k, v);
                            ev.tstor_snapshots.push(transient.clone());
                        } else {
                            storage.insert(k, v);
                            ev.stor_snapshots.push(storage.clone());
                        }
                    }
                    Stmt::Log {
                        off,
                        len,
                        topics,
                        data,
                    } => {
                        let tv: Vec<U256> = topics.iter().map(|t| ev.eval(*t, &mut memo)).collect();
                        let l = ev.eval(*len, &mut memo).as_usize().unwrap_or(0);
                        let o = ev.eval(*off, &mut memo);
                        let bytes = match data {
                            Some(words) => words_to_bytes(words, l, &mut ev, &mut memo),
                            None => copy_from(&mem, o, l),
                        };
                        acc.note(*off, o, l);
                        expand_mem(&mut mem, o, l);
                        logs.push(crate::interp::LogRecord {
                            topics: tv,
                            data: bytes,
                        });
                    }
                    Stmt::Call {
                        kind,
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
                        let g = ev.eval(*gas, &mut memo);
                        let a = ev.eval(*addr, &mut memo);
                        let v = value.map(|v| ev.eval(v, &mut memo)).unwrap_or(U256::ZERO);
                        let io = ev.eval(*in_off, &mut memo);
                        let il = ev.eval(*in_len, &mut memo).as_usize().unwrap_or(0);
                        let oo = ev.eval(*out_off, &mut memo);
                        let olv = ev.eval(*out_len, &mut memo);
                        let ol = olv.as_usize().unwrap_or(0);
                        let input_bytes = match input {
                            Some(words) => words_to_bytes(words, il, &mut ev, &mut memo),
                            None => copy_from(&mem, io, il),
                        };
                        acc.note(*in_off, io, il);
                        acc.note(*out_off, oo, ol);
                        expand_mem(&mut mem, io, il);
                        let idx = calls.len();
                        calls.push(crate::interp::CallRecord {
                            kind: *kind,
                            gas: g,
                            addr: a,
                            value: v,
                            input: input_bytes.clone(),
                            out_off: oo,
                            out_len: olv,
                        });
                        let (ok, data) = if a == U256::from_u64(4) {
                            (true, input_bytes)
                        } else {
                            host.call_result(idx)
                        };
                        ev.calls.push((ok, data.clone()));
                        if ol > 0 {
                            let mut buf = data.clone();
                            buf.truncate(ol);
                            expand_mem(&mut mem, oo, ol);
                            write_mem(&mut mem, oo, &buf);
                        }
                        ev.returndata = data;
                        // One generation per call statement.
                        ev.mem_snapshots.push(mem.clone());
                        if *kind != op::STATICCALL {
                            ev.stor_snapshots.push(storage.clone());
                        }
                    }
                    Stmt::Create {
                        kind,
                        value,
                        off,
                        len,
                        salt,
                        init,
                        ..
                    } => {
                        let v = ev.eval(*value, &mut memo);
                        let o = ev.eval(*off, &mut memo);
                        let l = ev.eval(*len, &mut memo).as_usize().unwrap_or(0);
                        let sv = salt.map(|s| ev.eval(s, &mut memo));
                        let bytes = match init {
                            Some(words) => words_to_bytes(words, l, &mut ev, &mut memo),
                            None => copy_from(&mem, o, l),
                        };
                        acc.note(*off, o, l);
                        expand_mem(&mut mem, o, l);
                        let idx = creates.len();
                        creates.push(crate::interp::CreateRecord {
                            kind: *kind,
                            value: v,
                            init: bytes,
                            salt: sv,
                        });
                        ev.creates.push(host.create_result(idx));
                        ev.returndata = Vec::new();
                        ev.stor_snapshots.push(storage.clone());
                        ev.mem_snapshots.push(mem.clone());
                    }
                    Stmt::Copy {
                        kind,
                        dest,
                        src,
                        len,
                        addr,
                    } => {
                        let d = ev.eval(*dest, &mut memo);
                        let sv = ev.eval(*src, &mut memo);
                        let l = ev.eval(*len, &mut memo).as_usize().unwrap_or(0);
                        let data = match *kind {
                            op::CALLDATACOPY => copy_from(&host.calldata, sv, l),
                            op::CODECOPY => copy_from(code, sv, l),
                            op::RETURNDATACOPY => copy_from(&ev.returndata, sv, l),
                            op::MCOPY => copy_from(&mem, sv, l),
                            op::EXTCODECOPY => {
                                let a = addr.map(|a| ev.eval(a, &mut memo)).unwrap_or(U256::ZERO);
                                let c = if a == host.address {
                                    code.to_vec()
                                } else {
                                    host.extcode(a)
                                };
                                copy_from(&c, sv, l)
                            }
                            _ => vec![0u8; l],
                        };
                        acc.note(*dest, d, l);
                        if *kind == op::MCOPY {
                            acc.note(*src, sv, l);
                        }
                        if !write_mem(&mut mem, d, &data) {
                            ev.inconclusive = Some("memory offset".into());
                        }
                        ev.mem_snapshots.push(mem.clone());
                    }
                    Stmt::Internal { .. }
                    | Stmt::Assign { .. }
                    | Stmt::Drop(_)
                    | Stmt::Require { .. } => {}
                }
            }
            // Terminator.
            let exit_stack: Vec<U256> = ln
                .exit_stack
                .iter()
                .map(|e| ev.eval(*e, &mut memo))
                .collect();
            // Memory reads inside expressions (for the aliasing check).
            {
                let mut seen = std::collections::HashSet::new();
                let mut stack: Vec<ExprId> = crate::lift::node_exprs(ln);
                stack.extend(ln.exit_stack.iter().copied());
                while let Some(x) = stack.pop() {
                    if !seen.insert(x) || seen.len() > 50_000 {
                        continue;
                    }
                    match expr::node(x) {
                        Node::MLoad(off, _) => {
                            let o = ev.eval(off, &mut memo);
                            acc.note(off, o, 32);
                        }
                        Node::KeccakMem(off, len, _) => {
                            let o = ev.eval(off, &mut memo);
                            let l = ev.eval(len, &mut memo).as_usize().unwrap_or(0).min(1 << 24);
                            acc.note(off, o, l);
                        }
                        _ => {}
                    }
                    stack.extend(expr::children(x));
                }
            }
            let lifted_outcome = match &ln.term {
                Term::Unresolved(t) => Outcome::Jump(ev.eval(*t, &mut memo)),
                Term::CondJump { cond, target } => {
                    let t = ev.eval(*target, &mut memo);
                    let c = ev.eval(*cond, &mut memo);
                    Outcome::JumpI(t, c)
                }
                Term::Return { off, len, data } | Term::Revert { off, len, data } => {
                    let l = ev.eval(*len, &mut memo).as_usize().unwrap_or(0);
                    let o = ev.eval(*off, &mut memo);
                    let bytes = match data {
                        Some(words) => words_to_bytes(words, l, &mut ev, &mut memo),
                        None => copy_from(&mem, o, l),
                    };
                    acc.note(*off, o, l);
                    expand_mem(&mut mem, o, l);
                    if matches!(&ln.term, Term::Return { .. }) {
                        Outcome::Return(bytes)
                    } else {
                        Outcome::Revert(bytes)
                    }
                }
                Term::Stop => {
                    if op::is_terminator(b.terminator) {
                        Outcome::Stop
                    } else {
                        Outcome::Fallthrough
                    }
                }
                Term::Invalid => Outcome::Invalid,
                Term::SelfDestruct(a) => Outcome::SelfDestruct(ev.eval(*a, &mut memo)),
                Term::Jump(_) | Term::Infeasible | Term::ReturnDyn { .. } => Outcome::Fallthrough,
                other => {
                    ev.inconclusive =
                        Some(format!("terminator {:?}", std::mem::discriminant(other)));
                    Outcome::Fallthrough
                }
            };
            if let Some(reason) = &ev.inconclusive {
                stats.inconclusive += 1;
                block_inconclusive = true;
                *stats
                    .inconclusive_reasons
                    .entry(reason.clone())
                    .or_default() += 1;
                continue;
            }
            if acc.aliased() {
                // The random state made two differently-based memory accesses overlap: the lifter's
                // documented no-alias assumption does not apply, so the run proves nothing.
                stats.inconclusive += 1;
                block_inconclusive = true;
                *stats
                    .inconclusive_reasons
                    .entry("memory aliasing between symbolic bases".into())
                    .or_default() += 1;
                continue;
            }
            // Compare.
            let mut ref_mem = m.memory.clone();
            let n = ref_mem.len().max(mem.len());
            ref_mem.resize(n, 0);
            let mut our_mem = mem.clone();
            our_mem.resize(n, 0);
            // Compare outcomes modulo the EVM's "exception" cases we don't model identically.
            let outcome_eq = match (&outcome, &lifted_outcome) {
                (Outcome::Fallthrough, Outcome::Fallthrough) => true,
                (a, b) => a == b,
            };
            // Exit stack: the reference stack may contain the untouched part below.
            let ref_stack = &m.stack;
            let stack_eq = if matches!(
                outcome,
                Outcome::Jump(_) | Outcome::JumpI(..) | Outcome::Fallthrough
            ) {
                let k = exit_stack.len();
                // Our explicit exit stack covers the top `k` entries; below them the reference must
                // hold the untouched entry stack.
                let untouched = stack0.len().saturating_sub(lifted.n_args);
                ref_stack.len() == untouched + k
                    && ref_stack[untouched..] == exit_stack[..]
                    && ref_stack[..untouched] == stack0[..untouched]
            } else {
                true
            };
            if !outcome_eq {
                diverged = Some(format!(
                    "outcome {:?} vs {:?}",
                    short(&outcome),
                    short(&lifted_outcome)
                ));
            } else if !stack_eq {
                diverged = Some(format!(
                    "exit stack ref={} ours={}",
                    fmt_stack(ref_stack),
                    fmt_stack(&exit_stack)
                ));
            } else if ref_mem != our_mem {
                let first = ref_mem
                    .iter()
                    .zip(&our_mem)
                    .position(|(a, b)| a != b)
                    .unwrap_or(0);
                diverged = Some(format!("memory differs at offset {:#x}", first));
            } else if m.storage != storage {
                diverged = Some("storage differs".into());
            } else if m.transient != transient {
                diverged = Some("transient storage differs".into());
            } else if m.logs != logs {
                diverged = Some("logs differ".into());
            } else if m.calls != calls {
                diverged = Some("calls differ".into());
            } else if m.creates != creates {
                diverged = Some("creates differ".into());
            }
            match diverged {
                None => {
                    stats.agree += 1;
                    block_agree += 1;
                }
                Some(d) => {
                    stats.mismatch += 1;
                    block_ok = false;
                    if stats.mismatches.len() < 50 {
                        stats
                            .mismatches
                            .push(format!("block {:#x}: {}", b.start, d));
                    }
                    if opts.verbose {
                        eprintln!("MISMATCH block {:#x}..{:#x}: {}", b.start, b.end, d);
                        let names = crate::emit::Names::default();
                        for s in &ln.stmts {
                            eprintln!("    {}", crate::emit::fmt_stmt(s, &names));
                        }
                        if let Some(t) = crate::emit::fmt_term_halt(&ln.term, &names) {
                            eprintln!("    {}", t);
                        }
                        eprintln!(
                            "    exit stack: {}",
                            ln.exit_stack
                                .iter()
                                .map(|e| crate::emit::fmt_expr(*e, &names))
                                .collect::<Vec<_>>()
                                .join(", ")
                        );
                    }
                }
            }
        }
        // A block is verified when at least one conclusive run agreed and none disagreed.
        if !block_ok {
            stats.blocks_mismatched += 1;
        } else if block_agree > 0 {
            stats.blocks_verified += 1;
            stats.instructions_verified += n_ins;
        } else {
            let _ = block_inconclusive;
            stats.blocks_inconclusive += 1;
        }
    }
    stats
}

fn words_to_bytes(
    words: &[ExprId],
    len: usize,
    ev: &mut Eval,
    memo: &mut HashMap<ExprId, U256>,
) -> Vec<u8> {
    let mut out = Vec::with_capacity(len);
    for (i, w) in words.iter().enumerate() {
        let v = ev.eval(*w, memo).to_be_bytes();
        let remaining = len.saturating_sub(out.len());
        if remaining == 0 {
            break;
        }
        if i == words.len() - 1 && remaining < 32 {
            out.extend_from_slice(&v[32 - remaining..]);
        } else {
            out.extend_from_slice(&v[..remaining.min(32)]);
        }
    }
    out.truncate(len);
    out
}

fn short(o: &Outcome) -> String {
    match o {
        Outcome::Return(d) => format!("Return({} bytes)", d.len()),
        Outcome::Revert(d) => format!("Revert({} bytes)", d.len()),
        other => format!("{:?}", other),
    }
}

fn fmt_stack(s: &[U256]) -> String {
    format!(
        "[{}]",
        s.iter().map(|v| v.to_hex()).collect::<Vec<_>>().join(", ")
    )
}
