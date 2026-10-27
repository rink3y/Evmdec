//! Whole-contract decompilation: orchestration and the output model.

use crate::cfg::{self, Program, Recovered};
use crate::emit::{self, Names};
use crate::expr::{self, Node};
use crate::function::{self, FnKind, Mutability, Param};
use crate::lift::{self, Lifted, Lifter, Stmt, Term};
use crate::metadata::{self, BytecodeInfo, CodeKind};
use crate::opcode as op;
use crate::sigs;
use crate::u256::U256;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

#[derive(Clone, Debug, Default)]
pub struct Options {
    /// Emit labels/gotos instead of structured code.
    pub flat: bool,
    /// Include per-node program counters as comments.
    pub pcs: bool,
    /// Decompile embedded creation code (contracts deployed by this one).
    pub embedded: bool,
    /// Do not use the built-in signature dictionary (for measuring inference).
    pub no_sigs: bool,
}

#[derive(Clone, Debug, Serialize)]
pub struct Function {
    pub kind: FnKind,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub selector: Option<String>,
    pub name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub signature: Option<String>,
    pub mutability: Mutability,
    pub params: Vec<Param>,
    pub returns: Vec<String>,
    /// Entry program counter.
    pub pc: usize,
    pub code: String,
    pub nodes: usize,
    pub effects: function::Effects,
    #[serde(skip)]
    pub lifted: Option<Lifted>,
    /// Internal functions this one calls (entry pcs).
    pub calls: Vec<usize>,
    /// Internal-unit argument and return counts.
    pub n_args: usize,
    pub n_rets: usize,
}

#[derive(Clone, Debug, Serialize)]
pub struct StorageVar {
    pub slot: String,
    pub name: String,
    pub ty: String,
    pub reads: usize,
    pub writes: usize,
}

#[derive(Clone, Debug, Serialize)]
pub struct Stats {
    pub code_bytes: usize,
    pub instructions: usize,
    pub blocks: usize,
    pub code_blocks: usize,
    pub covered_blocks: usize,
    pub unresolved_jumps: usize,
    pub budget_exhausted: bool,
    pub external_functions: usize,
    pub internal_functions: usize,
    pub orphans: usize,
    pub lift_reprocess: usize,
    pub time_ms: u128,
}

#[derive(Clone, Debug, Serialize)]
pub struct Contract {
    pub info: BytecodeInfo,
    pub kind: CodeKind,
    pub language: String,
    pub functions: Vec<Function>,
    pub storage: Vec<StorageVar>,
    pub events: Vec<String>,
    pub errors: Vec<String>,
    pub strings: Vec<String>,
    pub selectors_called: Vec<String>,
    pub stats: Stats,
    pub source: String,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub embedded: Vec<Contract>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub constructor: Option<Box<Contract>>,
    /// Storage slots whose value is used as a DELEGATECALL target (proxy implementation slots).
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub delegatecall_slots: Vec<String>,
    /// Constant addresses used as DELEGATECALL targets.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub delegatecall_targets: Vec<String>,
    /// Filled when the contract was fetched by address.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub address: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub chain: Option<String>,
    /// Implementation behind this proxy, when resolved on-chain.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proxy: Option<ProxyRef>,
}

#[derive(Clone, Debug, Serialize)]
pub struct ProxyRef {
    pub kind: String,
    pub implementation: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub admin: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub contract: Option<Box<Contract>>,
}

pub fn decompile(code: &[u8], opts: &Options) -> Contract {
    let t0 = std::time::Instant::now();
    let info = metadata::analyze(code);
    let mut c = decompile_runtime(&info.runtime, &info, opts);
    if info.kind == CodeKind::Creation && !info.constructor.is_empty() {
        let cinfo = BytecodeInfo { kind: CodeKind::Runtime, runtime: info.constructor.clone(), constructor: vec![], constructor_args: vec![], runtime_offset: 0, runtime_len: info.constructor.len(), constructor_args_len: 0, metadata: None, constructor_metadata: None };
        let mut ctor = decompile_runtime(&info.constructor, &cinfo, opts);
        for f in ctor.functions.iter_mut() {
            if f.kind == FnKind::Fallback || (f.kind == FnKind::External && false) {
                f.kind = FnKind::Constructor;
                f.name = "constructor".into();
            }
        }
        ctor.source = render(&ctor, "constructor");
        c.constructor = Some(Box::new(ctor));
    }
    c.stats.time_ms = t0.elapsed().as_millis();
    c.source = render(&c, "Contract");
    c
}

fn detect_language(info: &BytecodeInfo, code: &[u8]) -> String {
    if let Some(m) = &info.metadata {
        return match m.version.as_ref() {
            Some(v) => format!("{} {}", m.compiler, v),
            None => m.compiler.clone(),
        };
    }
    // Vyper (< 0.3.10) has no metadata; solc runtime starts with the free-memory-pointer setup.
    let solc_prologue = code.len() > 4 && code[0] == 0x60 && (code[1] == 0x80 || code[1] == 0x60) && code[2] == 0x60 && code[3] == 0x40 && code[4] == 0x52;
    if solc_prologue {
        return "solc (unknown version, no metadata)".into();
    }
    if code.len() > 2 && code[0] == 0x60 && code[1] == 0x04 && code[2] == 0x36 {
        return "vyper (< 0.3.10, no metadata)".into();
    }
    "unknown".into()
}

pub fn decompile_runtime(code: &[u8], info: &BytecodeInfo, opts: &Options) -> Contract {
    let t0 = std::time::Instant::now();
    let timing = std::env::var("EVMDEC_TIMING").is_ok();
    if timing {
        eprintln!("[timing] start runtime of {} bytes", code.len());
    }
    let prog = Program::new(code.to_vec());
    let mut code_end = info.metadata.as_ref().map(|m| m.offset).unwrap_or(code.len());
    let mut rec = cfg::recover(&prog, code_end);
    if info.metadata.is_none() {
        // Without a metadata trailer the end of the code is unknown: a trailing region that is
        // reached by nothing and whose JUMPDESTs are referenced by no PUSH in reached code is data
        // (Vyper constants, embedded payloads), not code.
        let reached: BTreeSet<usize> = std::iter::once(&rec.main).chain(rec.functions.values()).flat_map(|u| u.nodes.iter().map(|n| n.block)).collect();
        if let Some(last) = reached.iter().max() {
            let last_end = prog.blocks[*last].end;
            let referenced: HashSet<usize> = std::iter::once(&rec.main).chain(rec.functions.values()).flat_map(|u| u.nodes.iter()).flat_map(|n| prog.block_insns(&prog.blocks[n.block]).iter().filter_map(|i| i.imm.and_then(|v| v.as_usize()))).filter(|pc| *pc >= last_end && prog.jumpdests.contains(pc)).collect();
            if referenced.is_empty() && last_end < code.len() {
                code_end = last_end;
                rec = cfg::recover(&prog, code_end);
            }
        }
    }
    // Embedded creation code (CODECOPY'd into memory and fed to CREATE/CREATE2) is data for the
    // purposes of this contract: it is excluded from coverage and decompiled separately on request.
    let embedded_ranges = embedded_regions(&prog, &rec);
    let in_embedded = |pc: usize| embedded_ranges.iter().any(|(o, l)| pc >= *o && pc < *o + *l);
    if !embedded_ranges.is_empty() {
        // Re-run recovery so that orphan discovery skips the embedded bytes.
        let keep: HashSet<usize> = prog.blocks.iter().filter(|b| !in_embedded(b.start)).map(|b| b.id).collect();
        rec.orphans.retain(|b, _| keep.contains(b));
        rec.unresolved_jumps.retain(|pc| !in_embedded(*pc));
    }
    let language = detect_language(info, code);
    let vyper = language.starts_with("vyper");

    let tick = |label: &str, t: &mut std::time::Instant| {
        if timing {
            eprintln!("[timing] {}: {:?}", label, t.elapsed());
            *t = std::time::Instant::now();
        }
    };
    let mut tt = std::time::Instant::now();
    tick("recover", &mut tt);
    // Internal function units first: simple ones (ABI decoders/encoders, getters) are summarised
    // and seen through at their call sites.
    let mut int_lifter = Lifter { prog: &prog, root: false, summaries: HashMap::new(), oracle: false };
    let mut internals: BTreeMap<usize, Lifted> = BTreeMap::new();
    let mut by_block: Vec<(usize, Lifted)> = Vec::new();
    // Callees before callers where possible: iterate until the summary set stabilises.
    for _round in 0..3 {
        by_block.clear();
        for (b, unit) in &rec.functions {
            let l = int_lifter.lift(unit, None);
            by_block.push((*b, l));
        }
        let mut sums = HashMap::new();
        for (b, l) in &by_block {
            if let Some(sm) = lift::summarize(l) {
                sums.insert(*b, sm);
            }
        }
        let same = sums.len() == int_lifter.summaries.len() && sums.keys().all(|k| int_lifter.summaries.contains_key(k));
        int_lifter.summaries = sums;
        if same {
            break;
        }
    }
    for (b, l) in by_block {
        internals.insert(prog.blocks[b].start, l);
    }
    tick("lift internals", &mut tt);
    let lifter = Lifter { prog: &prog, root: true, summaries: int_lifter.summaries.clone(), oracle: false };
    let main = lifter.lift(&rec.main, None);
    let dispatch = function::discover(&main);
    let contract_nonpayable = function::dispatcher_nonpayable(&main, &dispatch.dispatcher);
    tick("lift main", &mut tt);
    let mut orphans: BTreeMap<usize, Lifted> = BTreeMap::new();
    for (b, unit) in &rec.orphans {
        let t1 = std::time::Instant::now();
        orphans.insert(prog.blocks[*b].start, int_lifter.lift(unit, None));
        if timing && t1.elapsed().as_millis() > 200 {
            eprintln!("[timing] slow orphan {:#x}: nodes={} {:?}", prog.blocks[*b].start, unit.nodes.len(), t1.elapsed());
        }
    }
    tick("lift orphans", &mut tt);
    // Map callee block ids to pcs in Internal statements.
    let block_pc: HashMap<usize, usize> = prog.blocks.iter().map(|b| (b.id, b.start)).collect();

    let mut functions: Vec<Function> = Vec::new();
    let reprocess = main.reprocess_count + internals.values().map(|l| l.reprocess_count).sum::<usize>();

    // Effects of internal functions (transitive).
    let mut int_effects: HashMap<usize, function::Effects> = HashMap::new();
    for (pc, l) in &internals {
        let mut e = function::effects(l);
        e.internal_callees = e.internal_callees.iter().map(|b| block_pc[b]).collect();
        int_effects.insert(*pc, e);
    }
    let transitive = |e: &function::Effects, int_effects: &HashMap<usize, function::Effects>| -> function::Effects {
        let mut acc = e.clone();
        let mut seen: HashSet<usize> = HashSet::new();
        let mut stack: Vec<usize> = acc.internal_callees.clone();
        while let Some(c) = stack.pop() {
            if !seen.insert(c) {
                continue;
            }
            if let Some(ce) = int_effects.get(&c) {
                acc.writes_storage |= ce.writes_storage;
                acc.reads_storage |= ce.reads_storage;
                acc.logs |= ce.logs;
                acc.calls |= ce.calls;
                acc.static_calls |= ce.static_calls;
                acc.creates |= ce.creates;
                acc.selfdestruct |= ce.selfdestruct;
                acc.delegatecall |= ce.delegatecall;
                acc.reads_env |= ce.reads_env;
                stack.extend(ce.internal_callees.iter().copied());
            }
        }
        acc
    };

    // Leak the internal graphs for the lifetime of this analysis so the resolver can hand out
    // `&'static` references (the decompiler is a one-shot process per contract).
    let internals_static: &'static HashMap<usize, Lifted> = Box::leak(Box::new(internals.iter().map(|(pc, l)| (*pc, l.clone())).collect::<HashMap<usize, Lifted>>()));
    let pc_of_block: HashMap<usize, usize> = block_pc.clone();
    let resolve = move |block: usize| -> Option<&'static Lifted> { pc_of_block.get(&block).and_then(|pc| internals_static.get(pc)) };
    let make = |kind: FnKind, selector: Option<u32>, l: Lifted, pc: usize, name_hint: Option<String>, n_args: usize, n_rets: usize| -> Function {
        let mut eff = function::effects(&l);
        eff.internal_callees = eff.internal_callees.iter().map(|b| block_pc[b]).collect();
        let calls = eff.internal_callees.clone();
        let eff = transitive(&eff, &int_effects);
        let mut params = if matches!(kind, FnKind::External) {
            let exprs = function::exprs_with_callees(&l, &resolve, 2);
            function::infer_params_from(&exprs)
        } else {
            vec![]
        };
        let mut returns = if matches!(kind, FnKind::External) { function::infer_returns(&l) } else { vec![] };
        let signature = if opts.no_sigs { None } else { selector.and_then(sigs::function).map(|s| s.to_string()) };
        let name = match (&signature, name_hint, selector) {
            (Some(s), _, _) => sigs::name_of(s).to_string(),
            (None, Some(h), _) => h,
            (None, None, Some(sel)) => format!("func_{:08x}", sel),
            (None, None, None) => format!("func_{:#x}", pc),
        };
        if let Some(sig) = &signature {
            let tys = sigs::params_of(sig);
            if tys.len() >= params.len() {
                params = tys.iter().enumerate().map(|(i, t)| Param { index: i as u32, ty: t.clone(), name: format!("arg{}", i) }).collect();
            }
        }
        let nonpayable = contract_nonpayable || function::is_nonpayable(&l);
        let state_changing = eff.writes_storage || eff.logs || eff.calls || eff.creates || eff.selfdestruct;
        let mutability = if state_changing || kind == FnKind::Fallback || kind == FnKind::Receive {
            if nonpayable { Mutability::NonPayable } else { Mutability::Payable }
        } else if !nonpayable && kind == FnKind::External {
            Mutability::Payable
        } else if eff.reads_storage || eff.reads_env || eff.static_calls {
            Mutability::View
        } else {
            Mutability::Pure
        };
        if kind == FnKind::Receive {
            returns.clear();
        }
        Function { kind, selector: selector.map(|s| format!("{:#010x}", s)), name, signature, mutability, params, returns, pc, code: String::new(), nodes: l.nodes.len(), effects: eff, lifted: Some(l), calls, n_args, n_rets }
    };

    // Each external function is lifted again on its own from the state the dispatcher hands it,
    // so that code shared between functions (ABI-encoding tails, reverts) is specialised per
    // function instead of merged across all of them.
    let unit_node_of = |lifted_node: usize| -> Option<usize> { main.node_map.iter().find(|(_, v)| **v == lifted_node).map(|(k, _)| *k) };
    let relift = |entry: usize| -> Lifted {
        if let Some(un) = unit_node_of(entry) {
            if let Some(state) = Lifter::entry_state_of(&main, un) {
                let (sub, _) = rec.main.slice(un);
                return lifter.lift_from(&sub, state);
            }
        }
        function::slice(&main, entry)
    };
    for d in &dispatch.functions {
        let sl = relift(d.entry);
        let pc = main.nodes[d.entry].pc;
        functions.push(make(FnKind::External, Some(d.selector), sl, pc, None, 0, 0));
    }
    if let Some(r) = dispatch.receive {
        let sl = relift(r);
        functions.push(make(FnKind::Receive, None, sl, main.nodes[r].pc, Some("receive".into()), 0, 0));
    }
    if let Some(f) = dispatch.fallback {
        let sl = relift(f);
        functions.push(make(FnKind::Fallback, None, sl, main.nodes[f].pc, Some("fallback".into()), 0, 0));
    }
    if dispatch.functions.is_empty() && dispatch.fallback.is_none() && dispatch.receive.is_none() {
        // No dispatcher at all: the whole runtime is one entry (e.g. a hand-written contract).
        functions.push(make(FnKind::Fallback, None, main.clone(), 0, Some("fallback".into()), 0, 0));
    }
    for (pc, l) in internals {
        let n_rets = l.nodes.iter().filter_map(|n| if let Term::InternalReturn(v) = &n.term { Some(v.len()) } else { None }).max().unwrap_or(0);
        let n_args = match l.ret_slot {
            Some(k) => (k as usize).min(l.n_args),
            None => l.n_args,
        };
        functions.push(make(FnKind::Internal, None, l, pc, Some(format!("func_{:#x}", pc)), n_args, n_rets));
    }
    for (pc, l) in orphans {
        let n_args = l.n_args;
        functions.push(make(FnKind::Orphan, None, l, pc, Some(format!("orphan_{:#x}", pc)), n_args, 0));
    }

    // Inventories.
    let (storage, events, errors, mut strings, selectors_called) = inventories(&functions, vyper);
    for st in scan_strings(code, code_end) {
        if !strings.iter().any(|x| x.contains(&st)) {
            strings.push(st);
        }
    }
    strings.sort();
    strings.dedup();

    tick("discover+inventories", &mut tt);
    // Render code for each function.
    for f in functions.iter_mut() {
        let names = make_names(f, &storage, vyper);
        let l = f.lifted.as_ref().unwrap();
        let t1 = std::time::Instant::now();
        let body = if opts.flat { emit::fmt_flat(l, &names, "        ") } else { crate::structure::fmt_structured(l, &names, "        ") };
        if timing && t1.elapsed().as_millis() > 200 {
            eprintln!("[timing] slow render {} nodes={} {:?}", f.name, l.nodes.len(), t1.elapsed());
        }
        f.code = body;
    }
    tick("render", &mut tt);

    let covered: BTreeSet<usize> = std::iter::once(&rec.main).chain(rec.functions.values()).chain(rec.orphans.values()).flat_map(|u| u.nodes.iter().map(|n| n.block)).collect();
    let code_blocks = prog.blocks.iter().filter(|b| b.start < code_end && !in_embedded(b.start)).count();
    let stats = Stats {
        code_bytes: code.len(),
        instructions: prog.insns.len(),
        blocks: prog.blocks.len(),
        code_blocks,
        covered_blocks: covered.iter().filter(|b| prog.blocks[**b].start < code_end && !in_embedded(prog.blocks[**b].start)).count(),
        unresolved_jumps: rec.unresolved_jumps.len(),
        budget_exhausted: rec.budget_exhausted,
        external_functions: functions.iter().filter(|f| f.kind == FnKind::External).count(),
        internal_functions: functions.iter().filter(|f| f.kind == FnKind::Internal).count(),
        orphans: functions.iter().filter(|f| f.kind == FnKind::Orphan).count(),
        lift_reprocess: reprocess,
        time_ms: t0.elapsed().as_millis(),
    };

    let mut embedded = Vec::new();
    if opts.embedded {
        for region in embedded_ranges.iter().copied() {
            let sub = &code[region.0..region.0 + region.1];
            let sub_info = metadata::analyze(sub);
            if sub_info.kind == CodeKind::Creation || sub_info.metadata.is_some() {
                let mut sc = decompile(sub, &Options { embedded: false, ..opts.clone() });
                sc.source = render(&sc, &format!("Embedded_{:#x}", region.0));
                embedded.push(sc);
            }
        }
    }

    // Delegatecall targets (proxy resolution).
    let mut dc_slots: Vec<String> = Vec::new();
    let mut dc_targets: Vec<String> = Vec::new();
    for f in &functions {
        let Some(l) = &f.lifted else { continue };
        for nd in &l.nodes {
            for st in &nd.stmts {
                if let Stmt::Call { kind: op::DELEGATECALL, addr, .. } = st {
                    let a = match expr::node(*addr) {
                        Node::Op(op::AND, v) => v[0],
                        _ => *addr,
                    };
                    match expr::node(a) {
                        Node::SLoad(k, false, _) => {
                            if let Some(c) = expr::as_const(k) {
                                let h = c.to_hex_padded(32);
                                if !dc_slots.contains(&h) {
                                    dc_slots.push(h);
                                }
                            }
                        }
                        Node::Const(c) => {
                            let h = c.to_hex_padded(20);
                            if !dc_targets.contains(&h) {
                                dc_targets.push(h);
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
    }
    let mut c = Contract { info: info.clone(), kind: info.kind, language, functions, storage, events, errors, strings, selectors_called, stats, source: String::new(), embedded, constructor: None, delegatecall_slots: dc_slots, delegatecall_targets: dc_targets, address: None, chain: None, proxy: None };
    c.source = render(&c, "Contract");
    c
}

/// Code regions copied to memory and fed to CREATE/CREATE2 (embedded contracts).
fn embedded_regions(prog: &Program, rec: &Recovered) -> Vec<(usize, usize)> {
    let mut out: Vec<(usize, usize)> = Vec::new();
    // Heuristic: constant CODECOPY of a large region that starts at a block boundary past the dispatcher.
    for u in std::iter::once(&rec.main).chain(rec.functions.values()) {
        for n in &u.nodes {
            let b = &prog.blocks[n.block];
            let insns = prog.block_insns(b);
            for (i, ins) in insns.iter().enumerate() {
                if ins.opcode == op::CODECOPY && i >= 3 {
                    let st = metadata::constant_stack(&insns[..i]);
                    let l = st.len();
                    if l >= 3 {
                        if let (Some(off), Some(len)) = (st[l - 2].and_then(|v| v.as_usize()), st[l - 3].and_then(|v| v.as_usize())) {
                            if len >= 64 && off + len <= prog.code.len() && off > b.end && !out.contains(&(off, len)) {
                                out.push((off, len));
                            }
                        }
                    }
                }
            }
        }
    }
    out.sort();
    out
}

pub fn make_names(f: &Function, storage: &[StorageVar], vyper: bool) -> Names {
    let mut n = Names::default();
    n.vyper = vyper;
    for p in &f.params {
        n.params.insert(p.index, p.name.clone());
    }
    if let Some(l) = &f.lifted {
        // Internal units: Arg(i) below the return slot k are the parameters, last pushed on top.
        let k = l.ret_slot.map(|k| k as usize).unwrap_or(l.n_args);
        for i in 0..l.n_args.max(k + 1) {
            let name = if i < k {
                format!("arg{}", k - 1 - i)
            } else if i == k && l.ret_slot.is_some() {
                "__return_pc".to_string()
            } else {
                format!("caller_stack{}", i - k - if l.ret_slot.is_some() { 1 } else { 0 })
            };
            n.args.insert(i as u32, name);
        }
    }
    for s in storage {
        if let Some(slot) = U256::from_hex_str(&s.slot).or_else(|| U256::from_dec_str(&s.slot)) {
            n.storage.insert(slot, s.name.clone());
        }
    }
    n
}

fn inventories(functions: &[Function], vyper: bool) -> (Vec<StorageVar>, Vec<String>, Vec<String>, Vec<String>, Vec<String>) {
    let mut slots: BTreeMap<U256, (usize, usize, BTreeSet<String>)> = BTreeMap::new();
    let mut events: BTreeSet<String> = BTreeSet::new();
    let mut errors: BTreeSet<String> = BTreeSet::new();
    let mut strings: BTreeSet<String> = BTreeSet::new();
    let mut selectors: BTreeSet<String> = BTreeSet::new();
    let names = Names { vyper, ..Default::default() };
    for f in functions {
        let Some(l) = &f.lifted else { continue };
        for nd in &l.nodes {
            for s in &nd.stmts {
                match s {
                    Stmt::SStore { key, val, transient: false } => {
                        note_slot(*key, &mut slots, false, Some(*val), vyper);
                    }
                    Stmt::Log { topics, .. } => {
                        if let Some(t0) = topics.first().and_then(|t| expr::as_const(*t)) {
                            match sigs::event(&t0.to_be_bytes()) {
                                Some(sig) => events.insert(sig.to_string()),
                                None => events.insert(format!("{} (unknown, {} indexed)", t0.to_hex_padded(32), topics.len() - 1)),
                            };
                        } else if topics.is_empty() {
                            events.insert("<anonymous log0>".into());
                        }
                    }
                    Stmt::Call { input, in_len, .. } => {
                        if let Some(words) = input {
                            if let Some(c0) = words.first().and_then(|w| expr::as_const(*w)) {
                                let in_len_c = expr::as_const(*in_len).and_then(|l| l.as_usize());
                                let first_bytes = in_len_c.map(|l| l.min(32)).unwrap_or(32) as u32;
                                if in_len_c.map_or((c0 & expr::mask_bits(224)).is_zero(), |l| l >= 4 && (l - 4) % 32 == 0) {
                                    let sel = c0.shr(8 * (first_bytes - 4)).low_u64() as u32;
                                    if in_len_c.map_or(true, |l| l >= 4) {
                                        selectors.insert(match sigs::function(sel) {
                                            Some(sig) => format!("{:#010x} {}", sel, sig),
                                            None => format!("{:#010x}", sel),
                                        });
                                    }
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
            if let Term::Revert { data: Some(words), .. } = &nd.term {
                if let Some(c0) = words.first().and_then(|w| expr::as_const(*w)) {
                    if (c0 & expr::mask_bits(224)).is_zero() {
                        let sel = c0.shr(224).low_u64() as u32;
                        if sel == 0x08c379a0 {
                            if let Some(s) = emit::decode_string_payload(words) {
                                strings.insert(s);
                            }
                        } else if sel != 0x4e487b71 {
                            errors.insert(match sigs::error(sel) {
                                Some(sig) => sig.to_string(),
                                None => format!("{:#010x} (unknown custom error)", sel),
                            });
                        }
                    }
                }
            }
            for e in lift::node_exprs(nd) {
                collect_sloads(e, &mut slots, vyper);
                collect_strings(e, &mut strings);
            }
        }
    }
    let _ = names;
    let storage: Vec<StorageVar> = slots
        .into_iter()
        .map(|(slot, (reads, writes, tys))| {
            let ty = if tys.is_empty() { "uint256".to_string() } else if tys.len() == 1 { tys.into_iter().next().unwrap() } else {
                // Prefer the most specific.
                let mut v: Vec<String> = tys.into_iter().collect();
                v.sort_by_key(|t| if t.starts_with("mapping") { 0 } else if t.contains('[') { 1 } else if t == "address" || t == "bool" { 2 } else { 3 });
                v[0].clone()
            };
            let name = if slot.bits() <= 32 { format!("stor_{}", slot.to_decimal()) } else { format!("stor_{}", slot.to_hex()) };
            StorageVar { slot: slot.to_hex(), name, ty, reads, writes }
        })
        .collect();
    (storage, events.into_iter().collect(), errors.into_iter().collect(), strings.into_iter().collect(), selectors.into_iter().collect())
}

fn note_slot(key: expr::ExprId, slots: &mut BTreeMap<U256, (usize, usize, BTreeSet<String>)>, read: bool, val: Option<expr::ExprId>, vyper: bool) {
    let (root, ty) = slot_root(key, vyper);
    let Some(root) = root else { return };
    let e = slots.entry(root).or_insert((0, 0, BTreeSet::new()));
    if read {
        e.0 += 1;
    } else {
        e.1 += 1;
    }
    if let Some(t) = ty {
        e.2.insert(t);
    } else if let Some(v) = val {
        let t = function::type_of_value(v);
        if t != "uint256" {
            e.2.insert(t);
        }
    }
}

/// Root slot of a storage key and the shape of the variable it implies.
fn slot_root(key: expr::ExprId, vyper: bool) -> (Option<U256>, Option<String>) {
    if let Some(c) = expr::as_const(key) {
        return (Some(c), None);
    }
    match expr::node(key) {
        Node::Keccak(words, 0) if words.len() == 2 => {
            let (k, s) = if vyper { (words[1], words[0]) } else { (words[0], words[1]) };
            let (root, inner) = slot_root(s, vyper);
            let kt = function::type_of_value(k);
            let kt = if kt == "uint256" { "uint256".to_string() } else { kt };
            let ty = match inner {
                Some(t) => format!("mapping({} => {})", kt, t),
                None => format!("mapping({} => uint256)", kt),
            };
            (root, Some(ty))
        }
        Node::Keccak(words, 0) if words.len() == 1 => {
            let (root, _) = slot_root(words[0], vyper);
            (root, Some("uint256[]".into()))
        }
        Node::Op(op::ADD, v) => {
            let (root, inner) = slot_root(v[0], vyper);
            match inner {
                Some(t) if t.starts_with("mapping") => (root, Some(t)),
                _ => (root, Some("uint256[]".into())),
            }
        }
        _ => (None, None),
    }
}

fn collect_sloads(e: expr::ExprId, slots: &mut BTreeMap<U256, (usize, usize, BTreeSet<String>)>, vyper: bool) {
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 50_000 {
            continue;
        }
        let n = expr::node(x);
        match &n {
            Node::SLoad(key, false, _) => note_slot(*key, slots, true, None, vyper),
            Node::Op(op::AND, v) => {
                if let (Node::SLoad(key, false, _), Some(m)) = (expr::node(v[0]), expr::as_const(v[1])) {
                    if m.is_low_mask() {
                        let (root, inner) = slot_root(key, vyper);
                        if let Some(root) = root {
                            let bits = m.bits();
                            let t = if bits == 160 { "address".to_string() } else if bits == 1 { "bool".to_string() } else if bits % 8 == 0 { format!("uint{}", bits) } else { "uint256".into() };
                            let full = match inner {
                                Some(i) => i.replace("=> uint256)", &format!("=> {})", t)),
                                None => t,
                            };
                            slots.entry(root).or_insert((0, 0, BTreeSet::new())).2.insert(full);
                        }
                    }
                }
            }
            _ => {}
        }
        stack.extend(expr::children(x));
    }
}

/// Printable ASCII runs in the code's data area (strings longer than 32 bytes are stored as data
/// and loaded with CODECOPY by older compilers).
fn scan_strings(code: &[u8], code_end: usize) -> Vec<String> {
    let mut out = Vec::new();
    let mut i = 0;
    let end = code_end.min(code.len());
    while i < end {
        let start = i;
        while i < end && (0x20..0x7f).contains(&code[i]) {
            i += 1;
        }
        let run = &code[start..i];
        if run.len() >= 12 && run.iter().filter(|b| b.is_ascii_alphabetic() || **b == b' ').count() * 3 >= run.len() * 2 && run.contains(&b' ') {
            out.push(String::from_utf8_lossy(run).trim().to_string());
        }
        i += 1;
    }
    out
}

fn collect_strings(e: expr::ExprId, out: &mut BTreeSet<String>) {
    if let Some(c) = expr::as_const(e) {
        let b = c.to_be_bytes();
        // Left-aligned ASCII (string constants are stored left-aligned).
        let end = b.iter().position(|x| *x == 0).unwrap_or(32);
        if end >= 4 && b[..end].iter().all(|x| (0x20..0x7f).contains(x)) && b[end..].iter().all(|x| *x == 0) {
            out.insert(String::from_utf8_lossy(&b[..end]).into_owned());
        }
    }
}

fn mutability_str(m: Mutability) -> &'static str {
    match m {
        Mutability::Pure => " pure",
        Mutability::View => " view",
        Mutability::NonPayable => "",
        Mutability::Payable => " payable",
    }
}

/// Render the whole contract as pseudo-Solidity.
pub fn render(c: &Contract, name: &str) -> String {
    let mut out = String::new();
    out.push_str(&format!("// Decompiled by evmdec. Compiler: {}.\n", c.language));
    if let Some(m) = &c.info.metadata {
        if let Some(h) = &m.ipfs {
            out.push_str(&format!("// Metadata: ipfs {}\n", h));
        }
        if let Some(h) = &m.bzzr {
            out.push_str(&format!("// Metadata: {}\n", h));
        }
    }
    out.push_str(&format!("// Coverage: {}/{} code blocks, {} unresolved jumps, {} external / {} internal functions.\n", c.stats.covered_blocks, c.stats.code_blocks, c.stats.unresolved_jumps, c.stats.external_functions, c.stats.internal_functions));
    out.push_str(&format!("\ncontract {} {{\n", name));
    if !c.storage.is_empty() {
        out.push_str("    // ---- storage layout ----\n");
        for s in &c.storage {
            out.push_str(&format!("    {} {}; // slot {}, {} reads, {} writes\n", s.ty, s.name, s.slot, s.reads, s.writes));
        }
        out.push('\n');
    }
    if !c.events.is_empty() {
        for e in &c.events {
            out.push_str(&format!("    event {};\n", e));
        }
        out.push('\n');
    }
    if !c.errors.is_empty() {
        for e in &c.errors {
            out.push_str(&format!("    error {};\n", e));
        }
        out.push('\n');
    }
    for f in &c.functions {
        out.push_str(&fmt_function_header(f));
        out.push_str(&f.code);
        out.push_str("    }\n\n");
    }
    out.push_str("}\n");
    for e in &c.embedded {
        out.push_str("\n// ---- embedded contract (deployed by the code above) ----\n");
        out.push_str(&e.source);
    }
    if let Some(ctor) = &c.constructor {
        out.push_str("\n// ---- constructor (creation code) ----\n");
        out.push_str(&ctor.source);
    }
    if let Some(p) = &c.proxy {
        out.push_str(&format!("\n// ---- {}: implementation {} ----\n", p.kind, p.implementation));
        if let Some(ic) = &p.contract {
            out.push_str(&ic.source);
        }
    }
    out
}

pub fn fmt_function_header(f: &Function) -> String {
    let mut s = String::new();
    match f.kind {
        FnKind::External => {
            let params: Vec<String> = f.params.iter().map(|p| format!("{} {}", p.ty, p.name)).collect();
            s.push_str(&format!("    // selector {}{}\n", f.selector.clone().unwrap_or_default(), if f.signature.is_none() { " (unknown signature)" } else { "" }));
            s.push_str(&format!("    function {}({}) external{}", f.name, params.join(", "), mutability_str(f.mutability)));
            if !f.returns.is_empty() {
                s.push_str(&format!(" returns ({})", f.returns.join(", ")));
            }
            s.push_str(" {\n");
        }
        FnKind::Fallback => s.push_str(&format!("    fallback() external{} {{\n", if f.mutability == Mutability::Payable { " payable" } else { "" })),
        FnKind::Receive => s.push_str("    receive() external payable {\n"),
        FnKind::Constructor => s.push_str("    constructor() {\n"),
        FnKind::Internal => {
            let params: Vec<String> = (0..f.n_args).map(|i| format!("uint256 arg{}", i)).collect();
            let m = match f.mutability {
                Mutability::View | Mutability::Pure => mutability_str(f.mutability),
                _ => "",
            };
            s.push_str(&format!("    function {}({}) internal{}", f.name, params.join(", "), m));
            if f.n_rets > 0 {
                s.push_str(&format!(" returns ({})", vec!["uint256"; f.n_rets].join(", ")));
            }
            s.push_str(" {\n");
        }
        FnKind::Orphan => {
            let params: Vec<String> = (0..f.n_args).map(|i| format!("uint256 arg{}", i)).collect();
            s.push_str(&format!("    // unreachable code at {:#x}\n    function {}({}) internal {{\n", f.pc, f.name, params.join(", ")));
        }
    }
    s
}
