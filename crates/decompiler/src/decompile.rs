use crate::cfg::{self, Program, Recovered};
use crate::compiler;
use crate::emit::{self, MappingLayout, Names, SlotSpace};
use crate::expr::{self, ExprId, Node};
use crate::function::{self, FnKind, Mutability, Param};
use crate::lift::{self, Lifted, Lifter, Stmt, Term};
use crate::metadata::{self, BytecodeInfo, CodeKind};
use crate::naming;
use crate::opcode as op;
use crate::sigs;
use crate::ssa::{self, Shape, ShapeStep, Step};
use crate::types::{self, TypeEnv};
use crate::u256::U256;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Write as _;

#[derive(Clone, Debug, Default)]
pub struct Options {
    pub flat: bool,
    pub pcs: bool,
    pub embedded: bool,
    pub no_sigs: bool,
    pub extra_sigs: HashMap<u32, String>,
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
    pub pc: usize,
    pub code: String,
    pub nodes: usize,
    pub effects: function::Effects,
    #[serde(skip)]
    pub lifted: Option<Lifted>,
    pub calls: Vec<usize>,
    pub n_args: usize,
    pub n_rets: usize,
    #[serde(default)]
    pub inlined: bool,
    #[serde(skip)]
    pub bool_vars: Vec<u32>,
    #[serde(skip_serializing_if = "is_zero_usize")]
    pub part: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub origin: Option<String>,
}

fn is_zero_usize(n: &usize) -> bool {
    *n == 0
}

#[derive(Clone, Debug, Serialize)]
pub struct StorageVar {
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub fixed_array: bool,
    pub slot: String,
    pub name: String,
    pub ty: String,
    pub reads: usize,
    pub writes: usize,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub fields: Vec<StorageField>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub members: Vec<StructMember>,
}

#[derive(Clone, Debug, Serialize)]
pub struct StructMember {
    pub offset: u64,
    pub name: String,
    pub ty: String,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub fields: Vec<StorageField>,
}

impl StorageVar {
    #[must_use]
    pub fn struct_name(&self) -> String {
        match self.name.strip_prefix("stor_") {
            Some(suffix) => format!("Struct_{suffix}"),
            None => {
                let mut cs = self.name.chars();
                let first = cs.next().map(|c| c.to_ascii_uppercase()).unwrap_or('S');
                format!("{first}{}Entry", cs.as_str())
            }
        }
    }

    #[must_use]
    pub fn declared_type(&self) -> String {
        if self.members.is_empty() {
            return self.ty.clone();
        }
        let name = self.struct_name();
        match self.ty.rfind(" => ") {
            Some(i) => {
                let rest = &self.ty[i + 4..];
                let end = rest.find([')', '[']).unwrap_or(rest.len());
                format!("{}{}{}", &self.ty[..i + 4], name, &rest[end..])
            }
            None => {
                let end = self.ty.find('[').unwrap_or(self.ty.len());
                format!("{}{}", name, &self.ty[end..])
            }
        }
    }
}

impl StructMember {
    #[must_use]
    pub fn holds_many(&self) -> bool {
        self.ty.starts_with("mapping(") || self.ty.ends_with("[]") || self.ty == "bytes"
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct StorageField {
    pub offset: u32,
    pub bits: u32,
    pub name: String,
    pub ty: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct Stats {
    pub code_bytes: usize,
    pub instructions: usize,
    pub blocks: usize,
    pub code_blocks: usize,
    pub covered_blocks: usize,
    pub unresolved_jumps: usize,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub unresolved_jump_pcs: Vec<String>,
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
    pub compiler: compiler::Profile,
    #[serde(skip)]
    pub types: TypeEnv,
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
    pub region: Option<(usize, usize)>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub constructor: Option<Box<Contract>>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub delegatecall_slots: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub delegatecall_targets: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub library_targets: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub call_targets: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub call_target_slots: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub clone_targets: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub written_targets: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub stored_targets: Vec<(String, String)>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub linked: Vec<Contract>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub link: Option<Link>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub unfollowed: Vec<Unfollowed>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub admits: Vec<String>,
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub gates_read: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub address: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub chain: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proxy: Option<ProxyRef>,
    #[serde(skip)]
    pub string_loaders: HashMap<usize, U256>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub parts: Vec<Part>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub composite: Option<Composite>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub diamond_lookup: Option<DiamondLookup>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize)]
pub struct DiamondLookup {
    pub slot: String,
    pub offset: u64,
}

fn selector_lookup(key: ExprId, layout: MappingLayout) -> Option<DiamondLookup> {
    let path = ssa::slot_path(key, layout)?;
    let (k, offset) = match &path.steps[..] {
        [Step::Key(k)] => (*k, 0),
        [Step::Key(k), Step::Offset(n)] => (*k, *n),
        _ => return None,
    };
    reads_selector(k).then(|| DiamondLookup {
        slot: path.root.to_hex_padded(32),
        offset,
    })
}

// A key is a small expression. A larger one is not a selector lookup.
const SELECTOR_SEARCH_LIMIT: usize = 2_000;

fn reads_selector(e: ExprId) -> bool {
    let mut stack = vec![e];
    let mut seen = HashSet::new();
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > SELECTOR_SEARCH_LIMIT {
            continue;
        }
        if let Node::CallDataLoad(off) = expr::node(x) {
            if expr::as_const(off).is_some_and(|c| c.is_zero()) {
                return true;
            }
        }
        stack.extend(expr::children(x));
    }
    false
}

#[derive(Clone, Debug, Serialize)]
pub struct Part {
    pub role: PartRole,
    pub address: String,
    pub selectors: Vec<String>,
    #[serde(skip)]
    pub base: usize,
    #[serde(skip)]
    pub runtime: Vec<u8>,
    pub compiler: String,
    pub storage: Vec<StorageVar>,
    pub source: String,
    pub stats: Stats,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum PartRole {
    Shell,
    Implementation,
    Facet,
}

#[derive(Clone, Debug, Serialize)]
pub struct Composite {
    pub kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub admin: Option<String>,
    pub collisions: Vec<StorageCollision>,
    pub shadowed: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct StorageCollision {
    pub slot: String,
    pub first: (usize, String),
    pub second: (usize, String),
}

impl Contract {
    #[must_use]
    pub fn code_of(&self, f: &Function) -> &[u8] {
        match self.parts.get(f.part) {
            Some(p) => &p.runtime,
            None => &self.info.runtime,
        }
    }

    #[must_use]
    pub fn base_of(&self, f: &Function) -> usize {
        self.parts.get(f.part).map_or(0, |p| p.base)
    }

    #[must_use]
    pub fn local_pc(&self, f: &Function, pc: usize) -> usize {
        pc.saturating_sub(self.base_of(f))
    }
}

// EVM code is under 2^15 bytes, so the pc ranges of parts never overlap.
pub const PART_STRIDE: usize = 1 << 24;

impl Contract {
    pub fn rebase(&mut self, base: usize) {
        if base == 0 {
            return;
        }
        for f in &mut self.functions {
            f.pc += base;
            for pc in &mut f.calls {
                *pc += base;
            }
            for pc in &mut f.effects.internal_callees {
                *pc += base;
            }
            if let Some(l) = &mut f.lifted {
                for nd in &mut l.nodes {
                    nd.pc += base;
                    for st in &mut nd.stmts {
                        if let Stmt::Internal { callee, .. } = st {
                            *callee += base;
                        }
                    }
                }
            }
        }
        self.string_loaders = self
            .string_loaders
            .drain()
            .map(|(pc, slot)| (pc + base, slot))
            .collect();
        self.types.rebase(base);
    }
}

#[derive(Debug)]
pub struct PartInput {
    pub role: PartRole,
    pub address: String,
    pub selectors: Vec<String>,
    pub contract: Contract,
}

pub fn compose(
    mut shell: Contract,
    kind: &str,
    admin: Option<String>,
    parts: Vec<PartInput>,
) -> Contract {
    let mut all_parts = vec![Part {
        role: PartRole::Shell,
        address: shell.address.clone().unwrap_or_default(),
        selectors: Vec::new(),
        base: 0,
        runtime: shell.info.runtime.clone(),
        compiler: shell.language.clone(),
        storage: shell.storage.clone(),
        source: shell.source.clone(),
        stats: shell.stats.clone(),
    }];
    let shell_selectors: Vec<String> = shell
        .functions
        .iter()
        .filter_map(|f| f.selector.clone())
        .collect();
    let mut declared: HashMap<String, usize> =
        shell.storage.iter().map(|v| (v.slot.clone(), 0)).collect();
    let mut shadowed = Vec::new();
    let mut collisions = Vec::new();
    for PartInput {
        role,
        address,
        selectors,
        contract: mut part,
    } in parts
    {
        let index = all_parts.len();
        let base = index * PART_STRIDE;
        part.rebase(base);
        all_parts.push(Part {
            role,
            address: address.clone(),
            selectors: selectors.clone(),
            base,
            runtime: std::mem::take(&mut part.info.runtime),
            compiler: part.language.clone(),
            storage: part.storage.clone(),
            source: std::mem::take(&mut part.source),
            stats: part.stats.clone(),
        });
        for mut f in part.functions {
            let routed = match (&f.selector, selectors.is_empty()) {
                (Some(sel), false) => selectors.iter().any(|s| s.eq_ignore_ascii_case(sel)),
                _ => true,
            };
            if f.kind == FnKind::External && !routed {
                continue;
            }
            if let Some(sel) = &f.selector {
                if shell_selectors.iter().any(|s| s.eq_ignore_ascii_case(sel)) {
                    shadowed.push(sel.clone());
                    continue;
                }
            }
            f.part = index;
            f.origin = Some(address.clone());
            shell.functions.push(f);
        }
        for var in part.storage {
            match shell.storage.iter().position(|v| v.slot == var.slot) {
                None => {
                    declared.insert(var.slot.clone(), index);
                    shell.storage.push(var);
                }
                Some(i) => {
                    let mine = &mut shell.storage[i];
                    if !compatible(&type_family(&mine.ty), &type_family(&var.ty)) {
                        let first = declared.get(&var.slot).copied().unwrap_or(0);
                        collisions.push(StorageCollision {
                            slot: var.slot.clone(),
                            first: (first, mine.ty.clone()),
                            second: (index, var.ty.clone()),
                        });
                    }
                    mine.reads += var.reads;
                    mine.writes += var.writes;
                }
            }
        }
        for v in part.events {
            if !shell.events.contains(&v) {
                shell.events.push(v);
            }
        }
        for v in part.errors {
            if !shell.errors.contains(&v) {
                shell.errors.push(v);
            }
        }
        for v in part.strings {
            if !shell.strings.contains(&v) {
                shell.strings.push(v);
            }
        }
        for v in part.selectors_called {
            if !shell.selectors_called.contains(&v) {
                shell.selectors_called.push(v);
            }
        }
        shell.embedded.extend(part.embedded);
        for v in part.call_targets {
            if !shell.call_targets.contains(&v) && !v.eq_ignore_ascii_case(&address) {
                shell.call_targets.push(v);
            }
        }
        for v in part.library_targets {
            if !shell.library_targets.contains(&v) && !v.eq_ignore_ascii_case(&address) {
                shell.library_targets.push(v);
            }
        }
        for v in part.clone_targets {
            if !shell.clone_targets.contains(&v) {
                shell.clone_targets.push(v);
            }
        }
        for v in part.written_targets {
            if !shell.written_targets.contains(&v) {
                shell.written_targets.push(v);
            }
        }
        for v in part.call_target_slots {
            if !shell.call_target_slots.contains(&v) {
                shell.call_target_slots.push(v);
            }
        }
        shell.string_loaders.extend(part.string_loaders);
        shell.types.absorb(part.types);
        let s = &mut shell.stats;
        s.code_bytes += part.stats.code_bytes;
        s.instructions += part.stats.instructions;
        s.blocks += part.stats.blocks;
        s.code_blocks += part.stats.code_blocks;
        s.covered_blocks += part.stats.covered_blocks;
        s.unresolved_jumps += part.stats.unresolved_jumps;
        s.unresolved_jump_pcs.extend(part.stats.unresolved_jump_pcs);
        s.budget_exhausted |= part.stats.budget_exhausted;
        s.external_functions += part.stats.external_functions;
        s.internal_functions += part.stats.internal_functions;
        s.orphans += part.stats.orphans;
    }
    shadowed.sort();
    shadowed.dedup();
    shell.parts = all_parts;
    shell.composite = Some(Composite {
        kind: kind.to_string(),
        admin,
        collisions,
        shadowed,
    });
    shell.source = render(&shell, "Contract");
    shell
}

fn compatible(a: &str, b: &str) -> bool {
    if a == "*" || b == "*" || a == b {
        return true;
    }
    let inner = |t: &str| {
        t.strip_prefix("mapping(")
            .and_then(|r| r.strip_suffix(')'))
            .and_then(|r| r.split_once(" => "))
            .map(|(k, v)| (k.to_string(), v.to_string()))
    };
    match (inner(a), inner(b)) {
        (Some((ka, va)), Some((kb, vb))) => compatible(&ka, &kb) && compatible(&va, &vb),
        (None, None) => match (a.strip_suffix("[]"), b.strip_suffix("[]")) {
            (Some(ea), Some(eb)) => compatible(ea, eb),
            _ => false,
        },
        _ => false,
    }
}

fn type_family(ty: &str) -> String {
    let ty = ty.trim();
    if let Some(inner) = ty
        .strip_prefix("mapping(")
        .and_then(|r| r.strip_suffix(')'))
    {
        if let Some((k, v)) = inner.split_once(" => ") {
            return format!("mapping({} => {})", type_family(k), type_family(v));
        }
    }
    if let Some(base) = ty.strip_suffix("[]") {
        return format!("{}[]", type_family(base));
    }
    match ty {
        "" | "unknown" | "uint256" | "int256" | "bytes32" => "*".into(),
        "address" | "bool" | "string" | "bytes" => ty.into(),
        t if t.starts_with("uint") || t.starts_with("int") => "uint".into(),
        t if t.starts_with("bytes") => "bytes".into(),
        t => t.into(),
    }
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

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct Link {
    pub from: String,
    pub how: String,
    pub depth: usize,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct Unfollowed {
    pub target: String,
    pub from: String,
    pub reason: String,
}

pub fn decompile(code: &[u8], opts: &Options) -> Contract {
    let t0 = std::time::Instant::now();
    let code: &[u8] = if code.is_empty() { &[op::STOP] } else { code };
    let info = metadata::analyze(code);
    let mut c = decompile_runtime(&info.runtime, &info, opts);
    if info.kind == CodeKind::Creation && !info.constructor.is_empty() {
        let cinfo = BytecodeInfo {
            kind: CodeKind::Runtime,
            runtime: info.constructor.clone(),
            constructor: vec![],
            constructor_args: vec![],
            runtime_offset: 0,
            runtime_len: info.constructor.len(),
            constructor_args_len: 0,
            metadata: None,
            constructor_metadata: None,
        };
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

pub fn decompile_runtime(code: &[u8], info: &BytecodeInfo, opts: &Options) -> Contract {
    let t0 = std::time::Instant::now();
    let timing = std::env::var("EVMDEC_TIMING").is_ok();
    if timing {
        eprintln!("[timing] start runtime of {} bytes", code.len());
    }
    let mut prog = Program::new(code.to_vec());
    let mut code_end = info
        .metadata
        .as_ref()
        .map(|m| m.offset)
        .unwrap_or(code.len());
    let mut rec = cfg::recover(&prog, code_end);
    let embedded_ranges = embedded_regions(&prog, &rec);
    let in_embedded = |pc: usize| {
        embedded_ranges
            .iter()
            .any(|(o, l)| pc >= *o && pc < *o + *l)
    };
    let prune_embedded = |rec: &mut Recovered| {
        if !embedded_ranges.is_empty() {
            let keep: HashSet<usize> = prog
                .blocks
                .iter()
                .filter(|b| !in_embedded(b.start))
                .map(|b| b.id)
                .collect();
            rec.orphans.retain(|b, _| keep.contains(b));
            let mut un: Vec<usize> = std::iter::once(&rec.main)
                .chain(rec.functions.values())
                .chain(rec.orphans.values())
                .flat_map(|u| {
                    u.nodes
                        .iter()
                        .filter(|n| n.unresolved)
                        .map(|n| prog.blocks[n.block].end)
                })
                .filter(|pc| !in_embedded(*pc))
                .collect();
            un.sort_unstable();
            un.dedup();
            rec.unresolved_jumps = un;
        }
    };
    prune_embedded(&mut rec);
    if !rec.unresolved_jumps.is_empty() {
        let oracle = Lifter {
            prog: &prog,
            root: false,
            summaries: HashMap::new(),
            footprints: HashMap::new(),
            oracle: true,
            copy_loops: Default::default(),
        };
        let mut computed: HashMap<usize, Vec<usize>> = HashMap::new();
        for b in &prog.blocks {
            if !matches!(b.terminator, op::JUMP | op::JUMPI)
                || !rec.unresolved_jumps.contains(&b.end)
                || in_embedded(b.start)
                || b.end > code_end
            {
                continue;
            }
            let unit = cfg::Unit {
                entry_block: b.id,
                nodes: vec![cfg::UNode {
                    id: 0,
                    block: b.id,
                    entry: cfg::AState::new(),
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
            let l = oracle.lift(&unit, None);
            let target = match &l.nodes[0].term {
                Term::Unresolved(t) => *t,
                Term::CondJump { target, .. } => *target,
                _ => continue,
            };
            let pcs = lift::jump_candidates(target, &prog.jumpdests, code_end);
            let cands: Vec<usize> = pcs
                .iter()
                .filter_map(|pc| prog.block_at_pc.get(pc).copied())
                .collect();
            if !cands.is_empty() && cands.len() <= 512 {
                computed.insert(b.id, cands);
            }
        }
        if !computed.is_empty() {
            prog.computed_jumps = computed;
            rec = cfg::recover(&prog, code_end);
            prune_embedded(&mut rec);
        }
    }
    if info.metadata.is_none() {
        let reached: BTreeSet<usize> = std::iter::once(&rec.main)
            .chain(rec.functions.values())
            .flat_map(|u| u.nodes.iter().map(|n| n.block))
            .collect();
        if let Some(last) = reached.iter().max() {
            let last_end = prog.blocks[*last].end;
            let referenced: HashSet<usize> = std::iter::once(&rec.main)
                .chain(rec.functions.values())
                .flat_map(|u| u.nodes.iter())
                .flat_map(|n| {
                    prog.block_insns(&prog.blocks[n.block])
                        .iter()
                        .filter_map(|i| i.imm.and_then(|v| v.as_usize()))
                })
                .filter(|pc| *pc >= last_end && prog.jumpdests.contains(pc))
                .collect();
            if referenced.is_empty() && last_end < code.len() {
                code_end = last_end;
                rec = cfg::recover(&prog, code_end);
            }
        }
    }
    let profile = compiler::profile(code, info.metadata.as_ref());
    let language = profile.to_string();
    let layout = profile.layout;

    let tick = |label: &str, t: &mut std::time::Instant| {
        if timing {
            eprintln!("[timing] {}: {:?}", label, t.elapsed());
            *t = std::time::Instant::now();
        }
    };
    let mut tt = std::time::Instant::now();
    tick("recover", &mut tt);
    let mut int_lifter = Lifter {
        prog: &prog,
        root: false,
        summaries: HashMap::new(),
        footprints: HashMap::new(),
        oracle: false,
        copy_loops: Default::default(),
    };
    let mut internals: BTreeMap<usize, Lifted> = BTreeMap::new();
    let mut by_block: Vec<(usize, Lifted)> = Vec::new();
    for _round in 0..8 {
        by_block.clear();
        for (b, unit) in &rec.functions {
            let l = int_lifter.lift_summarizing(unit, None);
            by_block.push((*b, l));
        }
        let mut sums = HashMap::new();
        let debug_sum = std::env::var("EVMDEC_DEBUG_SUMMARY").is_ok();
        for (b, l) in &by_block {
            if debug_sum {
                eprintln!(
                    "[summary] round {} function {:#x}:",
                    _round, prog.blocks[*b].start
                );
            }
            if let Some(sm) = lift::summarize(l) {
                if debug_sum {
                    eprintln!(
                        "[summary]   ok: returns {} mstores {} copies {} maybe {} guards {}",
                        sm.returns.len(),
                        sm.mstores.len(),
                        sm.copies.len(),
                        sm.maybe_mstores.len(),
                        sm.guards.len()
                    );
                }
                sums.insert(*b, sm);
            }
        }
        let footprints: HashMap<usize, lift::MemoryWrites> = by_block
            .iter()
            .filter(|_| profile.kind != compiler::Kind::Solc)
            .map(|(b, l)| (*b, l.mem_writes.clone()))
            .collect();
        let same = sums.len() == int_lifter.summaries.len()
            && sums.keys().all(|k| int_lifter.summaries.contains_key(k))
            && footprints == int_lifter.footprints;
        int_lifter.summaries = sums;
        int_lifter.footprints = footprints;
        if same {
            break;
        }
    }
    for (b, l) in by_block {
        internals.insert(prog.blocks[b].start, l);
    }
    tick("lift internals", &mut tt);
    let loaders: HashMap<usize, U256> = internals
        .iter()
        .filter_map(|(pc, l)| crate::idiom::storage_string_loader(l).map(|k| (*pc, k)))
        .collect();
    let lifter = Lifter {
        prog: &prog,
        root: true,
        summaries: int_lifter.summaries.clone(),
        footprints: int_lifter.footprints.clone(),
        oracle: false,
        copy_loops: Default::default(),
    };
    let main = lifter.lift_summarizing(&rec.main, None);
    let dispatch = function::discover(&main);
    let contract_nonpayable = function::dispatcher_nonpayable(&main, &dispatch.dispatcher);
    tick("lift main", &mut tt);
    let mut orphans: BTreeMap<usize, Lifted> = BTreeMap::new();
    for (b, unit) in &rec.orphans {
        crate::clock::check();
        let t1 = std::time::Instant::now();
        orphans.insert(prog.blocks[*b].start, int_lifter.lift(unit, None));
        if timing && t1.elapsed().as_millis() > 200 {
            eprintln!(
                "[timing] slow orphan {:#x}: nodes={} {:?}",
                prog.blocks[*b].start,
                unit.nodes.len(),
                t1.elapsed()
            );
        }
    }
    tick("lift orphans", &mut tt);
    let mut functions: Vec<Function> = Vec::new();
    let reprocess =
        main.reprocess_count + internals.values().map(|l| l.reprocess_count).sum::<usize>();

    let mut int_effects: HashMap<usize, function::Effects> = HashMap::new();
    for (pc, l) in &internals {
        int_effects.insert(*pc, function::effects(l));
    }
    let transitive = |e: &function::Effects,
                      int_effects: &HashMap<usize, function::Effects>|
     -> function::Effects {
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

    let internals_static: &'static HashMap<usize, Lifted> = Box::leak(Box::new(
        internals
            .iter()
            .map(|(pc, l)| (*pc, l.clone()))
            .collect::<HashMap<usize, Lifted>>(),
    ));
    let resolve = move |pc: usize| -> Option<&'static Lifted> { internals_static.get(&pc) };
    let make = |kind: FnKind,
                selector: Option<u32>,
                l: Lifted,
                pc: usize,
                name_hint: Option<String>,
                n_args: usize,
                n_rets: usize|
     -> Function {
        let eff = function::effects(&l);
        let calls = eff.internal_callees.clone();
        let eff = transitive(&eff, &int_effects);
        let mut params = if matches!(kind, FnKind::External) {
            let exprs = function::exprs_with_callees_tagged(&l, &resolve, 2);
            function::infer_params_from(&exprs)
        } else {
            vec![]
        };
        let mut returns = if matches!(kind, FnKind::External) {
            function::infer_returns(&l)
        } else {
            function::infer_internal_returns(&l, n_rets)
        };
        let signature = if opts.no_sigs {
            None
        } else {
            selector.and_then(|sel| {
                opts.extra_sigs
                    .get(&sel)
                    .cloned()
                    .or_else(|| sigs::function(sel).map(|s| s.into_owned()))
            })
        };
        let name = match (&signature, name_hint, selector) {
            (Some(s), _, _) => sigs::name_of(s).to_string(),
            (None, Some(h), _) => h,
            (None, None, Some(sel)) => format!("func_{:08x}", sel),
            (None, None, None) => format!("func_{:#x}", pc),
        };
        if let Some(sig) = &signature {
            let tys = sigs::params_of(sig);
            if tys.len() >= params.len() {
                params = tys
                    .iter()
                    .enumerate()
                    .map(|(i, t)| Param {
                        index: i as u32,
                        ty: t.clone(),
                        name: format!("arg{}", i),
                    })
                    .collect();
            }
        }
        let nonpayable = contract_nonpayable || function::is_nonpayable(&l);
        let state_changing =
            eff.writes_storage || eff.logs || eff.calls || eff.creates || eff.selfdestruct;
        let mutability = if state_changing || kind == FnKind::Fallback || kind == FnKind::Receive {
            if nonpayable {
                Mutability::NonPayable
            } else {
                Mutability::Payable
            }
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
        if l.nodes.iter().any(|nd| matches!(&nd.term, Term::ReturnDyn { ptr } if crate::idiom::is_string_pointer(&l, *ptr, &loaders).is_some())) {
            returns = vec!["string".into()];
        }
        Function {
            kind,
            selector: selector.map(|s| format!("{:#010x}", s)),
            name,
            signature,
            mutability,
            params,
            returns,
            pc,
            code: String::new(),
            nodes: l.nodes.len(),
            effects: eff,
            lifted: Some(l),
            calls,
            n_args,
            n_rets,
            inlined: false,
            bool_vars: Vec::new(),
            part: 0,
            origin: None,
        }
    };

    let unit_node_of = |lifted_node: usize| -> Option<usize> {
        main.node_map
            .iter()
            .find(|(_, v)| **v == lifted_node)
            .map(|(k, _)| *k)
    };
    let relift = |entry: usize| -> Lifted {
        if let Some(un) = unit_node_of(entry) {
            if let Some(state) = Lifter::entry_state_of(&main, un) {
                let (sub, _) = rec.main.slice(un);
                return lifter.lift_from_summarizing(&sub, state);
            }
        }
        function::slice(&main, entry)
    };
    for d in &dispatch.functions {
        let mut sl = relift(d.entry);
        crate::idiom::fold(&mut sl);
        let pc = main.nodes[d.entry].pc;
        functions.push(make(FnKind::External, Some(d.selector), sl, pc, None, 0, 0));
    }
    if let Some(r) = dispatch.receive {
        let mut sl = relift(r);
        crate::idiom::fold(&mut sl);
        functions.push(make(
            FnKind::Receive,
            None,
            sl,
            main.nodes[r].pc,
            Some("receive".into()),
            0,
            0,
        ));
    }
    if let Some(f) = dispatch.fallback {
        let mut sl = relift(f);
        crate::idiom::fold(&mut sl);
        functions.push(make(
            FnKind::Fallback,
            None,
            sl,
            main.nodes[f].pc,
            Some("fallback".into()),
            0,
            0,
        ));
    }
    if dispatch.functions.is_empty() && dispatch.fallback.is_none() && dispatch.receive.is_none() {
        functions.push(make(
            FnKind::Fallback,
            None,
            main.clone(),
            0,
            Some("fallback".into()),
            0,
            0,
        ));
    }
    for (pc, mut l) in internals {
        crate::idiom::fold(&mut l);
        let n_rets = l
            .nodes
            .iter()
            .filter_map(|n| {
                if let Term::InternalReturn(v) = &n.term {
                    Some(v.len())
                } else {
                    None
                }
            })
            .max()
            .unwrap_or(0);
        let n_args = match l.ret_slot {
            Some(k) => (k as usize).min(l.n_args),
            None => l.n_args,
        };
        functions.push(make(
            FnKind::Internal,
            None,
            l,
            pc,
            Some(format!("func_{:#x}", pc)),
            n_args,
            n_rets,
        ));
    }
    for (pc, l) in orphans {
        let n_args = l.n_args;
        functions.push(make(
            FnKind::Orphan,
            None,
            l,
            pc,
            Some(format!("orphan_{:#x}", pc)),
            n_args,
            0,
        ));
    }

    {
        let mut referenced: HashSet<usize> = HashSet::new();
        for f in &functions {
            if let Some(l) = &f.lifted {
                for nd in &l.nodes {
                    for st in &nd.stmts {
                        if let Stmt::Internal {
                            callee, results, ..
                        } = st
                        {
                            if !(loaders.contains_key(callee) && !results.is_empty()) {
                                referenced.insert(*callee);
                            }
                        }
                    }
                }
            }
        }
        let mut continuation: HashSet<usize> = HashSet::new();
        for f in &functions {
            if f.kind != FnKind::Internal || !referenced.contains(&f.pc) {
                continue;
            }
            let callers: Vec<&Function> = functions
                .iter()
                .filter(|g| g.pc != f.pc && g.calls.contains(&f.pc))
                .collect();
            if !callers.is_empty()
                && callers.iter().all(|g| {
                    g.lifted
                        .as_ref()
                        .is_some_and(|l| l.nodes.iter().any(|nd| nd.pc == f.pc))
                })
            {
                continuation.insert(f.pc);
            }
        }
        for f in functions.iter_mut() {
            if f.kind == FnKind::Internal
                && (!referenced.contains(&f.pc) || continuation.contains(&f.pc))
            {
                f.inlined = true;
            }
        }
    }

    let env = {
        let units: Vec<(usize, &Lifted)> = functions
            .iter()
            .filter_map(|f| f.lifted.as_ref().map(|l| (f.pc, l)))
            .collect();
        let declared: Vec<types::Declared> = functions
            .iter()
            .filter(|f| f.kind == FnKind::External)
            .filter_map(|f| f.signature.as_ref().map(|sig| (f.pc, sig)))
            .flat_map(|(pc, sig)| {
                types::declared_words(&sigs::params_of(sig))
                    .into_iter()
                    .map(move |(word, ty)| (pc, word, ty))
            })
            .collect();
        types::solve(&units, layout, &declared)
    };
    refine_types(&mut functions, &env);
    tick("types", &mut tt);

    let string_slots: HashSet<U256> = loaders.values().copied().collect();
    let solc08 = profile.kind == compiler::Kind::Solc && profile.checked_arithmetic;
    let Inventories {
        mut storage,
        events,
        errors,
        mut strings,
        selectors: selectors_called,
    } = inventories(&functions, layout, &string_slots);
    refine_storage_types(&mut storage, &env);
    struct_members(&mut storage, &env, &hashed_slots(&functions, layout));
    name_storage_from_getters(&functions, &mut storage, layout);
    naming::name_storage(&functions, &mut storage, layout, !opts.no_sigs);
    naming::name_helpers(&mut functions, &storage, layout, !opts.no_sigs);
    naming::name_params(&mut functions, &storage, layout);
    for var in storage.iter_mut().filter(|v| !v.members.is_empty()) {
        var.ty = var.declared_type();
    }
    for st in scan_strings(code, code_end, &embedded_ranges) {
        if !strings.iter().any(|x| x.contains(&st)) {
            strings.push(st);
        }
    }
    strings.sort();
    strings.dedup();
    strings.retain(|s| {
        s.len() >= 5 && s.chars().filter(|c| c.is_ascii_alphabetic()).count() * 2 >= s.len()
    });
    let snap = strings.clone();
    strings.retain(|s| {
        !snap
            .iter()
            .any(|o| o.len() > s.len() && o.contains(s.as_str()))
    });

    tick("discover+inventories", &mut tt);
    let pure_callees: HashSet<usize> = functions
        .iter()
        .filter(|f| {
            f.kind == FnKind::Internal
                && matches!(f.mutability, Mutability::View | Mutability::Pure)
        })
        .map(|f| f.pc)
        .collect();
    let callees = Callees::of(&functions, profile.kind);
    let array_resizers: HashSet<usize> = functions
        .iter()
        .filter(|f| f.kind == FnKind::Internal && f.lifted.as_ref().is_some_and(is_array_resizer))
        .map(|f| f.pc)
        .collect();
    for f in functions.iter_mut() {
        let mut names = make_names(f, &storage, layout, &loaders, &callees);
        names.hide_checked = solc08;
        names.pure_callees = pure_callees.clone();
        names.array_resizers = array_resizers.clone();
        let l = f
            .lifted
            .as_ref()
            .expect("functions are lifted before they are printed");
        crate::clock::check();
        let t1 = std::time::Instant::now();
        let body = if opts.flat {
            emit::fmt_flat(l, &names, "        ")
        } else {
            crate::structure::fmt_structured(l, &names, "        ")
        };
        if timing && t1.elapsed().as_millis() > 200 {
            eprintln!(
                "[timing] slow render {} nodes={} {:?}",
                f.name,
                l.nodes.len(),
                t1.elapsed()
            );
        }
        f.code = body;
    }
    tick("render", &mut tt);

    let covered: BTreeSet<usize> = std::iter::once(&rec.main)
        .chain(rec.functions.values())
        .chain(rec.orphans.values())
        .flat_map(|u| u.nodes.iter().map(|n| n.block))
        .collect();
    let code_blocks = prog
        .blocks
        .iter()
        .filter(|b| b.start < code_end && !in_embedded(b.start) && prog.is_potential_code(b.id))
        .count();
    let stats = Stats {
        code_bytes: code.len(),
        instructions: prog.insns.len(),
        blocks: prog.blocks.len(),
        code_blocks,
        covered_blocks: covered
            .iter()
            .filter(|b| {
                prog.blocks[**b].start < code_end
                    && !in_embedded(prog.blocks[**b].start)
                    && prog.is_potential_code(**b)
            })
            .count(),
        unresolved_jumps: rec.unresolved_jumps.len(),
        unresolved_jump_pcs: rec
            .unresolved_jumps
            .iter()
            .map(|pc| format!("{:#x}", pc))
            .collect(),
        budget_exhausted: rec.budget_exhausted,
        external_functions: functions
            .iter()
            .filter(|f| f.kind == FnKind::External)
            .count(),
        internal_functions: functions
            .iter()
            .filter(|f| f.kind == FnKind::Internal)
            .count(),
        orphans: functions
            .iter()
            .filter(|f| f.kind == FnKind::Orphan)
            .count(),
        lift_reprocess: reprocess,
        time_ms: t0.elapsed().as_millis(),
    };

    let mut embedded = Vec::new();
    if opts.embedded {
        for region in embedded_ranges.iter().copied() {
            let sub = &code[region.0..region.0 + region.1];
            let sub_info = metadata::analyze(sub);
            if sub_info.kind == CodeKind::Creation || sub_info.metadata.is_some() {
                let mut sc = decompile(
                    sub,
                    &Options {
                        embedded: false,
                        ..opts.clone()
                    },
                );
                sc.source = render(&sc, &format!("Embedded_{:#x}", region.0));
                sc.region = Some(region);
                embedded.push(sc);
            }
        }
    }

    let mut dc_slots: Vec<String> = Vec::new();
    let mut dc_targets: Vec<String> = Vec::new();
    let mut library_targets: Vec<String> = Vec::new();
    let mut call_targets: Vec<String> = Vec::new();
    let mut call_target_slots: Vec<String> = Vec::new();
    let mut written_targets: Vec<String> = Vec::new();
    let mut clone_targets: Vec<String> = Vec::new();
    let mut diamond_lookup: Option<DiamondLookup> = None;
    for f in &functions {
        let Some(l) = &f.lifted else { continue };
        for nd in &l.nodes {
            for st in &nd.stmts {
                if let Stmt::Create {
                    init: Some(words),
                    len,
                    ..
                } = st
                {
                    if let Some(target) = clone_target(words, *len) {
                        if !clone_targets.contains(&target) {
                            clone_targets.push(target);
                        }
                    }
                }
                if let Stmt::Call {
                    kind, addr, in_len, ..
                } = st
                {
                    let forwards = matches!(expr::node(*in_len), Node::Env(op::CALLDATASIZE, _));
                    let a = match expr::node(*addr) {
                        Node::Op(op::AND, v) => v[0],
                        _ => *addr,
                    };
                    match expr::node(a) {
                        Node::SLoad(k, false, _)
                            if matches!(*kind, op::CALL | op::STATICCALL | op::CALLCODE) =>
                        {
                            if let Some(c) = expr::as_const(k) {
                                let h = c.to_hex_padded(32);
                                if *kind != op::STATICCALL && !written_targets.contains(&h) {
                                    written_targets.push(h.clone());
                                }
                                if !call_target_slots.contains(&h) {
                                    call_target_slots.push(h);
                                }
                            }
                        }
                        Node::SLoad(k, false, _) if *kind == op::DELEGATECALL => {
                            if let Some(c) = expr::as_const(k) {
                                let h = c.to_hex_padded(32);
                                if !dc_slots.contains(&h) {
                                    dc_slots.push(h);
                                }
                            } else if diamond_lookup.is_none() {
                                diamond_lookup = selector_lookup(k, layout);
                            }
                        }
                        Node::Const(c) if *kind == op::DELEGATECALL => {
                            let h = (c & expr::mask_bits(160)).to_hex_padded(20);
                            let list = match forwards {
                                true => &mut dc_targets,
                                false => &mut library_targets,
                            };
                            if !list.contains(&h) {
                                list.push(h);
                            }
                        }
                        Node::Const(c)
                            if matches!(*kind, op::CALL | op::STATICCALL | op::CALLCODE) =>
                        {
                            let low = c & expr::mask_bits(160);
                            let is_precompile =
                                low.fits_u64() && (1..=0x11).contains(&low.low_u64());
                            if !low.is_zero() && !is_precompile {
                                let h = low.to_hex_padded(20);
                                if *kind != op::STATICCALL && !written_targets.contains(&h) {
                                    written_targets.push(h.clone());
                                }
                                if !call_targets.contains(&h) {
                                    call_targets.push(h);
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
    }
    let mut c = Contract {
        info: info.clone(),
        kind: info.kind,
        language,
        compiler: profile,
        types: env,
        functions,
        storage,
        events,
        errors,
        strings,
        selectors_called,
        stats,
        source: String::new(),
        embedded,
        region: None,
        constructor: None,
        delegatecall_slots: dc_slots,
        delegatecall_targets: dc_targets,
        library_targets,
        call_targets,
        call_target_slots,
        clone_targets,
        written_targets,
        stored_targets: Vec::new(),
        linked: Vec::new(),
        link: None,
        unfollowed: Vec::new(),
        admits: Vec::new(),
        gates_read: false,
        address: None,
        chain: None,
        proxy: None,
        string_loaders: loaders,
        parts: Vec::new(),
        composite: None,
        diamond_lookup,
    };
    c.source = render(&c, "Contract");
    c
}

pub(crate) fn clone_target(init: &[ExprId], len: ExprId) -> Option<String> {
    const HEAD: [u8; 20] = [
        0x3d, 0x60, 0x2d, 0x80, 0x60, 0x0a, 0x3d, 0x39, 0x81, 0xf3, 0x36, 0x3d, 0x3d, 0x37, 0x3d,
        0x3d, 0x3d, 0x36, 0x3d, 0x73,
    ];
    let len = expr::as_const(len)?.as_usize()?;
    let mut bytes = Vec::with_capacity(32 * init.len());
    for (i, w) in init.iter().enumerate().take(3) {
        let word = expr::as_const(*w)?;
        let short = i == init.len() - 1 && len % 32 != 0;
        let word = match short {
            true => word << (8 * (32 - len % 32)) as u32,
            false => word,
        };
        bytes.extend_from_slice(&word.to_be_bytes());
    }
    let at = bytes.windows(HEAD.len()).position(|w| w == HEAD)? + HEAD.len();
    let address = bytes.get(at..at + 20)?;
    Some(U256::from_be_bytes(address).to_hex_padded(20))
}

fn embedded_regions(prog: &Program, rec: &Recovered) -> Vec<(usize, usize)> {
    let mut out: Vec<(usize, usize)> = Vec::new();
    for u in std::iter::once(&rec.main).chain(rec.functions.values()) {
        for n in &u.nodes {
            let b = &prog.blocks[n.block];
            let insns = prog.block_insns(b);
            for (i, ins) in insns.iter().enumerate() {
                if ins.opcode == op::CODECOPY && i >= 3 {
                    let st = metadata::constant_stack(&insns[..i]);
                    let l = st.len();
                    if l >= 3 {
                        if let (Some(off), Some(len)) = (
                            st[l - 2].and_then(|v| v.as_usize()),
                            st[l - 3].and_then(|v| v.as_usize()),
                        ) {
                            if len >= 64
                                && off + len <= prog.code.len()
                                && off >= b.end
                                && !out.contains(&(off, len))
                            {
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

fn element_types(functions: &[Function]) -> HashMap<U256, String> {
    // Writes decide when there are any.
    // A read mask may be ABI packing. A write mask never is.
    #[derive(Default)]
    struct Accesses {
        write_widths: BTreeSet<u32>,
        flags: Vec<U256>,
        other_write: bool,
        read_widths: BTreeSet<u32>,
    }
    let mut seen: HashMap<U256, Accesses> = HashMap::new();
    let width_of = |mask: U256| -> Option<u32> {
        let cleared = !mask;
        cleared.is_low_mask().then(|| cleared.bits())
    };
    for f in functions {
        let Some(l) = &f.lifted else { continue };
        for nd in &l.nodes {
            for s in &nd.stmts {
                let Stmt::SStore {
                    key,
                    val,
                    transient: false,
                    ..
                } = s
                else {
                    continue;
                };
                let Some(root) = emit::element_root(*key) else {
                    continue;
                };
                let keeps = |e: ExprId| -> Option<u32> {
                    let Node::Op(op::AND, w) = expr::node(e) else {
                        return None;
                    };
                    for (a, b) in [(w[0], w[1]), (w[1], w[0])] {
                        if let (Node::SLoad(k, false, _), Some(m)) =
                            (expr::node(a), expr::as_const(b))
                        {
                            if k == *key {
                                return width_of(m);
                            }
                        }
                    }
                    None
                };
                let (bits, value) = match expr::node(*val) {
                    Node::Op(op::OR, v) => match (keeps(v[1]), keeps(v[0])) {
                        (Some(b), _) => (b, Some(v[0])),
                        (_, Some(b)) => (b, Some(v[1])),
                        _ => continue,
                    },
                    _ => match keeps(*val) {
                        Some(b) => (b, None),
                        None => continue,
                    },
                };
                let e = seen.entry(root).or_default();
                e.write_widths.insert(bits);
                match value.map(expr::as_const) {
                    None => e.flags.push(U256::ZERO),
                    Some(Some(c)) if c.is_zero() || c == U256::ONE => e.flags.push(c),
                    Some(_) => e.other_write = true,
                }
            }
            for root in lift::roots(nd) {
                let mut stack = vec![root.expr];
                let mut visited = HashSet::new();
                while let Some(x) = stack.pop() {
                    if !visited.insert(x) || visited.len() > 20_000 {
                        continue;
                    }
                    if x == root.expr && root.payload {
                        stack.extend(expr::children(x));
                        continue;
                    }
                    if let Node::Op(op::AND, v) = expr::node(x) {
                        for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
                            if let (Node::SLoad(k, false, _), Some(m)) =
                                (expr::node(a), expr::as_const(b))
                            {
                                if m.is_low_mask() {
                                    if let Some(root) = emit::element_root(k) {
                                        seen.entry(root).or_default().read_widths.insert(m.bits());
                                    }
                                }
                            }
                        }
                    }
                    stack.extend(expr::children(x));
                }
            }
        }
    }
    seen.into_iter()
        .filter_map(|(root, a)| {
            let widths = if a.write_widths.is_empty() {
                a.read_widths
            } else {
                a.write_widths
            };
            let w = *widths.iter().next()?;
            if widths.len() != 1 {
                return None;
            }
            let ty = if w == 8 && !a.other_write && a.flags.contains(&U256::ONE) {
                "bool".to_string()
            } else if w == 160 {
                "address".to_string()
            } else if w < 256 && w % 8 == 0 {
                format!("uint{}", w)
            } else {
                return None;
            };
            Some((root, ty))
        })
        .collect()
}

fn element_type(ty: &str) -> Option<String> {
    let t = if let Some(elem) = ty.strip_suffix("[]") {
        elem
    } else if ty.starts_with("mapping(") {
        ty.rsplit("=> ").next()?.trim_end_matches(')')
    } else {
        return None;
    };
    (t == "bool" || t == "address" || (t.starts_with("uint") && t != "uint256"))
        .then(|| t.to_string())
}

fn is_array_resizer(l: &Lifted) -> bool {
    let k = l.ret_slot.map(|k| k as usize).unwrap_or(l.n_args);
    let is_arg = |e: ExprId| matches!(expr::node(e), Node::Arg(i) if (i as usize) < k);
    let mut stores_arg_to_arg = false;
    let mut clears = false;
    for nd in &l.nodes {
        for s in &nd.stmts {
            match s {
                Stmt::SStore { key, val, .. } if is_arg(*key) && is_arg(*val) => {
                    stores_arg_to_arg = true;
                }
                Stmt::SStore { key, val, .. }
                    if expr::as_const(*val) == Some(U256::ZERO) && !expr::is_const(*key) =>
                {
                    clears = true;
                }
                Stmt::Internal { .. } => clears = true,
                Stmt::Call { .. } | Stmt::Log { .. } | Stmt::Create { .. } => return false,
                _ => {}
            }
        }
    }
    k == 2 && stores_arg_to_arg && clears
}

fn name_storage_from_getters(
    functions: &[Function],
    storage: &mut [StorageVar],
    layout: MappingLayout,
) {
    let mut taken: HashSet<String> = storage.iter().map(|s| s.name.clone()).collect();
    for f in functions {
        let (FnKind::External, Some(sig), Some(l)) = (f.kind, &f.signature, &f.lifted) else {
            continue;
        };
        let raw = sigs::name_of(sig);
        let name = match raw.strip_prefix("get") {
            Some(rest) if rest.chars().next().is_some_and(|c| c.is_ascii_uppercase()) => {
                let mut cs = rest.chars();
                let first = cs
                    .next()
                    .map(|c| c.to_ascii_lowercase())
                    .unwrap_or_default();
                format!("{first}{}", cs.as_str())
            }
            _ => raw.to_string(),
        };
        if name.is_empty()
            || !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
            || taken.contains(&name)
        {
            continue;
        }
        let effectful = l.nodes.iter().any(|nd| {
            nd.stmts.iter().any(|s| {
                matches!(
                    s,
                    Stmt::SStore { .. }
                        | Stmt::Log { .. }
                        | Stmt::Create { .. }
                        | Stmt::Internal { .. }
                ) || matches!(s, Stmt::Call { kind, .. } if *kind != op::STATICCALL)
            }) || matches!(nd.term, Term::SelfDestruct(_))
        });
        if effectful {
            continue;
        }
        let mut returned: Vec<ExprId> = Vec::new();
        for nd in &l.nodes {
            if let Term::Return { data: Some(w), .. } = &nd.term {
                if w.len() != 1 {
                    returned.clear();
                    break;
                }
                if !returned.contains(&w[0]) {
                    returned.push(w[0]);
                }
            }
        }
        let [word] = returned.as_slice() else {
            continue;
        };
        let mut word = *word;
        let mut tested = false;
        if let Node::Op(op::ISZERO, v) = expr::node(word) {
            if let Node::Op(op::ISZERO, w) = expr::node(v[0]) {
                word = w[0];
                tested = true;
            }
        }
        let returned = word;
        let word = match expr::node(word) {
            Node::Op(op::AND, v) if expr::as_const(v[1]).is_some_and(|m| m.is_low_mask()) => v[0],
            Node::Op(op::AND, v) if expr::as_const(v[0]).is_some_and(|m| m.is_low_mask()) => v[1],
            _ => word,
        };
        let read = ssa::field_read(returned)
            .map(|f| (f.key, Some((f.bit_offset / 8, f.bits))))
            .or_else(|| match expr::node(word) {
                Node::SLoad(key, false, _) => Some((key, None)),
                _ => None,
            });
        let member_of = read.and_then(|(key, part)| {
            let path = ssa::slot_path(key, layout)?;
            let var = storage.iter().position(|s| {
                !s.members.is_empty() && U256::from_hex_str(&s.slot) == Some(path.root)
            })?;
            let depth = element_depth(&storage[var].ty);
            let (offset, nested) = match path.steps.get(depth..)?.split_first() {
                Some((Step::Offset(o), nested)) => (*o, nested),
                _ => (0, &path.steps[depth..]),
            };
            Some((var, offset, part, !nested.is_empty()))
        });
        if let Some((var, offset, part, nested)) = member_of {
            let Some(member) = storage[var].members.iter_mut().find(|m| m.offset == offset) else {
                continue;
            };
            if member.holds_many() != nested {
                continue;
            }
            let field = part.and_then(|(byte, bits)| {
                member
                    .fields
                    .iter()
                    .position(|f| f.offset == byte && f.bits == bits)
            });
            let ty = match field {
                Some(i) => member.fields[i].ty.clone(),
                None => member.ty.clone(),
            };
            let target = match field {
                Some(i) => &mut member.fields[i].name,
                None if member.fields.is_empty() => &mut member.name,
                None => continue,
            };
            let predicate = tested && ty != "bool" && ty != "uint8";
            if target.starts_with("field") && !predicate {
                *target = name.clone();
                taken.insert(name);
            }
            continue;
        }
        let field = emit::packed_read(word);
        let root: Option<U256> = match (field, expr::node(word)) {
            (Some((k, _, _)), _) => Some(k),
            (None, Node::SLoad(key, false, _)) => match expr::node(key) {
                Node::Const(k) => emit::hashed_slot(k).map(|(s, _)| s).or(Some(k)),
                _ => emit::element_root(key).or_else(|| {
                    ssa::slot_path(key, layout)
                        .filter(|p| p.steps.iter().all(|s| matches!(s, ssa::Step::Key(_))))
                        .map(|p| p.root)
                }),
            },
            _ => None,
        };
        let Some(root) = root else { continue };
        let Some(var) = storage.iter_mut().find(|s| {
            U256::from_hex_str(&s.slot).or_else(|| U256::from_dec_str(&s.slot)) == Some(root)
        }) else {
            continue;
        };
        match field {
            Some((_, off, bits)) => {
                let prefix = format!("{}_", var.name);
                let Some(fld) = var
                    .fields
                    .iter_mut()
                    .find(|x| x.offset == off && x.bits == bits)
                else {
                    continue;
                };
                if !fld.name.starts_with(&prefix) {
                    continue;
                }
                fld.name = name.clone();
            }
            None => {
                let bare =
                    matches!(expr::node(word), Node::SLoad(key, false, _) if expr::is_const(key));
                if !var.name.starts_with("stor_")
                    || !var.fields.is_empty()
                    || (bare && var.ty.ends_with("[]"))
                {
                    continue;
                }
                var.name = name.clone();
            }
        }
        taken.insert(name);
    }
}

fn element_depth(ty: &str) -> usize {
    ty.matches("mapping(").count() + ty.matches("[]").count()
}

#[derive(Clone, Debug, Default)]
pub struct Callees {
    pub returns: HashMap<usize, Vec<String>>,
    pub names: HashMap<usize, String>,
    pub free_pointer: bool,
    pub reads: std::sync::Arc<HashMap<usize, lift::MemoryReads>>,
}

fn callee_reads(
    functions: &[Function],
    checked_indices: bool,
) -> HashMap<usize, lift::MemoryReads> {
    let internal: Vec<(usize, &Lifted)> = functions
        .iter()
        .filter(|f| f.kind == FnKind::Internal)
        .filter_map(|f| f.lifted.as_ref().map(|l| (f.pc, l)))
        .collect();
    let mut reads: HashMap<usize, lift::MemoryReads> = internal
        .iter()
        .map(|(pc, _)| (*pc, lift::MemoryReads::default()))
        .collect();
    loop {
        let mut changed = false;
        for (pc, l) in &internal {
            let now = l.entry_reads(checked_indices, &|callee| reads.get(&callee));
            if reads.get(pc) != Some(&now) {
                reads.insert(*pc, now);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    reads
}

impl Callees {
    #[must_use]
    pub fn of(functions: &[Function], compiler: compiler::Kind) -> Callees {
        let internal = || functions.iter().filter(|f| f.kind == FnKind::Internal);
        Callees {
            returns: internal().map(|f| (f.pc, f.returns.clone())).collect(),
            names: internal().map(|f| (f.pc, f.name.clone())).collect(),
            free_pointer: compiler == compiler::Kind::Solc,
            reads: std::sync::Arc::new(callee_reads(functions, compiler == compiler::Kind::Vyper)),
        }
    }
}

pub fn make_names(
    f: &Function,
    storage: &[StorageVar],
    layout: MappingLayout,
    loaders: &HashMap<usize, U256>,
    callees: &Callees,
) -> Names {
    let mut n = Names {
        layout,
        callee_names: callees.names.clone(),
        callee_reads: Some(callees.reads.clone()),
        blocks: f
            .lifted
            .as_ref()
            .filter(|_| callees.free_pointer)
            .map(emit::number_blocks),
        ..Default::default()
    };
    if f.kind != FnKind::Internal {
        for p in &f.params {
            n.params.insert(p.index, p.name.clone());
        }
    }
    n.bool_returns = f.returns.iter().map(|t| t == "bool").collect();
    n.bools.extend(f.bool_vars.iter().map(|v| expr::var(*v)));
    if let Some(l) = &f.lifted {
        let mut seqs: Vec<u32> = l
            .nodes
            .iter()
            .flat_map(|nd| nd.stmts.iter())
            .filter_map(|st| match st {
                Stmt::Call { seq, .. } | Stmt::Create { seq, .. } | Stmt::Internal { seq, .. } => {
                    Some(*seq)
                }
                _ => None,
            })
            .collect();
        seqs.sort_unstable();
        seqs.dedup();
        let mut m = n.seqs.borrow_mut();
        for (i, sq) in seqs.iter().enumerate() {
            m.insert(*sq, i as u32 + 1);
        }
    }
    if let Some(l) = &f.lifted {
        let k = l.ret_slot.map(|k| k as usize).unwrap_or(l.n_args);
        for i in 0..l.n_args.max(k + 1) {
            let name = if i < k {
                let index = k - 1 - i;
                match f.params.get(index).filter(|_| f.kind == FnKind::Internal) {
                    Some(p) => p.name.clone(),
                    None => format!("arg{index}"),
                }
            } else if i == k && l.ret_slot.is_some() {
                "__return_pc".to_string()
            } else {
                format!(
                    "caller_stack{}",
                    i - k - if l.ret_slot.is_some() { 1 } else { 0 }
                )
            };
            n.args.insert(i as u32, name);
        }
    }
    for s in storage {
        if let Some(slot) = U256::from_hex_str(&s.slot).or_else(|| U256::from_dec_str(&s.slot)) {
            n.storage.insert(slot, s.name.clone());
            if s.ty.ends_with("[]") && s.fixed_array {
                n.array_bases.insert(slot);
            }
            if s.ty.ends_with("[]") && !s.fixed_array {
                n.dyn_arrays.insert(slot);
            }
            if let Some(t) = element_type(&s.ty) {
                n.elem_types.insert(slot, t);
            }
            for fld in &s.fields {
                n.fields
                    .insert((slot, fld.offset, fld.bits), fld.name.clone());
                if fld.ty == "bool" {
                    n.bool_fields.insert((slot, fld.offset, fld.bits));
                }
            }
            if !s.members.is_empty() {
                n.struct_depth.insert(slot, element_depth(&s.ty));
            }
            for member in &s.members {
                n.members.insert((slot, member.offset), member.name.clone());
                let narrow = emit::element_width(&member.ty).filter(|bits| *bits < 256);
                for bits in narrow.into_iter().chain((member.ty == "bool").then_some(1)) {
                    n.member_fields
                        .insert((slot, member.offset, 0, bits), member.name.clone());
                }
                for fld in &member.fields {
                    n.member_fields.insert(
                        (slot, member.offset, fld.offset, fld.bits),
                        fld.name.clone(),
                    );
                }
            }
        }
    }
    if let Some(l) = &f.lifted {
        for nd in &l.nodes {
            for st in &nd.stmts {
                if let Stmt::Internal {
                    callee, results, ..
                } = st
                {
                    if let (Some(k), [r]) = (loaders.get(callee), results.as_slice()) {
                        let name = n
                            .storage
                            .get(k)
                            .cloned()
                            .unwrap_or_else(|| format!("stor_{}", k.to_decimal()));
                        n.aliases.insert(*r, name);
                    }
                    if let Some(tys) = callees.returns.get(callee) {
                        for (r, ty) in results.iter().zip(tys) {
                            if ty == "bool" {
                                n.bools.insert(*r);
                            }
                        }
                    }
                }
            }
        }
    }
    n
}

fn refine_types(functions: &mut [Function], env: &TypeEnv) {
    let debug = std::env::var("EVMDEC_DEBUG_TYPES").is_ok();
    for f in functions.iter_mut() {
        let Some(l) = &f.lifted else { continue };
        match f.kind {
            FnKind::External => {
                refine_params(f.pc, &mut f.params, env);
                refine_returns(&mut f.returns, l, f.pc, &f.name, env, debug);
            }
            FnKind::Internal => {
                f.params = internal_params(l, f.pc, f.n_args, env);
                refine_results(&mut f.returns, f.pc, env);
            }
            _ => {}
        }
        f.bool_vars = bool_vars(f.pc, l, env);
    }
}

fn refine_params(pc: usize, params: &mut [Param], env: &TypeEnv) {
    for p in params.iter_mut() {
        if p.ty == "address" || p.ty.starts_with("uint") {
            if let Some(t) = env.param_type(pc, p.index) {
                p.ty = t;
            }
        } else if p.ty == "bool" && env.param_is_numeric(pc, p.index) {
            p.ty = env
                .param_type(pc, p.index)
                .unwrap_or_else(|| "uint256".to_string());
        }
    }
}

fn refine_returns(
    returns: &mut [String],
    l: &Lifted,
    pc: usize,
    name: &str,
    env: &TypeEnv,
    debug: bool,
) {
    let rets: Vec<&[ExprId]> = l
        .nodes
        .iter()
        .filter_map(|nd| match &nd.term {
            Term::Return { data: Some(w), .. } => Some(w.as_slice()),
            _ => None,
        })
        .collect();
    if env.vyper() {
        for ty in returns.iter_mut() {
            if ty.starts_with("uint") && ty != "uint256" {
                *ty = "uint256".into();
            }
        }
    }
    if rets.is_empty() || rets.iter().any(|w| w.len() != returns.len()) {
        return;
    }
    for (i, ty) in returns.iter_mut().enumerate() {
        let t = rets
            .iter()
            .fold(types::Ty::Unknown, |t, w| t.join(env.type_of(w[i], pc)));
        if ty == "address" && t == types::Ty::Uint(160) {
            *ty = "uint160".into();
        }
        if ty != "uint256" {
            continue;
        }
        if debug {
            eprintln!(
                "[types] return {} of {} (pc {:#x}): {:?} from {:?}",
                i,
                name,
                pc,
                t,
                rets.iter().map(|w| expr::node(w[i])).collect::<Vec<_>>()
            );
        }
        if let Some(t) = t.solidity() {
            *ty = t;
        }
    }
}

fn internal_params(l: &Lifted, pc: usize, n_args: usize, env: &TypeEnv) -> Vec<Param> {
    let arity = ssa::arity(l);
    let direct = function::internal_param_types(l, n_args);
    (0..n_args)
        .map(|i| {
            let ty = match direct.get(i) {
                Some(t) if t != "uint256" => t.clone(),
                _ => env
                    .arg_type(pc, arity, i)
                    .unwrap_or_else(|| "uint256".to_string()),
            };
            Param {
                index: i as u32,
                ty,
                name: format!("arg{}", i),
            }
        })
        .collect()
}

fn refine_results(returns: &mut [String], pc: usize, env: &TypeEnv) {
    let n = returns.len();
    for (i, ty) in returns.iter_mut().enumerate() {
        if ty == "uint256" {
            if let Some(t) = env.result_type(pc, (n - 1 - i) as u16) {
                *ty = t;
            }
        }
    }
}

fn bool_vars(pc: usize, l: &Lifted, env: &TypeEnv) -> Vec<u32> {
    let mut vars: Vec<u32> = ssa::phi_defs(l)
        .keys()
        .filter_map(|var| match expr::node(*var) {
            Node::Var(v) if env.var_is_bool(pc, v) => Some(v),
            _ => None,
        })
        .collect();
    vars.sort_unstable();
    vars
}

fn refine_storage_types(storage: &mut [StorageVar], env: &TypeEnv) {
    fn refine(ty: &str, root: U256, steps: &mut Vec<ShapeStep>, env: &TypeEnv) -> String {
        if let Some(inner) = ty
            .strip_prefix("mapping(")
            .and_then(|r| r.strip_suffix(')'))
        {
            let Some((k, v)) = inner.split_once(" => ") else {
                return ty.to_string();
            };
            steps.push(ShapeStep::Key);
            let kt = if k == "uint256" {
                env.key_type(root, steps).unwrap_or_else(|| k.to_string())
            } else {
                k.to_string()
            };
            let vt = refine(v, root, steps, env);
            steps.pop();
            return format!("mapping({} => {})", kt, vt);
        }
        if let Some(elem) = ty.strip_suffix("[]") {
            steps.push(ShapeStep::Index);
            let et = refine(elem, root, steps, env);
            steps.pop();
            return format!("{}[]", et);
        }
        if ty == "uint256" {
            if let Some(t) = env.slot_type(root, steps) {
                return t;
            }
        }
        ty.to_string()
    }
    for var in storage.iter_mut() {
        if !var.fields.is_empty() {
            continue;
        }
        let Some(root) = U256::from_hex_str(&var.slot) else {
            continue;
        };
        var.ty = refine(&var.ty, root, &mut Vec::new(), env);
    }
}

fn hashed_slots(functions: &[Function], layout: MappingLayout) -> BTreeSet<Shape> {
    let mut seen: HashSet<ExprId> = HashSet::new();
    let mut found = BTreeSet::new();
    let mut pending: Vec<ExprId> = Vec::new();
    for f in functions {
        let Some(l) = &f.lifted else { continue };
        for nd in &l.nodes {
            pending.extend(lift::roots(nd).into_iter().map(|r| r.expr));
        }
    }
    while let Some(e) = pending.pop() {
        if !seen.insert(e) {
            continue;
        }
        if let Node::Keccak(words, 0) = expr::node(e) {
            if let [head] = words.as_slice() {
                if let Some(path) = ssa::slot_path(*head, layout) {
                    found.insert(path.shape(SlotSpace::Persistent));
                }
            }
        }
        pending.extend(expr::children(e));
    }
    found
}

fn element_container(ty: &str, depth: usize) -> String {
    if depth == 0 {
        return "uint256".to_string();
    }
    if let Some(inner) = ty.strip_suffix("[]") {
        return format!("{}[]", element_container(inner, depth - 1));
    }
    let entry = ty
        .strip_prefix("mapping(")
        .and_then(|r| r.strip_suffix(')'))
        .and_then(|inner| inner.split_once(" => "));
    match entry {
        Some((key, value)) => {
            format!("mapping({key} => {})", element_container(value, depth - 1))
        }
        None => ty.to_string(),
    }
}

fn nested_type(
    root: U256,
    steps: &mut Vec<ShapeStep>,
    rest: &[ShapeStep],
    env: &TypeEnv,
) -> String {
    let Some((step, deeper)) = rest.split_first() else {
        return env
            .slot_type(root, steps)
            .unwrap_or_else(|| "uint256".to_string());
    };
    steps.push(*step);
    let ty = match step {
        ShapeStep::Key => {
            let key = env
                .key_type(root, steps)
                .unwrap_or_else(|| "uint256".to_string());
            format!(
                "mapping({key} => {})",
                nested_type(root, steps, deeper, env)
            )
        }
        _ => format!("{}[]", nested_type(root, steps, deeper, env)),
    };
    steps.pop();
    ty
}

type Located<'a> = (&'a Shape, Option<(u32, u32)>);

fn struct_members(storage: &mut [StorageVar], env: &TypeEnv, hashed: &BTreeSet<Shape>) {
    #[derive(Default)]
    struct Member {
        fields: BTreeSet<(u32, u32)>,
        nesting: Vec<ShapeStep>,
    }
    let mut shapes: BTreeMap<U256, Vec<Located<'_>>> = BTreeMap::new();
    for loc in env.locations() {
        let (shape, field) = match loc {
            types::Loc::Slot(shape) => (shape, None),
            types::Loc::Field {
                shape,
                bit_offset,
                bits,
            } => (shape, Some((*bit_offset, *bits))),
            _ => continue,
        };
        if shape.space == SlotSpace::Persistent {
            shapes.entry(shape.root).or_default().push((shape, field));
        }
    }
    let is_offset = |s: &ShapeStep| matches!(s, ShapeStep::Offset(_));
    for var in storage.iter_mut() {
        let Some(root) = U256::from_hex_str(&var.slot) else {
            continue;
        };
        let Some(found) = shapes.get(&root) else {
            continue;
        };
        let depth = found
            .iter()
            .filter_map(|(shape, _)| shape.steps.iter().position(is_offset))
            .min();
        let Some(depth) = depth.filter(|d| (1..=element_depth(&var.ty)).contains(d)) else {
            continue;
        };
        let mut members: BTreeMap<u64, Member> = BTreeMap::new();
        for (shape, field) in found {
            if shape.steps.len() < depth {
                continue;
            }
            let (offset, rest) = match shape.steps[depth..].split_first() {
                Some((ShapeStep::Offset(o), rest)) => (*o, rest),
                _ => (0, &shape.steps[depth..]),
            };
            let nesting = &rest[..rest.iter().position(is_offset).unwrap_or(rest.len())];
            let member = members.entry(offset).or_default();
            if nesting.len() > member.nesting.len() {
                member.nesting = nesting.to_vec();
            }
            if rest.is_empty() {
                member.fields.extend(*field);
            }
        }
        let element: Vec<ShapeStep> = found
            .iter()
            .find(|(shape, _)| shape.steps.len() >= depth)
            .map(|(shape, _)| shape.steps[..depth].to_vec())
            .unwrap_or_default();
        var.ty = element_container(&var.ty, depth);
        var.members = members
            .iter()
            .map(|(offset, member)| {
                let mut steps = element.clone();
                if *offset > 0 {
                    steps.push(ShapeStep::Offset(*offset));
                }
                let name = format!("field{offset}");
                let narrowest: BTreeMap<u32, u32> =
                    member
                        .fields
                        .iter()
                        .fold(BTreeMap::new(), |mut at, (bit_offset, bits)| {
                            let width = at.entry(*bit_offset).or_insert(*bits);
                            *width = (*width).min(*bits);
                            at
                        });
                let fields_seen: Vec<(u32, u32)> = narrowest.into_iter().collect();
                let packed = fields_seen.len() > 1 || fields_seen.iter().any(|(at, _)| *at > 0);
                let field_type = |bit_offset: u32, bits: u32| {
                    let shape = Shape {
                        root,
                        steps: steps.clone(),
                        space: SlotSpace::Persistent,
                    };
                    env.info(&types::Loc::Field {
                        shape,
                        bit_offset,
                        bits,
                    })
                    .and_then(|i| i.ty.solidity())
                    .unwrap_or_else(|| match bits {
                        160 => "address".to_string(),
                        b if b.is_multiple_of(8) => format!("uint{b}"),
                        b => format!("uint{}", b.div_ceil(8) * 8),
                    })
                };
                let head = Shape {
                    root,
                    steps: steps.clone(),
                    space: SlotSpace::Persistent,
                };
                let scalar = match (packed, fields_seen.first()) {
                    (true, _) => "packed".to_string(),
                    (false, Some((bit_offset, bits))) => field_type(*bit_offset, *bits),
                    (false, None) => env
                        .slot_type(root, &steps)
                        .unwrap_or_else(|| "uint256".to_string()),
                };
                let flagged = packed || scalar == "bool";
                if hashed.contains(&head) && flagged {
                    return StructMember {
                        offset: *offset,
                        name,
                        ty: "bytes".to_string(),
                        fields: Vec::new(),
                    };
                }
                if !member.nesting.is_empty() || hashed.contains(&head) {
                    let nesting = match member.nesting.is_empty() {
                        true => vec![ShapeStep::Index],
                        false => member.nesting.clone(),
                    };
                    return StructMember {
                        offset: *offset,
                        name,
                        ty: nested_type(root, &mut steps.clone(), &nesting, env),
                        fields: Vec::new(),
                    };
                }
                let fields: Vec<StorageField> = if packed {
                    fields_seen
                        .iter()
                        .map(|(bit_offset, bits)| StorageField {
                            offset: bit_offset / 8,
                            bits: *bits,
                            name: format!("{name}_{}", bit_offset / 8),
                            ty: field_type(*bit_offset, *bits),
                        })
                        .collect()
                } else {
                    Vec::new()
                };
                StructMember {
                    offset: *offset,
                    name,
                    ty: scalar,
                    fields,
                }
            })
            .collect();
    }
}

type PackedFields = BTreeMap<U256, BTreeMap<(u32, u32), Vec<Option<U256>>>>;

struct Inventories {
    storage: Vec<StorageVar>,
    events: Vec<String>,
    errors: Vec<String>,
    strings: Vec<String>,
    selectors: Vec<String>,
}

fn inventories(
    functions: &[Function],
    layout: MappingLayout,
    string_slots: &HashSet<U256>,
) -> Inventories {
    let vyper = layout == MappingLayout::Vyper;
    let mut slots: BTreeMap<U256, (usize, usize, BTreeSet<String>)> = BTreeMap::new();
    let mut events: BTreeSet<String> = BTreeSet::new();
    let mut errors: BTreeSet<String> = BTreeSet::new();
    let mut strings: BTreeSet<String> = BTreeSet::new();
    let mut selectors: BTreeSet<String> = BTreeSet::new();
    let names = Names {
        layout,
        ..Default::default()
    };
    let mut fields: PackedFields = BTreeMap::new();
    let bases = fixed_array_bases(functions);
    for f in functions {
        let Some(l) = &f.lifted else { continue };
        for nd in &l.nodes {
            for s in &nd.stmts {
                match s {
                    Stmt::SStore {
                        key,
                        val,
                        transient: false,
                        ..
                    } => {
                        note_slot(*key, &mut slots, false, Some(*val), vyper, &bases);
                        if let Some((k, off, bits, value)) = emit::packed_write(*key, *val) {
                            fields
                                .entry(k)
                                .or_default()
                                .entry((off, bits))
                                .or_default()
                                .push(expr::as_const(value));
                        }
                    }
                    Stmt::Log { topics, data, .. } => {
                        if let Some(t0) = topics.first().and_then(|t| expr::as_const(*t)) {
                            match sigs::event(&t0.to_be_bytes()) {
                                Some(sig) => events.insert(with_indexed(&sig, topics.len() - 1)),
                                None => {
                                    let mut tys: Vec<String> =
                                        vec!["uint256 indexed".to_string(); topics.len() - 1];
                                    match data {
                                        Some(w) => {
                                            tys.extend(w.iter().map(|_| "uint256".to_string()))
                                        }
                                        None => tys.push("bytes".to_string()),
                                    }
                                    events.insert(format!(
                                        "{}({}); // topic0 {}",
                                        emit::event_placeholder_name(t0),
                                        tys.join(", "),
                                        t0.to_hex_padded(32)
                                    ))
                                }
                            };
                        } else if topics.is_empty() {
                            events.insert("<anonymous log0>".into());
                        }
                    }
                    Stmt::Call {
                        input: Some(words),
                        in_len,
                        ..
                    } => {
                        if let Some(w0) = words.first() {
                            let in_len_c = expr::as_const(*in_len).and_then(|l| l.as_usize());
                            if let Some(sel) = emit::leading_selector(*w0, in_len_c) {
                                if in_len_c.is_none_or(|l| l >= 4 && (l - 4) % 32 == 0) {
                                    selectors.insert(match sigs::function(sel) {
                                        Some(sig) => format!("{:#010x} {}", sel, sig),
                                        None => format!("{:#010x}", sel),
                                    });
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
            if let Term::Revert {
                data: Some(words),
                len,
                ..
            } = &nd.term
            {
                if let Some(c0) = words.first().and_then(|w| expr::as_const(*w)) {
                    if (c0 & expr::mask_bits(224)).is_zero() {
                        let sel = (c0 >> 224).low_u64() as u32;
                        if sel == emit::SEL_ERROR {
                            if let Some(s) = emit::decode_string_payload(
                                words,
                                expr::as_const(*len).and_then(|l| l.as_usize()),
                            ) {
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
            let init_words: HashSet<ExprId> = nd
                .stmts
                .iter()
                .filter_map(|s| match s {
                    Stmt::Create { init: Some(w), .. } => Some(w.iter().copied()),
                    _ => None,
                })
                .flatten()
                .collect();
            for root in lift::roots(nd) {
                collect_sloads(root.expr, &mut slots, vyper, &bases);
                if !init_words.contains(&root.expr) {
                    collect_strings(root.expr, &mut strings);
                }
                collect_fields(root, &mut fields);
            }
        }
    }
    let _ = names;
    let elem_types = element_types(functions);
    let storage: Vec<StorageVar> = slots
        .into_iter()
        .map(|(slot, (reads, writes, tys))| {
            let fixed_array = tys.contains("fixed[]");
            let tys: BTreeSet<String> = tys
                .into_iter()
                .map(|t| {
                    if t == "fixed[]" {
                        "uint256[]".to_string()
                    } else {
                        t
                    }
                })
                .collect();
            let ty = if string_slots.contains(&slot) {
                "string".to_string()
            } else {
                let mut v: Vec<String> = tys.into_iter().collect();
                v.sort_by_key(|t| {
                    if t.starts_with("mapping") {
                        0
                    } else if t.contains('[') {
                        1
                    } else if t == "address" || t == "bool" {
                        2
                    } else {
                        3
                    }
                });
                let picked = v
                    .into_iter()
                    .next()
                    .unwrap_or_else(|| "uint256".to_string());
                match elem_types.get(&slot) {
                    Some(t) if picked.ends_with("[]") => format!("{}[]", t),
                    Some(t) if picked.starts_with("mapping(") => {
                        let head = picked.rsplit_once("=> ").map(|(h, _)| h.to_string());
                        match head {
                            Some(h) => format!("{}=> {})", h, t),
                            None => picked,
                        }
                    }
                    _ => picked,
                }
            };
            let name = match crate::slots::well_known(slot) {
                Some(known) => known.to_string(),
                None if slot.bits() <= 32 => format!("stor_{}", slot.to_decimal()),
                None => format!("stor_{}", slot.to_hex()),
            };
            let mut fs: Vec<StorageField> = Vec::new();
            if let (Some(acc), false) = (fields.get(&slot), string_slots.contains(&slot)) {
                let keys: Vec<(u32, u32)> = acc
                    .keys()
                    .copied()
                    .filter(|(off, bits)| *bits < 256 && off * 8 + bits <= 256)
                    .collect();
                let packed = keys.iter().any(|(off, _)| *off > 0) || keys.len() > 1;
                if packed {
                    let mut sorted = keys.clone();
                    sorted.sort();
                    for (off, bits) in sorted {
                        let covered = keys.iter().any(|(o2, b2)| {
                            (*o2, *b2) != (off, bits) && *o2 >= off && o2 * 8 + b2 <= off * 8 + bits
                        }) && keys
                            .iter()
                            .filter(|(o2, _)| *o2 >= off && o2 * 8 < off * 8 + bits)
                            .count()
                            > 1;
                        if covered {
                            continue;
                        }
                        let writes = &acc[&(off, bits)];
                        let signed = writes.contains(&Some(U256::MAX));
                        let boolish = bits == 8
                            && !writes.is_empty()
                            && writes
                                .iter()
                                .all(|w| matches!(w, Some(c) if c.is_zero() || *c == U256::ONE));
                        let ty = if signed {
                            format!("int{}", bits)
                        } else if bits == 160 {
                            "address".to_string()
                        } else if bits == 1 || boolish {
                            "bool".to_string()
                        } else if bits % 8 == 0 {
                            format!("uint{}", bits)
                        } else {
                            format!("uint{}", bits.div_ceil(8) * 8)
                        };
                        fs.push(StorageField {
                            offset: off,
                            bits,
                            name: format!("{}_{}", name, off),
                            ty,
                        });
                    }
                }
            }
            let ty = if fs.is_empty() {
                ty
            } else {
                "packed".to_string()
            };
            StorageVar {
                fixed_array,
                slot: slot.to_hex(),
                name,
                ty,
                reads,
                writes,
                fields: fs,
                members: Vec::new(),
            }
        })
        .collect();
    Inventories {
        storage,
        events: events.into_iter().collect(),
        errors: errors.into_iter().collect(),
        strings: strings.into_iter().collect(),
        selectors: selectors.into_iter().collect(),
    }
}

// Indexed parameters are conventionally declared first, so the first n are marked. This is a guess.
fn with_indexed(sig: &str, n: usize) -> String {
    let Some(open) = sig.find('(') else {
        return sig.to_string();
    };
    let name = &sig[..open];
    let inner = sig[open + 1..].trim_end_matches(')');
    if inner.is_empty() || n == 0 {
        return sig.to_string();
    }
    let mut parts = Vec::new();
    let mut depth = 0;
    let mut start = 0;
    for (i, ch) in inner.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => depth -= 1,
            ',' if depth == 0 => {
                parts.push(&inner[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    parts.push(&inner[start..]);
    let n = n.min(parts.len());
    let out: Vec<String> = parts
        .iter()
        .enumerate()
        .map(|(i, p)| {
            if i < n {
                format!("{} indexed", p)
            } else {
                p.to_string()
            }
        })
        .collect();
    format!("{}({})", name, out.join(", "))
}

fn note_slot(
    key: ExprId,
    slots: &mut BTreeMap<U256, (usize, usize, BTreeSet<String>)>,
    read: bool,
    val: Option<ExprId>,
    vyper: bool,
    bases: &BTreeSet<U256>,
) {
    let (root, ty) = slot_root(key, vyper, bases);
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

fn fixed_array_bases(functions: &[Function]) -> BTreeSet<U256> {
    let mut seen: BTreeSet<U256> = BTreeSet::new();
    let mut keys: Vec<(ExprId, usize)> = Vec::new();
    let mut bounded: Vec<HashSet<ExprId>> = Vec::new();
    for (fi, f) in functions.iter().enumerate() {
        let Some(l) = &f.lifted else { continue };
        let mut bounds: HashSet<ExprId> = HashSet::new();
        for nd in &l.nodes {
            let mut conds: Vec<ExprId> = nd
                .stmts
                .iter()
                .filter_map(|st| match st {
                    Stmt::Require { cond, .. } => Some(*cond),
                    _ => None,
                })
                .collect();
            if let Term::Branch { cond, .. } = &nd.term {
                conds.push(*cond);
            }
            for mut c in conds {
                while let Node::Op(op::ISZERO, v) = expr::node(c) {
                    c = v[0];
                }
                match expr::node(c) {
                    Node::Op(op::LT, v) if expr::as_const(v[1]).is_some_and(|n| n.bits() <= 16) => {
                        bounds.insert(v[0]);
                    }
                    Node::Op(op::GT, v) if expr::as_const(v[0]).is_some_and(|n| n.bits() <= 16) => {
                        bounds.insert(v[1]);
                    }
                    _ => {}
                }
            }
            for st in &nd.stmts {
                if let Stmt::SStore { key, .. } = st {
                    keys.push((*key, fi));
                }
            }
            for e in lift::node_exprs(nd) {
                let mut stack = vec![e];
                let mut visited = HashSet::new();
                while let Some(x) = stack.pop() {
                    if !visited.insert(x) || visited.len() > 20_000 {
                        continue;
                    }
                    if let Node::SLoad(k, false, _) = expr::node(x) {
                        keys.push((k, fi));
                    }
                    stack.extend(expr::children(x));
                }
            }
        }
        bounded.resize(fi + 1, HashSet::new());
        bounded[fi] = bounds;
    }
    for (k, fi) in keys {
        if let Node::Op(op::ADD, v) = expr::node(k) {
            for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
                if let Some(c) = expr::as_const(a) {
                    let plain = emit::is_plain_index(b);
                    let is_bounded = bounded.get(fi).is_some_and(|bs| bs.contains(&b));
                    if plain && is_bounded && c.bits() <= 32 && !c.is_zero() {
                        seen.insert(c);
                    }
                }
            }
        }
    }
    let mut bases: BTreeSet<U256> = BTreeSet::new();
    for c in seen {
        match bases.range(..=c).next_back() {
            Some(b) if c.wrapping_sub(*b).low_u64() < 16 => {}
            _ => {
                bases.insert(c);
            }
        }
    }
    bases
}

// A key that happens to be zero or one where it is used says nothing about the key type.
fn slot_root(key: ExprId, vyper: bool, bases: &BTreeSet<U256>) -> (Option<U256>, Option<String>) {
    if let Some(c) = expr::as_const(key) {
        if let Some((s, _)) = emit::hashed_slot(c) {
            return (Some(s), Some("uint256[]".into()));
        }
        return (Some(c), None);
    }
    match expr::node(key) {
        Node::Keccak(words, 0) if words.len() == 2 => {
            let (k, s) = if vyper {
                (words[1], words[0])
            } else {
                (words[0], words[1])
            };
            let (root, inner) = slot_root(s, vyper, bases);
            let kt = match function::type_of_value(k).as_str() {
                "bool" => "uint256".to_string(),
                kt => kt.to_string(),
            };
            let ty = match inner {
                Some(t) => format!("mapping({} => {})", kt, t),
                None => format!("mapping({} => uint256)", kt),
            };
            (root, Some(ty))
        }
        Node::Keccak(words, 0) if words.len() == 1 => {
            let (root, _) = slot_root(words[0], vyper, bases);
            (root, Some("uint256[]".into()))
        }
        Node::Op(op::ADD, v) => {
            for (a, _) in [(v[0], v[1]), (v[1], v[0])] {
                if let Some((s, _)) = expr::as_const(a).and_then(emit::hashed_slot) {
                    return (Some(s), Some("uint256[]".into()));
                }
            }
            for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
                if let Some(c) = expr::as_const(a) {
                    if emit::is_plain_index(b) {
                        if let Some(base) = bases.range(..=c).next_back() {
                            if c.wrapping_sub(*base).low_u64() < 16 {
                                return (Some(*base), Some("fixed[]".into()));
                            }
                        }
                    }
                }
            }
            let (root, inner) = slot_root(v[0], vyper, bases);
            match inner {
                Some(t) if t.starts_with("mapping") => (root, Some(t)),
                _ => (root, Some("uint256[]".into())),
            }
        }
        _ => (None, None),
    }
}

fn collect_fields(root: lift::Root, fields: &mut PackedFields) {
    let mut seen = HashSet::new();
    let mut stack = vec![root.expr];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 50_000 {
            continue;
        }
        if x == root.expr && root.payload {
            stack.extend(expr::children(x));
            continue;
        }
        if let Some((k, off, bits)) = emit::packed_read(x) {
            if off > 0 || bits < 256 {
                let entry = fields.entry(k).or_default().entry((off, bits)).or_default();
                if matches!(expr::node(x), Node::Op(op::SIGNEXTEND, _)) {
                    entry.push(Some(U256::MAX));
                }
            }
        }
        stack.extend(expr::children(x));
    }
}

fn collect_sloads(
    e: ExprId,
    slots: &mut BTreeMap<U256, (usize, usize, BTreeSet<String>)>,
    vyper: bool,
    bases: &BTreeSet<U256>,
) {
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 50_000 {
            continue;
        }
        let n = expr::node(x);
        match &n {
            Node::SLoad(key, false, _) => note_slot(*key, slots, true, None, vyper, bases),
            Node::Op(op::AND, v) => {
                if let (Node::SLoad(key, false, _), Some(m)) =
                    (expr::node(v[0]), expr::as_const(v[1]))
                {
                    if m.is_low_mask() {
                        let (root, inner) = slot_root(key, vyper, bases);
                        if let Some(root) = root {
                            let bits = m.bits();
                            let t = if bits == 160 {
                                "address".to_string()
                            } else if bits == 1 {
                                "bool".to_string()
                            } else if bits % 8 == 0 {
                                format!("uint{}", bits)
                            } else {
                                "uint256".into()
                            };
                            let full = match inner {
                                Some(i) => i.replace("=> uint256)", &format!("=> {})", t)),
                                None => t,
                            };
                            slots
                                .entry(root)
                                .or_insert((0, 0, BTreeSet::new()))
                                .2
                                .insert(full);
                        }
                    }
                }
            }
            _ => {}
        }
        stack.extend(expr::children(x));
    }
}

fn scan_strings(code: &[u8], code_end: usize, skip: &[(usize, usize)]) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let end = code_end.min(code.len());
    let mut pending: Option<(String, usize)> = None;
    let insns = crate::disasm::disassemble(&code[..end]);
    for (idx, insn) in insns.iter().enumerate() {
        if skip.iter().any(|(o, l)| insn.pc >= *o && insn.pc < *o + *l) {
            continue;
        }
        let Some(imm) = insn.imm else { continue };
        let mut size = insn.opcode as usize - 0x5f;
        let mut imm = imm;
        if let (Some(a), Some(b)) = (insns.get(idx + 1), insns.get(idx + 2)) {
            if a.opcode == 0x60 && b.opcode == crate::opcode::SHL {
                if let Some(k) = a.imm.and_then(|k| k.as_usize()) {
                    if k < 256 {
                        imm = imm << k as u32;
                        size = 32;
                    }
                }
            }
        }
        if size < 4 {
            continue;
        }
        let bytes = imm.to_be_bytes();
        let b = &bytes[32 - size..];
        let text_end = b.iter().position(|x| *x == 0).unwrap_or(b.len());
        let run = &b[..text_end];
        let printable = !run.is_empty()
            && run.iter().all(|x| (0x20..0x7f).contains(x))
            && b[text_end..].iter().all(|x| *x == 0);
        if !printable {
            continue;
        }
        let text = String::from_utf8_lossy(run).into_owned();
        let full = size == 32 && text_end == 32;
        match pending.take() {
            Some((mut acc, at)) if idx - at <= 16 => {
                acc.push_str(&text);
                if full {
                    pending = Some((acc, idx));
                } else {
                    out.push(acc);
                }
            }
            other => {
                if let Some((acc, _)) = other {
                    out.push(acc);
                }
                if full {
                    pending = Some((text, idx));
                } else {
                    out.push(text);
                }
            }
        }
    }
    if let Some((acc, _)) = pending {
        out.push(acc);
    }
    out.retain(|s| {
        let letters = s.chars().filter(|c| c.is_ascii_alphabetic()).count();
        s.len() >= 6 && letters * 2 >= s.len()
    });
    let mut out: Vec<String> = out.iter().map(|s| s.trim().to_string()).collect();
    out.sort();
    out.dedup();
    let snap = out.clone();
    out.retain(|s| {
        !snap
            .iter()
            .any(|o| o.len() > s.len() && o.contains(s.as_str()))
    });
    out
}

fn collect_strings(e: ExprId, out: &mut BTreeSet<String>) {
    if let Some(c) = expr::as_const(e) {
        let b = c.to_be_bytes();
        let end = b.iter().position(|x| *x == 0).unwrap_or(32);
        if end >= 4
            && b[..end].iter().all(|x| (0x20..0x7f).contains(x))
            && b[end..].iter().all(|x| *x == 0)
        {
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

pub fn render(c: &Contract, name: &str) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "// Decompiled by evmdec. Compiler: {}.\n",
        c.language
    ));
    out.push_str(&composite_header(c));
    if let Some(m) = &c.info.metadata {
        if let Some(h) = &m.ipfs {
            match m.ipfs_cid() {
                Some(cid) => {
                    out.push_str(&format!("// Metadata: ipfs {} (multihash {})\n", cid, h))
                }
                None => out.push_str(&format!("// Metadata: ipfs {}\n", h)),
            }
        }
        if let Some(h) = &m.bzzr {
            out.push_str(&format!("// Metadata: {}\n", h));
        }
    }
    let inlined = c.functions.iter().filter(|f| f.inlined).count();
    out.push_str(&format!(
        "// Coverage: {}/{} code blocks, {} unresolved jumps, {} external / {} internal functions{}.\n",
        c.stats.covered_blocks,
        c.stats.code_blocks,
        c.stats.unresolved_jumps,
        c.stats.external_functions,
        c.stats.internal_functions,
        if inlined > 0 { format!(" ({} inlined at every call site and not shown)", inlined) } else { String::new() }
    ));
    if c.functions.iter().any(|f| f.code.contains("ptr")) {
        out.push_str(
            "// Memory: ptrN is a block allocated at the free memory pointer; \
             ptrN = memory(a, b) writes its words; bytes(p) is the byte string at p.\n",
        );
    }
    if c.functions.iter().any(|f| f.code.contains("loc_")) {
        out.push_str(
            "// Memory: loc_N is the variable kept at the fixed memory address 0xN; \
             loc_N[i] is word i of the list that starts there.\n",
        );
    }
    out.push_str(&format!("\ncontract {} {{\n", name));
    if !c.storage.is_empty() {
        out.push_str("    // ---- storage layout ----\n");
        for s in &c.storage {
            if !s.members.is_empty() {
                out.push_str(&format!("    struct {} {{\n", s.struct_name()));
                for member in &s.members {
                    if member.fields.is_empty() {
                        out.push_str(&format!(
                            "        {} {}; // slot +{}\n",
                            member.ty, member.name, member.offset
                        ));
                    }
                    for fld in &member.fields {
                        out.push_str(&format!(
                            "        {} {}; // slot +{} bytes {}..{}\n",
                            fld.ty,
                            fld.name,
                            member.offset,
                            fld.offset,
                            fld.offset + fld.bits.div_ceil(8)
                        ));
                    }
                }
                out.push_str("    }\n");
            }
            if s.fields.is_empty() {
                out.push_str(&format!(
                    "    {} {}; // slot {}, {}{} reads, {} writes\n",
                    s.declared_type(),
                    s.name,
                    s.slot,
                    if s.fixed_array {
                        "fixed-size array in the slots that follow, "
                    } else {
                        ""
                    },
                    s.reads,
                    s.writes
                ));
            } else {
                out.push_str(&format!(
                    "    // slot {} is packed ({} reads, {} writes):\n",
                    s.slot, s.reads, s.writes
                ));
                for fld in &s.fields {
                    out.push_str(&format!(
                        "    {} {}; // slot {} bytes {}..{}\n",
                        fld.ty,
                        fld.name,
                        s.slot,
                        fld.offset,
                        fld.offset + fld.bits.div_ceil(8)
                    ));
                }
            }
        }
        out.push('\n');
    }
    if !c.events.is_empty() {
        for e in &c.events {
            if e.contains("; //") {
                out.push_str(&format!("    event {}\n", e));
            } else {
                out.push_str(&format!("    event {};\n", e));
            }
        }
        out.push('\n');
    }
    if !c.errors.is_empty() {
        for e in &c.errors {
            out.push_str(&format!("    error {};\n", e));
        }
        out.push('\n');
    }
    let mut current_part: Option<usize> = None;
    for f in &c.functions {
        if f.inlined {
            continue;
        }
        if !c.parts.is_empty() && current_part != Some(f.part) {
            current_part = Some(f.part);
            out.push_str(&part_banner(c, f.part));
        }
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
        if c.composite.is_none() {
            out.push_str(&format!(
                "\n// ---- {}: implementation {} ----\n",
                p.kind, p.implementation
            ));
            if let Some(ic) = &p.contract {
                out.push_str(&ic.source);
            }
        }
    }
    out
}

fn part_banner(c: &Contract, index: usize) -> String {
    let Some(p) = c.parts.get(index) else {
        return String::new();
    };
    let what = match (p.role, p.selectors.len()) {
        (PartRole::Shell, _) => "shell: routes calls".to_string(),
        (PartRole::Implementation, _) => "implementation: every unrouted selector".to_string(),
        (PartRole::Facet, n) => format!("facet: {} selectors", n),
    };
    format!(
        "    // ==== {} — {}, {} ====\n\n",
        p.address, what, p.compiler
    )
}

fn composite_header(c: &Contract) -> String {
    let Some(comp) = &c.composite else {
        return String::new();
    };
    let mut out = format!("// Composite: {}. Parts:\n", comp.kind);
    for p in &c.parts {
        let what = match (p.role, p.selectors.len()) {
            (PartRole::Shell, _) => "shell (routes calls)".to_string(),
            (PartRole::Implementation, _) => "implementation (every unrouted selector)".to_string(),
            (PartRole::Facet, n) => format!("facet ({} selectors)", n),
        };
        let _ = writeln!(out, "//   {} — {}, {}", p.address, what, p.compiler);
    }
    out
}

pub fn fmt_function_header(f: &Function) -> String {
    let mut s = String::new();
    match f.kind {
        FnKind::External => {
            let params: Vec<String> = f
                .params
                .iter()
                .map(|p| format!("{} {}", p.ty, p.name))
                .collect();
            s.push_str(&format!(
                "    // selector {}{}\n",
                f.selector.clone().unwrap_or_default(),
                if f.signature.is_none() {
                    " (unknown signature)"
                } else {
                    ""
                }
            ));
            s.push_str(&format!(
                "    function {}({}) external{}",
                f.name,
                params.join(", "),
                mutability_str(f.mutability)
            ));
            if !f.returns.is_empty() {
                s.push_str(&format!(" returns ({})", f.returns.join(", ")));
            }
            s.push_str(" {\n");
        }
        FnKind::Fallback => s.push_str(&format!(
            "    fallback() external{} {{\n",
            if f.mutability == Mutability::Payable {
                " payable"
            } else {
                ""
            }
        )),
        FnKind::Receive => s.push_str("    receive() external payable {\n"),
        FnKind::Constructor => s.push_str("    constructor() {\n"),
        FnKind::Internal => {
            let params: Vec<String> = (0..f.n_args)
                .map(|i| match f.params.get(i) {
                    Some(p) => format!("{} {}", p.ty, p.name),
                    None => format!("uint256 arg{i}"),
                })
                .collect();
            let m = match f.mutability {
                Mutability::View | Mutability::Pure => mutability_str(f.mutability),
                _ => "",
            };
            s.push_str(&format!(
                "    function {}({}) internal{}",
                f.name,
                params.join(", "),
                m
            ));
            if f.n_rets > 0 {
                let tys = if f.returns.len() == f.n_rets {
                    f.returns.clone()
                } else {
                    vec!["uint256".to_string(); f.n_rets]
                };
                s.push_str(&format!(" returns ({})", tys.join(", ")));
            }
            s.push_str(" {\n");
        }
        FnKind::Orphan => {
            let params: Vec<String> = (0..f.n_args).map(|i| format!("uint256 arg{}", i)).collect();
            s.push_str(&format!(
                "    // unreachable code at {:#x}\n    function {}({}) internal {{\n",
                f.pc,
                f.name,
                params.join(", ")
            ));
        }
    }
    s
}
