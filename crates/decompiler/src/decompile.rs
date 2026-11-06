//! Whole-contract decompilation: orchestration and the output model.

use crate::cfg::{self, Program, Recovered};
use crate::compiler;
use crate::emit::{self, MappingLayout, Names};
use crate::expr::{self, ExprId, Node};
use crate::function::{self, FnKind, Mutability, Param};
use crate::lift::{self, Lifted, Lifter, Stmt, Term};
use crate::metadata::{self, BytecodeInfo, CodeKind};
use crate::opcode as op;
use crate::sigs;
use crate::ssa::{self, ShapeStep, Step};
use crate::types::{self, TypeEnv};
use crate::u256::U256;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Write as _;

#[derive(Clone, Debug, Default)]
/// Knobs for one decompilation run.
pub struct Options {
    /// Emit labels/gotos instead of structured code.
    pub flat: bool,
    /// Include per-node program counters as comments.
    pub pcs: bool,
    /// Decompile embedded creation code (contracts deployed by this one).
    pub embedded: bool,
    /// Do not use the built-in signature dictionary (for measuring inference).
    pub no_sigs: bool,
    /// Additional function signatures by selector (e.g. from an online lookup or an ABI).
    pub extra_sigs: HashMap<u32, String>,
}

#[derive(Clone, Debug, Serialize)]
/// One decompiled function: an external entry point, an internal helper or an orphan region.
pub struct Function {
    /// External entry, fallback, receive, constructor, internal helper or orphan region.
    pub kind: FnKind,
    #[serde(skip_serializing_if = "Option::is_none")]
    /// 4-byte selector as `0x`-prefixed hex; external functions only.
    pub selector: Option<String>,
    /// Printed name: from the signature when known, else `func_<selector>` or `func_<pc>`.
    pub name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    /// Canonical signature (`name(type,...)`) when the selector is in a dictionary.
    pub signature: Option<String>,
    /// Inferred state mutability (`pure`, `view`, `nonpayable` or `payable`).
    pub mutability: Mutability,
    /// Parameters: from the signature when known, inferred from calldata use otherwise.
    pub params: Vec<Param>,
    /// Inferred return types.
    pub returns: Vec<String>,
    /// Entry program counter.
    pub pc: usize,
    /// Body rendered as pseudo-Solidity, without the header line.
    pub code: String,
    /// Number of nodes in the lifted control-flow graph (a size measure).
    pub nodes: usize,
    /// State the function touches, including through the internal functions it calls.
    pub effects: function::Effects,
    #[serde(skip)]
    /// The lifted graph the code was rendered from; kept for later analysis, not serialised.
    pub lifted: Option<Lifted>,
    /// Internal functions this one calls (entry pcs).
    pub calls: Vec<usize>,
    /// Number of stack arguments an internal unit takes.
    pub n_args: usize,
    /// Number of values an internal unit returns (the largest `InternalReturn` seen).
    pub n_rets: usize,
    /// Internal helper whose every call site was inlined: not printed.
    #[serde(default)]
    pub inlined: bool,
    /// Phi variables the type solver found to be booleans.
    #[serde(skip)]
    pub bool_vars: Vec<u32>,
    /// Index into [`Contract::parts`] of the part whose code holds this function; 0 is the
    /// contract's own code.
    #[serde(skip_serializing_if = "is_zero_usize")]
    pub part: usize,
    /// Address of the part whose code holds this function, when it is not the contract's own.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub origin: Option<String>,
}

/// Serde helper: skip a zero.
fn is_zero_usize(n: &usize) -> bool {
    *n == 0
}

#[derive(Clone, Debug, Serialize)]
/// A storage slot the contract reads or writes, as listed in the contract header.
pub struct StorageVar {
    /// The variable is a fixed-size array laid out from this slot (`uint[256] owners`): its
    /// elements occupy the following slots rather than `keccak256(slot) + i`.
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub fixed_array: bool,
    /// Root slot as `0x`-prefixed hex (the base slot for mappings and arrays).
    pub slot: String,
    /// Printed name: `stor_<slot>` (decimal for small slots, hex otherwise).
    pub name: String,
    /// Inferred type (`mapping(…)`, `address`, `string`, …); `packed` when `fields` is set.
    pub ty: String,
    /// Number of `SLOAD`s of this slot, or of a key rooted at it, across all functions.
    pub reads: usize,
    /// Number of `SSTORE`s to this slot, or to a key rooted at it, across all functions.
    pub writes: usize,
    /// Fields of a packed slot (several variables share the 32 bytes).
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub fields: Vec<StorageField>,
}

#[derive(Clone, Debug, Serialize)]
/// One variable of a packed storage slot.
pub struct StorageField {
    /// Byte offset within the slot (0 = least significant).
    pub offset: u32,
    /// Width in bits.
    pub bits: u32,
    /// Printed name: `<slot name>_<byte offset>`.
    pub name: String,
    /// Type inferred from the width and the constants written (`bool`, `address`, `uintN`, `intN`).
    pub ty: String,
}

#[derive(Clone, Debug, Serialize)]
/// Coverage and size figures for one code body, printed in the header comment.
pub struct Stats {
    /// Length of the analysed bytecode in bytes.
    pub code_bytes: usize,
    /// Number of decoded instructions.
    pub instructions: usize,
    /// Number of basic blocks, data and dead regions included.
    pub blocks: usize,
    /// Blocks the EVM could enter, excluding the metadata trailer and embedded creation code.
    pub code_blocks: usize,
    /// Of `code_blocks`, those reached by the main unit, an internal function or an orphan.
    pub covered_blocks: usize,
    /// Jumps whose target could not be resolved.
    pub unresolved_jumps: usize,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    /// Program counters of the unresolved jumps, as hex.
    pub unresolved_jump_pcs: Vec<String>,
    /// Control-flow recovery gave up early on some unit, so the output may be incomplete.
    pub budget_exhausted: bool,
    /// Number of external functions (dispatcher entries).
    pub external_functions: usize,
    /// Number of internal functions, inlined ones included.
    pub internal_functions: usize,
    /// Number of orphan regions (code reached by nothing).
    pub orphans: usize,
    /// Nodes the lifter processed more than once while reaching a fixpoint, summed over units.
    pub lift_reprocess: usize,
    /// Wall-clock time of the decompilation in milliseconds.
    pub time_ms: u128,
}

#[derive(Clone, Debug, Serialize)]
/// The decompilation of one code body: the JSON the CLI prints and the web UI shows.
pub struct Contract {
    /// Bytecode layout: creation/runtime split, constructor arguments and metadata trailer.
    pub info: BytecodeInfo,
    /// Whether the input was runtime code or creation (deployment) code.
    pub kind: CodeKind,
    /// Compiler and version (`solc 0.8.19`), or the bounds the bytecode fingerprints give
    /// without metadata (`solc >= 0.8.0 (no metadata)`).
    pub language: String,
    /// The compiler profile: family, version bounds and code-generation features.
    pub compiler: compiler::Profile,
    /// The solved types of every parameter, helper argument, storage slot and phi variable;
    /// kept for the analyzer, not serialised.
    #[serde(skip)]
    pub types: TypeEnv,
    /// Every recovered function: external entries first, then internal helpers and orphans.
    pub functions: Vec<Function>,
    /// Storage variables, ordered by slot.
    pub storage: Vec<StorageVar>,
    /// Event declarations (`Name(type indexed name, …)` or a placeholder with the topic hash).
    pub events: Vec<String>,
    /// Custom error declarations the code reverts with.
    pub errors: Vec<String>,
    /// String constants found in revert payloads, stored values and the code bytes.
    pub strings: Vec<String>,
    /// `0xselector signature` of the external functions this contract calls.
    pub selectors_called: Vec<String>,
    /// Coverage and size figures.
    pub stats: Stats,
    /// The whole contract rendered as pseudo-Solidity.
    pub source: String,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    /// Contracts this one deploys, decompiled from embedded creation code (`Options::embedded`).
    pub embedded: Vec<Contract>,
    #[serde(skip_serializing_if = "Option::is_none")]
    /// The constructor, decompiled from the creation code when the input was creation code.
    pub constructor: Option<Box<Contract>>,
    /// Storage slots whose value is used as a DELEGATECALL target (proxy implementation slots).
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub delegatecall_slots: Vec<String>,
    /// Constant addresses used as DELEGATECALL targets.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub delegatecall_targets: Vec<String>,
    /// Constant addresses this contract calls (`CALL`/`STATICCALL`/`CALLCODE` to a literal
    /// address): hard-coded dependencies such as tokens, oracles and registries. Precompiles
    /// (1..=9) are excluded.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub call_targets: Vec<String>,
    /// Storage slots whose value is called with `CALL`/`STATICCALL`/`CALLCODE`: dependencies
    /// chosen at run time, read and linked when the contract is fetched by address.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub call_target_slots: Vec<String>,
    /// The addresses found in `call_target_slots` when fetched: `(slot, address)`.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub stored_targets: Vec<(String, String)>,
    /// Contracts fetched and decompiled at this contract's hard-coded call targets, one level
    /// deep, when following links over RPC. Each is taken as found: a target that is itself a
    /// proxy appears as its stub, and the JSON output carries the contracts without reports.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub linked: Vec<Contract>,
    /// Filled when the contract was fetched by address.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub address: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    /// Chain the contract was fetched from, when fetched by address.
    pub chain: Option<String>,
    /// Implementation behind this proxy, when resolved on-chain.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proxy: Option<ProxyRef>,
    /// Internal helpers that copy a storage string to memory: entry pc -> slot.
    #[serde(skip)]
    pub string_loaders: HashMap<usize, U256>,
    /// The code units this contract is assembled from, when it is a composite ([`compose`]):
    /// index 0 is the contract's own code (the proxy or diamond shell), the rest the
    /// implementation or facets whose code runs in its storage through `DELEGATECALL`.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub parts: Vec<Part>,
    /// How the composite was assembled, when it is one.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub composite: Option<Composite>,
    /// The selector-keyed storage lookup the fallback delegatecalls through, when the code is
    /// an EIP-2535 diamond shell.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub diamond_lookup: Option<DiamondLookup>,
}

/// Where a diamond shell keeps its selector-to-facet mapping.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize)]
pub struct DiamondLookup {
    /// Root slot of the `mapping(bytes4 => ...)`, as 32-byte hex.
    pub slot: String,
    /// Slots past the mapping entry at which the facet address sits (0 for a plain mapping or
    /// a struct whose first member is the address).
    pub offset: u64,
}

/// A storage read whose key is a mapping entry under the call's own selector: the facet lookup
/// of a diamond shell. Returns the mapping's root and the struct offset of the entry read.
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

/// Nodes visited when looking for the selector under a mapping key; a key is a small
/// expression, so a larger one is not a selector lookup.
const SELECTOR_SEARCH_LIMIT: usize = 2_000;

/// Does `e` derive from the first calldata word, which holds the selector?
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

/// One code unit of a composite contract.
#[derive(Clone, Debug, Serialize)]
pub struct Part {
    /// What the unit is to the contract.
    pub role: PartRole,
    /// The unit's address.
    pub address: String,
    /// Selectors the shell routes to this unit, as `0x`-prefixed 4-byte hex. Empty for the
    /// shell and for an implementation that receives every call the shell does not answer.
    pub selectors: Vec<String>,
    /// Offset added to every pc of this unit so pcs are unique across the composite.
    #[serde(skip)]
    pub base: usize,
    /// The unit's runtime code, which the executor runs in the composite's storage.
    #[serde(skip)]
    pub runtime: Vec<u8>,
    /// Compiler of the unit, as the header prints it.
    pub compiler: String,
    /// The unit's own storage layout.
    pub storage: Vec<StorageVar>,
    /// The unit's own decompiled source.
    pub source: String,
    /// Size and coverage of the unit.
    pub stats: Stats,
}

/// The role of a part in a composite.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum PartRole {
    /// The contract's own code: the proxy or diamond shell that routes calls.
    Shell,
    /// The single implementation a proxy forwards to.
    Implementation,
    /// One facet of a diamond.
    Facet,
}

/// How a composite was assembled.
#[derive(Clone, Debug, Serialize)]
pub struct Composite {
    /// The routing pattern, e.g. `EIP-1967 proxy` or `EIP-2535 diamond`.
    pub kind: String,
    /// Admin address, for patterns that have one.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub admin: Option<String>,
    /// Storage slots two parts declare with incompatible types (see [`StorageCollision`]).
    pub collisions: Vec<StorageCollision>,
    /// Routed selectors the shell answers itself as well, so the shell wins.
    pub shadowed: Vec<String>,
}

/// Two parts declaring the same storage slot with different types.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct StorageCollision {
    /// The slot.
    pub slot: String,
    /// The first part and the type it uses.
    pub first: (usize, String),
    /// The second part and the type it uses.
    pub second: (usize, String),
}

impl Contract {
    /// The runtime code that holds `f`: its part's code in a composite, else the contract's.
    #[must_use]
    pub fn code_of(&self, f: &Function) -> &[u8] {
        match self.parts.get(f.part) {
            Some(p) => &p.runtime,
            None => &self.info.runtime,
        }
    }

    /// The pc offset of the part that holds `f` (0 outside a composite).
    #[must_use]
    pub fn base_of(&self, f: &Function) -> usize {
        self.parts.get(f.part).map_or(0, |p| p.base)
    }

    /// The pc `pc` of `f` as an offset into the part's own code.
    #[must_use]
    pub fn local_pc(&self, f: &Function, pc: usize) -> usize {
        pc.saturating_sub(self.base_of(f))
    }
}

/// Distance between the pc ranges of consecutive parts; EVM code is below 2^15 bytes.
pub const PART_STRIDE: usize = 1 << 24;

impl Contract {
    /// Add `base` to every program counter so this contract's functions can sit next to
    /// another's without colliding: function entries, callee lists, lifted node pcs, internal
    /// call targets, string loaders and the type environment's scopes.
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

/// A code unit to compose with a shell.
#[derive(Debug)]
pub struct PartInput {
    /// What the unit is to the contract.
    pub role: PartRole,
    /// The unit's address.
    pub address: String,
    /// Selectors the shell routes to it; empty for an implementation that receives every
    /// selector the shell does not answer.
    pub selectors: Vec<String>,
    /// The unit's own decompilation.
    pub contract: Contract,
}

/// Assemble a proxy or diamond and the code it forwards to into one contract: the shell's
/// functions, every routed function of every other part and the parts' internal helpers in one
/// list, their storage layouts and type environments merged, so the analyzer sees the contract
/// users call rather than its pieces.
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
    // Which part first declared each slot, for naming both sides of a collision.
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
        for v in part.call_targets {
            if !shell.call_targets.contains(&v) && !v.eq_ignore_ascii_case(&address) {
                shell.call_targets.push(v);
            }
        }
        // The part's code calls through slots of the shell's storage.
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

/// Do two type families agree wherever both say something? `*` matches anything at its level,
/// so `mapping(address => *)` agrees with `mapping(address => uint)` but not with `address`.
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

/// A storage type with its widths erased, for the collision check: two parts that read the
/// same mapping as `uint16` and `uint256` values agree on its shape, while `address` against
/// `mapping(...)` or `bool` against `address` do not. A full word (`uint256`, `bytes32`, an
/// unknown type) says nothing about the shape and becomes `*`, which never collides.
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
/// The implementation a proxy contract forwards to.
pub struct ProxyRef {
    /// Human-readable pattern name, e.g. `EIP-1967 proxy` or `EIP-1167 minimal proxy`.
    pub kind: String,
    /// Implementation address.
    pub implementation: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    /// Admin address, for patterns that have one.
    pub admin: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    /// The implementation's own decompilation, when its code was fetched.
    pub contract: Option<Box<Contract>>,
}

/// Decompile a bytecode blob: runtime code, or creation code with its constructor.
///
/// Creation code yields the runtime contract with `constructor` filled in; the rendered source of
/// the whole thing lands in `Contract::source`.
pub fn decompile(code: &[u8], opts: &Options) -> Contract {
    let t0 = std::time::Instant::now();
    // No code (an account without a contract) decompiles as a contract that only stops.
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

/// Decompile one code body (`info` says how it sits in the input) into a [`Contract`].
///
/// Recovers the control flow, lifts internal functions, the dispatcher and orphans, infers
/// signatures and the storage layout, then renders every function. Embedded creation code is
/// treated as data unless `opts.embedded` is set.
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
    // Embedded creation code (CODECOPY'd into memory and fed to CREATE/CREATE2) is data for the
    // purposes of this contract: it is excluded from coverage and decompiled separately on request.
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
            // Unresolved jumps are those of the surviving units only.
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
    // Computed jumps (hand-written dispatchers): derive candidate targets from the target
    // expression's shape and recover again with them.
    if !rec.unresolved_jumps.is_empty() {
        let oracle = Lifter {
            prog: &prog,
            root: false,
            summaries: HashMap::new(),
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
        // Without a metadata trailer the end of the code is unknown: a trailing region that is
        // reached by nothing and whose JUMPDESTs are referenced by no PUSH in reached code is data
        // (Vyper constants, embedded payloads), not code.
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
    // Internal function units first: simple ones (ABI decoders/encoders, getters) are summarised
    // and seen through at their call sites.
    let mut int_lifter = Lifter {
        prog: &prog,
        root: false,
        summaries: HashMap::new(),
        oracle: false,
        copy_loops: Default::default(),
    };
    let mut internals: BTreeMap<usize, Lifted> = BTreeMap::new();
    let mut by_block: Vec<(usize, Lifted)> = Vec::new();
    // Callees before callers where possible: iterate until the summary set stabilises.
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
        let same = sums.len() == int_lifter.summaries.len()
            && sums.keys().all(|k| int_lifter.summaries.contains_key(k));
        int_lifter.summaries = sums;
        if same {
            break;
        }
    }
    for (b, l) in by_block {
        internals.insert(prog.blocks[b].start, l);
    }
    tick("lift internals", &mut tt);
    // Helpers that load a storage string: their result prints as the storage variable.
    let loaders: HashMap<usize, U256> = internals
        .iter()
        .filter_map(|(pc, l)| crate::idiom::storage_string_loader(l).map(|k| (*pc, k)))
        .collect();
    let lifter = Lifter {
        prog: &prog,
        root: true,
        summaries: int_lifter.summaries.clone(),
        oracle: false,
        copy_loops: Default::default(),
    };
    let main = lifter.lift_summarizing(&rec.main, None);
    let dispatch = function::discover(&main);
    let contract_nonpayable = function::dispatcher_nonpayable(&main, &dispatch.dispatcher);
    tick("lift main", &mut tt);
    let mut orphans: BTreeMap<usize, Lifted> = BTreeMap::new();
    for (b, unit) in &rec.orphans {
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

    // Effects of internal functions (transitive).
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

    // Leak the internal graphs for the lifetime of this analysis so the resolver can hand out
    // `&'static` references (the decompiler is a one-shot process per contract).
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

    // Each external function is lifted again on its own from the state the dispatcher hands it,
    // so that code shared between functions (ABI-encoding tails, reverts) is specialised per
    // function instead of merged across all of them.
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
        // No dispatcher at all: the whole runtime is one entry (e.g. a hand-written contract).
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

    // Internal helpers that no printed statement calls any more (every call site was inlined or
    // aliased) are kept for the JSON but not printed.
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
        // A "helper" whose entry block every caller also holds as a plain node of its own is
        // the continuation of those callers (old solc reaches the rest of a modified function
        // both by falling through and by a jump with a return address): its body is already
        // printed inline, so the duplicate definition is not.
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

    // Types: follow values through phis, helpers and storage to fill in what the direct
    // heuristics leave at `uint256`.
    let env = {
        let units: Vec<(usize, &Lifted)> = functions
            .iter()
            .filter_map(|f| f.lifted.as_ref().map(|l| (f.pc, l)))
            .collect();
        types::solve(&units, layout)
    };
    refine_types(&mut functions, &env);
    tick("types", &mut tt);

    // Inventories.
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
    name_storage_from_getters(&functions, &mut storage);
    for st in scan_strings(code, code_end, &embedded_ranges) {
        if !strings.iter().any(|x| x.contains(&st)) {
            strings.push(st);
        }
    }
    strings.sort();
    strings.dedup();
    // Pieces of a longer string (32-byte halves of a revert reason) are not strings of their own.
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
    // Render code for each function.
    let pure_callees: HashSet<usize> = functions
        .iter()
        .filter(|f| {
            f.kind == FnKind::Internal
                && matches!(f.mutability, Mutability::View | Mutability::Pure)
        })
        .map(|f| f.pc)
        .collect();
    let callee_returns: HashMap<usize, Vec<String>> = functions
        .iter()
        .filter(|f| f.kind == FnKind::Internal)
        .map(|f| (f.pc, f.returns.clone()))
        .collect();
    let array_resizers: HashSet<usize> = functions
        .iter()
        .filter(|f| f.kind == FnKind::Internal && f.lifted.as_ref().is_some_and(is_array_resizer))
        .map(|f| f.pc)
        .collect();
    for f in functions.iter_mut() {
        let mut names = make_names(f, &storage, layout, &loaders, &callee_returns);
        names.hide_checked = solc08;
        names.pure_callees = pure_callees.clone();
        names.array_resizers = array_resizers.clone();
        let l = f
            .lifted
            .as_ref()
            .expect("functions are lifted before they are printed");
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
                embedded.push(sc);
            }
        }
    }

    // Delegatecall targets (proxy resolution).
    let mut dc_slots: Vec<String> = Vec::new();
    let mut dc_targets: Vec<String> = Vec::new();
    let mut call_targets: Vec<String> = Vec::new();
    let mut call_target_slots: Vec<String> = Vec::new();
    let mut diamond_lookup: Option<DiamondLookup> = None;
    for f in &functions {
        let Some(l) = &f.lifted else { continue };
        for nd in &l.nodes {
            for st in &nd.stmts {
                if let Stmt::Call { kind, addr, .. } = st {
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
                            let h = c.to_hex_padded(20);
                            if !dc_targets.contains(&h) {
                                dc_targets.push(h);
                            }
                        }
                        // A literal address called with CALL/STATICCALL/CALLCODE: a hard-coded
                        // dependency. Precompiles (0x01 through 0x11 as of Prague) and the zero
                        // address are not contracts to link.
                        Node::Const(c)
                            if matches!(*kind, op::CALL | op::STATICCALL | op::CALLCODE) =>
                        {
                            let low = c & expr::mask_bits(160);
                            let is_precompile =
                                low.fits_u64() && (1..=0x11).contains(&low.low_u64());
                            if !low.is_zero() && !is_precompile {
                                let h = low.to_hex_padded(20);
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
        constructor: None,
        delegatecall_slots: dc_slots,
        delegatecall_targets: dc_targets,
        call_targets,
        call_target_slots,
        stored_targets: Vec::new(),
        linked: Vec::new(),
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
                        if let (Some(off), Some(len)) = (
                            st[l - 2].and_then(|v| v.as_usize()),
                            st[l - 3].and_then(|v| v.as_usize()),
                        ) {
                            if len >= 64
                                && off + len <= prog.code.len()
                                && off > b.end
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

/// Element value types of mappings and dynamic arrays, from how their entries are written and
/// read: an entry written as `| 1` / `& ~0xff` and read through an 8-bit mask is a `bool`, one
/// written or read through a 160-bit mask an `address`, a narrower one `uintN`.
fn element_types(functions: &[Function]) -> HashMap<U256, String> {
    /// What the accesses to one root's entries show. Writes decide when there are any: a read
    /// mask may be ABI packing (`uint32(x)` of an address straddling two payload words), a
    /// write mask never is.
    #[derive(Default)]
    struct Accesses {
        write_widths: BTreeSet<u32>,
        /// Constants written as bool-sized values (0 or 1).
        flags: Vec<U256>,
        /// Some write was neither 0 nor 1.
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
                    // The 4-byte tail of a payload is a bare mask of its last value.
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

/// Element type of an array or mapping type string (`address[]` -> `address`,
/// `mapping(address => bool)` -> `bool`), when it is a concrete value type.
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

/// The compiler's array-resize helper: `old = sload(slot); sstore(slot, n);` then, when the
/// array shrinks, the dropped elements are zeroed. Two parameters, the slot and the new length,
/// the slot stored to directly.
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
                // Larger shrinks zero the dropped elements in a loop the compiler outlines.
                Stmt::Internal { .. } => clears = true,
                Stmt::Call { .. } | Stmt::Log { .. } | Stmt::Create { .. } => return false,
                _ => {}
            }
        }
    }
    k == 2 && stores_arg_to_arg && clears
}

/// A public getter whose signature is known names the variable it returns: a function that only
/// reads one slot (or one packed field, or one mapping entry keyed by its parameter) and returns
/// it gives that slot its name.
fn name_storage_from_getters(functions: &[Function], storage: &mut [StorageVar]) {
    let mut taken: HashSet<String> = storage.iter().map(|s| s.name.clone()).collect();
    for f in functions {
        let (FnKind::External, Some(sig), Some(l)) = (f.kind, &f.signature, &f.lifted) else {
            continue;
        };
        // `getSwapFee()` names the variable `swapFee`.
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
        // Strip a bool test (`x != 0`) and a type mask.
        let mut word = *word;
        if let Node::Op(op::ISZERO, v) = expr::node(word) {
            if let Node::Op(op::ISZERO, w) = expr::node(v[0]) {
                word = w[0];
            }
        }
        let word = match expr::node(word) {
            Node::Op(op::AND, v) if expr::as_const(v[1]).is_some_and(|m| m.is_low_mask()) => v[0],
            Node::Op(op::AND, v) if expr::as_const(v[0]).is_some_and(|m| m.is_low_mask()) => v[1],
            _ => word,
        };
        let field = emit::packed_read(word);
        let root: Option<U256> = match (field, expr::node(word)) {
            (Some((k, _, _)), _) => Some(k),
            (None, Node::SLoad(key, false, _)) => match expr::node(key) {
                Node::Const(k) => emit::hashed_slot(k).map(|(s, _)| s).or(Some(k)),
                // A mapping entry or array element: the root slot of the key.
                _ => emit::element_root(key),
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
                // A getter of the bare slot of an array returns its length, not the array.
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

/// Naming context for printing `f`: parameters, internal-unit arguments, storage variables and
/// packed fields, aliases for the results of storage-string loaders, and the helper results
/// known to be booleans (`callee_returns` maps a helper's entry pc to its return types).
pub fn make_names(
    f: &Function,
    storage: &[StorageVar],
    layout: MappingLayout,
    loaders: &HashMap<usize, U256>,
    callee_returns: &HashMap<usize, Vec<String>>,
) -> Names {
    let mut n = Names {
        layout,
        ..Default::default()
    };
    if f.kind != FnKind::Internal {
        for p in &f.params {
            n.params.insert(p.index, p.name.clone());
        }
    }
    n.bool_returns = f.returns.iter().map(|t| t == "bool").collect();
    n.bools.extend(f.bool_vars.iter().map(|v| expr::var(*v)));
    // Call results are numbered by the order of their calls in the function, the same for every
    // reader of these names (the printer and the analyzer's evidence lines).
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
        // Internal units: Arg(i) below the return slot k are the parameters, last pushed on top.
        let k = l.ret_slot.map(|k| k as usize).unwrap_or(l.n_args);
        for i in 0..l.n_args.max(k + 1) {
            let name = if i < k {
                format!("arg{}", k - 1 - i)
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
                    if let Some(tys) = callee_returns.get(callee) {
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

/// Fill in the types the direct heuristics left at `uint256` from the solved environment:
/// calldata parameters, return words, internal parameters and results, and the phi variables
/// that are booleans.
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

/// Calldata parameters: the solver sees the same decoder masks as the direct inference plus
/// every use of the word, so it decides integer widths and `address`; the direct inference still
/// decides dynamic types and the words decoded in helpers it sees through.
fn refine_params(pc: usize, params: &mut [Param], env: &TypeEnv) {
    for p in params.iter_mut() {
        if p.ty == "address" || p.ty.starts_with("uint") {
            if let Some(t) = env.param_type(pc, p.index) {
                p.ty = t;
            }
        } else if p.ty == "bool" && env.param_is_numeric(pc, p.index) {
            // `x != 0` on a word that helpers further down do arithmetic on.
            p.ty = env
                .param_type(pc, p.index)
                .unwrap_or_else(|| "uint256".to_string());
        }
    }
}

/// Return words of an external function: every `return` must agree on the shape for a position
/// to be typed.
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
    if rets.is_empty() || rets.iter().any(|w| w.len() != returns.len()) {
        return;
    }
    for (i, ty) in returns.iter_mut().enumerate() {
        if ty != "uint256" {
            continue;
        }
        let t = rets
            .iter()
            .fold(types::Ty::Unknown, |t, w| t.join(env.type_of(w[i], pc)));
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

/// Parameters of an internal unit: the direct address heuristic first, the solver otherwise.
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

/// Results of an internal unit: declaration position `i` is result `n - 1 - i` (deepest first).
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

/// The phi variables of a function the solver found to be booleans.
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

/// Replace the `uint256` leaves and keys of the storage declarations by what the solver found
/// for the corresponding element and key shapes.
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

/// Packed storage fields: slot -> (byte offset, bits) -> constant values written (for typing).
type PackedFields = BTreeMap<U256, BTreeMap<(u32, u32), Vec<Option<U256>>>>;

/// What a contract's functions reference, collected for the contract header.
struct Inventories {
    storage: Vec<StorageVar>,
    /// Event declarations (`Name(type indexed name, …)` or the raw topic).
    events: Vec<String>,
    /// Custom error declarations.
    errors: Vec<String>,
    /// String constants the code reverts with or stores.
    strings: Vec<String>,
    /// `0xselector signature` of the external functions the contract calls.
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
    // Packed fields: slot -> (offset, bits) -> constant values written (for bool typing).
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
                                    // Unknown signature: named by the hash's first four bytes, with
                                    // one indexed parameter per extra topic and one per data word.
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
            // Init code of a deployed contract is bytes, not this contract's string constants.
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
                // Prefer the most specific.
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
                // The element type the accesses show (`bool` flags, `address` entries).
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
            // A slot is packed when a field starts past byte 0 or several fields share it.
            let mut fs: Vec<StorageField> = Vec::new();
            // (a string slot is read with `& 1` and `>> 8`, which is its length encoding, not packing)
            if let (Some(acc), false) = (fields.get(&slot), string_slots.contains(&slot)) {
                let keys: Vec<(u32, u32)> = acc
                    .keys()
                    .copied()
                    .filter(|(off, bits)| *bits < 256 && off * 8 + bits <= 256)
                    .collect();
                let packed = keys.iter().any(|(off, _)| *off > 0) || keys.len() > 1;
                if packed {
                    // Drop a field that is the union of others (`slot >> 8` read as one word over two fields).
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

/// `Transfer(address,address,uint256)` with 2 topics besides the signature becomes
/// `Transfer(address indexed, address indexed, uint256)`. Solidity emits indexed parameters as
/// topics in declaration order and they are conventionally declared first, so the first `n`
/// parameters are marked.
fn with_indexed(sig: &str, n: usize) -> String {
    let Some(open) = sig.find('(') else {
        return sig.to_string();
    };
    let name = &sig[..open];
    let inner = sig[open + 1..].trim_end_matches(')');
    if inner.is_empty() || n == 0 {
        return sig.to_string();
    }
    // Split on top-level commas (tuple types contain nested commas).
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

/// First slots of fixed-size arrays: constants `c` in keys of the form `index + c` where the
/// index is neither constant nor hashed. Nearby constants (`index + 3` for an array at 2, from
/// `owners[n + 1]`) fold onto the lowest one of their cluster.
fn fixed_array_bases(functions: &[Function]) -> BTreeSet<U256> {
    let mut seen: BTreeSet<U256> = BTreeSet::new();
    // (key, index expressions bounded by `index < N` in the same function)
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
    // Only an index the function bounds (`require(i < 256)`) marks a fixed-size array; a bare
    // `p + 1` is as often a pointer into a dynamic array's data.
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
    // Cluster: a constant within 16 of a lower one is an offset into that array.
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

/// Root slot of a storage key and the shape of the variable it implies.
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
            let kt = function::type_of_value(k);
            let kt = if kt == "uint256" {
                "uint256".to_string()
            } else {
                kt
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
            // `keccak256(slot) + i` with the hash precomputed by the compiler.
            for (a, _) in [(v[0], v[1]), (v[1], v[0])] {
                if let Some((s, _)) = expr::as_const(a).and_then(emit::hashed_slot) {
                    return (Some(s), Some("uint256[]".into()));
                }
            }
            // `index + c` into a fixed-size array at a known base.
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

/// Packed-field reads anywhere in `e` (see `emit::packed_read`).
fn collect_fields(root: lift::Root, fields: &mut PackedFields) {
    let mut seen = HashSet::new();
    let mut stack = vec![root.expr];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 50_000 {
            continue;
        }
        // The 4-byte tail of a payload is a bare mask of its last value, not a field read.
        if x == root.expr && root.payload {
            stack.extend(expr::children(x));
            continue;
        }
        if let Some((k, off, bits)) = emit::packed_read(x) {
            if off > 0 || bits < 256 {
                let entry = fields.entry(k).or_default().entry((off, bits)).or_default();
                if matches!(expr::node(x), Node::Op(op::SIGNEXTEND, _)) {
                    // Marker for a signed field (never a written constant otherwise).
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

/// Printable ASCII runs in the code's data area (strings longer than 32 bytes are stored as data
/// and loaded with CODECOPY by older compilers).
/// Printable `PUSH` immediates (string constants a compiler placed in code), whole immediates
/// only, so that fragments straddling instruction boundaries are not reported.
/// `skip` lists embedded code regions as `(offset, length)`.
fn scan_strings(code: &[u8], code_end: usize, skip: &[(usize, usize)]) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let end = code_end.min(code.len());
    // A string longer than 32 bytes is pushed in 32-byte pieces a few instructions apart: a
    // full printable PUSH32 is held back and joined with the piece that follows it.
    let mut pending: Option<(String, usize)> = None;
    let insns = crate::disasm::disassemble(&code[..end]);
    for (idx, insn) in insns.iter().enumerate() {
        // Embedded creation code (and its metadata) is data here, not this contract's strings.
        if skip.iter().any(|(o, l)| insn.pc >= *o && insn.pc < *o + *l) {
            continue;
        }
        let Some(imm) = insn.imm else { continue };
        let mut size = insn.opcode as usize - 0x5f;
        // `PUSHn x; PUSH1 k; SHL`: the optimizer's form of a left-aligned short piece.
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
    // One entry per string: no duplicates, and no 32-byte piece of a longer string that was
    // also joined.
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
        // Left-aligned ASCII (string constants are stored left-aligned).
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

/// Render the whole contract as pseudo-Solidity.
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
    out.push_str(&format!("\ncontract {} {{\n", name));
    if !c.storage.is_empty() {
        out.push_str("    // ---- storage layout ----\n");
        for s in &c.storage {
            if s.fields.is_empty() {
                out.push_str(&format!(
                    "    {} {}; // slot {}, {}{} reads, {} writes\n",
                    s.ty,
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

/// The banner that opens the functions of part `index` in a composite's source.
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

/// The header comment of a composite: what it is and which parts it was assembled from.
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

/// The `function …(…) … {` line of a function, preceded by its selector comment.
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
            // `refine_types` fills the parameters of every lifted internal unit.
            let params: Vec<String> = (0..f.n_args)
                .map(|i| {
                    let ty = f.params.get(i).map_or("uint256", |p| p.ty.as_str());
                    format!("{} arg{}", ty, i)
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
