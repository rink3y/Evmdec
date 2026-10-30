//! Compiler profile: which compiler produced the code, its version (exact or bounded) and the
//! code-generation features that follow from it.
//!
//! The metadata trailer gives the exact version when present. Without it, or to cross-check it,
//! the bytecode itself carries fingerprints: each compiler release introduced idioms (the
//! `Panic(uint256)` revert, the `0x80` free-memory pointer, the calldata head-size checks,
//! `PUSH0`) that bound the version from below or above. Later passes ask the profile rather than
//! the metadata, so a stripped contract is still printed and judged by the compiler that made it.

use crate::disasm::{self, Instruction};
use crate::emit::{MappingLayout, SEL_ERROR, SEL_PANIC};
use crate::expr;
use crate::metadata::Metadata;
use crate::opcode as op;
use crate::u256::U256;
use serde::Serialize;
use std::fmt;

/// Compiler family.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Kind {
    /// Solidity (`solc`).
    Solc,
    /// Vyper.
    Vyper,
    /// Neither recognised: hand-written, another compiler, or too little code to tell.
    #[default]
    Unknown,
}

/// A compiler release.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct Version {
    /// Major version.
    pub major: u32,
    /// Minor version.
    pub minor: u32,
    /// Patch version.
    pub patch: u32,
}

impl Version {
    /// `major.minor.patch`.
    pub const fn new(major: u32, minor: u32, patch: u32) -> Version {
        Version {
            major,
            minor,
            patch,
        }
    }
}

impl From<(u32, u32, u32)> for Version {
    fn from((major, minor, patch): (u32, u32, u32)) -> Version {
        Version::new(major, minor, patch)
    }
}

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)
    }
}

/// What is known about the compiler that produced a code body.
#[derive(Clone, Debug, Default, PartialEq, Serialize)]
pub struct Profile {
    /// Compiler family.
    pub kind: Kind,
    /// Exact version, from the metadata trailer.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub version: Option<Version>,
    /// Lowest version consistent with the fingerprints (inclusive).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub at_least: Option<Version>,
    /// Lowest version ruled out by the fingerprints (exclusive upper bound).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub below: Option<Version>,
    /// The code carries a metadata trailer.
    pub metadata: bool,
    /// The compiler emits overflow, division-by-zero and similar checks itself
    /// (solc >= 0.8, every Vyper).
    pub checked_arithmetic: bool,
    /// Reverts with `Panic(uint256)` for the compiler's own assertions (solc >= 0.8).
    pub panic_errors: bool,
    /// Reverts with `Error(string)` for `require` reasons (solc >= 0.4.22).
    pub error_strings: bool,
    /// The ABI decoder checks `calldatasize` against the head size before reading parameters
    /// (solc >= 0.5).
    pub abi_size_checks: bool,
    /// The ABI decoder validates `address` and `bool` parameters by masking and comparing
    /// (solc >= 0.5).
    pub abi_validation: bool,
    /// `PUSH0` is used (solc >= 0.8.20 targeting Shanghai or later).
    pub push0: bool,
    /// Compiled through the Yul IR pipeline (`via-ir`), recognised from its prologue.
    pub via_ir: bool,
    /// Initial value of the free-memory pointer written by the prologue (`0x80` since solc
    /// 0.4.22, `0x60` before), when a prologue was found.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub free_memory_pointer: Option<u64>,
    /// Mapping slot layout of this compiler family.
    #[serde(skip)]
    pub layout: MappingLayout,
    /// Fingerprints found in the code, for the report.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub evidence: Vec<String>,
}

impl Profile {
    /// Does the profile establish that the version is at least `v`?
    pub fn is_at_least(&self, v: Version) -> bool {
        match (self.version, self.at_least) {
            (Some(x), _) => x >= v,
            (None, Some(lo)) => lo >= v,
            (None, None) => false,
        }
    }

    /// Does the profile establish that the version is below `v`?
    pub fn is_below(&self, v: Version) -> bool {
        match (self.version, self.below) {
            (Some(x), _) => x < v,
            (None, Some(hi)) => hi <= v,
            (None, None) => false,
        }
    }

    /// The version to judge compiler-dependent behaviour by: the exact one, else the lower
    /// bound the fingerprints establish.
    pub fn effective_version(&self) -> Option<Version> {
        self.version.or(self.at_least)
    }

    /// The version range the fingerprints establish (`>= 0.8.0, < 0.8.20`), when the exact
    /// version is unknown and some bound is.
    pub fn bounds(&self) -> Option<String> {
        if self.version.is_some() {
            return None;
        }
        let mut parts = Vec::new();
        if let Some(lo) = self.at_least {
            parts.push(format!(">= {}", lo));
        }
        if let Some(hi) = self.below {
            parts.push(format!("< {}", hi));
        }
        (!parts.is_empty()).then(|| parts.join(", "))
    }
}

/// `solc 0.8.19`, `solc >= 0.8.0, < 0.8.20 (no metadata)`, `vyper < 0.3.10 (no metadata)`.
impl fmt::Display for Profile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self.kind {
            Kind::Solc => "solc",
            Kind::Vyper => "vyper",
            Kind::Unknown => return write!(f, "unknown"),
        };
        if let Some(v) = self.version {
            return write!(f, "{} {}", name, v);
        }
        let suffix = if self.metadata {
            "version not in metadata"
        } else {
            "no metadata"
        };
        match self.bounds() {
            Some(b) => write!(f, "{} {} ({})", name, b, suffix),
            None => write!(f, "{} (unknown version, {})", name, suffix),
        }
    }
}

/// Fingerprints read from one code body.
#[derive(Default)]
struct Fingerprints {
    /// `Panic(uint256)` selector pushed somewhere.
    panic: bool,
    /// `Error(string)` selector pushed somewhere.
    error_string: bool,
    /// `PUSH0` used.
    push0: bool,
    /// Shift instructions used.
    shifts: bool,
    /// Initial free-memory pointer written by the prologue.
    free_pointer: Option<u64>,
    /// `calldatasize - 4 < n` / `calldatasize < 4 + n` head-size checks.
    head_checks: bool,
    /// `AND 0xff..ff (160 bits)` applied to a `CALLDATALOAD` then compared `EQ`: the >= 0.5
    /// decoder validator.
    validators: bool,
    /// `PUSH1 3|4 CALLDATASIZE` at the entry: Vyper's dispatcher.
    vyper_prologue: bool,
    /// `PUSH1 0x80 PUSH1 0x40 MSTORE` (or the via-IR variant) at the entry.
    solc_prologue: bool,
    /// The prologue duplicates the pointer before storing it: the Yul pipeline.
    via_ir: bool,
    /// Selector read as `calldataload(0) / 2^224` (pre-shift compilers).
    div_selector: bool,
}

/// Instructions looked back over for a multi-instruction idiom.
const WINDOW: usize = 5;

fn fingerprint(code: &[u8]) -> Fingerprints {
    let insns = disasm::disassemble(code);
    let mut p = Fingerprints::default();
    prologue(&insns, &mut p);
    let mask160 = expr::mask_bits(160);
    let two224 = U256::ONE << 224;
    for (i, insn) in insns.iter().enumerate() {
        let window = &insns[i.saturating_sub(WINDOW)..i];
        match insn.opcode {
            op::PUSH0 => p.push0 = true,
            op::SHR | op::SHL | op::SAR => p.shifts = true,
            op::SLT | op::LT if is_head_check(window) => p.head_checks = true,
            op::EQ if is_validator(window, mask160) => p.validators = true,
            op::DIV if window.iter().rev().take(3).any(|x| x.imm == Some(two224)) => {
                p.div_selector = true;
            }
            op::PUSH4 | op::PUSH32 => {
                if let Some(v) = insn.imm {
                    let sel = if insn.opcode == op::PUSH4 {
                        v.low_u64()
                    } else {
                        (v >> 224).low_u64()
                    };
                    if sel == SEL_PANIC as u64 {
                        p.panic = true;
                    } else if sel == SEL_ERROR as u64 {
                        p.error_string = true;
                    }
                }
            }
            _ => {}
        }
    }
    p
}

/// Legacy codegen opens with `PUSH1 0x80 PUSH1 0x40 MSTORE`; the Yul pipeline (via-IR)
/// duplicates the pointer first: `PUSH1 0x40 PUSH1 0x80 DUP2 MSTORE`. Vyper opens with
/// `PUSH1 4 CALLDATASIZE LT` (or `PUSH1 3 ... GT`).
fn prologue(insns: &[Instruction], p: &mut Fingerprints) {
    let head = &insns[..insns.len().min(6)];
    if let Some(ms) = head.iter().position(|x| x.opcode == op::MSTORE) {
        let pushes: Vec<u64> = head[..ms]
            .iter()
            .filter(|x| x.opcode == op::PUSH1)
            .filter_map(|x| x.imm.map(|v| v.low_u64()))
            .collect();
        let dups = head[..ms]
            .iter()
            .any(|x| (op::DUP1..=op::DUP16).contains(&x.opcode));
        if pushes.len() == 2 && pushes.contains(&0x40) && ms <= 4 {
            p.solc_prologue = true;
            p.via_ir = dups;
            p.free_pointer = pushes.iter().copied().find(|v| *v != 0x40);
        }
    }
    if insns.len() > 2
        && insns[0].opcode == op::PUSH1
        && insns[0].imm.is_some_and(|v| matches!(v.low_u64(), 3 | 4))
        && insns[1].opcode == op::CALLDATASIZE
    {
        p.vyper_prologue = true;
    }
}

/// `calldatasize PUSH 4 ... sub PUSH n slt` or `PUSH n calldatasize lt`.
fn is_head_check(window: &[Instruction]) -> bool {
    window.iter().any(|x| x.opcode == op::CALLDATASIZE)
        && window
            .iter()
            .any(|x| x.opcode == op::PUSH1 && x.imm.is_some_and(|v| v.low_u64() == 4))
        && window.iter().any(|x| x.opcode == op::SUB)
        && window.iter().any(|x| {
            x.is_push()
                && x.imm
                    .is_some_and(|v| v.low_u64() >= 32 && v.low_u64().is_multiple_of(32))
        })
}

/// `calldataload dup1 PUSH mask and eq` validates an address parameter.
fn is_validator(window: &[Instruction], mask160: U256) -> bool {
    window
        .iter()
        .any(|x| x.opcode == op::CALLDATALOAD || x.opcode == op::DUP1)
        && window.iter().any(|x| x.imm == Some(mask160))
        && window.iter().any(|x| x.opcode == op::AND)
}

/// Version bounds accumulated from fingerprints, each with its reason.
#[derive(Default)]
struct Bounds {
    lo: Option<Version>,
    hi: Option<Version>,
    evidence: Vec<String>,
}

impl Bounds {
    /// The compiler is at least `v`.
    fn raise(&mut self, v: Version, why: &str) {
        if self.lo.is_none_or(|l| v > l) {
            self.lo = Some(v);
        }
        self.evidence.push(format!("{} (solc >= {})", why, v));
    }

    /// The compiler is below `v`.
    fn cap(&mut self, v: Version, why: &str) {
        if self.hi.is_none_or(|h| v < h) {
            self.hi = Some(v);
        }
        self.evidence.push(format!("{} (solc < {})", why, v));
    }

    /// Bounds that contradict each other are kept as evidence only.
    fn consistent(&self) -> bool {
        self.lo.zip(self.hi).is_none_or(|(l, h)| l < h)
    }
}

fn detect_kind(md: Option<&Metadata>, p: &Fingerprints) -> Kind {
    match md {
        Some(m) if m.compiler == "vyper" => Kind::Vyper,
        Some(m) if m.compiler == "solc" => Kind::Solc,
        _ if p.vyper_prologue && !p.solc_prologue => Kind::Vyper,
        _ if p.solc_prologue => Kind::Solc,
        _ => Kind::Unknown,
    }
}

/// What the fingerprints say about a solc release.
fn solc_bounds(md: Option<&Metadata>, p: &Fingerprints) -> Bounds {
    let mut b = Bounds::default();
    match p.free_pointer {
        Some(0x80) => b.raise(Version::new(0, 4, 22), "free-memory pointer starts at 0x80"),
        Some(0x60) => b.cap(Version::new(0, 4, 22), "free-memory pointer starts at 0x60"),
        _ => {}
    }
    if p.panic {
        b.raise(Version::new(0, 8, 0), "reverts with Panic(uint256)");
    }
    if p.error_string {
        b.raise(Version::new(0, 4, 22), "reverts with Error(string)");
    }
    if p.push0 {
        b.raise(Version::new(0, 8, 20), "uses PUSH0");
    }
    if p.head_checks {
        b.raise(Version::new(0, 5, 0), "checks the calldata head size");
    }
    if p.validators {
        b.raise(
            Version::new(0, 5, 0),
            "validates address parameters when decoding",
        );
    }
    if p.shifts {
        b.raise(Version::new(0, 5, 5), "uses shift instructions");
    }
    if p.div_selector && !p.shifts {
        b.cap(Version::new(0, 5, 5), "extracts the selector by division");
    }
    if let Some(m) = md {
        if m.implies_pre_0_5_9() {
            b.cap(
                Version::new(0, 5, 9),
                "metadata carries a bzzr0 hash and no version",
            );
        } else if m.version.is_none() && m.bzzr.as_deref().is_some_and(|b| b.starts_with("bzzr1")) {
            b.raise(Version::new(0, 5, 9), "metadata carries a bzzr1 hash");
        }
    }
    b
}

/// Build the profile of `code` (the runtime body, metadata trailer included or not) from its
/// metadata trailer and its fingerprints.
pub fn profile(code: &[u8], md: Option<&Metadata>) -> Profile {
    let body = match md {
        Some(m) if m.offset <= code.len() => &code[..m.offset],
        _ => code,
    };
    let p = fingerprint(body);
    let kind = detect_kind(md, &p);
    let mut prof = Profile {
        kind,
        metadata: md.is_some(),
        version: md.and_then(|m| m.version_tuple()).map(Version::from),
        layout: match kind {
            Kind::Vyper => MappingLayout::Vyper,
            _ => MappingLayout::Solidity,
        },
        panic_errors: p.panic,
        error_strings: p.error_string,
        push0: p.push0,
        via_ir: p.via_ir && kind == Kind::Solc,
        free_memory_pointer: p.free_pointer.filter(|_| kind == Kind::Solc),
        ..Default::default()
    };
    // The `vyper` metadata key appeared in 0.3.10.
    if kind == Kind::Vyper && prof.version.is_none() {
        if md.is_some() {
            prof.at_least = Some(Version::new(0, 3, 10));
        } else {
            prof.below = Some(Version::new(0, 3, 10));
            prof.evidence
                .push("no metadata trailer (vyper < 0.3.10)".into());
        }
    }
    if kind == Kind::Solc {
        let b = solc_bounds(md, &p);
        if prof.version.is_none() && b.consistent() {
            prof.at_least = b.lo;
            prof.below = b.hi;
        }
        prof.evidence.extend(b.evidence);
    }
    if prof.via_ir {
        prof.evidence
            .push("prologue of the Yul IR pipeline (via-ir)".into());
    }
    let solc = kind == Kind::Solc;
    prof.checked_arithmetic = match kind {
        Kind::Vyper => true,
        Kind::Solc => prof.is_at_least(Version::new(0, 8, 0)) || p.panic,
        Kind::Unknown => p.panic,
    };
    prof.abi_size_checks = p.head_checks || (solc && prof.is_at_least(Version::new(0, 5, 0)));
    prof.abi_validation = p.validators || (solc && prof.is_at_least(Version::new(0, 5, 0)));
    prof
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metadata;

    fn fixture(name: &str) -> Vec<u8> {
        let path = format!(
            "{}/../../testdata/mainnet/{}.hex",
            env!("CARGO_MANIFEST_DIR"),
            name
        );
        let text = std::fs::read_to_string(path).expect("fixture present");
        crate::hex::decode(text.trim()).expect("hex fixture")
    }

    #[test]
    fn metadata_gives_the_exact_version() {
        let code = fixture("uni_token");
        let md = metadata::parse_metadata(&code).expect("uni token carries metadata");
        let p = profile(&code, Some(&md));
        assert_eq!(p.kind, Kind::Solc);
        assert_eq!(p.version, md.version_tuple().map(Version::from));
        assert!(p.version.is_some());
        assert!(p.to_string().starts_with("solc 0."));
    }

    #[test]
    fn a_stripped_0_8_contract_is_still_recognised_as_checked() {
        let code = fixture("permit2");
        let md = metadata::parse_metadata(&code).expect("permit2 carries metadata");
        assert!(md.version_tuple().is_some_and(|v| v >= (0, 8, 0)));
        let stripped = &code[..md.offset];
        let p = profile(stripped, None);
        assert_eq!(p.kind, Kind::Solc);
        assert!(p.version.is_none());
        assert!(p.is_at_least(Version::new(0, 8, 0)), "{:?}", p.evidence);
        assert!(p.checked_arithmetic);
        assert!(p.to_string().contains(">= 0.8"), "{}", p);
        assert!(p.via_ir, "permit2 is compiled via-ir: {:?}", p.evidence);
    }

    #[test]
    fn an_old_contract_is_bounded_from_above() {
        // 0x60 free-memory pointer and division-based selector extraction: solc 0.4.
        let code = crate::hex::decode(
            "6060604052600436106100405763ffffffff7c01000000000000000000000000000000000000000000000000000000006000350416631a2b3c4d8114610045575b5bfd",
        )
        .expect("hex");
        let p = profile(&code, None);
        assert_eq!(p.kind, Kind::Solc);
        assert!(p.is_below(Version::new(0, 4, 22)), "{:?}", p);
        assert!(!p.checked_arithmetic);
        assert_eq!(p.free_memory_pointer, Some(0x60));
        assert_eq!(p.bounds().as_deref(), Some("< 0.4.22"));
    }

    #[test]
    fn vyper_without_metadata_is_recognised_by_its_prologue() {
        let code = fixture("curve_3pool_vyper");
        let md = metadata::parse_metadata(&code);
        let p = profile(&code, md.as_ref());
        assert_eq!(p.kind, Kind::Vyper);
        assert!(p.checked_arithmetic);
        assert_eq!(p.layout, MappingLayout::Vyper);
        assert_eq!(p.to_string(), "vyper < 0.3.10 (no metadata)");
    }
}
