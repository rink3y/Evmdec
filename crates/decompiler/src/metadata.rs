//! Compiler metadata (the CBOR trailer solc and vyper append) and creation/runtime splitting.

use crate::disasm;
use crate::hex;
use crate::opcode;
use crate::u256::U256;
use serde::Serialize;

#[derive(Clone, Debug, Default, Serialize, PartialEq)]
pub struct Metadata {
    /// "solc" or "vyper".
    pub compiler: String,
    /// Version as "major.minor.patch" when encoded.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub version: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ipfs: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub bzzr: Option<String>,
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub experimental: bool,
    /// Byte offset where the metadata trailer begins (code ends here).
    pub offset: usize,
    pub length: usize,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub raw_keys: Vec<String>,
}

impl Metadata {
    pub fn version_tuple(&self) -> Option<(u32, u32, u32)> {
        let v = self.version.as_ref()?;
        let mut it = v.split('.').map(|p| p.parse::<u32>().ok());
        Some((it.next()??, it.next()??, it.next()??))
    }
}

#[derive(Clone, Debug)]
enum Cbor {
    UInt(u64),
    NegInt(#[allow(dead_code)] i64),
    Bytes(Vec<u8>),
    Text(String),
    Array(Vec<Cbor>),
    Map(Vec<(Cbor, Cbor)>),
    Bool(bool),
    Null,
    Other,
}

fn cbor_read(data: &[u8], pos: &mut usize, depth: u32) -> Option<Cbor> {
    if depth > 16 || *pos >= data.len() {
        return None;
    }
    let ib = data[*pos];
    *pos += 1;
    let major = ib >> 5;
    let ai = ib & 0x1f;
    let arg: u64 = match ai {
        0..=23 => ai as u64,
        24 => {
            let v = *data.get(*pos)? as u64;
            *pos += 1;
            v
        }
        25 => {
            let v = u16::from_be_bytes([*data.get(*pos)?, *data.get(*pos + 1)?]) as u64;
            *pos += 2;
            v
        }
        26 => {
            let b = data.get(*pos..*pos + 4)?;
            *pos += 4;
            u32::from_be_bytes([b[0], b[1], b[2], b[3]]) as u64
        }
        27 => {
            let b = data.get(*pos..*pos + 8)?;
            *pos += 8;
            u64::from_be_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]])
        }
        _ => return None, // indefinite lengths are not used by compilers
    };
    Some(match major {
        0 => Cbor::UInt(arg),
        1 => Cbor::NegInt(-1 - arg as i64),
        2 => {
            let b = data.get(*pos..*pos + arg as usize)?.to_vec();
            *pos += arg as usize;
            Cbor::Bytes(b)
        }
        3 => {
            let b = data.get(*pos..*pos + arg as usize)?;
            *pos += arg as usize;
            Cbor::Text(String::from_utf8_lossy(b).into_owned())
        }
        4 => {
            let mut v = Vec::new();
            for _ in 0..arg.min(1024) {
                v.push(cbor_read(data, pos, depth + 1)?);
            }
            Cbor::Array(v)
        }
        5 => {
            let mut v = Vec::new();
            for _ in 0..arg.min(1024) {
                let k = cbor_read(data, pos, depth + 1)?;
                let val = cbor_read(data, pos, depth + 1)?;
                v.push((k, val));
            }
            Cbor::Map(v)
        }
        7 => match ai {
            20 => Cbor::Bool(false),
            21 => Cbor::Bool(true),
            22 => Cbor::Null,
            _ => Cbor::Other,
        },
        _ => Cbor::Other,
    })
}

/// Parse the CBOR metadata trailer, if `code` ends with one.
pub fn parse_metadata(code: &[u8]) -> Option<Metadata> {
    if code.len() < 4 {
        return None;
    }
    let n = code.len();
    let len = u16::from_be_bytes([code[n - 2], code[n - 1]]) as usize;
    if len == 0 || len + 2 > n || len > 1024 {
        return None;
    }
    let start = n - 2 - len;
    let blob = &code[start..n - 2];
    let mut pos = 0;
    let Cbor::Map(entries) = cbor_read(blob, &mut pos, 0)? else { return None };
    if pos != blob.len() {
        return None;
    }
    let mut md = Metadata { offset: start, length: len + 2, ..Default::default() };
    let mut recognised = false;
    for (k, v) in entries {
        let Cbor::Text(key) = k else { return None };
        md.raw_keys.push(key.clone());
        match (key.as_str(), v) {
            ("solc", Cbor::Bytes(b)) if b.len() == 3 => {
                md.compiler = "solc".into();
                md.version = Some(format!("{}.{}.{}", b[0], b[1], b[2]));
                recognised = true;
            }
            ("solc", Cbor::Text(t)) => {
                md.compiler = "solc".into();
                md.version = Some(t);
                recognised = true;
            }
            ("vyper", Cbor::Array(a)) => {
                md.compiler = "vyper".into();
                let parts: Vec<String> = a.iter().filter_map(|x| if let Cbor::UInt(n) = x { Some(n.to_string()) } else { None }).collect();
                if parts.len() == 3 {
                    md.version = Some(parts.join("."));
                }
                recognised = true;
            }
            ("ipfs", Cbor::Bytes(b)) => {
                md.ipfs = Some(hex::encode_plain(&b));
                recognised = true;
            }
            (k, Cbor::Bytes(b)) if k.starts_with("bzzr") => {
                md.bzzr = Some(format!("{}:{}", k, hex::encode_plain(&b)));
                recognised = true;
            }
            ("experimental", Cbor::Bool(b)) => md.experimental = b,
            ("integrity", _) | ("runtimeSize", _) | ("dataSizes", _) | ("immutableSize", _) => {
                md.compiler = "vyper".into();
                recognised = true;
            }
            _ => {}
        }
    }
    if !recognised {
        return None;
    }
    if md.compiler.is_empty() {
        md.compiler = "solc".into();
    }
    Some(md)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CodeKind {
    Runtime,
    Creation,
}

#[derive(Clone, Debug, Serialize)]
pub struct BytecodeInfo {
    pub kind: CodeKind,
    /// The runtime code (the input itself for runtime code; the returned region for creation code).
    #[serde(skip)]
    pub runtime: Vec<u8>,
    /// For creation code: the constructor bytecode (prefix before the runtime).
    #[serde(skip)]
    pub constructor: Vec<u8>,
    /// For creation code: ABI-encoded constructor arguments appended after the runtime.
    #[serde(skip)]
    pub constructor_args: Vec<u8>,
    pub runtime_offset: usize,
    pub runtime_len: usize,
    pub constructor_args_len: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub metadata: Option<Metadata>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub constructor_metadata: Option<Metadata>,
}

/// Simulate the constant stack through a straight-line prefix of instructions.
/// Unknown values are `None`. Only PUSH/DUP/SWAP/POP are modelled exactly; every other
/// instruction pops/pushes unknowns.
pub fn constant_stack(insns: &[disasm::Instruction]) -> Vec<Option<U256>> {
    let mut st: Vec<Option<U256>> = Vec::new();
    for i in insns {
        let op = i.opcode;
        if opcode::is_push(op) {
            st.push(i.imm);
        } else if opcode::is_dup(op) {
            let n = (op - 0x7f) as usize;
            let v = if st.len() >= n { st[st.len() - n] } else { None };
            st.push(v);
        } else if opcode::is_swap(op) {
            let n = (op - 0x8f) as usize;
            let l = st.len();
            if l > n {
                st.swap(l - 1, l - 1 - n);
            } else {
                st.clear();
            }
        } else if let Some(info) = opcode::info(op) {
            for _ in 0..info.pops {
                st.pop();
            }
            for _ in 0..info.pushes {
                st.push(None);
            }
        } else {
            st.clear();
        }
    }
    st
}

/// Detect creation code of the shape `... CODECOPY(dest, offset, len) ... RETURN(dest, len)` where the
/// copied region lies after the constructor, and split it.
fn detect_creation(code: &[u8]) -> Option<(usize, usize)> {
    let insns = disasm::disassemble(code);
    // Walk block by block; within each block simulate the constant stack to find CODECOPY args.
    let mut block_start = 0;
    let mut i = 0;
    let mut best: Option<(usize, usize)> = None;
    while i < insns.len() {
        let op = insns[i].opcode;
        if op == opcode::CODECOPY {
            let st = constant_stack(&insns[block_start..i]);
            let l = st.len();
            if l >= 3 {
                if let (Some(dest), Some(offset), Some(len)) = (st[l - 1], st[l - 2], st[l - 3]) {
                    if let (Some(dest), Some(offset), Some(len)) = (dest.as_usize(), offset.as_usize(), len.as_usize()) {
                        // Must copy a region that starts after this CODECOPY and is non-trivial.
                        if offset > insns[i].pc && len >= 1 && offset.checked_add(len).map_or(false, |e| e <= code.len()) {
                            // Look for a RETURN later in the same block (before next terminator) that returns from `dest`.
                            let mut j = i + 1;
                            let mut found = false;
                            while j < insns.len() {
                                let o = insns[j].opcode;
                                if o == opcode::RETURN {
                                    let st2 = constant_stack(&insns[block_start..j]);
                                    let l2 = st2.len();
                                    if l2 >= 2 {
                                        let roff = st2[l2 - 1];
                                        let rlen = st2[l2 - 2];
                                        if (roff.is_none() || roff.and_then(|v| v.as_usize()) == Some(dest)) && (rlen.is_none() || rlen.and_then(|v| v.as_usize()) == Some(len)) {
                                            found = true;
                                        }
                                    } else {
                                        found = true;
                                    }
                                    break;
                                }
                                if opcode::is_terminator(o) || o == opcode::JUMPDEST {
                                    break;
                                }
                                j += 1;
                            }
                            if found {
                                // Prefer the largest region (the runtime) when several copies exist (immutables are smaller).
                                if best.map_or(true, |(_, bl)| len > bl) {
                                    best = Some((offset, len));
                                }
                            }
                        }
                    }
                }
            }
        }
        if opcode::is_terminator(op) || (op == opcode::JUMPDEST && i > block_start) {
            block_start = if op == opcode::JUMPDEST { i } else { i + 1 };
        }
        i += 1;
        // Only the constructor prefix matters; the runtime itself is never scanned past its start.
        if let Some((off, _)) = best {
            if insns[i.min(insns.len() - 1)].pc >= off {
                break;
            }
        }
    }
    best
}

pub fn analyze(code: &[u8]) -> BytecodeInfo {
    if let Some((off, len)) = detect_creation(code) {
        let runtime = code[off..off + len].to_vec();
        let args = code[off + len..].to_vec();
        let constructor = code[..off].to_vec();
        let metadata = parse_metadata(&runtime);
        let constructor_metadata = parse_metadata(&constructor);
        return BytecodeInfo {
            kind: CodeKind::Creation,
            runtime_offset: off,
            runtime_len: len,
            constructor_args_len: args.len(),
            runtime,
            constructor,
            constructor_args: args,
            metadata,
            constructor_metadata,
        };
    }
    BytecodeInfo {
        kind: CodeKind::Runtime,
        runtime_offset: 0,
        runtime_len: code.len(),
        constructor_args_len: 0,
        runtime: code.to_vec(),
        constructor: Vec::new(),
        constructor_args: Vec::new(),
        metadata: parse_metadata(code),
        constructor_metadata: None,
    }
}
