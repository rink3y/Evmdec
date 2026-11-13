use crate::disasm;
use crate::hex;
use crate::opcode;
use crate::u256::U256;
use serde::Serialize;

#[derive(Clone, Debug, Default, Serialize, PartialEq)]
pub struct Metadata {
    pub compiler: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub version: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ipfs: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub bzzr: Option<String>,
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub experimental: bool,
    pub offset: usize,
    pub length: usize,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub raw_keys: Vec<String>,
}

impl Metadata {
    pub fn ipfs_cid(&self) -> Option<String> {
        let bytes = hex::decode(self.ipfs.as_deref()?).ok()?;
        if bytes.len() != 34 || bytes[0] != 0x12 || bytes[1] != 0x20 {
            return None;
        }
        Some(base58(&bytes))
    }

    // solc put its version in the metadata from 0.5.9 and moved to bzzr1 in 0.5.11.
    // A bzzr0-only trailer pins the compiler below 0.5.9.
    pub fn implies_pre_0_5_9(&self) -> bool {
        self.compiler == "solc"
            && self.version.is_none()
            && self.bzzr.as_deref().is_some_and(|b| b.starts_with("bzzr0"))
    }

    pub fn version_tuple(&self) -> Option<(u32, u32, u32)> {
        let v = self.version.as_ref()?;
        let mut it = v.split('.').map(|p| p.parse::<u32>().ok());
        Some((it.next()??, it.next()??, it.next()??))
    }
}

#[derive(Clone, Debug)]
enum Cbor {
    UInt(u64),
    NegInt,
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
        _ => return None,
    };
    Some(match major {
        0 => Cbor::UInt(arg),
        1 => Cbor::NegInt,
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
    let Cbor::Map(entries) = cbor_read(blob, &mut pos, 0)? else {
        return None;
    };
    if pos != blob.len() {
        return None;
    }
    let mut md = Metadata {
        offset: start,
        length: len + 2,
        ..Default::default()
    };
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
                let parts: Vec<String> = a
                    .iter()
                    .filter_map(|x| {
                        if let Cbor::UInt(n) = x {
                            Some(n.to_string())
                        } else {
                            None
                        }
                    })
                    .collect();
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
    #[serde(skip)]
    pub runtime: Vec<u8>,
    #[serde(skip)]
    pub constructor: Vec<u8>,
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

pub fn constant_step(st: &mut Vec<Option<U256>>, i: &disasm::Instruction) {
    let op = i.opcode;
    if opcode::is_push(op) {
        st.push(i.imm);
    } else if opcode::is_dup(op) {
        let n = (op - 0x7f) as usize;
        let v = if st.len() >= n {
            st[st.len() - n]
        } else {
            None
        };
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

pub fn constant_stack(insns: &[disasm::Instruction]) -> Vec<Option<U256>> {
    let mut st: Vec<Option<U256>> = Vec::new();
    for i in insns {
        constant_step(&mut st, i);
    }
    st
}

// Runtime code that loads constants with CODECOPY in a returning block has the same shape.
// A constructor never reads calldata.
// Creation code ends in the runtime's trailer plus its arguments.
fn detect_creation(code: &[u8]) -> Option<(usize, usize)> {
    let insns = disasm::disassemble(code);
    let (off, len) = creation_split(code, &insns)?;
    let reads_calldata = insns
        .iter()
        .take_while(|i| i.pc < off)
        .any(|i| i.opcode == opcode::CALLDATALOAD || i.opcode == opcode::CALLDATACOPY);
    if reads_calldata {
        return None;
    }
    if off + len < code.len() && parse_metadata(code).is_some() {
        return None;
    }
    Some((off, len))
}

// One pass keeps a running stack per block. A copy is judged when its block ends.
// Working the stack out again for every copy was quadratic in a block full of them.
fn creation_split(code: &[u8], insns: &[disasm::Instruction]) -> Option<(usize, usize)> {
    let mut best: Option<(usize, usize)> = None;
    let mut st: Vec<Option<U256>> = Vec::new();
    let mut copies: Vec<(usize, usize, usize, usize)> = Vec::new();
    for ins in insns {
        if best.is_some_and(|(off, _)| ins.pc >= off) {
            break;
        }
        let op = ins.opcode;
        if op == opcode::JUMPDEST {
            st.clear();
            copies.clear();
        }
        if op == opcode::CODECOPY {
            if let [.., Some(len), Some(offset), Some(dest)] = st[..] {
                if let (Some(dest), Some(offset), Some(len)) =
                    (dest.as_usize(), offset.as_usize(), len.as_usize())
                {
                    let inside = offset.checked_add(len).is_some_and(|e| e <= code.len());
                    if offset > ins.pc && len >= 1 && inside {
                        copies.push((ins.pc, dest, offset, len));
                    }
                }
            }
        }
        if op == opcode::RETURN {
            let returned = match st[..] {
                [.., len, off] => Some((off, len)),
                _ => None,
            };
            for (pc, dest, offset, len) in copies.drain(..) {
                if best.is_some_and(|(off, _)| pc >= off) {
                    break;
                }
                let same = |v: Option<U256>, want: usize| {
                    v.is_none() || v.and_then(|v| v.as_usize()) == Some(want)
                };
                let found = returned.is_none_or(|(off, n)| same(off, dest) && same(n, len));
                if found && best.is_none_or(|(_, bl)| len > bl) {
                    best = Some((offset, len));
                }
            }
        }
        if opcode::is_terminator(op) {
            st.clear();
            copies.clear();
        } else {
            constant_step(&mut st, ins);
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

fn base58(bytes: &[u8]) -> String {
    const ALPHABET: &[u8; 58] = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    let mut digits: Vec<u8> = vec![0];
    for &b in bytes {
        let mut carry = b as u32;
        for d in digits.iter_mut() {
            carry += (*d as u32) << 8;
            *d = (carry % 58) as u8;
            carry /= 58;
        }
        while carry > 0 {
            digits.push((carry % 58) as u8);
            carry /= 58;
        }
    }
    let zeros = bytes.iter().take_while(|&&b| b == 0).count();
    let mut out: String = std::iter::repeat_n('1', zeros).collect();
    out.extend(digits.iter().rev().map(|&d| ALPHABET[d as usize] as char));
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ipfs_cid_renders_the_multihash_as_base58() {
        let md = Metadata {
            ipfs: Some(
                "1220ac2f73a8a42fb656e037faafe3f9cd5da4f8716016daabc5646a90ab4183ca44".into(),
            ),
            ..Default::default()
        };
        assert_eq!(
            md.ipfs_cid().as_deref(),
            Some("QmZvnoMz7Fa2K3yc1J3yBH4DvE7z96jKVVFyiTvQWCNnCT")
        );
        assert_eq!(Metadata::default().ipfs_cid(), None);
    }

    fn wrap(runtime: &[u8]) -> Vec<u8> {
        let mut v = vec![0x60, runtime.len() as u8, 0x60, 0x0c, 0x60, 0x00, 0x39];
        v.extend_from_slice(&[0x60, runtime.len() as u8, 0x60, 0x00, 0xf3]);
        v.extend_from_slice(runtime);
        v
    }

    #[test]
    fn creation_code_is_split() {
        let info = analyze(&wrap(&[0x5f, 0x35, 0x00]));
        assert_eq!(info.kind, CodeKind::Creation);
        assert_eq!(info.runtime, [0x5f, 0x35, 0x00]);
    }

    #[test]
    fn runtime_loading_a_constant_from_code_is_not_creation_code() {
        let mut code = vec![0x5f, 0x35, 0x50, 0x60, 0x20, 0x60, 0x13, 0x5f, 0x39];
        code.extend_from_slice(&[0x5f, 0x51, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3, 0x00, 0x00]);
        assert_eq!(code.len(), 0x13);
        code.extend_from_slice(&[0xab; 32]);
        assert_eq!(analyze(&code).kind, CodeKind::Runtime);
    }

    #[test]
    fn code_ending_in_its_own_metadata_is_runtime() {
        let mut code = vec![
            0x60, 0x20, 0x60, 0x0c, 0x5f, 0x39, 0x60, 0x20, 0x5f, 0xf3, 0x00, 0x00,
        ];
        code.extend_from_slice(&[0xab; 32]);
        let trailer = hex::decode("a164736f6c6343000823000a").unwrap();
        code.extend_from_slice(&trailer);
        assert!(parse_metadata(&code).is_some());
        assert_eq!(analyze(&code).kind, CodeKind::Runtime);
        let mut creation = code[..12 + 32].to_vec();
        creation.extend_from_slice(&[0u8; 32]);
        assert_eq!(analyze(&creation).kind, CodeKind::Creation);
    }
}
