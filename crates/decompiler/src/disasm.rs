//! Linear-sweep disassembly with immediate decoding.

use crate::opcode;
use crate::u256::U256;
use serde::Serialize;

/// One decoded EVM instruction.
#[derive(Clone, Debug, Serialize)]
pub struct Instruction {
    /// Byte offset of the opcode within the code.
    pub pc: usize,
    /// Raw opcode byte.
    pub opcode: u8,
    /// Mnemonic, or `UNKNOWN_xx` for an undefined opcode.
    pub name: String,
    /// Immediate value of a PUSH (PUSH0 => zero).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub imm: Option<U256>,
    /// Width of the whole instruction in bytes.
    pub size: usize,
    /// True when a PUSH's immediate was cut short by the end of code (treated as zero-padded, as the EVM does).
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub truncated: bool,
}

impl Instruction {
    /// True for `PUSH0`..`PUSH32`.
    pub fn is_push(&self) -> bool {
        opcode::is_push(self.opcode)
    }
    /// The PUSH immediate, or `None` for any other instruction.
    pub fn push_value(&self) -> Option<U256> {
        self.imm
    }
}

impl Serialize for U256 {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(&self.to_hex())
    }
}

/// Disassemble every byte of `code` as an instruction stream, starting at offset 0.
/// Unknown opcodes become `UNKNOWN_xx` single-byte instructions; nothing is ever rejected.
pub fn disassemble(code: &[u8]) -> Vec<Instruction> {
    let mut out = Vec::with_capacity(code.len() / 2);
    let mut pc = 0;
    while pc < code.len() {
        let insn = decode_at(code, pc);
        pc += insn.size;
        out.push(insn);
    }
    out
}

/// Decodes the single instruction at byte offset `pc`, which must lie within `code`.
///
/// A PUSH immediate cut short by the end of code is zero-padded and flagged `truncated`.
pub fn decode_at(code: &[u8], pc: usize) -> Instruction {
    let op = code[pc];
    let info = opcode::info(op);
    let imm_len = info.map(|i| i.imm as usize).unwrap_or(0);
    let mut truncated = false;
    let imm = if opcode::is_push(op) {
        let end = pc + 1 + imm_len;
        let avail = &code[pc + 1..end.min(code.len())];
        if avail.len() < imm_len {
            truncated = true;
            let mut buf = avail.to_vec();
            buf.resize(imm_len, 0);
            Some(U256::from_be_bytes(&buf))
        } else {
            Some(U256::from_be_bytes(avail))
        }
    } else {
        None
    };
    Instruction {
        pc,
        opcode: op,
        name: opcode::name(op),
        imm,
        size: 1 + imm_len,
        truncated,
    }
}

/// All valid jump destinations: JUMPDEST bytes that are not inside a PUSH immediate.
pub fn jumpdests(code: &[u8]) -> Vec<usize> {
    let mut v = Vec::new();
    let mut pc = 0;
    while pc < code.len() {
        let op = code[pc];
        if op == opcode::JUMPDEST {
            v.push(pc);
        }
        pc += 1 + if opcode::is_push(op) {
            (op - 0x5f) as usize
        } else {
            0
        };
    }
    v
}

/// Renders an instruction as `pc: NAME imm`, with a six-digit hex pc and the immediate
/// padded to the PUSH width.
pub fn format_instruction(i: &Instruction) -> String {
    match i.imm {
        Some(v) if i.opcode != opcode::PUSH0 => format!(
            "{:06x}: {} {}",
            i.pc,
            i.name,
            v.to_hex_padded((i.opcode - 0x5f) as usize)
        ),
        _ => format!("{:06x}: {}", i.pc, i.name),
    }
}
