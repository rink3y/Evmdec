//! Linear-sweep disassembly with immediate decoding.

use crate::opcode;
use crate::u256::U256;
use serde::Serialize;

#[derive(Clone, Debug, Serialize)]
pub struct Instruction {
    pub pc: usize,
    pub opcode: u8,
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
    pub fn is_push(&self) -> bool {
        opcode::is_push(self.opcode)
    }
    pub fn push_value(&self) -> Option<U256> {
        self.imm
    }
}

impl serde::Serialize for U256 {
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
        out.push(decode_at(code, pc));
        pc += out.last().unwrap().size;
    }
    out
}

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
    Instruction { pc, opcode: op, name: opcode::name(op), imm, size: 1 + imm_len, truncated }
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
        pc += 1 + if opcode::is_push(op) { (op - 0x5f) as usize } else { 0 };
    }
    v
}

pub fn format_instruction(i: &Instruction) -> String {
    match i.imm {
        Some(v) if i.opcode != opcode::PUSH0 => format!("{:06x}: {} {}", i.pc, i.name, v.to_hex_padded((i.opcode - 0x5f) as usize)),
        _ => format!("{:06x}: {}", i.pc, i.name),
    }
}
