use crate::opcode;
use crate::u256::U256;
use serde::Serialize;

#[derive(Clone, Debug, Serialize)]
pub struct Instruction {
    pub pc: usize,
    pub opcode: u8,
    pub name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub imm: Option<U256>,
    pub size: usize,
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub truncated: bool,
}

impl Instruction {
    pub fn is_push(&self) -> bool {
        opcode::is_push(self.opcode)
    }
}

impl Serialize for U256 {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(&self.to_hex())
    }
}

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_push_cut_off_by_the_end_of_the_code_is_marked() {
        let insns = disassemble(&[0x60, 0x01, 0x61, 0xff]);
        assert_eq!(insns.len(), 2);
        assert!(!insns[0].truncated && insns[1].truncated);
        assert_eq!(insns[1].pc, 2);
    }

    #[test]
    fn a_jump_destination_inside_push_data_is_not_one() {
        assert_eq!(jumpdests(&[0x60, 0x5b, 0x5b, 0x00]), vec![2]);
    }
}
