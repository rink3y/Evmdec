//! The EVM instruction set (Frontier through Prague), with static stack effects.

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct OpInfo {
    pub name: &'static str,
    /// Items popped.
    pub pops: u8,
    /// Items pushed.
    pub pushes: u8,
    /// Immediate bytes following the opcode (PUSHn only).
    pub imm: u8,
    /// Static base gas (informational; dynamic parts excluded).
    pub gas: u16,
}

const fn op(name: &'static str, pops: u8, pushes: u8, gas: u16) -> OpInfo {
    OpInfo { name, pops, pushes, imm: 0, gas }
}

pub const STOP: u8 = 0x00;
pub const ADD: u8 = 0x01;
pub const MUL: u8 = 0x02;
pub const SUB: u8 = 0x03;
pub const DIV: u8 = 0x04;
pub const SDIV: u8 = 0x05;
pub const MOD: u8 = 0x06;
pub const SMOD: u8 = 0x07;
pub const ADDMOD: u8 = 0x08;
pub const MULMOD: u8 = 0x09;
pub const EXP: u8 = 0x0a;
pub const SIGNEXTEND: u8 = 0x0b;
pub const LT: u8 = 0x10;
pub const GT: u8 = 0x11;
pub const SLT: u8 = 0x12;
pub const SGT: u8 = 0x13;
pub const EQ: u8 = 0x14;
pub const ISZERO: u8 = 0x15;
pub const AND: u8 = 0x16;
pub const OR: u8 = 0x17;
pub const XOR: u8 = 0x18;
pub const NOT: u8 = 0x19;
pub const BYTE: u8 = 0x1a;
pub const SHL: u8 = 0x1b;
pub const SHR: u8 = 0x1c;
pub const SAR: u8 = 0x1d;
pub const KECCAK256: u8 = 0x20;
pub const ADDRESS: u8 = 0x30;
pub const BALANCE: u8 = 0x31;
pub const ORIGIN: u8 = 0x32;
pub const CALLER: u8 = 0x33;
pub const CALLVALUE: u8 = 0x34;
pub const CALLDATALOAD: u8 = 0x35;
pub const CALLDATASIZE: u8 = 0x36;
pub const CALLDATACOPY: u8 = 0x37;
pub const CODESIZE: u8 = 0x38;
pub const CODECOPY: u8 = 0x39;
pub const GASPRICE: u8 = 0x3a;
pub const EXTCODESIZE: u8 = 0x3b;
pub const EXTCODECOPY: u8 = 0x3c;
pub const RETURNDATASIZE: u8 = 0x3d;
pub const RETURNDATACOPY: u8 = 0x3e;
pub const EXTCODEHASH: u8 = 0x3f;
pub const BLOCKHASH: u8 = 0x40;
pub const COINBASE: u8 = 0x41;
pub const TIMESTAMP: u8 = 0x42;
pub const NUMBER: u8 = 0x43;
pub const PREVRANDAO: u8 = 0x44;
pub const GASLIMIT: u8 = 0x45;
pub const CHAINID: u8 = 0x46;
pub const SELFBALANCE: u8 = 0x47;
pub const BASEFEE: u8 = 0x48;
pub const BLOBHASH: u8 = 0x49;
pub const BLOBBASEFEE: u8 = 0x4a;
pub const POP: u8 = 0x50;
pub const MLOAD: u8 = 0x51;
pub const MSTORE: u8 = 0x52;
pub const MSTORE8: u8 = 0x53;
pub const SLOAD: u8 = 0x54;
pub const SSTORE: u8 = 0x55;
pub const JUMP: u8 = 0x56;
pub const JUMPI: u8 = 0x57;
pub const PC: u8 = 0x58;
pub const MSIZE: u8 = 0x59;
pub const GAS: u8 = 0x5a;
pub const JUMPDEST: u8 = 0x5b;
pub const TLOAD: u8 = 0x5c;
pub const TSTORE: u8 = 0x5d;
pub const MCOPY: u8 = 0x5e;
pub const PUSH0: u8 = 0x5f;
pub const PUSH1: u8 = 0x60;
pub const PUSH32: u8 = 0x7f;
pub const DUP1: u8 = 0x80;
pub const DUP16: u8 = 0x8f;
pub const SWAP1: u8 = 0x90;
pub const SWAP16: u8 = 0x9f;
pub const LOG0: u8 = 0xa0;
pub const LOG4: u8 = 0xa4;
pub const CREATE: u8 = 0xf0;
pub const CALL: u8 = 0xf1;
pub const CALLCODE: u8 = 0xf2;
pub const RETURN: u8 = 0xf3;
pub const DELEGATECALL: u8 = 0xf4;
pub const CREATE2: u8 = 0xf5;
pub const STATICCALL: u8 = 0xfa;
pub const REVERT: u8 = 0xfd;
pub const INVALID: u8 = 0xfe;
pub const SELFDESTRUCT: u8 = 0xff;

pub fn info(opcode: u8) -> Option<OpInfo> {
    Some(match opcode {
        0x00 => op("STOP", 0, 0, 0),
        0x01 => op("ADD", 2, 1, 3),
        0x02 => op("MUL", 2, 1, 5),
        0x03 => op("SUB", 2, 1, 3),
        0x04 => op("DIV", 2, 1, 5),
        0x05 => op("SDIV", 2, 1, 5),
        0x06 => op("MOD", 2, 1, 5),
        0x07 => op("SMOD", 2, 1, 5),
        0x08 => op("ADDMOD", 3, 1, 8),
        0x09 => op("MULMOD", 3, 1, 8),
        0x0a => op("EXP", 2, 1, 10),
        0x0b => op("SIGNEXTEND", 2, 1, 5),
        0x10 => op("LT", 2, 1, 3),
        0x11 => op("GT", 2, 1, 3),
        0x12 => op("SLT", 2, 1, 3),
        0x13 => op("SGT", 2, 1, 3),
        0x14 => op("EQ", 2, 1, 3),
        0x15 => op("ISZERO", 1, 1, 3),
        0x16 => op("AND", 2, 1, 3),
        0x17 => op("OR", 2, 1, 3),
        0x18 => op("XOR", 2, 1, 3),
        0x19 => op("NOT", 1, 1, 3),
        0x1a => op("BYTE", 2, 1, 3),
        0x1b => op("SHL", 2, 1, 3),
        0x1c => op("SHR", 2, 1, 3),
        0x1d => op("SAR", 2, 1, 3),
        0x20 => op("KECCAK256", 2, 1, 30),
        0x30 => op("ADDRESS", 0, 1, 2),
        0x31 => op("BALANCE", 1, 1, 100),
        0x32 => op("ORIGIN", 0, 1, 2),
        0x33 => op("CALLER", 0, 1, 2),
        0x34 => op("CALLVALUE", 0, 1, 2),
        0x35 => op("CALLDATALOAD", 1, 1, 3),
        0x36 => op("CALLDATASIZE", 0, 1, 2),
        0x37 => op("CALLDATACOPY", 3, 0, 3),
        0x38 => op("CODESIZE", 0, 1, 2),
        0x39 => op("CODECOPY", 3, 0, 3),
        0x3a => op("GASPRICE", 0, 1, 2),
        0x3b => op("EXTCODESIZE", 1, 1, 100),
        0x3c => op("EXTCODECOPY", 4, 0, 100),
        0x3d => op("RETURNDATASIZE", 0, 1, 2),
        0x3e => op("RETURNDATACOPY", 3, 0, 3),
        0x3f => op("EXTCODEHASH", 1, 1, 100),
        0x40 => op("BLOCKHASH", 1, 1, 20),
        0x41 => op("COINBASE", 0, 1, 2),
        0x42 => op("TIMESTAMP", 0, 1, 2),
        0x43 => op("NUMBER", 0, 1, 2),
        0x44 => op("PREVRANDAO", 0, 1, 2),
        0x45 => op("GASLIMIT", 0, 1, 2),
        0x46 => op("CHAINID", 0, 1, 2),
        0x47 => op("SELFBALANCE", 0, 1, 5),
        0x48 => op("BASEFEE", 0, 1, 2),
        0x49 => op("BLOBHASH", 1, 1, 3),
        0x4a => op("BLOBBASEFEE", 0, 1, 2),
        0x50 => op("POP", 1, 0, 2),
        0x51 => op("MLOAD", 1, 1, 3),
        0x52 => op("MSTORE", 2, 0, 3),
        0x53 => op("MSTORE8", 2, 0, 3),
        0x54 => op("SLOAD", 1, 1, 100),
        0x55 => op("SSTORE", 2, 0, 100),
        0x56 => op("JUMP", 1, 0, 8),
        0x57 => op("JUMPI", 2, 0, 10),
        0x58 => op("PC", 0, 1, 2),
        0x59 => op("MSIZE", 0, 1, 2),
        0x5a => op("GAS", 0, 1, 2),
        0x5b => op("JUMPDEST", 0, 0, 1),
        0x5c => op("TLOAD", 1, 1, 100),
        0x5d => op("TSTORE", 2, 0, 100),
        0x5e => op("MCOPY", 3, 0, 3),
        0x5f => op("PUSH0", 0, 1, 2),
        0x60..=0x7f => OpInfo { name: PUSH_NAMES[(opcode - 0x60) as usize], pops: 0, pushes: 1, imm: opcode - 0x5f, gas: 3 },
        0x80..=0x8f => OpInfo { name: DUP_NAMES[(opcode - 0x80) as usize], pops: opcode - 0x7f, pushes: opcode - 0x7e, imm: 0, gas: 3 },
        0x90..=0x9f => OpInfo { name: SWAP_NAMES[(opcode - 0x90) as usize], pops: opcode - 0x8e, pushes: opcode - 0x8e, imm: 0, gas: 3 },
        0xa0..=0xa4 => OpInfo { name: LOG_NAMES[(opcode - 0xa0) as usize], pops: opcode - 0xa0 + 2, pushes: 0, imm: 0, gas: 375 },
        0xf0 => op("CREATE", 3, 1, 32000),
        0xf1 => op("CALL", 7, 1, 100),
        0xf2 => op("CALLCODE", 7, 1, 100),
        0xf3 => op("RETURN", 2, 0, 0),
        0xf4 => op("DELEGATECALL", 6, 1, 100),
        0xf5 => op("CREATE2", 4, 1, 32000),
        0xfa => op("STATICCALL", 6, 1, 100),
        0xfd => op("REVERT", 2, 0, 0),
        0xfe => op("INVALID", 0, 0, 0),
        0xff => op("SELFDESTRUCT", 1, 0, 5000),
        _ => return None,
    })
}

const PUSH_NAMES: [&str; 32] = [
    "PUSH1", "PUSH2", "PUSH3", "PUSH4", "PUSH5", "PUSH6", "PUSH7", "PUSH8", "PUSH9", "PUSH10", "PUSH11", "PUSH12", "PUSH13", "PUSH14", "PUSH15", "PUSH16",
    "PUSH17", "PUSH18", "PUSH19", "PUSH20", "PUSH21", "PUSH22", "PUSH23", "PUSH24", "PUSH25", "PUSH26", "PUSH27", "PUSH28", "PUSH29", "PUSH30", "PUSH31", "PUSH32",
];
const DUP_NAMES: [&str; 16] = ["DUP1", "DUP2", "DUP3", "DUP4", "DUP5", "DUP6", "DUP7", "DUP8", "DUP9", "DUP10", "DUP11", "DUP12", "DUP13", "DUP14", "DUP15", "DUP16"];
const SWAP_NAMES: [&str; 16] = ["SWAP1", "SWAP2", "SWAP3", "SWAP4", "SWAP5", "SWAP6", "SWAP7", "SWAP8", "SWAP9", "SWAP10", "SWAP11", "SWAP12", "SWAP13", "SWAP14", "SWAP15", "SWAP16"];
const LOG_NAMES: [&str; 5] = ["LOG0", "LOG1", "LOG2", "LOG3", "LOG4"];

pub fn is_push(op: u8) -> bool {
    (0x5f..=0x7f).contains(&op)
}
pub fn is_dup(op: u8) -> bool {
    (0x80..=0x8f).contains(&op)
}
pub fn is_swap(op: u8) -> bool {
    (0x90..=0x9f).contains(&op)
}
pub fn is_log(op: u8) -> bool {
    (0xa0..=0xa4).contains(&op)
}
/// Instructions that end a basic block.
pub fn is_terminator(op: u8) -> bool {
    matches!(op, STOP | JUMP | JUMPI | RETURN | REVERT | INVALID | SELFDESTRUCT) || info(op).is_none()
}
/// Instructions after which execution never continues in this frame.
pub fn is_halt(op: u8) -> bool {
    matches!(op, STOP | RETURN | REVERT | INVALID | SELFDESTRUCT) || info(op).is_none()
}
pub fn name(op: u8) -> String {
    match info(op) {
        Some(i) => i.name.to_string(),
        None => format!("UNKNOWN_{:02x}", op),
    }
}
