//! The EVM instruction set (Frontier through Prague), with static stack effects.

/// Static facts about one opcode.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct OpInfo {
    /// Mnemonic.
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
    OpInfo {
        name,
        pops,
        pushes,
        imm: 0,
        gas,
    }
}

/// `STOP` (0x00): Halts execution.
pub const STOP: u8 = 0x00;
/// `ADD` (0x01): Addition modulo 2^256.
pub const ADD: u8 = 0x01;
/// `MUL` (0x02): Multiplication modulo 2^256.
pub const MUL: u8 = 0x02;
/// `SUB` (0x03): Subtraction modulo 2^256.
pub const SUB: u8 = 0x03;
/// `DIV` (0x04): Unsigned integer division; division by zero yields zero.
pub const DIV: u8 = 0x04;
/// `SDIV` (0x05): Signed integer division; division by zero yields zero.
pub const SDIV: u8 = 0x05;
/// `MOD` (0x06): Unsigned modulo remainder; a zero modulus yields zero.
pub const MOD: u8 = 0x06;
/// `SMOD` (0x07): Signed modulo remainder; a zero modulus yields zero.
pub const SMOD: u8 = 0x07;
/// `ADDMOD` (0x08): Modular addition without intermediate overflow.
pub const ADDMOD: u8 = 0x08;
/// `MULMOD` (0x09): Modular multiplication without intermediate overflow.
pub const MULMOD: u8 = 0x09;
/// `EXP` (0x0a): Exponentiation modulo 2^256.
pub const EXP: u8 = 0x0a;
/// `SIGNEXTEND` (0x0b): Sign-extends a two's-complement integer of `b + 1` bytes.
pub const SIGNEXTEND: u8 = 0x0b;
/// `LT` (0x10): Unsigned less-than comparison.
pub const LT: u8 = 0x10;
/// `GT` (0x11): Unsigned greater-than comparison.
pub const GT: u8 = 0x11;
/// `SLT` (0x12): Signed less-than comparison.
pub const SLT: u8 = 0x12;
/// `SGT` (0x13): Signed greater-than comparison.
pub const SGT: u8 = 0x13;
/// `EQ` (0x14): Equality comparison.
pub const EQ: u8 = 0x14;
/// `ISZERO` (0x15): Logical negation: 1 when the operand is zero.
pub const ISZERO: u8 = 0x15;
/// `AND` (0x16): Bitwise AND.
pub const AND: u8 = 0x16;
/// `OR` (0x17): Bitwise OR.
pub const OR: u8 = 0x17;
/// `XOR` (0x18): Bitwise XOR.
pub const XOR: u8 = 0x18;
/// `NOT` (0x19): Bitwise NOT.
pub const NOT: u8 = 0x19;
/// `BYTE` (0x1a): Extracts one byte (big-endian index) of a word.
pub const BYTE: u8 = 0x1a;
/// `SHL` (0x1b): Logical shift left.
pub const SHL: u8 = 0x1b;
/// `SHR` (0x1c): Logical shift right.
pub const SHR: u8 = 0x1c;
/// `SAR` (0x1d): Arithmetic (sign-preserving) shift right.
pub const SAR: u8 = 0x1d;
/// `KECCAK256` (0x20): Keccak-256 hash of a memory range.
pub const KECCAK256: u8 = 0x20;
/// `ADDRESS` (0x30): Address of the executing account.
pub const ADDRESS: u8 = 0x30;
/// `BALANCE` (0x31): Balance of an account.
pub const BALANCE: u8 = 0x31;
/// `ORIGIN` (0x32): Transaction sender (`tx.origin`).
pub const ORIGIN: u8 = 0x32;
/// `CALLER` (0x33): Direct caller (`msg.sender`).
pub const CALLER: u8 = 0x33;
/// `CALLVALUE` (0x34): Wei sent with the call (`msg.value`).
pub const CALLVALUE: u8 = 0x34;
/// `CALLDATALOAD` (0x35): Loads a 32-byte word of calldata.
pub const CALLDATALOAD: u8 = 0x35;
/// `CALLDATASIZE` (0x36): Size of the calldata in bytes.
pub const CALLDATASIZE: u8 = 0x36;
/// `CALLDATACOPY` (0x37): Copies calldata into memory.
pub const CALLDATACOPY: u8 = 0x37;
/// `CODESIZE` (0x38): Size of the executing code.
pub const CODESIZE: u8 = 0x38;
/// `CODECOPY` (0x39): Copies executing code into memory.
pub const CODECOPY: u8 = 0x39;
/// `GASPRICE` (0x3a): Gas price of the transaction.
pub const GASPRICE: u8 = 0x3a;
/// `EXTCODESIZE` (0x3b): Code size of an account.
pub const EXTCODESIZE: u8 = 0x3b;
/// `EXTCODECOPY` (0x3c): Copies an account's code into memory.
pub const EXTCODECOPY: u8 = 0x3c;
/// `RETURNDATASIZE` (0x3d): Size of the last call's return data.
pub const RETURNDATASIZE: u8 = 0x3d;
/// `RETURNDATACOPY` (0x3e): Copies the last call's return data into memory.
pub const RETURNDATACOPY: u8 = 0x3e;
/// `EXTCODEHASH` (0x3f): Code hash of an account.
pub const EXTCODEHASH: u8 = 0x3f;
/// `BLOCKHASH` (0x40): Hash of one of the 256 most recent blocks.
pub const BLOCKHASH: u8 = 0x40;
/// `COINBASE` (0x41): Block beneficiary address.
pub const COINBASE: u8 = 0x41;
/// `TIMESTAMP` (0x42): Block timestamp.
pub const TIMESTAMP: u8 = 0x42;
/// `NUMBER` (0x43): Block number.
pub const NUMBER: u8 = 0x43;
/// `PREVRANDAO` (0x44): Beacon chain randomness of the previous block (`DIFFICULTY` before the merge).
pub const PREVRANDAO: u8 = 0x44;
/// `GASLIMIT` (0x45): Block gas limit.
pub const GASLIMIT: u8 = 0x45;
/// `CHAINID` (0x46): Chain identifier.
pub const CHAINID: u8 = 0x46;
/// `SELFBALANCE` (0x47): Balance of the executing account.
pub const SELFBALANCE: u8 = 0x47;
/// `BASEFEE` (0x48): Block base fee (EIP-3198).
pub const BASEFEE: u8 = 0x48;
/// `BLOBHASH` (0x49): Versioned hash of a transaction blob (EIP-4844).
pub const BLOBHASH: u8 = 0x49;
/// `BLOBBASEFEE` (0x4a): Blob base fee of the block (EIP-7516).
pub const BLOBBASEFEE: u8 = 0x4a;
/// `POP` (0x50): Discards the top stack item.
pub const POP: u8 = 0x50;
/// `MLOAD` (0x51): Loads a 32-byte word from memory.
pub const MLOAD: u8 = 0x51;
/// `MSTORE` (0x52): Stores a 32-byte word to memory.
pub const MSTORE: u8 = 0x52;
/// `MSTORE8` (0x53): Stores one byte to memory.
pub const MSTORE8: u8 = 0x53;
/// `SLOAD` (0x54): Loads a storage slot.
pub const SLOAD: u8 = 0x54;
/// `SSTORE` (0x55): Stores a storage slot.
pub const SSTORE: u8 = 0x55;
/// `JUMP` (0x56): Unconditional jump to a `JUMPDEST`.
pub const JUMP: u8 = 0x56;
/// `JUMPI` (0x57): Conditional jump to a `JUMPDEST`.
pub const JUMPI: u8 = 0x57;
/// `PC` (0x58): Program counter before this instruction.
pub const PC: u8 = 0x58;
/// `MSIZE` (0x59): Size of active memory in bytes.
pub const MSIZE: u8 = 0x59;
/// `GAS` (0x5a): Remaining gas after this instruction.
pub const GAS: u8 = 0x5a;
/// `JUMPDEST` (0x5b): Marks a valid jump target.
pub const JUMPDEST: u8 = 0x5b;
/// `TLOAD` (0x5c): Loads a transient storage slot (EIP-1153).
pub const TLOAD: u8 = 0x5c;
/// `TSTORE` (0x5d): Stores a transient storage slot (EIP-1153).
pub const TSTORE: u8 = 0x5d;
/// `MCOPY` (0x5e): Copies a memory range (EIP-5656).
pub const MCOPY: u8 = 0x5e;
/// `PUSH0` (0x5f): Pushes zero (EIP-3855).
pub const PUSH0: u8 = 0x5f;
/// `PUSH1` (0x60): Pushes a 1-byte immediate; `PUSH1..=PUSH32` are consecutive.
pub const PUSH1: u8 = 0x60;
/// `PUSH32` (0x7f): Pushes a 32-byte immediate.
pub const PUSH32: u8 = 0x7f;
/// `DUP1` (0x80): Duplicates the top stack item; `DUP1..=DUP16` are consecutive.
pub const DUP1: u8 = 0x80;
/// `DUP16` (0x8f): Duplicates the 16th stack item.
pub const DUP16: u8 = 0x8f;
/// `SWAP1` (0x90): Swaps the top two stack items; `SWAP1..=SWAP16` are consecutive.
pub const SWAP1: u8 = 0x90;
/// `SWAP16` (0x9f): Swaps the top with the 17th stack item.
pub const SWAP16: u8 = 0x9f;
/// `LOG0` (0xa0): Emits a log with no topics; `LOG0..=LOG4` are consecutive.
pub const LOG0: u8 = 0xa0;
/// `LOG4` (0xa4): Emits a log with four topics.
pub const LOG4: u8 = 0xa4;
/// `CREATE` (0xf0): Creates a contract.
pub const CREATE: u8 = 0xf0;
/// `CALL` (0xf1): Message call into an account.
pub const CALL: u8 = 0xf1;
/// `CALLCODE` (0xf2): Message call with the caller's storage (legacy).
pub const CALLCODE: u8 = 0xf2;
/// `RETURN` (0xf3): Halts and returns a memory range.
pub const RETURN: u8 = 0xf3;
/// `DELEGATECALL` (0xf4): Message call keeping the caller's context.
pub const DELEGATECALL: u8 = 0xf4;
/// `CREATE2` (0xf5): Creates a contract at a salt-derived address.
pub const CREATE2: u8 = 0xf5;
/// `STATICCALL` (0xfa): Read-only message call.
pub const STATICCALL: u8 = 0xfa;
/// `REVERT` (0xfd): Halts, reverts state and returns a memory range.
pub const REVERT: u8 = 0xfd;
/// `INVALID` (0xfe): Designated invalid instruction.
pub const INVALID: u8 = 0xfe;
/// `SELFDESTRUCT` (0xff): Schedules the account for destruction and sends its balance.
pub const SELFDESTRUCT: u8 = 0xff;

/// The table entry of an opcode, or `None` for an undefined byte.
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
        0x60..=0x7f => OpInfo {
            name: PUSH_NAMES[(opcode - 0x60) as usize],
            pops: 0,
            pushes: 1,
            imm: opcode - 0x5f,
            gas: 3,
        },
        0x80..=0x8f => OpInfo {
            name: DUP_NAMES[(opcode - 0x80) as usize],
            pops: opcode - 0x7f,
            pushes: opcode - 0x7e,
            imm: 0,
            gas: 3,
        },
        0x90..=0x9f => OpInfo {
            name: SWAP_NAMES[(opcode - 0x90) as usize],
            pops: opcode - 0x8e,
            pushes: opcode - 0x8e,
            imm: 0,
            gas: 3,
        },
        0xa0..=0xa4 => OpInfo {
            name: LOG_NAMES[(opcode - 0xa0) as usize],
            pops: opcode - 0xa0 + 2,
            pushes: 0,
            imm: 0,
            gas: 375,
        },
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
    "PUSH1", "PUSH2", "PUSH3", "PUSH4", "PUSH5", "PUSH6", "PUSH7", "PUSH8", "PUSH9", "PUSH10",
    "PUSH11", "PUSH12", "PUSH13", "PUSH14", "PUSH15", "PUSH16", "PUSH17", "PUSH18", "PUSH19",
    "PUSH20", "PUSH21", "PUSH22", "PUSH23", "PUSH24", "PUSH25", "PUSH26", "PUSH27", "PUSH28",
    "PUSH29", "PUSH30", "PUSH31", "PUSH32",
];
const DUP_NAMES: [&str; 16] = [
    "DUP1", "DUP2", "DUP3", "DUP4", "DUP5", "DUP6", "DUP7", "DUP8", "DUP9", "DUP10", "DUP11",
    "DUP12", "DUP13", "DUP14", "DUP15", "DUP16",
];
const SWAP_NAMES: [&str; 16] = [
    "SWAP1", "SWAP2", "SWAP3", "SWAP4", "SWAP5", "SWAP6", "SWAP7", "SWAP8", "SWAP9", "SWAP10",
    "SWAP11", "SWAP12", "SWAP13", "SWAP14", "SWAP15", "SWAP16",
];
const LOG_NAMES: [&str; 5] = ["LOG0", "LOG1", "LOG2", "LOG3", "LOG4"];

/// `PUSH0..=PUSH32`.
pub fn is_push(op: u8) -> bool {
    (0x5f..=0x7f).contains(&op)
}
/// `DUP1..=DUP16`.
pub fn is_dup(op: u8) -> bool {
    (0x80..=0x8f).contains(&op)
}
/// `SWAP1..=SWAP16`.
pub fn is_swap(op: u8) -> bool {
    (0x90..=0x9f).contains(&op)
}
/// `LOG0..=LOG4`.
pub fn is_log(op: u8) -> bool {
    (0xa0..=0xa4).contains(&op)
}
/// Instructions that end a basic block.
/// Ends a basic block: a jump, a halt or an undefined byte.
pub fn is_terminator(op: u8) -> bool {
    matches!(
        op,
        STOP | JUMP | JUMPI | RETURN | REVERT | INVALID | SELFDESTRUCT
    ) || info(op).is_none()
}
/// Instructions after which execution never continues in this frame.
/// Ends execution of the frame: `STOP`, `RETURN`, `REVERT`, `INVALID` or `SELFDESTRUCT`.
pub fn is_halt(op: u8) -> bool {
    matches!(op, STOP | RETURN | REVERT | INVALID | SELFDESTRUCT) || info(op).is_none()
}
/// Mnemonic of an opcode, or `UNKNOWN_xx` for an undefined byte.
pub fn name(op: u8) -> String {
    match info(op) {
        Some(i) => i.name.to_string(),
        None => format!("UNKNOWN_{:02x}", op),
    }
}
