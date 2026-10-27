//! `evmdec`: a from-scratch EVM bytecode decompiler and security analyzer.
//!
//! Pipeline: bytes → [`disasm`] → [`cfg`] (context-sensitive jump resolution) → [`symexec`] (lifting
//! to expression IR) → [`structure`] → [`emit`] (pseudo-Solidity) and [`analyze`] (findings).

pub mod disasm;
pub mod hex;
pub mod keccak;
pub mod metadata;
pub mod opcode;
pub mod u256;

pub use u256::U256;
pub mod cfg;
pub mod expr;
pub mod lift;
pub mod sigs;
pub mod emit;
pub mod function;
pub mod decompile;
pub mod structure;
pub mod analyze;
