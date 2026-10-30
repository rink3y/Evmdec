//! `evmdec`: a from-scratch EVM bytecode decompiler and security analyzer.
//!
//! Pipeline: bytes → [`disasm`] → [`cfg`](mod@cfg) (context-sensitive jump resolution) → [`lift`] (lifting
//! to expression IR) → [`structure`] → [`emit`] (pseudo-Solidity) and [`analyze`] (findings).

#![warn(missing_docs)]

pub mod disasm;
pub mod hex;
pub mod idiom;
pub mod keccak;
pub mod metadata;
pub mod opcode;
pub mod u256;

pub use u256::U256;
pub mod analyze;
pub mod cfg;
pub mod compiler;
pub mod decompile;
pub mod emit;
pub mod expr;
pub mod function;
pub mod interp;
pub mod lift;
#[cfg(feature = "rpc")]
pub mod rpc;
pub mod sigdb;
pub mod sigs;
pub mod ssa;
pub mod structure;
pub mod types;
pub mod verify;
