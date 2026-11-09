//! A concrete EVM interpreter for single-frame execution (the reference side of the oracle).
//! External effects (calls, creates, environment, other accounts) are provided by a deterministic
//! pseudo-random host so that both sides of a comparison see the same world.

use crate::keccak;
use crate::opcode as op;
use crate::u256::U256;
use std::collections::HashMap;

/// Deterministic PRNG (xorshift64*).
#[derive(Clone, Debug)]
pub struct Rng(pub u64);
impl Rng {
    /// Creates a generator from `seed`; the state is forced odd so it is never the all-zero
    /// fixed point of xorshift.
    pub fn new(seed: u64) -> Rng {
        Rng(seed.wrapping_mul(0x9e3779b97f4a7c15) | 1)
    }
    /// Advances the state and returns the next 64-bit output.
    pub fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545f4914f6cdd1d)
    }
    /// A value in `0..n` (`0` when `n == 0`).
    pub fn below(&mut self, n: u64) -> u64 {
        if n == 0 {
            0
        } else {
            self.next_u64() % n
        }
    }
    /// A uniformly random 256-bit word.
    pub fn word(&mut self) -> U256 {
        U256([
            self.next_u64(),
            self.next_u64(),
            self.next_u64(),
            self.next_u64(),
        ])
    }
    /// `n` random bytes.
    pub fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.next_u64() as u8).collect()
    }
    /// A stack value drawn from a distribution that exercises offsets, small ints, addresses and full words.
    pub fn value(&mut self) -> U256 {
        match self.below(12) {
            0..=2 => U256::from_u64(self.below(64)),
            3..=5 => U256::from_u64(0x80 + 32 * self.below(64)),
            6 => U256::from_u64(0x1000 + self.below(0x4000)),
            7 => U256::from_be_bytes(&self.bytes(20)),
            8 => U256::from_u64(self.next_u64()),
            9 => U256::MAX.wrapping_sub(U256::from_u64(self.below(64))),
            _ => self.word(),
        }
    }
}

fn h(data: &[u8]) -> U256 {
    U256::from_be_bytes(&keccak::keccak256(data))
}

/// The world outside the frame: environment values and deterministic external effects.
#[derive(Clone, Debug)]
pub struct Host {
    /// Address of the executing account (`ADDRESS`).
    pub address: U256,
    /// Immediate caller of the frame (`CALLER`).
    pub caller: U256,
    /// Transaction sender (`ORIGIN`).
    pub origin: U256,
    /// Value sent with the call (`CALLVALUE`).
    pub callvalue: U256,
    /// Input data of the frame (`CALLDATALOAD`, `CALLDATASIZE`, `CALLDATACOPY`).
    pub calldata: Vec<u8>,
    /// Gas price of the transaction (`GASPRICE`).
    pub gasprice: U256,
    /// Block beneficiary (`COINBASE`).
    pub coinbase: U256,
    /// Block timestamp (`TIMESTAMP`).
    pub timestamp: U256,
    /// Block number (`NUMBER`); also bounds the range `blockhash` answers for.
    pub number: U256,
    /// Beacon chain randomness (`PREVRANDAO`).
    pub prevrandao: U256,
    /// Block gas limit (`GASLIMIT`).
    pub gaslimit: U256,
    /// Chain identifier (`CHAINID`).
    pub chainid: U256,
    /// Balance of the executing account (`SELFBALANCE`).
    pub selfbalance: U256,
    /// Block base fee (`BASEFEE`).
    pub basefee: U256,
    /// Blob base fee (`BLOBBASEFEE`).
    pub blobbasefee: U256,
    /// Seed from which every external effect (balances, code, storage, call and create results)
    /// is derived, so two machines sharing a host observe the same world.
    pub seed: u64,
    /// When set, `storage` reads as zero for every key not written in the frame (a freshly
    /// deployed, empty contract), instead of the seed-derived value. Used by the executor so a
    /// confirmation run starts from a clean, chosen state.
    pub zero_storage: bool,
    /// When set, every external call returns this success flag with empty data, instead of the
    /// seed-derived outcome. Lets a confirmation run assume the worst (or best) case of a callee.
    pub force_calls: Option<bool>,
}

impl Host {
    /// Draws a plausible environment from `rng`: 20-byte addresses, up to 260 bytes of calldata,
    /// recent-looking block values and a fresh effect `seed`.
    pub fn random(rng: &mut Rng) -> Host {
        Host {
            address: U256::from_be_bytes(&rng.bytes(20)),
            caller: U256::from_be_bytes(&rng.bytes(20)),
            origin: U256::from_be_bytes(&rng.bytes(20)),
            callvalue: if rng.below(2) == 0 {
                U256::ZERO
            } else {
                U256::from_u64(rng.next_u64())
            },
            calldata: {
                let n = rng.below(260) as usize;
                rng.bytes(n)
            },
            gasprice: U256::from_u64(rng.below(1 << 40)),
            coinbase: U256::from_be_bytes(&rng.bytes(20)),
            timestamp: U256::from_u64(1_600_000_000 + rng.below(1 << 30)),
            number: U256::from_u64(rng.below(1 << 24)),
            prevrandao: rng.word(),
            gaslimit: U256::from_u64(30_000_000),
            chainid: U256::from_u64(1 + rng.below(5)),
            selfbalance: U256::from_u64(rng.next_u64()),
            basefee: U256::from_u64(rng.below(1 << 36)),
            blobbasefee: U256::from_u64(rng.below(1 << 20)),
            seed: rng.next_u64(),
            zero_storage: false,
            force_calls: None,
        }
    }

    /// A controlled environment for a confirmation run: `caller` is both the immediate caller
    /// and the transaction origin (the account whose reach is being tested), `calldata` is the
    /// input, storage reads as zero unless written, and the block values are fixed. External
    /// calls succeed with empty return data (plain transfers land and the caller's own contracts
    /// cooperate), which is the case a reachability witness is about. Every field is
    /// deterministic so a reached sink is reproducible.
    pub fn controlled(address: U256, caller: U256, calldata: Vec<u8>, callvalue: U256) -> Host {
        Host {
            address,
            caller,
            origin: caller,
            callvalue,
            calldata,
            gasprice: U256::from_u64(1_000_000_000),
            coinbase: U256::from_u64(0xc0),
            timestamp: U256::from_u64(1_700_000_000),
            number: U256::from_u64(18_000_000),
            prevrandao: U256::from_u64(0x1234_5678_9abc_def0),
            gaslimit: U256::from_u64(30_000_000),
            chainid: U256::ONE,
            selfbalance: U256::from_u64(1_000_000_000_000_000_000),
            basefee: U256::from_u64(1_000_000_000),
            blobbasefee: U256::ONE,
            seed: 0x5eed,
            zero_storage: true,
            force_calls: Some(true),
        }
    }
    /// Balance of account `a` (`BALANCE`): seed-derived, limited to 64 bits.
    pub fn balance(&self, a: U256) -> U256 {
        h(&[&self.seed.to_be_bytes()[..], b"bal", &a.to_be_bytes()].concat())
            & U256::from_u64(u64::MAX)
    }
    /// Code size of account `a` (`EXTCODESIZE`): seed-derived, below 300 bytes. The zero address
    /// never holds code, so an unset storage slot read as an address has none.
    pub fn extcodesize(&self, a: U256) -> U256 {
        if a.is_zero() {
            return U256::ZERO;
        }
        U256::from_u64(
            h(&[&self.seed.to_be_bytes()[..], b"size", &a.to_be_bytes()].concat()).low_u64() % 300,
        )
    }
    /// Code hash of account `a` (`EXTCODEHASH`): seed-derived, not the hash of `extcode`; zero
    /// for the zero address, which has no code.
    pub fn extcodehash(&self, a: U256) -> U256 {
        if a.is_zero() {
            return U256::ZERO;
        }
        h(&[&self.seed.to_be_bytes()[..], b"hash", &a.to_be_bytes()].concat())
    }
    /// Code of account `a` (`EXTCODECOPY`): `extcodesize(a)` seed-derived bytes.
    pub fn extcode(&self, a: U256) -> Vec<u8> {
        let n = self.extcodesize(a).low_u64() as usize;
        let mut v = Vec::new();
        let mut i = 0u64;
        while v.len() < n {
            v.extend_from_slice(&keccak::keccak256(
                &[
                    &self.seed.to_be_bytes()[..],
                    b"code",
                    &a.to_be_bytes(),
                    &i.to_be_bytes(),
                ]
                .concat(),
            ));
            i += 1;
        }
        v.truncate(n);
        v
    }
    /// Hash of block `n` (`BLOCKHASH`): zero unless `n` is one of the 256 blocks before `number`.
    pub fn blockhash(&self, n: U256) -> U256 {
        if n >= self.number || self.number.wrapping_sub(n) > U256::from_u64(256) {
            U256::ZERO
        } else {
            h(&[&self.seed.to_be_bytes()[..], b"bh", &n.to_be_bytes()].concat())
        }
    }
    /// Versioned hash of blob `i` (`BLOBHASH`): zero for indices of 3 and above.
    pub fn blobhash(&self, i: U256) -> U256 {
        if i >= U256::from_u64(3) {
            U256::ZERO
        } else {
            h(&[&self.seed.to_be_bytes()[..], b"blob", &i.to_be_bytes()].concat())
        }
    }
    /// Initial storage value of a key (random but deterministic).
    pub fn storage(&self, k: U256) -> U256 {
        if self.zero_storage {
            return U256::ZERO;
        }
        let r = h(&[&self.seed.to_be_bytes()[..], b"stor", &k.to_be_bytes()].concat());
        if r.low_u64().is_multiple_of(3) {
            U256::ZERO
        } else {
            r
        }
    }
    /// Outcome of the i-th external call: (success, return data).
    pub fn call_result(&self, i: usize) -> (bool, Vec<u8>) {
        if let Some(b) = self.force_calls {
            return (b, Vec::new());
        }
        let r = keccak::keccak256(
            &[
                &self.seed.to_be_bytes()[..],
                b"call",
                &(i as u64).to_be_bytes(),
            ]
            .concat(),
        );
        let success = !r[0].is_multiple_of(4);
        let n = (r[1] as usize) % 97;
        let mut data = Vec::new();
        let mut j = 0u64;
        while data.len() < n {
            data.extend_from_slice(&keccak::keccak256(&[&r[..], &j.to_be_bytes()].concat()));
            j += 1;
        }
        data.truncate(n);
        (success, data)
    }
    /// Address returned by the i-th `CREATE`/`CREATE2`; zero (failure) for roughly one in five.
    pub fn create_result(&self, i: usize) -> U256 {
        let r = h(&[
            &self.seed.to_be_bytes()[..],
            b"create",
            &(i as u64).to_be_bytes(),
        ]
        .concat());
        if r.low_u64().is_multiple_of(5) {
            U256::ZERO
        } else {
            r & crate::expr::mask_bits(160)
        }
    }
    /// Gas available when the frame starts: between one and two million, seed-derived.
    pub fn initial_gas(&self) -> u64 {
        1_000_000 + (self.seed % 1_000_000)
    }
}

/// Operands of one external call, recorded so both sides of a comparison can be checked.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallRecord {
    /// The opcode: `CALL`, `CALLCODE`, `DELEGATECALL` or `STATICCALL`.
    pub kind: u8,
    /// Gas operand.
    pub gas: U256,
    /// Callee address.
    pub addr: U256,
    /// Value operand (zero for `DELEGATECALL` and `STATICCALL`, which have none).
    pub value: U256,
    /// Input bytes read from memory.
    pub input: Vec<u8>,
    /// Memory offset the return data is written to.
    pub out_off: U256,
    /// Maximum number of return-data bytes written to memory.
    pub out_len: U256,
}

/// Operands of one contract creation, recorded so both sides of a comparison can be checked.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CreateRecord {
    /// The opcode: `CREATE` or `CREATE2`.
    pub kind: u8,
    /// Value endowed to the new account.
    pub value: U256,
    /// Init code read from memory.
    pub init: Vec<u8>,
    /// Salt operand; present only for `CREATE2`.
    pub salt: Option<U256>,
}

/// One emitted log (`LOG0`..`LOG4`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LogRecord {
    /// Topics in operand order (zero to four).
    pub topics: Vec<U256>,
    /// Payload read from memory.
    pub data: Vec<u8>,
}

/// How a block's execution ended.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    /// Block ended with JUMP to this target value.
    Jump(U256),
    /// JUMPI: (target, condition).
    JumpI(U256, U256),
    /// Fell through to the next block.
    Fallthrough,
    /// `STOP`.
    Stop,
    /// `RETURN` with the returned bytes.
    Return(Vec<u8>),
    /// `REVERT` with the revert data.
    Revert(Vec<u8>),
    /// `SELFDESTRUCT` with the beneficiary address.
    SelfDestruct(U256),
    /// `INVALID` or an undefined opcode.
    Invalid,
    /// Exceptional halt inside the block (stack underflow/overflow, bad opcode).
    Exception(String),
}

/// Execution state of one frame: the EVM machine state plus a record of every external effect.
#[derive(Clone, Debug)]
pub struct Machine<'a> {
    /// The bytecode being executed.
    pub code: &'a [u8],
    /// Environment and external effects.
    pub host: &'a Host,
    /// Operand stack, bottom first.
    pub stack: Vec<U256>,
    /// Memory, always a whole number of 32-byte words.
    pub memory: Vec<u8>,
    /// Storage overrides (reads fall back to `host.storage`).
    pub storage: HashMap<U256, U256>,
    /// Transient storage (`TLOAD`/`TSTORE`); unset keys read as zero.
    pub transient: HashMap<U256, U256>,
    /// Return data of the last call or create (`RETURNDATASIZE`/`RETURNDATACOPY`).
    pub returndata: Vec<u8>,
    /// Remaining gas, decremented by each instruction's static cost.
    pub gas: u64,
    /// Logs emitted so far, in order.
    pub logs: Vec<LogRecord>,
    /// External calls made so far, in order; the index selects `Host::call_result`.
    pub calls: Vec<CallRecord>,
    /// Creations made so far, in order; the index selects `Host::create_result`.
    pub creates: Vec<CreateRecord>,
    /// Values observed by GAS and MSIZE, in order (the lifter treats them as opaque).
    pub gas_obs: Vec<U256>,
    /// Values observed by `MSIZE`, in order.
    pub msize_obs: Vec<U256>,
    /// Offset of the next instruction to execute.
    pub pc: usize,
}

impl<'a> Machine<'a> {
    /// A machine at offset 0 with empty stack, memory and effects, and the host's initial gas.
    pub fn new(code: &'a [u8], host: &'a Host) -> Machine<'a> {
        Machine {
            code,
            host,
            stack: Vec::new(),
            memory: Vec::new(),
            storage: HashMap::new(),
            transient: HashMap::new(),
            returndata: Vec::new(),
            gas: host.initial_gas(),
            logs: vec![],
            calls: vec![],
            creates: vec![],
            gas_obs: vec![],
            msize_obs: vec![],
            pc: 0,
        }
    }

    /// Current value of storage key `k`: a write made in this frame, else the host's initial value.
    pub fn sload(&self, k: U256) -> U256 {
        self.storage
            .get(&k)
            .copied()
            .unwrap_or_else(|| self.host.storage(k))
    }

    const MEM_LIMIT: usize = 1 << 26;
    fn expand(&mut self, off: usize, len: usize) -> Result<(), String> {
        if len == 0 {
            return Ok(());
        }
        let end = off.saturating_add(len);
        if end > Self::MEM_LIMIT {
            return Err("memory offset too large".into());
        }
        let rounded = end.div_ceil(32) * 32;
        if rounded > self.memory.len() {
            self.memory.resize(rounded, 0);
        }
        Ok(())
    }
    /// Reads `len` bytes at `off`, expanding memory first; fails when the range exceeds the
    /// memory limit.
    pub fn mread(&mut self, off: U256, len: usize) -> Result<Vec<u8>, String> {
        if len == 0 {
            return Ok(vec![]);
        }
        let o = off
            .as_usize()
            .filter(|o| *o < Self::MEM_LIMIT)
            .ok_or("memory offset too large")?;
        self.expand(o, len)?;
        Ok(self.memory[o..o + len].to_vec())
    }
    /// Writes `data` at `off`, expanding memory first; fails when the range exceeds the memory
    /// limit.
    pub fn mwrite(&mut self, off: U256, data: &[u8]) -> Result<(), String> {
        if data.is_empty() {
            return Ok(());
        }
        let o = off
            .as_usize()
            .filter(|o| *o < Self::MEM_LIMIT)
            .ok_or("memory offset too large")?;
        self.expand(o, data.len())?;
        self.memory[o..o + data.len()].copy_from_slice(data);
        Ok(())
    }
    fn copy_in(&mut self, dest: U256, src: U256, len: U256, source: &[u8]) -> Result<(), String> {
        let n = len
            .as_usize()
            .filter(|n| *n < (1 << 26))
            .ok_or("copy length too large")?;
        if n == 0 {
            return Ok(());
        }
        let mut buf = vec![0u8; n];
        if let Some(s) = src.as_usize() {
            for (i, out) in buf.iter_mut().enumerate() {
                if let Some(b) = source.get(s.saturating_add(i)) {
                    *out = *b;
                }
            }
        }
        self.mwrite(dest, &buf)
    }

    fn pop(&mut self) -> Result<U256, String> {
        self.stack
            .pop()
            .ok_or_else(|| "stack underflow".to_string())
    }
    fn push(&mut self, v: U256) -> Result<(), String> {
        if self.stack.len() >= 1024 {
            return Err("stack overflow".into());
        }
        self.stack.push(v);
        Ok(())
    }

    /// Execute instructions from `pc` until the end of the block (`end` exclusive) or a terminator.
    pub fn run_block(&mut self, start: usize, end: usize) -> Outcome {
        self.pc = start;
        while self.pc < end && self.pc < self.code.len() {
            match self.step() {
                Ok(Some(outcome)) => return outcome,
                Ok(None) => {}
                Err(e) => return Outcome::Exception(e),
            }
        }
        Outcome::Fallthrough
    }

    /// Execute one instruction. Returns Some(outcome) if the block ends here.
    pub fn step(&mut self) -> Result<Option<Outcome>, String> {
        let o = self.code[self.pc];
        let info = op::info(o);
        self.gas = self
            .gas
            .saturating_sub(info.map(|i| i.gas as u64).unwrap_or(0));
        let mut next = self.pc + 1;
        macro_rules! bin {
            ($f:expr) => {{
                let a = self.pop()?;
                let b = self.pop()?;
                self.push($f(a, b))?;
            }};
        }
        match o {
            op::STOP => return Ok(Some(Outcome::Stop)),
            op::ADD => bin!(|a: U256, b: U256| a.wrapping_add(b)),
            op::MUL => bin!(|a: U256, b: U256| a.wrapping_mul(b)),
            op::SUB => bin!(|a: U256, b: U256| a.wrapping_sub(b)),
            op::DIV => bin!(|a: U256, b: U256| a / b),
            op::SDIV => bin!(|a: U256, b: U256| a.sdiv(b)),
            op::MOD => bin!(|a: U256, b: U256| a % b),
            op::SMOD => bin!(|a: U256, b: U256| a.smod(b)),
            op::ADDMOD => {
                let a = self.pop()?;
                let b = self.pop()?;
                let n = self.pop()?;
                self.push(a.addmod(b, n))?;
            }
            op::MULMOD => {
                let a = self.pop()?;
                let b = self.pop()?;
                let n = self.pop()?;
                self.push(a.mulmod(b, n))?;
            }
            op::EXP => bin!(|a: U256, b: U256| a.pow(b)),
            op::SIGNEXTEND => bin!(|a: U256, b: U256| U256::signextend(a, b)),
            op::LT => bin!(|a: U256, b: U256| U256::from(a < b)),
            op::GT => bin!(|a: U256, b: U256| U256::from(a > b)),
            op::SLT => bin!(|a: U256, b: U256| U256::from(a.scmp(&b) == std::cmp::Ordering::Less)),
            op::SGT => {
                bin!(|a: U256, b: U256| U256::from(a.scmp(&b) == std::cmp::Ordering::Greater))
            }
            op::EQ => bin!(|a: U256, b: U256| U256::from(a == b)),
            op::ISZERO => {
                let a = self.pop()?;
                self.push(U256::from(a.is_zero()))?;
            }
            op::AND => bin!(|a: U256, b: U256| a & b),
            op::OR => bin!(|a: U256, b: U256| a | b),
            op::XOR => bin!(|a: U256, b: U256| a ^ b),
            op::NOT => {
                let a = self.pop()?;
                self.push(!a)?;
            }
            op::BYTE => bin!(|a: U256, b: U256| U256::byte(a, b)),
            op::SHL => bin!(|a: U256, b: U256| if a >= U256::from_u64(256) {
                U256::ZERO
            } else {
                b << a.low_u64() as u32
            }),
            op::SHR => bin!(|a: U256, b: U256| if a >= U256::from_u64(256) {
                U256::ZERO
            } else {
                b >> a.low_u64() as u32
            }),
            op::SAR => bin!(|a: U256, b: U256| if a >= U256::from_u64(256) {
                if b.is_negative() {
                    U256::MAX
                } else {
                    U256::ZERO
                }
            } else {
                b.sar(a.low_u64() as u32)
            }),
            op::KECCAK256 => {
                let off = self.pop()?;
                let len = self.pop()?;
                let n = len
                    .as_usize()
                    .filter(|n| *n < (1 << 24))
                    .ok_or("keccak length too large")?;
                let data = self.mread(off, n)?;
                self.push(U256::from_be_bytes(&keccak::keccak256(&data)))?;
            }
            op::ADDRESS => self.push(self.host.address)?,
            op::BALANCE => {
                let a = self.pop()?;
                let v = if a == self.host.address {
                    self.host.selfbalance
                } else {
                    self.host.balance(a)
                };
                self.push(v)?;
            }
            op::ORIGIN => self.push(self.host.origin)?,
            op::CALLER => self.push(self.host.caller)?,
            op::CALLVALUE => self.push(self.host.callvalue)?,
            op::CALLDATALOAD => {
                let off = self.pop()?;
                let mut buf = [0u8; 32];
                if let Some(o) = off.as_usize() {
                    for (i, out) in buf.iter_mut().enumerate() {
                        if let Some(b) = self.host.calldata.get(o.saturating_add(i)) {
                            *out = *b;
                        }
                    }
                }
                self.push(U256::from_be_bytes(&buf))?;
            }
            op::CALLDATASIZE => self.push(U256::from(self.host.calldata.len()))?,
            op::CALLDATACOPY => {
                let d = self.pop()?;
                let s = self.pop()?;
                let l = self.pop()?;
                let src = self.host.calldata.clone();
                self.copy_in(d, s, l, &src)?;
            }
            op::CODESIZE => self.push(U256::from(self.code.len()))?,
            op::CODECOPY => {
                let d = self.pop()?;
                let s = self.pop()?;
                let l = self.pop()?;
                let code = self.code;
                self.copy_in(d, s, l, code)?;
            }
            op::GASPRICE => self.push(self.host.gasprice)?,
            op::EXTCODESIZE => {
                let a = self.pop()?;
                let v = if a == self.host.address {
                    U256::from(self.code.len())
                } else {
                    self.host.extcodesize(a)
                };
                self.push(v)?;
            }
            op::EXTCODECOPY => {
                let a = self.pop()?;
                let d = self.pop()?;
                let s = self.pop()?;
                let l = self.pop()?;
                let src = if a == self.host.address {
                    self.code.to_vec()
                } else {
                    self.host.extcode(a)
                };
                self.copy_in(d, s, l, &src)?;
            }
            op::RETURNDATASIZE => self.push(U256::from(self.returndata.len()))?,
            op::RETURNDATACOPY => {
                let d = self.pop()?;
                let s = self.pop()?;
                let l = self.pop()?;
                let end = s
                    .as_usize()
                    .and_then(|s| l.as_usize().map(|l| s.saturating_add(l)));
                if end.is_none_or(|e| e > self.returndata.len()) && !l.is_zero() {
                    return Err("returndata out of bounds".into());
                }
                let src = self.returndata.clone();
                self.copy_in(d, s, l, &src)?;
            }
            op::EXTCODEHASH => {
                let a = self.pop()?;
                self.push(self.host.extcodehash(a))?;
            }
            op::BLOCKHASH => {
                let n = self.pop()?;
                self.push(self.host.blockhash(n))?;
            }
            op::COINBASE => self.push(self.host.coinbase)?,
            op::TIMESTAMP => self.push(self.host.timestamp)?,
            op::NUMBER => self.push(self.host.number)?,
            op::PREVRANDAO => self.push(self.host.prevrandao)?,
            op::GASLIMIT => self.push(self.host.gaslimit)?,
            op::CHAINID => self.push(self.host.chainid)?,
            op::SELFBALANCE => self.push(self.host.selfbalance)?,
            op::BASEFEE => self.push(self.host.basefee)?,
            op::BLOBHASH => {
                let i = self.pop()?;
                self.push(self.host.blobhash(i))?;
            }
            op::BLOBBASEFEE => self.push(self.host.blobbasefee)?,
            op::POP => {
                self.pop()?;
            }
            op::MLOAD => {
                let off = self.pop()?;
                let b = self.mread(off, 32)?;
                self.push(U256::from_be_bytes(&b))?;
            }
            op::MSTORE => {
                let off = self.pop()?;
                let v = self.pop()?;
                self.mwrite(off, &v.to_be_bytes())?;
            }
            op::MSTORE8 => {
                let off = self.pop()?;
                let v = self.pop()?;
                self.mwrite(off, &[v.to_be_bytes()[31]])?;
            }
            op::SLOAD => {
                let k = self.pop()?;
                let v = self.sload(k);
                self.push(v)?;
            }
            op::SSTORE => {
                let k = self.pop()?;
                let v = self.pop()?;
                self.storage.insert(k, v);
            }
            op::JUMP => {
                let t = self.pop()?;
                return Ok(Some(Outcome::Jump(t)));
            }
            op::JUMPI => {
                let t = self.pop()?;
                let c = self.pop()?;
                return Ok(Some(Outcome::JumpI(t, c)));
            }
            op::PC => self.push(U256::from(self.pc))?,
            op::MSIZE => {
                let v = U256::from(self.memory.len());
                self.msize_obs.push(v);
                self.push(v)?;
            }
            op::GAS => {
                let v = U256::from_u64(self.gas);
                self.gas_obs.push(v);
                self.push(v)?;
            }
            op::JUMPDEST => {}
            op::TLOAD => {
                let k = self.pop()?;
                let v = self.transient.get(&k).copied().unwrap_or(U256::ZERO);
                self.push(v)?;
            }
            op::TSTORE => {
                let k = self.pop()?;
                let v = self.pop()?;
                self.transient.insert(k, v);
            }
            op::MCOPY => {
                let d = self.pop()?;
                let s = self.pop()?;
                let l = self.pop()?;
                let n = l
                    .as_usize()
                    .filter(|n| *n < (1 << 24))
                    .ok_or("mcopy too large")?;
                let data = self.mread(s, n)?;
                self.mwrite(d, &data)?;
            }
            op::PUSH0 => self.push(U256::ZERO)?,
            0x60..=0x7f => {
                let n = (o - 0x5f) as usize;
                let end = (self.pc + 1 + n).min(self.code.len());
                let mut buf = self.code[self.pc + 1..end].to_vec();
                buf.resize(n, 0);
                self.push(U256::from_be_bytes(&buf))?;
                next = self.pc + 1 + n;
            }
            0x80..=0x8f => {
                let n = (o - 0x7f) as usize;
                if self.stack.len() < n {
                    return Err("stack underflow".into());
                }
                let v = self.stack[self.stack.len() - n];
                self.push(v)?;
            }
            0x90..=0x9f => {
                let n = (o - 0x8f) as usize;
                if self.stack.len() < n + 1 {
                    return Err("stack underflow".into());
                }
                let l = self.stack.len();
                self.stack.swap(l - 1, l - 1 - n);
            }
            0xa0..=0xa4 => {
                let off = self.pop()?;
                let len = self.pop()?;
                let n = (o - 0xa0) as usize;
                let mut topics = Vec::new();
                for _ in 0..n {
                    topics.push(self.pop()?);
                }
                let l = len
                    .as_usize()
                    .filter(|l| *l < (1 << 24))
                    .ok_or("log too large")?;
                let data = self.mread(off, l)?;
                self.logs.push(LogRecord { topics, data });
            }
            op::CREATE | op::CREATE2 => {
                let value = self.pop()?;
                let off = self.pop()?;
                let len = self.pop()?;
                let salt = if o == op::CREATE2 {
                    Some(self.pop()?)
                } else {
                    None
                };
                let l = len
                    .as_usize()
                    .filter(|l| *l < (1 << 24))
                    .ok_or("init code too large")?;
                let init = self.mread(off, l)?;
                let idx = self.creates.len();
                self.creates.push(CreateRecord {
                    kind: o,
                    value,
                    init,
                    salt,
                });
                let addr = self.host.create_result(idx);
                self.returndata = Vec::new();
                self.push(addr)?;
            }
            op::CALL | op::CALLCODE | op::DELEGATECALL | op::STATICCALL => {
                let gas = self.pop()?;
                let addr = self.pop()?;
                let value = if o == op::CALL || o == op::CALLCODE {
                    self.pop()?
                } else {
                    U256::ZERO
                };
                let in_off = self.pop()?;
                let in_len = self.pop()?;
                let out_off = self.pop()?;
                let out_len = self.pop()?;
                let il = in_len
                    .as_usize()
                    .filter(|l| *l < (1 << 24))
                    .ok_or("call input too large")?;
                let input = self.mread(in_off, il)?;
                let idx = self.calls.len();
                self.calls.push(CallRecord {
                    kind: o,
                    gas,
                    addr,
                    value,
                    input: input.clone(),
                    out_off,
                    out_len,
                });
                let (success, data) = if addr == U256::from_u64(4) {
                    (true, input)
                } else {
                    self.host.call_result(idx)
                };
                let ol = out_len
                    .as_usize()
                    .filter(|l| *l < (1 << 24))
                    .ok_or("call output too large")?;
                if ol > 0 {
                    let mut buf = data.clone();
                    buf.truncate(ol);
                    self.expand(out_off.as_usize().ok_or("out offset too large")?, ol)?;
                    self.mwrite(out_off, &buf)?;
                }
                self.returndata = data;
                self.push(U256::from(success))?;
            }
            op::RETURN | op::REVERT => {
                let off = self.pop()?;
                let len = self.pop()?;
                let l = len
                    .as_usize()
                    .filter(|l| *l < (1 << 24))
                    .ok_or("return too large")?;
                let data = self.mread(off, l)?;
                return Ok(Some(if o == op::RETURN {
                    Outcome::Return(data)
                } else {
                    Outcome::Revert(data)
                }));
            }
            op::SELFDESTRUCT => {
                let a = self.pop()?;
                return Ok(Some(Outcome::SelfDestruct(a)));
            }
            op::INVALID => return Ok(Some(Outcome::Invalid)),
            _ => return Ok(Some(Outcome::Invalid)),
        }
        self.pc = next;
        Ok(None)
    }
}
