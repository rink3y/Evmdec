use crate::decompile::Contract;
use crate::interp::{CreateRecord, Host, LogRecord, Machine, Outcome, Rng};
use crate::opcode as op;
use crate::{keccak, U256};
use serde::Serialize;
use std::collections::{BTreeMap, HashSet};

const STEPS: usize = 300_000;
// A source that walks the bytecode instruction by instruction takes many steps for one.
const SLOWER: usize = 96;
const GAS_AT_START: u64 = 30_000_000;
const GAS_STEP: u64 = 1_000;
const THIS: u64 = 0xc0de_c0de;
const ACTORS: [u64; 3] = [0xa11ce, 0xb0b0, 0xca401];
const IDENTITY: u64 = 4;
const ORIGIN: u64 = 0x0419;
const SHOWN_CALLDATA: usize = 1024;
const NOTED: usize = 64;
const FOLLOWED: usize = 4;
const DEPTH: usize = 2;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    pub selector: Option<u32>,
    pub signature: String,
    /* For a function written out in a newer Solidity than the original was built with.
    The newer compiler refuses arguments wider than their types, where the old one cut
    them, and names its own failures with a panic code, where the old one gave no data.
    Neither can be written away, so such a function is compared on well-formed calls
    and any two built-in failures count as the same failure. */
    pub loose: bool,
}

#[derive(Clone, Debug, Serialize)]
pub struct Checked {
    pub signature: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub selector: Option<String>,
    pub runs: usize,
    pub returned: usize,
    pub unsettled: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub differs: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct Report {
    pub functions: Vec<Checked>,
    pub branches_reached: usize,
    pub branches: usize,
}

impl Report {
    #[must_use]
    pub fn equal(&self) -> bool {
        self.functions.iter().all(|f| f.differs.is_none())
    }
}

#[derive(Clone, Debug)]
struct Input {
    calldata: Vec<u8>,
    caller: U256,
    origin: U256,
    value: U256,
    timestamp: U256,
    stored: BTreeMap<U256, U256>,
    unset: bool,
    well_formed: bool,
    seed: u64,
}

/* One thing about a call to set so that a comparison the code made comes out equal.
Drawn values almost never land on the edge of a comparison, and the edge is where
`<` and `<=` part. */
#[derive(Clone, Debug, PartialEq, Eq)]
enum Change {
    Caller(U256),
    Value(U256),
    Timestamp(U256),
    Argument(usize, U256),
    Stored(U256, U256),
}

impl Input {
    fn with(&self, change: &Change) -> Input {
        let mut next = self.clone();
        match change {
            Change::Caller(v) => next.caller = *v,
            Change::Value(v) => next.value = *v,
            Change::Timestamp(v) => next.timestamp = *v,
            Change::Argument(i, v) => {
                next.calldata[4 + 32 * i..36 + 32 * i].copy_from_slice(&v.to_be_bytes());
            }
            Change::Stored(slot, v) => {
                next.stored.insert(*slot, *v);
            }
        }
        next
    }

    fn held(&self, host: &Host, slot: U256) -> U256 {
        let set = self.stored.get(&slot).copied();
        set.unwrap_or_else(|| host.storage(slot))
    }

    fn changes(&self, loads: &[(U256, U256)], mine: U256, other: U256) -> Vec<Change> {
        let mut found = Vec::new();
        if mine == self.caller && other.bits() <= 160 {
            found.push(Change::Caller(other));
        }
        if mine == self.value {
            found.push(Change::Value(other));
        }
        if mine == self.timestamp {
            found.push(Change::Timestamp(other));
        }
        let (arguments, _) = self.calldata.get(4..).unwrap_or(&[]).as_chunks::<32>();
        for (i, chunk) in arguments.iter().enumerate() {
            if U256::from_be_bytes(chunk) == mine {
                found.push(Change::Argument(i, other));
            }
        }
        let read = loads.iter().filter(|(_, value)| *value == mine);
        found.extend(read.map(|(slot, _)| Change::Stored(*slot, other)));
        found
    }
}

#[derive(Debug, Default, PartialEq, Eq)]
struct Effect {
    ok: bool,
    data: Vec<u8>,
    storage: BTreeMap<U256, U256>,
    transient: BTreeMap<U256, U256>,
    logs: Vec<LogRecord>,
    calls: Vec<Called>,
    creates: Vec<CreateRecord>,
    destroyed: Option<U256>,
}

/* Gas and where the answer lands in memory are left out. Two compilations of the same
source differ in both and no other account can see either. */
#[derive(Debug, PartialEq, Eq)]
struct Called {
    kind: u8,
    to: U256,
    value: U256,
    input: Vec<u8>,
}

struct Ran {
    effect: Option<Effect>,
    wanted: Vec<Change>,
    steps: usize,
}

fn jump_targets(code: &[u8]) -> Vec<bool> {
    let mut targets = vec![false; code.len()];
    let mut pc = 0;
    while pc < code.len() {
        let o = code[pc];
        targets[pc] = o == op::JUMPDEST;
        pc += 1;
        if (op::PUSH1..=op::PUSH32).contains(&o) {
            pc += usize::from(o - op::PUSH1) + 1;
        }
    }
    targets
}

fn branches(code: &[u8]) -> usize {
    let info = crate::metadata::analyze(code);
    let end = info.metadata.map_or(code.len(), |m| m.offset);
    let mut pc = 0;
    let mut found = 0;
    while pc < end.min(code.len()) {
        let o = code[pc];
        found += usize::from(o == op::JUMPI);
        pc += 1;
        if (op::PUSH1..=op::PUSH32).contains(&o) {
            pc += usize::from(o - op::PUSH1) + 1;
        }
    }
    2 * found
}

fn word(v: U256) -> Vec<u8> {
    v.to_be_bytes().to_vec()
}

/* What an outside call answers. Random bytes would fail nearly every decoder, so most
answers have the shapes real contracts give: nothing, a flag, a small number. */
fn answer(seed: u64, index: usize) -> (bool, Vec<u8>) {
    let label = [
        &seed.to_be_bytes()[..],
        b"answer",
        &(index as u64).to_be_bytes(),
    ]
    .concat();
    let r = keccak::keccak256(&label);
    let small = |i: usize| U256::from_u64(u64::from(r[i]) * u64::from(r[i + 1]));
    match r[0] % 8 {
        0 => (true, Vec::new()),
        1 | 2 => (true, word(U256::ONE)),
        3 => (true, word(U256::ZERO)),
        4 => (true, word(small(1))),
        5 => (true, r.to_vec()),
        6 => (
            true,
            [word(small(1)), word(small(3)), word(small(5))].concat(),
        ),
        _ => (false, Vec::new()),
    }
}

fn settled(m: &Machine<'_>, input: &Input, ok: bool, data: Vec<u8>, calls: Vec<Called>) -> Effect {
    if !ok {
        return Effect {
            data,
            ..Effect::default()
        };
    }
    let changed = |(k, v): (&U256, &U256)| (*v != input.held(m.host, *k)).then_some((*k, *v));
    let set = |(k, v): (&U256, &U256)| (!v.is_zero()).then_some((*k, *v));
    Effect {
        ok,
        data,
        storage: m.storage.iter().filter_map(changed).collect(),
        transient: m.transient.iter().filter_map(set).collect(),
        logs: m.logs.clone(),
        calls,
        creates: m.creates.clone(),
        destroyed: None,
    }
}

fn run(
    code: &[u8],
    input: &Input,
    steps: usize,
    mut reached: Option<&mut HashSet<(usize, bool)>>,
) -> Ran {
    let targets = jump_targets(code);
    let this = U256::from_u64(THIS);
    let mut host = Host::controlled(this, input.caller, input.calldata.clone(), input.value);
    host.seed = input.seed;
    host.origin = input.origin;
    host.unset_storage = input.unset;
    host.timestamp = input.timestamp;
    host.intercept_calls = true;
    let mut m = Machine::new(code, &host);
    m.move_limit = Machine::LOOPED_MOVE_LIMIT;
    m.storage = input.stored.iter().map(|(k, v)| (*k, *v)).collect();
    let mut calls: Vec<Called> = Vec::new();
    let mut loads: Vec<(U256, U256)> = Vec::new();
    let mut wanted: Vec<Change> = Vec::new();
    let mut gas_read = 0u64;
    let mut taken = 0;
    let effect = 'ran: {
        for _ in 0..steps {
            taken += 1;
            if m.pc >= code.len() {
                let effect = settled(&m, input, true, Vec::new(), calls);
                break 'ran Some(effect);
            }
            let top = m.stack.iter().rev().copied();
            match (code[m.pc], top.collect::<Vec<_>>().as_slice()) {
                (op::SLOAD, [slot, ..]) if loads.len() < NOTED => {
                    loads.push((*slot, m.sload(*slot)));
                }
                (op::LT | op::GT | op::SLT | op::SGT | op::EQ, [a, b, ..]) if a != b => {
                    for (mine, other) in [(*a, *b), (*b, *a)] {
                        if mine.is_zero() {
                            continue;
                        }
                        for change in input.changes(&loads, mine, other) {
                            wanted.retain(|w| *w != change);
                            wanted.push(change);
                        }
                    }
                    let extra = wanted.len().saturating_sub(NOTED);
                    wanted.drain(..extra);
                }
                _ => {}
            }
            let at = m.pc;
            let outcome = match m.step() {
                Ok(None) if code[at] == op::GAS => {
                    // Two builds of one source never have the same gas left. Each reading
                    // is a fixed step below the one before, so gas a function reports as
                    // spent between two readings comes out the same in both.
                    gas_read += 1;
                    if let Some(top) = m.stack.last_mut() {
                        *top = U256::from_u64(GAS_AT_START - GAS_STEP * gas_read);
                    }
                    continue;
                }
                Ok(None) => continue,
                Ok(Some(outcome)) => outcome,
                // Running out of stack is a real halt. Every other error is a limit of this
                // interpreter, and says nothing about the code.
                Err(e) if e.starts_with("stack") => Outcome::Invalid,
                Err(_) => break 'ran None,
            };
            let goes = |t: U256| t.as_usize().filter(|t| targets.get(*t) == Some(&true));
            let (ok, data) = match outcome {
                Outcome::Jump(t) => match goes(t) {
                    Some(t) => {
                        m.pc = t;
                        continue;
                    }
                    None => (false, Vec::new()),
                },
                Outcome::JumpI(t, c) => {
                    if let Some(reached) = reached.as_deref_mut() {
                        reached.insert((at, !c.is_zero()));
                    }
                    match (c.is_zero(), goes(t)) {
                        (true, _) => m.pc += 1,
                        (false, Some(t)) => m.pc = t,
                        (false, None) => {
                            let effect = settled(&m, input, false, Vec::new(), calls);
                            break 'ran Some(effect);
                        }
                    }
                    continue;
                }
                Outcome::Call(i) => {
                    let call = m.calls[i].clone();
                    // Old compilers copy memory by calling the identity contract and new ones
                    // use one instruction. The copy is not something another account sees.
                    let (success, data) = if call.addr == U256::from_u64(IDENTITY) {
                        (true, call.input)
                    } else {
                        let said = answer(input.seed, calls.len());
                        calls.push(Called {
                            kind: call.kind,
                            to: call.addr,
                            value: call.value,
                            input: call.input,
                        });
                        said
                    };
                    if m.resume_after_call(i, success, data).is_err() {
                        break 'ran None;
                    }
                    m.pc += 1;
                    continue;
                }
                Outcome::Create(i) => {
                    if m.resume_after_create(host.create_result(i)).is_err() {
                        break 'ran None;
                    }
                    m.pc += 1;
                    continue;
                }
                Outcome::Stop | Outcome::Fallthrough => (true, Vec::new()),
                Outcome::Return(data) => (true, data),
                Outcome::Revert(data) => (false, data),
                Outcome::Invalid | Outcome::Exception(_) => (false, Vec::new()),
                Outcome::SelfDestruct(to) => {
                    let mut effect = settled(&m, input, true, Vec::new(), calls);
                    effect.destroyed = Some(to);
                    break 'ran Some(effect);
                }
            };
            let effect = settled(&m, input, ok, data, calls);
            break 'ran Some(effect);
        }
        None
    };
    Ran {
        effect,
        wanted,
        steps: taken,
    }
}

// The low bits of this generator repeat in step with each other. Two choices made
// from them one after the other would not be independent.
fn below(rng: &mut Rng, n: u64) -> u64 {
    (rng.next_u64() >> 32) % n.max(1)
}

fn pick<T: Copy>(rng: &mut Rng, from: &[T]) -> T {
    from[below(rng, from.len() as u64) as usize]
}

fn low_bits(bits: u32) -> U256 {
    if bits >= 256 {
        U256::MAX
    } else {
        (U256::ONE << bits).wrapping_sub(U256::ONE)
    }
}

fn number(rng: &mut Rng, bits: u32, signed: bool) -> U256 {
    let mask = low_bits(bits);
    let ether = U256::from_u64(1_000_000_000_000_000_000);
    let unsigned = match below(rng, 8) {
        0 => U256::ZERO,
        1 => U256::ONE,
        2 | 3 => U256::from_u64(below(rng, 1000)),
        4 => ether.wrapping_mul(U256::from_u64(below(rng, 1000))) & mask,
        5 => mask,
        6 => U256::from_u64(rng.next_u64()) & mask,
        _ => rng.word() & mask,
    };
    if !signed {
        return unsigned;
    }
    let positive = unsigned & low_bits(bits - 1);
    match below(rng, 3) {
        0 => positive,
        1 => U256::ZERO.wrapping_sub(positive),
        _ => U256::ZERO.wrapping_sub(U256::ONE << (bits - 1)),
    }
}

fn address(rng: &mut Rng) -> U256 {
    match below(rng, 6) {
        0 => U256::ZERO,
        1 => U256::from_u64(THIS),
        2 => U256::from_be_bytes(&rng.bytes(20)),
        _ => U256::from_u64(pick(rng, &ACTORS)),
    }
}

fn width(ty: &str, prefix: &str) -> Option<u32> {
    let rest = ty.strip_prefix(prefix)?;
    if rest.is_empty() {
        return Some(256);
    }
    rest.parse::<u32>().ok().filter(|n| (1..=256).contains(n))
}

fn fits(ty: &str, v: U256) -> Option<bool> {
    if ty.starts_with("address") {
        return Some(v.bits() <= 160);
    }
    if ty == "bool" {
        return Some(v.bits() <= 1);
    }
    if let Some(bits) = width(ty, "uint") {
        return Some(v.bits() <= bits);
    }
    if let Some(bits) = width(ty, "int") {
        return Some(U256::signextend(U256::from(bits / 8 - 1), v) == v);
    }
    let n = width(ty, "bytes").filter(|n| *n <= 32)?;
    Some((v & low_bits(256 - 8 * n)).is_zero())
}

fn single(ty: &str, rng: &mut Rng, well_formed: &mut bool) -> U256 {
    // A decoder has to refuse a word wider than its type. Some words are drawn too wide
    // on purpose so that refusal is compared too.
    if below(rng, 16) == 0 {
        let v = rng.value();
        *well_formed &= fits(ty, v).unwrap_or(false);
        return v;
    }
    if ty.starts_with("address") {
        return address(rng);
    }
    if ty == "bool" {
        return U256::from_u64(below(rng, 2));
    }
    if let Some(bits) = width(ty, "uint") {
        return number(rng, bits, false);
    }
    if let Some(bits) = width(ty, "int") {
        return number(rng, bits, true);
    }
    match width(ty, "bytes").filter(|n| *n <= 32) {
        Some(n) => rng.word() & !low_bits(256 - 8 * n),
        None => rng.value(),
    }
}

fn padded(mut bytes: Vec<u8>) -> Vec<u8> {
    bytes.resize(bytes.len().div_ceil(32) * 32, 0);
    bytes
}

fn tuple(parts: Vec<(Vec<u8>, bool)>) -> (Vec<u8>, bool) {
    let dynamic = parts.iter().any(|(_, d)| *d);
    let head: usize = parts
        .iter()
        .map(|(bytes, d)| if *d { 32 } else { bytes.len() })
        .sum();
    let (mut heads, mut tails) = (Vec::new(), Vec::new());
    for (bytes, d) in parts {
        if d {
            heads.extend(word(U256::from(head + tails.len())));
            tails.extend(bytes);
        } else {
            heads.extend(bytes);
        }
    }
    heads.extend(tails);
    (heads, dynamic)
}

const MAX_FIXED: usize = 64;

fn encode(ty: &str, rng: &mut Rng, well: &mut bool) -> (Vec<u8>, bool) {
    let ty = ty.trim();
    if let Some(open) = ty.rfind('[').filter(|_| ty.ends_with(']')) {
        let inner = &ty[..open];
        return match ty[open + 1..ty.len() - 1].parse::<usize>() {
            Ok(n) => tuple(
                (0..n.min(MAX_FIXED))
                    .map(|_| encode(inner, rng, well))
                    .collect(),
            ),
            Err(_) => {
                let n = below(rng, 4) as usize;
                let (items, _) = tuple((0..n).map(|_| encode(inner, rng, well)).collect());
                ([word(U256::from(n)), items].concat(), true)
            }
        };
    }
    if let Some(inner) = ty.strip_prefix('(').and_then(|t| t.strip_suffix(')')) {
        let parts = crate::abi::split_top(inner);
        return tuple(parts.into_iter().map(|p| encode(p, rng, well)).collect());
    }
    if ty == "bytes" || ty == "string" {
        let n = pick(rng, &[0usize, 1, 31, 32, 33, 68]);
        return ([word(U256::from(n)), padded(rng.bytes(n))].concat(), true);
    }
    (word(single(ty, rng, well)), false)
}

fn types_of(signature: &str) -> Vec<&str> {
    let inner = signature
        .split_once('(')
        .and_then(|(_, rest)| rest.strip_suffix(')'));
    crate::abi::split_top(inner.unwrap_or(""))
}

fn arguments(signature: &str, rng: &mut Rng) -> (Vec<u8>, bool) {
    let types = types_of(signature);
    // Both codes have to refuse malformed input the same way, so some calls ignore the types.
    if below(rng, 8) == 0 {
        let n = below(rng, types.len() as u64 + 3) as usize;
        let mut bytes: Vec<u8> = (0..n).flat_map(|_| word(rng.value())).collect();
        bytes.truncate(bytes.len().saturating_sub(below(rng, 3) as usize * 5));
        return (bytes, false);
    }
    let mut well = true;
    let parts = types.into_iter().map(|t| encode(t, rng, &mut well));
    (tuple(parts.collect()).0, well)
}

fn draw(entry: &Entry, rng: &mut Rng) -> Input {
    let (calldata, well_formed) = match entry.selector {
        Some(selector) => {
            let mut bytes = selector.to_be_bytes().to_vec();
            let (drawn, well) = arguments(&entry.signature, rng);
            bytes.extend(drawn);
            (bytes, well)
        }
        None => {
            let n = pick(rng, &[0usize, 0, 1, 3, 4, 36]);
            (rng.bytes(n), true)
        }
    };
    let value = match below(rng, 4) {
        0 => U256::from_u64(1 + below(rng, 1_000_000_000)),
        _ => U256::ZERO,
    };
    let caller = U256::from_u64(pick(rng, &ACTORS));
    let seed = rng.next_u64();
    Input {
        calldata,
        caller,
        // Mostly the caller itself, as for a call made straight from a wallet.
        origin: match below(rng, 4) {
            0 => U256::from_u64(ORIGIN),
            _ => caller,
        },
        value,
        timestamp: U256::from_u64(1_700_000_000 + seed % (1 << 24)),
        stored: BTreeMap::new(),
        // A contract nobody has used yet. Flags are down and every balance is nothing,
        // which drawn storage almost never gives.
        unset: below(rng, 4) == 0,
        well_formed,
        seed,
    }
}

fn hex_of(bytes: &[u8]) -> String {
    let shown = &bytes[..bytes.len().min(SHOWN_CALLDATA)];
    let cut = if shown.len() < bytes.len() { "..." } else { "" };
    format!("{}{cut}", crate::hex::encode(shown))
}

fn difference(a: &Effect, b: &Effect) -> String {
    let outcome = |e: &Effect| if e.ok { "returns" } else { "reverts" };
    if a.ok != b.ok {
        return format!("the original {} and the source {}", outcome(a), outcome(b));
    }
    if a.data != b.data {
        let what = if a.ok { "return" } else { "revert" };
        let (x, y) = (hex_of(&a.data), hex_of(&b.data));
        return format!("{what} data: the original gives {x} and the source {y}");
    }
    let slots = a.storage.keys().chain(b.storage.keys());
    let unequal = |k: &&U256| a.storage.get(k) != b.storage.get(k);
    if let Some(slot) = slots.into_iter().find(unequal) {
        let held = |e: &Effect| match e.storage.get(slot) {
            Some(v) => v.to_hex(),
            None => "what it held".to_string(),
        };
        let (x, y) = (held(a), held(b));
        let slot = slot.to_hex();
        return format!("storage slot {slot}: the original leaves {x} and the source {y}");
    }
    let parts = [
        ("transient storage", a.transient == b.transient),
        ("events", a.logs == b.logs),
        ("outside calls", a.calls == b.calls),
        ("contracts created", a.creates == b.creates),
        ("self-destruct", a.destroyed == b.destroyed),
    ];
    let unequal = parts.iter().find(|(_, same)| !same);
    unequal.map_or("unknown", |(name, _)| name).to_string()
}

fn described(input: &Input, said: &str) -> String {
    let stored = input.stored.iter();
    let set: Vec<String> = stored
        .map(|(slot, v)| format!(", slot {} holding {}", slot.to_hex(), v.to_hex()))
        .collect();
    format!(
        "{said}, for calldata {} from caller {} and origin {} with value {} at time {} and seed {}{}{}",
        hex_of(&input.calldata),
        input.caller.to_hex(),
        input.origin.to_hex(),
        input.value.to_decimal(),
        input.timestamp.to_decimal(),
        input.seed,
        if input.unset { " on unset storage" } else { "" },
        set.concat()
    )
}

fn built_in(failure: &[u8]) -> bool {
    failure.is_empty() || (failure.len() == 36 && failure[..4] == [0x4e, 0x48, 0x7b, 0x71])
}

fn same(a: &Effect, b: &Effect, loose: bool) -> bool {
    a == b || (loose && !a.ok && !b.ok && built_in(&a.data) && built_in(&b.data))
}

// An argument set to the far side of a comparison can stop fitting its type.
fn still_well_formed(entry: &Entry, change: &Change) -> bool {
    let Change::Argument(i, v) = change else {
        return true;
    };
    let types = types_of(&entry.signature);
    let plain = types.iter().all(|t| fits(t, U256::ZERO).is_some());
    plain && types.get(*i).and_then(|t| fits(t, *v)) == Some(true)
}

pub fn compare(original: &[u8], candidate: &[u8], entries: &[Entry], runs: usize) -> Report {
    let mut reached = HashSet::new();
    let mut functions = Vec::new();
    for entry in entries {
        let mut rng = Rng::new(u64::from(entry.selector.unwrap_or(0)) ^ 0x5eed_c0de);
        let mut checked = Checked {
            signature: entry.signature.clone(),
            selector: entry.selector.map(|s| format!("0x{s:08x}")),
            runs: 0,
            returned: 0,
            unsettled: 0,
            differs: None,
        };
        let mut queue: Vec<(Input, usize)> = Vec::new();
        let mut drawn = 0;
        while drawn < runs || !queue.is_empty() {
            let (input, depth) = queue.pop().unwrap_or_else(|| {
                drawn += 1;
                (draw(entry, &mut rng), 0)
            });
            if entry.loose && !input.well_formed {
                continue;
            }
            let a = run(original, &input, STEPS, Some(&mut reached));
            // The last comparisons of a run are the ones that decided how it ended.
            if depth < DEPTH {
                for change in a.wanted.iter().rev().take(FOLLOWED) {
                    let mut next = input.with(change);
                    next.well_formed &= still_well_formed(entry, change);
                    queue.push((next, depth + 1));
                }
            }
            checked.runs += 1;
            // A run the original did not finish has nothing to compare with. The budget
            // of the source follows what the original needed, so a source that loops
            // forever is stopped soon.
            let budget = SLOWER * (a.steps + 1000);
            let b = a
                .effect
                .as_ref()
                .map(|_| run(candidate, &input, budget, None));
            let (Some(a), Some(b)) = (a.effect, b.and_then(|b| b.effect)) else {
                checked.unsettled += 1;
                continue;
            };
            // Storage no compiler would have written, such as a string whose length and
            // flag disagree, is refused by a newer build and read as it lies by an old one.
            if entry.loose && !b.ok && b.data.len() == 36 && b.data[35] == 0x22 && built_in(&b.data)
            {
                checked.unsettled += 1;
                continue;
            }
            checked.returned += usize::from(a.ok);
            if !same(&a, &b, entry.loose) && checked.differs.is_none() {
                checked.differs = Some(described(&input, &difference(&a, &b)));
            }
        }
        functions.push(checked);
    }
    Report {
        functions,
        branches_reached: reached.len(),
        branches: branches(original),
    }
}

fn selector_of(text: &str) -> Option<u32> {
    u32::from_str_radix(text.trim_start_matches("0x"), 16).ok()
}

pub fn entries(original: &Contract, named: &[(u32, String)]) -> Vec<Entry> {
    let mut found: Vec<Entry> = Vec::new();
    for f in &original.functions {
        let Some(selector) = f.selector.as_deref().and_then(selector_of) else {
            continue;
        };
        let types: Vec<&str> = f.params.iter().map(|p| p.ty.as_str()).collect();
        let own = || format!("{}({})", f.name, types.join(","));
        let given = named.iter().find(|(s, _)| *s == selector);
        let signature = given.map_or_else(own, |(_, signature)| signature.clone());
        if found.iter().all(|e| e.selector != Some(selector)) {
            found.push(Entry {
                selector: Some(selector),
                signature,
                loose: false,
            });
        }
    }
    for (selector, signature) in named {
        if found.iter().all(|e| e.selector != Some(*selector)) {
            found.push(Entry {
                selector: Some(*selector),
                signature: signature.clone(),
                loose: false,
            });
        }
    }
    found.push(Entry {
        selector: None,
        signature: "no selector".to_string(),
        loose: false,
    });
    found
}

#[cfg(feature = "rpc")]
pub fn against_source(
    original: &[u8],
    source: &str,
    runs: usize,
    loose: bool,
) -> Result<(crate::solc::Built, Report), String> {
    let decompiled = crate::decompile::decompile(original, &crate::decompile::Options::default());
    let own: HashSet<u32> = entries(&decompiled, &[])
        .iter()
        .filter_map(|e| e.selector)
        .collect();
    let built = crate::solc::compile(source)?;
    let shared = |b: &crate::solc::Built| b.signatures.keys().filter(|s| own.contains(s)).count();
    let best = built
        .into_iter()
        .max_by_key(shared)
        .ok_or("the source holds no contract")?;
    let mut named: Vec<(u32, String)> = best.signatures.clone().into_iter().collect();
    named.sort();
    let mut entries = entries(&decompiled, &named);
    for e in &mut entries {
        e.loose = loose && e.selector.is_some_and(|s| best.signatures.contains_key(&s));
    }
    let report = compare(&decompiled.info.runtime, &best.runtime, &entries, runs);
    Ok((best, report))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn raw() -> Vec<Entry> {
        vec![Entry {
            selector: None,
            signature: String::new(),
            loose: false,
        }]
    }

    #[test]
    fn two_codes_with_one_behaviour_are_equal_and_a_changed_store_is_not() {
        let stops = crate::hex::decode("600160005500").unwrap();
        let returns = crate::hex::decode("600160005560006000f3").unwrap();
        let other = crate::hex::decode("600260005500").unwrap();
        assert!(compare(&stops, &returns, &raw(), 16).equal());
        let report = compare(&stops, &other, &raw(), 16);
        let said = report.functions[0].differs.as_deref().unwrap_or("");
        assert!(said.starts_with("storage slot 0x0"), "{said}");
    }

    #[test]
    fn a_function_for_one_account_is_run_as_that_account() {
        let only = "73000000000000000000000000000000000000beef3314601d575f5ffd5b600160015500";
        let guarded = crate::hex::decode(only).unwrap();
        let open = crate::hex::decode("600160015500").unwrap();
        let report = compare(&guarded, &guarded, &raw(), 8);
        assert!(report.functions[0].returned > 0);
        assert!(!compare(&guarded, &open, &raw(), 8).equal());
    }

    #[test]
    fn arguments_follow_the_types_of_the_signature() {
        let mut rng = Rng::new(7);
        let mut well = true;
        let (bytes, dynamic) = encode("(uint8,bytes)[2]", &mut rng, &mut well);
        assert!(dynamic);
        assert_eq!(bytes.len() % 32, 0);
        assert_eq!(U256::from_be_bytes(&bytes[..32]), U256::from_u64(64));
        assert_eq!(encode("uint256[3]", &mut rng, &mut well).0.len(), 96);
    }
}
