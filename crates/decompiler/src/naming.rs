//! Names the code implies where no signature gives one.
//!
//! A storage variable is named by the setter that writes it, by the event announcing its
//! change, or by its role: the address the contract's guards compare with the caller, the slot
//! toggled as a lock, the ledger a transfer debits and credits with the allowance and supply
//! that move with it, a timestamp. An internal function is named by what it does: the event it
//! emits, the call it makes, the variable it writes, the caller check it performs. A parameter
//! is named by how it is used: the account debited, the account credited, the amount, a
//! deadline, the parts of a signature, a call target. Every rule reads the lifted code; none
//! lists contracts, and a name is given only where the default (`stor_3`, `func_0x1fbb`,
//! `arg0`) would otherwise stand.

use crate::decompile::{Function, StorageVar};
use crate::emit::{self, MappingLayout};
use crate::expr::{self, ExprId, Node};
use crate::function::FnKind;
use crate::lift::{Lifted, Stmt, Term};
use crate::opcode as op;
use crate::sigs;
use crate::ssa::{self, Step};
use crate::u256::U256;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

/// A storage variable or one packed field of it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Target {
    /// The variable rooted at this slot (a scalar, a mapping, an array).
    Var(U256),
    /// The field at this byte offset and bit width of a packed slot.
    Field(U256, u32, u32),
    /// What an element of the mapping or array rooted at this slot holds at this slot offset,
    /// byte offset and bit width: a struct member, or the element itself where there is no
    /// struct.
    Member(U256, u64, u32, u32),
}

/// One ledger movement: `entry = entry - amount` or `entry = entry + amount`.
#[derive(Clone, Debug)]
struct Movement {
    /// Root slot of the mapping.
    root: U256,
    /// Keys from the root to the entry.
    keys: Vec<ExprId>,
    /// The amount moved.
    amount: ExprId,
    /// The entry grew.
    credit: bool,
}

/// What one function's own statements do, as far as naming cares.
#[derive(Clone, Debug, Default)]
struct Facts {
    /// Every store: where and what.
    stores: Vec<(Target, ExprId)>,
    /// Mapping entries raised or lowered by an amount.
    movements: Vec<Movement>,
    /// Constant slots raised or lowered by an amount: `(slot, amount, grew)`.
    scalar_moves: Vec<(U256, ExprId, bool)>,
    /// Names of the events emitted, where the topic is known.
    events: BTreeSet<String>,
    /// Some event with an unknown topic is emitted.
    unknown_event: bool,
    /// Names of the functions called on other contracts, where the selector is known.
    calls: BTreeSet<String>,
    /// Some call on another contract has an unknown selector.
    unknown_call: bool,
    /// Ether is sent with an empty payload.
    sends_value: bool,
    /// Storage the caller is compared with in a guard.
    caller_guards: BTreeSet<Target>,
    /// Internal functions called.
    callees: Vec<usize>,
}

fn slot_of(v: &StorageVar) -> Option<U256> {
    U256::from_hex_str(&v.slot).or_else(|| U256::from_dec_str(&v.slot))
}

fn unmask(e: ExprId) -> ExprId {
    if let Node::Op(op::AND, v) = expr::node(e) {
        for (m, x) in [(v[0], v[1]), (v[1], v[0])] {
            if expr::as_const(m).is_some_and(|c| c.is_low_mask()) {
                return x;
            }
        }
    }
    e
}

fn is_caller(e: ExprId) -> bool {
    matches!(expr::node(unmask(e)), Node::Env(op::CALLER, _))
}

/// The variable, field or element member a store writes.
fn store_target(key: ExprId, val: ExprId, layout: MappingLayout) -> Option<Target> {
    let path = ssa::slot_path(key, layout)?;
    let field = || ssa::field_write(key, val).map(|w| (w.bit_offset / 8, w.bits));
    match path.steps.split_last() {
        None => Some(match field() {
            Some((byte, bits)) => Target::Field(path.root, byte, bits),
            None => Target::Var(path.root),
        }),
        Some((Step::Offset(at), element))
            if !element.iter().any(|s| matches!(s, Step::Offset(_))) =>
        {
            let (byte, bits) = field().unwrap_or((0, 256));
            Some(Target::Member(path.root, *at, byte, bits))
        }
        Some(_) if path.steps.iter().any(|s| matches!(s, Step::Offset(_))) => None,
        Some(_) => Some(Target::Member(path.root, 0, 0, 256)),
    }
}

/// The constant slot or packed field `e` reads, through a width mask.
fn read_target(e: ExprId) -> Option<Target> {
    if let Some((slot, offset, bits)) = emit::packed_read(e) {
        return Some(if offset == 0 && bits >= 160 {
            Target::Var(slot)
        } else {
            Target::Field(slot, offset, bits)
        });
    }
    match expr::node(unmask(e)) {
        Node::SLoad(k, false, _) => expr::as_const(k).map(Target::Var),
        _ => None,
    }
}

/// Storage compared for equality with the caller anywhere in `cond`.
fn caller_comparisons(cond: ExprId, out: &mut BTreeSet<Target>) {
    let mut seen = HashSet::new();
    let mut stack = vec![cond];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 2_000 {
            continue;
        }
        if let Node::Op(op::EQ | op::SUB | op::XOR, v) = expr::node(x) {
            for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
                if is_caller(a) {
                    if let Some(t) = read_target(b) {
                        out.insert(t);
                    }
                }
            }
        }
        stack.extend(expr::children(x));
    }
}

fn facts(l: &Lifted, layout: MappingLayout, use_sigs: bool) -> Facts {
    let mut f = Facts::default();
    for nd in &l.nodes {
        if let Term::Branch { cond, .. } = &nd.term {
            caller_comparisons(*cond, &mut f.caller_guards);
        }
        for st in &nd.stmts {
            match st {
                Stmt::Require { cond, .. } => caller_comparisons(*cond, &mut f.caller_guards),
                Stmt::SStore {
                    key,
                    val,
                    transient: false,
                    ..
                } => {
                    if let Some(t) = store_target(*key, *val, layout) {
                        f.stores.push((t, *val));
                    }
                    let moved = match expr::node(*val) {
                        Node::Op(op::SUB, v) => {
                            matches!(expr::node(v[0]), Node::SLoad(k, false, _) if k == *key)
                                .then_some((v[1], false))
                        }
                        Node::Op(op::ADD, v) => [(v[0], v[1]), (v[1], v[0])]
                            .into_iter()
                            .find(|(a, _)| {
                                matches!(expr::node(*a), Node::SLoad(k, false, _) if k == *key)
                            })
                            .map(|(_, amount)| (amount, true)),
                        _ => None,
                    };
                    let Some((amount, credit)) = moved else {
                        continue;
                    };
                    let Some(path) = ssa::slot_path(*key, layout) else {
                        continue;
                    };
                    let keys: Option<Vec<ExprId>> = path
                        .steps
                        .iter()
                        .map(|s| match s {
                            Step::Key(k) => Some(*k),
                            _ => None,
                        })
                        .collect();
                    match keys {
                        Some(keys) if keys.is_empty() => {
                            f.scalar_moves.push((path.root, amount, credit));
                        }
                        Some(keys) => f.movements.push(Movement {
                            root: path.root,
                            keys,
                            amount,
                            credit,
                        }),
                        None => {}
                    }
                }
                Stmt::Log { topics, .. } => {
                    let name = topics
                        .first()
                        .and_then(|t| expr::as_const(*t))
                        .filter(|_| use_sigs)
                        .and_then(|t| sigs::event(&t.to_be_bytes()))
                        .map(|s| sigs::name_of(&s).to_string());
                    match name {
                        Some(n) => {
                            f.events.insert(n);
                        }
                        None => f.unknown_event = true,
                    }
                }
                Stmt::Call {
                    addr,
                    value,
                    input,
                    input_head,
                    in_len,
                    ..
                } => {
                    if expr::as_const(*addr).is_some_and(|a| a.fits_u64() && a.low_u64() < 16) {
                        continue;
                    }
                    let len = expr::as_const(*in_len).and_then(|l| l.as_usize());
                    if len == Some(0) {
                        if value.is_some_and(|v| expr::as_const(v) != Some(U256::ZERO)) {
                            f.sends_value = true;
                        }
                        continue;
                    }
                    let words: &[ExprId] = input.as_deref().unwrap_or(input_head);
                    let name = words
                        .first()
                        .and_then(|w0| emit::leading_selector(*w0, len))
                        .filter(|_| use_sigs)
                        .and_then(sigs::function)
                        .map(|s| sigs::name_of(&s).to_string());
                    match name {
                        Some(n) => {
                            f.calls.insert(n);
                        }
                        None => f.unknown_call = true,
                    }
                }
                Stmt::Internal { callee, .. } => f.callees.push(*callee),
                _ => {}
            }
        }
    }
    f
}

/// `facts` of every lifted function, by entry pc.
fn all_facts(
    functions: &[Function],
    layout: MappingLayout,
    use_sigs: bool,
) -> BTreeMap<usize, Facts> {
    functions
        .iter()
        .filter_map(|f| {
            f.lifted
                .as_ref()
                .map(|l| (f.pc, facts(l, layout, use_sigs)))
        })
        .collect()
}

/// The functions reachable from `pc` through internal calls, `pc` included.
fn reach(pc: usize, all: &BTreeMap<usize, Facts>) -> Vec<usize> {
    let mut seen = BTreeSet::new();
    let mut stack = vec![pc];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 256 {
            continue;
        }
        if let Some(f) = all.get(&x) {
            stack.extend(f.callees.iter().copied());
        }
    }
    seen.into_iter().collect()
}

/// `fee` for `Fee`, `ttl` for `TTL`, `uriPrefix` for `URIPrefix`: a leading run of capitals
/// is one word, up to the capital that starts the next.
fn lower_first(s: &str) -> String {
    let run = s.chars().take_while(char::is_ascii_uppercase).count();
    let word = match run {
        0 => 0,
        n if n == s.len() || n == 1 => n,
        n => n - 1,
    };
    format!("{}{}", s[..word].to_ascii_lowercase(), &s[word..])
}

fn upper_first(s: &str) -> String {
    let mut cs = s.chars();
    match cs.next() {
        Some(c) => format!("{}{}", c.to_ascii_uppercase(), cs.as_str()),
        None => String::new(),
    }
}

/// `fee` for `setFee`, `updateFee`, `changeFee` and `set_fee`.
fn setter_stem(name: &str) -> Option<String> {
    ["set", "update", "change"].iter().find_map(|p| {
        let rest = name.strip_prefix(p)?;
        let first = rest.chars().next()?;
        (first.is_ascii_uppercase() || first == '_')
            .then(|| lower_first(rest.trim_start_matches('_')))
            .filter(|s| !s.is_empty())
    })
}

/// `fee` for `FeeUpdated`, `FeeChanged`, `FeeSet`, `NewFee`, `SetFee` and `UpdateFee`.
fn event_stem(name: &str) -> Option<String> {
    let suffix = ["Updated", "Changed", "Set"]
        .iter()
        .find_map(|s| name.strip_suffix(s))
        .filter(|rest| !rest.is_empty());
    let prefix = ["New", "Set", "Update"].iter().find_map(|p| {
        name.strip_prefix(p)
            .filter(|rest| rest.chars().next().is_some_and(|c| c.is_ascii_uppercase()))
    });
    suffix.or(prefix).map(lower_first)
}

/// Words a name must not be: they would read as the language, not as a variable.
const RESERVED: &[&str] = &[
    "address",
    "bool",
    "string",
    "bytes",
    "uint",
    "int",
    "mapping",
    "function",
    "return",
    "returns",
    "if",
    "else",
    "for",
    "while",
    "do",
    "break",
    "continue",
    "require",
    "revert",
    "emit",
    "event",
    "error",
    "this",
    "msg",
    "block",
    "tx",
    "true",
    "false",
    "new",
    "delete",
    "contract",
    "internal",
    "external",
    "public",
    "private",
    "view",
    "pure",
    "payable",
    "memory",
    "storage",
    "calldata",
    "constant",
    "immutable",
    "struct",
    "enum",
    "type",
    "is",
];

fn usable(name: &str) -> bool {
    let mut cs = name.chars();
    cs.next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && cs.all(|c| c.is_ascii_alphanumeric() || c == '_')
        && !RESERVED.contains(&name)
        && name.len() <= 48
}

/// The names in use and the renaming of storage that still carries a default name.
struct Namer<'a> {
    storage: &'a mut [StorageVar],
    taken: HashSet<String>,
}

impl<'a> Namer<'a> {
    /// A variable may share its name with an external function, as a public variable does with
    /// its getter; it may not share one with another variable or with an internal function.
    fn new(storage: &'a mut [StorageVar], functions: &[Function]) -> Namer<'a> {
        let mut taken: HashSet<String> = functions
            .iter()
            .filter(|f| f.kind == FnKind::Internal)
            .map(|f| f.name.clone())
            .collect();
        for v in storage.iter() {
            taken.insert(v.name.clone());
            taken.extend(v.fields.iter().map(|f| f.name.clone()));
        }
        Namer { storage, taken }
    }

    /// Whether `t` exists and still has its default name. A mapping or array of structs is not
    /// named here: a store that looks like a write of the variable is a write of one member.
    fn unnamed(&self, t: Target) -> bool {
        match canonical(self.storage, t) {
            Target::Var(slot) => self.storage.iter().any(|v| {
                slot_of(v) == Some(slot)
                    && v.fields.is_empty()
                    && v.members.is_empty()
                    && v.name.starts_with("stor_")
            }),
            Target::Field(slot, offset, bits) => self.storage.iter().any(|v| {
                slot_of(v) == Some(slot)
                    && v.fields.iter().any(|f| {
                        f.offset == offset && f.bits == bits && f.name.starts_with("stor_")
                    })
            }),
            Target::Member(slot, at, byte, bits) => self.storage.iter().any(|v| {
                slot_of(v) == Some(slot)
                    && v.members.iter().any(|m| {
                        m.offset == at
                            && !m.holds_many()
                            && match m.fields.is_empty() {
                                true => m.name.starts_with("field"),
                                false => m.fields.iter().any(|f| {
                                    f.offset == byte
                                        && f.bits == bits
                                        && f.name.starts_with("field")
                                }),
                            }
                    })
            }),
        }
    }

    /// Give `t` the name, if it is still unnamed and the name is free.
    fn name(&mut self, t: Target, name: &str) -> bool {
        if !usable(name) || self.taken.contains(name) || !self.unnamed(t) {
            return false;
        }
        let t = canonical(self.storage, t);
        for v in self.storage.iter_mut() {
            match t {
                Target::Var(slot) if slot_of(v) == Some(slot) => v.name = name.to_string(),
                Target::Field(slot, offset, bits) if slot_of(v) == Some(slot) => {
                    for f in v.fields.iter_mut() {
                        if f.offset == offset && f.bits == bits {
                            f.name = name.to_string();
                        }
                    }
                }
                Target::Member(slot, at, byte, bits) if slot_of(v) == Some(slot) => {
                    for m in v.members.iter_mut().filter(|m| m.offset == at) {
                        match m.fields.is_empty() {
                            true => m.name = name.to_string(),
                            false => {
                                for f in m.fields.iter_mut() {
                                    if f.offset == byte && f.bits == bits {
                                        f.name = name.to_string();
                                    }
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        self.taken.insert(name.to_string());
        true
    }

    /// The suffix of a default name: `3` for `stor_3`.
    fn suffix(&self, t: Target) -> Option<String> {
        let t = canonical(self.storage, t);
        self.storage.iter().find_map(|v| match t {
            Target::Var(slot) if slot_of(v) == Some(slot) => {
                v.name.strip_prefix("stor_").map(str::to_string)
            }
            Target::Field(slot, offset, bits) if slot_of(v) == Some(slot) => v
                .fields
                .iter()
                .find(|f| f.offset == offset && f.bits == bits)
                .and_then(|f| f.name.strip_prefix("stor_").map(str::to_string)),
            _ => None,
        })
    }
}

/// Mappings some function both lowers and raises by one key: a ledger whose entries are
/// balances moved between parties.
fn ledger_roots(all: &BTreeMap<usize, Facts>) -> BTreeSet<U256> {
    let mut out = BTreeSet::new();
    for facts in all.values() {
        for m in facts
            .movements
            .iter()
            .filter(|m| m.keys.len() == 1 && !m.credit)
        {
            let paired = facts
                .movements
                .iter()
                .any(|c| c.credit && c.root == m.root && c.keys.len() == 1);
            if paired {
                out.insert(m.root);
            }
        }
    }
    out
}

/// Name storage variables and struct members that still have a default name: by the one
/// variable a setter writes (the plainest setter name wins where several write it), by the one
/// variable written where a change event is emitted, then by role.
pub fn name_storage(
    functions: &[Function],
    storage: &mut [StorageVar],
    layout: MappingLayout,
    use_sigs: bool,
) {
    let all = all_facts(functions, layout, use_sigs);
    let mut namer = Namer::new(storage, functions);
    let written = |pcs: &[usize]| -> BTreeSet<Target> {
        pcs.iter()
            .filter_map(|pc| all.get(pc))
            .flat_map(|f| f.stores.iter().map(|(t, _)| *t))
            .collect()
    };

    if use_sigs {
        let mut setters: Vec<(String, Target)> = Vec::new();
        for f in functions.iter().filter(|f| f.kind == FnKind::External) {
            let Some(stem) = f
                .signature
                .as_deref()
                .map(sigs::name_of)
                .and_then(setter_stem)
            else {
                continue;
            };
            let targets = written(&reach(f.pc, &all));
            if let [t] = targets.iter().copied().collect::<Vec<_>>()[..] {
                setters.push((stem, t));
            }
        }
        setters.sort_by(|a, b| (a.0.len(), &a.0).cmp(&(b.0.len(), &b.0)));
        for (stem, t) in setters {
            namer.name(t, &stem);
        }
        for (pc, facts) in &all {
            let stems: BTreeSet<String> =
                facts.events.iter().filter_map(|e| event_stem(e)).collect();
            let targets = written(&[*pc]);
            if let ([stem], [t]) = (
                &stems.into_iter().collect::<Vec<_>>()[..],
                &targets.into_iter().collect::<Vec<_>>()[..],
            ) {
                namer.name(*t, stem);
            }
        }
    }

    let externals: Vec<usize> = functions
        .iter()
        .filter(|f| f.kind == FnKind::External)
        .map(|f| f.pc)
        .collect();

    let mut guarded: BTreeMap<Target, usize> = BTreeMap::new();
    for pc in &externals {
        let targets: BTreeSet<Target> = reach(*pc, &all)
            .iter()
            .filter_map(|p| all.get(p))
            .flat_map(|f| f.caller_guards.iter().copied())
            .collect();
        for t in targets {
            *guarded.entry(t).or_default() += 1;
        }
    }
    let owners: Vec<Target> = guarded
        .iter()
        .filter(|(_, n)| **n >= 2)
        .map(|(t, _)| *t)
        .collect();
    if let [t] = owners[..] {
        namer.name(t, "owner");
    }

    let mut constants: BTreeMap<Target, Option<BTreeSet<U256>>> = BTreeMap::new();
    for facts in all.values() {
        for (t, val) in &facts.stores {
            let entry = constants.entry(*t).or_insert_with(|| Some(BTreeSet::new()));
            match (expr::as_const(*val), entry.as_mut()) {
                (Some(c), Some(set)) => {
                    set.insert(c);
                }
                _ => *entry = None,
            }
        }
    }
    let mut toggled: BTreeMap<Target, usize> = BTreeMap::new();
    for pc in &externals {
        let mut per: BTreeMap<Target, BTreeSet<U256>> = BTreeMap::new();
        for p in reach(*pc, &all) {
            for (t, val) in all.get(&p).map(|f| f.stores.as_slice()).unwrap_or_default() {
                if let Some(c) = expr::as_const(*val) {
                    per.entry(*t).or_default().insert(c);
                }
            }
        }
        for (t, values) in per {
            if values.len() == 2 {
                *toggled.entry(t).or_default() += 1;
            }
        }
    }
    let locks: Vec<Target> = toggled
        .iter()
        .filter(|(t, n)| {
            **n >= 2
                && matches!(t, Target::Var(_))
                && constants
                    .get(*t)
                    .is_some_and(|c| c.as_ref().is_some_and(|set| set.len() == 2))
        })
        .map(|(t, _)| *t)
        .collect();
    if let [t] = locks[..] {
        namer.name(t, "reentrancyLock");
    }

    let ledgers = ledger_roots(&all);
    let mut allowances: BTreeSet<U256> = BTreeSet::new();
    for facts in all.values() {
        for m in &facts.movements {
            if m.keys.len() == 2 && !m.credit && is_caller(m.keys[1]) {
                allowances.insert(m.root);
            }
        }
    }
    if let [root] = ledgers.iter().copied().collect::<Vec<_>>()[..] {
        namer.name(Target::Var(root), "balances");
        let mut supplies: BTreeSet<U256> = BTreeSet::new();
        for facts in all.values() {
            let one_sided: Vec<&Movement> = facts
                .movements
                .iter()
                .filter(|m| m.root == root && m.keys.len() == 1)
                .filter(|m| {
                    !facts
                        .movements
                        .iter()
                        .any(|o| o.root == root && o.keys.len() == 1 && o.credit != m.credit)
                })
                .collect();
            for (slot, amount, grew) in &facts.scalar_moves {
                if one_sided
                    .iter()
                    .any(|m| m.amount == *amount && m.credit == *grew)
                {
                    supplies.insert(*slot);
                }
            }
        }
        if let [slot] = supplies.iter().copied().collect::<Vec<_>>()[..] {
            namer.name(Target::Var(slot), "totalSupply");
        }
    }
    if let [root] = allowances.iter().copied().collect::<Vec<_>>()[..] {
        namer.name(Target::Var(root), "allowances");
    }

    let mut clock: BTreeMap<Target, Option<u8>> = BTreeMap::new();
    for facts in all.values() {
        for (t, val) in &facts.stores {
            let source = match expr::node(*val) {
                Node::Env(o @ (op::TIMESTAMP | op::NUMBER), _) => Some(o),
                _ => None,
            };
            clock
                .entry(*t)
                .and_modify(|c| {
                    if *c != source {
                        *c = None;
                    }
                })
                .or_insert(source);
        }
    }
    for (t, source) in clock {
        let (Some(source), Some(suffix)) = (source, namer.suffix(t)) else {
            continue;
        };
        let base = if source == op::TIMESTAMP {
            "timestamp"
        } else {
            "blockNumber"
        };
        namer.name(t, &format!("{base}_{suffix}"));
    }
}

/// `t` as the layout declares it: a write through a mask to a slot that holds one variable is
/// that variable, and a whole-word read of a packed slot's first field is that field.
fn canonical(storage: &[StorageVar], t: Target) -> Target {
    let var = |slot: U256| storage.iter().find(|v| slot_of(v) == Some(slot));
    match t {
        Target::Field(slot, 0, _) if var(slot).is_some_and(|v| v.fields.is_empty()) => {
            Target::Var(slot)
        }
        Target::Var(slot) => var(slot)
            .and_then(|v| v.fields.iter().find(|f| f.offset == 0))
            .map_or(t, |f| Target::Field(slot, 0, f.bits)),
        Target::Member(slot, 0, _, _) if var(slot).is_some_and(|v| v.members.is_empty()) => {
            Target::Var(slot)
        }
        Target::Member(slot, at, _, _)
            if var(slot)
                .and_then(|v| v.members.iter().find(|m| m.offset == at))
                .is_some_and(|m| m.fields.is_empty()) =>
        {
            Target::Member(slot, at, 0, 256)
        }
        other => other,
    }
}

/// The printed name of a variable or field.
fn label_in(storage: &[StorageVar], t: Target) -> Option<String> {
    let t = canonical(storage, t);
    storage.iter().find_map(|v| match t {
        Target::Var(slot) if slot_of(v) == Some(slot) => Some(v.name.clone()),
        Target::Field(slot, offset, bits) if slot_of(v) == Some(slot) => v
            .fields
            .iter()
            .find(|f| f.offset == offset && f.bits == bits)
            .map(|f| f.name.clone()),
        Target::Member(slot, at, byte, bits) if slot_of(v) == Some(slot) => {
            let member = v.members.iter().find(|m| m.offset == at)?;
            match member.fields.is_empty() {
                true => Some(member.name.clone()),
                false => member
                    .fields
                    .iter()
                    .find(|f| f.offset == byte && f.bits == bits)
                    .map(|f| f.name.clone()),
            }
        }
        _ => None,
    })
}

/// Name internal functions that still have a default name by what their own statements do.
pub fn name_helpers(
    functions: &mut [Function],
    storage: &[StorageVar],
    layout: MappingLayout,
    use_sigs: bool,
) {
    let all = all_facts(functions, layout, use_sigs);
    let default_member = |n: &str| {
        n.strip_prefix("field")
            .is_some_and(|rest| rest.starts_with(|c: char| c.is_ascii_digit()))
    };
    let named =
        |t: Target| label_in(storage, t).filter(|n| !n.starts_with("stor_") && !default_member(n));
    let mut taken: HashSet<String> = functions.iter().map(|f| f.name.clone()).collect();
    taken.extend(storage.iter().map(|v| v.name.clone()));
    let mut order: Vec<usize> = (0..functions.len()).collect();
    order.sort_by_key(|i| functions[*i].pc);
    for i in order {
        let f = &functions[i];
        if f.kind != FnKind::Internal || f.inlined || !f.name.starts_with("func_0x") {
            continue;
        }
        let Some(facts) = all.get(&f.pc) else {
            continue;
        };
        let writes: BTreeSet<Target> = facts.stores.iter().map(|(t, _)| *t).collect();
        let quiet = facts.stores.is_empty()
            && facts.events.is_empty()
            && !facts.unknown_event
            && facts.calls.is_empty()
            && !facts.unknown_call
            && !facts.sends_value;
        let one = |set: &BTreeSet<String>| -> Option<String> {
            (set.len() == 1)
                .then(|| set.iter().next().cloned())
                .flatten()
        };
        let base = if quiet && facts.callees.is_empty() && facts.caller_guards.len() == 1 {
            let t = *facts.caller_guards.iter().next().expect("one guard");
            Some(match named(t) {
                Some(n) => format!("_only{}", upper_first(&n)),
                None => "_onlyAuthorized".to_string(),
            })
        } else if let (Some(event), false) = (one(&facts.events), facts.unknown_event) {
            Some(
                if facts.stores.is_empty() && facts.calls.is_empty() && !facts.unknown_call {
                    format!("_emit{event}")
                } else {
                    format!("_{}", lower_first(&event))
                },
            )
        } else if !facts.events.is_empty() || facts.unknown_event {
            None
        } else if let (Some(call), false, true) = (
            one(&facts.calls),
            facts.unknown_call,
            facts.stores.is_empty(),
        ) {
            Some(format!("_call{}", upper_first(&call)))
        } else if !facts.calls.is_empty() || facts.unknown_call {
            None
        } else if facts.sends_value && facts.stores.is_empty() {
            Some("_sendValue".to_string())
        } else if let [t] = writes.iter().copied().collect::<Vec<_>>()[..] {
            named(t).map(|n| format!("_set{}", upper_first(&n)))
        } else {
            None
        };
        let Some(base) = base.filter(|b| usable(b)) else {
            continue;
        };
        let name = (1..)
            .map(|n| {
                if n == 1 {
                    base.clone()
                } else {
                    format!("{base}_{n}")
                }
            })
            .find(|n| !taken.contains(n))
            .expect("some suffix is free");
        taken.insert(name.clone());
        functions[i].name = name;
    }
}

/// How a function uses one of its inputs, strongest first.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Role {
    /// Key of a ledger entry that is lowered.
    From,
    /// Key of a ledger entry that is raised.
    To,
    /// The amount an entry or a counter moves by.
    Amount,
    /// Compared with the block timestamp in a guard.
    Deadline,
    /// The recovery byte given to `ecrecover`.
    SigV,
    /// The first half of a signature given to `ecrecover`.
    SigR,
    /// The second half of a signature given to `ecrecover`.
    SigS,
    /// The hash given to `ecrecover`.
    Digest,
    /// Address ether is sent to, or the beneficiary of a self-destruct.
    Recipient,
    /// Address a call is made on.
    Target,
    /// Key of a mapping entry that is written or read.
    Account,
}

impl Role {
    /// The name for an input of Solidity type `ty`, or `None` when the type does not fit the
    /// role: only an address is a party to a transfer or a call target, only an unsigned
    /// integer an amount or a deadline. A mapping key that is not an address is a `key`.
    fn name_for(self, ty: &str) -> Option<&'static str> {
        let address = ty.starts_with("address");
        let unsigned = ty.starts_with("uint");
        match self {
            Role::From => address.then_some("from"),
            Role::To => address.then_some("to"),
            Role::Recipient => address.then_some("recipient"),
            Role::Target => address.then_some("target"),
            Role::Account if address => Some("account"),
            Role::Account => Some("key"),
            Role::Amount => unsigned.then_some("amount"),
            Role::Deadline => unsigned.then_some("deadline"),
            Role::SigV => Some("v"),
            Role::SigR => Some("r"),
            Role::SigS => Some("s"),
            Role::Digest => Some("digest"),
        }
    }
}

/// An input of a function: a calldata head word, or a parameter of an internal function in
/// declaration order.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Input {
    Word(u32),
    Param(u32),
}

/// What is known about one input: its strongest role, and where it is stored as it is.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Use {
    role: Option<Role>,
    /// The scalar variable or field the input is stored into unchanged.
    variable: Option<Target>,
    /// The input is stored unchanged somewhere: a variable, a mapping entry, an array.
    stored: bool,
}

impl Use {
    fn take_role(&mut self, role: Role) {
        if self.role.is_none_or(|r| role < r) {
            self.role = Some(role);
        }
    }

    fn merge(&mut self, other: Use) {
        if let Some(role) = other.role {
            self.take_role(role);
        }
        self.variable = self.variable.or(other.variable);
        self.stored |= other.stored;
    }
}

fn input_of(e: ExprId, arity: usize) -> Option<Input> {
    let mut e = unmask(e);
    if let Node::Op(op::ISZERO, v) = expr::node(e) {
        if let Node::Op(op::ISZERO, w) = expr::node(v[0]) {
            e = unmask(w[0]);
        }
    }
    match expr::node(e) {
        Node::CallDataLoad(off) => emit::calldata_word_index(off).map(Input::Word),
        Node::Arg(slot) => (slot as usize)
            .checked_add(1)
            .and_then(|s| arity.checked_sub(s))
            .map(|i| Input::Param(i as u32)),
        _ => None,
    }
}

/// What the statements of `l` say about its inputs. `callee` gives what is already known for
/// an internal function's parameters, so a value passed on takes the use it has there.
fn uses(
    l: &Lifted,
    layout: MappingLayout,
    ledgers: &BTreeSet<U256>,
    arity_of: &dyn Fn(usize) -> Option<usize>,
    callee: &BTreeMap<usize, BTreeMap<Input, Use>>,
) -> BTreeMap<Input, Use> {
    let arity = ssa::arity(l);
    let mut out: BTreeMap<Input, Use> = BTreeMap::new();
    let mut note = |e: ExprId, f: &dyn Fn(&mut Use)| {
        if let Some(input) = input_of(e, arity) {
            f(out.entry(input).or_default());
        }
    };
    let mut seen: HashSet<ExprId> = HashSet::new();
    for nd in &l.nodes {
        let mut stack = crate::lift::node_exprs(nd);
        while let Some(x) = stack.pop() {
            if !seen.insert(x) || seen.len() > 50_000 {
                continue;
            }
            if let Node::SLoad(key, false, _) = expr::node(x) {
                if let Some(path) = ssa::slot_path(key, layout) {
                    for step in &path.steps {
                        if let Step::Key(k) = step {
                            note(*k, &|u| u.take_role(Role::Account));
                        }
                    }
                }
            }
            stack.extend(expr::children(x));
        }
        if let Term::Branch { cond, .. } = &nd.term {
            let mut c = *cond;
            while let Node::Op(op::ISZERO, v) = expr::node(c) {
                c = v[0];
            }
            if let Node::Op(op::LT | op::GT, v) = expr::node(c) {
                for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
                    if matches!(expr::node(b), Node::Env(op::TIMESTAMP, _)) {
                        note(a, &|u| u.take_role(Role::Deadline));
                    }
                }
            }
        }
        if let Term::SelfDestruct(to) = &nd.term {
            note(*to, &|u| u.take_role(Role::Recipient));
        }
        for st in &nd.stmts {
            match st {
                Stmt::SStore {
                    key,
                    val,
                    transient: false,
                    ..
                } => {
                    let Some(path) = ssa::slot_path(*key, layout) else {
                        continue;
                    };
                    let entry =
                        |e: ExprId| matches!(expr::node(e), Node::SLoad(k, false, _) if k == *key);
                    let moved = match expr::node(*val) {
                        Node::Op(op::SUB, v) if entry(v[0]) => Some((v[1], Role::From)),
                        Node::Op(op::ADD, v) if entry(v[0]) => Some((v[1], Role::To)),
                        Node::Op(op::ADD, v) if entry(v[1]) => Some((v[0], Role::To)),
                        _ => None,
                    };
                    let ledger =
                        ledgers.contains(&path.root) && matches!(path.steps[..], [Step::Key(_)]);
                    for step in &path.steps {
                        if let Step::Key(k) = step {
                            let role = match moved {
                                Some((_, side)) if ledger => side,
                                _ => Role::Account,
                            };
                            note(*k, &|u| u.take_role(role));
                        }
                    }
                    match moved {
                        Some((amount, _)) => note(amount, &|u| u.take_role(Role::Amount)),
                        None => {
                            let scalar = path.steps.is_empty();
                            let variable =
                                scalar.then(|| store_target(*key, *val, layout)).flatten();
                            let value = ssa::field_write(*key, *val).map_or(*val, |w| w.value);
                            note(value, &|u| {
                                u.stored = true;
                                u.variable = u.variable.or(variable);
                            });
                        }
                    }
                }
                Stmt::Call {
                    addr,
                    value,
                    input,
                    input_head,
                    in_len,
                    ..
                } => {
                    if expr::as_const(*addr) == Some(U256::ONE) {
                        let words: &[ExprId] = input.as_deref().unwrap_or(input_head);
                        let parts = [Role::Digest, Role::SigV, Role::SigR, Role::SigS];
                        for (w, role) in words.iter().zip(parts) {
                            note(*w, &|u| u.take_role(role));
                        }
                        continue;
                    }
                    let empty = expr::as_const(*in_len) == Some(U256::ZERO);
                    let pays = value.is_some_and(|v| expr::as_const(v) != Some(U256::ZERO));
                    let role = if empty && pays {
                        Role::Recipient
                    } else {
                        Role::Target
                    };
                    note(*addr, &|u| u.take_role(role));
                }
                _ => {}
            }
        }
    }
    for site in ssa::call_sites(l, arity_of) {
        let Some(theirs) = callee.get(&site.callee) else {
            continue;
        };
        for (index, val) in site.args {
            if let Some(known) = theirs.get(&Input::Param(index)) {
                note(val, &|u| u.merge(*known));
            }
        }
    }
    out
}

/// Name parameters that still have a default name by what the code does with them: the name of
/// the variable an input is stored into, else its role. Two inputs with the same name are
/// numbered; a name a storage variable already has gets a trailing underscore, so a parameter
/// never reads as the variable. An input stored somewhere without a name of its own is a
/// `value` only when nothing better is known and it is the function's only such input.
pub fn name_params(functions: &mut [Function], storage: &[StorageVar], layout: MappingLayout) {
    let arities: HashMap<usize, usize> = functions
        .iter()
        .filter_map(|f| f.lifted.as_ref().map(|l| (f.pc, ssa::arity(l))))
        .collect();
    let arity_of = |pc: usize| arities.get(&pc).copied();
    let ledgers = ledger_roots(&all_facts(functions, layout, false));
    let mut known: BTreeMap<usize, BTreeMap<Input, Use>> = BTreeMap::new();
    for _ in 0..4 {
        let mut next = BTreeMap::new();
        for f in functions.iter() {
            if let Some(l) = &f.lifted {
                next.insert(f.pc, uses(l, layout, &ledgers, &arity_of, &known));
            }
        }
        if next == known {
            break;
        }
        known = next;
    }
    let mut reserved: HashSet<String> = storage.iter().map(|v| v.name.clone()).collect();
    for v in storage {
        reserved.extend(v.fields.iter().map(|f| f.name.clone()));
    }
    reserved.extend(functions.iter().map(|f| f.name.clone()));
    let variable_name = |u: &Use| {
        u.variable
            .and_then(|t| label_in(storage, t))
            .filter(|n| !n.starts_with("stor_"))
            .map(|n| format!("new{}", upper_first(&n)))
    };
    for f in functions.iter_mut() {
        let Some(mine) = known.get(&f.pc) else {
            continue;
        };
        let external = match f.kind {
            FnKind::External => true,
            FnKind::Internal => false,
            _ => continue,
        };
        let multiword = f.signature.as_deref().is_some_and(|s| {
            sigs::params_of(s)
                .iter()
                .any(|p| p.starts_with('(') || (p.ends_with(']') && !p.ends_with("[]")))
        });
        if multiword {
            continue;
        }
        let choice = |p: &crate::function::Param| -> Option<String> {
            let input = if external {
                Input::Word(p.index)
            } else {
                Input::Param(p.index)
            };
            let u = mine.get(&input)?;
            variable_name(u).or_else(|| u.role.and_then(|r| r.name_for(&p.ty)).map(str::to_string))
        };
        let plain: Vec<u32> = f
            .params
            .iter()
            .filter(|p| choice(p).is_none())
            .filter(|p| !p.ty.starts_with("address"))
            .filter(|p| {
                let input = if external {
                    Input::Word(p.index)
                } else {
                    Input::Param(p.index)
                };
                mine.get(&input).is_some_and(|u| u.stored)
            })
            .map(|p| p.index)
            .collect();
        let mut used: HashSet<String> = f.params.iter().map(|p| p.name.clone()).collect();
        for i in 0..f.params.len() {
            let p = &f.params[i];
            if p.name != format!("arg{}", p.index) {
                continue;
            }
            let base = match choice(p) {
                Some(name) => name,
                None if plain == [p.index] => "value".to_string(),
                None => continue,
            };
            let name = (1..)
                .map(|n| match (n, reserved.contains(&base)) {
                    (1, false) => base.clone(),
                    (1, true) => format!("{base}_"),
                    (n, _) => format!("{base}{n}"),
                })
                .find(|n| !used.contains(n) && !reserved.contains(n))
                .expect("some name is free");
            used.insert(name.clone());
            f.params[i].name = name;
        }
    }
}
