use crate::compiler;
use crate::cross::World as CrossWorld;
use crate::decompile::{self, Contract, Function};
use crate::emit::{self, Names, SlotSpace};
use crate::exec;
use crate::expr::{self, ExprId, Node};
use crate::function::FnKind;
use crate::lift::{self, Lifted, Stmt, Term};
use crate::opcode as op;
use crate::origin::{self, Model};
use crate::sigs;
use crate::ssa;
use crate::type_rules;
use crate::u256::U256;
use serde::Serialize;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    Critical,
    High,
    Medium,
    Low,
    Info,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Confidence {
    High,
    Medium,
    Low,
}

#[derive(Clone, Debug, Serialize)]
pub struct Finding {
    pub id: String,
    pub title: String,
    pub severity: Severity,
    pub confidence: Confidence,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub function: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub pc: Option<usize>,
    pub description: String,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub evidence: Vec<String>,
    pub recommendation: String,
    #[serde(skip_serializing_if = "is_one")]
    pub sites: usize,
    #[serde(skip_serializing_if = "std::ops::Not::not", default)]
    pub confirmed: bool,
    #[serde(skip_serializing_if = "Option::is_none", default)]
    pub witness: Option<String>,
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub setup: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub observed: Vec<String>,
}

impl Finding {
    pub fn confirm(&mut self, path: &crate::path::Path) {
        self.confirmed = true;
        self.witness = Some(crate::hex::encode(&path.inputs.calldata));
        self.observed = crate::evidence::observed(&path.inputs, &path.run);
    }
}

fn is_one(n: &usize) -> bool {
    *n == 1
}

#[derive(Clone, Debug, Serialize, Default)]
pub struct Report {
    pub contract_kind: Vec<String>,
    pub findings: Vec<Finding>,
    pub privileged_functions: Vec<String>,
    pub unauthenticated_state_changers: Vec<String>,
    pub external_calls: Vec<String>,
    pub summary: BTreeMap<String, usize>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub summaries: Vec<FnSummary>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub maps: Vec<Section>,
    pub risk_score: u32,
}

#[derive(Clone, Debug, Default, Serialize, PartialEq, Eq)]
pub struct Section {
    pub title: String,
    pub lines: Vec<String>,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct ParamUse {
    pub word: u32,
    pub line: String,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct ParamStore {
    pub word: u32,
    pub slot: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub base: Option<u32>,
    pub gates: bool,
    pub line: String,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct RelativeSlot {
    pub base: u32,
    pub offset: String,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct ParamForward {
    pub word: u32,
    pub arg: u32,
    pub target: String,
    pub selector: String,
    pub line: String,
}

#[derive(Clone, Debug, Serialize, Default, PartialEq, Eq)]
pub struct FnSummary {
    pub function: String,
    pub selector: String,
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub gated: bool,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub gate_slots: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub gate_roles: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub gate_relative: Vec<RelativeSlot>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub creates: Option<String>,
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub signed: bool,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub bound: Vec<u32>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub lowers: Vec<ParamUse>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub pays: Vec<ParamUse>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub stores: Vec<ParamStore>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub forwards: Vec<ParamForward>,
    #[serde(skip)]
    pub(crate) returns: Option<ExprId>,
}

fn stmt_exprs(s: &Stmt) -> Vec<ExprId> {
    lift::node_exprs(&lift::LNode {
        id: 0,
        block: 0,
        pc: 0,
        stmts: vec![s.clone()],
        term: Term::Stop,
        preds: vec![],
        succs: vec![],
        entry_stack: vec![],
        exit_stack: vec![],
    })
}

fn term_exprs(t: &Term) -> Vec<ExprId> {
    lift::node_exprs(&lift::LNode {
        id: 0,
        block: 0,
        pc: 0,
        stmts: vec![],
        term: t.clone(),
        preds: vec![],
        succs: vec![],
        entry_stack: vec![],
        exit_stack: vec![],
    })
}

fn event_exprs(e: &Event) -> Vec<ExprId> {
    let mut v = e.stmt.as_ref().map(stmt_exprs).unwrap_or_default();
    if let Some(t) = &e.term {
        v.extend(term_exprs(t));
    }
    v
}

fn contains_expr(e: ExprId, target: ExprId) -> bool {
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if x == target {
            return true;
        }
        if !seen.insert(x) || seen.len() > 5000 {
            continue;
        }
        stack.extend(expr::children(x));
    }
    false
}

fn mentions_returndata(e: ExprId, seq: u32) -> bool {
    mentions(e, &|n| matches!(n, Node::ReturnData(s, _) if *s == seq))
}

const SEL_TRANSFER: u32 = 0xa9059cbb;
const SEL_TRANSFER_FROM: u32 = 0x23b872dd;
const SEL_SYNC: u32 = 0xfff6cae9;
const SEL_SKIM: u32 = 0xbc25cf77;
const SEL_GET_RESERVES: u32 = 0x0902f1ac;
const SEL_TOKEN0: u32 = 0x0dfe1681;
const SEL_TOKEN1: u32 = 0xd21220a7;
// Secondary evidence only. A rule must still fire without this list.
const POOL_SELECTORS: &[u32] = &[
    SEL_SYNC,
    SEL_SKIM,
    SEL_GET_RESERVES,
    SEL_TOKEN0,
    SEL_TOKEN1,
    0x3850c7bd,
    0x1a686502,
    0x128acb08,
    0x3c8a7d8d,
    0xa34123a7,
    0x4f1eb3d8,
    0x883bdbfd,
    0x48c89491,
    0x11da60b4,
    0x0b0d9c09,
    0x5a6bcfda,
    0xf3cd914c,
    0x5e0d443f,
    0x3df02124,
    0x0b4c7e4d,
    0x5b36389c,
    0x52bbbe29,
    0xb95cac28,
    0x8bdb3913,
    0xf6c00927,
];
const SEL_APPROVE: u32 = 0x095ea7b3;
const SEL_BALANCE_OF: u32 = 0x70a08231;
const SEL_LATEST_ROUND_DATA: u32 = 0xfeaf968c;
const SEL_LATEST_ANSWER: u32 = 0x50d25bcd;
const CALLBACK_SELECTORS: &[u32] = &[
    0x42842e0e, 0xb88d4fde, 0xf242432a, 0x2eb2c2d6, 0x150b7a02, 0xf23a6e61, 0xbc197c81, 0x0023de29,
    0x9bd9bbc6, 0x62ad1b83,
];
const SECP_HALF_ORDER: &str = "7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a0";

// Helpers that call helpers multiply. Ordinary functions stay under 9,000 events.
const MAX_INLINED_EVENTS: usize = 12_000;

#[derive(Clone)]
struct Event {
    node: usize,
    pc: usize,
    callee: Option<usize>,
    inst: usize,
    inner: usize,
    path: Vec<(usize, Option<usize>, usize)>,
    stmt: Option<Stmt>,
    term: Option<Term>,
    in_loop: bool,
}

struct Ctx<'a> {
    c: &'a Contract,
    world: &'a World<'a>,
    computed_returns: RefCell<HashMap<u32, ExprId>>,
    made: RefCell<HashMap<ExprId, String>>,
    code_copies: RefCell<Vec<(ExprId, usize, usize)>>,
    internals: HashMap<usize, &'a Function>,
    version: Option<(u32, u32, u32)>,
    vyper: bool,
    callee_writes: RefCell<HashMap<usize, Option<MemWrites>>>,
    inst_seq: std::cell::Cell<usize>,
    inline_left: std::cell::Cell<usize>,
    divides: RefCell<HashMap<usize, bool>>,
    roles: HashSet<U256>,
    slot_writes: HashSet<U256>,
    field_writes: HashSet<(U256, u32, u32)>,
    transient_storage: bool,
    calldata_copies: bool,
    unguarded_extenders: HashMap<U256, Vec<String>>,
}

type MemWrites = Vec<(ExprId, Option<u64>)>;

struct FnFacts {
    name: String,
    selector: Option<String>,
    pc: usize,
    external: bool,
    state_changing: bool,
    caller_checked: bool,
    auth_slots: Vec<(ExprId, String)>,
    const_writes: Vec<(ExprId, WriteSource, String)>,
    ether_out: Vec<(ExprId, ExprId, String)>,
    selfdestructs: Vec<(ExprId, String)>,
    delegatecalls: Vec<(ExprId, String)>,
    time_gated: bool,
    init_guarded: bool,
    stored_callees: Vec<StoredCall>,
    debits: Vec<Debit>,
    allowance_of: Vec<ExprId>,
    syncs: Vec<PairSync>,
    factory_slots: Vec<ExprId>,
    compared_slots: Vec<ExprId>,
    ledger_reads: Vec<(U256, ExprId)>,
    account_authorised: bool,
    signature_authorised: bool,
    avail_bounds: Vec<AvailBound>,
    ref_bounds: Vec<AvailBound>,
    moves_value: bool,
    linked_calls: Vec<LinkedCall>,
    ledger_writes: Vec<LedgerWrite>,
    total_changes: Vec<(ExprId, Change)>,
    stale_moves: Vec<StaleMove>,
    surplus_moves: Vec<SurplusMove>,
}

#[derive(Clone, Debug)]
struct StoredCall {
    slot: ExprId,
    selector: Option<u32>,
    is_static: bool,
    passes_sender: bool,
    line: String,
}

#[derive(Clone, Debug)]
struct Debit {
    root: U256,
    key: ExprId,
    account_text: String,
    line: String,
}

#[derive(Clone, Debug)]
struct LinkedCall {
    address: String,
    selector: Option<u32>,
    sends_value: bool,
    approval: bool,
    line: String,
}

struct World<'a> {
    members: HashMap<String, &'a Contract>,
    // None marks a contract whose analysis is under way.
    // It stops two contracts that call each other from recursing forever.
    reports: RefCell<HashMap<String, Option<Rc<Report>>>>,
}

impl<'a> World<'a> {
    fn of(root: &'a Contract) -> World<'a> {
        let mut members = HashMap::new();
        let mut work = vec![root];
        while let Some(c) = work.pop() {
            if let Some(a) = &c.address {
                members.entry(a.to_ascii_lowercase()).or_insert(c);
            }
            let creator = c.address.as_deref().unwrap_or_default();
            for made in &c.embedded {
                if let Some((offset, _)) = made.region {
                    members.entry(created_key(creator, offset)).or_insert(made);
                }
            }
            work.extend(c.linked.iter());
        }
        World {
            members,
            reports: RefCell::new(HashMap::new()),
        }
    }

    fn has_other(&self, c: &Contract) -> bool {
        self.members.values().any(|m| !std::ptr::eq(*m, c))
    }

    fn contract(&self, address: &str) -> Option<&'a Contract> {
        let address = address.strip_suffix(CLONE).unwrap_or(address);
        self.members.get(&address.to_ascii_lowercase()).copied()
    }

    fn report(&self, address: &str) -> Option<Rc<Report>> {
        let key = address
            .strip_suffix(CLONE)
            .unwrap_or(address)
            .to_ascii_lowercase();
        if let Some(known) = self.reports.borrow().get(&key) {
            return known.clone();
        }
        let c = self.contract(&key)?;
        self.reports.borrow_mut().insert(key.clone(), None);
        let report = Rc::new(analyze_in(c, self));
        self.reports
            .borrow_mut()
            .insert(key, Some(Rc::clone(&report)));
        Some(report)
    }
}

fn created_key(creator: &str, offset: usize) -> String {
    format!("{}#{offset:#x}", creator.to_ascii_lowercase())
}

const CLONE: &str = "#clone";

fn describe(key: &str) -> String {
    if let Some(target) = key.strip_suffix(CLONE) {
        return format!("a clone of the contract at {target}, created in the same call");
    }
    match key.split_once('#') {
        Some(("", _)) => "a contract this one creates".to_string(),
        Some((creator, _)) => format!("a contract that {creator} creates"),
        None => format!("the contract at {key}"),
    }
}

fn created_code(ctx: &Ctx, off: ExprId, len: ExprId, init: Option<&[ExprId]>) -> Option<String> {
    if let Some(target) = init.and_then(|words| decompile::clone_target(words, len)) {
        return Some(format!("{target}{CLONE}"));
    }
    let copies = ctx.code_copies.borrow();
    let held = |offset: usize| {
        ctx.c
            .embedded
            .iter()
            .any(|made| made.region.is_some_and(|r| r.0 == offset))
    };
    let (_, offset, _) = copies
        .iter()
        .rev()
        .find(|(dest, offset, _)| *dest == off && held(*offset))
        .or_else(|| copies.iter().rev().find(|(_, offset, _)| held(*offset)))?;
    Some(created_key(
        ctx.c.address.as_deref().unwrap_or_default(),
        *offset,
    ))
}

fn made_by_call(ctx: &Ctx, st: &Stmt) -> Option<String> {
    let Stmt::Call {
        addr,
        input,
        input_head,
        in_len,
        ..
    } = st
    else {
        return None;
    };
    if !ctx.world.has_other(ctx.c) {
        return None;
    }
    let words: &[ExprId] = input.as_deref().unwrap_or(input_head);
    let len = expr::as_const(*in_len).and_then(|l| l.as_usize());
    let selector = emit::leading_selector(*words.first()?, len)?;
    let address = linked_address(ctx, *addr)?;
    let report = ctx.world.report(&address)?;
    let hex = format!("{selector:#010x}");
    report
        .summaries
        .iter()
        .find(|g| g.selector.eq_ignore_ascii_case(&hex))?
        .creates
        .clone()
}

fn linked_address(ctx: &Ctx, e: ExprId) -> Option<String> {
    let e = unmask(e);
    if let Some(key) = ctx.made.borrow().get(&e) {
        return linked_contract(ctx, key).map(|_| key.to_ascii_lowercase());
    }
    let address = match expr::as_const(e) {
        Some(a) => a.to_hex_padded(20),
        None => {
            let slot = expr::as_const(ssa::stored_address_slot(e)?)?.to_hex_padded(32);
            let held = ctx
                .c
                .stored_targets
                .iter()
                .find(|(s, _)| s.eq_ignore_ascii_case(&slot))?;
            held.1.clone()
        }
    };
    linked_contract(ctx, &address).map(|_| address.to_ascii_lowercase())
}

fn linked_contract<'a>(ctx: &Ctx<'a>, address: &str) -> Option<&'a Contract> {
    ctx.world
        .contract(address)
        .filter(|lc| !std::ptr::eq(*lc, ctx.c))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Change {
    Up(ExprId),
    Down(ExprId),
    Set,
}

#[derive(Clone, Debug)]
struct LedgerWrite {
    root: U256,
    account: ExprId,
    change: Change,
    gen: u32,
    read_gen: Option<u32>,
    inst: usize,
    at: usize,
    in_loop: bool,
    line: String,
}

#[derive(Clone, Debug)]
struct StaleMove {
    lines: [String; 2],
}

#[derive(Clone, Debug)]
struct SurplusMove {
    surplus: Vec<String>,
    lines: Vec<String>,
}

fn change_of(val: ExprId, key: ExprId) -> (Change, Option<u32>) {
    let own = |e: ExprId| match expr::node(e) {
        Node::SLoad(k, false, g) if k == key => Some(g),
        _ => None,
    };
    match expr::node(val) {
        Node::Op(op::SUB, v) => match own(v[0]) {
            Some(g) => (Change::Down(v[1]), Some(g)),
            None => (Change::Set, None),
        },
        Node::Op(op::ADD, v) => match (own(v[0]), own(v[1])) {
            (Some(g), _) => (Change::Up(v[1]), Some(g)),
            (_, Some(g)) => (Change::Up(v[0]), Some(g)),
            _ => (Change::Set, None),
        },
        _ => (Change::Set, None),
    }
}

fn add_terms(e: ExprId, sign: i64, terms: &mut BTreeMap<ExprId, i64>, depth: u32) {
    match expr::node(e) {
        Node::Op(op::ADD, v) if depth < 16 => {
            add_terms(v[0], sign, terms, depth + 1);
            add_terms(v[1], sign, terms, depth + 1);
        }
        Node::Op(op::SUB, v) if depth < 16 => {
            add_terms(v[0], sign, terms, depth + 1);
            add_terms(v[1], -sign, terms, depth + 1);
        }
        _ => *terms.entry(e).or_insert(0) += sign,
    }
}

fn ledger_writes(
    events: &[Event],
    layout: emit::MappingLayout,
    names: &Names,
) -> (Vec<LedgerWrite>, Vec<(ExprId, Change)>) {
    let mut writes = Vec::new();
    let mut totals = Vec::new();
    for (at, ev) in events.iter().enumerate() {
        let Some(
            st @ Stmt::SStore {
                key,
                val,
                transient: false,
                gen,
            },
        ) = &ev.stmt
        else {
            continue;
        };
        let (change, read_gen) = change_of(*val, *key);
        if expr::is_const(*key) {
            totals.push((*key, change));
        } else if let Some((root, account)) = ledger_entry(*key, layout) {
            writes.push(LedgerWrite {
                root,
                account: unmask(account),
                change,
                gen: *gen,
                read_gen,
                inst: ev.inst,
                at,
                in_loop: ev.in_loop,
                line: emit::fmt_stmt(st, names),
            });
        }
    }
    (writes, totals)
}

fn stale_moves(ctx: &Ctx, l: &Lifted, events: &[Event], writes: &[LedgerWrite]) -> Vec<StaleMove> {
    let conds = guard_conds(events);
    let told_apart = |a: ExprId, b: ExprId| {
        conds.iter().any(|c| {
            mentions(*c, &|n| match n {
                Node::Op(op::EQ | op::SUB | op::XOR, v) => {
                    let (x, y) = (unmask(v[0]), unmask(v[1]));
                    (x == a && y == b) || (x == b && y == a)
                }
                _ => false,
            })
        })
    };
    let mut out = Vec::new();
    for (i, first) in writes.iter().enumerate() {
        for second in &writes[i + 1..] {
            let stale = first.root == second.root
                && first.inst == second.inst
                && first.account != second.account
                && matches!(first.change, Change::Down(_))
                && matches!(second.change, Change::Up(_))
                && first.gen < second.gen
                && second.read_gen.is_some_and(|g| g <= first.gen)
                && ev_reaches(ctx, l, &events[first.at], &events[second.at])
                && !told_apart(first.account, second.account);
            if stale {
                out.push(StaleMove {
                    lines: [first.line.clone(), second.line.clone()],
                });
            }
        }
    }
    out
}

fn surplus_moves(
    ctx: &Ctx,
    l: &Lifted,
    events: &[Event],
    writes: &[LedgerWrite],
    totals: &[(ExprId, Change)],
    names: &Names,
) -> Vec<SurplusMove> {
    if totals.iter().any(|(_, c)| matches!(c, Change::Up(_))) {
        return Vec::new();
    }
    let mut roots: Vec<U256> = writes.iter().map(|w| w.root).collect();
    roots.sort();
    roots.dedup();
    let mut out = Vec::new();
    for root in roots {
        let on: Vec<&LedgerWrite> = writes.iter().filter(|w| w.root == root).collect();
        let falls = on.iter().any(|w| matches!(w.change, Change::Down(_)));
        let plain = on.iter().all(|w| w.change != Change::Set && !w.in_loop);
        let chained = on
            .windows(2)
            .all(|w| ev_reaches(ctx, l, &events[w[0].at], &events[w[1].at]));
        if !falls || !plain || !chained {
            continue;
        }
        let mut terms: BTreeMap<ExprId, i64> = BTreeMap::new();
        for w in &on {
            match w.change {
                Change::Up(amount) => add_terms(amount, 1, &mut terms, 0),
                Change::Down(amount) => add_terms(amount, -1, &mut terms, 0),
                Change::Set => {}
            }
        }
        terms.retain(|_, n| *n != 0);
        if terms.is_empty() || terms.values().any(|n| *n < 0) {
            continue;
        }
        out.push(SurplusMove {
            surplus: terms.keys().map(|e| emit::fmt_expr(*e, names)).collect(),
            lines: on.iter().map(|w| w.line.clone()).collect(),
        });
    }
    out
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Field {
    shape: ssa::Shape,
    lo: u32,
    width: u32,
}

#[derive(Clone, Debug)]
struct AvailBound {
    added: BTreeSet<Field>,
    subbed: BTreeSet<Field>,
    names: HashMap<Field, String>,
    line: String,
}

#[derive(Clone, Debug)]
struct PairSync {
    target: String,
    after_mutation: bool,
    line: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum WriteSource {
    Calldata,
    Caller,
    Other,
}

fn write_source(val: ExprId) -> WriteSource {
    let keeps_old_bytes = |e: ExprId| {
        matches!(expr::node(e), Node::Op(op::AND, w)
            if w.iter().any(|x| matches!(expr::node(*x), Node::SLoad(..)))
                && w.iter().any(|x| expr::as_const(*x).is_some()))
    };
    let v = match expr::node(val) {
        Node::Op(op::OR, w) if keeps_old_bytes(w[1]) => w[0],
        Node::Op(op::OR, w) if keeps_old_bytes(w[0]) => w[1],
        _ => val,
    };
    let v = match expr::node(v) {
        Node::Op(op::AND, w) if expr::as_const(w[1]).is_some_and(|m| m.is_low_mask()) => w[0],
        Node::Op(op::AND, w) if expr::as_const(w[0]).is_some_and(|m| m.is_low_mask()) => w[1],
        _ => v,
    };
    match expr::node(v) {
        Node::CallDataLoad(_) | Node::CopiedWord(op::CALLDATACOPY, _, _) => WriteSource::Calldata,
        Node::Env(op::CALLER, _) => WriteSource::Caller,
        _ => WriteSource::Other,
    }
}

fn guard_conds(events: &[Event]) -> Vec<ExprId> {
    let mut out = Vec::new();
    for e in events {
        if let Some(Stmt::Require { cond, .. }) = &e.stmt {
            out.push(*cond);
        }
        if let Some(Term::Branch { cond, .. }) = &e.term {
            out.push(*cond);
        }
    }
    out
}

fn is_time_cond(cond: ExprId) -> bool {
    mentions(cond, &|n| {
        matches!(n, Node::Env(op::TIMESTAMP | op::NUMBER, _))
    })
}

fn reads_slot(e: ExprId, slot: ExprId) -> bool {
    mentions(e, &|n| matches!(n, Node::SLoad(k, false, _) if *k == slot))
}

fn collect_facts(
    ctx: &Ctx,
    f: &Function,
    events: &[Event],
    caller_checked: bool,
    names: &Names,
) -> FnFacts {
    let mut facts = FnFacts {
        name: display_name(f),
        selector: f.selector.clone(),
        pc: f.pc,
        external: f.kind == FnKind::External,
        state_changing: f.effects.writes_storage
            || f.effects.calls
            || f.effects.selfdestruct
            || f.effects.creates,
        caller_checked,
        auth_slots: Vec::new(),
        const_writes: Vec::new(),
        ether_out: Vec::new(),
        selfdestructs: Vec::new(),
        delegatecalls: Vec::new(),
        time_gated: false,
        init_guarded: false,
        stored_callees: Vec::new(),
        debits: Vec::new(),
        allowance_of: Vec::new(),
        syncs: Vec::new(),
        factory_slots: Vec::new(),
        compared_slots: Vec::new(),
        ledger_reads: Vec::new(),
        account_authorised: false,
        signature_authorised: false,
        avail_bounds: Vec::new(),
        ref_bounds: Vec::new(),
        moves_value: false,
        linked_calls: Vec::new(),
        ledger_writes: Vec::new(),
        total_changes: Vec::new(),
        stale_moves: Vec::new(),
        surplus_moves: Vec::new(),
    };
    if let Some(l) = &f.lifted {
        let own = names.clone();
        let (writes, totals) = ledger_writes(events, ctx.c.compiler.layout, &own);
        facts.stale_moves = stale_moves(ctx, l, events, &writes);
        facts.surplus_moves = surplus_moves(ctx, l, events, &writes, &totals, &own);
        facts.ledger_writes = writes;
        facts.total_changes = totals;
    }
    for cond in guard_conds(events) {
        if compares_sender_with_entry(cond) {
            facts.account_authorised = true;
        }
        for slot in slots_compared_with_party(cond) {
            if !facts.compared_slots.contains(&slot) {
                facts.compared_slots.push(slot);
            }
        }
        if is_auth_cond_in(cond, &ctx.roles) {
            let mut slots = HashSet::new();
            collect_sload_keys(cond, &mut slots);
            for k in slots {
                if expr::is_const(k) && !facts.auth_slots.iter().any(|(s, _)| *s == k) {
                    facts
                        .auth_slots
                        .push((k, emit::fmt_slot(k, names, SlotSpace::Persistent)));
                }
            }
        }
        if is_time_cond(cond) {
            facts.time_gated = true;
        }
        if matches!(
            expr::node(cond),
            Node::Op(op::ISZERO | op::EQ | op::AND, _) | Node::SLoad(..)
        ) && mentions(
            cond,
            &|n| matches!(n, Node::SLoad(k, false, _) if expr::is_const(*k)),
        ) && !is_auth_cond_in(cond, &ctx.roles)
        {
            facts.init_guarded = true;
        }
    }
    let layout = ctx.c.compiler.layout;
    let mut mutations: Vec<&Event> = Vec::new();
    let mut call_selector: HashMap<u32, u32> = HashMap::new();
    let mut linked_sites: Vec<(String, Option<u32>, bool, bool, Stmt)> = Vec::new();
    for ev in events {
        match &ev.stmt {
            Some(
                st @ Stmt::SStore {
                    key,
                    val,
                    transient: false,
                    ..
                },
            ) if expr::is_const(*key) => {
                facts
                    .const_writes
                    .push((*key, write_source(*val), emit::fmt_stmt(st, names)));
                let from_return = matches!(expr::node(unmask(*val)), Node::ReturnData(..));
                if from_return && !facts.factory_slots.contains(key) {
                    facts.factory_slots.push(*key);
                }
                mutations.push(ev);
            }
            Some(
                st @ Stmt::SStore {
                    key,
                    val,
                    transient: false,
                    ..
                },
            ) => {
                if let Some((root, account)) = ledger_entry(*key, layout) {
                    if subtracts_from(*val, *key).is_some_and(|amount| !expr::is_const(amount)) {
                        facts.debits.push(Debit {
                            root,
                            key: account,
                            account_text: emit::fmt_expr(account, names),
                            line: emit::fmt_stmt(st, names),
                        });
                    }
                }
                mutations.push(ev);
            }
            Some(
                st @ Stmt::Call {
                    kind,
                    addr,
                    value,
                    input,
                    input_head,
                    in_len,
                    seq,
                    ..
                },
            ) => {
                if *kind == op::DELEGATECALL || *kind == op::CALLCODE {
                    facts.delegatecalls.push((*addr, emit::fmt_stmt(st, names)));
                }
                if let Some(v) = value {
                    if expr::as_const(*v) != Some(U256::ZERO) {
                        facts.ether_out.push((*addr, *v, emit::fmt_stmt(st, names)));
                    }
                }
                let selector = input
                    .as_ref()
                    .and_then(|w| w.first().copied())
                    .or(input_head.first().copied())
                    .and_then(|w0| {
                        emit::leading_selector(
                            w0,
                            expr::as_const(*in_len).and_then(|l| l.as_usize()),
                        )
                    });
                if let Some(sel) = selector {
                    call_selector.insert(*seq, sel);
                }
                let is_static = *kind == op::STATICCALL;
                if ctx.world.has_other(ctx.c) {
                    let words: &[ExprId] = input.as_deref().unwrap_or(input_head);
                    let sends_value = value.is_some_and(|v| expr::as_const(v) != Some(U256::ZERO));
                    let spender = (selector == Some(SEL_APPROVE) && words.len() >= 2).then(|| {
                        let len = expr::as_const(*in_len).and_then(|l| l.as_usize());
                        emit::shifted_word_len(words, 0, len)
                    });
                    let callee = linked_address(ctx, *addr).map(|a| (a, false));
                    let approved = spender
                        .and_then(|sp| linked_address(ctx, sp))
                        .map(|a| (a, true));
                    for (address, approval) in callee.into_iter().chain(approved) {
                        linked_sites.push((address, selector, sends_value, approval, st.clone()));
                    }
                }
                if let Some(slot) = ssa::stored_address_slot(*addr) {
                    let words: &[ExprId] = input.as_deref().unwrap_or(input_head);
                    facts.stored_callees.push(StoredCall {
                        slot,
                        selector,
                        is_static,
                        passes_sender: words.iter().any(|w| from_caller(*w)),
                        line: emit::fmt_stmt(st, names),
                    });
                }
                if matches!(selector, Some(SEL_SYNC | SEL_SKIM)) {
                    let after_mutation = f
                        .lifted
                        .as_ref()
                        .is_some_and(|l| mutations.iter().any(|m| ev_reaches(ctx, l, m, ev)));
                    facts.syncs.push(PairSync {
                        target: emit::fmt_expr(*addr, names),
                        after_mutation,
                        line: emit::fmt_stmt(st, names),
                    });
                }
                if !is_static {
                    mutations.push(ev);
                }
            }
            _ => {}
        }
        let exprs: Vec<ExprId> = ev
            .stmt
            .iter()
            .flat_map(lift::stmt_exprs)
            .chain(ev.term.iter().flat_map(lift::term_exprs))
            .collect();
        for e in &exprs {
            collect_allowance_keys(*e, layout, &mut facts.allowance_of);
            if reads_under_sender(*e, layout) {
                facts.account_authorised = true;
            }
            collect_ledger_reads_under_slots(*e, layout, &mut facts.ledger_reads);
        }
        if let Some(Stmt::Call { addr, .. }) = &ev.stmt {
            if expr::as_const(*addr) == Some(U256::ONE) {
                facts.signature_authorised = true;
            }
        }
        if let Some(Term::SelfDestruct(a)) = &ev.term {
            facts
                .selfdestructs
                .push((*a, format!("selfdestruct({});", emit::fmt_expr(*a, names))));
        }
    }
    if !facts.account_authorised {
        'callees: for cf in transitive_callees(ctx, f) {
            let Some(l) = &cf.lifted else { continue };
            for nd in &l.nodes {
                for e in lift::node_exprs(nd) {
                    if reads_under_sender(e, layout) || compares_sender_with_entry(e) {
                        facts.account_authorised = true;
                        break 'callees;
                    }
                }
            }
        }
    }
    if !linked_sites.is_empty() {
        let own = names.clone();
        facts.linked_calls = linked_sites
            .into_iter()
            .map(
                |(address, selector, sends_value, approval, st)| LinkedCall {
                    address,
                    selector,
                    sends_value,
                    approval,
                    line: emit::fmt_stmt(&st, &own),
                },
            )
            .collect();
    }
    facts.moves_value = !facts.ether_out.is_empty()
        || !facts.debits.is_empty()
        || call_selector.values().any(|s| *s == SEL_TRANSFER);
    let mut outflows: Vec<ExprId> = facts.ether_out.iter().map(|(_, v, _)| *v).collect();
    let mut candidates: Vec<(AvailBound, ExprId)> = Vec::new();
    let mut seen = HashSet::new();
    for ev in events {
        match &ev.stmt {
            Some(Stmt::Call {
                input,
                input_head,
                in_len,
                ..
            }) => {
                let words: &[ExprId] = input.as_deref().unwrap_or(input_head);
                let len = expr::as_const(*in_len).and_then(|l| l.as_usize());
                let selector = words
                    .first()
                    .and_then(|w0| emit::leading_selector(*w0, len));
                if selector == Some(SEL_TRANSFER) && words.len() >= 2 {
                    outflows.push(emit::shifted_word_len(words, 1, len));
                }
            }
            Some(Stmt::SStore {
                key,
                val,
                transient: false,
                ..
            }) => {
                if let Some(amount) = subtracts_from(*val, *key) {
                    outflows.push(amount);
                }
            }
            _ => {}
        }
        for e in ev
            .stmt
            .iter()
            .flat_map(lift::stmt_exprs)
            .chain(ev.term.iter().flat_map(lift::term_exprs))
        {
            limits_in(e, layout, names, &mut seen, &mut candidates);
        }
    }
    if std::env::var("EVMDEC_DEBUG_LIMITS").is_ok() && !candidates.is_empty() {
        eprintln!(
            "[outflow] {} moves={} outflows={:?} others={:?}",
            facts.name,
            facts.moves_value,
            outflows
                .iter()
                .map(|a| emit::fmt_expr(*a, names))
                .collect::<Vec<_>>(),
            candidates
                .iter()
                .map(|(_, o)| emit::fmt_expr(*o, names))
                .collect::<Vec<_>>()
        );
    }
    if std::env::var("EVMDEC_DEBUG_UNPLACED").is_ok() {
        debug_unplaced(&facts.name, events, layout, names);
    }
    facts.ref_bounds = candidates.iter().map(|(b, _)| b.clone()).collect();
    for ev in events {
        if let Some(Term::Return {
            data: Some(words), ..
        }) = &ev.term
        {
            for w in words {
                if let Some(b) = linear_bound(*w, layout, names) {
                    facts.ref_bounds.push(b);
                }
            }
        }
    }
    facts.avail_bounds = candidates
        .into_iter()
        .filter(|(_, other)| limits_outflow(*other, &outflows))
        .map(|(b, _)| b)
        .collect();
    if std::env::var("EVMDEC_DEBUG_LIMITS").is_ok() {
        for b in &facts.avail_bounds {
            let show = |set: &BTreeSet<Field>| {
                set.iter()
                    .map(|f| b.names.get(f).cloned().unwrap_or_default())
                    .collect::<Vec<_>>()
                    .join(" + ")
            };
            eprintln!(
                "[limit] {} moves={} : ({}) - ({})",
                facts.name,
                facts.moves_value,
                show(&b.added),
                show(&b.subbed)
            );
        }
    }
    if std::env::var("EVMDEC_DEBUG_FACTS").is_ok() {
        eprintln!(
            "[facts] {} checked={} init={} time={} auth={:?} writes={} ether={} sd={} dc={} guards={:?}",
            facts.name,
            facts.caller_checked,
            facts.init_guarded,
            facts.time_gated,
            facts.auth_slots.iter().map(|(_, n)| n.clone()).collect::<Vec<_>>(),
            facts.const_writes.len(),
            facts.ether_out.len(),
            facts.selfdestructs.len(),
            facts.delegatecalls.len(),
            guard_conds(events)
                .iter()
                .map(|c| emit::fmt_cond(*c, names))
                .collect::<Vec<_>>()
        );
    }
    facts
}

fn uncast(e: ExprId) -> Option<ExprId> {
    let Node::Op(o, v) = expr::node(e) else {
        return None;
    };
    let power = |e: ExprId| {
        expr::as_const(e)
            .filter(|c| !c.is_zero() && (*c & c.wrapping_sub(U256::ONE)).is_zero())
            .map(|c| c.trailing_zeros())
    };
    let shift = |e: ExprId| {
        expr::as_const(e)
            .filter(|c| c.fits_u64())
            .map(|c| c.low_u64() as u32)
    };
    let raised = |e: ExprId| match expr::node(e) {
        Node::Op(op::MUL, w) => power(w[1])
            .map(|k| (w[0], k))
            .or(power(w[0]).map(|k| (w[1], k))),
        Node::Op(op::SHL, w) => shift(w[0]).map(|k| (w[1], k)),
        _ => None,
    };
    match o {
        op::AND if expr::as_const(v[1]).is_some_and(|m| m.is_low_mask()) => Some(v[0]),
        op::SHR => raised(v[1])
            .filter(|(_, k)| shift(v[0]) == Some(*k))
            .map(|(x, _)| x),
        op::DIV => raised(v[0])
            .filter(|(_, k)| power(v[1]) == Some(*k))
            .map(|(x, _)| x),
        _ => None,
    }
}

fn param_word(e: ExprId) -> Option<u32> {
    if let Some(inner) = uncast(e) {
        return param_word(inner);
    }
    match expr::node(e) {
        Node::CallDataLoad(off) | Node::CopiedWord(op::CALLDATACOPY, off, _) => {
            emit::calldata_word_index(off)
        }
        _ => None,
    }
}

fn calldata_locals(events: &[Event]) -> HashMap<u64, u32> {
    let mut held: HashMap<u64, Option<u32>> = HashMap::new();
    let mut open_from = u64::MAX;
    let put = |at: u64, word: Option<u32>, held: &mut HashMap<u64, Option<u32>>| {
        held.entry(at)
            .and_modify(|w| {
                if *w != word {
                    *w = None;
                }
            })
            .or_insert(word);
    };
    let small = |e: ExprId| {
        expr::as_const(e)
            .filter(|c| c.fits_u64())
            .map(|c| c.low_u64())
    };
    for ev in events {
        match &ev.stmt {
            Some(Stmt::MStore {
                off, val, width, ..
            }) => {
                if let Some(at) = small(*off) {
                    let word = param_word(*val).filter(|_| *width == 32);
                    put(at, word, &mut held);
                }
            }
            Some(Stmt::Copy {
                kind,
                dest,
                src,
                len,
                ..
            }) => match (small(*dest), small(*len)) {
                (Some(at), Some(n)) => {
                    let from = small(*src).filter(|_| *kind == op::CALLDATACOPY);
                    for k in 0..n.div_ceil(32).min(64) {
                        let word = from
                            .filter(|_| (k + 1) * 32 <= n)
                            .and_then(|s| emit::calldata_word_index(expr::konst_u64(s + 32 * k)));
                        put(at + 32 * k, word, &mut held);
                    }
                }
                (Some(at), None) => open_from = open_from.min(at),
                _ => {}
            },
            Some(Stmt::Call {
                out_off, out_len, ..
            }) => match (small(*out_off), small(*out_len)) {
                (_, Some(0)) => {}
                (Some(at), Some(n)) => {
                    for k in 0..n.div_ceil(32).min(64) {
                        put(at + 32 * k, None, &mut held);
                    }
                }
                (Some(at), None) => open_from = open_from.min(at),
                _ => {}
            },
            _ => {}
        }
    }
    held.into_iter()
        .filter(|(at, _)| *at < open_from && *at >= 0x60)
        .filter_map(|(at, word)| Some((at, word?)))
        .collect()
}

fn is_caller(e: ExprId) -> bool {
    match uncast(e) {
        Some(inner) => is_caller(inner),
        None => matches!(expr::node(e), Node::Env(op::CALLER, _)),
    }
}

fn walk(e: ExprId, seen: &mut HashSet<ExprId>, visit: &mut dyn FnMut(ExprId, &Node)) {
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if seen.len() > 20_000 || !seen.insert(x) {
            continue;
        }
        let n = expr::node(x);
        visit(x, &n);
        stack.extend(expr::children(x));
    }
}

fn key_parties(key: ExprId) -> (Vec<u32>, bool) {
    let mut words = Vec::new();
    let mut caller = false;
    walk(key, &mut HashSet::new(), &mut |_, n| {
        if let Node::Keccak(parts, _) = n {
            for p in parts {
                if let Some(w) = param_word(*p) {
                    if !words.contains(&w) {
                        words.push(w);
                    }
                }
                caller |= is_caller(*p);
            }
        }
    });
    (words, caller)
}

fn computed_return(events: &[Event]) -> Option<ExprId> {
    let mut out: Option<ExprId> = None;
    for ev in events {
        if let Some(
            Stmt::SStore { .. } | Stmt::Call { .. } | Stmt::Create { .. } | Stmt::Log { .. },
        ) = &ev.stmt
        {
            return None;
        }
        match &ev.term {
            Some(Term::Return {
                data: Some(words), ..
            }) if words.len() == 1 => {
                if out.is_some_and(|o| o != words[0]) {
                    return None;
                }
                out = Some(words[0]);
            }
            Some(
                Term::Jump(..) | Term::Branch { .. } | Term::Switch { .. } | Term::Revert { .. },
            )
            | Some(Term::Invalid | Term::InternalReturn { .. } | Term::Infeasible)
            | None => {}
            Some(_) => return None,
        }
    }
    out.filter(|e| {
        !mentions(*e, &|n| match n {
            Node::Const(_) | Node::Op(..) => false,
            Node::CallDataLoad(off) => emit::calldata_word_index(*off).is_none(),
            _ => true,
        })
    })
}

fn computed_result(ctx: &Ctx, st: &Stmt) -> Option<ExprId> {
    let Stmt::Call {
        addr,
        input,
        input_head,
        in_len,
        ..
    } = st
    else {
        return None;
    };
    if !ctx.world.has_other(ctx.c) {
        return None;
    }
    let words: &[ExprId] = input.as_deref().unwrap_or(input_head);
    let len = expr::as_const(*in_len).and_then(|l| l.as_usize());
    let selector = emit::leading_selector(*words.first()?, len)?;
    let address = linked_address(ctx, *addr)?;
    let report = ctx.world.report(&address)?;
    let hex = format!("{selector:#010x}");
    let returns = report
        .summaries
        .iter()
        .find(|g| g.selector.eq_ignore_ascii_case(&hex))?
        .returns?;
    Some(expr::substitute(
        returns,
        &|n| match n {
            Node::CallDataLoad(off) => emit::calldata_word_index(*off)
                .map(|i| emit::shifted_word_len(words, i as usize, len)),
            _ => None,
        },
        &mut HashMap::new(),
    ))
}

fn slot_place(key: ExprId) -> Option<(Option<u32>, U256)> {
    if let Some(word) = param_word(key) {
        return Some((Some(word), U256::ZERO));
    }
    match expr::split_offset(key) {
        (None, slot) => Some((None, slot)),
        (Some(base), offset) => Some((Some(param_word(base)?), offset)),
    }
}

fn summarise(
    ctx: &Ctx,
    facts: &FnFacts,
    events: &[Event],
    auth: &HashSet<ExprId>,
    names: &Names,
) -> Option<FnSummary> {
    let selector = facts.selector.clone().filter(|_| facts.external)?;
    let mut sum = FnSummary {
        function: facts.name.clone(),
        selector,
        gated: facts.caller_checked,
        signed: facts.signature_authorised,
        ..FnSummary::default()
    };
    sum.gate_slots = facts
        .auth_slots
        .iter()
        .filter_map(|(k, _)| expr::as_const(*k))
        .map(|k| k.to_hex_padded(32))
        .collect();
    let bind = |w: u32, bound: &mut Vec<u32>| {
        if !bound.contains(&w) {
            bound.push(w);
        }
    };
    let own = names.clone();
    let mut seen = HashSet::new();
    let locals = calldata_locals(events);
    let resolved: Vec<Event>;
    let events = if locals.is_empty() {
        events
    } else {
        let memo = RefCell::new(HashMap::new());
        let read = |e: ExprId| {
            expr::substitute(
                e,
                &|n| match n {
                    Node::MLoad(a, _) => expr::as_const(*a)
                        .filter(|c| c.fits_u64())
                        .and_then(|c| locals.get(&c.low_u64()))
                        .map(|w| expr::calldataload(expr::konst_u64(4 + 32 * u64::from(*w)))),
                    _ => None,
                },
                &mut memo.borrow_mut(),
            )
        };
        resolved = events
            .iter()
            .map(|ev| Event {
                stmt: ev.stmt.as_ref().map(|st| lift::map_stmt(st, &read)),
                term: ev.term.as_ref().map(|t| lift::map_term(t, &read)),
                ..ev.clone()
            })
            .collect();
        &resolved[..]
    };
    for cond in guard_conds(events) {
        if let Some(root) = role_test_root(cond) {
            let root = root.to_hex_padded(32);
            if !sum.gate_roles.contains(&root) {
                sum.gate_roles.push(root);
            }
        }
        walk(cond, &mut HashSet::new(), &mut |_, n| {
            let Node::Op(op::EQ | op::SUB | op::XOR, v) = n else {
                return;
            };
            for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
                if !is_caller(a) {
                    continue;
                }
                if let Some(w) = param_word(b) {
                    bind(w, &mut sum.bound);
                }
                if let Node::SLoad(k, false, _) = expr::node(unmask(b)) {
                    for w in key_parties(k).0 {
                        bind(w, &mut sum.bound);
                    }
                    if let Some((Some(base), offset)) = slot_place(k) {
                        let gate = RelativeSlot {
                            base,
                            offset: offset.to_hex_padded(32),
                        };
                        if !sum.gate_relative.contains(&gate) {
                            sum.gate_relative.push(gate);
                        }
                    }
                }
            }
        });
    }
    for ev in events {
        let exprs = ev
            .stmt
            .iter()
            .flat_map(lift::stmt_exprs)
            .chain(ev.term.iter().flat_map(lift::term_exprs));
        for e in exprs {
            walk(e, &mut seen, &mut |_, n| {
                if let Node::SLoad(k, false, _) = n {
                    let (words, caller) = key_parties(*k);
                    if caller {
                        for w in words {
                            bind(w, &mut sum.bound);
                        }
                    }
                }
            });
        }
        let Some(st) = &ev.stmt else { continue };
        match st {
            Stmt::SStore {
                key,
                val,
                transient: false,
                ..
            } => {
                let stored = param_word(*val)
                    .or_else(|| emit::packed_write(*key, *val).and_then(|(.., v)| param_word(v)))
                    .or_else(|| {
                        ssa::field_writes(*key, *val)
                            .iter()
                            .find_map(|w| param_word(w.value))
                    });
                if let (Some((base, slot)), Some(word)) = (slot_place(*key), stored) {
                    sum.stores.push(ParamStore {
                        word,
                        slot: slot.to_hex_padded(32),
                        base,
                        gates: base.is_none() && auth.contains(key),
                        line: emit::fmt_stmt(st, &own),
                    });
                }
                let lowered = !expr::is_const(*key)
                    && (matches!(change_of(*val, *key).0, Change::Down(a) if !expr::is_const(a))
                        || expr::as_const(*val) == Some(U256::ZERO));
                if lowered {
                    let line = emit::fmt_stmt(st, &own);
                    for word in key_parties(*key).0 {
                        sum.lowers.push(ParamUse {
                            word,
                            line: line.clone(),
                        });
                    }
                }
            }
            Stmt::Call {
                kind,
                addr,
                value,
                input,
                input_head,
                in_len,
                ..
            } if *kind == op::CALL || *kind == op::DELEGATECALL => {
                let words: &[ExprId] = input.as_deref().unwrap_or(input_head);
                let len = expr::as_const(*in_len).and_then(|l| l.as_usize());
                let selector = words
                    .first()
                    .and_then(|w0| emit::leading_selector(*w0, len));
                let sends = value.is_some_and(|v| expr::as_const(v) != Some(U256::ZERO));
                if let (true, Some(word)) = (sends, param_word(*addr)) {
                    sum.pays.push(ParamUse {
                        word,
                        line: emit::fmt_stmt(st, &own),
                    });
                }
                let Some(sel) = selector else { continue };
                let count = match len {
                    Some(l) => l.saturating_sub(4) / 32,
                    None => words.len().saturating_sub(1),
                }
                .min(12);
                let args: Vec<Option<u32>> = (0..count)
                    .map(|i| param_word(emit::shifted_word_len(words, i, len)))
                    .collect();
                let arg = |i: usize| args.get(i).copied().flatten();
                if *kind == op::DELEGATECALL {
                    let hex = format!("{sel:#010x}");
                    let report = linked_address(ctx, *addr).and_then(|a| ctx.world.report(&a));
                    let Some(report) = report else { continue };
                    let Some(h) = report
                        .summaries
                        .iter()
                        .find(|h| h.selector.eq_ignore_ascii_case(&hex))
                    else {
                        continue;
                    };
                    let back = |word: u32| arg(word as usize);
                    let place = |base: Option<u32>, slot: &str| -> Option<(Option<u32>, String)> {
                        let Some(base) = base else {
                            return Some((None, slot.to_string()));
                        };
                        let position = emit::shifted_word_len(words, base as usize, len);
                        match expr::as_const(position) {
                            Some(start) => {
                                let slot = start.wrapping_add(U256::from_hex_str(slot)?);
                                Some((None, slot.to_hex_padded(32)))
                            }
                            None => Some((Some(param_word(position)?), slot.to_string())),
                        }
                    };
                    sum.gated |= h.gated;
                    sum.signed |= h.signed;
                    for slot in &h.gate_slots {
                        if !sum.gate_slots.contains(slot) {
                            sum.gate_slots.push(slot.clone());
                        }
                    }
                    for root in &h.gate_roles {
                        if !sum.gate_roles.contains(root) {
                            sum.gate_roles.push(root.clone());
                        }
                    }
                    for gate in &h.gate_relative {
                        match place(Some(gate.base), &gate.offset) {
                            Some((None, slot)) if !sum.gate_slots.contains(&slot) => {
                                sum.gate_slots.push(slot);
                            }
                            Some((Some(base), offset)) => {
                                sum.gate_relative.push(RelativeSlot { base, offset });
                            }
                            _ => {}
                        }
                    }
                    for word in h.bound.iter().filter_map(|w| back(*w)) {
                        bind(word, &mut sum.bound);
                    }
                    for u in &h.lowers {
                        if let Some(word) = back(u.word) {
                            sum.lowers.push(ParamUse {
                                word,
                                line: u.line.clone(),
                            });
                        }
                    }
                    for u in &h.pays {
                        if let Some(word) = back(u.word) {
                            sum.pays.push(ParamUse {
                                word,
                                line: u.line.clone(),
                            });
                        }
                    }
                    for held in &h.stores {
                        let placed = place(held.base, &held.slot);
                        if let (Some(word), Some((base, slot))) = (back(held.word), placed) {
                            sum.stores.push(ParamStore {
                                word,
                                slot,
                                base,
                                gates: held.gates && base.is_none(),
                                line: held.line.clone(),
                            });
                        }
                    }
                    for fw in &h.forwards {
                        if let Some(word) = back(fw.word) {
                            sum.forwards.push(ParamForward { word, ..fw.clone() });
                        }
                    }
                    continue;
                }
                let (from, to) = match sel {
                    SEL_TRANSFER => (None, arg(0)),
                    SEL_TRANSFER_FROM => (arg(0), arg(1)),
                    _ => (None, None),
                };
                if let Some(word) = from {
                    sum.lowers.push(ParamUse {
                        word,
                        line: emit::fmt_stmt(st, &own),
                    });
                }
                if let Some(word) = to {
                    sum.pays.push(ParamUse {
                        word,
                        line: emit::fmt_stmt(st, &own),
                    });
                }
                let target = match linked_address(ctx, *addr) {
                    Some(a) => Some(a),
                    None => match expr::as_const(unmask(*addr)) {
                        Some(a) => Some(a.to_hex_padded(20)),
                        None => ssa::stored_address_slot(*addr)
                            .and_then(expr::as_const)
                            .map(|k| format!("slot {}", k.to_hex_padded(32))),
                    },
                };
                let Some(target) = target else { continue };
                for (i, word) in args.iter().enumerate() {
                    let Some(word) = word else { continue };
                    sum.forwards.push(ParamForward {
                        word: *word,
                        arg: i as u32,
                        target: target.clone(),
                        selector: format!("{sel:#010x}"),
                        line: emit::fmt_stmt(st, &own),
                    });
                }
            }
            _ => {}
        }
    }
    sum.creates = events.iter().find_map(|ev| match &ev.term {
        Some(Term::Return {
            data: Some(words), ..
        }) => {
            let made = ctx.made.borrow();
            words.first().and_then(|w| made.get(&unmask(*w)).cloned())
        }
        _ => None,
    });
    sum.returns = computed_return(events);
    sum.bound.sort_unstable();
    sum.lowers.dedup();
    sum.pays.dedup();
    sum.stores.dedup();
    sum.forwards.dedup();
    Some(sum)
}

fn writes_of<'a>(
    ctx: &Ctx,
    nodes: impl Iterator<Item = &'a lift::LNode>,
    visited: &mut HashSet<usize>,
) -> Option<Vec<(ExprId, Option<u64>)>> {
    let mut out = Vec::new();
    for nd in nodes {
        for s in &nd.stmts {
            match s {
                Stmt::MStore { off, width, .. } => {
                    expr::as_const(*off)?;
                    out.push((*off, Some(*width as u64)));
                }
                Stmt::Copy { dest, len, .. } => {
                    expr::as_const(*dest)?;
                    out.push((
                        *dest,
                        expr::as_const(*len)
                            .and_then(|l| l.as_usize())
                            .map(|l| l as u64),
                    ));
                }
                Stmt::Call {
                    out_off, out_len, ..
                } => {
                    let ol = expr::as_const(*out_len)
                        .and_then(|l| l.as_usize())
                        .map(|l| l as u64);
                    if ol != Some(0) {
                        expr::as_const(*out_off)?;
                        out.push((*out_off, ol));
                    }
                }
                Stmt::Internal { callee, .. } => out.extend(callee_writes(ctx, *callee, visited)?),
                _ => {}
            }
        }
    }
    Some(out)
}

fn callee_writes(
    ctx: &Ctx,
    target: usize,
    visited: &mut HashSet<usize>,
) -> Option<Vec<(ExprId, Option<u64>)>> {
    if let Some(w) = ctx.callee_writes.borrow().get(&target) {
        return w.clone();
    }
    if !visited.insert(target) {
        return Some(Vec::new());
    }
    let r = match ctx.internals.get(&target).and_then(|f| f.lifted.as_ref()) {
        Some(cl) => writes_of(ctx, cl.nodes.iter(), visited),
        None => None,
    };
    ctx.callee_writes.borrow_mut().insert(target, r.clone());
    r
}

fn forget_writes(mem: &mut lift::MemView, writes: Option<Vec<(ExprId, Option<u64>)>>) {
    match writes {
        Some(ws) => {
            for (off, len) in ws {
                mem.unknown(off, len);
            }
        }
        None => mem.unfresh(),
    }
}

fn mentions(e: ExprId, pred: &dyn Fn(&Node) -> bool) -> bool {
    expr::contains(e, pred)
}
fn mentions_outside(e: ExprId, target: ExprId, excluded: ExprId) -> bool {
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if x == excluded || !seen.insert(x) || seen.len() > 5000 {
            continue;
        }
        if x == target {
            return true;
        }
        stack.extend(expr::children(x));
    }
    false
}

fn from_calldata(e: ExprId) -> bool {
    mentions(e, &|n| {
        matches!(
            n,
            Node::CallDataLoad(_) | Node::CopiedWord(op::CALLDATACOPY, _, _)
        )
    })
}
fn unmask(e: ExprId) -> ExprId {
    match expr::node(e) {
        Node::Op(op::AND, v) if expr::as_const(v[1]) == Some(expr::mask_bits(160)) => unmask(v[0]),
        _ => e,
    }
}

fn ledger_entry(key: ExprId, layout: emit::MappingLayout) -> Option<(U256, ExprId)> {
    let path = ssa::slot_path(key, layout)?;
    match path.steps[..] {
        [ssa::Step::Key(k)] => Some((path.root, k)),
        _ => None,
    }
}

fn pooled_field(e: ExprId, layout: emit::MappingLayout) -> Option<Field> {
    let mut x = e;
    let mut width = 256u32;
    let mut lo = 0u32;
    if let Node::Op(op::AND, v) = expr::node(x) {
        let masked = [(v[0], v[1]), (v[1], v[0])].into_iter().find_map(|(m, o)| {
            let c = expr::as_const(m)?;
            let tz = c.trailing_zeros();
            (tz < 256 && (c >> tz).is_low_mask()).then(|| (tz, c.count_ones(), o))
        });
        let (t, w, o) = masked?;
        lo = t;
        width = w;
        x = o;
    }
    if lo == 0 {
        if let Node::Op(op::SHR, v) = expr::node(x) {
            let s = expr::as_const(v[0]).filter(|s| s.fits_u64() && s.low_u64() < 256)?;
            lo = s.low_u64() as u32;
            x = v[1];
        }
    }
    let Node::SLoad(k, false, _) = expr::node(x) else {
        return None;
    };
    let p = ssa::slot_path(k, layout)?;
    if !p
        .steps
        .iter()
        .any(|st| matches!(st, ssa::Step::Key(_) | ssa::Step::Index(_)))
    {
        return None;
    }
    Some(Field {
        shape: p.shape(SlotSpace::Persistent),
        lo,
        width: width.min(256 - lo),
    })
}

fn linear_fields(
    e: ExprId,
    sign: i32,
    layout: emit::MappingLayout,
    names: &Names,
    coef: &mut BTreeMap<Field, i32>,
    labels: &mut HashMap<Field, String>,
    budget: &mut u32,
) {
    if *budget == 0 {
        return;
    }
    *budget -= 1;
    if let Some(f) = pooled_field(e, layout) {
        labels
            .entry(f.clone())
            .or_insert_with(|| emit::fmt_expr(e, names));
        *coef.entry(f).or_insert(0) += sign;
        return;
    }
    match expr::node(e) {
        Node::Op(op::ADD, v) => {
            for x in v {
                linear_fields(x, sign, layout, names, coef, labels, budget);
            }
        }
        Node::Op(op::SUB, v) if v.len() == 2 => {
            linear_fields(v[0], sign, layout, names, coef, labels, budget);
            linear_fields(v[1], -sign, layout, names, coef, labels, budget);
        }
        Node::Op(op::AND, v) if v.len() == 2 => {
            for (m, o) in [(v[0], v[1]), (v[1], v[0])] {
                if expr::as_const(m).is_some_and(|c| c.is_low_mask()) {
                    linear_fields(o, sign, layout, names, coef, labels, budget);
                    break;
                }
            }
        }
        _ => {}
    }
}

fn unplaced_terms(e: ExprId, sign: i32, names: &Names, out: &mut Vec<String>, budget: &mut u32) {
    if *budget == 0 {
        return;
    }
    *budget -= 1;
    match expr::node(e) {
        Node::Op(op::ADD, v) => {
            for x in v {
                unplaced_terms(x, sign, names, out, budget);
            }
        }
        Node::Op(op::SUB, v) if v.len() == 2 => {
            unplaced_terms(v[0], sign, names, out, budget);
            unplaced_terms(v[1], -sign, names, out, budget);
        }
        Node::Op(op::AND, v) if v.len() == 2 => {
            for x in v {
                if !expr::is_const(x) {
                    unplaced_terms(x, sign, names, out, budget);
                }
            }
        }
        Node::MLoad(..) | Node::IntRet(..) | Node::Var(_) => {
            out.push(format!(
                "{}{}",
                if sign > 0 { "+" } else { "-" },
                emit::fmt_expr(e, names)
            ));
        }
        _ => {}
    }
}

fn debug_unplaced(name: &str, events: &[Event], layout: emit::MappingLayout, names: &Names) {
    let mut seen = HashSet::new();
    for ev in events {
        for e in ev
            .stmt
            .iter()
            .flat_map(lift::stmt_exprs)
            .chain(ev.term.iter().flat_map(lift::term_exprs))
        {
            let mut stack = vec![e];
            while let Some(x) = stack.pop() {
                if !seen.insert(x) || seen.len() > 50_000 {
                    continue;
                }
                if let Node::Op(op::SUB, _) = expr::node(x) {
                    let mut coef = BTreeMap::new();
                    let mut labels = HashMap::new();
                    let mut budget = 256;
                    linear_fields(x, 1, layout, names, &mut coef, &mut labels, &mut budget);
                    let mut un = Vec::new();
                    let mut b2 = 256;
                    unplaced_terms(x, 1, names, &mut un, &mut b2);
                    if coef.values().any(|c| *c < 0) && !un.is_empty() {
                        let fields: Vec<String> = coef
                            .iter()
                            .filter(|(_, c)| **c != 0)
                            .map(|(f, c)| {
                                format!("{}{}", if *c > 0 { "+" } else { "-" }, labels[f])
                            })
                            .collect();
                        eprintln!("[unplaced] {} fields={:?} unplaced={:?}", name, fields, un);
                    }
                }
                stack.extend(expr::children(x));
            }
        }
    }
}

fn linear_bound(e: ExprId, layout: emit::MappingLayout, names: &Names) -> Option<AvailBound> {
    let mut coef = BTreeMap::new();
    let mut labels = HashMap::new();
    let mut budget = 256;
    linear_fields(e, 1, layout, names, &mut coef, &mut labels, &mut budget);
    let added: BTreeSet<Field> = coef
        .iter()
        .filter(|(_, c)| **c > 0)
        .map(|(f, _)| f.clone())
        .collect();
    let subbed: BTreeSet<Field> = coef
        .iter()
        .filter(|(_, c)| **c < 0)
        .map(|(f, _)| f.clone())
        .collect();
    (!added.is_empty() && !subbed.is_empty()).then(|| AvailBound {
        added,
        subbed,
        names: labels,
        line: emit::fmt_expr(e, names),
    })
}

fn amount_term(e: ExprId, layout: emit::MappingLayout, budget: &mut u32) -> Option<ExprId> {
    if *budget == 0 || pooled_field(e, layout).is_some() {
        return None;
    }
    *budget -= 1;
    match expr::node(e) {
        Node::Op(op::ADD | op::SUB, v) => v.iter().find_map(|x| amount_term(*x, layout, budget)),
        Node::Op(op::AND, v) if v.len() == 2 => {
            let masked = v.iter().find(|x| !expr::is_const(**x))?;
            amount_term(*masked, layout, budget)
        }
        Node::SLoad(..) | Node::Const(_) => None,
        _ => expr::contains(e, &|n| matches!(n, Node::CallDataLoad(_))).then_some(e),
    }
}

// `amount + owed < held` says the same as `amount < held - owed`.
// Fields that stand with the amount are owed, and fields on the other side are held.
fn two_sided_bound(
    with_amount: ExprId,
    opposite: ExprId,
    layout: emit::MappingLayout,
    names: &Names,
) -> Option<(AvailBound, ExprId)> {
    let amount = amount_term(with_amount, layout, &mut 64)?;
    if amount_term(opposite, layout, &mut 64).is_some() {
        return None;
    }
    let mut labels = HashMap::new();
    let mut fields = |e: ExprId| {
        let mut coef = BTreeMap::new();
        linear_fields(e, 1, layout, names, &mut coef, &mut labels, &mut 256);
        coef
    };
    let (near, far) = (fields(with_amount), fields(opposite));
    let pick = |from: &BTreeMap<Field, i32>, positive: bool| -> BTreeSet<Field> {
        let wanted = from
            .iter()
            .filter(|(_, c)| (**c > 0) == positive && **c != 0);
        wanted.map(|(f, _)| f.clone()).collect()
    };
    let added: BTreeSet<Field> = pick(&far, true)
        .union(&pick(&near, false))
        .cloned()
        .collect();
    let subbed: BTreeSet<Field> = pick(&near, true)
        .union(&pick(&far, false))
        .cloned()
        .collect();
    let line = format!(
        "{} vs {}",
        emit::fmt_expr(with_amount, names),
        emit::fmt_expr(opposite, names)
    );
    (!added.is_empty() && !subbed.is_empty() && !near.is_empty()).then_some((
        AvailBound {
            added,
            subbed,
            names: labels,
            line,
        },
        amount,
    ))
}

fn limits_outflow(other: ExprId, outflows: &[ExprId]) -> bool {
    let calldata = |e: ExprId| {
        let mut words = HashSet::new();
        let mut stack = vec![e];
        let mut seen = HashSet::new();
        while let Some(x) = stack.pop() {
            if !seen.insert(x) || seen.len() > 5_000 {
                continue;
            }
            if let Node::CallDataLoad(off) = expr::node(x) {
                words.insert(off);
            }
            stack.extend(expr::children(x));
        }
        words
    };
    let mine = calldata(other);
    outflows.iter().any(|a| {
        *a == other
            || contains_expr(*a, other)
            || contains_expr(other, *a)
            || !mine.is_disjoint(&calldata(*a))
    })
}

fn limits_in(
    e: ExprId,
    layout: emit::MappingLayout,
    names: &Names,
    seen: &mut HashSet<ExprId>,
    out: &mut Vec<(AvailBound, ExprId)>,
) {
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 50_000 {
            continue;
        }
        if let Node::Op(op::LT | op::GT | op::SLT | op::SGT, v) = expr::node(x) {
            let mut found: Vec<(AvailBound, ExprId)> = Vec::new();
            for (side, other) in [(v[0], v[1]), (v[1], v[0])] {
                if expr::is_const(other) {
                    continue;
                }
                found.extend(linear_bound(side, layout, names).map(|b| (b, other)));
                found.extend(two_sided_bound(other, side, layout, names));
            }
            for (b, other) in found {
                if !out
                    .iter()
                    .any(|(o, w)| *w == other && o.added == b.added && o.subbed == b.subbed)
                {
                    out.push((b, other));
                }
            }
        }
        stack.extend(expr::children(x));
    }
}

fn subtracts_from(val: ExprId, key: ExprId) -> Option<ExprId> {
    let Node::Op(op::SUB, v) = expr::node(val) else {
        return None;
    };
    let reads_entry = matches!(expr::node(v[0]), Node::SLoad(k, false, _) if k == key);
    reads_entry.then_some(v[1])
}

fn reads_under_sender(e: ExprId, layout: emit::MappingLayout) -> bool {
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 20_000 {
            continue;
        }
        if let Node::SLoad(k, false, _) = expr::node(x) {
            if let Some(path) = ssa::slot_path(k, layout) {
                if path.steps.len() >= 2
                    && matches!(path.steps.last(), Some(ssa::Step::Key(s)) if from_caller(*s))
                {
                    return true;
                }
            }
        }
        stack.extend(expr::children(x));
    }
    false
}

fn compares_sender_with_entry(e: ExprId) -> bool {
    let entry_load = |x: ExprId| {
        let x = unmask(x);
        matches!(expr::node(x), Node::SLoad(k, false, _) if !expr::is_const(k))
    };
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 20_000 {
            continue;
        }
        if let Node::Op(op::EQ, v) = expr::node(x) {
            let sender = |y: ExprId| matches!(expr::node(unmask(y)), Node::Env(op::CALLER, _));
            if (sender(v[0]) && entry_load(v[1])) || (sender(v[1]) && entry_load(v[0])) {
                return true;
            }
        }
        stack.extend(expr::children(x));
    }
    false
}

fn slots_compared_with_party(cond: ExprId) -> Vec<ExprId> {
    let party = |e: ExprId| {
        let e = unmask(e);
        from_calldata(e)
            || from_caller(e)
            || matches!(expr::node(e), Node::Arg(_) | Node::Var(_) | Node::MLoad(..))
    };
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    let mut stack = vec![cond];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 20_000 {
            continue;
        }
        if let Node::Op(op::EQ | op::SUB | op::XOR, v) = expr::node(x) {
            for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
                if let Some(slot) = ssa::stored_address_slot(a) {
                    if party(b) && !out.contains(&slot) {
                        out.push(slot);
                    }
                }
            }
        }
        stack.extend(expr::children(x));
    }
    out
}

fn collect_ledger_reads_under_slots(
    e: ExprId,
    layout: emit::MappingLayout,
    out: &mut Vec<(U256, ExprId)>,
) {
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 20_000 {
            continue;
        }
        if let Node::SLoad(k, false, _) = expr::node(x) {
            if let Some((root, account)) = ledger_entry(k, layout) {
                if let Some(slot) = ssa::stored_address_slot(account) {
                    if !out.contains(&(root, slot)) {
                        out.push((root, slot));
                    }
                }
            }
        }
        stack.extend(expr::children(x));
    }
}

fn collect_allowance_keys(e: ExprId, layout: emit::MappingLayout, out: &mut Vec<ExprId>) {
    let mut keys = Vec::new();
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 20_000 {
            continue;
        }
        if let Node::SLoad(k, false, _) = expr::node(x) {
            keys.push(k);
        }
        stack.extend(expr::children(x));
    }
    for k in keys {
        let Some(path) = ssa::slot_path(k, layout) else {
            continue;
        };
        if let [ssa::Step::Key(owner), ssa::Step::Key(spender)] = path.steps[..] {
            let owner = unmask(owner);
            if from_caller(spender) && !out.contains(&owner) {
                out.push(owner);
            }
        }
    }
}

fn from_storage(e: ExprId) -> bool {
    mentions(e, &|n| matches!(n, Node::SLoad(..)))
}
fn from_caller(e: ExprId) -> bool {
    mentions(e, &|n| matches!(n, Node::Env(op::CALLER, _)))
}
fn is_const_addr(e: ExprId) -> bool {
    expr::as_const(e).is_some()
}

fn caller_derived(l: &Lifted, events: &[Event], e: ExprId, depth: usize) -> bool {
    if from_caller(e) {
        return true;
    }
    if depth == 0 {
        return false;
    }
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 5000 {
            continue;
        }
        match expr::node(x) {
            Node::Var(_) => {
                let incoming: Vec<ExprId> = l
                    .edge_assigns
                    .values()
                    .flatten()
                    .filter(|(v, _)| *v == x)
                    .map(|(_, val)| *val)
                    .collect();
                if !incoming.is_empty()
                    && incoming
                        .iter()
                        .all(|v| caller_derived(l, events, *v, depth - 1))
                {
                    return true;
                }
            }
            Node::ReturnData(sq, _) => {
                let fed_by_caller = events.iter().any(|ev| match &ev.stmt {
                    Some(Stmt::Call {
                        seq,
                        input,
                        input_head,
                        ..
                    }) if *seq == sq => input
                        .as_ref()
                        .map_or(input_head.as_slice(), |w| w.as_slice())
                        .iter()
                        .any(|w| from_caller(*w)),
                    _ => false,
                });
                if fed_by_caller {
                    return true;
                }
            }
            _ => {}
        }
        stack.extend(expr::children(x));
    }
    false
}

fn self_deployed(events: &[Event], addr: ExprId) -> bool {
    let addr = match expr::node(addr) {
        Node::Op(op::AND, v) if expr::as_const(v[1]).is_some_and(|m| m.is_low_mask()) => v[0],
        Node::Op(op::AND, v) if expr::as_const(v[0]).is_some_and(|m| m.is_low_mask()) => v[1],
        _ => addr,
    };
    let Node::CreateResult(sq) = expr::node(addr) else {
        return false;
    };
    let created_at = events
        .iter()
        .position(|ev| matches!(&ev.stmt, Some(Stmt::Create { seq, .. }) if *seq == sq));
    created_at.is_some_and(|i| {
        events[..i].iter().any(|ev| {
            matches!(
                &ev.stmt,
                Some(Stmt::Copy {
                    kind: op::CODECOPY,
                    ..
                })
            )
        })
    })
}

fn array_root_of(e: ExprId) -> Option<U256> {
    let mut found = None;
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if found.is_some() || !seen.insert(x) || seen.len() > 5000 {
            continue;
        }
        if let Node::SLoad(key, false, _) = expr::node(x) {
            if !expr::is_const(key) || emit::hashed_slot(expr::as_const(key)?).is_some() {
                found = emit::element_root(key);
            }
        }
        stack.extend(expr::children(x));
    }
    found
}

fn fixed_in_storage(ctx: &Ctx, e: ExprId) -> bool {
    let e = match expr::node(e) {
        Node::Op(op::AND, v) if expr::as_const(v[1]).is_some_and(|m| m.is_low_mask()) => v[0],
        Node::Op(op::AND, v) if expr::as_const(v[0]).is_some_and(|m| m.is_low_mask()) => v[1],
        _ => e,
    };
    if let Some((k, off, bits)) = emit::packed_read(e) {
        let overlaps = |(k2, o2, b2): &(U256, u32, u32)| {
            *k2 == k && o2 * 8 < off * 8 + bits && off * 8 < o2 * 8 + b2
        };
        return !ctx.slot_writes.contains(&k) && !ctx.field_writes.iter().any(overlaps);
    }
    match expr::node(e) {
        Node::SLoad(key, false, _) => match expr::as_const(key) {
            Some(k) => {
                !ctx.slot_writes.contains(&k) && !ctx.field_writes.iter().any(|(k2, _, _)| *k2 == k)
            }
            None => false,
        },
        _ => false,
    }
}

fn deep_mentions(
    ctx: &Ctx,
    events: &[Event],
    e: ExprId,
    pred: &dyn Fn(&Node) -> bool,
    depth: usize,
) -> bool {
    if mentions(e, pred) {
        return true;
    }
    if depth == 0 {
        return false;
    }
    let mut seqs: Vec<u32> = Vec::new();
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 5000 {
            continue;
        }
        if let Node::IntRet(sq, _) = expr::node(x) {
            seqs.push(sq);
        }
        stack.extend(expr::children(x));
    }
    seqs.iter().any(|sq| {
        events.iter().any(|ev| match &ev.stmt {
            Some(Stmt::Internal {
                seq, callee, args, ..
            }) if seq == sq => {
                args.iter()
                    .any(|a| deep_mentions(ctx, events, *a, pred, depth - 1))
                    || ctx.internals.get(callee).is_some_and(|cf| {
                        cf.lifted.as_ref().is_some_and(|cl| {
                            cl.nodes.iter().any(|nd| match &nd.term {
                                Term::InternalReturn(vals) => vals
                                    .iter()
                                    .any(|v| graph_mentions(ctx, cl, *v, pred, depth - 1)),
                                _ => false,
                            })
                        })
                    })
            }
            _ => false,
        })
    })
}

fn graph_mentions(
    ctx: &Ctx,
    l: &Lifted,
    e: ExprId,
    pred: &dyn Fn(&Node) -> bool,
    depth: usize,
) -> bool {
    if mentions(e, pred) {
        return true;
    }
    if depth == 0 {
        return false;
    }
    let mut seqs: Vec<u32> = Vec::new();
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 5000 {
            continue;
        }
        if let Node::IntRet(sq, _) = expr::node(x) {
            seqs.push(sq);
        }
        stack.extend(expr::children(x));
    }
    seqs.iter().any(|sq| {
        l.nodes.iter().any(|nd| {
            nd.stmts.iter().any(|st| match st {
                Stmt::Internal {
                    seq, callee, args, ..
                } if seq == sq => {
                    args.iter()
                        .any(|a| graph_mentions(ctx, l, *a, pred, depth - 1))
                        || ctx.internals.get(callee).is_some_and(|cf| {
                            cf.lifted.as_ref().is_some_and(|cl| {
                                cl.nodes.iter().any(|nd2| match &nd2.term {
                                    Term::InternalReturn(vals) => vals
                                        .iter()
                                        .any(|v| graph_mentions(ctx, cl, *v, pred, depth - 1)),
                                    _ => false,
                                })
                            })
                        })
                }
                _ => false,
            })
        })
    })
}

fn loop_nodes(l: &Lifted) -> HashSet<usize> {
    const UNSEEN: usize = usize::MAX;
    let n = l.nodes.len();
    let mut index = vec![UNSEEN; n];
    let mut low = vec![0usize; n];
    let mut on_stack = vec![false; n];
    let mut component: Vec<usize> = Vec::new();
    let mut in_loop = HashSet::new();
    let mut next = 0usize;
    for root in 0..n {
        if index[root] != UNSEEN {
            continue;
        }
        let mut calls: Vec<(usize, usize)> = vec![(root, 0)];
        while let Some(&(x, child)) = calls.last() {
            if child == 0 {
                index[x] = next;
                low[x] = next;
                next += 1;
                component.push(x);
                on_stack[x] = true;
            }
            if let Some(&y) = l.nodes[x].succs.get(child) {
                calls.last_mut().expect("the frame being advanced").1 += 1;
                if y >= n {
                    continue;
                }
                if index[y] == UNSEEN {
                    calls.push((y, 0));
                } else if on_stack[y] {
                    low[x] = low[x].min(index[y]);
                }
                continue;
            }
            calls.pop();
            if let Some(&(parent, _)) = calls.last() {
                low[parent] = low[parent].min(low[x]);
            }
            if low[x] != index[x] {
                continue;
            }
            let start = component
                .iter()
                .rposition(|m| *m == x)
                .expect("a root is on the stack of its component");
            let members = component.split_off(start);
            let cyclic = members.len() > 1 || l.nodes[x].succs.contains(&x);
            for m in members {
                on_stack[m] = false;
                if cyclic {
                    in_loop.insert(m);
                }
            }
        }
    }
    in_loop
}

fn events_of(ctx: &Ctx, l: &Lifted, depth: usize, in_loop_outer: bool) -> Vec<Event> {
    ctx.computed_returns.borrow_mut().clear();
    ctx.made.borrow_mut().clear();
    ctx.code_copies.borrow_mut().clear();
    ctx.inline_left.set(MAX_INLINED_EVENTS);
    let mut mem = lift::MemView::new_fresh();
    events_of_in(
        ctx,
        l,
        depth,
        in_loop_outer,
        None,
        None,
        0,
        &[],
        &HashMap::new(),
        &mut mem,
    )
}

fn ev_reaches(ctx: &Ctx, l: &Lifted, a: &Event, b: &Event) -> bool {
    for (i, ((ia, ca, na), (ib, _, nb))) in a.path.iter().zip(b.path.iter()).enumerate() {
        if ia != ib {
            return true;
        }
        if na == nb {
            continue;
        }
        let graph = if i == 0 {
            Some(l)
        } else {
            ca.and_then(|pc| ctx.internals.get(&pc))
                .and_then(|f| f.lifted.as_ref())
        };
        return graph.is_none_or(|g| reaches(g, *na, *nb));
    }
    true
}

#[allow(
    clippy::too_many_arguments,
    reason = "the replay threads the inlining path, substitution and memory view through every level"
)]
fn events_of_in(
    ctx: &Ctx,
    l: &Lifted,
    depth: usize,
    in_loop_outer: bool,
    outer_node: Option<usize>,
    callee: Option<usize>,
    inst: usize,
    ancestors: &[(usize, Option<usize>, usize)],
    subst: &HashMap<u32, ExprId>,
    mem: &mut lift::MemView,
) -> Vec<Event> {
    let free_ptr = expr::konst(U256::from_u64(0x40));
    let apply = |e: ExprId, mem: &lift::MemView| -> ExprId {
        let mut memo = HashMap::new();
        expr::substitute(
            e,
            &|n| match n {
                Node::Arg(i) => subst.get(i).copied(),
                Node::ReturnData(seq, off) if expr::as_const(*off) == Some(U256::ZERO) => {
                    ctx.computed_returns.borrow().get(seq).copied()
                }
                Node::MLoad(a, _) if *a != free_ptr => {
                    let a2 = if subst.is_empty() {
                        *a
                    } else {
                        expr::substitute(
                            *a,
                            &|m| {
                                if let Node::Arg(i) = m {
                                    subst.get(i).copied()
                                } else {
                                    None
                                }
                            },
                            &mut HashMap::new(),
                        )
                    };
                    mem.load(a2)
                }
                _ => None,
            },
            &mut memo,
        )
    };
    let loops = loop_nodes(l);
    let dbg_memview = std::env::var("EVMDEC_DEBUG_MEMVIEW").ok();
    let dbg_unfresh = std::env::var("EVMDEC_DEBUG_UNFRESH").is_ok();
    let mut out = Vec::new();
    let mut order = Vec::new();
    let mut seen = HashSet::new();
    fn dfs(l: &Lifted, x: usize, seen: &mut HashSet<usize>, order: &mut Vec<usize>) {
        if !seen.insert(x) {
            return;
        }
        for s in &l.nodes[x].succs {
            dfs(l, *s, seen, order);
        }
        order.push(x);
    }
    dfs(l, l.entry, &mut seen, &mut order);
    order.reverse();
    if !loops.is_empty() {
        let w = writes_of(ctx, loops.iter().map(|n| &l.nodes[*n]), &mut HashSet::new());
        if dbg_unfresh {
            eprintln!(
                "loops in callee={:?} entry pc={}: writes={}",
                callee,
                l.nodes[l.entry].pc,
                w.as_ref()
                    .map_or("pointer".to_string(), |w| format!("{} slots", w.len()))
            );
        }
        forget_writes(mem, w);
    }
    for nid in order {
        let nd = &l.nodes[nid];
        let in_loop = in_loop_outer || loops.contains(&nid);
        let anchor = outer_node.unwrap_or(nid);
        let path: Vec<(usize, Option<usize>, usize)> = ancestors
            .iter()
            .copied()
            .chain(std::iter::once((inst, callee, nid)))
            .collect();
        for s in &nd.stmts {
            let s = lift::map_stmt(s, &|e| apply(e, mem));
            match &s {
                Stmt::Call { seq, .. } => {
                    let computed = computed_result(ctx, &s);
                    match computed {
                        Some(e) => ctx.computed_returns.borrow_mut().insert(*seq, e),
                        None => ctx.computed_returns.borrow_mut().remove(seq),
                    };
                    if let Some(key) = made_by_call(ctx, &s) {
                        let word = expr::intern(Node::ReturnData(*seq, expr::konst(U256::ZERO)));
                        ctx.made.borrow_mut().insert(word, key);
                    }
                }
                Stmt::Copy {
                    kind: op::CODECOPY,
                    dest,
                    src,
                    len,
                    ..
                } => {
                    let fixed = |e: ExprId| expr::as_const(e).and_then(|c| c.as_usize());
                    if let (Some(offset), Some(n)) = (fixed(*src), fixed(*len)) {
                        ctx.code_copies.borrow_mut().push((*dest, offset, n));
                    }
                }
                Stmt::Create {
                    off,
                    len,
                    result,
                    init,
                    ..
                } => {
                    if let Some(key) = created_code(ctx, *off, *len, init.as_deref()) {
                        ctx.made.borrow_mut().insert(*result, key);
                    }
                }
                _ => {}
            }
            let depth = if ctx.inline_left.get() == 0 { 0 } else { depth };
            if let Stmt::Internal { callee: t, .. } = &s {
                let inlined = depth > 0 && ctx.internals.get(t).is_some_and(|f| f.lifted.is_some());
                if !inlined {
                    let w = callee_writes(ctx, *t, &mut HashSet::new());
                    if dbg_unfresh {
                        eprintln!(
                            "non-inlined call to {} from callee={:?} depth={}: writes={}",
                            t,
                            callee,
                            depth,
                            w.as_ref()
                                .map_or("pointer".to_string(), |w| format!("{} slots", w.len()))
                        );
                    }
                    forget_writes(mem, w);
                }
            }
            if let Some(want) = &dbg_memview {
                if let Stmt::MStore { off, val, .. } = &s {
                    let w =
                        u64::from_str_radix(want.trim_start_matches("0x"), 16).unwrap_or(u64::MAX);
                    if expr::as_const(*off) == Some(U256::from_u64(w)) {
                        eprintln!(
                            "memview store [{}] = {} (callee={:?} node={} pc={})",
                            want,
                            emit::fmt_expr(*val, &Names::default()),
                            callee,
                            nid,
                            nd.pc
                        );
                    }
                }
            }
            match &s {
                Stmt::MStore { off, width: 32, .. } if in_loop => mem.unknown(*off, Some(32)),
                Stmt::MStore {
                    off,
                    val,
                    width: 32,
                    ..
                } => mem.store(*off, *val),
                Stmt::MStore { off, .. } => mem.unknown(*off, Some(1)),
                Stmt::Copy {
                    kind: op::MCOPY,
                    dest,
                    src,
                    len,
                    ..
                } => mem.copy(*dest, *src, *len),
                Stmt::Copy { dest, len, .. } => mem.unknown(
                    *dest,
                    expr::as_const(*len)
                        .and_then(|l| l.as_usize())
                        .map(|l| l as u64),
                ),
                Stmt::Call {
                    out_off, out_len, ..
                } => {
                    let ol = expr::as_const(*out_len)
                        .and_then(|l| l.as_usize())
                        .map(|l| l as u64);
                    if ol != Some(0) {
                        mem.unknown(*out_off, ol);
                    }
                }
                _ => {}
            }
            if let Stmt::Internal {
                callee: target,
                args,
                ..
            } = &s
            {
                if depth > 0 {
                    if let Some(f) = ctx.internals.get(target) {
                        if let Some(cl) = &f.lifted {
                            let k = cl.ret_slot.map(|k| k as usize).unwrap_or(usize::MAX);
                            let mut inner: HashMap<u32, ExprId> = HashMap::new();
                            if k != usize::MAX {
                                for (j, a) in args.iter().enumerate() {
                                    if j < k {
                                        inner.insert((k - 1 - j) as u32, *a);
                                    }
                                }
                            }
                            out.push(Event {
                                node: anchor,
                                pc: nd.pc,
                                callee,
                                inst,
                                inner: nid,
                                path: path.clone(),
                                stmt: Some(s.clone()),
                                term: None,
                                in_loop,
                            });
                            ctx.inst_seq.set(ctx.inst_seq.get() + 1);
                            let inlined = events_of_in(
                                ctx,
                                cl,
                                depth - 1,
                                in_loop,
                                Some(anchor),
                                Some(*target),
                                ctx.inst_seq.get(),
                                &path,
                                &inner,
                                mem,
                            );
                            ctx.inline_left
                                .set(ctx.inline_left.get().saturating_sub(inlined.len()));
                            out.extend(inlined);
                            continue;
                        }
                    }
                }
            }
            out.push(Event {
                node: anchor,
                pc: nd.pc,
                callee,
                inst,
                inner: nid,
                path: path.clone(),
                stmt: Some(s),
                term: None,
                in_loop,
            });
        }
        let term = lift::map_term(&nd.term, &|e| apply(e, mem));
        out.push(Event {
            node: anchor,
            pc: nd.pc,
            callee,
            inst,
            inner: nid,
            path: path.clone(),
            stmt: None,
            term: Some(term),
            in_loop,
        });
    }
    out
}

fn reaches(l: &Lifted, a: usize, b: usize) -> bool {
    let mut seen = HashSet::new();
    let mut stack = vec![a];
    while let Some(x) = stack.pop() {
        if x == b {
            return true;
        }
        if !seen.insert(x) {
            continue;
        }
        stack.extend(l.nodes[x].succs.iter().copied());
    }
    false
}

fn short_address(a: &str) -> String {
    if a.len() > 12 {
        format!("{}…{}", &a[..6], &a[a.len() - 4..])
    } else {
        a.to_string()
    }
}

pub(crate) fn display_name(f: &Function) -> String {
    let origin = f
        .origin
        .as_ref()
        .map(|a| format!(" @ {}", a))
        .unwrap_or_default();
    match f.kind {
        FnKind::External => format!(
            "{}{}{}",
            f.name,
            f.selector
                .as_ref()
                .map(|s| format!(" [{}]", s))
                .unwrap_or_default(),
            origin
        ),
        _ => format!("{}{}", f.name, origin),
    }
}

#[allow(
    clippy::too_many_arguments,
    reason = "a finding is built from its fields in one call at every rule site"
)]
pub(crate) fn push(
    findings: &mut Vec<Finding>,
    id: &str,
    title: &str,
    sev: Severity,
    conf: Confidence,
    f: Option<&Function>,
    pc: Option<usize>,
    desc: String,
    evidence: Vec<String>,
    rec: &str,
) {
    findings.push(Finding {
        id: id.into(),
        title: title.into(),
        severity: sev,
        confidence: conf,
        function: f.map(display_name),
        pc,
        description: desc,
        evidence,
        sites: 1,
        recommendation: rec.into(),
        confirmed: false,
        witness: None,
        setup: Vec::new(),
        observed: Vec::new(),
    });
}

fn mapping_root(key: ExprId) -> Option<U256> {
    match expr::node(key) {
        Node::Keccak(words, _) => {
            for w in &words {
                if let Node::Keccak(..) = expr::node(*w) {
                    if let Some(r) = mapping_root(*w) {
                        return Some(r);
                    }
                }
            }
            words
                .iter()
                .filter_map(|w| expr::as_const(*w))
                .find(|c| c.bits() <= 32)
        }
        _ => None,
    }
}

fn is_owner_cond(cond: ExprId) -> bool {
    is_auth_cond(cond) && role_test_root(cond).is_none()
}

fn role_test_root(cond: ExprId) -> Option<U256> {
    fn strip(e: ExprId) -> ExprId {
        match expr::node(e) {
            Node::Op(op::ISZERO, v) => strip(v[0]),
            Node::Op(op::AND, v) if expr::as_const(v[1]).is_some_and(|m| m.is_low_mask()) => {
                strip(v[0])
            }
            _ => e,
        }
    }
    match expr::node(strip(cond)) {
        Node::SLoad(k, _, _) if from_caller(k) => mapping_root(k),
        _ => None,
    }
}

fn is_auth_cond_in(cond: ExprId, roles: &HashSet<U256>) -> bool {
    match role_test_root(cond) {
        Some(root) => roles.contains(&root),
        None => is_auth_cond(cond),
    }
}

fn role_mappings(ctx: &Ctx) -> HashSet<U256> {
    struct Writer {
        owner: bool,
        tests: HashSet<U256>,
        writes: HashSet<U256>,
    }
    let mut writers: Vec<Writer> = Vec::new();
    let mut tested: HashSet<U256> = HashSet::new();
    for f in ctx
        .c
        .functions
        .iter()
        .filter(|f| f.kind != FnKind::Internal && f.kind != FnKind::Orphan)
    {
        let Some(l) = &f.lifted else { continue };
        let mut graphs: Vec<&Lifted> = vec![l];
        graphs.extend(
            transitive_callees(ctx, f)
                .into_iter()
                .filter_map(|cf| cf.lifted.as_ref()),
        );
        let mut w = Writer {
            owner: false,
            tests: HashSet::new(),
            writes: HashSet::new(),
        };
        for g in graphs {
            for nd in &g.nodes {
                for cond in node_conds(nd) {
                    if is_owner_cond(cond) {
                        w.owner = true;
                    }
                    if let Some(r) = role_test_root(cond) {
                        w.tests.insert(r);
                        tested.insert(r);
                    }
                }
                for st in &nd.stmts {
                    if let Stmt::SStore {
                        key,
                        transient: false,
                        ..
                    } = st
                    {
                        if let Some(r) = mapping_root(*key) {
                            w.writes.insert(r);
                        }
                    }
                }
            }
        }
        writers.push(w);
    }
    let mut roles: HashSet<U256> = HashSet::new();
    loop {
        let mut changed = false;
        for r in &tested {
            if roles.contains(r) {
                continue;
            }
            let gated = writers
                .iter()
                .filter(|w| w.writes.contains(r))
                .all(|w| w.owner || w.tests.iter().any(|t| t == r || roles.contains(t)));
            if gated {
                roles.insert(*r);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    roles
}

#[derive(Clone, Debug, Default)]
pub struct Gates {
    pub slots: Vec<U256>,
    pub keys: Vec<ExprId>,
}

pub fn gates(c: &Contract) -> Gates {
    fn strip(e: ExprId) -> ExprId {
        match expr::node(e) {
            Node::Op(op::ISZERO, v) => strip(v[0]),
            Node::Op(op::AND, v) if expr::as_const(v[1]).is_some_and(|m| m.is_low_mask()) => {
                strip(v[0])
            }
            _ => e,
        }
    }
    let mut out = Gates::default();
    for f in &c.functions {
        let Some(l) = &f.lifted else { continue };
        for cond in l.nodes.iter().flat_map(node_conds) {
            let tested = strip(cond);
            if let Node::SLoad(k, false, _) = expr::node(tested) {
                let closed = !mentions(k, &|n| {
                    !matches!(
                        n,
                        Node::Const(_) | Node::Op(..) | Node::Keccak(..) | Node::Env(op::CALLER, _)
                    )
                });
                if closed && from_caller(k) && !out.keys.contains(&k) {
                    out.keys.push(k);
                }
            }
            walk(tested, &mut HashSet::new(), &mut |_, n| {
                let Node::Op(op::EQ | op::SUB | op::XOR, v) = n else {
                    return;
                };
                for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
                    let slot = ssa::stored_address_slot(b).and_then(expr::as_const);
                    if let (true, Some(slot)) = (is_caller(a), slot) {
                        if !out.slots.contains(&slot) {
                            out.slots.push(slot);
                        }
                    }
                }
            });
        }
    }
    out
}

pub fn key_for(key: ExprId, caller: U256) -> Option<U256> {
    match expr::node(key) {
        Node::Const(c) => Some(c),
        Node::Env(op::CALLER, _) => Some(caller),
        Node::Keccak(words, 0) => {
            let mut bytes = Vec::with_capacity(32 * words.len());
            for w in words {
                bytes.extend_from_slice(&key_for(w, caller)?.to_be_bytes());
            }
            Some(U256::from_be_bytes(&crate::keccak::keccak256(&bytes)))
        }
        Node::Op(o, v) if v.len() == 2 => {
            let a = expr::konst(key_for(v[0], caller)?);
            let b = expr::konst(key_for(v[1], caller)?);
            expr::as_const(expr::op2(o, a, b))
        }
        _ => None,
    }
}

pub fn is_auth_cond(cond: ExprId) -> bool {
    fn strip(e: ExprId) -> ExprId {
        match expr::node(e) {
            Node::Op(op::ISZERO, v) => strip(v[0]),
            Node::Op(op::AND, v) if expr::as_const(v[1]).is_some_and(|m| m.is_low_mask()) => {
                strip(v[0])
            }
            _ => e,
        }
    }
    let c = strip(cond);
    match expr::node(c) {
        Node::Op(op::EQ | op::SUB | op::XOR, v) => {
            let is_caller = |e: ExprId| matches!(expr::node(strip(e)), Node::Env(op::CALLER, _));
            for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
                if is_caller(a) {
                    let b2 = strip(b);
                    if let Node::SLoad(k, _, _) = expr::node(b2) {
                        if !from_caller(k) {
                            return true;
                        }
                    }
                    if expr::as_const(b2).is_some_and(|c| c.byte_len() >= 15) {
                        return true;
                    }
                    if matches!(
                        expr::node(b2),
                        Node::Env(op::ADDRESS, _) | Node::Env(op::ORIGIN, _)
                    ) {
                        return true;
                    }
                }
            }
            false
        }
        Node::SLoad(k, _, _) => from_caller(k),
        _ => false,
    }
}

fn node_conds(nd: &lift::LNode) -> Vec<ExprId> {
    let mut v: Vec<ExprId> = nd
        .stmts
        .iter()
        .filter_map(|s| {
            if let Stmt::Require { cond, .. } = s {
                Some(*cond)
            } else {
                None
            }
        })
        .collect();
    if let Term::Branch { cond, .. } = &nd.term {
        v.push(*cond);
    }
    v
}

fn has_caller_check(l: &Lifted, before: Option<usize>, roles: &HashSet<U256>) -> bool {
    for nd in &l.nodes {
        if node_conds(nd)
            .into_iter()
            .any(|c| is_auth_cond_in(c, roles))
            && before.is_none_or(|b| reaches(l, nd.id, b))
        {
            return true;
        }
    }
    false
}

fn transitive_callees<'a>(ctx: &'a Ctx, f: &Function) -> Vec<&'a Function> {
    let mut out = Vec::new();
    let mut seen: HashSet<usize> = HashSet::new();
    let mut work: Vec<usize> = f.calls.clone();
    while let Some(pc) = work.pop() {
        if !seen.insert(pc) {
            continue;
        }
        if let Some(cf) = ctx.internals.get(&pc) {
            out.push(*cf);
            work.extend(cf.calls.iter().copied());
        }
    }
    out
}

fn any_caller_check(ctx: &Ctx, f: &Function) -> bool {
    let Some(l) = &f.lifted else { return false };
    if has_caller_check(l, None, &ctx.roles) {
        return true;
    }
    transitive_callees(ctx, f).iter().any(|cf| {
        cf.lifted
            .as_ref()
            .is_some_and(|cl| has_caller_check(cl, None, &ctx.roles))
    })
}

fn auth_slots(ctx: &Ctx) -> HashSet<ExprId> {
    let mut slots = HashSet::new();
    for f in &ctx.c.functions {
        let Some(l) = &f.lifted else { continue };
        for nd in &l.nodes {
            for cond in node_conds(nd) {
                if is_auth_cond_in(cond, &ctx.roles) {
                    collect_sload_keys(cond, &mut slots);
                }
            }
        }
    }
    slots
}

fn collect_sload_keys(e: ExprId, out: &mut HashSet<ExprId>) {
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 20_000 {
            continue;
        }
        if let Node::SLoad(k, false, _) = expr::node(x) {
            if !from_caller(k) {
                out.insert(k);
            }
        }
        stack.extend(expr::children(x));
    }
}

const EIP1967_IMPL: &str = "0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc";
const EIP1967_ADMIN: &str = "0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103";
const EIP1967_BEACON: &str = "0xa3f0ad74e5423aebfd80d3ef4346578335a9a72aeaee59ff6cb3582b35133d50";

fn legacy_consequence(before_0_5: bool) -> &'static str {
    if before_0_5 {
        "Arithmetic does not check for overflow and ABI decoding does not validate the upper bits of address and bool arguments."
    } else {
        "Arithmetic does not check for overflow."
    }
}

pub fn analyze(c: &Contract) -> Report {
    let world = World::of(c);
    if let Some(a) = &c.address {
        world
            .reports
            .borrow_mut()
            .insert(a.to_ascii_lowercase(), None);
    }
    analyze_in(c, &world)
}

fn analyze_in<'a>(c: &'a Contract, world: &'a World<'a>) -> Report {
    let internals: HashMap<usize, &Function> = c
        .functions
        .iter()
        .filter(|f| f.kind == FnKind::Internal)
        .map(|f| (f.pc, f))
        .collect();
    let version = c.info.metadata.as_ref().and_then(|m| {
        if m.compiler == "solc" {
            m.version_tuple()
        } else {
            None
        }
    });
    let mut ctx = Ctx {
        c,
        world,
        computed_returns: RefCell::default(),
        made: RefCell::default(),
        code_copies: RefCell::default(),
        internals,
        version,
        vyper: c.language.starts_with("vyper"),
        callee_writes: Default::default(),
        inst_seq: std::cell::Cell::new(0),
        inline_left: std::cell::Cell::new(MAX_INLINED_EVENTS),
        divides: Default::default(),
        roles: HashSet::new(),
        slot_writes: HashSet::new(),
        field_writes: HashSet::new(),
        transient_storage: false,
        calldata_copies: false,
        unguarded_extenders: HashMap::new(),
    };
    ctx.roles = role_mappings(&ctx);
    for f in c.functions.iter().filter(|f| f.kind == FnKind::External) {
        if any_caller_check(&ctx, f) {
            continue;
        }
        let Some(l) = &f.lifted else { continue };
        let mut grown: HashSet<U256> = HashSet::new();
        for ev in events_of(&ctx, l, 5, false) {
            if let Some(Stmt::SStore {
                key,
                val,
                transient: false,
                ..
            }) = &ev.stmt
            {
                if let Some(k) = expr::as_const(*key) {
                    if let Node::Op(op::ADD, v) = expr::node(*val) {
                        if v.iter().any(|x| reads_slot(*x, *key))
                            && v.iter().any(|x| expr::as_const(*x).is_some())
                        {
                            grown.insert(k);
                        }
                    }
                }
            }
        }
        for k in grown {
            ctx.unguarded_extenders
                .entry(k)
                .or_default()
                .push(display_name(f));
        }
    }
    for f in &c.functions {
        let Some(l) = &f.lifted else { continue };
        for nd in &l.nodes {
            for st in &nd.stmts {
                match st {
                    Stmt::SStore {
                        key,
                        val,
                        transient: false,
                        ..
                    } => {
                        if let Some(k) = expr::as_const(*key) {
                            match emit::packed_write(*key, *val) {
                                Some((k2, off, bits, _)) => {
                                    ctx.field_writes.insert((k2, off, bits));
                                }
                                None => {
                                    ctx.slot_writes.insert(k);
                                }
                            }
                        }
                    }
                    Stmt::SStore {
                        transient: true, ..
                    } => ctx.transient_storage = true,
                    Stmt::Copy {
                        kind: op::CALLDATACOPY,
                        ..
                    } if f.kind == FnKind::External => ctx.calldata_copies = true,
                    _ => {}
                }
            }
            if lift::node_exprs(nd)
                .iter()
                .any(|e| mentions(*e, &|n| matches!(n, Node::SLoad(_, true, _))))
            {
                ctx.transient_storage = true;
            }
        }
    }
    let ctx = ctx;
    let mut findings: Vec<Finding> = Vec::new();
    let mut report = Report::default();
    let callees = decompile::Callees::of(&c.functions, c.compiler.kind);
    let names_for = |f: &Function| -> Names {
        decompile::make_names(
            f,
            &c.storage,
            c.compiler.layout,
            &c.string_loaders,
            &callees,
        )
    };

    let sels: HashSet<String> = c
        .functions
        .iter()
        .filter_map(|f| f.signature.clone())
        .collect();
    let has = |s: &str| sels.contains(s);
    let mut kinds = Vec::new();
    if has("transfer(address,uint256)") && has("balanceOf(address)") && has("totalSupply()") {
        kinds.push("ERC20 token".to_string());
    }
    if has("ownerOf(uint256)") && has("safeTransferFrom(address,address,uint256)") {
        kinds.push("ERC721 NFT".to_string());
    }
    if has("balanceOfBatch(address[],uint256[])") {
        kinds.push("ERC1155".to_string());
    }
    if has("execTransaction(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,bytes)") {
        kinds.push("Gnosis Safe multisig".to_string());
    }
    if has("getReserves()") && has("swap(uint256,uint256,address,bytes)") {
        kinds.push("Uniswap V2 pair".to_string());
    }
    if has("asset()") && has("convertToShares(uint256)") {
        kinds.push("ERC4626 vault".to_string());
    }
    if has("upgradeTo(address)") || has("upgradeToAndCall(address,bytes)") {
        kinds.push("Upgradeable (UUPS/transparent admin)".to_string());
    }

    let auth = auth_slots(&ctx);
    let caps = capped_slots(c);
    let mut external_calls: BTreeSet<String> = BTreeSet::new();
    let mut privileged: Vec<String> = Vec::new();
    let mut unauthenticated: Vec<String> = Vec::new();
    let mut facts: Vec<FnFacts> = Vec::new();
    let mut summaries: Vec<FnSummary> = Vec::new();
    let mut stores: Vec<origin::Store> = Vec::new();
    let mut uses: Vec<StoredUse> = Vec::new();
    let mut lock_slots: HashMap<ExprId, HashSet<usize>> = HashMap::new();
    let mut any_payable = false;
    let mut any_ether_out = false;
    let mut fallback_delegatecall = false;
    let mut diamond_router = false;
    let mut eip1967 = false;
    let mut delegatecall_targets_storage = false;

    for f in c
        .functions
        .iter()
        .filter(|f| f.kind != FnKind::Internal && f.kind != FnKind::Orphan)
    {
        let Some(l) = &f.lifted else { continue };
        let names = names_for(f);
        let events = events_of(&ctx, l, 5, false);
        let caller_checked = any_caller_check(&ctx, f);
        let fact = collect_facts(&ctx, f, &events, caller_checked, &names);
        summaries.extend(summarise(&ctx, &fact, &events, &auth, &names));
        stored_uses(
            &ctx,
            &fact,
            facts.len(),
            &events,
            &names,
            &mut stores,
            &mut uses,
        );
        facts.push(fact);
        let loop_cap: Option<u64> = {
            let mut keys: Vec<U256> = Vec::new();
            let mut graphs: Vec<&Lifted> = vec![l];
            graphs.extend(
                transitive_callees(&ctx, f)
                    .into_iter()
                    .filter_map(|cf| cf.lifted.as_ref()),
            );
            for g in graphs {
                let lp = loop_nodes(g);
                for nd in &g.nodes {
                    if !lp.contains(&nd.id) {
                        continue;
                    }
                    if let Term::Branch { cond, .. } = &nd.term {
                        keys.extend(const_slot_keys(*cond));
                    }
                }
            }
            if keys.is_empty() || !keys.iter().all(|k| caps.contains_key(k)) {
                None
            } else {
                keys.iter().filter_map(|k| caps.get(k).copied()).max()
            }
        };
        let state_changing = f.effects.writes_storage
            || f.effects.calls
            || f.effects.selfdestruct
            || f.effects.creates;
        if caller_checked && state_changing {
            privileged.push(display_name(f));
        } else if state_changing && f.kind == FnKind::External {
            unauthenticated.push(display_name(f));
        }
        if f.mutability == crate::function::Mutability::Payable {
            any_payable = true;
        }
        let always_reverts = !l.nodes.iter().any(|nd| {
            matches!(
                nd.term,
                Term::Return { .. } | Term::ReturnDyn { .. } | Term::Stop | Term::SelfDestruct(_)
            )
        });

        let const_sloads = |e: ExprId| -> Vec<ExprId> {
            let mut out = Vec::new();
            let mut seen = HashSet::new();
            let mut stack = vec![e];
            while let Some(x) = stack.pop() {
                if !seen.insert(x) || seen.len() > 2000 {
                    continue;
                }
                if let Node::SLoad(k, _, _) = expr::node(x) {
                    if expr::is_const(k) {
                        out.push(k);
                    }
                }
                stack.extend(expr::children(x));
            }
            out
        };
        let const_store = |e: &Event| match &e.stmt {
            Some(Stmt::SStore { key, val, .. }) if expr::is_const(*key) => {
                let restores_const = expr::is_const(*val)
                    || emit::packed_write(*key, *val).is_some_and(|(_, _, _, v)| expr::is_const(v));
                Some((*key, restores_const))
            }
            _ => None,
        };
        let mut last_restore: HashMap<ExprId, usize> = HashMap::new();
        for (j, e) in events.iter().enumerate() {
            if let Some((key, true)) = const_store(e) {
                last_restore.insert(key, j);
            }
        }
        let mut stored: Vec<ExprId> = Vec::new();
        let mut tested: HashSet<ExprId> = HashSet::new();
        let mut guarded_calls: HashSet<usize> = HashSet::new();
        for (i, ev) in events.iter().enumerate() {
            if matches!(&ev.stmt, Some(Stmt::Call { kind, .. }) if *kind == op::CALL || *kind == op::CALLCODE)
            {
                let guarded = stored
                    .iter()
                    .find(|k| tested.contains(*k) && last_restore.get(*k).is_some_and(|j| *j > i));
                if let Some(slot) = guarded {
                    lock_slots.entry(*slot).or_default().insert(f.pc);
                    guarded_calls.insert(i);
                }
            }
            if let Some((key, _)) = const_store(ev) {
                if !stored.contains(&key) {
                    stored.push(key);
                }
            }
            if let Some(Stmt::Require { cond, .. }) = &ev.stmt {
                tested.extend(const_sloads(*cond));
            }
            if let Some(Term::Branch { cond, .. }) = &ev.term {
                tested.extend(const_sloads(*cond));
            }
        }
        let seqs_in = |roots: Vec<ExprId>, pick: &dyn Fn(&Node) -> Option<u32>| {
            let mut found: HashSet<u32> = HashSet::new();
            let mut seen: HashSet<ExprId> = HashSet::new();
            let mut pending = roots;
            while let Some(x) = pending.pop() {
                if !seen.insert(x) {
                    continue;
                }
                found.extend(pick(&expr::node(x)));
                pending.extend(expr::children(x));
            }
            found
        };
        let carried: Vec<ExprId> = l.edge_assigns.values().flatten().map(|(_, v)| *v).collect();
        let checked: Vec<ExprId> = events
            .iter()
            .flat_map(|e| {
                let stmt = match &e.stmt {
                    Some(Stmt::Drop(_)) | None => Vec::new(),
                    Some(other) => stmt_exprs(other),
                };
                let term = match &e.term {
                    Some(Term::Branch { cond, .. }) => vec![*cond],
                    Some(Term::Return { data: Some(d), .. }) => d.clone(),
                    _ => Vec::new(),
                };
                stmt.into_iter().chain(term)
            })
            .chain(carried.iter().copied())
            .collect();
        let used_results = seqs_in(checked, &|n| match n {
            Node::CallResult(s) => Some(*s),
            _ => None,
        });
        let everything: Vec<ExprId> = events
            .iter()
            .flat_map(event_exprs)
            .chain(carried.iter().copied())
            .collect();
        let read_returns = seqs_in(everything, &|n| match n {
            Node::ReturnData(s, _) => Some(*s),
            _ => None,
        });
        for (i, ev) in events.iter().enumerate() {
            let Some(stmt) = &ev.stmt else { continue };
            let names = &names;
            match stmt {
                Stmt::Call {
                    kind,
                    addr,
                    value,
                    input,
                    input_head,
                    in_off,
                    in_len,
                    out_len,
                    result,
                    gas,
                    seq,
                    ..
                } => {
                    let target = emit::fmt_expr(*addr, names);
                    let line = emit::fmt_stmt(stmt, names);
                    external_calls.insert(format!(
                        "{}: {}",
                        display_name(f),
                        line.trim_end_matches(';')
                    ));
                    let in_len_c = expr::as_const(*in_len).and_then(|l| l.as_usize());
                    let selector: Option<u32> = input
                        .as_ref()
                        .and_then(|w| w.first().copied())
                        .or(input_head.first().copied())
                        .and_then(|w0| emit::leading_selector(w0, in_len_c));
                    let selector_known =
                        selector.is_some() || expr::as_const(*in_len) == Some(U256::ZERO);
                    if std::env::var("EVMDEC_DEBUG_CALLS").is_ok() {
                        eprintln!(
                            "call pc={} fn={} sel={:?} head=[{}] in_len={}",
                            ev.pc,
                            f.name,
                            selector,
                            input_head
                                .iter()
                                .map(|w| emit::fmt_expr(*w, names))
                                .collect::<Vec<_>>()
                                .join(", "),
                            emit::fmt_expr(*in_len, names)
                        );
                    }
                    let words_view: Option<&Vec<ExprId>> =
                        input.as_ref().or(if input_head.is_empty() {
                            None
                        } else {
                            Some(input_head)
                        });
                    if value.is_some_and(|v| expr::as_const(v) != Some(U256::ZERO)) {
                        any_ether_out = true;
                    }
                    let value_nonzero =
                        value.is_some_and(|v| expr::as_const(v) != Some(U256::ZERO));
                    let gas_stipend = expr::as_const(*gas)
                        .is_some_and(|g| g <= U256::from_u64(2300))
                        || matches!(expr::node(*gas), Node::Op(op::MUL, ref v) if expr::as_const(v[1]) == Some(U256::from_u64(2300)) || expr::as_const(v[0]) == Some(U256::from_u64(2300)));
                    let user_target = from_calldata(*addr) || from_caller(*addr);
                    let storage_target = from_storage(*addr);
                    let precompile = expr::as_const(*addr).is_some_and(|a| a <= U256::from_u64(10));

                    if *kind == op::DELEGATECALL || *kind == op::CALLCODE {
                        if f.kind == FnKind::Fallback {
                            fallback_delegatecall = true;
                        }
                        if storage_target {
                            delegatecall_targets_storage = true;
                        }
                        let router = storage_target
                            && ctx.c.diamond_lookup.is_some()
                            && f.kind == FnKind::Fallback;
                        if router {
                            diamond_router = true;
                        } else if from_calldata(*addr) && !caller_checked && always_reverts {
                            push(&mut findings, "delegatecall-simulation", "Delegatecall to a caller-controlled address in an always-reverting function", Severity::Info, Confidence::Medium, Some(f), Some(ev.pc),
                                format!("`{}` delegatecalls to `{}` from calldata, but every path of the function reverts, so the call's effects are rolled back (simulation helper).", f.name, target),
                                vec![line.clone()], "Make sure no path can return successfully.");
                        } else if from_calldata(*addr) && !caller_checked {
                            push(&mut findings, "arbitrary-delegatecall", "Delegatecall to a caller-controlled address", Severity::Critical, Confidence::High, Some(f), Some(ev.pc),
                                format!("`{}` delegatecalls to `{}`, which is derived from calldata, without any msg.sender check. Anyone can execute arbitrary code in this contract's storage context (take over storage, selfdestruct).", f.name, target),
                                vec![line.clone()], "Restrict the target to a whitelist or trusted storage slot and gate the function with access control.");
                        } else if from_calldata(*addr) {
                            push(&mut findings, "delegatecall-user-target", "Delegatecall target derived from calldata (access-controlled)", Severity::High, Confidence::Medium, Some(f), Some(ev.pc),
                                format!("`{}` delegatecalls to `{}` derived from calldata. Only safe if the caller check is sufficient and the target is trusted.", f.name, target), vec![line.clone()], "Validate the target against an allowlist even for privileged callers.");
                        } else if !storage_target && !is_const_addr(*addr) {
                            push(&mut findings, "delegatecall-dynamic-target", "Delegatecall to a computed address", Severity::Medium, Confidence::Low, Some(f), Some(ev.pc),
                                format!("`{}` delegatecalls to `{}`.", f.name, target), vec![line.clone()], "Make sure the computed implementation cannot be influenced by callers.");
                        }
                    }

                    if *kind == op::CALL || *kind == op::CALLCODE {
                        let later_write = events[i + 1..].iter().any(|e2| {
                            let hit = matches!(&e2.stmt, Some(Stmt::SStore { .. }))
                                && ev_reaches(&ctx, l, ev, e2);
                            if hit && std::env::var("EVMDEC_DEBUG_REENTRANCY").is_ok() {
                                eprintln!(
                                    "[reentrancy] {} call pc={} inst={} inner={} node={} callee={:?} -> store pc={} inst={} inner={} node={} callee={:?}: {}",
                                    f.name, ev.pc, ev.inst, ev.inner, ev.node, ev.callee, e2.pc, e2.inst, e2.inner, e2.node, e2.callee,
                                    e2.stmt.as_ref().map(|st| emit::fmt_stmt(st, names)).unwrap_or_default()
                                );
                            }
                            hit
                        });
                        let hook = selector.is_some_and(|s| CALLBACK_SELECTORS.contains(&s));
                        if later_write && !precompile {
                            let (id, sev, conf, extra) = if guarded_calls.contains(&i) {
                                ("reentrancy", Severity::Info, Confidence::Medium, " A storage lock written before and after the call looks like a reentrancy guard, so this is reported for awareness only.")
                            } else if fixed_in_storage(&ctx, *addr) && !hook {
                                ("reentrancy-fixed-callee", Severity::Info, Confidence::Low, " The callee address is held in storage that no runtime code writes, so it was fixed at deployment: only that one contract could re-enter, and only if it is malicious or compromised.")
                            } else if self_deployed(&events[..i], *addr) && !hook {
                                ("reentrancy-fixed-callee", Severity::Info, Confidence::Low, " The callee is a contract this function has just deployed from the running contract's own code, so what it does is as fixed as this contract is.")
                            } else if gas_stipend {
                                ("reentrancy", Severity::Low, Confidence::Medium, " The call forwards only a 2300 gas stipend (`transfer`/`send`), which limits what a reentrant callee can do.")
                            } else if hook {
                                ("reentrancy", Severity::High, Confidence::High, " The call is a token transfer with a receiver hook (ERC721/ERC1155/ERC777 `on…Received`/`tokensReceived`), so the recipient is called with the state not yet updated.")
                            } else if (value_nonzero || user_target) && caller_checked {
                                ("reentrancy", Severity::Medium, Confidence::Medium, " The function is behind a msg.sender check, so the re-entering callee must be, or be controlled by, an authorised account (an owner-chosen payee that is itself an owner, for instance).")
                            } else if value_nonzero || user_target {
                                ("reentrancy", Severity::High, Confidence::Medium, "")
                            } else {
                                ("reentrancy", Severity::Medium, Confidence::Low, "")
                            };
                            push(&mut findings, id, "State written after an external call (reentrancy)", sev, conf, Some(f), Some(ev.pc),
                                format!("`{}` performs an external call to `{}` and writes storage afterwards. A malicious callee can re-enter before the state update is applied (checks-effects-interactions violated).{}", f.name, target, extra),
                                vec![line.clone()], "Apply the checks-effects-interactions pattern (update state before calling out) or use a reentrancy guard.");
                        }
                        let used = used_results.contains(seq);
                        if !used && !precompile {
                            push(&mut findings, "unchecked-call", "Return value of external call ignored", if value_nonzero { Severity::Medium } else { Severity::Low }, Confidence::High, Some(f), Some(ev.pc),
                                format!("`{}` ignores the success flag of a low-level call to `{}`. If the call fails (reverting callee, out of gas, non-contract address) execution continues as if it succeeded{}.", f.name, target, if value_nonzero { ", and the ether is kept by this contract while state may assume it was sent" } else { "" }),
                                vec![line.clone()], "Check the returned boolean (`require(success)`) or use a high-level call that reverts on failure.");
                        }
                        if input.is_some() {
                            if let Some(sel) = selector {
                                if matches!(sel, SEL_TRANSFER | SEL_TRANSFER_FROM | SEL_APPROVE) {
                                    let out_zero = expr::as_const(*out_len) == Some(U256::ZERO);
                                    let decoded = read_returns.contains(seq);
                                    let window_end = events[i + 1..]
                                        .iter()
                                        .position(|e2| matches!(e2.stmt, Some(Stmt::Call { .. })))
                                        .map_or(events.len(), |k| i + 1 + k);
                                    let mut copied = false;
                                    for e2 in &events[i + 1..window_end] {
                                        if matches!(
                                            e2.stmt,
                                            Some(Stmt::Copy {
                                                kind: op::RETURNDATACOPY,
                                                ..
                                            })
                                        ) {
                                            copied = true;
                                            break;
                                        }
                                        let cond = match (&e2.stmt, &e2.term) {
                                            (Some(Stmt::Require { cond, .. }), _) => Some(*cond),
                                            (_, Some(Term::Branch { cond, .. })) => Some(*cond),
                                            _ => None,
                                        };
                                        if let Some(c) = cond {
                                            if mentions(c, &|n| {
                                                matches!(n, Node::Env(op::RETURNDATASIZE, _))
                                            }) {
                                                copied = true;
                                                break;
                                            }
                                            if mentions(
                                                c,
                                                &|n| matches!(n, Node::CallResult(s2) if *s2 == *seq),
                                            ) {
                                                break;
                                            }
                                        }
                                    }
                                    if out_zero
                                        && !decoded
                                        && !copied
                                        && !matches!(expr::node(*addr), Node::Const(_))
                                    {
                                        let sig = sigs::function(sel);
                                        let name =
                                            sig.as_deref().map(sigs::name_of).unwrap_or("transfer");
                                        let payout =
                                            events[i + 1..].iter().find_map(|e2| match &e2.stmt {
                                                Some(
                                                    st2 @ Stmt::Call {
                                                        value: Some(v),
                                                        addr: a2,
                                                        ..
                                                    },
                                                ) if expr::as_const(*v) != Some(U256::ZERO)
                                                    && from_caller(*a2) =>
                                                {
                                                    Some((
                                                        "sends ether to msg.sender",
                                                        emit::fmt_stmt(st2, names),
                                                    ))
                                                }
                                                Some(
                                                    st2 @ Stmt::Call {
                                                        input: Some(w2),
                                                        in_len: l2,
                                                        ..
                                                    },
                                                ) if w0_selector(&Some(w2.clone()), *l2)
                                                    == Some(SEL_TRANSFER)
                                                    && from_caller(emit::shifted_word_len(
                                                        w2,
                                                        0,
                                                        expr::as_const(*l2)
                                                            .and_then(|l| l.as_usize()),
                                                    )) =>
                                                {
                                                    Some((
                                                        "transfers tokens to msg.sender",
                                                        emit::fmt_stmt(st2, names),
                                                    ))
                                                }
                                                Some(st2 @ Stmt::SStore { key: k2, .. })
                                                    if from_caller(*k2) =>
                                                {
                                                    Some((
                                                        "credits a balance keyed by msg.sender",
                                                        emit::fmt_stmt(st2, names),
                                                    ))
                                                }
                                                _ => None,
                                            });
                                        if let (SEL_TRANSFER_FROM, Some((what, line2)), false) =
                                            (sel, payout, caller_checked)
                                        {
                                            let sev = if what.starts_with("credits") {
                                                Severity::Medium
                                            } else {
                                                Severity::High
                                            };
                                            push(&mut findings, "unchecked-token-pull", "Tokens pulled without checking the result, then paid for", sev, Confidence::Low, Some(f), Some(ev.pc),
                                                format!("`{}` pulls tokens with `transferFrom` on `{}` without reading the result, then {}. With a token that returns `false` instead of reverting (or returns nothing and ignores the call), the pull does nothing and the payout is free. Whether that is possible depends on the token behind `{}`.", f.name, target, what, target),
                                                vec![line.clone(), line2], "Require the call to succeed and its return data, when present, to decode to true (SafeERC20), or credit the balance actually received.");
                                        } else {
                                            push(&mut findings, "erc20-return-ignored", "ERC20 call result not checked", Severity::Low, Confidence::Medium, Some(f), Some(ev.pc),
                                                format!("`{}` calls `{}` on `{}` and never reads the returned boolean. Tokens that return `false` instead of reverting (and tokens that return nothing) are treated as if the transfer succeeded.", f.name, name, target),
                                                vec![line.clone()], "Use a SafeERC20-style wrapper: require the call to succeed and, when return data is present, require it to decode to true.");
                                        }
                                    }
                                }
                            }
                        }
                        let same_addr = |a: ExprId, b: ExprId| {
                            strip_versions(a, &mut HashMap::new())
                                == strip_versions(b, &mut HashMap::new())
                        };
                        let input_from_calldata = match input {
                            Some(w) => w.first().is_some_and(|w0| emit::leading_selector(*w0, expr::as_const(*in_len).and_then(|l| l.as_usize())).is_none() && from_calldata(*w0)),
                            None => events[..i].iter().any(|e| matches!(&e.stmt, Some(Stmt::Copy { kind: op::CALLDATACOPY, dest, .. }) if same_addr(*dest, *in_off))),
                        };
                        let arbitrary = from_calldata(*addr)
                            && input_from_calldata
                            && !caller_checked
                            && !always_reverts
                            && f.kind == FnKind::External;
                        if arbitrary {
                            push(&mut findings, "arbitrary-call", "Arbitrary external call with caller-controlled target and data", Severity::High, Confidence::Medium, Some(f), Some(ev.pc),
                                format!("`{}` calls `{}` with calldata-derived payload and no access control. If this contract holds token approvals or ether, anyone can drain them through it (e.g. calling `transferFrom` on an approved token).", f.name, target),
                                vec![line.clone()], "Restrict callable targets/selectors, or make sure the contract never holds funds or approvals.");
                        }
                        let int_ret_fixed = |e: ExprId| -> bool {
                            let seqs: RefCell<Vec<u32>> = RefCell::new(Vec::new());
                            mentions(e, &|n| {
                                if let Node::IntRet(seq, _) = n {
                                    seqs.borrow_mut().push(*seq);
                                }
                                false
                            });
                            let seqs = seqs.into_inner();
                            seqs.iter().all(|seq| {
                                events[..i].iter().any(|e2| matches!(&e2.stmt, Some(Stmt::Internal { seq: s2, args, .. }) if s2 == seq
                                    && !args.iter().any(|a| from_calldata(*a) || mentions(*a, &|n| matches!(n, Node::MLoad(..) | Node::CopiedWord(..))))))
                            })
                        };
                        let fixed_target = expr::is_const(*addr)
                            || from_storage(*addr)
                            || from_caller(*addr)
                            || mentions(*addr, &|n| {
                                matches!(
                                    n,
                                    Node::Env(op::ADDRESS, _)
                                        | Node::Keccak(..)
                                        | Node::KeccakMem(..)
                                        | Node::ReturnData(..)
                                        | Node::CreateResult(_)
                                        | Node::CopiedWord(op::CODECOPY, _, _)
                                )
                            })
                            || (mentions(*addr, &|n| matches!(n, Node::IntRet(..)))
                                && int_ret_fixed(*addr));
                        if !arbitrary
                            && !fixed_target
                            && !selector_known
                            && !caller_checked
                            && !always_reverts
                            && !precompile
                            && f.kind == FnKind::External
                        {
                            let caller_fed = from_calldata(*addr)
                                || (mentions(*addr, &|n| matches!(n, Node::IntRet(..)))
                                    && !int_ret_fixed(*addr));
                            let sev = if caller_fed {
                                Severity::High
                            } else {
                                Severity::Medium
                            };
                            push(&mut findings, "dynamic-call", "Call target and selector are both computed at run time", sev, Confidence::Low, Some(f), Some(ev.pc),
                                format!("`{}` calls `{}` with a payload whose selector is computed rather than fixed, and the function has no access control. If the caller can influence either (through calldata, a forged proof, or a message the contract trusts), this is an arbitrary call made by this contract.", f.name, target),
                                vec![line.clone()], "Whitelist the targets and the selectors that can be dispatched, and authenticate the source of the request.");
                        }
                        if let (Some(words), Some(SEL_TRANSFER_FROM)) = (words_view, selector) {
                            if !caller_checked && f.kind == FnKind::External && !always_reverts {
                                let from = emit::shifted_word_len(words, 0, in_len_c);
                                let from_user = from_calldata(from)
                                    && !from_caller(from)
                                    && !mentions(from, &|n| matches!(n, Node::Env(op::ADDRESS, _)));
                                let allowance = events.iter().flat_map(event_exprs).any(|e| mentions(e, &|n| matches!(n, Node::SLoad(k, _, _) if from_caller(*k) && contains_expr(*k, from))));
                                let signed = events.iter().any(|e| match &e.stmt {
                                    Some(Stmt::Call {
                                        addr,
                                        input,
                                        input_head,
                                        in_len,
                                        ..
                                    }) => {
                                        expr::as_const(*addr) == Some(U256::ONE)
                                            || input
                                                .as_ref()
                                                .and_then(|w| w.first().copied())
                                                .or(input_head.first().copied())
                                                .and_then(|w0| {
                                                    emit::leading_selector(
                                                        w0,
                                                        expr::as_const(*in_len)
                                                            .and_then(|l| l.as_usize()),
                                                    )
                                                })
                                                == Some(0x1626ba7e)
                                    }
                                    _ => false,
                                });
                                if from_user && !allowance && !signed {
                                    push(&mut findings, "arbitrary-transferfrom", "transferFrom with a caller-chosen `from` address", Severity::High, Confidence::Medium, Some(f), Some(ev.pc),
                                        format!("`{}` calls `transferFrom({}, …)` on `{}` where `from` comes from calldata, with no msg.sender check, no allowance bookkeeping keyed by the caller and no signature. Anyone can move tokens that other users approved to this contract.", f.name, emit::fmt_expr(from, names), target),
                                        vec![line.clone()], "Only transfer from msg.sender, or check an allowance/signature that the `from` account granted to the caller.");
                                }
                            }
                        }
                        if user_target
                            && !caller_checked
                            && !precompile
                            && f.kind == FnKind::External
                            && *kind != op::DELEGATECALL
                        {
                            let used_in_decision = events.iter().any(|e2| matches!(&e2.term, Some(Term::Branch { cond, .. }) if mentions_returndata(*cond, *seq)) || matches!(&e2.stmt, Some(Stmt::Require { cond, .. }) if mentions_returndata(*cond, *seq)));
                            let used_in_effect = events[i + 1..].iter().any(|e2| match &e2.stmt {
                                Some(Stmt::SStore { val, key, .. }) => {
                                    mentions_returndata(*val, *seq)
                                        || mentions_returndata(*key, *seq)
                                }
                                Some(Stmt::Call { input: Some(w), .. }) => {
                                    w.iter().any(|x| mentions_returndata(*x, *seq))
                                }
                                Some(Stmt::Call { value: Some(v), .. }) => {
                                    mentions_returndata(*v, *seq)
                                }
                                _ => false,
                            });
                            let registry_checked = events[..i].iter().any(|e| {
                                let conds: Vec<ExprId> = match (&e.stmt, &e.term) {
                                    (Some(Stmt::Require { cond, .. }), _) => vec![*cond],
                                    (_, Some(Term::Branch { cond, .. })) => vec![*cond],
                                    _ => vec![],
                                };
                                conds.into_iter().any(|c| {
                                    mentions(c, &|n| matches!(n, Node::SLoad(k, _, _) if contains_expr(*k, *addr)))
                                })
                            });
                            let erc20_result_only = matches!(
                                selector,
                                Some(SEL_TRANSFER | SEL_TRANSFER_FROM | SEL_APPROVE)
                            ) && !used_in_effect;
                            if (used_in_decision || used_in_effect)
                                && !registry_checked
                                && !erc20_result_only
                            {
                                push(&mut findings, "untrusted-return-data", "Data returned by a caller-chosen contract drives a decision", Severity::Medium, Confidence::Low, Some(f), Some(ev.pc),
                                    format!("`{}` calls `{}`, an address the caller supplies, and then {} what it returns. The callee can answer anything, so checks based on its answer (ownership, balances, transfer success) can be forged.", f.name, target, if used_in_decision && used_in_effect { "branches on and stores" } else if used_in_decision { "branches on" } else { "stores or forwards" }),
                                    vec![line.clone()], "Only trust return data from addresses taken from storage or a registry; measure effects (balance deltas) instead of believing the callee.");
                            }
                        }
                        if let Some(sel) = selector {
                            if sel == SEL_LATEST_ROUND_DATA || sel == SEL_LATEST_ANSWER {
                                let answer_idx = if sel == SEL_LATEST_ROUND_DATA { 1 } else { 0 };
                                let all: Vec<ExprId> =
                                    events.iter().flat_map(event_exprs).collect();
                                let rd = |idx: u64, e: ExprId| {
                                    mentions(
                                        e,
                                        &|n| matches!(n, Node::ReturnData(s, o) if *s == *seq && expr::as_const(*o) == Some(U256::from_u64(32 * idx))),
                                    )
                                };
                                let answer_checked = all.iter().any(|e| matches!(expr::node(*e), Node::Op(o, ref v) if matches!(o, op::GT | op::LT | op::SGT | op::SLT | op::EQ) && v.iter().any(|x| rd(answer_idx, *x))));
                                let fresh_checked = sel == SEL_LATEST_ROUND_DATA
                                    && all.iter().any(|e| {
                                        rd(3, *e)
                                            && mentions(*e, &|n| {
                                                matches!(n, Node::Env(op::TIMESTAMP, _))
                                            })
                                    });
                                if !answer_checked
                                    || (sel == SEL_LATEST_ROUND_DATA && !fresh_checked)
                                {
                                    push(&mut findings, "oracle-unchecked", "Price feed answer used without validity or staleness checks", Severity::Medium, Confidence::Medium, Some(f), Some(ev.pc),
                                        format!("`{}` reads a Chainlink-style feed on `{}`{}{}.", f.name, target, if answer_checked { "" } else { " without checking that the answer is positive" }, if sel == SEL_LATEST_ROUND_DATA && !fresh_checked { " and without comparing `updatedAt` to the current time" } else { "" }),
                                        vec![line.clone()], "Require answer > 0 and block.timestamp - updatedAt below a freshness bound; handle a reverting feed.");
                                }
                            }
                        }
                        if let (Some(words), Some(SEL_TRANSFER_FROM)) = (words_view, selector) {
                            let to = emit::shifted_word_len(words, 1, in_len_c);
                            if mentions(to, &|n| matches!(n, Node::Env(op::ADDRESS, _))) {
                                let amount = emit::shifted_word_len(words, 2, in_len_c);
                                let credited = events[i + 1..].iter().any(|e2| matches!(&e2.stmt, Some(Stmt::SStore { val, .. }) if contains_expr(*val, amount)));
                                let measured = events[i + 1..].iter().any(|e2| matches!(&e2.stmt, Some(Stmt::Call { input: Some(w), in_len, .. }) if w.first().and_then(|w0| emit::leading_selector(*w0, expr::as_const(*in_len).and_then(|l| l.as_usize()))) == Some(SEL_BALANCE_OF)));
                                if credited && !measured && !expr::is_const(amount) {
                                    push(&mut findings, "fee-on-transfer", "Token amount credited without measuring the balance received", Severity::Low, Confidence::Low, Some(f), Some(ev.pc),
                                        format!("`{}` pulls `{}` tokens with transferFrom and then books that same amount into storage. Fee-on-transfer, rebasing or non-standard tokens deliver a different amount than requested.", f.name, emit::fmt_expr(amount, names)),
                                        vec![line.clone()], "Credit `balanceOf(this)` after minus before, or restrict the accepted tokens.");
                                }
                            }
                        }
                        if let (Some(words), Some(sel)) = (words_view, selector) {
                            if let Some((given, received, how)) =
                                reverse_quote(&ctx, l, &events, words, sel, in_len_c)
                            {
                                push(&mut findings, "reverse-quote-rounding", "Caller-chosen output with a computed input bounded only by zero", Severity::Medium, Confidence::Medium, Some(f), Some(ev.pc),
                                    format!("`{}` lets the caller fix the amount it receives ({}) while the amount it gives, `{}`, is computed with a division and only required to be nonzero{}. When the balance behind the computation is small relative to the arithmetic's precision, the computed amount floors to dust and the caller gets the full output for almost nothing (Balancer V1 `joinswapPoolAmountOut`, 2026).", f.name, received, emit::fmt_expr(given, names), how),
                                    vec![line.clone()], "Round the computed input up and the output down, and require a minimum input relative to the output (or a minimum reserve) instead of a nonzero check.");
                            }
                        }
                        if let (Some(v), true, true, false, FnKind::External) = (
                            *value,
                            value_nonzero,
                            from_caller(*addr),
                            caller_checked,
                            f.kind,
                        ) {
                            let graph_of = |ev2: &Event| -> &Lifted {
                                ev2.callee
                                    .and_then(|pc| ctx.internals.get(&pc))
                                    .and_then(|cf| cf.lifted.as_ref())
                                    .unwrap_or(l)
                            };
                            let caller_slot = |e: ExprId, g: &Lifted| {
                                let mut keys = Vec::new();
                                let mut seen = HashSet::new();
                                let mut stack = vec![e];
                                while let Some(x) = stack.pop() {
                                    if !seen.insert(x) || seen.len() > 5000 {
                                        continue;
                                    }
                                    if let Node::SLoad(k, ..) = expr::node(x) {
                                        keys.push(k);
                                    }
                                    stack.extend(expr::children(x));
                                }
                                keys.iter().any(|k| caller_derived(g, &events, *k, 3))
                            };
                            let accounted = events[..i].iter().any(|e| match (&e.stmt, &e.term) {
                                (Some(Stmt::SStore { key, .. }), _) => {
                                    caller_derived(graph_of(e), &events, *key, 3)
                                }
                                (Some(Stmt::Require { cond, .. }), _) => {
                                    caller_slot(*cond, graph_of(e))
                                }
                                (_, Some(Term::Branch { cond, .. })) => {
                                    caller_slot(*cond, graph_of(e))
                                }
                                (
                                    Some(Stmt::Call {
                                        input: Some(w),
                                        in_len,
                                        ..
                                    }),
                                    _,
                                ) => {
                                    w0_selector(&Some(w.clone()), *in_len)
                                        == Some(SEL_TRANSFER_FROM)
                                        && from_caller(emit::shifted_word_len(
                                            w,
                                            0,
                                            expr::as_const(*in_len).and_then(|l| l.as_usize()),
                                        ))
                                }
                                _ => false,
                            });
                            if !from_caller(v) && !accounted {
                                push(&mut findings, "unprotected-ether-withdrawal", "Ether sent to msg.sender without per-caller accounting", Severity::Medium, Confidence::Low, Some(f), Some(ev.pc),
                                    format!("`{}` sends `{}` wei to msg.sender; the amount is not derived from a msg.sender-keyed balance and the function has no access control.", f.name, emit::fmt_expr(v, names)),
                                    vec![line.clone()], "Verify the amount is bounded by what the caller is owed.");
                            }
                        }
                        if let (Some(v), true) = (*value, value_nonzero) {
                            let wrapping = c.compiler.kind == compiler::Kind::Solc
                                && c.compiler.is_below(compiler::Version::new(0, 8, 0));
                            let unbounded_param = |e: ExprId| -> bool {
                                mentions(
                                    e,
                                    &|n| matches!(n, Node::Op(op::SUB | op::MUL, ref w) if w.iter().any(|x| from_calldata(*x))),
                                )
                            };
                            let bounded = events[..i]
                                .iter()
                                .flat_map(|e| {
                                    let mut v = Vec::new();
                                    if let Some(Stmt::Require { cond, .. }) = &e.stmt {
                                        v.push(*cond);
                                    }
                                    if let Some(Term::Branch { cond, .. }) = &e.term {
                                        v.push(*cond);
                                    }
                                    v
                                })
                                .any(|cond| {
                                    from_calldata(cond)
                                        && matches!(
                                            expr::node(cond),
                                            Node::Op(op::LT | op::GT | op::SLT | op::SGT, _)
                                                | Node::Op(op::ISZERO, _)
                                        )
                                });
                            if wrapping && !ctx.vyper && unbounded_param(v) && !bounded {
                                let sev = if caller_checked {
                                    Severity::Low
                                } else {
                                    Severity::Medium
                                };
                                push(&mut findings, "unbounded-payout-parameter", "Payout amount computed from an unbounded parameter with wrapping arithmetic", sev, Confidence::Low, Some(f), Some(ev.pc),
                                    format!("`{}` sends `{}`: the amount is computed with `-` or `*` from a call parameter that no earlier check bounds, and this compiler version does not check overflow. A parameter outside the intended range wraps the amount instead of reverting{}.", f.name, emit::fmt_expr(v, names), if caller_checked { "; the function is access-controlled, so this needs a privileged mistake" } else { "" }),
                                    vec![line.clone()], "Bound the parameter with a require, or use checked arithmetic (SafeMath / solc >= 0.8).");
                            }
                        }
                        if ev.in_loop && !precompile {
                            let required = events.iter().any(|e2| match (&e2.stmt, &e2.term) {
                                (Some(Stmt::Require { cond, .. }), _)
                                | (_, Some(Term::Branch { cond, .. })) => mentions(
                                    *cond,
                                    &|n| matches!(n, Node::CallResult(s) if *s == *seq),
                                ),
                                _ => false,
                            });
                            let array = array_root_of(*addr);
                            let extenders = array.and_then(|a| ctx.unguarded_extenders.get(&a));
                            if let (true, true, Some(a), Some(who)) =
                                (value_nonzero, required, array, extenders)
                            {
                                let array_name =
                                    emit::fmt_slot(expr::konst(a), names, SlotSpace::Persistent);
                                let who: Vec<&str> = who.iter().map(String::as_str).collect();
                                push(&mut findings, "blocking-payout-loop", "A single entry can block the payout loop", Severity::Medium, Confidence::Medium, Some(f), Some(ev.pc),
                                    format!("`{}` sends ether to every address in `{}` and reverts unless each call succeeds. {} adds entries to that array without access control, so one entry that rejects the call (an account without code, a contract without the function, or one that reverts on purpose) blocks the payout for everyone.", f.name, array_name, join_names(&who, 3)),
                                    vec![line.clone()], "Let each member pull its share, or skip failed calls and record what is owed.");
                            } else {
                                let (sev, note) = match loop_cap {
                                    Some(cap) => (Severity::Info, format!(" The loop runs over a storage counter the contract caps at {}, so the iteration is bounded.", cap)),
                                    None => (Severity::Low, String::new()),
                                };
                                push(&mut findings, "call-in-loop", "External call inside a loop", sev, Confidence::Medium, Some(f), Some(ev.pc),
                                    format!("`{}` performs an external call to `{}` inside a loop; one failing or gas-hungry callee can block the whole iteration (denial of service).{}", f.name, target, note), vec![line.clone()], "Prefer pull-payments or bound the iteration.");
                            }
                        }
                        if expr::as_const(*addr) == Some(U256::ONE) {
                            let zero_checked = l.nodes.iter().any(|nd| matches!(&nd.term, Term::Branch { cond, .. } if mentions(*cond, &|n| matches!(n, Node::ReturnData(s, _) if *s == *seq)) || mentions(*cond, &|n| matches!(n, Node::MLoad(..)))));
                            if !zero_checked {
                                push(&mut findings, "ecrecover-zero", "ecrecover result may be the zero address", Severity::Medium, Confidence::Low, Some(f), Some(ev.pc),
                                    format!("`{}` calls the ecrecover precompile; no comparison of the recovered address against zero was found. An invalid signature recovers to address(0), which may match an unset storage slot.", f.name), vec![line.clone()], "Require the recovered signer to be non-zero (or use OpenZeppelin ECDSA).");
                            }
                            if let Some(words) = input.as_ref().filter(|w| !w.is_empty()) {
                                let all: Vec<ExprId> =
                                    events.iter().flat_map(event_exprs).collect();
                                let digest = words[0];
                                let domain_bound =
                                    mentions(digest, &|n| {
                                        matches!(
                                            n,
                                            Node::Env(op::CHAINID, _) | Node::Env(op::ADDRESS, _)
                                        )
                                    }) || matches!(expr::node(digest), Node::KeccakMem(..))
                                        || from_storage(digest);
                                if !domain_bound {
                                    push(&mut findings, "signature-replay-domain", "Signed digest does not bind the chain or this contract", Severity::Medium, Confidence::Low, Some(f), Some(ev.pc),
                                        format!("`{}` verifies a signature over `{}`, which includes neither `block.chainid` nor `address(this)` (no EIP-712 domain). The same signature is valid on every chain and every deployment.", f.name, emit::fmt_expr(digest, names)),
                                        vec![line.clone()], "Sign an EIP-712 digest that includes the chain id and the verifying contract.");
                                }
                                let signer_keyed_write = events.iter().any(|e2| matches!(&e2.stmt, Some(Stmt::SStore { key, .. }) if mentions_returndata(*key, *seq) || contains_expr(*key, digest) || mentions(*key, &|n| matches!(n, Node::Keccak(..) | Node::KeccakMem(..)))));
                                if !signer_keyed_write && !always_reverts {
                                    push(&mut findings, "signature-replay-nonce", "No nonce or consumed-digest bookkeeping for a verified signature", Severity::Medium, Confidence::Low, Some(f), Some(ev.pc),
                                        format!("`{}` recovers a signer but writes no storage keyed by the signer or by the digest, so the same signature can be submitted again.", f.name),
                                        vec![line.clone()], "Store and increment a per-signer nonce, or mark the digest as used.");
                                }
                                if words.len() >= 4 {
                                    let half = U256::from_hex_str(SECP_HALF_ORDER);
                                    let s_checked = all.iter().any(|e| {
                                        mentions(
                                            *e,
                                            &|n| matches!(n, Node::Const(c) if Some(*c) == half),
                                        )
                                    });
                                    if !s_checked {
                                        push(&mut findings, "signature-malleability", "No check that the signature `s` value is canonical", Severity::Low, Confidence::Low, Some(f), Some(ev.pc),
                                            format!("`{}` accepts any `s`; for every valid signature there is a second one with `s' = n - s` that recovers the same signer, which breaks digest-based replay protection.", f.name),
                                            vec![line.clone()], "Require s <= secp256k1n/2 (OpenZeppelin ECDSA does this).");
                                    }
                                }
                            }
                        }
                    }
                    let _ = result;
                }
                Stmt::Create { kind, .. } => {
                    let line = emit::fmt_stmt(stmt, names);
                    push(
                        &mut findings,
                        "contract-creation",
                        if *kind == op::CREATE2 {
                            "Deploys contracts with CREATE2"
                        } else {
                            "Deploys contracts with CREATE"
                        },
                        Severity::Info,
                        Confidence::High,
                        Some(f),
                        Some(ev.pc),
                        format!("`{}` deploys a new contract.", f.name),
                        vec![line],
                        "Informational.",
                    );
                }
                _ => {}
            }
        }

        for (si, ev) in events.iter().enumerate() {
            let Some(Term::SelfDestruct(a)) = &ev.term else {
                continue;
            };
            let a = *a;
            let to_caller = from_caller(a) || from_calldata(a);
            let time_guard = guard_conds(&events).into_iter().find(|c| is_time_cond(*c));
            let paid_before = events[..si].iter().any(|e2| {
                matches!(&e2.stmt, Some(Stmt::Call { value: Some(v), .. })
                    if expr::as_const(*v) != Some(U256::ZERO))
                    && ev_reaches(&ctx, l, e2, ev)
            });
            let state_gate = events[..si]
                .iter()
                .filter(|e2| ev_reaches(&ctx, l, e2, ev))
                .filter_map(|e2| match (&e2.stmt, &e2.term) {
                    (Some(Stmt::Require { cond, .. }), _) => Some(*cond),
                    (_, Some(Term::Branch { cond, .. })) => Some(*cond),
                    _ => None,
                })
                .find(|c| {
                    from_storage(*c)
                        && !from_caller(*c)
                        && !from_calldata(*c)
                        && !is_time_cond(*c)
                        && !mentions(*c, &|n| matches!(n, Node::Env(op::CALLVALUE, _)))
                });
            let (sev, conf, title) = if caller_checked {
                (
                    Severity::Medium,
                    Confidence::Medium,
                    "Contract can self-destruct",
                )
            } else if to_caller && paid_before {
                (
                    Severity::Low,
                    Confidence::Medium,
                    "Self-destruct after the payout forwards the remainder to the caller",
                )
            } else if to_caller && state_gate.is_some() {
                (
                    Severity::Medium,
                    Confidence::Medium,
                    "Contract self-destructs to the caller once a state condition holds",
                )
            } else if to_caller {
                (
                    Severity::Critical,
                    Confidence::High,
                    "Anyone can destroy the contract and collect its balance",
                )
            } else {
                (
                    Severity::Critical,
                    Confidence::High,
                    "Contract can self-destruct",
                )
            };
            let guard_note = if caller_checked {
                " (behind a msg.sender check)".to_string()
            } else if to_caller && paid_before {
                match state_gate {
                    Some(g) => format!(
                        ", but only after the calls above have paid the balance out and only when `{}`: what the caller collects is the remainder",
                        emit::fmt_cond(g, &names)
                    ),
                    None => ", but only after the calls above have paid the balance out: what the caller collects is the remainder".to_string(),
                }
            } else if let Some(g) = state_gate.filter(|_| to_caller) {
                format!(
                    " with no access control, once `{}` holds; whether a caller can bring that about alone decides how serious this is",
                    emit::fmt_cond(g, &names)
                )
            } else if let Some(g) = time_guard {
                format!(
                    " with no access control: the only guard is the time condition `{}`, so once it holds the first caller triggers it",
                    emit::fmt_cond(g, &names)
                )
            } else {
                " with no access control found".to_string()
            };
            let where_ = match ev.callee {
                Some(pc) => format!(" (in the helper `{}`)", names.callee_name(pc)),
                None => String::new(),
            };
            push(&mut findings, "selfdestruct", title, sev, conf, Some(f), Some(ev.pc),
                format!("`{}` can destroy the contract and send its balance to `{}`{}{}.", f.name, emit::fmt_expr(a, &names), guard_note, where_),
                vec![format!("selfdestruct({});", emit::fmt_expr(a, &names))], "Remove selfdestruct or make sure the access control is correct (note: Cancun changed selfdestruct semantics).");
        }
        for nd in &l.nodes {
            if let Term::Unresolved(t) = &nd.term {
                push(&mut findings, "unresolved-jump", "Jump target could not be resolved", Severity::Info, Confidence::High, Some(f), Some(nd.pc), format!("A jump to `{}` could not be resolved statically; code behind it is not shown.", emit::fmt_expr(*t, &names)), vec![], "Review the disassembly around this program counter.");
            }
        }

        for nd in &l.nodes {
            if let Term::Branch { cond, .. } = &nd.term {
                if mentions(*cond, &|n| matches!(n, Node::Env(op::ORIGIN, _)))
                    && matches!(
                        expr::node(*cond),
                        Node::Op(op::EQ, _) | Node::Op(op::ISZERO, _)
                    )
                {
                    push(&mut findings, "tx-origin", "tx.origin used in a condition", Severity::Medium, Confidence::Medium, Some(f), Some(nd.pc),
                        format!("`{}` compares `tx.origin`. Using tx.origin for authorization lets a phishing contract act on behalf of the user.", f.name), vec![format!("if ({})", emit::fmt_expr(*cond, &names))], "Use msg.sender for authorization.");
                }
            }
        }

        {
            let blocky = |n: &Node| {
                matches!(n, Node::Env(o, _) if matches!(*o, op::TIMESTAMP | op::NUMBER | op::PREVRANDAO | op::COINBASE | op::GASLIMIT))
                    || matches!(n, Node::Op(op::BLOCKHASH, _))
            };
            let is_hash = |n: &Node| {
                matches!(
                    n,
                    Node::Keccak(..) | Node::KeccakMem(..) | Node::Op(op::BLOCKHASH, _)
                )
            };
            let mut hashes: Vec<ExprId> = Vec::new();
            for e in events.iter().flat_map(event_exprs) {
                let mut seen = HashSet::new();
                let mut stack = vec![e];
                while let Some(x) = stack.pop() {
                    if !seen.insert(x) || seen.len() > 5000 {
                        continue;
                    }
                    let n = expr::node(x);
                    if is_hash(&n) && mentions(x, &blocky) && !hashes.contains(&x) {
                        hashes.push(x);
                    }
                    stack.extend(expr::children(x));
                }
            }
            if !hashes.is_empty() {
                let uses_hash = |e: ExprId| hashes.iter().any(|h| contains_expr(e, *h));
                let mut reduced: Option<ExprId> = None;
                let mut decided: Option<ExprId> = None;
                let mut pc = l.nodes[l.entry].pc;
                for ev in &events {
                    for e in event_exprs(ev) {
                        let mut seen = HashSet::new();
                        let mut stack = vec![e];
                        while let Some(x) = stack.pop() {
                            if !seen.insert(x) || seen.len() > 5000 {
                                continue;
                            }
                            if let Node::Op(o, v) = expr::node(x) {
                                if matches!(
                                    o,
                                    op::MOD
                                        | op::DIV
                                        | op::SUB
                                        | op::LT
                                        | op::GT
                                        | op::SLT
                                        | op::SGT
                                ) && v.iter().any(|y| uses_hash(*y))
                                    && reduced.is_none()
                                {
                                    reduced = Some(x);
                                    pc = ev.pc;
                                }
                            }
                            stack.extend(expr::children(x));
                        }
                    }
                    if let Some(Term::Branch { cond, .. }) = &ev.term {
                        if uses_hash(*cond) && decided.is_none() {
                            decided = Some(*cond);
                            pc = ev.pc;
                        }
                    }
                }
                let (sev, conf, what) = match (reduced, decided) {
                    (Some(r), _) => (
                        Severity::Medium,
                        Confidence::Medium,
                        emit::fmt_expr(r, &names),
                    ),
                    (None, Some(d)) => {
                        (Severity::Medium, Confidence::Low, emit::fmt_expr(d, &names))
                    }
                    (None, None) => (
                        Severity::Low,
                        Confidence::Low,
                        emit::fmt_expr(hashes[0], &names),
                    ),
                };
                push(&mut findings, "weak-randomness", "Block attributes used as a randomness source", sev, conf, Some(f), Some(pc),
                    format!("`{}` hashes `block.timestamp`/`block.number`/`prevrandao`/`coinbase`/`blockhash`{}. Validators and front-running contracts can predict or influence every one of these inputs.", f.name, match (reduced, decided) { (Some(_), _) => " and reduces the result to a range", (None, Some(_)) => " and branches on the result", _ => "" }),
                    vec![what], "Use a verifiable randomness source (VRF, commit-reveal) and never decide payouts on block attributes.");
            }
        }

        if f.mutability == crate::function::Mutability::Payable {
            let cv = |e: ExprId| mentions(e, &|n| matches!(n, Node::Env(op::CALLVALUE, _)));
            if let Some(ev) = events
                .iter()
                .find(|e| e.in_loop && event_exprs(e).iter().any(|x| cv(*x)))
            {
                let shown = ev
                    .stmt
                    .as_ref()
                    .map(|s| emit::fmt_stmt(s, &names))
                    .or_else(|| {
                        ev.term.as_ref().and_then(|t| {
                            if let Term::Branch { cond, .. } = t {
                                Some(format!("if ({})", emit::fmt_expr(*cond, &names)))
                            } else {
                                None
                            }
                        })
                    })
                    .unwrap_or_default();
                push(&mut findings, "msg-value-in-loop", "msg.value used inside a loop", Severity::Medium, Confidence::Medium, Some(f), Some(ev.pc),
                    format!("`{}` reads `msg.value` in a loop body. The value is the same in every iteration, so one payment can satisfy a per-item check or be credited once per item.", f.name),
                    vec![shown], "Track the remaining value explicitly (subtract what each iteration consumes) or move the check outside the loop.");
            }
        }

        {
            let mut shown: Option<(ExprId, usize)> = None;
            for ev in &events {
                for e in event_exprs(ev) {
                    let mut seen = HashSet::new();
                    let mut stack = vec![e];
                    while let Some(x) = stack.pop() {
                        if !seen.insert(x) || seen.len() > 5000 {
                            continue;
                        }
                        if let Node::Op(op::MUL, v) = expr::node(x) {
                            for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
                                if let Node::Op(op::DIV, d) = expr::node(a) {
                                    let divisor_pow2 =
                                        expr::as_const(d[1]).is_some_and(|c| c.is_power_of_two());
                                    if !divisor_pow2
                                        && !expr::is_const(d[0])
                                        && d[1] != b
                                        && !(expr::is_const(d[1]) && expr::is_const(b))
                                        && shown.is_none()
                                    {
                                        shown = Some((x, ev.pc));
                                    }
                                }
                            }
                        }
                        stack.extend(expr::children(x));
                    }
                }
            }
            if let Some((x, pc)) = shown {
                push(&mut findings, "division-before-multiplication", "Division before multiplication", Severity::Low, Confidence::Low, Some(f), Some(pc),
                    format!("`{}` computes `{}`: the quotient is truncated before being scaled, so the result can be off by up to the multiplier (percent-of-balance maths that rounds in the caller's or the protocol's favour).", f.name, emit::fmt_expr(x, &names)),
                    vec![], "Multiply first, divide last, and keep the intermediate in uint256.");
            }
        }

        if f.kind == FnKind::External {
            let spot = |e: ExprId| -> bool {
                mentions(e, &|n| matches!(n, Node::Env(op::SELFBALANCE, _)) || matches!(n, Node::Op(op::BALANCE, ref v) if matches!(expr::node(v[0]), Node::Env(op::ADDRESS, _))))
                    || events.iter().any(|ev| matches!(&ev.stmt, Some(Stmt::Call { seq, input: Some(w), in_len, .. }) if w.first().and_then(|w0| emit::leading_selector(*w0, expr::as_const(*in_len).and_then(|l| l.as_usize()))) == Some(SEL_BALANCE_OF) && mentions_returndata(e, *seq)))
            };
            let has_div = |e: ExprId| mentions(e, &|n| matches!(n, Node::Op(op::DIV, _)));
            let mut hit: Option<(String, usize)> = None;
            for ev in &events {
                if let Some(
                    stmt @ Stmt::Call {
                        value,
                        input,
                        in_len,
                        ..
                    },
                ) = &ev.stmt
                {
                    if let Some(v) = value {
                        if spot(*v) && has_div(*v) && !expr::is_const(*v) {
                            hit = Some((emit::fmt_stmt(stmt, &names), ev.pc));
                            break;
                        }
                    }
                    if let (Some(w), Some(sel)) = (input, w0_selector(input, *in_len)) {
                        if matches!(sel, SEL_TRANSFER | SEL_TRANSFER_FROM) {
                            let in_len_c = expr::as_const(*in_len).and_then(|l| l.as_usize());
                            let amount = emit::shifted_word_len(
                                w,
                                if sel == SEL_TRANSFER { 1 } else { 2 },
                                in_len_c,
                            );
                            if spot(amount) && has_div(amount) {
                                hit = Some((emit::fmt_stmt(stmt, &names), ev.pc));
                                break;
                            }
                        }
                    }
                }
            }
            if let Some((line, pc)) = hit {
                push(&mut findings, "spot-balance-price", "Amount paid out derives from a spot balance", Severity::Medium, Confidence::Low, Some(f), Some(pc),
                    format!("`{}` pays out an amount computed from `address(this).balance` or a `balanceOf(this)` reading. Spot balances move with a single transfer or flash loan, so the price or share can be manipulated inside one transaction.", f.name),
                    vec![line], "Use time-weighted or oracle prices, or internal accounting that donations cannot move.");
            }
        }

        if f.kind == FnKind::External && !caller_checked {
            let payouts: Vec<(ExprId, String, usize)> = events
                .iter()
                .filter_map(|ev| match &ev.stmt {
                    Some(
                        st @ Stmt::Call {
                            value: Some(v),
                            addr,
                            ..
                        },
                    ) if from_caller(*addr) && expr::as_const(*v) != Some(U256::ZERO) => {
                        Some((*v, emit::fmt_stmt(st, &names), ev.pc))
                    }
                    Some(
                        st @ Stmt::Call {
                            input: Some(w),
                            in_len,
                            ..
                        },
                    ) if w0_selector(&Some(w.clone()), *in_len) == Some(SEL_TRANSFER) => {
                        let in_len_c = expr::as_const(*in_len).and_then(|l| l.as_usize());
                        let to = emit::shifted_word_len(w, 0, in_len_c);
                        let amount = emit::shifted_word_len(w, 1, in_len_c);
                        from_caller(to).then(|| (amount, emit::fmt_stmt(st, &names), ev.pc))
                    }
                    _ => None,
                })
                .collect();
            let guards = guard_conds(&events);
            for (amount, line, pc) in &payouts {
                if expr::is_const(*amount) || from_calldata(*amount) && !from_storage(*amount) {
                    continue;
                }
                let state = |n: &Node| {
                    matches!(
                        n,
                        Node::SLoad(..) | Node::Env(op::SELFBALANCE, _) | Node::ReturnData(..)
                    )
                };
                let input =
                    |n: &Node| matches!(n, Node::CallDataLoad(_) | Node::Env(op::CALLVALUE, _));
                if !deep_mentions(&ctx, &events, *amount, &state, 3)
                    || !deep_mentions(&ctx, &events, *amount, &input, 3)
                    || !computed_by_division(&ctx, &events, *amount)
                {
                    continue;
                }
                let mut parts: HashSet<ExprId> = HashSet::new();
                let mut seen = HashSet::new();
                let mut stack = vec![*amount];
                while let Some(x) = stack.pop() {
                    if !seen.insert(x) || seen.len() > 5000 {
                        continue;
                    }
                    if matches!(expr::node(x), Node::IntRet(..) | Node::ReturnData(..)) {
                        parts.insert(x);
                    }
                    stack.extend(expr::children(x));
                }
                parts.insert(*amount);
                let bounded = guards
                    .iter()
                    .any(|c| from_calldata(*c) && parts.iter().any(|p| contains_expr(*c, *p)));
                if !bounded {
                    push(&mut findings, "no-slippage-bound", "Computed payout has no caller-supplied minimum", Severity::Low, Confidence::Low, Some(f), Some(*pc),
                        format!("`{}` pays `{}` to msg.sender: an amount computed from balances or storage and the caller's input, with no check against a value the caller passes in. Whoever transacts first can move the price, so the caller may receive far less than expected (front-running, sandwiching).", f.name, emit::fmt_expr(*amount, &names)),
                        vec![line.clone()], "Take a minimum acceptable output (and a deadline) as parameters and require them.");
                }
            }
            if !payouts.is_empty() {
                for ev in &events {
                    let Some(
                        st @ Stmt::Call {
                            value: Some(v),
                            addr,
                            seq,
                            ..
                        },
                    ) = &ev.stmt
                    else {
                        continue;
                    };
                    if expr::as_const(*v) == Some(U256::ZERO)
                        || from_caller(*addr)
                        || from_calldata(*addr)
                        || !(from_storage(*addr) || expr::is_const(*addr))
                    {
                        continue;
                    }
                    let result_required = events.iter().any(|e2| match (&e2.stmt, &e2.term) {
                        (Some(Stmt::Require { cond, .. }), _) => {
                            mentions(*cond, &|n| matches!(n, Node::CallResult(s) if *s == *seq))
                        }
                        (_, Some(Term::Branch { cond, .. })) => {
                            mentions(*cond, &|n| matches!(n, Node::CallResult(s) if *s == *seq))
                        }
                        _ => false,
                    });
                    if result_required {
                        push(&mut findings, "fixed-payee-can-block", "A required payment to a fixed address can block the function", Severity::Low, Confidence::Low, Some(f), Some(ev.pc),
                            format!("`{}` sends ether to `{}`, an address held in storage or in the code, and reverts unless that transfer succeeds, while also paying msg.sender. If that address rejects ether (a contract without a payable fallback, or one that reverts), nobody can use the function.", f.name, emit::fmt_expr(*addr, &names)),
                            vec![emit::fmt_stmt(st, &names)], "Record what the payee is owed and let it withdraw, or do not revert when the fee transfer fails.");
                        break;
                    }
                }
            }
        }

        let solc = c.compiler.kind == compiler::Kind::Solc;
        let pre08 = solc && !c.compiler.checked_arithmetic;
        let post08 = solc && c.compiler.checked_arithmetic;
        if (pre08 || post08) && f.kind == FnKind::External {
            let mut flagged = 0;
            let mut ev_lines = Vec::new();
            let callees = transitive_callees(&ctx, f);
            let mut bodies: Vec<(&Lifted, &Function)> = vec![(l, f)];
            for cf in &callees {
                if let Some(cl) = &cf.lifted {
                    bodies.push((cl, cf));
                }
            }
            let resolve = |pc: usize| -> Option<&Lifted> {
                ctx.internals.get(&pc).and_then(|cf| cf.lifted.as_ref())
            };
            let mut memo = HashMap::new();
            for (body, body_fn) in &bodies {
                let body_names = names_for(body_fn);
                let conds: Vec<ExprId> = crate::function::exprs_with_callees(body, &resolve, 2)
                    .into_iter()
                    .filter(|e| expr::is_boolean(*e))
                    .map(|e| strip_versions(e, &mut memo))
                    .collect();
                for nd in body.nodes.iter() {
                    for s in &nd.stmts {
                        if let Stmt::SStore { val, .. } = s {
                            let mut stack = vec![*val];
                            let mut seen = HashSet::new();
                            while let Some(x) = stack.pop() {
                                if !seen.insert(x) || seen.len() > 2000 {
                                    continue;
                                }
                                if let Node::Op(o, v) = expr::node(x) {
                                    if (o == op::ADD || o == op::SUB || o == op::MUL)
                                        && !expr::is_const(v[0])
                                        && !expr::is_const(v[1])
                                    {
                                        let (xn, v0, v1) = (
                                            strip_versions(x, &mut memo),
                                            strip_versions(v[0], &mut memo),
                                            strip_versions(v[1], &mut memo),
                                        );
                                        let outside = |cnd: ExprId, target: ExprId| {
                                            mentions_outside(cnd, target, xn)
                                        };
                                        let checked = conds.iter().any(|cnd| (mentions(*cnd, &|n| matches!(n, Node::Op(_, w) if w.contains(&xn))) && (outside(*cnd, v0) || outside(*cnd, v1))) || (outside(*cnd, v0) && outside(*cnd, v1) && !mentions(*cnd, &|n| matches!(n, Node::Op(_, w) if w.contains(&xn)))) || (outside(*cnd, v0) && outside(*cnd, v1)));
                                        if !checked {
                                            flagged += 1;
                                            if ev_lines.len() < 3 {
                                                ev_lines.push(emit::fmt_stmt(s, &body_names));
                                            }
                                        }
                                    }
                                }
                                if !matches!(
                                    expr::node(x),
                                    Node::MLoad(..)
                                        | Node::SLoad(..)
                                        | Node::KeccakMem(..)
                                        | Node::CallDataLoad(_)
                                        | Node::CopiedWord(..)
                                        | Node::ReturnData(..)
                                ) {
                                    stack.extend(expr::children(x));
                                }
                            }
                        }
                    }
                }
            }
            if flagged > 0 && pre08 {
                push(&mut findings, "unchecked-arithmetic", "Arithmetic without overflow check (compiler < 0.8)", Severity::Medium, Confidence::Low, Some(f), None,
                    format!("`{}` stores the result of {} arithmetic operation(s) with no visible bound check. Compilers before 0.8.0 wrap silently on overflow/underflow.", f.name, flagged), ev_lines, "Use SafeMath-style checks or compile with >= 0.8.0.");
            } else if flagged > 0 {
                push(&mut findings, "unchecked-block-arithmetic", "Arithmetic in an unchecked block", Severity::Low, Confidence::Medium, Some(f), None,
                    format!("`{}` stores the result of {} arithmetic operation(s) that carry none of the compiler's overflow guards, i.e. they sit in `unchecked {{ }}`. Make sure the bounds really hold.", f.name, flagged), ev_lines, "Keep unchecked blocks to proven-safe counters; otherwise remove them.");
            }
        }

        {
            let loops = loop_nodes(l);
            for nd in &l.nodes {
                if !loops.contains(&nd.id) {
                    continue;
                }
                if let Term::Branch { cond, .. } = &nd.term {
                    if from_storage(*cond)
                        && matches!(
                            expr::node(*cond),
                            Node::Op(op::LT, _)
                                | Node::Op(op::GT, _)
                                | Node::Op(op::ISZERO, _)
                                | Node::Op(op::EQ, _)
                        )
                    {
                        let cap = const_slot_keys(*cond)
                            .iter()
                            .filter_map(|k| caps.get(k).copied())
                            .max();
                        if let Some(cap) = cap {
                            push(&mut findings, "storage-bounded-loop", "Loop bounded by a capped storage counter", Severity::Info, Confidence::Medium, Some(f), Some(nd.pc),
                                format!("`{}` loops while `{}`; the bound is a counter the contract never lets exceed {}, so the loop cannot grow without limit.", f.name, emit::fmt_expr(*cond, &names), cap), vec![], "Informational.");
                            break;
                        }
                        push(&mut findings, "storage-bounded-loop", "Loop bounded by a storage value", Severity::Low, Confidence::Medium, Some(f), Some(nd.pc),
                            format!("`{}` loops while `{}`; if the bound grows (e.g. an unbounded array) the function can exceed the block gas limit and become unusable.", f.name, emit::fmt_expr(*cond, &names)), vec![], "Bound the iteration or paginate.");
                        break;
                    }
                }
            }
        }

        if f.kind == FnKind::External && !caller_checked {
            for nd in &l.nodes {
                for s in &nd.stmts {
                    if let Stmt::SStore { key, val, .. } = s {
                        if auth.contains(key)
                            && expr::is_const(*key)
                            && (from_calldata(*val) || from_caller(*val))
                        {
                            let k = *key;
                            let init_guard = events.iter().any(|e| match (&e.term, &e.stmt) {
                                (Some(Term::Branch { cond, .. }), _) | (_, Some(Stmt::Require { cond, .. })) => mentions(*cond, &|n| matches!(n, Node::SLoad(kk, _, _) if *kk == k)) || mentions(*cond, &|n| matches!(n, Node::SLoad(kk, _, _) if expr::is_const(*kk) && *kk != k)) && matches!(expr::node(*cond), Node::Op(op::ISZERO, _) | Node::Op(op::EQ, _)),
                                _ => false,
                            });
                            if init_guard {
                                push(&mut findings, "unprotected-initializer", "Initializer sets the authority and is callable by anyone", Severity::Medium, Confidence::Medium, Some(f), Some(nd.pc),
                                    format!("`{}` writes the authority slot `{}` behind an 'not yet initialized' check only. If deployment does not call it in the same transaction, the first caller becomes the owner (uninitialised proxy / constructor-as-function pattern).", f.name, emit::fmt_slot(*key, &names, SlotSpace::Persistent)),
                                    vec![emit::fmt_stmt(s, &names)], "Initialise in the constructor or the deployment transaction, and disable re-initialisation.");
                            } else {
                                push(&mut findings, "unprotected-owner-write", "Authority slot writable without access control", Severity::Critical, Confidence::Medium, Some(f), Some(nd.pc),
                                    format!("`{}` writes storage slot `{}`, which other functions compare against msg.sender for authorization, and the function itself has no msg.sender check. Anyone may be able to take over the privileged role.", f.name, emit::fmt_slot(*key, &names, SlotSpace::Persistent)),
                                    vec![emit::fmt_stmt(s, &names)], "Gate the function with the same access control that protects the role.");
                            }
                        }
                    }
                }
            }
        }

        if f.mutability == crate::function::Mutability::Payable {
            let dc_in_loop = events.iter().any(|e| {
                e.in_loop
                    && matches!(
                        &e.stmt,
                        Some(Stmt::Call {
                            kind: op::DELEGATECALL,
                            ..
                        })
                    )
            });
            if dc_in_loop {
                push(&mut findings, "msg-value-multicall", "Payable function delegatecalls in a loop", Severity::Medium, Confidence::Low, Some(f), None,
                    format!("`{}` is payable and delegatecalls repeatedly (multicall pattern). Each delegated call sees the same `msg.value`, so ether can be counted several times if any callee relies on it.", f.name), vec![], "Reject msg.value in multicall, or make the inner functions non-payable.");
            }
        }

        for nd in &l.nodes {
            for e in lift::node_exprs(nd) {
                if mentions(
                    e,
                    &|n| matches!(n, Node::Const(c) if c.to_hex() == EIP1967_IMPL || c.to_hex() == EIP1967_ADMIN || c.to_hex() == EIP1967_BEACON),
                ) {
                    eip1967 = true;
                }
            }
        }
    }

    silent_guard_findings(&ctx, &mut findings);

    policy_findings(&facts, &mut findings);
    chain_findings(&facts, &auth, &mut findings);
    trace_bounds(c, &mut facts, &names_for);
    accounting_findings(&facts, &mut findings);
    let slot_names = c.functions.first().map(names_for).unwrap_or_default();
    let slot_name = |slot: ExprId| emit::fmt_slot(slot, &slot_names, SlotSpace::Persistent);
    conservation_findings(&facts, &slot_name, &mut findings);
    link_findings(&ctx, &facts, &mut findings);
    passed_word_findings(&ctx, &facts, &summaries, &mut findings);
    origin_findings(&ctx, &facts, &stores, &uses, &mut findings);
    trust_findings(&ctx, &facts, &mut findings);

    type_rules::findings(c, &c.types, names_for, &mut findings);

    crate::confirm::confirm(c, &mut findings);
    crate::confirm::confirm_wraps(c, &mut findings);

    crate::invariant::findings(c, &c.types, &mut findings);
    let begin = crate::deploy::storage(c);
    report.maps.extend(crate::deploy::section(c));
    report
        .maps
        .extend(authority(&facts, &stores, &uses, &begin, &mut findings));
    report.maps.extend(crate::props::findings(c, &mut findings));
    crate::flow::findings(c, &mut findings);
    crate::signed::findings(c, &mut findings);
    report
        .maps
        .extend(crate::standard::findings(c, &mut findings));

    if std::env::var("EVMDEC_DEBUG_LOCKS").is_ok() {
        for (slot, fs) in &lock_slots {
            eprintln!(
                "[locks] slot {:?} used by {} function(s): {:?}",
                expr::as_const(*slot).map(|c| c.to_hex()),
                fs.len(),
                fs.iter().map(|pc| format!("{:#x}", pc)).collect::<Vec<_>>()
            );
        }
    }
    if ctx.vyper && lock_slots.len() >= 3 {
        let mut fns: Vec<String> = lock_slots
            .values()
            .flatten()
            .filter_map(|pc| c.functions.iter().find(|f| f.pc == *pc).map(display_name))
            .collect();
        fns.sort();
        push(&mut findings, "vyper-reentrancy-lock-bug", "Each @nonreentrant function uses its own lock slot (Vyper 0.2.15 – 0.3.0 codegen bug)", Severity::High, Confidence::Medium, None, None,
            format!("{} functions implement a reentrancy lock, and every one of them locks a different storage slot, so none of them excludes the others. Vyper 0.2.15, 0.2.16 and 0.3.0 compiled `@nonreentrant(\"key\")` this way (Curve pools, July 2023). Functions: {}.", lock_slots.len(), fns.join(", ")),
            vec![], "Recompile with a fixed compiler; until then treat every locked function as re-enterable from the others.");
    }
    if any_payable
        && !any_ether_out
        && !c.functions.iter().any(|f| {
            f.effects.selfdestruct
                || f.effects.calls
                    && f.lifted.as_ref().is_some_and(|l| {
                        l.nodes.iter().any(|nd| {
                            nd.stmts.iter().any(|s| {
                                matches!(
                                    s,
                                    Stmt::Call {
                                        kind: op::DELEGATECALL,
                                        ..
                                    }
                                )
                            })
                        })
                    })
        })
    {
        push(&mut findings, "locked-ether", "Ether can be received but never sent out", Severity::Low, Confidence::Medium, None, None,
            "At least one function is payable, yet no code path transfers ether out (no call with value, no selfdestruct, no delegatecall). Ether sent to this contract is stuck.".into(), vec![], "Add a withdrawal path or reject ether (remove payable).");
    }
    if let Some(comp) = &c.composite {
        kinds.push(comp.kind.clone());
        let routed: usize = c.parts.iter().skip(1).map(|p| p.selectors.len()).sum();
        let parts: Vec<String> = c
            .parts
            .iter()
            .skip(1)
            .map(|p| match p.selectors.len() {
                0 => format!("`{}` (every unrouted selector)", p.address),
                n => format!("`{}` ({} selectors)", p.address, n),
            })
            .collect();
        let shadow = if comp.shadowed.is_empty() {
            String::new()
        } else {
            format!(
                " The shell answers {} routed selector(s) itself, so those facet functions are unreachable: {}.",
                comp.shadowed.len(),
                comp.shadowed.join(", ")
            )
        };
        push(&mut findings, "composite", "Analysed as one contract with the code it forwards to", Severity::Info, Confidence::High, None, None,
            format!("{}: {} part(s) besides the shell, {} routed selector(s). Their functions run in this contract's storage through `DELEGATECALL` and are reported here under the address they come from: {}.{}", comp.kind, c.parts.len().saturating_sub(1), routed, parts.join(", "), shadow),
            vec![], "Review the parts as one system: access control, storage layout and upgrade rights are shared.");
        for col in &comp.collisions {
            let name = |i: usize| {
                c.parts
                    .get(i)
                    .map(|p| p.address.clone())
                    .unwrap_or_default()
            };
            push(&mut findings, "storage-collision", "Two parts use the same storage slot with different types", Severity::High, Confidence::Medium, None, None,
                format!("Slot {} is `{}` in `{}` and `{}` in `{}`. Parts of a proxy or diamond share one storage; a slot two of them read differently is overwritten by whichever runs, which corrupts state or hands over a role.", col.slot, col.first.1, name(col.first.0), col.second.1, name(col.second.0)),
                vec![], "Give every part the same storage layout, or keep each part's state under its own hashed position (diamond storage).");
        }
    } else if diamond_router {
        kinds.push("EIP-2535 diamond".to_string());
        push(&mut findings, "diamond", "This contract is a diamond shell", Severity::Info, Confidence::High, None, None,
            "The fallback looks the facet up in storage under the call's selector and delegatecalls it (EIP-2535). The logic lives in the facets; decompile by address to assemble them with the shell.".to_string(),
            vec![], "Review who can cut facets (diamondCut) and the facets themselves.");
    } else if fallback_delegatecall {
        let kind = if eip1967 {
            "EIP-1967 upgradeable proxy"
        } else if c.info.runtime.len() < 100 {
            "EIP-1167 minimal proxy (clone)"
        } else if delegatecall_targets_storage {
            "Proxy (implementation address in storage)"
        } else {
            "Proxy"
        };
        kinds.push(kind.to_string());
        push(&mut findings, "proxy", "This contract is a proxy", Severity::Info, Confidence::High, None, None,
            format!("The fallback function delegatecalls to another contract ({}). The real logic lives in the implementation; decompile it as well (use `--follow-proxy` with an address).", kind), vec![], "Review the implementation and who can upgrade it.");
    }
    if sels.contains("upgradeTo(address)") || sels.contains("upgradeToAndCall(address,bytes)") {
        let upg: Vec<&Function> = c
            .functions
            .iter()
            .filter(|f| {
                f.signature.as_deref() == Some("upgradeTo(address)")
                    || f.signature.as_deref() == Some("upgradeToAndCall(address,bytes)")
            })
            .collect();
        for f in upg {
            if !any_caller_check(&ctx, f) {
                push(
                    &mut findings,
                    "unprotected-upgrade",
                    "Upgrade function without access control",
                    Severity::Critical,
                    Confidence::Medium,
                    Some(f),
                    Some(f.pc),
                    format!(
                        "`{}` changes the implementation and no msg.sender check was found.",
                        f.name
                    ),
                    vec![],
                    "Restrict upgrades to the admin/owner.",
                );
            }
        }
    }
    if let Some(v) = ctx.version {
        for bug in COMPILER_BUGS {
            if v >= bug.first && v <= bug.last {
                let sev = match bug.needs {
                    BugNeeds::TransientStorage if !ctx.transient_storage => continue,
                    BugNeeds::CalldataCopy if !ctx.calldata_copies => continue,
                    BugNeeds::TransientStorage | BugNeeds::CalldataCopy => Severity::Low,
                    BugNeeds::Unknowable => Severity::Info,
                };
                push(
                    &mut findings,
                    "compiler-bug",
                    bug.title,
                    sev,
                    Confidence::Low,
                    None,
                    None,
                    format!(
                        "Compiled with solc {}.{}.{}. {}",
                        v.0, v.1, v.2, bug.description
                    ),
                    vec![],
                    "Check whether the affected pattern is used; recompile with a fixed version.",
                );
            }
        }
        if v.1 < 8 {
            push(
                &mut findings,
                "legacy-compiler",
                "Compiled with a pre-0.8 compiler",
                Severity::Info,
                Confidence::High,
                None,
                None,
                format!(
                    "Compiled with solc {}.{}.{}. {}",
                    v.0,
                    v.1,
                    v.2,
                    legacy_consequence(v.1 < 5)
                ),
                vec![],
                "Prefer >= 0.8 for new deployments.",
            );
        }
    } else if c.compiler.kind == compiler::Kind::Solc
        && c.compiler.is_below(compiler::Version::new(0, 8, 0))
    {
        let bound = c.compiler.bounds().unwrap_or_else(|| "< 0.8.0".to_string());
        let before_5 = c.compiler.is_below(compiler::Version::new(0, 5, 0));
        push(
            &mut findings,
            "legacy-compiler",
            "Compiled with a pre-0.8 compiler",
            Severity::Info,
            Confidence::High,
            None,
            None,
            format!(
                "Compiled with solc {}. {}",
                bound,
                legacy_consequence(before_5)
            ),
            vec![],
            "Prefer >= 0.8 for new deployments.",
        );
    }
    if c.info.metadata.is_none() && !ctx.vyper {
        let bounds = match c.compiler.bounds() {
            None => String::new(),
            Some(b) => format!(
                " The fingerprints place the compiler at solc {}: {}.",
                b,
                c.compiler.evidence.join("; ")
            ),
        };
        push(&mut findings, "no-metadata", "No compiler metadata", Severity::Info, Confidence::High, None, None, format!("The bytecode carries no CBOR metadata trailer (stripped, hand-written, or a very old compiler). Source verification is not possible by hash.{}", bounds), vec![], "Informational.");
    }
    if c.stats.unresolved_jumps > 0 {
        push(&mut findings, "coverage", "Some code could not be reached by the analysis", Severity::Info, Confidence::High, None, None, format!("{} jump(s) have unresolved targets and {} of {} code blocks were covered. Findings may be incomplete.", c.stats.unresolved_jumps, c.stats.covered_blocks, c.stats.code_blocks), vec![], "Informational.");
    }
    let unknown: Vec<String> = c
        .functions
        .iter()
        .filter(|f| f.kind == FnKind::External && f.signature.is_none())
        .map(|f| f.selector.clone().unwrap_or_default())
        .collect();
    if !unknown.is_empty() {
        push(&mut findings, "unknown-selectors", "Functions with unknown signatures", Severity::Info, Confidence::High, None, None, format!("{} external function selector(s) are not in the built-in dictionary: {}. Their names are guessed from behaviour only.", unknown.len(), unknown.join(", ")), vec![], "Look them up (4byte / openchain) or provide an ABI.");
    }
    if !c.strings.is_empty() {
        push(
            &mut findings,
            "revert-strings",
            "Revert reasons found in the bytecode",
            Severity::Info,
            Confidence::High,
            None,
            None,
            format!(
                "{} string(s): {}",
                c.strings.len(),
                c.strings
                    .iter()
                    .take(12)
                    .map(|s| format!("\"{}\"", s))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            vec![],
            "Informational.",
        );
    }

    let mut seen = HashSet::new();
    findings.retain(|f| seen.insert((f.id.clone(), f.function.clone(), f.pc, f.title.clone())));
    let positions: HashMap<String, Vec<(String, String)>> = c
        .functions
        .iter()
        .filter(|f| f.kind == FnKind::External)
        .map(|f| {
            let renamed = f
                .params
                .iter()
                .map(|p| (p.name.clone(), format!("arg{}", p.index)))
                .filter(|(name, position)| name != position)
                .collect();
            (display_name(f), renamed)
        })
        .collect();
    let mut findings = merge_findings(findings, &positions);
    let reentrant: HashSet<Option<String>> = findings
        .iter()
        .filter(|f| f.id == "reentrancy")
        .map(|f| f.function.clone())
        .collect();
    findings.retain(|f| f.id != "reentrancy-fixed-callee" || !reentrant.contains(&f.function));
    let locked: Vec<Finding> = findings
        .iter()
        .filter(|f| f.id == "reentrancy" && f.severity == Severity::Info)
        .cloned()
        .collect();
    if locked.len() >= 2 {
        findings.retain(|f| !(f.id == "reentrancy" && f.severity == Severity::Info));
        let names: Vec<String> = locked
            .iter()
            .map(|f| f.function.clone().unwrap_or_default())
            .collect();
        findings.push(Finding {
            id: "reentrancy-locked".into(),
            title: "Calls followed by state writes sit behind a reentrancy lock".into(),
            severity: Severity::Info,
            confidence: Confidence::Medium,
            function: None,
            pc: None,
            description: format!(
                "{} functions call out and write storage afterwards, each behind a lock that is tested before the call, set on entry and restored after it: {}. Reported for awareness: the lock protects these paths only while every function that writes the same state takes it too.",
                locked.len(),
                names.iter().map(|n| format!("`{}`", n)).collect::<Vec<_>>().join(", ")
            ),
            evidence: Vec::new(),
            recommendation: "Make sure every state-changing entry point that touches the same storage takes the same lock.".into(),
            sites: locked.len(),
            confirmed: false,
            witness: None,
            setup: Vec::new(),
            observed: Vec::new(),
        });
    }
    findings.sort_by(|a, b| {
        a.severity
            .cmp(&b.severity)
            .then(a.confidence.cmp(&b.confidence))
            .then(a.function.cmp(&b.function))
    });

    let mut summary = BTreeMap::new();
    for f in &findings {
        *summary
            .entry(format!("{:?}", f.severity).to_lowercase())
            .or_insert(0) += 1;
    }
    report.risk_score = risk_score(&findings);
    report.contract_kind = kinds;
    report.findings = findings;
    report.privileged_functions = privileged;
    report.unauthenticated_state_changers = unauthenticated;
    report.external_calls = external_calls.into_iter().collect();
    let gate_slots: HashSet<String> = summaries
        .iter()
        .flat_map(|g| g.gate_slots.iter().cloned())
        .collect();
    for held in summaries.iter_mut().flat_map(|g| g.stores.iter_mut()) {
        held.gates |= held.base.is_none() && gate_slots.contains(&held.slot);
    }
    report.summary = summary;
    report.summaries = summaries;
    report
}

fn callee_divides(ctx: &Ctx, pc: usize, seen: &mut HashSet<usize>) -> bool {
    if !seen.insert(pc) {
        return false;
    }
    if let Some(known) = ctx.divides.borrow().get(&pc) {
        return *known;
    }
    let mut result = false;
    if let Some(l) = ctx.internals.get(&pc).and_then(|f| f.lifted.as_ref()) {
        'outer: for nd in &l.nodes {
            for e in lift::node_exprs(nd) {
                if mentions(e, &|n| matches!(n, Node::Op(op::DIV | op::SDIV, _))) {
                    result = true;
                    break 'outer;
                }
            }
            for st in &nd.stmts {
                if let Stmt::Internal { callee, .. } = st {
                    if callee_divides(ctx, *callee, seen) {
                        result = true;
                        break 'outer;
                    }
                }
            }
        }
    }
    ctx.divides.borrow_mut().insert(pc, result);
    result
}

fn computed_by_division(ctx: &Ctx, events: &[Event], e: ExprId) -> bool {
    if mentions(e, &|n| matches!(n, Node::Op(op::DIV | op::SDIV, _))) {
        return true;
    }
    let mut seqs: Vec<u32> = Vec::new();
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 5000 {
            continue;
        }
        if let Node::IntRet(s, _) = expr::node(x) {
            seqs.push(s);
        }
        stack.extend(expr::children(x));
    }
    seqs.iter().any(|s| {
        events.iter().any(|ev| {
            matches!(&ev.stmt, Some(Stmt::Internal { seq, callee, .. })
                if seq == s && callee_divides(ctx, *callee, &mut HashSet::new()))
        })
    })
}

fn const_slot_keys(e: ExprId) -> Vec<U256> {
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 5000 {
            continue;
        }
        if let Node::SLoad(k, false, _) = expr::node(x) {
            if let Some(c) = expr::as_const(k) {
                if !out.contains(&c) {
                    out.push(c);
                }
            }
        }
        stack.extend(expr::children(x));
    }
    out
}

fn capped_slots(c: &Contract) -> HashMap<U256, u64> {
    let mut writes: HashMap<U256, Vec<(usize, ExprId)>> = HashMap::new();
    let mut bounds: HashMap<(usize, U256), u64> = HashMap::new();
    for (fi, f) in c.functions.iter().enumerate() {
        let Some(l) = &f.lifted else { continue };
        for nd in &l.nodes {
            for mut cond in node_conds(nd) {
                while let Node::Op(op::ISZERO, v) = expr::node(cond) {
                    cond = v[0];
                }
                let (slot, limit) = match expr::node(cond) {
                    Node::Op(op::LT, v) => (v[0], v[1]),
                    Node::Op(op::GT, v) => (v[1], v[0]),
                    _ => continue,
                };
                if let (Node::SLoad(k, false, _), Some(c)) =
                    (expr::node(slot), expr::as_const(limit))
                {
                    if let (Some(k), true) = (expr::as_const(k), c.bits() <= 16) {
                        let e = bounds.entry((fi, k)).or_insert(0);
                        *e = (*e).max(c.low_u64());
                    }
                }
            }
            for st in &nd.stmts {
                if let Stmt::SStore {
                    key,
                    val,
                    transient: false,
                    ..
                } = st
                {
                    if let Some(k) = expr::as_const(*key) {
                        writes.entry(k).or_default().push((fi, *val));
                    }
                }
            }
        }
    }
    if std::env::var("EVMDEC_DEBUG_CAPS").is_ok() {
        for (k, ws) in &writes {
            eprintln!(
                "[caps] slot {} writes: {:?} bounds: {:?}",
                k.to_decimal(),
                ws.iter()
                    .map(|(fi, v)| format!("fn{}={}", fi, emit::fmt_expr(*v, &Names::default())))
                    .collect::<Vec<_>>(),
                bounds
                    .iter()
                    .filter(|((_, kk), _)| kk == k)
                    .map(|((fi, _), c)| format!("fn{}<{}", fi, c))
                    .collect::<Vec<_>>()
            );
        }
    }
    let mut out = HashMap::new();
    'slots: for (k, ws) in writes {
        let mut cap = 0u64;
        for (fi, val) in ws {
            if expr::is_const(val) {
                continue;
            }
            let loads_k = |e: ExprId| matches!(expr::node(e), Node::SLoad(kk, false, _) if expr::as_const(kk) == Some(k));
            match expr::node(val) {
                Node::Op(op::SUB, v) if loads_k(v[0]) => {}
                Node::Op(op::ADD, v)
                    if (loads_k(v[0]) && expr::as_const(v[1]) == Some(U256::ONE))
                        || (loads_k(v[1]) && expr::as_const(v[0]) == Some(U256::ONE)) =>
                {
                    match bounds.get(&(fi, k)) {
                        Some(c) => cap = cap.max(*c),
                        None => continue 'slots,
                    }
                }
                _ => continue 'slots,
            }
        }
        if cap > 0 {
            out.insert(k, cap);
        }
    }
    out
}

fn require_conds(ctx: &Ctx, l: &Lifted, events: &[Event]) -> Vec<(ExprId, bool)> {
    let mut out = Vec::new();
    for e in events {
        if let Some(Stmt::Require { cond, .. }) = &e.stmt {
            out.push((*cond, true));
        }
        if let Some(Term::Branch {
            cond,
            t: Some(t),
            f,
        }) = &e.term
        {
            let graph = if e.inst == 0 {
                Some(l)
            } else {
                e.callee
                    .and_then(|pc| ctx.internals.get(&pc))
                    .and_then(|f| f.lifted.as_ref())
            };
            let Some(g) = graph else { continue };
            if lift::always_reverts(g, *t) {
                out.push((*cond, false));
            } else if lift::always_reverts(g, *f) {
                out.push((*cond, true));
            }
        }
    }
    out
}

fn only_nonzero_bound(ctx: &Ctx, l: &Lifted, events: &[Event], amt: ExprId) -> Option<bool> {
    let mut zero_test = false;
    for (c0, holds) in require_conds(ctx, l, events) {
        if !contains_expr(c0, amt) {
            continue;
        }
        let mut c = c0;
        let mut pol = holds;
        while let Node::Op(op::ISZERO, v) = expr::node(c) {
            c = v[0];
            pol = !pol;
        }
        let zero = |x: ExprId| expr::as_const(x) == Some(U256::ZERO);
        let zero_cmp = c == amt
            || matches!(expr::node(c), Node::Op(op::EQ, v) if (v[0] == amt && zero(v[1])) || (v[1] == amt && zero(v[0])))
            || matches!(expr::node(c), Node::Op(op::GT, v) if v[0] == amt && zero(v[1]))
            || matches!(expr::node(c), Node::Op(op::LT, v) if v[1] == amt && zero(v[0]));
        if zero_cmp {
            zero_test = true;
            continue;
        }
        if from_calldata(c) {
            continue;
        }
        let lower = match expr::node(c) {
            Node::Op(op::GT, v) if v[0] == amt => pol,
            Node::Op(op::LT, v) if v[1] == amt => pol,
            Node::Op(op::LT, v) if v[0] == amt => !pol,
            Node::Op(op::GT, v) if v[1] == amt => !pol,
            Node::Op(op::EQ, v) if v[0] == amt || v[1] == amt => pol,
            _ => false,
        };
        if lower {
            return Some(false);
        }
    }
    if zero_test {
        Some(true)
    } else {
        None
    }
}

fn reverse_quote(
    ctx: &Ctx,
    l: &Lifted,
    events: &[Event],
    words: &[ExprId],
    sel: u32,
    in_len: Option<usize>,
) -> Option<(ExprId, String, &'static str)> {
    let direct = |e: ExprId| write_source(e) == WriteSource::Calldata;
    let names = Names::default();
    match sel {
        SEL_TRANSFER_FROM => {
            let to = emit::shifted_word_len(words, 1, in_len);
            let amt = emit::shifted_word_len(words, 2, in_len);
            if std::env::var("EVMDEC_DEBUG_RQ").is_ok() {
                eprintln!(
                    "[rq] transferFrom to={} amt={} to_this={} div={} bound={:?} words={}",
                    emit::fmt_expr(to, &names),
                    emit::fmt_expr(amt, &names),
                    mentions(to, &|n| matches!(n, Node::Env(op::ADDRESS, _))),
                    computed_by_division(ctx, events, amt),
                    only_nonzero_bound(ctx, l, events, amt),
                    words.len()
                );
            }
            if !mentions(to, &|n| matches!(n, Node::Env(op::ADDRESS, _))) {
                return None;
            }
            if !computed_by_division(ctx, events, amt)
                || only_nonzero_bound(ctx, l, events, amt) != Some(true)
            {
                return None;
            }
            let credit = events.iter().find_map(|ev| match &ev.stmt {
                Some(st @ Stmt::SStore { val, .. }) => match expr::node(*val) {
                    Node::Op(op::ADD, v) if v.iter().any(|x| direct(*x)) => {
                        Some(emit::fmt_stmt(st, &names))
                    }
                    _ => None,
                },
                _ => None,
            })?;
            Some((
                amt,
                format!("`{}`", credit),
                " or below a caller-supplied limit",
            ))
        }
        SEL_TRANSFER => {
            let amt_out = emit::shifted_word_len(words, 1, in_len);
            if !direct(amt_out) {
                return None;
            }
            let computed_input = |x: ExprId| {
                computed_by_division(ctx, events, x)
                    && only_nonzero_bound(ctx, l, events, x) == Some(true)
            };
            let debit = events.iter().find_map(|ev| {
                let Some(st @ Stmt::SStore { val, .. }) = &ev.stmt else {
                    return None;
                };
                match expr::node(*val) {
                    Node::Op(op::SUB, v) if computed_input(v[1]) => {
                        Some((v[1], emit::fmt_stmt(st, &names)))
                    }
                    Node::IntRet(seq, _) => events.iter().find_map(|e2| match &e2.stmt {
                        Some(Stmt::Internal { seq: s, args, .. }) if *s == seq => args
                            .iter()
                            .copied()
                            .find(|a| computed_input(*a))
                            .map(|a| (a, emit::fmt_stmt(st, &names))),
                        _ => None,
                    }),
                    _ => None,
                }
            })?;
            Some((
                debit.0,
                format!(
                    "the transfer of `{}`, then `{}`",
                    emit::fmt_expr(amt_out, &names),
                    debit.1
                ),
                " or below a caller-supplied limit",
            ))
        }
        _ => None,
    }
}

fn effect_free_exit(l: &Lifted, start: usize) -> bool {
    let mut seen = HashSet::new();
    let mut stack = vec![start];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 2000 {
            continue;
        }
        let nd = &l.nodes[x];
        for st in &nd.stmts {
            if matches!(
                st,
                Stmt::SStore { .. }
                    | Stmt::Log { .. }
                    | Stmt::Call { .. }
                    | Stmt::Create { .. }
                    | Stmt::Internal { .. }
            ) {
                return false;
            }
        }
        match &nd.term {
            Term::Revert { .. } | Term::Invalid | Term::SelfDestruct(_) | Term::Unresolved(_) => {
                return false
            }
            Term::Return { .. } | Term::ReturnDyn { .. } | Term::Stop | Term::InternalReturn(_) => {
            }
            _ => stack.extend(nd.succs.iter().copied()),
        }
    }
    true
}

fn silent_guard_findings(ctx: &Ctx, findings: &mut Vec<Finding>) {
    for f in &ctx.c.functions {
        if f.kind == FnKind::Orphan || f.inlined {
            continue;
        }
        let Some(l) = &f.lifted else { continue };
        let names = decompile::make_names(
            f,
            &ctx.c.storage,
            ctx.c.compiler.layout,
            &ctx.c.string_loaders,
            &decompile::Callees::of(&ctx.c.functions, ctx.c.compiler.kind),
        );
        for nd in &l.nodes {
            let Term::Branch {
                cond,
                t: Some(t),
                f: fnode,
            } = &nd.term
            else {
                continue;
            };
            if !is_auth_cond_in(*cond, &ctx.roles) {
                continue;
            }
            let (t, fnode) = (*t, *fnode);
            let silent = match (effect_free_exit(l, t), effect_free_exit(l, fnode)) {
                (true, false) => Some(t),
                (false, true) => Some(fnode),
                _ => None,
            };
            let Some(_) = silent else { continue };
            let callers: Vec<String> = if f.kind == FnKind::Internal {
                ctx.c
                    .functions
                    .iter()
                    .filter(|g| g.kind != FnKind::Internal && g.kind != FnKind::Orphan)
                    .filter(|g| transitive_callees(ctx, g).iter().any(|cf| cf.pc == f.pc))
                    .map(|g| g.name.clone())
                    .collect()
            } else {
                Vec::new()
            };
            let reach = if callers.is_empty() {
                String::new()
            } else {
                format!(
                    " The helper guards {}.",
                    join_names(&callers.iter().map(|c| c.as_str()).collect::<Vec<_>>(), 6)
                )
            };
            push(findings, "silent-auth-failure", "Authorisation failure returns instead of reverting", Severity::Low, Confidence::Medium, Some(f), Some(nd.pc),
                format!("`{}` tests `{}`; when the test fails it returns normally without changing state instead of reverting.{} A caller cannot tell a rejected call from a successful one by the transaction's status, and ether sent along stays in the contract.", f.name, emit::fmt_cond(*cond, &names), reach),
                vec![format!("if ({}) …", emit::fmt_cond(*cond, &names))], "Revert (require) when the caller is not authorised.");
            break;
        }
    }
}

#[allow(
    clippy::too_many_arguments,
    reason = "a finding is built from its fields in one call at every rule site"
)]
fn push_fact(
    findings: &mut Vec<Finding>,
    id: &str,
    title: &str,
    sev: Severity,
    conf: Confidence,
    x: &FnFacts,
    desc: String,
    evidence: Vec<String>,
    rec: &str,
) {
    findings.push(Finding {
        id: id.into(),
        title: title.into(),
        severity: sev,
        confidence: conf,
        function: Some(x.name.clone()),
        pc: Some(x.pc),
        description: desc,
        evidence,
        recommendation: rec.into(),
        sites: 1,
        confirmed: false,
        witness: None,
        setup: Vec::new(),
        observed: Vec::new(),
    });
}

fn join_names(names: &[&str], max: usize) -> String {
    let shown: Vec<String> = names.iter().take(max).map(|n| format!("`{}`", n)).collect();
    if names.len() > max {
        format!("{} and {} more", shown.join(", "), names.len() - max)
    } else {
        shown.join(", ")
    }
}

fn trust_findings(ctx: &Ctx, facts: &[FnFacts], findings: &mut Vec<Finding>) {
    let c = ctx.c;
    let slot_const = |e: ExprId| expr::as_const(e);
    let ledgers: HashSet<U256> = crate::invariant::balance_mappings(&c.types)
        .into_iter()
        .map(|l| l.root)
        .filter(|r| crate::invariant::is_ledger(c, *r))
        .collect();
    let mut pool_slots: HashSet<U256> = HashSet::new();
    for x in facts {
        for sc in &x.stored_callees {
            if sc.selector.is_some_and(|sel| POOL_SELECTORS.contains(&sel)) {
                if let Some(k) = slot_const(sc.slot) {
                    pool_slots.insert(k);
                }
            }
        }
        for k in x.factory_slots.iter().chain(&x.compared_slots) {
            if let Some(kc) = slot_const(*k) {
                pool_slots.insert(kc);
            }
        }
        for (root, k) in &x.ledger_reads {
            if ledgers.contains(root) {
                if let Some(kc) = slot_const(*k) {
                    pool_slots.insert(kc);
                }
            }
        }
    }
    let mut named_slots: HashSet<U256> = HashSet::new();
    for f in &c.functions {
        let getter_name = f
            .signature
            .as_deref()
            .and_then(|s| s.strip_suffix("()"))
            .map(|n| n.to_ascii_lowercase());
        let named_pair = getter_name
            .is_some_and(|n| n.ends_with("pair") || n.ends_with("pool") || n.ends_with("lptoken"));
        if !named_pair || f.kind != FnKind::External || f.returns.len() != 1 {
            continue;
        }
        if let Some(l) = &f.lifted {
            for nd in &l.nodes {
                for e in lift::node_exprs(nd) {
                    let mut keys = HashSet::new();
                    collect_sload_keys(e, &mut keys);
                    for k in keys {
                        if let Some(kc) = expr::as_const(k) {
                            named_slots.insert(kc);
                        }
                    }
                }
            }
        }
    }

    let mut open_gates: HashMap<usize, Vec<String>> = HashMap::new();
    let mut linked_cache: HashMap<String, LinkedSummary> = HashMap::new();
    for x in facts
        .iter()
        .filter(|x| x.external && x.state_changing && x.caller_checked)
    {
        for (slot, slot_name) in &x.auth_slots {
            let Some(sk) = slot_const(*slot) else {
                continue;
            };
            let callers: Vec<(&FnFacts, &StoredCall)> = facts
                .iter()
                .filter(|y| y.external && !y.caller_checked && y.pc != x.pc)
                .flat_map(|y| {
                    y.stored_callees
                        .iter()
                        .filter(|sc| !sc.is_static && slot_const(sc.slot) == Some(sk))
                        .map(move |sc| (y, sc))
                })
                .collect();
            if callers.is_empty() {
                continue;
            }
            let (y, sc) = callers[0];
            let via: Vec<String> = callers.iter().map(|(y, _)| y.name.clone()).collect();
            let forwarded = linked_forwards(ctx, sk, x, sc.selector, &mut linked_cache);
            let (sev, tail) = match &forwarded {
                Some(note) => (Severity::Critical, note.clone()),
                None => (
                    Severity::Medium,
                    "If that contract forwards calls it receives (a sell hook, a router, a controller), the gate is open to every caller; decompile by address to have it fetched and checked.".to_string(),
                ),
            };
            push_fact(findings, "trusted-callee-loop", "A role check trusts a contract this contract calls on a public path", sev, Confidence::Medium, x,
                format!(
                    "`{}` is gated on the address in `{}`, but `{}` calls that same address on a path anyone can take{}. The check authenticates a contract this contract itself drives rather than a person. {}",
                    x.name, slot_name, y.name,
                    if sc.passes_sender { ", passing the sender along" } else { "" },
                    tail
                ),
                vec![sc.line.clone()],
                "Gate the function on the account that may use it, not on a contract that acts for arbitrary callers, and never let a hook re-enter privileged paths.");
            open_gates.entry(x.pc).or_default().extend(via);
        }
    }

    for x in facts {
        if x.account_authorised || x.signature_authorised {
            continue;
        }
        for d in &x.debits {
            if !ledgers.contains(&d.root) {
                continue;
            }
            let target_slot = ssa::stored_address_slot(d.key).and_then(slot_const);
            let gate_target = target_slot
                .is_some_and(|k| x.auth_slots.iter().any(|(s, _)| slot_const(*s) == Some(k)));
            if gate_target || (target_slot.is_none() && !from_calldata(unmask(d.key))) {
                continue;
            }
            if std::env::var("EVMDEC_DEBUG_TRUST").is_ok() {
                eprintln!(
                    "[trust] {} debit {} key={:?} allowances={:?}",
                    x.name,
                    d.account_text,
                    unmask(d.key),
                    x.allowance_of
                );
            }
            if from_caller(d.key)
                || x.allowance_of.contains(&unmask(d.key))
                || mentions(d.key, &|n| matches!(n, Node::Env(op::ADDRESS, _)))
            {
                continue;
            }
            let by_use = target_slot.is_some_and(|k| pool_slots.contains(&k));
            let by_name = target_slot.is_some_and(|k| named_slots.contains(&k));
            let is_pool = by_use || by_name;
            let name_only = by_name && !by_use;
            let (what, sev) = if is_pool {
                ("the stored liquidity pair", Severity::Critical)
            } else if target_slot.is_some() {
                ("an address held in storage", Severity::High)
            } else {
                (
                    "an account chosen by the caller",
                    if x.caller_checked {
                        Severity::Medium
                    } else {
                        Severity::High
                    },
                )
            };
            let open = open_gates.get(&x.pc);
            let gate = match (x.caller_checked, open) {
                (true, Some(via)) => format!(" The function is gated, but the gate is open through {} (see the trusted-callee finding).", via.iter().map(|v| format!("`{}`", v)).collect::<Vec<_>>().join(", ")),
                (true, None) => " The function is gated, so this is what the role holder can do to other accounts.".to_string(),
                (false, _) => " Anyone can call it.".to_string(),
            };
            let pool_note = if is_pool {
                " Removing tokens from the pair without moving its reserves leaves the pair pricing against a balance that is gone; a `sync()` then collapses the recorded reserve and the next swap takes the other asset."
            } else {
                ""
            };
            let conf = if name_only {
                Confidence::Low
            } else {
                Confidence::Medium
            };
            push_fact(findings, "third-party-balance-debit", "A balance is taken from an account the caller does not own", sev, conf, x,
                format!(
                    "`{}` lowers `{}` on {}: the entry `{}` in the mapping at slot {} is reduced by a chosen amount, with no transfer from the caller and no allowance check.{}{}",
                    x.name, d.account_text, what, d.account_text, d.root.to_hex(), gate, pool_note
                ),
                vec![d.line.clone()],
                "Only debit `msg.sender` or an account whose allowance for the caller is checked; never debit the pair.");
        }
    }

    for x in facts {
        for sync in &x.syncs {
            if !sync.after_mutation {
                continue;
            }
            let sev = if x.caller_checked {
                Severity::Medium
            } else {
                Severity::High
            };
            push_fact(findings, "pair-sync-after-state-change", "A pair is synchronised after balances or other contracts were changed", sev, Confidence::Medium, x,
                format!(
                    "`{}` calls `sync()`/`skim()` on `{}` after writing storage or calling another contract in the same path. `sync()` makes the pair adopt its current token balances as reserves, so any balance moved beforehand is priced in at once.{}",
                    x.name, sync.target,
                    if x.caller_checked { "" } else { " Anyone can trigger this." }
                ),
                vec![sync.line.clone()],
                "Do not let callers reach a pair's `sync()` after state that affects the pair's balances has been changed in the same transaction.");
        }
    }
}

struct LinkedSummary {
    forwarders: Vec<String>,
    selectors_called: Vec<String>,
}

fn linked_forwards(
    ctx: &Ctx,
    slot: U256,
    gated: &FnFacts,
    called: Option<u32>,
    cache: &mut HashMap<String, LinkedSummary>,
) -> Option<String> {
    let slot_hex = slot.to_hex_padded(32);
    let address = ctx
        .c
        .stored_targets
        .iter()
        .find(|(s, _)| s.eq_ignore_ascii_case(&slot_hex))
        .map(|(_, a)| a.to_ascii_lowercase())?;
    if !cache.contains_key(&address) {
        let lc = linked_contract(ctx, &address)?;
        let report = ctx.world.report(&address)?;
        let forwarders = report
            .unauthenticated_state_changers
            .iter()
            .filter(|name| {
                report.external_calls.iter().any(|line| {
                    line.strip_prefix(name.as_str())
                        .is_some_and(|rest| rest.starts_with(": ") && !rest.contains("staticcall"))
                })
            })
            .cloned()
            .collect();
        cache.insert(
            address.clone(),
            LinkedSummary {
                forwarders,
                selectors_called: lc.selectors_called.clone(),
            },
        );
    }
    let summary = &cache[&address];
    let calls_back = gated.selector.as_deref().is_some_and(|sel| {
        summary.selectors_called.iter().any(|entry| {
            entry
                .split_whitespace()
                .next()
                .is_some_and(|tok| tok.eq_ignore_ascii_case(sel))
        })
    });
    let mut forwarders: Vec<&String> = summary.forwarders.iter().collect();
    if let Some(sel) = called {
        let tag = format!("{:#010x}", sel);
        forwarders.sort_by_key(|name| !name.contains(&tag));
    }
    if forwarders.is_empty() && !calls_back {
        return None;
    }
    Some(format!(
        "The contract at `{}` was fetched: {}{} so the loop is open to every caller.",
        address,
        match forwarders.first() {
            Some(f) => format!("`{}` there can be called by anyone and calls out again", f),
            None => "it calls out from its functions".to_string(),
        },
        if calls_back {
            " (it calls this function's selector),"
        } else {
            ","
        }
    ))
}

fn policy_findings(facts: &[FnFacts], findings: &mut Vec<Finding>) {
    let gated: Vec<&FnFacts> = facts
        .iter()
        .filter(|x| x.external && x.state_changing && x.caller_checked)
        .collect();
    if gated.len() < 2 {
        return;
    }
    let mut uses: HashMap<ExprId, (usize, String)> = HashMap::new();
    for g in &gated {
        for (slot, name) in &g.auth_slots {
            let e = uses.entry(*slot).or_insert((0, name.clone()));
            e.0 += 1;
        }
    }
    let policy: Vec<(ExprId, String)> = uses
        .into_iter()
        .filter(|(_, (n, _))| *n >= 2)
        .map(|(slot, (_, name))| (slot, name))
        .collect();
    if policy.is_empty() {
        return;
    }
    let policy_names: Vec<&str> = policy.iter().map(|(_, n)| n.as_str()).collect();
    let followers: Vec<&FnFacts> = gated
        .iter()
        .copied()
        .filter(|g| {
            g.auth_slots
                .iter()
                .any(|(s, _)| policy.iter().any(|(p, _)| p == s))
        })
        .collect();
    if followers.len() < 2 {
        return;
    }
    let follower_names: Vec<&str> = followers.iter().map(|g| g.name.as_str()).collect();
    let mut gated_slots: HashSet<ExprId> = HashSet::new();
    for g in followers.iter().filter(|g| !g.init_guarded) {
        gated_slots.extend(g.const_writes.iter().map(|(s, _, _)| *s));
    }
    let gated_pays_storage = followers
        .iter()
        .any(|g| g.ether_out.iter().any(|(a, _, _)| from_storage(*a)));
    let gated_delegates = followers
        .iter()
        .any(|g| g.delegatecalls.iter().any(|(t, _)| from_storage(*t)));
    for x in facts
        .iter()
        .filter(|x| x.external && x.state_changing && !x.caller_checked)
    {
        for (s, _, _) in &x.const_writes {
            if facts
                .iter()
                .filter(|y| !y.caller_checked && !std::ptr::eq(*y, x))
                .any(|y| y.const_writes.iter().any(|(t, _, _)| t == s))
            {
                gated_slots.remove(s);
            }
        }
        let mut does: Vec<String> = Vec::new();
        let mut evidence: Vec<String> = Vec::new();
        let mut sev = Severity::Low;
        let mut conf = Confidence::Medium;
        let raise = |sev: &mut Severity, to: Severity| {
            if to < *sev {
                *sev = to;
            }
        };
        for (addr, _, line) in &x.ether_out {
            if from_caller(*addr)
                || from_calldata(*addr)
                || !from_storage(*addr)
                || !gated_pays_storage
            {
                continue;
            }
            does.push("sends ether to an address held in storage".into());
            raise(&mut sev, Severity::Medium);
            conf = Confidence::Low;
            evidence.push(line.clone());
        }
        for (a, line) in &x.selfdestructs {
            let to_user = from_caller(*a) || from_calldata(*a);
            does.push(if to_user {
                "self-destructs to an address the caller chooses".into()
            } else {
                "self-destructs".into()
            });
            raise(
                &mut sev,
                if to_user {
                    Severity::High
                } else {
                    Severity::Medium
                },
            );
            evidence.push(line.clone());
        }
        for (t, line) in &x.delegatecalls {
            if !from_storage(*t) || from_calldata(*t) || from_caller(*t) || !gated_delegates {
                continue;
            }
            does.push("delegatecalls an address held in storage".into());
            raise(&mut sev, Severity::Medium);
            evidence.push(line.clone());
        }
        for (slot, _, line) in &x.const_writes {
            if policy.iter().any(|(p, _)| p == slot) {
                continue;
            }
            if gated_slots.contains(slot) {
                does.push(
                    "writes a storage slot that is otherwise written only behind the check".into(),
                );
                raise(&mut sev, Severity::Medium);
                evidence.push(line.clone());
            }
        }
        if does.is_empty() {
            continue;
        }
        does.sort();
        does.dedup();
        evidence.truncate(4);
        let time_note = if x.time_gated {
            " Its only guard is a block or time condition, which gates when, not who."
        } else {
            ""
        };
        push_fact(findings, "inconsistent-access-control", "Missing access control, judged by the contract's own policy", sev, conf, x,
            format!("{} state-changing functions ({}) require msg.sender to match {}. `{}` has no such check yet {}.{} Either the omission is intentional and should be documented, or a modifier is missing.",
                followers.len(), join_names(&follower_names, 4), join_names(&policy_names, 2), x.name, does.join(", "), time_note),
            evidence, "Apply the same access control as the sibling functions, or make the public intent explicit.");
    }
}

fn chain_findings(facts: &[FnFacts], auth: &HashSet<ExprId>, findings: &mut Vec<Finding>) {
    let mut reported: HashSet<(String, String)> = HashSet::new();
    for x in facts.iter().filter(|x| x.external && !x.caller_checked) {
        let (chain_sev, init_note) = if x.init_guarded {
            (Severity::Medium, " Step 1 sits behind a not-yet-initialised check, so the chain is open only while the contract (or a bare implementation) is uninitialised.")
        } else {
            (Severity::Critical, "")
        };
        for (slot, source, wline) in &x.const_writes {
            if *source == WriteSource::Other {
                continue;
            }
            if auth.contains(slot) {
                for g in facts
                    .iter()
                    .filter(|g| g.caller_checked && g.auth_slots.iter().any(|(s, _)| s == slot))
                {
                    let mut steps: Vec<String> = Vec::new();
                    for (_, _, line) in &g.ether_out {
                        steps.push(format!("send ether: `{}`", line));
                    }
                    for (_, line) in &g.selfdestructs {
                        steps.push(format!("destroy the contract: `{}`", line));
                    }
                    for (_, line) in &g.delegatecalls {
                        steps.push(format!("run foreign code: `{}`", line));
                    }
                    if steps.is_empty() || !reported.insert((x.name.clone(), g.name.clone())) {
                        continue;
                    }
                    let slot_name = g
                        .auth_slots
                        .iter()
                        .find(|(s, _)| s == slot)
                        .map(|(_, n)| n.clone())
                        .unwrap_or_default();
                    push_fact(findings, "attack-chain", "Attack chain: take over the privileged role, then drain", chain_sev, Confidence::Medium, x,
                        format!("Step 1: `{}` lets anyone write `{}`, the slot that `{}` compares msg.sender against. Step 2: as the new `{}`, call `{}` to {}.{}",
                            x.name, slot_name, g.name, slot_name, g.name, steps.join("; "), init_note),
                        vec![wline.clone(), steps[0].split('`').nth(1).unwrap_or_default().to_string()],
                        "Protect the role write (step 1); the chain then collapses to an ordinary privileged function.");
                }
            }
            if *source != WriteSource::Calldata {
                continue;
            }
            for g in facts
                .iter()
                .filter(|g| !g.caller_checked && !std::ptr::eq(*g, x))
            {
                let mut hits: Vec<(String, String)> = Vec::new();
                for (addr, val, line) in &g.ether_out {
                    if reads_slot(*addr, *slot) {
                        hits.push((
                            "sends ether to the address stored there".into(),
                            line.clone(),
                        ));
                    } else if reads_slot(*val, *slot) {
                        hits.push((
                            "uses it as the amount of an ether transfer".into(),
                            line.clone(),
                        ));
                    }
                }
                for (a, line) in &g.selfdestructs {
                    if reads_slot(*a, *slot) {
                        hits.push((
                            "self-destructs to the address stored there".into(),
                            line.clone(),
                        ));
                    }
                }
                for (t, line) in &g.delegatecalls {
                    if reads_slot(*t, *slot) {
                        hits.push((
                            "delegatecalls the address stored there".into(),
                            line.clone(),
                        ));
                    }
                }
                let Some((what, gline)) = hits.first().cloned() else {
                    continue;
                };
                if !reported.insert((x.name.clone(), g.name.clone())) {
                    continue;
                }
                let slot_name = wline
                    .split(" = ")
                    .next()
                    .unwrap_or_default()
                    .trim()
                    .to_string();
                push_fact(findings, "attack-chain", "Attack chain: set a trusted slot, then trigger the function that trusts it", chain_sev, Confidence::Medium, x,
                    format!("Step 1: `{}` lets anyone write `{}` from its arguments. Step 2: `{}`, also callable by anyone, {}.{}", x.name, slot_name, g.name, what, init_note),
                    vec![wline.clone(), gline], "Protect the write in step 1 or validate the slot's value where it is used.");
            }
        }
    }
}

const TRACE_LIMITS: crate::path::Limits = crate::path::Limits {
    paths: 32,
    runs: 128,
    until: None,
};
const TRACE_WORDS: usize = 32;
const TRACE_ANSWER_BYTES: usize = 320;
const TRACE_BUDGET: std::time::Duration = std::time::Duration::from_secs(3);

// A record copied to memory and updated there hides its fields from the rule above.
// Along one run the lifter knows what every memory word holds, so the same limits are
// read again from the checks of each run and added to what the function is known to cap.
fn trace_bounds(c: &Contract, facts: &mut [FnFacts], names_for: &dyn Fn(&Function) -> Names) {
    if std::env::var("EVMDEC_NO_CONFIRM").is_ok() || c.info.runtime.is_empty() {
        return;
    }
    let layout = c.compiler.layout;
    let begin = crate::deploy::storage(c);
    let limits = crate::path::Limits {
        until: Some(std::time::Instant::now() + TRACE_BUDGET),
        ..TRACE_LIMITS
    };
    let mut explorers: HashMap<*const u8, crate::path::Explorer> = HashMap::new();
    for f in c.functions.iter().filter(|f| f.kind == FnKind::External) {
        let Some(fact) = facts.iter_mut().find(|x| x.external && x.pc == f.pc) else {
            continue;
        };
        let names = names_for(f);
        let code = c.code_of(f);
        let explorer = explorers
            .entry(code.as_ptr())
            .or_insert_with(|| crate::path::Explorer::new(code));
        // Zero words pass every type check on a decoded argument at once.
        // Other values would spend the path limit on one check per field.
        let mut start = crate::path::inputs_for(crate::exec::selector_of(f), TRACE_WORDS);
        start.storage = begin.clone();
        // A true word first, then room for a callee that answers with a record.
        start.returned = U256::ONE.to_be_bytes().to_vec();
        start.returned.resize(TRACE_ANSWER_BYTES, 0);
        let free = crate::solve::Free {
            words: TRACE_WORDS,
            value: true,
            storage: true,
            fixed: Vec::new(),
        };
        let explored = explorer.explore(&start, &free, limits);
        for p in explored {
            let mut outflows: Vec<ExprId> = Vec::new();
            for st in &p.effects {
                match st {
                    Stmt::Call {
                        value,
                        input,
                        input_head,
                        in_len,
                        ..
                    } => {
                        outflows.extend(value.filter(|v| !expr::is_const(*v)));
                        let words: &[ExprId] = input.as_deref().unwrap_or(input_head);
                        let len = expr::as_const(*in_len).and_then(|l| l.as_usize());
                        let selector = words
                            .first()
                            .and_then(|w0| emit::leading_selector(*w0, len));
                        if selector == Some(SEL_TRANSFER) && words.len() >= 2 {
                            outflows.push(emit::shifted_word_len(words, 1, len));
                        }
                    }
                    Stmt::SStore { key, val, .. } => outflows.extend(subtracts_from(*val, *key)),
                    _ => {}
                }
            }
            let mut candidates: Vec<(AvailBound, ExprId)> = Vec::new();
            let mut seen = HashSet::new();
            for item in &p.items {
                let e = match item {
                    crate::solve::Item::Check { cond, .. } => *cond,
                    crate::solve::Item::Store { val, .. } => *val,
                };
                limits_in(e, layout, &names, &mut seen, &mut candidates);
            }
            for (bound, other) in candidates {
                let same = |b: &AvailBound| b.added == bound.added && b.subbed == bound.subbed;
                if limits_outflow(other, &outflows) && !fact.avail_bounds.iter().any(same) {
                    fact.avail_bounds.push(bound.clone());
                    fact.moves_value = true;
                }
                if !fact.ref_bounds.iter().any(same) {
                    fact.ref_bounds.push(bound);
                }
            }
        }
    }
}

fn accounting_findings(facts: &[FnFacts], findings: &mut Vec<Finding>) {
    let mut flagged: HashSet<usize> = HashSet::new();
    for (i, f) in facts.iter().enumerate() {
        if !f.moves_value || flagged.contains(&i) {
            continue;
        }
        for fb in &f.avail_bounds {
            if fb.subbed.is_empty() {
                continue;
            }
            let stronger = facts.iter().enumerate().find_map(|(j, g)| {
                if i == j {
                    return None;
                }
                g.ref_bounds.iter().find_map(|gb| {
                    (fb.subbed.is_subset(&gb.subbed)
                        && fb.subbed != gb.subbed
                        && !fb.added.is_disjoint(&gb.added))
                    .then_some((g, gb))
                })
            });
            let Some((g, gb)) = stronger else { continue };
            let missing: Vec<String> = gb
                .subbed
                .difference(&fb.subbed)
                .map(|sh| gb.names.get(sh).cloned().unwrap_or_default())
                .filter(|n| !n.is_empty())
                .collect();
            push_fact(
                findings,
                "inconsistent-liability-accounting",
                "A payout limit omits a liability another path subtracts",
                Severity::High,
                Confidence::Medium,
                f,
                format!(
                    "`{}` limits how much may leave by subtracting {} outstanding-liability field(s) from the pooled deposits, while `{}` subtracts {} over the same deposits. The field(s) {} are not subtracted here, so once they hold a value this path counts as available what `{}` already counts as owed, and releases more than the shared balance backs.",
                    f.name,
                    fb.subbed.len(),
                    g.name,
                    gb.subbed.len(),
                    if missing.is_empty() { "it omits".to_string() } else { missing.join(", ") },
                    g.name,
                ),
                vec![fb.line.clone(), format!("vs {}: {}", g.name, gb.line)],
                "Subtract the same set of outstanding-liability fields in every function that releases value from the shared balance.",
            );
            flagged.insert(i);
            break;
        }
    }
}

fn link_findings(ctx: &Ctx, facts: &[FnFacts], findings: &mut Vec<Finding>) {
    let mut told: HashSet<(usize, String, &str)> = HashSet::new();
    for f in facts.iter().filter(|f| f.external) {
        for call in &f.linked_calls {
            let Some(lc) = linked_contract(ctx, &call.address) else {
                continue;
            };
            let externals = || lc.functions.iter().filter(|g| g.kind == FnKind::External);
            if externals().next().is_none() {
                continue;
            }
            let Some(report) = ctx.world.report(&call.address) else {
                continue;
            };
            let catch_all = |payable: bool| {
                lc.functions.iter().any(|g| {
                    matches!(g.kind, FnKind::Fallback | FnKind::Receive)
                        && g.lifted
                            .as_ref()
                            .is_some_and(|l| !lift::always_reverts(l, l.entry))
                        && (!payable || g.mutability == crate::function::Mutability::Payable)
                })
            };
            let mut tell = |id: &'static str,
                            title: &str,
                            sev: Severity,
                            desc: String,
                            evidence: Vec<String>,
                            rec: &str,
                            findings: &mut Vec<Finding>| {
                if told.insert((f.pc, call.address.clone(), id)) {
                    push_fact(
                        findings,
                        id,
                        title,
                        sev,
                        Confidence::Medium,
                        f,
                        desc,
                        evidence,
                        rec,
                    );
                }
            };
            if call.approval {
                let open = report
                    .findings
                    .iter()
                    .find(|x| x.id == "arbitrary-transferfrom" && x.severity <= Severity::High);
                if let Some(open) = open {
                    tell(
                        "approval-to-open-spender",
                        "Tokens are approved to a contract that moves them for any caller",
                        Severity::High,
                        format!(
                            "`{}` approves the contract at {} to spend tokens this contract holds. That contract's own report finds that `{}` moves tokens from an account its caller chooses, and this contract is such an account once the approval stands.",
                            f.name,
                            call.address,
                            open.function.as_deref().unwrap_or("a function"),
                        ),
                        vec![call.line.clone()],
                        "Approve only the amount a single operation needs, to a spender that moves tokens only from its own caller.",
                        findings,
                    );
                }
                continue;
            }
            let target = call.selector.and_then(|sel| {
                let hex = format!("{sel:#010x}");
                externals()
                    .find(|g| {
                        g.selector
                            .as_deref()
                            .is_some_and(|s| s.eq_ignore_ascii_case(&hex))
                    })
                    .map(|g| (hex, g))
            });
            match (call.selector, &target) {
                (Some(sel), None) if !catch_all(false) => tell(
                    "linked-call-unanswered",
                    "A call names a function the called contract does not have",
                    Severity::Medium,
                    format!(
                        "`{}` calls selector {sel:#010x} on the contract at {}. That contract's code has no function with this selector and nothing that runs for an unknown one, so the call fails every time.",
                        f.name, call.address
                    ),
                    vec![call.line.clone()],
                    "Call a function the target implements, or point the call at the contract that does.",
                    findings,
                ),
                (None, _) if call.sends_value && !catch_all(true) => tell(
                    "value-to-non-payable",
                    "Ether is sent to a contract that does not accept it",
                    Severity::Medium,
                    format!(
                        "`{}` sends ether with no function selected to the contract at {}, whose code has no payable receive or fallback. The transfer fails every time.",
                        f.name, call.address
                    ),
                    vec![call.line.clone()],
                    "Send value through a payable function of the target, or to an address that accepts plain transfers.",
                    findings,
                ),
                _ => {}
            }
            let Some((hex, g)) = target else { continue };
            if call.sends_value && g.mutability != crate::function::Mutability::Payable {
                tell(
                    "value-to-non-payable",
                    "Ether is sent to a contract that does not accept it",
                    Severity::Medium,
                    format!(
                        "`{}` sends ether with its call to `{}` on the contract at {}, and that function reverts when it receives any. The call fails whenever the amount is not zero.",
                        f.name, g.name, call.address
                    ),
                    vec![call.line.clone()],
                    "Send value only to a payable function.",
                    findings,
                );
            }
            let tag = format!("[{hex}]");
            let rated: Vec<&Finding> = report
                .findings
                .iter()
                .filter(|x| {
                    x.severity <= Severity::High
                        && x.function
                            .as_deref()
                            .is_some_and(|name| name.contains(&tag))
                })
                .collect();
            let Some(worst) = rated.iter().map(|x| x.severity).min() else {
                continue;
            };
            let titles: Vec<String> = rated
                .iter()
                .take(3)
                .map(|x| format!("{} ({})", x.title, x.id))
                .collect();
            tell(
                "linked-callee-defect",
                "A called function has a serious finding in its own contract's report",
                if worst == Severity::Critical { Severity::High } else { Severity::Medium },
                format!(
                    "`{}` calls `{}` on the contract at {}. That contract's own report rates this function {}: {}. What this contract takes from the call is only as sound as that function.",
                    f.name,
                    g.name,
                    call.address,
                    if worst == Severity::Critical { "critical" } else { "high" },
                    titles.join("; "),
                ),
                vec![call.line.clone()],
                "Review the linked contract's finding before relying on this call, and check what this contract does when the call misbehaves.",
                findings,
            );
        }
    }
}

enum UseKind {
    CallTarget { delegated: bool },
    Gate,
}

struct StoredUse {
    function: usize,
    kind: UseKind,
    value: ExprId,
    loc: origin::Loc,
    own_entry: bool,
    line: String,
}

fn stored_uses(
    ctx: &Ctx,
    fact: &FnFacts,
    function: usize,
    events: &[Event],
    names: &Names,
    stores: &mut Vec<origin::Store>,
    uses: &mut Vec<StoredUse>,
) {
    let layout = ctx.c.compiler.layout;
    let gated = fact.caller_checked || fact.init_guarded;
    let own = names.clone();
    let read_from = |e: ExprId| -> Option<(origin::Loc, bool)> {
        let mut found = None;
        walk(e, &mut HashSet::new(), &mut |_, n| {
            if let (Node::SLoad(k, false, _), None) = (n, &found) {
                found = origin::loc_of(*k, layout).map(|loc| (loc, key_parties(*k).1));
            }
        });
        found
    };
    for ev in events {
        match &ev.stmt {
            Some(Stmt::SStore {
                key,
                val,
                transient: false,
                ..
            }) => {
                if let Some(loc) = origin::loc_of(*key, layout) {
                    stores.push(origin::Store {
                        loc,
                        gated,
                        value: *val,
                        by: function,
                    });
                }
            }
            Some(st @ Stmt::Call { kind, addr, .. }) if *kind != op::STATICCALL => {
                if let Some((loc, own_entry)) = read_from(*addr) {
                    uses.push(StoredUse {
                        function,
                        kind: UseKind::CallTarget {
                            delegated: *kind == op::DELEGATECALL,
                        },
                        value: *addr,
                        loc,
                        own_entry,
                        line: emit::fmt_stmt(st, &own),
                    });
                }
            }
            _ => {}
        }
    }
    for cond in guard_conds(events) {
        walk(cond, &mut HashSet::new(), &mut |_, n| {
            let Node::Op(op::EQ | op::SUB | op::XOR, v) = n else {
                return;
            };
            for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
                let Node::SLoad(k, false, _) = expr::node(unmask(b)) else {
                    continue;
                };
                if let (true, Some(loc)) = (is_caller(a), origin::loc_of(k, layout)) {
                    uses.push(StoredUse {
                        function,
                        kind: UseKind::Gate,
                        value: b,
                        loc,
                        own_entry: key_parties(k).1,
                        line: emit::fmt_cond(cond, &own),
                    });
                }
            }
        });
    }
}

// A fixed slot that an ungated function fills straight from its input is the older rules' ground.
// These two report what they cannot see: values that arrive through other slots or sit in mappings.
fn authority(
    facts: &[FnFacts],
    stores: &[origin::Store],
    uses: &[StoredUse],
    begin: &HashMap<U256, U256>,
    findings: &mut Vec<Finding>,
) -> Option<Section> {
    let mut gates: BTreeMap<origin::Loc, BTreeSet<usize>> = BTreeMap::new();
    for u in uses.iter().filter(|u| matches!(u.kind, UseKind::Gate)) {
        gates.entry(u.loc).or_default().insert(u.function);
    }
    let name = |i: &usize| format!("`{}`", facts[*i].name);
    let mut lines = Vec::new();
    for (loc, gated) in &gates {
        let place = match loc.1 {
            0 => format!("slot {}", loc.0.to_hex()),
            _ => format!("the mapping at slot {}", loc.0.to_hex()),
        };
        let setters: BTreeSet<(usize, bool)> = stores
            .iter()
            .filter(|s| s.loc == *loc)
            .map(|s| (s.by, s.gated))
            .collect();
        let set_by = match setters.is_empty() {
            true => "No function in the runtime code writes it.".to_string(),
            false => {
                let each = setters.iter().map(|(by, checked)| {
                    let how = if *checked {
                        "behind a caller check"
                    } else {
                        "with no caller check"
                    };
                    format!("{} ({how})", name(by))
                });
                format!("It is written by {}.", each.collect::<Vec<_>>().join(", "))
            }
        };
        lines.push(format!(
            "{place} decides who may call {}. {set_by}",
            gated.iter().map(name).collect::<Vec<_>>().join(", "),
        ));
        let unset = !begin.is_empty() && begin.get(&loc.0).is_none_or(|v| v.is_zero());
        if let (true, true, 0, Some(first)) = (setters.is_empty(), unset, loc.1, gated.first()) {
            push_fact(
                findings,
                "gate-never-set",
                "A caller check reads a slot that nothing ever sets",
                Severity::Low,
                Confidence::Medium,
                &facts[*first],
                format!(
                    "{} function(s) compare the caller with slot {}. The constructor leaves that slot at zero and no function in the runtime code writes it, so no account can pass the check and what it protects cannot be called.",
                    gated.len(),
                    loc.0.to_hex(),
                ),
                Vec::new(),
                "Set the slot during construction, or add an authorised function that sets it, or remove the dead functions.",
            );
        }
    }
    (!lines.is_empty()).then_some(Section {
        title: "Authority map".to_string(),
        lines,
    })
}

fn origin_findings(
    ctx: &Ctx,
    facts: &[FnFacts],
    stores: &[origin::Store],
    uses: &[StoredUse],
    findings: &mut Vec<Finding>,
) {
    let model = Model::build(stores, ctx.c.compiler.layout);
    let mut told: HashSet<(usize, origin::Loc, bool)> = HashSet::new();
    for u in uses {
        let f = &facts[u.function];
        let fixed = u.loc.1 == 0;
        if !f.external || !model.of(u.value).open() || (fixed && model.set_directly(u.loc)) {
            continue;
        }
        match u.kind {
            UseKind::CallTarget { delegated } => {
                if f.caller_checked || (u.own_entry && !delegated) {
                    continue;
                }
                if told.insert((u.function, u.loc, false)) {
                    push_fact(
                        findings,
                        "stored-input-call-target",
                        "A call target is read from storage any caller can fill",
                        if delegated { Severity::High } else { Severity::Medium },
                        Confidence::Medium,
                        f,
                        format!(
                            "`{}` needs no role and {} an address it reads from storage. Following every store into that location back through the slots it is copied from, the value can be an argument or the caller of a function that needs no role either, so whoever calls first decides where this call goes.",
                            f.name,
                            if delegated { "runs the code at" } else { "calls" },
                        ),
                        vec![u.line.clone()],
                        "Let only an authorised caller fill the location, or check the address against a fixed set before using it.",
                    );
                }
            }
            UseKind::Gate => {
                if !fixed || !told.insert((usize::MAX, u.loc, true)) {
                    continue;
                }
                push_fact(
                    findings,
                    "gate-on-open-slot",
                    "An access check compares the caller with a value any caller can put there",
                    Severity::High,
                    Confidence::Medium,
                    f,
                    format!(
                        "`{}` compares `msg.sender` with a slot. No function stores an argument there directly, but following the stores back through the slots the value is copied from, it can be an argument or the caller of a function that needs no role. The check then passes for whoever made those calls.",
                        f.name,
                    ),
                    vec![u.line.clone()],
                    "Gate every function on the path that fills the slot.",
                );
            }
        }
    }
}

struct Reached {
    address: String,
    function: String,
    lowers: Option<String>,
    pays: bool,
    gate_store: Option<String>,
    admitted: Option<bool>,
    created: bool,
}

fn reach(
    world: &World,
    from: Option<&str>,
    address: &str,
    selector: &str,
    word: u32,
    depth: u32,
) -> Option<Reached> {
    let lc = world.contract(address)?;
    let report = world.report(address)?;
    let g = report
        .summaries
        .iter()
        .find(|g| g.selector.eq_ignore_ascii_case(selector))?;
    let created = address.contains('#');
    if !created && !g.gated && g.gate_roles.is_empty() {
        return None;
    }
    let listed = |from: &str| lc.admits.iter().any(|a| a.eq_ignore_ascii_case(from));
    let located = !g.gate_slots.is_empty() || !g.gate_roles.is_empty();
    let admitted = match from {
        Some(from) if listed(from) => Some(true),
        Some(_) if lc.gates_read && located => Some(false),
        _ => None,
    };
    let line_of = |uses: &[ParamUse]| uses.iter().find(|u| u.word == word).map(|u| u.line.clone());
    let mut reached = Reached {
        address: address.to_ascii_lowercase(),
        function: g.function.clone(),
        lowers: line_of(&g.lowers),
        pays: g.pays.iter().any(|u| u.word == word),
        gate_store: g
            .stores
            .iter()
            .find(|st| st.word == word && st.gates)
            .map(|st| st.line.clone()),
        admitted,
        created,
    };
    if reached.lowers.is_some() || reached.gate_store.is_some() || depth == 0 {
        return Some(reached);
    }
    for fw in g.forwards.iter().filter(|fw| fw.word == word) {
        let next = reach(
            world,
            Some(address),
            &fw.target,
            &fw.selector,
            fw.arg,
            depth - 1,
        );
        if let Some(next) = next.filter(|n| n.admitted != Some(false)) {
            if next.lowers.is_some() || next.gate_store.is_some() {
                reached.lowers = next.lowers;
                reached.gate_store = next.gate_store;
                reached.pays |= next.pays;
                reached.function = format!("{} (through `{}`)", next.function, g.function);
                reached.address = next.address;
                reached.created = next.created;
                break;
            }
        }
    }
    Some(reached)
}

const PASSED_ON_CONFIRMED: &str = concat!(
    " Confirmed by running the call across the fetched contracts, each linked contract",
    " approving only the callers its storage was read to approve: with a balance in the named",
    " account's entry, a caller holding no role completes the call and that entry ends lower,",
    " and naming a different account lowers that account's entry instead (a reproducing input",
    " is attached)."
);

// Not zero, not the caller, not a contract of the world.
const NAMED: [U256; 2] = [
    U256::from_u64(0x1111_2222_3333_4444),
    U256::from_u64(0x5555_6666_7777_8888),
];

const MAX_SHAPES: usize = 18;

fn place_contract(world: &mut CrossWorld, c: &Contract) -> Option<U256> {
    let address = U256::from_hex_str(c.address.as_deref()?)?;
    if c.info.runtime.is_empty() {
        return None;
    }
    world.place(address, c.info.runtime.clone());
    let units: Vec<U256> = c
        .parts
        .iter()
        .skip(1)
        .filter_map(|part| {
            let at = U256::from_hex_str(&part.address)?;
            world.place(at, part.runtime.clone());
            Some(at)
        })
        .collect();
    if let [implementation] = units[..] {
        for slot in c
            .delegatecall_slots
            .iter()
            .filter_map(|s| U256::from_hex_str(s))
        {
            world.seed(address, slot, implementation);
        }
    }
    for (slot, held) in &c.stored_targets {
        if let (Some(slot), Some(held)) = (U256::from_hex_str(slot), U256::from_hex_str(held)) {
            world.seed(address, slot, held);
        }
    }
    Some(address)
}

// Gates are opened only for callers the contract's storage was read to approve.
// An unread gate must stay shut, or an unverified finding gets confirmed.
fn confirm_passed(ctx: &Ctx, f: &FnFacts, word: u32, target: &str) -> Option<Vec<u8>> {
    if std::env::var("EVMDEC_NO_CONFIRM").is_ok() {
        return None;
    }
    let root = U256::from_hex_str(ctx.c.address.as_deref()?)?;
    let selector = f
        .selector
        .as_deref()
        .and_then(|s| u32::from_str_radix(s.trim_start_matches("0x"), 16).ok());
    let fixed_target = match target.contains('#') {
        true => None,
        false => Some(U256::from_hex_str(target)?),
    };
    let balance = U256::ONE << 128;
    let build = |held: &[(U256, U256)]| -> Option<CrossWorld> {
        let mut world = CrossWorld::new();
        place_contract(&mut world, ctx.c)?;
        for lc in &ctx.c.linked {
            let Some(address) = place_contract(&mut world, lc) else {
                continue;
            };
            let gate = gates(lc);
            for caller in lc.admits.iter().filter_map(|a| U256::from_hex_str(a)) {
                for slot in &gate.slots {
                    world.seed(address, *slot, caller);
                }
                for slot in gate.keys.iter().filter_map(|key| key_for(*key, caller)) {
                    world.seed(address, slot, U256::ONE);
                }
            }
        }
        for (address, slot) in held {
            world.seed(*address, *slot, balance);
        }
        Some(world)
    };
    let nargs = (word as usize + 1).max(8);
    let run = |account: U256, others: &[U256], held: &[(U256, U256)]| {
        let mut args = others.to_vec();
        args[word as usize] = account;
        let data = exec::calldata(selector, &args);
        let mut world = build(held)?;
        world
            .run(root, exec::CALLER, U256::ZERO, data.clone())
            .then_some((data, world))
    };
    let far = |world: &CrossWorld, at: U256| match fixed_target {
        Some(target) => at == target,
        None => world.was_made(at),
    };
    let written = |account: U256| -> Option<HashSet<(U256, U256)>> {
        let (_, world) = run(account, &vec![U256::ZERO; nargs], &[])?;
        let slots = world.writes().iter().filter(|w| far(&world, w.address));
        Some(slots.map(|w| (w.address, w.slot)).collect())
    };
    let (first, second) = (written(NAMED[0])?, written(NAMED[1])?);
    let own: [Vec<(U256, U256)>; 2] = [
        first.difference(&second).copied().collect(),
        second.difference(&first).copied().collect(),
    ];
    if own.iter().any(Vec::is_empty) {
        return None;
    }
    let amounts = [U256::ONE, U256::from_u64(1_000_000_000_000_000_000)];
    let mut shapes: Vec<Vec<U256>> = amounts.iter().map(|a| vec![*a; nargs]).collect();
    for position in (0..nargs).filter(|p| *p != word as usize) {
        for amount in amounts {
            let mut shape = vec![U256::ZERO; nargs];
            shape[position] = amount;
            shapes.push(shape);
        }
    }
    let lowered = |account: usize, shape: &[U256]| -> Option<Vec<u8>> {
        let (data, world) = run(NAMED[account], shape, &own[account])?;
        own[account]
            .iter()
            .any(|(address, slot)| world.stored(*address, *slot) < balance)
            .then_some(data)
    };
    shapes.iter().take(MAX_SHAPES).find_map(|shape| {
        let data = lowered(0, shape)?;
        lowered(1, shape).map(|_| data)
    })
}

fn passed_word_findings(
    ctx: &Ctx,
    facts: &[FnFacts],
    summaries: &[FnSummary],
    findings: &mut Vec<Finding>,
) {
    if !ctx.world.has_other(ctx.c) {
        return;
    }
    let own = ctx.c.address.as_deref();
    let mut told: HashSet<(String, String, u32, &str)> = HashSet::new();
    for sum in summaries.iter().filter(|s| !s.gated && !s.signed) {
        let Some(f) = facts
            .iter()
            .find(|f| f.external && f.selector.as_deref() == Some(sum.selector.as_str()))
        else {
            continue;
        };
        if f.account_authorised && sum.bound.is_empty() {
            continue;
        }
        let reached: Vec<(&ParamForward, Reached)> = sum
            .forwards
            .iter()
            .filter(|fw| !sum.bound.contains(&fw.word))
            .filter_map(|fw| {
                let r = reach(ctx.world, own, &fw.target, &fw.selector, fw.arg, 3)?;
                (r.admitted != Some(false)).then_some((fw, r))
            })
            .collect();
        let lowers_an_entry = reached.iter().any(|(_, r)| r.lowers.is_some());
        for (fw, r) in &reached {
            let confidence = match r.admitted {
                Some(true) => Confidence::High,
                _ => Confidence::Medium,
            };
            let standing = match (r.created, r.admitted) {
                (true, _) => "belongs to a contract this call creates",
                (false, Some(true)) => {
                    "runs only for callers its contract approves, and this contract is one of them"
                }
                (false, _) => "runs only for callers its contract approves",
            };
            let place = describe(&r.address);
            if let Some(line) = &r.lowers {
                if told.insert((sum.selector.clone(), r.address.clone(), fw.word, "lowers")) {
                    push_fact(
                        findings,
                        "unbound-account-passed-on",
                        "An account the caller names is passed to a contract that lowers its entry",
                        if r.pays { Severity::Low } else { Severity::High },
                        confidence,
                        f,
                        format!(
                            "`{}` takes an account from its call data (word {}) and passes it to `{}` on {place} without comparing it with `msg.sender`, checking a signature from it, or reading an approval it gave the caller. That function {standing}, and it lowers the entry stored under the account it is given{}. Whoever calls `{}` therefore chooses whose entry is lowered.",
                            f.name,
                            fw.word,
                            r.function,
                            if r.pays { ", paying the same account" } else { "" },
                            f.name,
                        ),
                        vec![fw.line.clone(), line.clone()],
                        "Require that `msg.sender` is the account, or that the account approved this caller or signed this exact action, before passing it on.",
                    );
                    if let Some(data) = confirm_passed(ctx, f, fw.word, &r.address) {
                        if let Some(last) = findings.last_mut() {
                            last.confirmed = true;
                            last.witness = Some(crate::hex::encode(&data));
                            last.confidence = Confidence::High;
                            last.description.push_str(PASSED_ON_CONFIRMED);
                        }
                    }
                }
            }
            let Some(line) = &r.gate_store else { continue };
            if r.created && !lowers_an_entry {
                continue;
            }
            if told.insert((sum.selector.clone(), r.address.clone(), fw.word, "gate")) {
                let consequence = match r.created {
                    true => format!(
                        "The same call lowers the entry of an account its caller names, so whoever calls `{}` chooses both whose entry is lowered and which address the new contract's checks accept.",
                        f.name
                    ),
                    false => format!(
                        "Whoever calls `{}` therefore chooses the address those checks accept.",
                        f.name
                    ),
                };
                push_fact(
                    findings,
                    "unbound-address-made-privileged",
                    "A caller-chosen address is written to a slot another contract's access checks read",
                    Severity::High,
                    confidence,
                    f,
                    format!(
                        "`{}` passes word {} of its call data, which it never ties to `msg.sender`, to `{}` on {place}. That function {standing}, and it writes the word to a slot that contract compares `msg.sender` with. {consequence}",
                        f.name, fw.word, r.function,
                    ),
                    vec![fw.line.clone(), line.clone()],
                    "Fix the address in the called contract, or let only an authorised caller choose it.",
                );
            }
        }
    }
}

fn conservation_findings(
    facts: &[FnFacts],
    slot_name: &dyn Fn(ExprId) -> String,
    findings: &mut Vec<Finding>,
) {
    for f in facts.iter().filter(|f| f.external) {
        if let Some(m) = f.stale_moves.first() {
            push_fact(
                findings,
                "stale-ledger-write",
                "Two entries of one ledger are written from values read before either write",
                Severity::High,
                Confidence::Medium,
                f,
                format!(
                    "`{}` lowers one entry of a mapping and then raises another, and the value it raises was read before the first write was stored. Nothing compares the two keys, so when both name the same entry the second write replaces the first with a value that never saw the decrease: the entry ends higher than it began and the ledger holds more than it did.",
                    f.name
                ),
                m.lines.to_vec(),
                "Read the second entry after the first write is stored, or require the two keys to differ.",
            );
        }
        if let Some(m) = f.surplus_moves.first() {
            push_fact(
                findings,
                "unbalanced-ledger-move",
                "A ledger's entries rise by more than they fall and no total changes",
                Severity::Medium,
                Confidence::Medium,
                f,
                format!(
                    "Along one chain of writes in `{}` the entries of a mapping rise by {} more than they fall, and the function raises no total. The difference is not taken from any entry, so the ledger's sum grows without a record of it.",
                    f.name,
                    m.surplus.join(" + ")
                ),
                m.lines.clone(),
                "Take every amount credited from an entry that is debited by it, or record it in the total.",
            );
        }
    }
    let rises = |c: &Change| matches!(c, Change::Up(_));
    let amount = |c: &Change| match c {
        Change::Up(a) | Change::Down(a) => Some(*a),
        Change::Set => None,
    };
    let mut in_step: BTreeMap<U256, BTreeMap<ExprId, usize>> = BTreeMap::new();
    for f in facts {
        let mut seen: BTreeSet<(U256, ExprId)> = BTreeSet::new();
        for w in &f.ledger_writes {
            for (slot, change) in &f.total_changes {
                let together = amount(&w.change).is_some_and(|a| !expr::is_const(a))
                    && amount(&w.change) == amount(change)
                    && rises(&w.change) == rises(change);
                if together && seen.insert((w.root, *slot)) {
                    *in_step.entry(w.root).or_default().entry(*slot).or_insert(0) += 1;
                }
            }
        }
    }
    for (root, totals) in &in_step {
        let Some((total, _)) = totals.iter().max_by_key(|(_, n)| **n) else {
            continue;
        };
        for f in facts.iter().filter(|f| f.external && !f.init_guarded) {
            let on: Vec<&LedgerWrite> =
                f.ledger_writes.iter().filter(|w| w.root == *root).collect();
            let one_way = !on.is_empty()
                && on.iter().all(|w| rises(&w.change) && !w.in_loop)
                && on
                    .iter()
                    .all(|w| amount(&w.change).is_some_and(|a| !expr::is_const(a)));
            let total_moves = f.const_writes.iter().any(|(slot, _, _)| slot == total);
            if !one_way || total_moves {
                continue;
            }
            push_fact(
                findings,
                "ledger-total-mismatch",
                "A ledger entry rises without the total that moves with it elsewhere",
                Severity::Medium,
                Confidence::Low,
                f,
                format!(
                    "Elsewhere in this contract an entry of this mapping and `{}` change together by the same amount. `{}` raises an entry, lowers none, and leaves `{}` as it was, so the entries no longer sum to the total the other paths maintain.",
                    slot_name(*total),
                    f.name,
                    slot_name(*total)
                ),
                on.iter().map(|w| w.line.clone()).collect(),
                "Move the total by the same amount wherever an entry is created or removed, or take the amount from another entry.",
            );
        }
    }
}

fn risk_score(findings: &[Finding]) -> u32 {
    let weight = |f: &Finding| -> f64 {
        let base = match f.severity {
            Severity::Critical => 90.0,
            Severity::High => 70.0,
            Severity::Medium => 40.0,
            Severity::Low => 10.0,
            Severity::Info => 0.0,
        };
        let conf = match f.confidence {
            Confidence::High => 1.0,
            Confidence::Medium => 0.9,
            Confidence::Low => 0.75,
        };
        base * conf
    };
    let mut ws: Vec<f64> = findings.iter().map(weight).collect();
    ws.sort_by(|a, b| b.total_cmp(a));
    let Some(top) = ws.first().copied() else {
        return 0;
    };
    let extra: f64 = ws
        .iter()
        .skip(1)
        .map(|w| {
            if *w >= 60.0 {
                4.0
            } else if *w >= 30.0 {
                1.5
            } else if *w >= 7.0 {
                0.5
            } else {
                0.0
            }
        })
        .sum();
    (top + extra).round().min(100.0) as u32
}

fn w0_selector(input: &Option<Vec<ExprId>>, in_len: ExprId) -> Option<u32> {
    input
        .as_ref()
        .and_then(|w| w.first().copied())
        .and_then(|w0| {
            emit::leading_selector(w0, expr::as_const(in_len).and_then(|l| l.as_usize()))
        })
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum BugNeeds {
    TransientStorage,
    CalldataCopy,
    Unknowable,
}

struct CompilerBug {
    first: (u32, u32, u32),
    last: (u32, u32, u32),
    title: &'static str,
    description: &'static str,
    needs: BugNeeds,
}

const COMPILER_BUGS: &[CompilerBug] = &[
    CompilerBug {
        first: (0, 8, 13),
        last: (0, 8, 16),
        title: "StorageWriteRemovalBeforeConditionalTermination",
        description: "The Yul optimizer could remove storage writes preceding a conditional `return`/`stop` in inline assembly (SOL-2022-6). Whether the source uses such assembly cannot be seen in the bytecode.",
        needs: BugNeeds::Unknowable,
    },
    CompilerBug {
        first: (0, 5, 8),
        last: (0, 8, 15),
        title: "HeadOverflowCalldataTuplesABIReencoding",
        description: "ABI re-encoding of calldata tuples ending in a statically-sized calldata array could corrupt data (SOL-2022-5). This contract copies calldata to memory, so the pattern may be present.",
        needs: BugNeeds::CalldataCopy,
    },
    CompilerBug {
        first: (0, 8, 13),
        last: (0, 8, 14),
        title: "InlineAssemblyMemorySideEffects",
        description: "The optimizer could remove memory writes in inline assembly blocks whose results were only read by other assembly (SOL-2022-4). Whether the source uses such assembly cannot be seen in the bytecode.",
        needs: BugNeeds::Unknowable,
    },
    CompilerBug {
        first: (0, 8, 0),
        last: (0, 8, 2),
        title: "KeccakCaching",
        description: "The optimizer could reuse a cached keccak256 result for a different input length (SOL-2021-1). Whether the optimizer took that path cannot be seen in the bytecode.",
        needs: BugNeeds::Unknowable,
    },
    CompilerBug {
        first: (0, 6, 7),
        last: (0, 8, 20),
        title: "FullInlinerNonExpressionSplitArgumentEvaluationOrder",
        description: "With viaIR, the full inliner could evaluate function arguments in the wrong order (SOL-2023-2, only affects --via-ir builds, which the bytecode does not reveal).",
        needs: BugNeeds::Unknowable,
    },
    CompilerBug {
        first: (0, 8, 24),
        last: (0, 8, 25),
        title: "TransientStorageReentrancy",
        description: "Transient storage is not cleared across reentrant calls within a transaction; this contract uses TSTORE/TLOAD.",
        needs: BugNeeds::TransientStorage,
    },
];

fn strip_versions(e: ExprId, memo: &mut HashMap<ExprId, ExprId>) -> ExprId {
    expr::substitute(
        e,
        &|n| match n {
            Node::SLoad(a, t, v) if *v != 0 => Some(expr::intern(Node::SLoad(
                strip_versions(*a, &mut HashMap::new()),
                *t,
                0,
            ))),
            Node::MLoad(a, v) if *v != 0 => Some(expr::intern(Node::MLoad(
                strip_versions(*a, &mut HashMap::new()),
                0,
            ))),
            _ => None,
        },
        memo,
    )
}

fn positional_evidence(
    f: &Finding,
    params: &HashMap<String, Vec<(String, String)>>,
) -> Vec<String> {
    let Some(renames) = f.function.as_ref().and_then(|name| params.get(name)) else {
        return f.evidence.clone();
    };
    f.evidence
        .iter()
        .map(|line| {
            let mut out = String::with_capacity(line.len());
            let mut chars = line.chars().peekable();
            while let Some(c) = chars.next() {
                if !(c.is_ascii_alphabetic() || c == '_') {
                    out.push(c);
                    continue;
                }
                let mut word = String::from(c);
                while let Some(n) = chars
                    .peek()
                    .filter(|n| n.is_ascii_alphanumeric() || **n == '_')
                {
                    word.push(*n);
                    chars.next();
                }
                let option = chars.peek() == Some(&':');
                let member = out.ends_with('.');
                match renames.iter().find(|(name, _)| *name == word) {
                    Some((_, position)) if !option && !member => out.push_str(position),
                    _ => out.push_str(&word),
                }
            }
            out
        })
        .collect()
}

fn merge_findings(
    findings: Vec<Finding>,
    params: &HashMap<String, Vec<(String, String)>>,
) -> Vec<Finding> {
    let conf_rank = |c: Confidence| match c {
        Confidence::High => 2,
        Confidence::Medium => 1,
        Confidence::Low => 0,
    };
    let mut by_fn: Vec<Finding> = Vec::new();
    for f in findings {
        let same = by_fn.iter_mut().find(|p| {
            p.id == f.id && p.title == f.title && p.function.is_some() && p.function == f.function
        });
        match same {
            Some(p) => {
                p.sites += 1;
                for e in f.evidence {
                    if !p.evidence.contains(&e) && p.evidence.len() < 4 {
                        p.evidence.push(e);
                    }
                }
                if f.severity < p.severity {
                    p.severity = f.severity;
                    p.description = f.description;
                }
                if conf_rank(f.confidence) > conf_rank(p.confidence) {
                    p.confidence = f.confidence;
                }
                if p.pc != f.pc {
                    p.pc = None;
                }
            }
            None => by_fn.push(f),
        }
    }
    for f in &mut by_fn {
        if f.sites > 1 {
            f.description.push_str(&format!(
                " The pattern occurs at {} sites in this function.",
                f.sites
            ));
        }
    }
    let mut out: Vec<Finding> = Vec::new();
    let mut extra: Vec<Vec<String>> = Vec::new();
    for f in by_fn {
        let same = f.pc.and_then(|_| {
            out.iter().position(|p| {
                p.id == f.id
                    && p.title == f.title
                    && p.pc == f.pc
                    && positional_evidence(p, params) == positional_evidence(&f, params)
                    && p.function.is_some()
                    && f.function.is_some()
            })
        });
        match same {
            Some(i) => {
                if let Some(name) = f.function {
                    extra[i].push(name);
                }
                if f.severity < out[i].severity {
                    out[i].severity = f.severity;
                }
            }
            None => {
                out.push(f);
                extra.push(Vec::new());
            }
        }
    }
    for (f, others) in out.iter_mut().zip(extra) {
        if !others.is_empty() {
            f.description.push_str(&format!(
                " The same code is reached from {}.",
                others
                    .iter()
                    .map(|o| format!("`{}`", o))
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
            if let Some(name) = &mut f.function {
                name.push_str(&format!(" (+{})", others.len()));
            }
        }
    }
    out
}

pub fn render_markdown(c: &Contract, r: &Report, title: &str) -> String {
    let mut out = String::new();
    out.push_str(&format!("# Security report: {}\n\n", title));
    out.push_str(&format!("- Compiler: {}\n- Code size: {} bytes, {} instructions, {} external functions, {} internal functions\n- Coverage: {}/{} code blocks, {} unresolved jumps\n- Kind: {}\n- Risk score: {}/100\n\n",
        c.language, c.stats.code_bytes, c.stats.instructions, c.stats.external_functions, c.stats.internal_functions, c.stats.covered_blocks, c.stats.code_blocks, c.stats.unresolved_jumps,
        if r.contract_kind.is_empty() { "unclassified".to_string() } else { r.contract_kind.join(", ") }, r.risk_score));
    out.push_str("## Findings\n\n");
    let mut counts: Vec<String> = Vec::new();
    for sev in [
        Severity::Critical,
        Severity::High,
        Severity::Medium,
        Severity::Low,
        Severity::Info,
    ] {
        let n = r.findings.iter().filter(|f| f.severity == sev).count();
        if n > 0 {
            counts.push(format!("{} {}", n, format!("{:?}", sev).to_lowercase()));
        }
    }
    out.push_str(&format!(
        "{}\n\n",
        if counts.is_empty() {
            "No findings.".to_string()
        } else {
            counts.join(", ")
        }
    ));
    for (i, f) in r.findings.iter().enumerate() {
        out.push_str(&format!(
            "### {}. [{}] {}\n\n",
            i + 1,
            format!("{:?}", f.severity).to_uppercase(),
            f.title
        ));
        if let Some(func) = &f.function {
            out.push_str(&format!("- Function: `{}`", func));
            if let Some(pc) = f.pc {
                let local = c
                    .functions
                    .iter()
                    .find(|g| display_name(g) == *func)
                    .map_or(pc, |g| c.local_pc(g, pc));
                out.push_str(&format!(" at pc {:#x}", local));
            }
            out.push('\n');
        }
        out.push_str(&format!("- Confidence: {:?}\n", f.confidence));
        if f.confirmed {
            out.push_str("- Confirmed by running it\n");
            for (i, call) in f.setup.iter().enumerate() {
                out.push_str(&format!("- Earlier call {}: `{}`\n", i + 1, call));
            }
            if let Some(w) = &f.witness {
                out.push_str(&format!("- Witness calldata: `{}`\n", w));
            }
            for line in &f.observed {
                out.push_str(&format!("- Observed: {line}\n"));
            }
        }
        out.push_str(&format!("\n{}\n\n", f.description));
        if !f.evidence.is_empty() {
            out.push_str("```solidity\n");
            for e in &f.evidence {
                out.push_str(e);
                out.push('\n');
            }
            out.push_str("```\n\n");
        }
        out.push_str(&format!("Recommendation: {}\n\n", f.recommendation));
    }
    for section in &r.maps {
        out.push_str(&format!("## {}\n\n", section.title));
        for line in &section.lines {
            out.push_str(&format!("- {line}\n"));
        }
        out.push('\n');
    }
    if !r.privileged_functions.is_empty() {
        out.push_str("## Privileged functions (gated by msg.sender checks)\n\n");
        for p in &r.privileged_functions {
            out.push_str(&format!("- `{}`\n", p));
        }
        out.push('\n');
    }
    if !r.unauthenticated_state_changers.is_empty() {
        out.push_str("## State-changing functions callable by anyone\n\n");
        for p in &r.unauthenticated_state_changers {
            out.push_str(&format!("- `{}`\n", p));
        }
        out.push('\n');
    }
    if !r.external_calls.is_empty() {
        out.push_str("## External calls\n\n");
        for e in &r.external_calls {
            out.push_str(&format!("- `{}`\n", e));
        }
        out.push('\n');
    }
    if let Some(comp) = &c.composite {
        out.push_str("## Parts\n\n");
        out.push_str(&format!("{}. Functions are listed under the address whose code holds them; all of them run in this contract's storage.\n\n", comp.kind));
        out.push_str("| role | address | selectors | compiler | code |\n|---|---|---|---|---|\n");
        for p in &c.parts {
            let sels = match (p.role, p.selectors.len()) {
                (decompile::PartRole::Shell, _) => "router".to_string(),
                (_, 0) => "all unrouted".to_string(),
                (_, n) => n.to_string(),
            };
            out.push_str(&format!(
                "| {:?} | `{}` | {} | {} | {} bytes |\n",
                p.role, p.address, sels, p.compiler, p.stats.code_bytes
            ));
        }
        out.push('\n');
    }
    if !c.call_targets.is_empty() {
        out.push_str("## Hard-coded dependencies\n\n");
        out.push_str("Addresses this contract calls as literals (fetched and reported separately when following links on-chain):\n\n");
        for t in &c.call_targets {
            out.push_str(&format!("- `0x{}`\n", t.trim_start_matches("0x")));
        }
        out.push('\n');
    }
    if !c.library_targets.is_empty() {
        out.push_str("## Libraries\n\n");
        out.push_str("Addresses whose code this contract runs in its own storage through a call it builds itself (a linked library, not an implementation):\n\n");
        for t in &c.library_targets {
            out.push_str(&format!("- `0x{}`\n", t.trim_start_matches("0x")));
        }
        out.push('\n');
    }
    if !c.linked.is_empty() {
        out.push_str("## Contracts fetched with this one\n\n");
        out.push_str(
            "| Address | Reached | Calls away | Approves its caller |\n|---|---|---|---|\n",
        );
        for lc in &c.linked {
            let address = lc.address.as_deref().unwrap_or("?");
            let (how, depth, approves) = match &lc.link {
                Some(link) => {
                    let listed = lc.admits.iter().any(|a| a.eq_ignore_ascii_case(&link.from));
                    let approves = match (listed, lc.gates_read) {
                        (true, _) => "yes",
                        (false, true) => "no",
                        (false, false) => "not read",
                    };
                    let how = format!("{}, from {}", link.how, short_address(&link.from));
                    (how, link.depth.to_string(), approves)
                }
                None => ("call target".to_string(), "1".to_string(), "not read"),
            };
            out.push_str(&format!("| `{address}` | {how} | {depth} | {approves} |\n"));
        }
        out.push('\n');
    }
    if !c.unfollowed.is_empty() {
        out.push_str("## Call targets not fetched\n\n");
        out.push_str("| Target | Called by | Why |\n|---|---|---|\n");
        for u in &c.unfollowed {
            out.push_str(&format!(
                "| `{}` | `{}` | {} |\n",
                u.target,
                short_address(&u.from),
                u.reason
            ));
        }
        out.push('\n');
    }
    if !c.storage.is_empty() {
        let composite = !c.parts.is_empty();
        let parts_of = |slot: &str| -> String {
            c.parts
                .iter()
                .enumerate()
                .filter(|(_, p)| p.storage.iter().any(|v| v.slot == slot))
                .map(|(i, p)| {
                    if i == 0 {
                        "shell".to_string()
                    } else {
                        short_address(&p.address)
                    }
                })
                .collect::<Vec<_>>()
                .join(", ")
        };
        if composite {
            out.push_str("## Storage layout\n\n| slot | name | type | reads | writes | parts |\n|---|---|---|---|---|---|\n");
        } else {
            out.push_str(
                "## Storage layout\n\n| slot | name | type | reads | writes |\n|---|---|---|---|---|\n",
            );
        }
        let tail = |slot: &str| {
            if composite {
                format!(" {} |", parts_of(slot))
            } else {
                String::new()
            }
        };
        for s in &c.storage {
            if s.fields.is_empty() {
                out.push_str(&format!(
                    "| {} | {} | {} | {} | {} |{}\n",
                    s.slot,
                    s.name,
                    s.ty.replace('|', "\\|"),
                    s.reads,
                    s.writes,
                    tail(&s.slot)
                ));
                let owner = s.struct_name();
                for m in &s.members {
                    let cells: Vec<(String, &str, &str)> = match m.fields.is_empty() {
                        true => vec![(String::new(), m.name.as_str(), m.ty.as_str())],
                        false => m
                            .fields
                            .iter()
                            .map(|f| {
                                let bytes = format!(
                                    " bytes {}..{}",
                                    f.offset,
                                    f.offset + f.bits.div_ceil(8)
                                );
                                (bytes, f.name.as_str(), f.ty.as_str())
                            })
                            .collect(),
                    };
                    for (bytes, name, ty) in cells {
                        out.push_str(&format!(
                            "| {} +{}{} | {}.{} | {} | | |{}\n",
                            s.slot,
                            m.offset,
                            bytes,
                            owner,
                            name,
                            ty.replace('|', "\\|"),
                            tail(&s.slot)
                        ));
                    }
                }
            } else {
                for fld in &s.fields {
                    out.push_str(&format!(
                        "| {} bytes {}..{} | {} | {} | {} | {} |{}\n",
                        s.slot,
                        fld.offset,
                        fld.offset + fld.bits.div_ceil(8),
                        fld.name,
                        fld.ty,
                        s.reads,
                        s.writes,
                        tail(&s.slot)
                    ));
                }
            }
        }
        out.push('\n');
    }
    if !c.events.is_empty() {
        out.push_str("## Events\n\n");
        for e in &c.events {
            out.push_str(&format!("- `{}`\n", e));
        }
        out.push('\n');
    }
    if !c.selectors_called.is_empty() {
        out.push_str("## Selectors called on other contracts\n\n");
        for s in &c.selectors_called {
            out.push_str(&format!("- `{}`\n", s));
        }
        out.push('\n');
    }
    let _ = sigs::get();
    out
}
