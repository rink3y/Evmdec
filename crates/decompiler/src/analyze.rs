//! Security analysis over the lifted IR: a rule engine producing findings with evidence.

use crate::compiler;
use crate::decompile::{self, Contract, Function};
use crate::emit::{self, Names, SlotSpace};
use crate::expr::{self, ExprId, Node};
use crate::function::FnKind;
use crate::lift::{self, Lifted, Stmt, Term};
use crate::opcode as op;
use crate::sigs;
use crate::ssa;
use crate::type_rules;
use crate::u256::U256;
use serde::Serialize;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

/// Impact of a finding, worst first; the derived ordering is what the report sorts by.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    /// Direct loss of funds or full takeover by an unprivileged caller.
    Critical,
    /// Serious damage that needs some precondition or a privileged but unexpected actor.
    High,
    /// Exploitable under narrower conditions, or a weakness that amplifies another bug.
    Medium,
    /// Minor robustness issue with little direct impact.
    Low,
    /// Not a defect: a fact about the contract worth knowing (compiler, coverage, kind).
    Info,
}

/// How sure a rule is that its finding is real, given the lifted IR it had to work from.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Confidence {
    /// The pattern is unambiguous in the bytecode.
    High,
    /// Plausible, but the rule relies on a heuristic (names, shapes) that can misfire.
    Medium,
    /// Speculative: the rule saw something suspicious but could not confirm the data flow.
    Low,
}

/// One issue reported by a rule, with the evidence that triggered it.
#[derive(Clone, Debug, Serialize)]
pub struct Finding {
    /// Stable, kebab-case rule identifier such as `reentrancy` or `arbitrary-delegatecall`.
    pub id: String,
    /// One-line human-readable headline.
    pub title: String,
    /// Impact if the finding is real.
    pub severity: Severity,
    /// How sure the rule is.
    pub confidence: Confidence,
    /// Display name of the function the finding is in; absent for contract-wide findings.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub function: Option<String>,
    /// Program counter of the offending instruction, when the finding points at one site.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub pc: Option<usize>,
    /// What was found and why it matters, in prose.
    pub description: String,
    /// Decompiled statements (Solidity-like) that triggered the rule.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub evidence: Vec<String>,
    /// What to do about it.
    pub recommendation: String,
    /// Number of code sites folded into this finding (same rule, same function).
    #[serde(skip_serializing_if = "is_one")]
    pub sites: usize,
    /// The confirmation pass reached this finding's sink from a fresh state with an arbitrary
    /// caller: the vulnerability is not merely a pattern but reachable.
    #[serde(skip_serializing_if = "std::ops::Not::not", default)]
    pub confirmed: bool,
    /// The calldata (0x-prefixed) that reached the sink, when `confirmed`.
    #[serde(skip_serializing_if = "Option::is_none", default)]
    pub witness: Option<String>,
}

fn is_one(n: &usize) -> bool {
    *n == 1
}

/// The result of [`analyze`]: findings plus the contract-wide facts they were judged against.
#[derive(Clone, Debug, Serialize, Default)]
pub struct Report {
    /// Standards the contract appears to implement, from its selectors ("ERC20 token",
    /// "Upgradeable (UUPS/transparent admin)", ...). Empty when nothing matched.
    pub contract_kind: Vec<String>,
    /// Deduplicated and merged findings, sorted by severity then function name.
    pub findings: Vec<Finding>,
    /// State-changing functions gated by a msg.sender check somewhere on their path.
    pub privileged_functions: Vec<String>,
    /// External functions that change state (storage, calls, creates, selfdestruct) and have no
    /// msg.sender check anywhere on their path.
    pub unauthenticated_state_changers: Vec<String>,
    /// Every call out of the contract as `function: statement`, sorted and deduplicated.
    pub external_calls: Vec<String>,
    /// Number of findings per severity, keyed by the lowercase severity name.
    pub summary: BTreeMap<String, usize>,
    /// 0..100, derived from the findings: the worst one (weighted by confidence) sets the level
    /// and the others add a little, so one confirmed critical outweighs many notes.
    pub risk_score: u32,
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

/// Does `e` contain the exact expression `target`?
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
/// `sync()` of a Uniswap V2 pair.
const SEL_SYNC: u32 = 0xfff6cae9;
/// `skim(address)` of a Uniswap V2 pair.
const SEL_SKIM: u32 = 0xbc25cf77;
/// `getReserves()` of a Uniswap V2 pair.
const SEL_GET_RESERVES: u32 = 0x0902f1ac;
/// `token0()` of a Uniswap V2 pair.
const SEL_TOKEN0: u32 = 0x0dfe1681;
/// `token1()` of a Uniswap V2 pair.
const SEL_TOKEN1: u32 = 0xd21220a7;
/// Selectors only a pool-type contract answers, a secondary sign that a stored address is one:
/// Uniswap V2 pairs, V3 pools, the V4 manager, Curve pools and Balancer vaults.
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
/// Token transfers that invoke a receiver hook on the destination (ERC721 / ERC1155 / ERC777).
const CALLBACK_SELECTORS: &[u32] = &[
    0x42842e0e, 0xb88d4fde, 0xf242432a, 0x2eb2c2d6, 0x150b7a02, 0xf23a6e61, 0xbc197c81, 0x0023de29,
    0x9bd9bbc6, 0x62ad1b83,
];
/// secp256k1 half order: `s` values above it are the malleable twin of a valid signature.
const SECP_HALF_ORDER: &str = "7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a0";

/// Flattened event stream of a function including inlined internal callees (depth-limited),
/// used by order-sensitive rules.
#[derive(Clone)]
struct Event {
    /// Node of the function being analysed that this event belongs to (the call-site node for
    /// events inlined from internal callees), so it indexes `l.nodes` and works with `reaches`.
    node: usize,
    /// Program counter of the node that holds the statement (inside the callee when inlined).
    pc: usize,
    /// Entry pc of the internal function whose body holds the statement, when inlined.
    callee: Option<usize>,
    /// Which inlined body the event belongs to: 0 for the function itself, otherwise a number
    /// unique to one inlining of one helper, so two events with the same `inst` share a graph.
    inst: usize,
    /// Node id inside that body (`inner` indexes the helper's own `Lifted` when `inst != 0`).
    inner: usize,
    /// The inlining path from the function down to the event: `(inst, callee entry pc, node in
    /// that body)` per level, the last entry being the event's own body and node.
    path: Vec<(usize, Option<usize>, usize)>,
    stmt: Option<Stmt>,
    term: Option<Term>,
    /// Inside a loop body.
    in_loop: bool,
}

struct Ctx<'a> {
    c: &'a Contract,
    internals: HashMap<usize, &'a Function>,
    version: Option<(u32, u32, u32)>,
    vyper: bool,
    /// Memory an internal function (transitively) writes: constant offsets with lengths, or
    /// `None` when it writes through a pointer.
    callee_writes: RefCell<HashMap<usize, Option<MemWrites>>>,
    /// Counter handing out `Event::inst` numbers.
    inst_seq: std::cell::Cell<usize>,
    /// Whether an internal function (transitively) divides, by entry pc.
    divides: RefCell<HashMap<usize, bool>>,
    /// Root slots of caller-keyed mappings that act as roles: every function writing them is
    /// itself gated (by an owner comparison or by a role), or nothing writes them at runtime.
    /// A test of `mapping[msg.sender]` is an access check only for these; for the others it is
    /// a balance or stake check anyone can satisfy.
    roles: HashSet<U256>,
    /// Constant slots some runtime code writes whole.
    slot_writes: HashSet<U256>,
    /// Packed fields some runtime code writes: (slot, byte offset, bits).
    field_writes: HashSet<(U256, u32, u32)>,
    /// The bytecode uses transient storage (`TLOAD`/`TSTORE`).
    transient_storage: bool,
    /// An ordinary external function copies calldata to memory (calldata arrays or tuples
    /// passed on, re-encoded).
    calldata_copies: bool,
    /// Constant slots some external function without an access check increments
    /// (`length + 1`, helpers included), with the names of those functions: arrays anyone can
    /// add an entry to.
    unguarded_extenders: HashMap<U256, Vec<String>>,
}

/// Constant-offset memory writes of a unit: `(offset, length)` with `None` for an unknown length.
type MemWrites = Vec<(ExprId, Option<u64>)>;

/// What one entry point does, kept for the cross-function passes: the access-control policy
/// the contract follows (and the functions that deviate from it) and multi-step attack chains.
struct FnFacts {
    /// Display name (`display_name`).
    name: String,
    /// The 4-byte selector as `0x`-prefixed hex, for external functions.
    selector: Option<String>,
    /// Entry pc, used as the finding's location.
    pc: usize,
    /// An externally callable function (not fallback/receive/constructor).
    external: bool,
    /// Writes storage, calls out, creates or self-destructs.
    state_changing: bool,
    /// A msg.sender comparison guards it somewhere on its path (helpers included).
    caller_checked: bool,
    /// Constant storage slots its msg.sender checks compare against, with their printed names.
    auth_slots: Vec<(ExprId, String)>,
    /// Constant (non-mapping) storage slots it writes: slot, how the value is chosen, printed
    /// statement.
    const_writes: Vec<(ExprId, WriteSource, String)>,
    /// Calls that carry ether: target, amount, printed statement.
    ether_out: Vec<(ExprId, ExprId, String)>,
    /// `selfdestruct` beneficiaries with the printed statement.
    selfdestructs: Vec<(ExprId, String)>,
    /// `delegatecall` targets with the printed statement.
    delegatecalls: Vec<(ExprId, String)>,
    /// Some guard compares against the block number or timestamp.
    time_gated: bool,
    /// Some guard tests a constant slot for "not yet set" (`require(owner == 0)`): an
    /// initializer, reachable only while the contract is uninitialised.
    init_guarded: bool,
    /// Calls whose target is an address held in a constant storage slot: the slot, the
    /// payload selector when known, whether the call is static, and whether the payload
    /// carries `msg.sender`.
    stored_callees: Vec<StoredCall>,
    /// Writes that subtract from a balance entry: the ledger root, the entry key, the printed
    /// statement.
    debits: Vec<Debit>,
    /// Mapping keys whose allowance for `msg.sender` the function reads (`allowance[k][sender]`).
    allowance_of: Vec<ExprId>,
    /// `sync()`/`skim()` calls on a pair.
    syncs: Vec<PairSync>,
    /// Constant slots written with an address another contract returned: a factory-made pool,
    /// a router's pair, a manager, whatever the design calls it.
    factory_slots: Vec<ExprId>,
    /// Constant slots whose address the function's guards compare with a transfer party (a
    /// calldata word, the caller, an argument): the token singles this address out, as every
    /// pool-aware token does for fees, limits or cooldowns.
    compared_slots: Vec<ExprId>,
    /// `(ledger root, slot)`: ledger entries read under an address held in a constant slot,
    /// the way a token prices or limits against its pool's balance.
    ledger_reads: Vec<(U256, ExprId)>,
    /// The function (or a helper it calls) authorises per account: it reads an entry keyed by
    /// `msg.sender` under another account (`allowance[owner][sender]`, operator approvals) or
    /// compares `msg.sender` with a mapping value (`approved[tokenId]`, `owners[id]`).
    account_authorised: bool,
    /// The function recovers a signer (`ecrecover`): accounts may be authorised by signature.
    signature_authorised: bool,
    /// Payout limits of the shape `deposits - liabilities` that gate value leaving this function.
    avail_bounds: Vec<AvailBound>,
    /// Every limit of that shape the function states, whether or not it caps a payout: in any
    /// comparison, or as a returned value (a view reporting what is available). Used only as the
    /// reference another function's payout limit is held against.
    ref_bounds: Vec<AvailBound>,
    /// The function lets value leave: an ether call, a token transfer, or a ledger debit.
    moves_value: bool,
}

/// A call to an address held in a constant storage slot.
#[derive(Clone, Debug)]
struct StoredCall {
    /// The constant slot key.
    slot: ExprId,
    /// Selector of the payload, when it is known.
    selector: Option<u32>,
    /// `STATICCALL`.
    is_static: bool,
    /// The payload mentions `msg.sender`.
    passes_sender: bool,
    /// Printed statement.
    line: String,
}

/// A write that lowers a balance entry.
#[derive(Clone, Debug)]
struct Debit {
    /// Root slot of the ledger mapping.
    root: U256,
    /// The entry key (the account).
    key: ExprId,
    /// The account as the printer shows it.
    account_text: String,
    /// Printed statement.
    line: String,
}

/// One field of pooled storage: the slot shape of a mapping entry or array element and the bit
/// range a read extracts from it, so the two halves of a packed slot are different fields.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Field {
    /// Slot shape (root and step kinds), independent of the concrete key.
    shape: ssa::Shape,
    /// Lowest bit of the field within the slot.
    lo: u32,
    /// Width in bits.
    width: u32,
}

/// A payout limit of the form `credits - liabilities`: one side of an ordering comparison that
/// adds some pooled fields and subtracts others. Two functions that limit value over the same
/// pooled record must subtract the same liability fields.
#[derive(Clone, Debug)]
struct AvailBound {
    /// Fields summed as available credit.
    added: BTreeSet<Field>,
    /// Fields subtracted as owed.
    subbed: BTreeSet<Field>,
    /// A readable name for each field, for the finding's evidence.
    names: HashMap<Field, String>,
    /// The printed limit expression.
    line: String,
}

/// A `sync()`/`skim()` call on a pair.
#[derive(Clone, Debug)]
struct PairSync {
    /// The pair as the printer shows it.
    target: String,
    /// A storage write or a state-changing call on a path that reaches this call precedes it.
    after_mutation: bool,
    /// Printed statement.
    line: String,
}

/// Where the value stored into a constant slot comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum WriteSource {
    /// A calldata word stored as is (an address mask on it is allowed): the caller picks it.
    Calldata,
    /// `msg.sender` stored as is.
    Caller,
    /// Anything else: a computed value, a constant, another slot.
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

/// The `require` and branch conditions along a function's events, helpers included.
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

/// A condition on the block number or timestamp (a deadline, a lock-up, a vesting schedule).
fn is_time_cond(cond: ExprId) -> bool {
    mentions(cond, &|n| {
        matches!(n, Node::Env(op::TIMESTAMP | op::NUMBER, _))
    })
}

/// Does the expression read the (persistent) storage slot `slot`?
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
    };
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

/// Constant-offset memory writes of some nodes (`None`: a write through a pointer or into
/// an unknown callee).
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

/// Forget what `mem` knows about the bytes `writes` touch (everything, for pointer writes).
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
/// Does `e` mention `target` anywhere outside the subtree `excluded`?
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
/// `e` without an address mask (`x & (2^160 - 1)`), so the same account compares equal
/// whether or not a cast was printed around it.
fn unmask(e: ExprId) -> ExprId {
    match expr::node(e) {
        Node::Op(op::AND, v) if expr::as_const(v[1]) == Some(expr::mask_bits(160)) => unmask(v[0]),
        _ => e,
    }
}

/// `(root, account)` when `key` is an entry of a single-level mapping: `keccak(account . root)`.
fn ledger_entry(key: ExprId, layout: emit::MappingLayout) -> Option<(U256, ExprId)> {
    let path = ssa::slot_path(key, layout)?;
    match path.steps[..] {
        [ssa::Step::Key(k)] => Some((path.root, k)),
        _ => None,
    }
}

/// The pooled field `e` reads: `SLOAD(k)`, optionally shifted right by a constant and masked
/// with a low mask, where `k` is a mapping entry or array element. A global scalar slot is not
/// pooled state and gives `None`.
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

/// Accumulate the linear combination `e` into signed coefficients per pooled field, so
/// `a + a - a` keeps one `a` and `a - a` cancels. Only sums, differences and width casts are
/// followed: a field inside a product, a quotient or a comparison is a factor, not a balance
/// term, and is left out.
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

/// Debug aid: the additive leaves of `e` that are memory reads or internal-call results, which
/// `linear_fields` cannot place, with the sign they carry.
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

/// Debug aid (`EVMDEC_DEBUG_UNPLACED`): every difference in the function that subtracts pooled
/// fields but also holds memory reads or internal-call results the accounting rule cannot place.
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

/// `e` as a limit, `credits - liabilities`: at least one pooled field with a positive net
/// coefficient and at least one with a negative one.
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

/// Does a limit compared with `other` cap one of `outflows`? It does when `other` is the amount
/// that leaves, sits inside it, contains it, or reads the same calldata word.
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

/// Every payout limit in `e`: each side of an ordering comparison (`<`, `>`, signed or not)
/// that adds at least one pooled field and subtracts at least one. Each side is read on its
/// own, so the amount being limited never mixes into the limit's fields.
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
            for (side, other) in [(v[0], v[1]), (v[1], v[0])] {
                if expr::is_const(other) {
                    continue;
                }
                let Some(b) = linear_bound(side, layout, names) else {
                    continue;
                };
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

/// `Some(amount)` when `val` is `SLOAD(key) - amount`: the entry lowered rather than set.
fn subtracts_from(val: ExprId, key: ExprId) -> Option<ExprId> {
    let Node::Op(op::SUB, v) = expr::node(val) else {
        return None;
    };
    let reads_entry = matches!(expr::node(v[0]), Node::SLoad(k, false, _) if k == key);
    reads_entry.then_some(v[1])
}

/// Does `e` read a mapping entry keyed by `msg.sender` under another key (`x[a][sender]`)?
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

/// Does `e` compare `msg.sender` with a value loaded from a mapping entry (`approved[id] ==
/// sender`, `owner[id] == sender`)?
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

/// Constant slots whose stored address `cond` compares with a transfer party: `to == pair`,
/// `from != pair` (also written `from - pair` as a branch condition).
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

/// Record `(root, slot)` for every single-level mapping entry read under an address held in a
/// constant slot (`balanceOf[pair]`).
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

/// Record the outer keys of two-level mapping reads whose inner key is `msg.sender`:
/// `allowance[owner][msg.sender]`.
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

/// Does `e` depend on msg.sender: directly, through a phi variable whose every incoming value
/// does, or through the result of a call whose payload named msg.sender (`crops(msg.sender)`,
/// a registry mapping the caller to its account)?
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

/// Is `addr` a contract this function deployed from its own code (a `CREATE` whose init code
/// was copied out of the running bytecode)? Such a callee is as trusted as the contract itself.
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

/// The dynamic storage array an expression indexes into (`stor_4[i]` reads
/// `sload(keccak256(4) + i)`): its root slot.
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

/// Is `e` an address read from storage that no runtime code writes (a slot or packed field set
/// only at deployment)? Such a callee is fixed: calling it is a call into one known contract.
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

/// Does `e` mention a node matching `pred`, looking through helper results into the helper's
/// returned expressions (and their helpers, to a small depth)?
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

/// `deep_mentions` inside one lifted graph (a helper body): helper results resolve through the
/// graph's own internal calls.
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

/// Loop membership of nodes (back edges via DFS).
fn loop_nodes(l: &Lifted) -> HashSet<usize> {
    let mut in_loop = HashSet::new();
    let n = l.nodes.len();
    for x in 0..n {
        let mut seen = HashSet::new();
        let mut stack: Vec<usize> = l.nodes[x].succs.clone();
        let mut found = false;
        while let Some(y) = stack.pop() {
            if y == x {
                found = true;
                break;
            }
            if !seen.insert(y) || seen.len() > 5000 {
                continue;
            }
            stack.extend(l.nodes[y].succs.iter().copied());
        }
        if found {
            in_loop.insert(x);
        }
    }
    in_loop
}

fn events_of(ctx: &Ctx, l: &Lifted, depth: usize, in_loop_outer: bool) -> Vec<Event> {
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

/// Can `b` execute after `a` on some path? The two inlining paths are walked together: at the
/// deepest body both events share, their nodes in that body decide (the same node counts, since
/// `b` follows `a` in event order; otherwise that body's graph is asked).
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

/// `subst` maps the helper's `Arg(i)` to the caller's actual values, so inlined statements read
/// in the caller's terms (`msg.sender` rather than `arg1`). `mem` replays the memory writes seen
/// so far; inside a helper, reads of memory the helper could not know (a payload the caller
/// built and passed by pointer) are resolved through it.
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
                            out.extend(events_of_in(
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
                            ));
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

/// Can node `b` be reached from node `a` (inclusive of a == b)?
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

/// `0x1234…cdef`: an address shortened for a table cell.
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

/// Append a finding. One positional constructor keeps the ~50 rule sites to a single call each.
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
    });
}

/// The root slot of a mapping key (`keccak256(k . slot)`, nested mappings included): the small
/// constant among the hashed words, innermost first.
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

/// `msg.sender == <slot | constant | this | origin>`: the comparison shape of an access check.
fn is_owner_cond(cond: ExprId) -> bool {
    is_auth_cond(cond) && role_test_root(cond).is_none()
}

/// The mapping whose caller-keyed entry `cond` tests as a boolean (`require(roles[msg.sender])`,
/// `if (!m[msg.sender])`): its root slot.
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

/// An access check in this contract: an owner comparison, or a test of a role mapping (see
/// `Ctx::roles`). A test of any other caller-keyed mapping is accounting, not authorisation.
fn is_auth_cond_in(cond: ExprId, roles: &HashSet<U256>) -> bool {
    match role_test_root(cond) {
        Some(root) => roles.contains(&root),
        None => is_auth_cond(cond),
    }
}

/// Which caller-keyed mappings are roles: iterate to a fixpoint from the mappings every writer
/// of which compares msg.sender against a slot or constant, adding mappings whose writers are
/// gated by an already known role (or by the mapping itself, as a multi-owner wallet is).
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

/// Does `cond` have the shape of an authorization check on msg.sender: `msg.sender == <storage
/// or constant address>`, or a caller-keyed storage flag used directly as a boolean
/// (`roles[msg.sender]`)? Shape only: see `is_auth_cond_in` for the contract-aware test.
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
        Node::Op(op::EQ, v) => {
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

/// Does the function check `msg.sender` (owner/role/constant) before `node`?
/// Conditions a node tests: its branch condition and the inlined guards (`require`) it holds.
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

/// All internal functions reachable from `f` through internal calls (transitively, `f` excluded).
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

/// Storage slots compared against msg.sender anywhere (owner/admin/role slots).
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

/// What a pre-0.8 compiler leaves out, for the `legacy-compiler` finding: overflow checks
/// always, and before 0.5 also the validation of the upper bits of `address` and `bool`
/// arguments during ABI decoding.
fn legacy_consequence(before_0_5: bool) -> &'static str {
    if before_0_5 {
        "Arithmetic does not check for overflow and ABI decoding does not validate the upper bits of address and bool arguments."
    } else {
        "Arithmetic does not check for overflow."
    }
}

/// Run every rule over a decompiled contract and assemble the [`Report`].
pub fn analyze(c: &Contract) -> Report {
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
        internals,
        version,
        vyper: c.language.starts_with("vyper"),
        callee_writes: Default::default(),
        inst_seq: std::cell::Cell::new(0),
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
    let callee_returns: HashMap<usize, Vec<String>> = c
        .functions
        .iter()
        .filter(|f| f.kind == FnKind::Internal)
        .map(|f| (f.pc, f.returns.clone()))
        .collect();
    let names_for = |f: &Function| -> Names {
        decompile::make_names(
            f,
            &c.storage,
            c.compiler.layout,
            &c.string_loaders,
            &callee_returns,
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
        facts.push(collect_facts(&ctx, f, &events, caller_checked, &names));
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
        let guarded_slot = |i: usize| -> Option<ExprId> {
            let mut tested: HashSet<ExprId> = HashSet::new();
            let mut before: HashSet<ExprId> = HashSet::new();
            let mut after: HashSet<ExprId> = HashSet::new();
            for (j, e) in events.iter().enumerate() {
                if let Some(Stmt::SStore { key, val, .. }) = &e.stmt {
                    if expr::is_const(*key) {
                        let restores_const = expr::is_const(*val)
                            || emit::packed_write(*key, *val)
                                .is_some_and(|(_, _, _, v)| expr::is_const(v));
                        if j < i {
                            before.insert(*key);
                        } else if j > i && restores_const {
                            after.insert(*key);
                        }
                    }
                }
                if j < i {
                    if let Some(Stmt::Require { cond, .. }) = &e.stmt {
                        tested.extend(const_sloads(*cond));
                    }
                    if let Some(Term::Branch { cond, .. }) = &e.term {
                        tested.extend(const_sloads(*cond));
                    }
                }
            }
            before
                .iter()
                .find(|k| after.contains(k) && tested.contains(k))
                .copied()
        };

        for (i, ev) in events.iter().enumerate() {
            if matches!(&ev.stmt, Some(Stmt::Call { kind, .. }) if *kind == op::CALL || *kind == op::CALLCODE)
            {
                if let Some(slot) = guarded_slot(i) {
                    lock_slots.entry(slot).or_default().insert(f.pc);
                }
            }
        }
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
                            let (id, sev, conf, extra) = if guarded_slot(i).is_some() {
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
                        let used = events.iter().any(|e2| {
                            e2.stmt.as_ref().is_some_and(|s2| match s2 {
                                Stmt::Drop(_) => false,
                                other => lift::node_exprs(&lift::LNode {
                                    id: 0,
                                    block: 0,
                                    pc: 0,
                                    stmts: vec![other.clone()],
                                    term: Term::Stop,
                                    preds: vec![],
                                    succs: vec![],
                                    entry_stack: vec![],
                                    exit_stack: vec![],
                                })
                                .iter()
                                .any(|e| {
                                    mentions(
                                        *e,
                                        &|n| matches!(n, Node::CallResult(s) if *s == *seq),
                                    )
                                }),
                            }) || e2.term.as_ref().is_some_and(|t| match t {
                                Term::Branch { cond, .. } => mentions(
                                    *cond,
                                    &|n| matches!(n, Node::CallResult(s) if *s == *seq),
                                ),
                                Term::Return { data: Some(d), .. } => d.iter().any(|e| {
                                    mentions(
                                        *e,
                                        &|n| matches!(n, Node::CallResult(s) if *s == *seq),
                                    )
                                }),
                                _ => false,
                            })
                        }) || l.edge_assigns.values().flatten().any(|(_, v)| {
                            mentions(*v, &|n| matches!(n, Node::CallResult(s) if *s == *seq))
                        });
                        if !used && !precompile {
                            push(&mut findings, "unchecked-call", "Return value of external call ignored", if value_nonzero { Severity::Medium } else { Severity::Low }, Confidence::High, Some(f), Some(ev.pc),
                                format!("`{}` ignores the success flag of a low-level call to `{}`. If the call fails (reverting callee, out of gas, non-contract address) execution continues as if it succeeded{}.", f.name, target, if value_nonzero { ", and the ether is kept by this contract while state may assume it was sent" } else { "" }),
                                vec![line.clone()], "Check the returned boolean (`require(success)`) or use a high-level call that reverts on failure.");
                        }
                        if input.is_some() {
                            if let Some(sel) = selector {
                                if matches!(sel, SEL_TRANSFER | SEL_TRANSFER_FROM | SEL_APPROVE) {
                                    let ret_read = |e: ExprId| {
                                        mentions(
                                            e,
                                            &|n| matches!(n, Node::ReturnData(s, _) if *s == *seq),
                                        )
                                    };
                                    let out_zero = expr::as_const(*out_len) == Some(U256::ZERO);
                                    let decoded = events.iter().any(|e2| {
                                        e2.stmt.as_ref().is_some_and(|s2| {
                                            lift::node_exprs(&lift::LNode {
                                                id: 0,
                                                block: 0,
                                                pc: 0,
                                                stmts: vec![s2.clone()],
                                                term: Term::Stop,
                                                preds: vec![],
                                                succs: vec![],
                                                entry_stack: vec![],
                                                exit_stack: vec![],
                                            })
                                            .iter()
                                            .any(|e| ret_read(*e))
                                        }) || e2.term.as_ref().is_some_and(|t| {
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
                                            .iter()
                                            .any(|e| ret_read(*e))
                                        })
                                    }) || l
                                        .edge_assigns
                                        .values()
                                        .flatten()
                                        .any(|(_, v)| ret_read(*v));
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
                            if let Some(words) = input {
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
                Some(pc) => format!(" (in the helper `func_{:#x}`)", pc),
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
    accounting_findings(&facts, &mut findings);
    trust_findings(c, &facts, &mut findings);

    type_rules::findings(c, &c.types, names_for, &mut findings);

    crate::confirm::confirm(c, &mut findings);

    crate::invariant::findings(c, &c.types, &mut findings);

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
    let mut findings = merge_findings(findings);
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
    report.summary = summary;
    report
}

/// Does the internal function at `pc` (or anything it calls) divide?
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

/// Is `e` the result of a division, directly or through an internal call whose body divides?
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

/// Constant storage slots read anywhere in `e`.
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

/// Storage counters the contract caps: every write to the slot is a reset to a constant, a
/// decrement, or an increment by one guarded by `slot < C` (or `C > slot`) in the same
/// function. Maps the slot to the largest such `C`.
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

/// Every path from `start` ends in a revert or an invalid opcode.
fn always_reverts(l: &Lifted, start: usize) -> bool {
    let mut seen = HashSet::new();
    let mut stack = vec![start];
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 2000 {
            continue;
        }
        match &l.nodes[x].term {
            Term::Revert { .. } | Term::Invalid => {}
            Term::Return { .. }
            | Term::ReturnDyn { .. }
            | Term::Stop
            | Term::InternalReturn(_)
            | Term::SelfDestruct(_)
            | Term::Unresolved(_) => return false,
            _ => stack.extend(l.nodes[x].succs.iter().copied()),
        }
    }
    true
}

/// Conditions that must hold for execution to go on, with their polarity: inlined helpers'
/// guards (`Require`) hold as written; a branch (of the function or of an inlined body) whose
/// one side only reverts holds in the polarity of the other side.
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
            if always_reverts(g, *t) {
                out.push((*cond, false));
            } else if always_reverts(g, *f) {
                out.push((*cond, true));
            }
        }
    }
    out
}

/// How the guards along the path bound `amt` from below: `Some(true)` when a nonzero test is
/// the only lower bound (other direct comparisons are upper bounds or caller-supplied limits),
/// `Some(false)` when another lower bound exists, `None` when nothing tests it for zero.
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

/// The caller names the amount it receives and the contract computes the amount it gives.
/// Returns `(given amount, what the caller fixed, how the given amount is bounded)`.
///
/// Join shape: `transferFrom(caller, this, computed)` with a storage credit of a calldata word.
/// Exit shape: `transfer(to, calldata)` with a storage debit of a computed amount.
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

/// From `start`, every path halts normally (return/stop/internal return) without touching
/// state: no store, log, call, create or selfdestruct. `None` when a path reverts or the walk
/// runs away.
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

/// A msg.sender test whose failing side returns normally, with nothing changed, instead of
/// reverting (`if (!isOwner(msg.sender)) return;`, or a pre-0.4 modifier whose body is simply
/// skipped). Reported on the function that holds the test; helpers name their external callers.
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
            &HashMap::new(),
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

/// Rules about what a contract hands to the addresses it stores. A role that is also a callee
/// on a public path means the gate authenticates a contract this contract drives; a balance
/// taken from an account the caller does not own is a confiscation primitive; a pair
/// synchronised after state was moved prices that move in at once.
fn trust_findings(c: &Contract, facts: &[FnFacts], findings: &mut Vec<Finding>) {
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
            let forwarded = linked_forwards(c, sk, x, sc.selector, &mut linked_cache);
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

/// What a fetched dependency exposes, computed once per contract.
struct LinkedSummary {
    /// Functions anyone can call that make a state-changing call out.
    forwarders: Vec<String>,
    /// Selectors the contract calls on other contracts.
    selectors_called: Vec<String>,
}

/// When the contract was fetched with its dependencies, does the contract held in slot `slot`
/// expose a function anyone can call that calls out again (the loop that opens `gated`)? A
/// note for the finding when it does. `called` is the selector this contract sends it.
fn linked_forwards(
    c: &Contract,
    slot: U256,
    gated: &FnFacts,
    called: Option<u32>,
    cache: &mut HashMap<String, LinkedSummary>,
) -> Option<String> {
    let slot_hex = slot.to_hex_padded(32);
    let address = c
        .stored_targets
        .iter()
        .find(|(s, _)| s.eq_ignore_ascii_case(&slot_hex))
        .map(|(_, a)| a.to_ascii_lowercase())?;
    if !cache.contains_key(&address) {
        let lc = c.linked.iter().find(|lc| {
            lc.address
                .as_deref()
                .is_some_and(|a| a.eq_ignore_ascii_case(&address))
        })?;
        let report = analyze(lc);
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

/// Access control by intent: when several state-changing functions compare msg.sender against
/// the same slot, that is the contract's policy. A state-changing function without the check
/// that still does what the gated ones do (moves ether, self-destructs, delegatecalls, or writes
/// a configuration slot otherwise written only behind the check) is reported as a deviation.
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

/// Multi-step attacks assembled from per-function facts: a write that anyone can make, followed
/// by a function that trusts the written slot.
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

/// Functions that release value must agree on what the shared balance already owes. When one
/// function limits a transfer by `deposits - liabilities` over some storage, and another limits
/// a transfer over the same deposits while subtracting strictly more liability fields, the first
/// treats as free balance what the second counts as owed, so it can release more than the pool
/// holds. The rule is a bytecode fact: it compares the sets of storage fields the two limits add
/// and subtract, and names no contract, token or protocol.
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

/// 0..100: the worst finding sets the level (weighted by its confidence), the rest add a little.
/// A single confirmed critical scores higher than twenty informational notes.
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

/// What a compiler bug needs in the code to matter; what the bytecode shows decides whether the
/// bug is reported, and how loudly.
#[derive(Clone, Copy, PartialEq, Eq)]
enum BugNeeds {
    /// Transient storage opcodes: the bug is dropped when the bytecode has none.
    TransientStorage,
    /// Calldata copied to memory by an ordinary function: dropped when none is.
    CalldataCopy,
    /// A compiler setting or source construct the bytecode cannot show (`--via-ir`, inline
    /// assembly, optimizer internals): reported for information only.
    Unknowable,
}

/// A solc release range affected by a notable compiler bug.
struct CompilerBug {
    /// First affected version (inclusive).
    first: (u32, u32, u32),
    /// Last affected version (inclusive).
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

/// Rewrite storage/memory loads to version 0 so that structurally equal expressions compare
/// equal across store generations.
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

/// Fold findings that describe one defect several times: the same rule firing at several sites
/// of one function (a loop body with many calls), and the same site reached from several
/// external functions through a shared helper. The report then has one entry per defect.
fn merge_findings(findings: Vec<Finding>) -> Vec<Finding> {
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
                    && p.evidence == f.evidence
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

/// Render a report as a Markdown document: header, findings, then the contract-wide
/// sections (privileged functions, external calls, storage layout, events, selectors).
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
            out.push_str("- Confirmed: reached from a fresh state by an arbitrary caller\n");
            if let Some(w) = &f.witness {
                out.push_str(&format!("- Witness calldata: `{}`\n", w));
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
