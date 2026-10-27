//! Security analysis over the lifted IR: a rule engine producing findings with evidence.

use crate::decompile::{self, Contract, Function};
use crate::emit::{self, Names};
use crate::expr::{self, ExprId, Node};
use crate::function::FnKind;
use crate::lift::{self, Lifted, Stmt, Term};
use crate::opcode as op;
use crate::sigs;
use crate::u256::U256;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    Critical,
    High,
    Medium,
    Low,
    Info,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
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
    /// Number of code sites folded into this finding (same rule, same function).
    #[serde(skip_serializing_if = "is_one")]
    pub sites: usize,
}

fn is_one(n: &usize) -> bool {
    *n == 1
}

#[derive(Clone, Debug, Serialize, Default)]
pub struct Report {
    pub contract_kind: Vec<String>,
    pub findings: Vec<Finding>,
    pub privileged_functions: Vec<String>,
    pub external_calls: Vec<String>,
    pub summary: BTreeMap<String, usize>,
    pub risk_score: u32,
}

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
    #[allow(dead_code)]
    callee: Option<usize>,
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
}

fn mentions(e: ExprId, pred: &dyn Fn(&Node) -> bool) -> bool {
    expr::contains(e, pred)
}
fn from_calldata(e: ExprId) -> bool {
    mentions(e, &|n| matches!(n, Node::CallDataLoad(_) | Node::CopiedWord(op::CALLDATACOPY, _, _)))
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

/// Loop membership of nodes (back edges via DFS).
fn loop_nodes(l: &Lifted) -> HashSet<usize> {
    let mut in_loop = HashSet::new();
    // Simple: node x is in a loop if x can reach itself.
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
    events_of_in(ctx, l, depth, in_loop_outer, None, None, &HashMap::new())
}

/// `subst` maps the helper's `Arg(i)` to the caller's actual values, so inlined statements read
/// in the caller's terms (`msg.sender` rather than `arg1`).
fn events_of_in(ctx: &Ctx, l: &Lifted, depth: usize, in_loop_outer: bool, outer_node: Option<usize>, callee: Option<usize>, subst: &HashMap<u32, ExprId>) -> Vec<Event> {
    let apply = |e: ExprId| -> ExprId {
        if subst.is_empty() {
            return e;
        }
        let mut memo = HashMap::new();
        expr::substitute(e, &|n| if let Node::Arg(i) = n { subst.get(i).copied() } else { None }, &mut memo)
    };
    let loops = loop_nodes(l);
    let mut out = Vec::new();
    // RPO order
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
    for nid in order {
        let nd = &l.nodes[nid];
        let in_loop = in_loop_outer || loops.contains(&nid);
        let anchor = outer_node.unwrap_or(nid);
        for s in &nd.stmts {
            let s = if subst.is_empty() { s.clone() } else { lift::map_stmt(s, &apply) };
            if let Stmt::Internal { callee: target, args, .. } = &s {
                if depth > 0 {
                    if let Some(f) = ctx.internals.get(target) {
                        if let Some(cl) = &f.lifted {
                            // Arg(i) (i < k) of the callee is argument k-1-i in natural order.
                            let k = cl.ret_slot.map(|k| k as usize).unwrap_or(usize::MAX);
                            let mut inner: HashMap<u32, ExprId> = HashMap::new();
                            if k != usize::MAX {
                                for (j, a) in args.iter().enumerate() {
                                    if j < k {
                                        inner.insert((k - 1 - j) as u32, *a);
                                    }
                                }
                            }
                            out.push(Event { node: anchor, pc: nd.pc, callee, stmt: Some(s.clone()), term: None, in_loop });
                            out.extend(events_of_in(ctx, cl, depth - 1, in_loop, Some(anchor), Some(*target), &inner));
                            continue;
                        }
                    }
                }
            }
            out.push(Event { node: anchor, pc: nd.pc, callee, stmt: Some(s), term: None, in_loop });
        }
        let term = if subst.is_empty() { nd.term.clone() } else { lift::map_term(&nd.term, &apply) };
        out.push(Event { node: anchor, pc: nd.pc, callee, stmt: None, term: Some(term), in_loop });
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

fn fname(f: &Function) -> String {
    match f.kind {
        FnKind::External => format!("{}{}", f.name, f.selector.as_ref().map(|s| format!(" [{}]", s)).unwrap_or_default()),
        _ => f.name.clone(),
    }
}

fn push(findings: &mut Vec<Finding>, id: &str, title: &str, sev: Severity, conf: Confidence, f: Option<&Function>, pc: Option<usize>, desc: String, evidence: Vec<String>, rec: &str) {
    findings.push(Finding { id: id.into(), title: title.into(), severity: sev, confidence: conf, function: f.map(fname), pc, description: desc, evidence, sites: 1, recommendation: rec.into() });
}

/// Is `cond` an authorization check on msg.sender: `msg.sender == <storage or constant address>`,
/// or a caller-keyed storage flag used directly as a boolean (`roles[msg.sender]`)?
pub fn is_auth_cond(cond: ExprId) -> bool {
    fn strip(e: ExprId) -> ExprId {
        match expr::node(e) {
            Node::Op(op::ISZERO, v) => strip(v[0]),
            Node::Op(op::AND, v) if expr::as_const(v[1]).map_or(false, |m| m.is_low_mask()) => strip(v[0]),
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
                    if expr::as_const(b2).map_or(false, |c| c.byte_len() >= 15) {
                        return true;
                    }
                    if matches!(expr::node(b2), Node::Env(op::ADDRESS, _) | Node::Env(op::ORIGIN, _)) {
                        return true;
                    }
                }
            }
            false
        }
        // roles[msg.sender] used as a boolean
        Node::SLoad(k, _, _) => from_caller(k),
        _ => false,
    }
}

/// Does the function check `msg.sender` (owner/role/constant) before `node`?
fn has_caller_check(l: &Lifted, before: Option<usize>) -> bool {
    for nd in &l.nodes {
        if let Term::Branch { cond, .. } = &nd.term {
            if is_auth_cond(*cond) && before.map_or(true, |b| reaches(l, nd.id, b)) {
                return true;
            }
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
    if has_caller_check(l, None) {
        return true;
    }
    transitive_callees(ctx, f).iter().any(|cf| cf.lifted.as_ref().map_or(false, |cl| has_caller_check(cl, None)))
}

/// Storage slots compared against msg.sender anywhere (owner/admin/role slots).
fn auth_slots(ctx: &Ctx) -> HashSet<ExprId> {
    let mut slots = HashSet::new();
    for f in &ctx.c.functions {
        let Some(l) = &f.lifted else { continue };
        for nd in &l.nodes {
            if let Term::Branch { cond, .. } = &nd.term {
                if is_auth_cond(*cond) {
                    collect_sload_keys(*cond, &mut slots);
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
            // Only constant slots / mapping roots, not keys that include msg.sender themselves
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

pub fn analyze(c: &Contract) -> Report {
    let internals: HashMap<usize, &Function> = c.functions.iter().filter(|f| f.kind == FnKind::Internal).map(|f| (f.pc, f)).collect();
    let version = c.info.metadata.as_ref().and_then(|m| if m.compiler == "solc" { m.version_tuple() } else { None });
    let ctx = Ctx { c, internals, version, vyper: c.language.starts_with("vyper") };
    let mut findings: Vec<Finding> = Vec::new();
    let mut report = Report::default();
    let names_for = |f: &Function| -> Names { decompile::make_names(f, &c.storage, ctx.vyper, &c.string_loaders) };

    // ---- contract kind ----
    let sels: HashSet<String> = c.functions.iter().filter_map(|f| f.signature.clone()).collect();
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

    // ---- per-function rules ----
    let auth = auth_slots(&ctx);
    let mut external_calls: BTreeSet<String> = BTreeSet::new();
    let mut privileged: Vec<String> = Vec::new();
    let mut fallback_delegatecall = false;
    let mut eip1967 = false;
    let mut delegatecall_targets_storage = false;

    for f in c.functions.iter().filter(|f| f.kind != FnKind::Internal && f.kind != FnKind::Orphan) {
        let Some(l) = &f.lifted else { continue };
        let names = names_for(f);
        let events = events_of(&ctx, l, 3, false);
        let caller_checked = any_caller_check(&ctx, f);
        if caller_checked && (f.effects.writes_storage || f.effects.calls || f.effects.selfdestruct || f.effects.creates) {
            privileged.push(fname(f));
        }
        // A function with no successful exit (simulation helpers such as Safe's
        // `simulateAndRevert`) leaves nothing behind: what it calls cannot change state.
        let always_reverts = !l.nodes.iter().any(|nd| matches!(nd.term, Term::Return { .. } | Term::ReturnDyn { .. } | Term::Stop | Term::SelfDestruct(_)));

        // Reentrancy guard: a constant slot that is tested before the call, set to a constant
        // before it and set to a constant again after it (`require(lock == 1); lock = 2; …;
        // lock = 1`, OpenZeppelin/Uniswap/Seaport style, storage or transient).
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
        let guarded = |i: usize| -> bool {
            let mut tested: HashSet<ExprId> = HashSet::new();
            let mut before: HashSet<ExprId> = HashSet::new();
            let mut after: HashSet<ExprId> = HashSet::new();
            for (j, e) in events.iter().enumerate() {
                if let Some(Stmt::SStore { key, val, .. }) = &e.stmt {
                    if expr::is_const(*key) {
                        // Entering may store a caller-dependent marker (`lockedBy = msg.sender`,
                        // `guard = accepting ? A : B`); leaving restores a constant.
                        if j < i {
                            before.insert(*key);
                        } else if j > i && expr::is_const(*val) {
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
            before.iter().any(|k| after.contains(k) && tested.contains(k))
        };

        // Walk events for call-related rules.
        for (i, ev) in events.iter().enumerate() {
            let Some(stmt) = &ev.stmt else { continue };
            // Inlined helper statements carry the caller's actual arguments (see `events_of_in`),
            // so they print with the caller's names.
            let names = &names;
            match stmt {
                Stmt::Call { kind, addr, value, input, in_off, in_len, out_len, result, gas, seq, .. } => {
                    let target = emit::fmt_expr(*addr, names);
                    let line = emit::fmt_stmt(stmt, names);
                    external_calls.insert(format!("{}: {}", fname(f), line.trim_end_matches(';')));
                    let value_nonzero = value.map_or(false, |v| expr::as_const(v) != Some(U256::ZERO));
                    let gas_stipend = expr::as_const(*gas).map_or(false, |g| g <= U256::from_u64(2300)) || matches!(expr::node(*gas), Node::Op(op::MUL, ref v) if expr::as_const(v[1]) == Some(U256::from_u64(2300)) || expr::as_const(v[0]) == Some(U256::from_u64(2300)));
                    let user_target = from_calldata(*addr) || from_caller(*addr);
                    let storage_target = from_storage(*addr);
                    // Known safe precompiles
                    let precompile = expr::as_const(*addr).map_or(false, |a| a <= U256::from_u64(10));

                    // Delegatecall
                    if *kind == op::DELEGATECALL || *kind == op::CALLCODE {
                        if f.kind == FnKind::Fallback {
                            fallback_delegatecall = true;
                        }
                        if storage_target {
                            delegatecall_targets_storage = true;
                        }
                        if from_calldata(*addr) && !caller_checked && always_reverts {
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

                    // Reentrancy: state write reachable after a non-static external call.
                    if *kind == op::CALL || *kind == op::CALLCODE {
                        let later_write = events[i + 1..].iter().any(|e2| matches!(&e2.stmt, Some(Stmt::SStore { .. })) && (reaches(l, ev.node, e2.node)));
                        if later_write && !precompile {
                            let (sev, conf, extra) = if guarded(i) {
                                (Severity::Info, Confidence::Medium, " A storage lock written before and after the call looks like a reentrancy guard, so this is reported for awareness only.")
                            } else if gas_stipend {
                                (Severity::Low, Confidence::Medium, " The call forwards only a 2300 gas stipend (`transfer`/`send`), which limits what a reentrant callee can do.")
                            } else if value_nonzero || user_target {
                                (Severity::High, Confidence::Medium, "")
                            } else {
                                (Severity::Medium, Confidence::Low, "")
                            };
                            push(&mut findings, "reentrancy", "State written after an external call (reentrancy)", sev, conf, Some(f), Some(ev.pc),
                                format!("`{}` performs an external call to `{}` and writes storage afterwards. A malicious callee can re-enter before the state update is applied (checks-effects-interactions violated).{}", f.name, target, extra),
                                vec![line.clone()], "Apply the checks-effects-interactions pattern (update state before calling out) or use a reentrancy guard.");
                        }
                        // Unchecked return value
                        let used = events.iter().any(|e2| {
                            e2.stmt.as_ref().map_or(false, |s2| match s2 {
                                Stmt::Drop(_) => false,
                                other => lift::node_exprs(&lift::LNode { id: 0, block: 0, pc: 0, stmts: vec![other.clone()], term: Term::Stop, preds: vec![], succs: vec![], entry_stack: vec![], exit_stack: vec![] }).iter().any(|e| mentions(*e, &|n| matches!(n, Node::CallResult(s) if *s == *seq)))
                            }) || e2.term.as_ref().map_or(false, |t| match t {
                                Term::Branch { cond, .. } => mentions(*cond, &|n| matches!(n, Node::CallResult(s) if *s == *seq)),
                                Term::Return { data: Some(d), .. } => d.iter().any(|e| mentions(*e, &|n| matches!(n, Node::CallResult(s) if *s == *seq))),
                                _ => false,
                            })
                        }) || l.edge_assigns.values().flatten().any(|(_, v)| mentions(*v, &|n| matches!(n, Node::CallResult(s) if *s == *seq)));
                        if !used && !precompile {
                            push(&mut findings, "unchecked-call", "Return value of external call ignored", if value_nonzero { Severity::Medium } else { Severity::Low }, Confidence::High, Some(f), Some(ev.pc),
                                format!("`{}` ignores the success flag of a low-level call to `{}`. If the call fails (reverting callee, out of gas, non-contract address) execution continues as if it succeeded{}.", f.name, target, if value_nonzero { ", and the ether is kept by this contract while state may assume it was sent" } else { "" }),
                                vec![line.clone()], "Check the returned boolean (`require(success)`) or use a high-level call that reverts on failure.");
                        }
                        // ERC20 transfer/transferFrom/approve whose returned bool is never read: a
                        // token that returns false instead of reverting is treated as a success.
                        if let Some(words) = input {
                            let in_len_c = expr::as_const(*in_len).and_then(|l| l.as_usize());
                            if let Some(sel) = words.first().and_then(|w0| emit::leading_selector(*w0, in_len_c)) {
                                if matches!(sel, 0xa9059cbb | 0x23b872dd | 0x095ea7b3) {
                                    let ret_read = |e: ExprId| mentions(e, &|n| matches!(n, Node::ReturnData(s, _) if *s == *seq));
                                    let out_zero = expr::as_const(*out_len) == Some(U256::ZERO);
                                    let decoded = events.iter().any(|e2| {
                                        e2.stmt.as_ref().map_or(false, |s2| lift::node_exprs(&lift::LNode { id: 0, block: 0, pc: 0, stmts: vec![s2.clone()], term: Term::Stop, preds: vec![], succs: vec![], entry_stack: vec![], exit_stack: vec![] }).iter().any(|e| ret_read(*e)))
                                            || e2.term.as_ref().map_or(false, |t| lift::node_exprs(&lift::LNode { id: 0, block: 0, pc: 0, stmts: vec![], term: t.clone(), preds: vec![], succs: vec![], entry_stack: vec![], exit_stack: vec![] }).iter().any(|e| ret_read(*e)))
                                    }) || l.edge_assigns.values().flatten().any(|(_, v)| ret_read(*v));
                                    if out_zero && !decoded && !matches!(expr::node(*addr), Node::Const(_)) {
                                        let name = sigs::function(sel).map(sigs::name_of).unwrap_or("transfer");
                                        push(&mut findings, "erc20-return-ignored", "ERC20 call result not checked", Severity::Low, Confidence::Medium, Some(f), Some(ev.pc),
                                            format!("`{}` calls `{}` on `{}` and never reads the returned boolean. Tokens that return `false` instead of reverting (and tokens that return nothing) are treated as if the transfer succeeded.", f.name, name, target),
                                            vec![line.clone()], "Use a SafeERC20-style wrapper: require the call to succeed and, when return data is present, require it to decode to true.");
                                    }
                                }
                            }
                        }
                        // Arbitrary call
                        // The payload counts as caller-controlled when its selector word comes from
                        // calldata, or when an undecoded payload starts with a CALLDATACOPY (the whole
                        // call data is the caller's). A fixed selector with calldata arguments
                        // (`token.transferFrom(from, to, amount)`) is an ordinary call.
                        let same_addr = |a: ExprId, b: ExprId| strip_versions(a, &mut HashMap::new()) == strip_versions(b, &mut HashMap::new());
                        let input_from_calldata = match input {
                            Some(w) => w.first().map_or(false, |w0| !expr::is_const(*w0) && from_calldata(*w0)),
                            None => events[..i].iter().any(|e| matches!(&e.stmt, Some(Stmt::Copy { kind: op::CALLDATACOPY, dest, .. }) if same_addr(*dest, *in_off))),
                        };
                        if from_calldata(*addr) && input_from_calldata && !caller_checked && !always_reverts && f.kind == FnKind::External {
                            push(&mut findings, "arbitrary-call", "Arbitrary external call with caller-controlled target and data", Severity::High, Confidence::Medium, Some(f), Some(ev.pc),
                                format!("`{}` calls `{}` with calldata-derived payload and no access control. If this contract holds token approvals or ether, anyone can drain them through it (e.g. calling `transferFrom` on an approved token).", f.name, target),
                                vec![line.clone()], "Restrict callable targets/selectors, or make sure the contract never holds funds or approvals.");
                        }
                        // Ether to caller without auth or balance accounting
                        if value_nonzero && from_caller(*addr) && !caller_checked && f.kind == FnKind::External {
                            let v = value.unwrap();
                            // Per-caller accounting before the transfer: a store to a caller-keyed
                            // slot, or a check against a caller-keyed balance (`balanceOf[msg.sender] >= wad`).
                            let caller_slot = |e: ExprId| mentions(e, &|n| matches!(n, Node::SLoad(k, ..) if from_caller(*k)));
                            let accounted = events[..i].iter().any(|e| match (&e.stmt, &e.term) {
                                (Some(Stmt::SStore { key, .. }), _) => from_caller(*key),
                                (Some(Stmt::Require { cond, .. }), _) => caller_slot(*cond),
                                (_, Some(Term::Branch { cond, .. })) => caller_slot(*cond),
                                _ => false,
                            });
                            if !from_caller(v) && !accounted {
                                push(&mut findings, "unprotected-ether-withdrawal", "Ether sent to msg.sender without per-caller accounting", Severity::Medium, Confidence::Low, Some(f), Some(ev.pc),
                                    format!("`{}` sends `{}` wei to msg.sender; the amount is not derived from a msg.sender-keyed balance and the function has no access control.", f.name, emit::fmt_expr(v, names)),
                                    vec![line.clone()], "Verify the amount is bounded by what the caller is owed.");
                            }
                        }
                        if ev.in_loop && !precompile {
                            push(&mut findings, "call-in-loop", "External call inside a loop", Severity::Low, Confidence::Medium, Some(f), Some(ev.pc),
                                format!("`{}` performs an external call to `{}` inside a loop; one failing or gas-hungry callee can block the whole iteration (denial of service).", f.name, target), vec![line.clone()], "Prefer pull-payments or bound the iteration.");
                        }
                        // ecrecover
                        if expr::as_const(*addr) == Some(U256::ONE) {
                            let zero_checked = l.nodes.iter().any(|nd| matches!(&nd.term, Term::Branch { cond, .. } if mentions(*cond, &|n| matches!(n, Node::ReturnData(s, _) if *s == *seq)) || mentions(*cond, &|n| matches!(n, Node::MLoad(..)))));
                            if !zero_checked {
                                push(&mut findings, "ecrecover-zero", "ecrecover result may be the zero address", Severity::Medium, Confidence::Low, Some(f), Some(ev.pc),
                                    format!("`{}` calls the ecrecover precompile; no comparison of the recovered address against zero was found. An invalid signature recovers to address(0), which may match an unset storage slot.", f.name), vec![line.clone()], "Require the recovered signer to be non-zero (or use OpenZeppelin ECDSA).");
                            }
                        }
                    }
                    let _ = result;
                }
                Stmt::Create { kind, .. } => {
                    let line = emit::fmt_stmt(stmt, names);
                    push(&mut findings, "contract-creation", if *kind == op::CREATE2 { "Deploys contracts with CREATE2" } else { "Deploys contracts with CREATE" }, Severity::Info, Confidence::High, Some(f), Some(ev.pc), format!("`{}` deploys a new contract.", f.name), vec![line], "Informational.");
                }
                _ => {}
            }
        }

        // Terminators: selfdestruct, unresolved
        for nd in &l.nodes {
            match &nd.term {
                Term::SelfDestruct(a) => {
                    let (sev, conf) = if caller_checked { (Severity::Medium, Confidence::Medium) } else { (Severity::Critical, Confidence::High) };
                    push(&mut findings, "selfdestruct", "Contract can self-destruct", sev, conf, Some(f), Some(nd.pc),
                        format!("`{}` can destroy the contract and send its balance to `{}`{}.", f.name, emit::fmt_expr(*a, &names), if caller_checked { " (behind a msg.sender check)" } else { " with no access control found" }),
                        vec![format!("selfdestruct({});", emit::fmt_expr(*a, &names))], "Remove selfdestruct or make sure the access control is correct (note: Cancun changed selfdestruct semantics).");
                }
                Term::Unresolved(t) => {
                    push(&mut findings, "unresolved-jump", "Jump target could not be resolved", Severity::Info, Confidence::High, Some(f), Some(nd.pc), format!("A jump to `{}` could not be resolved statically; code behind it is not shown.", emit::fmt_expr(*t, &names)), vec![], "Review the disassembly around this program counter.");
                }
                _ => {}
            }
        }

        // tx.origin authorization
        for nd in &l.nodes {
            if let Term::Branch { cond, .. } = &nd.term {
                if mentions(*cond, &|n| matches!(n, Node::Env(op::ORIGIN, _))) && matches!(expr::node(*cond), Node::Op(op::EQ, _) | Node::Op(op::ISZERO, _)) {
                    push(&mut findings, "tx-origin", "tx.origin used in a condition", Severity::Medium, Confidence::Medium, Some(f), Some(nd.pc),
                        format!("`{}` compares `tx.origin`. Using tx.origin for authorization lets a phishing contract act on behalf of the user.", f.name), vec![format!("if ({})", emit::fmt_expr(*cond, &names))], "Use msg.sender for authorization.");
                }
            }
        }

        // Weak randomness
        for nd in &l.nodes {
            for e in lift::node_exprs(nd) {
                if let Node::Op(op::MOD, v) = expr::node(e) {
                    let src = v[0];
                    let blocky = |n: &Node| matches!(n, Node::Env(o, _) if matches!(*o, op::TIMESTAMP | op::NUMBER | op::PREVRANDAO | op::COINBASE | op::GASLIMIT)) || matches!(n, Node::Op(op::BLOCKHASH, _));
                    if mentions(src, &blocky) && (matches!(expr::node(src), Node::Keccak(..)) || mentions(src, &|n| matches!(n, Node::Keccak(..) | Node::KeccakMem(..)))) {
                        push(&mut findings, "weak-randomness", "Block attributes used as a randomness source", Severity::Medium, Confidence::Medium, Some(f), Some(nd.pc),
                            format!("`{}` derives a value from `block.timestamp`/`block.number`/`prevrandao`/`blockhash` hashed and reduced modulo a range. Miners/validators and front-runners can predict or influence it.", f.name), vec![emit::fmt_expr(e, &names)], "Use a verifiable randomness source (VRF/commit-reveal).");
                        break;
                    }
                }
            }
        }

        // Unchecked arithmetic (pre-0.8 only)
        let pre08 = match ctx.version {
            Some((0, minor, _)) => minor < 8,
            None => !ctx.vyper && c.language.starts_with("solc"),
            _ => false,
        };
        if pre08 && f.kind == FnKind::External {
            let mut flagged = 0;
            let mut ev_lines = Vec::new();
            let callees = transitive_callees(&ctx, f);
            let mut bodies: Vec<(&Lifted, &Function)> = vec![(l, f)];
            for cf in &callees {
                if let Some(cl) = &cf.lifted {
                    bodies.push((cl, cf));
                }
            }
            let resolve = |pc: usize| -> Option<&Lifted> { ctx.internals.get(&pc).and_then(|cf| cf.lifted.as_ref()) };
            let mut memo = HashMap::new();
            for (body, body_fn) in &bodies {
                let body_names = names_for(body_fn);
                // Conditions visible from this body: its own plus those of the helpers it calls,
                // with the helpers' arguments replaced by the actual values (SafeMath-style checks
                // live in the callee and mention the caller's operands only after substitution).
                // Storage/memory versions are stripped so that a check made before an earlier
                // store still matches the operands of a later one.
                let conds: Vec<ExprId> = crate::function::exprs_with_callees(body, &resolve, 2).into_iter().filter(|e| expr::is_boolean(*e)).map(|e| strip_versions(e, &mut memo)).collect();
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
                                if (o == op::ADD || o == op::SUB || o == op::MUL) && !expr::is_const(v[0]) && !expr::is_const(v[1]) {
                                    // Is there a comparison involving this op or its operands (SafeMath-style check)?
                                    let (xn, v0, v1) = (strip_versions(x, &mut memo), strip_versions(v[0], &mut memo), strip_versions(v[1], &mut memo));
                                    let checked = conds.iter().any(|cnd| mentions(*cnd, &|n| matches!(n, Node::Op(_, w) if w.contains(&xn) || (w.contains(&v0) && w.contains(&v1)))));
                                    if !checked {
                                        flagged += 1;
                                        if ev_lines.len() < 3 {
                                            ev_lines.push(emit::fmt_stmt(s, &body_names));
                                        }
                                    }
                                }
                            }
                            // Addresses inside loads and hashes are pointer arithmetic, not values.
                            if !matches!(expr::node(x), Node::MLoad(..) | Node::SLoad(..) | Node::KeccakMem(..) | Node::CallDataLoad(_) | Node::CopiedWord(..) | Node::ReturnData(..)) {
                                stack.extend(expr::children(x));
                            }
                        }
                    }
                }
            }
            }
            if flagged > 0 {
                push(&mut findings, "unchecked-arithmetic", "Arithmetic without overflow check (compiler < 0.8)", Severity::Medium, Confidence::Low, Some(f), None,
                    format!("`{}` stores the result of {} arithmetic operation(s) with no visible bound check. Compilers before 0.8.0 wrap silently on overflow/underflow.", f.name, flagged), ev_lines, "Use SafeMath-style checks or compile with >= 0.8.0.");
            }
        }

        // Loops bounded by storage
        {
            let loops = loop_nodes(l);
            for nd in &l.nodes {
                if !loops.contains(&nd.id) {
                    continue;
                }
                if let Term::Branch { cond, .. } = &nd.term {
                    if from_storage(*cond) && matches!(expr::node(*cond), Node::Op(op::LT, _) | Node::Op(op::GT, _) | Node::Op(op::ISZERO, _) | Node::Op(op::EQ, _)) {
                        push(&mut findings, "storage-bounded-loop", "Loop bounded by a storage value", Severity::Low, Confidence::Medium, Some(f), Some(nd.pc),
                            format!("`{}` loops while `{}`; if the bound grows (e.g. an unbounded array) the function can exceed the block gas limit and become unusable.", f.name, emit::fmt_expr(*cond, &names)), vec![], "Bound the iteration or paginate.");
                        break;
                    }
                }
            }
        }

        // Privileged slot writable without access control.
        if f.kind == FnKind::External && !caller_checked {
            for nd in &l.nodes {
                for s in &nd.stmts {
                    if let Stmt::SStore { key, val, .. } = s {
                        if auth.contains(key) && expr::is_const(*key) && (from_calldata(*val) || from_caller(*val)) {
                            push(&mut findings, "unprotected-owner-write", "Authority slot writable without access control", Severity::Critical, Confidence::Medium, Some(f), Some(nd.pc),
                                format!("`{}` writes storage slot `{}`, which other functions compare against msg.sender for authorization, and the function itself has no msg.sender check. Anyone may be able to take over the privileged role.", f.name, emit::fmt_slot(*key, &names, false)),
                                vec![emit::fmt_stmt(s, &names)], "Gate the function with the same access control that protects the role.");
                        }
                    }
                }
            }
        }

        // msg.value reuse in delegatecall loops (multicall)
        if f.mutability == crate::function::Mutability::Payable {
            let dc_in_loop = events.iter().any(|e| e.in_loop && matches!(&e.stmt, Some(Stmt::Call { kind: op::DELEGATECALL, .. })));
            if dc_in_loop {
                push(&mut findings, "msg-value-multicall", "Payable function delegatecalls in a loop", Severity::Medium, Confidence::Low, Some(f), None,
                    format!("`{}` is payable and delegatecalls repeatedly (multicall pattern). Each delegated call sees the same `msg.value`, so ether can be counted several times if any callee relies on it.", f.name), vec![], "Reject msg.value in multicall, or make the inner functions non-payable.");
            }
        }

        // EIP-1967 slots
        for nd in &l.nodes {
            for e in lift::node_exprs(nd) {
                if mentions(e, &|n| matches!(n, Node::Const(c) if c.to_hex() == EIP1967_IMPL || c.to_hex() == EIP1967_ADMIN || c.to_hex() == EIP1967_BEACON)) {
                    eip1967 = true;
                }
            }
        }
    }

    // ---- contract-level findings ----
    if fallback_delegatecall {
        let kind = if eip1967 { "EIP-1967 upgradeable proxy" } else if c.info.runtime.len() < 100 { "EIP-1167 minimal proxy (clone)" } else if delegatecall_targets_storage { "Proxy (implementation address in storage)" } else { "Proxy" };
        kinds.push(kind.to_string());
        push(&mut findings, "proxy", "This contract is a proxy", Severity::Info, Confidence::High, None, None,
            format!("The fallback function delegatecalls to another contract ({}). The real logic lives in the implementation; decompile it as well (use `--follow-proxy` with an address).", kind), vec![], "Review the implementation and who can upgrade it.");
    }
    if sels.contains("upgradeTo(address)") || sels.contains("upgradeToAndCall(address,bytes)") {
        let upg: Vec<&Function> = c.functions.iter().filter(|f| f.signature.as_deref() == Some("upgradeTo(address)") || f.signature.as_deref() == Some("upgradeToAndCall(address,bytes)")).collect();
        for f in upg {
            if !any_caller_check(&ctx, f) {
                push(&mut findings, "unprotected-upgrade", "Upgrade function without access control", Severity::Critical, Confidence::Medium, Some(f), Some(f.pc), format!("`{}` changes the implementation and no msg.sender check was found.", f.name), vec![], "Restrict upgrades to the admin/owner.");
            }
        }
    }
    if let Some(v) = ctx.version {
        for (lo, hi, title, desc) in COMPILER_BUGS {
            if v >= *lo && v <= *hi {
                push(&mut findings, "compiler-bug", title, Severity::Low, Confidence::Low, None, None, format!("Compiled with solc {}.{}.{}. {}", v.0, v.1, v.2, desc), vec![], "Check whether the affected pattern is used; recompile with a fixed version.");
            }
        }
        if v.1 < 8 {
            push(&mut findings, "legacy-compiler", "Compiled with a pre-0.8 compiler", Severity::Info, Confidence::High, None, None, format!("solc {}.{}.{} has no built-in overflow checks and older ABI decoding (no validation of address/bool upper bits before 0.5).", v.0, v.1, v.2), vec![], "Prefer >= 0.8 for new deployments.");
        }
    } else if c.info.metadata.as_ref().map_or(false, |m| m.implies_pre_0_5_9()) {
        push(&mut findings, "legacy-compiler", "Compiled with a pre-0.8 compiler", Severity::Info, Confidence::High, None, None, "The metadata trailer carries a bzzr0 hash and no version field, which solc only emitted before 0.5.9. Such compilers have no built-in overflow checks and do not validate address/bool upper bits during ABI decoding (before 0.5).".into(), vec![], "Prefer >= 0.8 for new deployments.");
    } else if c.info.metadata.is_none() && !ctx.vyper {
        push(&mut findings, "no-metadata", "No compiler metadata", Severity::Info, Confidence::High, None, None, "The bytecode carries no CBOR metadata trailer (stripped, hand-written, or a very old compiler). Source verification is not possible by hash.".into(), vec![], "Informational.");
    }
    if c.stats.unresolved_jumps > 0 {
        push(&mut findings, "coverage", "Some code could not be reached by the analysis", Severity::Info, Confidence::High, None, None, format!("{} jump(s) have unresolved targets and {} of {} code blocks were covered. Findings may be incomplete.", c.stats.unresolved_jumps, c.stats.covered_blocks, c.stats.code_blocks), vec![], "Informational.");
    }
    // Unknown selectors
    let unknown: Vec<String> = c.functions.iter().filter(|f| f.kind == FnKind::External && f.signature.is_none()).map(|f| f.selector.clone().unwrap_or_default()).collect();
    if !unknown.is_empty() {
        push(&mut findings, "unknown-selectors", "Functions with unknown signatures", Severity::Info, Confidence::High, None, None, format!("{} external function selector(s) are not in the built-in dictionary: {}. Their names are guessed from behaviour only.", unknown.len(), unknown.join(", ")), vec![], "Look them up (4byte / openchain) or provide an ABI.");
    }
    if !c.strings.is_empty() {
        push(&mut findings, "revert-strings", "Revert reasons found in the bytecode", Severity::Info, Confidence::High, None, None, format!("{} string(s): {}", c.strings.len(), c.strings.iter().take(12).map(|s| format!("\"{}\"", s)).collect::<Vec<_>>().join(", ")), vec![], "Informational.");
    }

    // Deduplicate identical findings (same id, function, pc).
    let mut seen = HashSet::new();
    findings.retain(|f| seen.insert((f.id.clone(), f.function.clone(), f.pc, f.title.clone())));
    let mut findings = merge_findings(findings);
    findings.sort_by(|a, b| a.severity.cmp(&b.severity).then(a.function.cmp(&b.function)));

    let mut summary = BTreeMap::new();
    for f in &findings {
        *summary.entry(format!("{:?}", f.severity).to_lowercase()).or_insert(0) += 1;
    }
    let score: u32 = findings.iter().map(|f| match f.severity {
        Severity::Critical => 40,
        Severity::High => 20,
        Severity::Medium => 8,
        Severity::Low => 2,
        Severity::Info => 0,
    }).sum::<u32>().min(100);
    report.contract_kind = kinds;
    report.findings = findings;
    report.privileged_functions = privileged;
    report.external_calls = external_calls.into_iter().collect();
    report.summary = summary;
    report.risk_score = score;
    report
}

/// (from, to, title, description) — inclusive ranges of solc versions affected by notable bugs.
const COMPILER_BUGS: &[((u32, u32, u32), (u32, u32, u32), &str, &str)] = &[
    ((0, 8, 13), (0, 8, 16), "StorageWriteRemovalBeforeConditionalTermination", "The Yul optimizer could remove storage writes preceding a conditional `return`/`stop` in inline assembly (SOL-2022-6)."),
    ((0, 5, 8), (0, 8, 15), "HeadOverflowCalldataTuplesABIReencoding", "ABI re-encoding of calldata tuples ending in a statically-sized calldata array could corrupt data (SOL-2022-5)."),
    ((0, 8, 13), (0, 8, 14), "InlineAssemblyMemorySideEffects", "The optimizer could remove memory writes in inline assembly blocks whose results were only read by other assembly (SOL-2022-4)."),
    ((0, 8, 0), (0, 8, 2), "KeccakCaching", "The optimizer could reuse a cached keccak256 result for a different input length (SOL-2021-1)."),
    ((0, 6, 7), (0, 8, 20), "FullInlinerNonExpressionSplitArgumentEvaluationOrder", "With viaIR, the full inliner could evaluate function arguments in the wrong order (SOL-2023-2, only affects --via-ir builds)."),
    ((0, 7, 0), (0, 8, 25), "TransientStorageReentrancy", "Note: transient storage (0.8.24+) is not cleared across reentrant calls within a transaction; relevant only if TSTORE is used."),
];

/// Rewrite storage/memory loads to version 0 so that structurally equal expressions compare
/// equal across store generations.
fn strip_versions(e: ExprId, memo: &mut HashMap<ExprId, ExprId>) -> ExprId {
    expr::substitute(
        e,
        &|n| match n {
            Node::SLoad(a, t, v) if *v != 0 => Some(expr::intern(Node::SLoad(strip_versions(*a, &mut HashMap::new()), *t, 0))),
            Node::MLoad(a, v) if *v != 0 => Some(expr::intern(Node::MLoad(strip_versions(*a, &mut HashMap::new()), 0))),
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
    // Same rule and function.
    let mut by_fn: Vec<Finding> = Vec::new();
    for f in findings {
        let same = by_fn.iter_mut().find(|p| p.id == f.id && p.title == f.title && p.function.is_some() && p.function == f.function);
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
            f.description.push_str(&format!(" The pattern occurs at {} sites in this function.", f.sites));
        }
    }
    // Same rule, same code site (pc) and evidence, several functions: a shared helper.
    let mut out: Vec<Finding> = Vec::new();
    let mut extra: Vec<Vec<String>> = Vec::new();
    for f in by_fn {
        let same = f.pc.and_then(|_| out.iter().position(|p| p.id == f.id && p.title == f.title && p.pc == f.pc && p.evidence == f.evidence && p.function.is_some() && f.function.is_some()));
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
            f.description.push_str(&format!(" The same code is reached from {}.", others.iter().map(|o| format!("`{}`", o)).collect::<Vec<_>>().join(", ")));
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
    for sev in [Severity::Critical, Severity::High, Severity::Medium, Severity::Low, Severity::Info] {
        let n = r.findings.iter().filter(|f| f.severity == sev).count();
        if n > 0 {
            counts.push(format!("{} {}", n, format!("{:?}", sev).to_lowercase()));
        }
    }
    out.push_str(&format!("{}\n\n", if counts.is_empty() { "No findings.".to_string() } else { counts.join(", ") }));
    for (i, f) in r.findings.iter().enumerate() {
        out.push_str(&format!("### {}. [{}] {}\n\n", i + 1, format!("{:?}", f.severity).to_uppercase(), f.title));
        if let Some(func) = &f.function {
            out.push_str(&format!("- Function: `{}`", func));
            if let Some(pc) = f.pc {
                out.push_str(&format!(" at pc {:#x}", pc));
            }
            out.push('\n');
        }
        out.push_str(&format!("- Confidence: {:?}\n\n{}\n\n", f.confidence, f.description));
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
    if !r.external_calls.is_empty() {
        out.push_str("## External calls\n\n");
        for e in &r.external_calls {
            out.push_str(&format!("- `{}`\n", e));
        }
        out.push('\n');
    }
    if !c.storage.is_empty() {
        out.push_str("## Storage layout\n\n| slot | name | type | reads | writes |\n|---|---|---|---|---|\n");
        for s in &c.storage {
            if s.fields.is_empty() {
                out.push_str(&format!("| {} | {} | {} | {} | {} |\n", s.slot, s.name, s.ty.replace('|', "\\|"), s.reads, s.writes));
            } else {
                for fld in &s.fields {
                    out.push_str(&format!("| {} bytes {}..{} | {} | {} | {} | {} |\n", s.slot, fld.offset, fld.offset + fld.bits.div_ceil(8), fld.name, fld.ty, s.reads, s.writes));
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
