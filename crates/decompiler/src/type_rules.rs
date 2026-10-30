//! Rules over recovered types and widths.
//!
//! The type solver ([`crate::types`]) knows the width, signedness and uses of every parameter,
//! helper argument, storage slot and packed field. These rules ask the questions that only make
//! sense with that knowledge: was a wide value narrowed without a check, is one value treated as
//! both signed and unsigned, is an account computed with arithmetic, is a hash used as a number,
//! does a narrow storage counter advance. Every rule is stated in widths and uses, never in
//! names, so it applies to any contract.

use crate::analyze::{fname, push, Confidence, Finding, Severity};
use crate::compiler::Kind;
use crate::decompile::{Contract, Function, StorageVar};
use crate::emit::{self, Names};
use crate::expr::{self, ExprId, Node};
use crate::function::{self, FnKind};
use crate::lift::{self, Stmt, Term};
use crate::opcode as op;
use crate::sigs;
use crate::types::{self, Loc, Ty, TypeEnv};
use crate::u256::U256;
use std::collections::HashSet;

/// Run every type-based rule.
pub fn findings(
    c: &Contract,
    env: &TypeEnv,
    names_for: &dyn Fn(&Function) -> Names,
    out: &mut Vec<Finding>,
) {
    unchecked_downcasts(c, env, names_for, out);
    sign_confusion(c, env, out);
    arithmetic_accounts(c, env, names_for, out);
    hashes_as_numbers(c, env, out);
    narrow_counters(c, env, out);
}

/// Where a narrowed value ends up.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Sink {
    /// Written to storage.
    Stored,
    /// Sent to another contract (call payload or value).
    Passed,
    /// Returned to the caller.
    Returned,
}

/// A `uint256` (or wider than the mask) value cut down to `N` bits with no range check first:
/// the high bits vanish instead of reverting. Solc >= 0.8 masks only for explicit `uintN(x)`
/// casts (declared `uintN` values are validated, not masked), so a bare mask on an arithmetic
/// result there is an unchecked downcast. The decoder and the cleanup of narrow types also mask
/// parameters, so a parameter counts only when the signature declares it wider or the code uses
/// it unmasked elsewhere.
fn unchecked_downcasts(
    c: &Contract,
    env: &TypeEnv,
    names_for: &dyn Fn(&Function) -> Names,
    out: &mut Vec<Finding>,
) {
    if c.compiler.kind == Kind::Vyper {
        return;
    }
    let checked = c.compiler.checked_arithmetic;
    for f in c.functions.iter().filter(|f| f.kind == FnKind::External) {
        let declared = declared_param_types(f);
        let mut seen_lines: HashSet<String> = HashSet::new();
        for (body, scope) in bodies(c, f) {
            let Some(l) = &body.lifted else { continue };
            let names = names_for(body);
            for nd in &l.nodes {
                let roots = lift::roots(nd);
                let packing = function::packing_masks(&roots);
                let sinks: Vec<(Sink, Vec<ExprId>, String)> = sink_statements(nd, &names);
                for (sink, exprs, line) in sinks {
                    for (x, bits) in masks_in(&exprs, &packing) {
                        let Some((conf, what)) =
                            downcast_source(x, bits, scope, f, body, env, &declared, checked)
                        else {
                            continue;
                        };
                        if !seen_lines.insert(line.clone()) {
                            continue;
                        }
                        let sev = match (sink, conf) {
                            (
                                Sink::Stored | Sink::Passed,
                                Confidence::High | Confidence::Medium,
                            ) => Severity::Medium,
                            _ => Severity::Low,
                        };
                        let fate = match sink {
                            Sink::Stored => "stored",
                            Sink::Passed => "passed to another contract",
                            Sink::Returned => "returned",
                        };
                        push(
                            out,
                            "unchecked-downcast",
                            "Value narrowed to a smaller width without a range check",
                            sev,
                            conf,
                            Some(f),
                            Some(nd.pc),
                            format!(
                                "`{}` cuts {} down to {} bits (`uint{}`) and the result is {}. Nothing checks that the value fits first, so a larger value loses its high bits silently instead of reverting.",
                                f.name, what, bits, bits, fate
                            ),
                            vec![line.clone()],
                            "Check the range before narrowing (`require(x <= type(uintN).max)` or a SafeCast), or keep the wider type.",
                        );
                    }
                }
            }
        }
    }
}

/// The function and the internal helpers it calls, each with the pc that scopes its values.
fn bodies<'a>(c: &'a Contract, f: &'a Function) -> Vec<(&'a Function, usize)> {
    let mut out = vec![(f, f.pc)];
    let mut seen: HashSet<usize> = HashSet::new();
    let mut stack: Vec<usize> = f.calls.clone();
    while let Some(pc) = stack.pop() {
        if !seen.insert(pc) {
            continue;
        }
        if let Some(h) = c
            .functions
            .iter()
            .find(|g| g.kind == FnKind::Internal && g.pc == pc)
        {
            out.push((h, h.pc));
            stack.extend(h.calls.iter().copied());
        }
    }
    out
}

/// The declared type of every calldata head word, from the signature, when it has only value
/// types (tuples and static arrays would need a layout).
fn declared_param_types(f: &Function) -> Option<Vec<String>> {
    let sig = f.signature.as_ref()?;
    let params = sigs::params_of(sig);
    if params.iter().any(|p| p.contains('(') || p.contains('[')) {
        return None;
    }
    Some(params)
}

/// Statements of a node whose expressions are a sink for a narrowed value, with the rendered
/// line used as evidence.
fn sink_statements(nd: &lift::LNode, names: &Names) -> Vec<(Sink, Vec<ExprId>, String)> {
    let mut out = Vec::new();
    for s in &nd.stmts {
        let sink = match s {
            Stmt::SStore { .. } => Sink::Stored,
            Stmt::Call { .. } => Sink::Passed,
            _ => continue,
        };
        let exprs = match s {
            Stmt::SStore { val, .. } => vec![*val],
            Stmt::Call {
                value,
                input,
                input_head,
                ..
            } => {
                let mut v: Vec<ExprId> = value.iter().copied().collect();
                v.extend(input_head.iter().copied());
                if let Some(w) = input {
                    v.extend(w.iter().copied());
                }
                v
            }
            _ => Vec::new(),
        };
        out.push((sink, exprs, emit::fmt_stmt(s, names)));
    }
    if let Term::Return {
        data: Some(words), ..
    } = &nd.term
    {
        let line = emit::fmt_term_halt(&nd.term, names).unwrap_or_default();
        out.push((Sink::Returned, words.clone(), line));
    }
    out
}

/// `(masked value, width)` for every `x & (2^N - 1)` under `roots` that is a narrowing (8 to
/// 248 bits, whole bytes) and not a packing piece.
fn masks_in(roots: &[ExprId], packing: &HashSet<ExprId>) -> Vec<(ExprId, u32)> {
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    let mut stack: Vec<ExprId> = roots.to_vec();
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > 20_000 {
            continue;
        }
        if let Node::Op(op::AND, v) = expr::node(x) {
            if !packing.contains(&x) {
                for (a, m) in [(v[0], v[1]), (v[1], v[0])] {
                    if let Some(m) = expr::as_const(m) {
                        let bits = m.bits();
                        if m.is_low_mask() && bits.is_multiple_of(8) && (8..256).contains(&bits) {
                            out.push((a, bits));
                        }
                    }
                }
            }
        }
        stack.extend(expr::children(x));
    }
    out
}

/// Is the value masked to `bits` wider than that, and unchecked? Returns how sure the rule is
/// and a description of the value.
#[allow(clippy::too_many_arguments)]
fn downcast_source(
    x: ExprId,
    bits: u32,
    scope: usize,
    f: &Function,
    body: &Function,
    env: &TypeEnv,
    declared: &Option<Vec<String>>,
    checked_arithmetic: bool,
) -> Option<(Confidence, String)> {
    let info = env.location(x, scope).and_then(|l| env.info(&l));
    if info.as_ref().is_some_and(|i| i.checked(bits)) {
        return None;
    }
    match expr::node(x) {
        Node::CallDataLoad(off) if body.pc == f.pc => {
            let word = emit::calldata_word_index(off)?;
            let name = f
                .params
                .iter()
                .find(|p| p.index == word)
                .map(|p| p.name.clone())
                .unwrap_or_else(|| format!("arg{}", word));
            if let Some(decl) = declared {
                let ty = decl.get(word as usize)?;
                return wider_than(ty, bits).then(|| {
                    (
                        Confidence::High,
                        format!("the `{}` parameter `{}`", ty, name),
                    )
                });
            }
            // No signature: the word is wide when the code also uses it unmasked.
            info?
                .arith
                .then(|| (Confidence::Medium, format!("the parameter `{}`", name)))
        }
        _ if checked_arithmetic && types::is_arithmetic(x) => {
            Some((Confidence::Low, "the result of arithmetic".to_string()))
        }
        _ => None,
    }
}

/// Does the declared ABI type hold more than `bits` bits?
fn wider_than(ty: &str, bits: u32) -> bool {
    match ty {
        "uint" | "int" | "uint256" | "int256" | "bytes32" => true,
        t => t
            .strip_prefix("uint")
            .or_else(|| t.strip_prefix("int"))
            .and_then(|n| n.parse::<u32>().ok())
            .is_some_and(|n| n > bits),
    }
}

/// Where a location lives, for the report: the function it belongs to (when any) and a phrase.
fn describe<'a>(c: &'a Contract, loc: &Loc) -> Option<(Option<&'a Function>, String)> {
    let func = |pc: usize| c.functions.iter().find(|f| f.pc == pc);
    let var = |root: U256| -> Option<&StorageVar> {
        c.storage
            .iter()
            .find(|v| U256::from_hex_str(&v.slot) == Some(root))
    };
    match loc {
        Loc::Param { scope, word } => {
            let f = func(*scope)?;
            let name = f
                .params
                .iter()
                .find(|p| p.index == *word)
                .map(|p| p.name.clone())
                .unwrap_or_else(|| format!("arg{}", word));
            Some((Some(f), format!("parameter `{}` of `{}`", name, fname(f))))
        }
        Loc::Arg { unit, slot } => {
            let f = func(*unit)?;
            let l = f.lifted.as_ref()?;
            let k = crate::ssa::arity(l);
            let i = k.checked_sub(1 + *slot as usize)?;
            Some((
                Some(f),
                format!("parameter `arg{}` of helper `{}`", i, f.name),
            ))
        }
        Loc::Ret { unit, .. } => {
            let f = func(*unit)?;
            Some((Some(f), format!("the result of helper `{}`", f.name)))
        }
        Loc::Var { scope, .. } => {
            let f = func(*scope)?;
            Some((Some(f), format!("a value computed in `{}`", fname(f))))
        }
        Loc::Slot(shape) | Loc::Key(shape) => {
            let v = var(shape.root)?;
            let what = if matches!(loc, Loc::Key(_)) {
                "the keys of"
            } else if shape.steps.is_empty() {
                "storage variable"
            } else {
                "the entries of"
            };
            Some((None, format!("{} `{}`", what, v.name)))
        }
        Loc::Field {
            shape, bit_offset, ..
        } => {
            let v = var(shape.root)?;
            let field = v
                .fields
                .iter()
                .find(|fl| fl.offset == bit_offset / 8)
                .map(|fl| fl.name.clone())
                .unwrap_or_else(|| v.name.clone());
            Some((None, format!("storage field `{}`", field)))
        }
    }
}

/// The same value compared as a signed number in one place and as an unsigned number in
/// another: one of the two comparisons is wrong for every value with the top bit set.
fn sign_confusion(c: &Contract, env: &TypeEnv, out: &mut Vec<Finding>) {
    let mut locs: Vec<&Loc> = env.locations().collect();
    locs.sort_by_key(|l| format!("{:?}", l));
    for loc in locs {
        // Helper arguments are left out: solc's ABI decoders compare calldata offsets with
        // `slt` and `lt` by design.
        if !matches!(loc, Loc::Param { .. } | Loc::Slot(_) | Loc::Field { .. }) {
            continue;
        }
        let Some(info) = env.info(loc) else { continue };
        if !(info.signed_cmp && info.unsigned_cmp) || info.ty == Ty::Bool {
            continue;
        }
        // A declared narrow signed integer (validated against its signed bounds) is bounds-checked
        // unsigned when it indexes an array: that is the compiler's doing, not confusion.
        if matches!(info.ty, Ty::Int(n) if n < 256) {
            continue;
        }
        let Some((f, what)) = describe(c, loc) else {
            continue;
        };
        push(
            out,
            "signed-unsigned-confusion",
            "Value compared both as signed and as unsigned",
            Severity::Low,
            Confidence::Low,
            f,
            f.map(|f| f.pc),
            format!(
                "{} is compared with signed comparisons (`slt`/`sgt`) in one place and with unsigned ones (`lt`/`gt`) in another. A value with its top bit set is negative to one check and huge to the other, so one of them accepts what the other was meant to reject.",
                capitalise(&what)
            ),
            Vec::new(),
            "Use one signedness for the value throughout; cast explicitly with a range check where the two meet.",
        );
    }
}

/// An account computed with arithmetic (`add`, `mul`, ...) rather than decoded, loaded or
/// derived from a hash: either a packing mistake or an address meant to be forged.
fn arithmetic_accounts(
    c: &Contract,
    env: &TypeEnv,
    names_for: &dyn Fn(&Function) -> Names,
    out: &mut Vec<Finding>,
) {
    let mut locs: Vec<&Loc> = env.locations().collect();
    locs.sort_by_key(|l| format!("{:?}", l));
    for loc in locs {
        // Helper results are left out: a result position that is not aligned with the caller's
        // view would blame the wrong value.
        if matches!(loc, Loc::Ret { .. } | Loc::Key(_)) {
            continue;
        }
        let Some(info) = env.info(loc) else { continue };
        if !(info.account && info.arith_def) || info.ty != Ty::Address {
            continue;
        }
        let arith: Vec<(ExprId, usize)> = env
            .defs(loc)
            .iter()
            .copied()
            .filter(|(e, _)| types::is_arithmetic(*e))
            .collect();
        let Some((e, scope)) = arith.first().copied() else {
            continue;
        };
        let Some((f, what)) = describe(c, loc) else {
            continue;
        };
        let evidence = c
            .functions
            .iter()
            .find(|g| g.pc == scope)
            .map(|g| vec![emit::fmt_expr(e, &names_for(g))])
            .unwrap_or_default();
        push(
            out,
            "address-from-arithmetic",
            "Account address computed with arithmetic",
            Severity::Low,
            Confidence::Low,
            f,
            f.map(|f| f.pc),
            format!(
                "{} is used as an account (call target, balance query or comparison with `msg.sender`) but receives the result of arithmetic. Addresses are decoded, loaded or derived from a hash; one built by adding or multiplying numbers is either a packing mistake or an address the code means to construct.",
                capitalise(&what)
            ),
            evidence,
            "Check how the address is formed; if it is `CREATE2` or packing arithmetic, make the derivation explicit and test it.",
        );
    }
}

/// A `bytes32` parameter or storage value (a hash) used in arithmetic. Reducing a hash to a
/// range (`% n`) is the weak-randomness rule's job; this covers hashes added to, subtracted
/// from or multiplied (commitment arithmetic, hand-rolled identifiers).
fn hashes_as_numbers(c: &Contract, env: &TypeEnv, out: &mut Vec<Finding>) {
    let mut locs: Vec<&Loc> = env.locations().collect();
    locs.sort_by_key(|l| format!("{:?}", l));
    for loc in locs {
        // Stack values and helper arguments are left out: `keccak256(slot) + i` is how the
        // compiler addresses array elements, and resize helpers take that pointer as a parameter.
        if !matches!(loc, Loc::Param { .. } | Loc::Slot(_) | Loc::Field { .. }) {
            continue;
        }
        let Some(info) = env.info(loc) else { continue };
        if info.ty != Ty::Bytes(32) || !info.arith {
            continue;
        }
        let Some((f, what)) = describe(c, loc) else {
            continue;
        };
        push(
            out,
            "hash-as-number",
            "Hash value used as a number",
            Severity::Info,
            Confidence::Low,
            f,
            f.map(|f| f.pc),
            format!(
                "{} holds a `bytes32` hash and is used in arithmetic. A hash is an identifier: arithmetic on it has no meaning, and a result that depends on it is as controllable as the hash's input.",
                capitalise(&what)
            ),
            Vec::new(),
            "Treat hashes as opaque identifiers; if a numeric reading is intended (proof-of-work targets), document and bound it.",
        );
    }
}

/// A storage counter or timestamp of 64 bits or less that advances: it wraps silently before
/// solc 0.8 and reverts for good after it.
fn narrow_counters(c: &Contract, env: &TypeEnv, out: &mut Vec<Finding>) {
    let mut locs: Vec<&Loc> = env.locations().collect();
    locs.sort_by_key(|l| format!("{:?}", l));
    for loc in locs {
        if !matches!(loc, Loc::Slot(_) | Loc::Field { .. }) {
            continue;
        }
        let Some(info) = env.info(loc) else { continue };
        let Ty::Uint(bits) = info.ty else { continue };
        if bits > 64 || !bits.is_multiple_of(8) {
            continue;
        }
        let defs = env.defs(loc);
        let increments = defs
            .iter()
            .any(|(e, scope)| increments_self(*e, *scope, loc, env));
        let clock = defs.iter().any(|(e, _)| mentions_clock(*e));
        if !increments && !(clock && bits <= 32) {
            continue;
        }
        let Some((_, what)) = describe(c, loc) else {
            continue;
        };
        let (title, desc, rec) = if increments {
            let fate = if c.compiler.checked_arithmetic {
                "the increment reverts for good once the maximum is reached (every path through it stops working)"
            } else {
                "the counter wraps to zero once the maximum is reached (an identifier is reused, a cap is reset)"
            };
            (
                "Narrow storage counter",
                format!(
                    "{} is a `uint{}` that the code increments. With {} values, {}.",
                    capitalise(&what),
                    bits,
                    max_of(bits),
                    fate
                ),
                "Use a wider type for anything that counts up over the contract's life, or make the cap explicit.",
            )
        } else {
            (
                "Narrow storage timestamp",
                format!(
                    "{} is a `uint{}` that receives `block.timestamp` or `block.number`. A {}-bit timestamp overflows {}.",
                    capitalise(&what),
                    bits,
                    bits,
                    if bits <= 32 {
                        "in 2106 (and a block number sooner)"
                    } else {
                        "far in the future"
                    }
                ),
                "Store timestamps in at least 40 bits (`uint40` lasts until the year 36812).",
            )
        };
        push(
            out,
            "narrow-counter",
            title,
            if increments {
                Severity::Low
            } else {
                Severity::Info
            },
            Confidence::Medium,
            None,
            None,
            desc,
            Vec::new(),
            rec,
        );
    }
}

/// `x + c` (possibly masked back to the field's width) where `x` reads `loc` itself.
fn increments_self(e: ExprId, scope: usize, loc: &Loc, env: &TypeEnv) -> bool {
    let e = match expr::node(e) {
        Node::Op(op::AND, v) if v.iter().any(|m| expr::as_const(*m).is_some()) => v
            .iter()
            .copied()
            .find(|m| expr::as_const(*m).is_none())
            .unwrap_or(e),
        _ => e,
    };
    let Node::Op(op::ADD, v) = expr::node(e) else {
        return false;
    };
    v.iter()
        .any(|x| env.location(*x, scope).as_ref() == Some(loc))
        && v.iter().any(|x| expr::as_const(*x).is_some())
}

/// Does the expression read the block clock?
fn mentions_clock(e: ExprId) -> bool {
    expr::contains(e, &|n| {
        matches!(n, Node::Env(op::TIMESTAMP | op::NUMBER, _))
    })
}

/// `2^bits` as prose.
fn max_of(bits: u32) -> String {
    match bits {
        8 => "256".into(),
        16 => "65,536".into(),
        32 => "about 4.3 billion".into(),
        64 => "about 1.8e19".into(),
        n => format!("2^{}", n),
    }
}

fn capitalise(s: &str) -> String {
    let mut c = s.chars();
    match c.next() {
        Some(first) => first.to_uppercase().collect::<String>() + c.as_str(),
        None => String::new(),
    }
}
