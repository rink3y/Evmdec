use crate::analyze::{display_name, push, Confidence, Finding, Severity};
use crate::compiler::Kind;
use crate::decompile::{Contract, Function, StorageVar};
use crate::emit::{self, Names};
use crate::expr::{self, ExprId, Node};
use crate::function::{self, FnKind};
use crate::lift::{self, Stmt, Term};
use crate::opcode as op;
use crate::sigs;
use crate::ssa;
use crate::types::{self, Loc, Ty, TypeEnv};
use crate::u256::U256;
use std::collections::HashSet;

const MAX_VISITED: usize = 20_000;

pub fn findings(
    c: &Contract,
    env: &TypeEnv,
    names_for: impl Fn(&Function) -> Names,
    out: &mut Vec<Finding>,
) {
    unchecked_downcasts(c, env, &names_for, out);
    sign_confusion(c, env, out);
    arithmetic_accounts(c, env, &names_for, out);
    hashes_as_numbers(c, env, out);
    narrow_counters(c, env, out);
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Sink {
    Stored,
    Passed,
    Returned,
}

impl Sink {
    fn fate(self) -> &'static str {
        match self {
            Sink::Stored => "stored",
            Sink::Passed => "passed to another contract",
            Sink::Returned => "returned",
        }
    }
}

struct SinkSite {
    sink: Sink,
    exprs: Vec<ExprId>,
    line: String,
}

struct Downcast<'a> {
    c: &'a Contract,
    env: &'a TypeEnv,
    f: &'a Function,
    body: &'a Function,
    declared: Option<&'a [String]>,
}

fn unchecked_downcasts(
    c: &Contract,
    env: &TypeEnv,
    names_for: impl Fn(&Function) -> Names,
    out: &mut Vec<Finding>,
) {
    if c.compiler.kind == Kind::Vyper {
        return;
    }
    for f in c.functions.iter().filter(|f| f.kind == FnKind::External) {
        let declared = declared_param_types(f);
        let mut reported: HashSet<String> = HashSet::new();
        for body in bodies(c, f) {
            let Some(l) = &body.lifted else { continue };
            let names = names_for(body);
            let cx = Downcast {
                c,
                env,
                f,
                body,
                declared: declared.as_deref(),
            };
            for nd in &l.nodes {
                let roots = lift::roots(nd);
                let packing = function::packing_masks(&roots);
                for site in sink_statements(nd, &names) {
                    for (x, bits) in masks_in(&site.exprs, &packing) {
                        if let Some((conf, what)) = cx.source(x, bits) {
                            if reported.insert(site.line.clone()) {
                                report_downcast(&cx, &site, nd.pc, bits, conf, &what, out);
                            }
                        }
                    }
                }
            }
        }
    }
}

fn report_downcast(
    cx: &Downcast,
    site: &SinkSite,
    pc: usize,
    bits: u32,
    conf: Confidence,
    what: &str,
    out: &mut Vec<Finding>,
) {
    let sev = match (site.sink, conf) {
        (Sink::Stored | Sink::Passed, Confidence::High | Confidence::Medium) => Severity::Medium,
        _ => Severity::Low,
    };
    push(
        out,
        "unchecked-downcast",
        "Value narrowed to a smaller width without a range check",
        sev,
        conf,
        Some(cx.f),
        Some(pc),
        format!(
            "`{}` cuts {} down to {} bits (`uint{}`) and the result is {}. Nothing checks that the value fits first, so a larger value loses its high bits silently instead of reverting.",
            cx.f.name,
            what,
            bits,
            bits,
            site.sink.fate()
        ),
        vec![site.line.clone()],
        "Check the range before narrowing (`require(x <= type(uintN).max)` or a SafeCast), or keep the wider type.",
    );
}

impl Downcast<'_> {
    fn source(&self, x: ExprId, bits: u32) -> Option<(Confidence, String)> {
        let info = self
            .env
            .location(x, self.body.pc)
            .and_then(|l| self.env.info(&l));
        if info.is_some_and(|i| i.checked(bits)) {
            return None;
        }
        let checked_arithmetic = self.c.compiler.checked_arithmetic;
        match expr::node(x) {
            Node::CallDataLoad(off) if self.body.pc == self.f.pc => {
                let word = emit::calldata_word_index(off)?;
                let name = param_name(self.f, word);
                if let Some(decl) = self.declared {
                    let ty = decl.get(word as usize)?;
                    return wider_than(ty, bits).then(|| {
                        (
                            Confidence::High,
                            format!("the `{}` parameter `{}`", ty, name),
                        )
                    });
                }
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
}

fn bodies<'a>(c: &'a Contract, f: &'a Function) -> Vec<&'a Function> {
    let mut out = vec![f];
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
            out.push(h);
            stack.extend(h.calls.iter().copied());
        }
    }
    out
}

fn declared_param_types(f: &Function) -> Option<Vec<String>> {
    let sig = f.signature.as_ref()?;
    let params = sigs::params_of(sig);
    if params.iter().any(|p| p.contains('(') || p.contains('[')) {
        return None;
    }
    Some(params)
}

fn param_name(f: &Function, word: u32) -> String {
    f.params
        .iter()
        .find(|p| p.index == word)
        .map(|p| p.name.clone())
        .unwrap_or_else(|| format!("arg{}", word))
}

fn sink_statements(nd: &lift::LNode, names: &Names) -> Vec<SinkSite> {
    let mut out = Vec::new();
    for s in &nd.stmts {
        let (sink, exprs) = match s {
            Stmt::SStore { val, .. } => (Sink::Stored, vec![*val]),
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
                (Sink::Passed, v)
            }
            _ => continue,
        };
        out.push(SinkSite {
            sink,
            exprs,
            line: emit::fmt_stmt(s, names),
        });
    }
    if let Term::Return {
        data: Some(words), ..
    } = &nd.term
    {
        out.push(SinkSite {
            sink: Sink::Returned,
            exprs: words.clone(),
            line: emit::fmt_term_halt(&nd.term, names).unwrap_or_default(),
        });
    }
    out
}

fn masks_in(roots: &[ExprId], packing: &HashSet<ExprId>) -> Vec<(ExprId, u32)> {
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    let mut stack: Vec<ExprId> = roots.to_vec();
    while let Some(x) = stack.pop() {
        if !seen.insert(x) || seen.len() > MAX_VISITED {
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

struct Place<'a> {
    function: Option<&'a Function>,
    phrase: String,
}

fn describe<'a>(c: &'a Contract, loc: &Loc) -> Option<Place<'a>> {
    let func = |pc: usize| c.functions.iter().find(|f| f.pc == pc);
    let var = |root: U256| -> Option<&StorageVar> {
        c.storage
            .iter()
            .find(|v| U256::from_hex_str(&v.slot) == Some(root))
    };
    let place = |function: Option<&'a Function>, phrase: String| Some(Place { function, phrase });
    match loc {
        Loc::Param { scope, word } => {
            let f = func(*scope)?;
            place(
                Some(f),
                format!(
                    "parameter `{}` of `{}`",
                    param_name(f, *word),
                    display_name(f)
                ),
            )
        }
        Loc::Arg { unit, slot } => {
            let f = func(*unit)?;
            let k = ssa::arity(f.lifted.as_ref()?);
            let i = k.checked_sub(1 + *slot as usize)?;
            place(
                Some(f),
                format!("parameter `arg{}` of helper `{}`", i, f.name),
            )
        }
        Loc::Ret { unit, .. } => {
            let f = func(*unit)?;
            place(Some(f), format!("the result of helper `{}`", f.name))
        }
        Loc::Var { scope, .. } => {
            let f = func(*scope)?;
            place(
                Some(f),
                format!("a value computed in `{}`", display_name(f)),
            )
        }
        Loc::Output { scope, .. } => {
            let f = func(*scope)?;
            place(
                Some(f),
                format!("a value another contract returned to `{}`", display_name(f)),
            )
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
            place(None, format!("{} `{}`", what, v.name))
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
            place(None, format!("storage field `{}`", field))
        }
    }
}

fn sign_confusion(c: &Contract, env: &TypeEnv, out: &mut Vec<Finding>) {
    for loc in env.locations() {
        if !matches!(loc, Loc::Param { .. } | Loc::Slot(_) | Loc::Field { .. }) {
            continue;
        }
        let Some(info) = env.info(loc) else { continue };
        if !(info.signed_cmp && info.unsigned_cmp) || info.ty == Ty::Bool {
            continue;
        }
        if matches!(info.ty, Ty::Int(n) if n < 256) {
            continue;
        }
        let Some(p) = describe(c, loc) else { continue };
        push(
            out,
            "signed-unsigned-confusion",
            "Value compared both as signed and as unsigned",
            Severity::Low,
            Confidence::Low,
            p.function,
            p.function.map(|f| f.pc),
            format!(
                "{} is compared with signed comparisons (`slt`/`sgt`) in one place and with unsigned ones (`lt`/`gt`) in another. A value with its top bit set is negative to one check and huge to the other, so one of them accepts what the other was meant to reject.",
                capitalise(&p.phrase)
            ),
            Vec::new(),
            "Use one signedness for the value throughout; cast explicitly with a range check where the two meet.",
        );
    }
}

fn arithmetic_accounts(
    c: &Contract,
    env: &TypeEnv,
    names_for: impl Fn(&Function) -> Names,
    out: &mut Vec<Finding>,
) {
    for loc in env.locations() {
        if matches!(loc, Loc::Ret { .. } | Loc::Key(_)) {
            continue;
        }
        let Some(info) = env.info(loc) else { continue };
        if !(info.account && info.arith_def) || info.ty != Ty::Address {
            continue;
        }
        let Some((e, scope)) = env
            .defs(loc)
            .iter()
            .copied()
            .find(|(e, _)| types::is_arithmetic(*e))
        else {
            continue;
        };
        let Some(p) = describe(c, loc) else { continue };
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
            p.function,
            p.function.map(|f| f.pc),
            format!(
                "{} is used as an account (call target, balance query or comparison with `msg.sender`) but receives the result of arithmetic. Addresses are decoded, loaded or derived from a hash; one built by adding or multiplying numbers is either a packing mistake or an address the code means to construct.",
                capitalise(&p.phrase)
            ),
            evidence,
            "Check how the address is formed; if it is `CREATE2` or packing arithmetic, make the derivation explicit and test it.",
        );
    }
}

fn hashes_as_numbers(c: &Contract, env: &TypeEnv, out: &mut Vec<Finding>) {
    for loc in env.locations() {
        if !matches!(loc, Loc::Param { .. } | Loc::Slot(_) | Loc::Field { .. }) {
            continue;
        }
        let Some(info) = env.info(loc) else { continue };
        if info.ty != Ty::Bytes(32) || !info.arith {
            continue;
        }
        let Some(p) = describe(c, loc) else { continue };
        push(
            out,
            "hash-as-number",
            "Hash value used as a number",
            Severity::Info,
            Confidence::Low,
            p.function,
            p.function.map(|f| f.pc),
            format!(
                "{} holds a `bytes32` hash and is used in arithmetic. A hash is an identifier: arithmetic on it has no meaning, and a result that depends on it is as controllable as the hash's input.",
                capitalise(&p.phrase)
            ),
            Vec::new(),
            "Treat hashes as opaque identifiers; if a numeric reading is intended (proof-of-work targets), document and bound it.",
        );
    }
}

struct CounterMessage {
    title: &'static str,
    description: String,
    recommendation: &'static str,
    severity: Severity,
}

fn narrow_counters(c: &Contract, env: &TypeEnv, out: &mut Vec<Finding>) {
    for loc in env.locations() {
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
        let Some(p) = describe(c, loc) else { continue };
        let m = counter_message(&p.phrase, bits, increments, c.compiler.checked_arithmetic);
        push(
            out,
            "narrow-counter",
            m.title,
            m.severity,
            Confidence::Medium,
            None,
            None,
            m.description,
            Vec::new(),
            m.recommendation,
        );
    }
}

fn timestamp_fate(bits: u32) -> String {
    let seconds = 1u64 << bits.min(32);
    match bits {
        32 => "overflows in 2106".to_string(),
        _ if seconds < 3600 => format!("wraps every {} minutes", seconds / 60),
        _ if seconds < 172_800 => format!("wraps every {} hours", seconds / 3600),
        _ => format!("wraps every {} days", seconds / 86_400),
    }
}

fn counter_message(
    phrase: &str,
    bits: u32,
    increments: bool,
    checked_arithmetic: bool,
) -> CounterMessage {
    if increments {
        let fate = if checked_arithmetic {
            "the increment reverts for good once the maximum is reached (every path through it stops working)"
        } else {
            "the counter wraps to zero once the maximum is reached (an identifier is reused, a cap is reset)"
        };
        CounterMessage {
            title: "Narrow storage counter",
            description: format!(
                "{} is a `uint{}` that the code increments. Its maximum is {}; {}.",
                capitalise(phrase),
                bits,
                max_value(bits),
                fate
            ),
            recommendation: "Use a wider type for anything that counts up over the contract's life, or make the cap explicit.",
            severity: Severity::Low,
        }
    } else {
        CounterMessage {
            title: "Narrow storage timestamp",
            description: format!(
                "{} is a `uint{}` that receives `block.timestamp` or `block.number`. A {}-bit timestamp {} (and a block number sooner).",
                capitalise(phrase),
                bits,
                bits,
                timestamp_fate(bits)
            ),
            recommendation: "Store timestamps in at least 40 bits (`uint40` lasts until the year 36812).",
            severity: Severity::Info,
        }
    }
}

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

fn mentions_clock(e: ExprId) -> bool {
    expr::contains(e, &|n| {
        matches!(n, Node::Env(op::TIMESTAMP | op::NUMBER, _))
    })
}

fn max_value(bits: u32) -> String {
    match bits {
        8 => "255".into(),
        16 => "65,535".into(),
        32 => "about 4.3 billion".into(),
        64 => "about 1.8e19".into(),
        n => format!("2^{} - 1", n),
    }
}

fn capitalise(s: &str) -> String {
    let mut c = s.chars();
    match c.next() {
        Some(first) => first.to_uppercase().collect::<String>() + c.as_str(),
        None => String::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn declared_width_comparison() {
        assert!(wider_than("uint256", 32));
        assert!(wider_than("bytes32", 160));
        assert!(wider_than("uint64", 32));
        assert!(!wider_than("uint32", 32));
        assert!(!wider_than("address", 160));
        assert!(!wider_than("bool", 8));
    }

    #[test]
    fn masks_are_found_and_packing_pieces_skipped() {
        let x = expr::var(1);
        let narrow = expr::op2(op::AND, x, expr::konst(expr::mask_bits(32)));
        let piece = expr::op2(op::AND, x, expr::konst(expr::mask_bits(64)));
        let packing: HashSet<ExprId> = [piece].into_iter().collect();
        let found = masks_in(&[narrow, piece], &packing);
        assert_eq!(found, vec![(x, 32)]);
    }

    #[test]
    fn prose_helpers() {
        assert_eq!(max_value(8), "255");
        assert_eq!(max_value(24), "2^24 - 1");
        assert_eq!(capitalise("storage field `x`"), "Storage field `x`");
        assert_eq!(capitalise(""), "");
    }
}
