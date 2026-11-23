use crate::decompile::{Contract, Function};
use crate::function::{FnKind, Mutability};
use crate::{abi, exact, keccak};
use std::collections::BTreeSet;

// The oldest release whose assembly knows every instruction in use today.
const MODERN: &str = "^0.8.24";
const RENAMED: (u64, u64, u64) = (0, 8, 18);
const FEW: usize = 8;

#[derive(Clone, Debug, Default)]
pub struct Shape {
    pub own_version: bool,
    pub names: bool,
    pub events: bool,
    pub fallback_only: bool,
    pub few_arguments: bool,
    pub outside: BTreeSet<u32>,
}

fn version(c: &Contract) -> Option<(u64, u64, u64)> {
    let metadata = c.info.metadata.as_ref()?;
    let text = metadata.version.as_deref()?;
    let mut parts = text.split(['.', '+', '-']).map(str::parse::<u64>);
    let found = (
        parts.next()?.ok()?,
        parts.next()?.ok()?,
        parts.next()?.ok()?,
    );
    (metadata.compiler == "solc" && found >= (0, 8, 0)).then_some(found)
}

fn sized(ty: &str, prefix: &str, sizes: impl Fn(u32) -> bool) -> bool {
    let digits = ty.strip_prefix(prefix);
    digits.is_some_and(|d| d.parse::<u32>().is_ok_and(&sizes) && !d.starts_with('0'))
}

fn elementary(ty: &str) -> bool {
    let whole_bytes = |n: u32| n.is_multiple_of(8) && (8..=256).contains(&n);
    matches!(ty, "address" | "bool")
        || sized(ty, "uint", whole_bytes)
        || sized(ty, "int", whole_bytes)
        || sized(ty, "bytes", |n| (1..=32).contains(&n))
}

/* An ABI type as a function header writes it. A tuple needs a struct declared for it,
which this form does not make, so a function with one stays out of the headers. */
fn written(ty: &str, place: &str) -> Option<String> {
    let base = ty.split('[').next()?;
    let lists = &ty[base.len()..];
    let counted = lists
        .split(']')
        .all(|l| l.is_empty() || l == "[" || l[1..].parse::<u32>().is_ok());
    let dynamic = matches!(base, "bytes" | "string");
    if !(elementary(base) || dynamic) || !counted || !(lists.is_empty() || lists.ends_with(']')) {
        return None;
    }
    match dynamic || !lists.is_empty() {
        true => Some(format!("{ty} {place}")),
        false => Some(ty.to_string()),
    }
}

const RESERVED: [&str; 40] = [
    "address", "bool", "string", "bytes", "mapping", "function", "contract", "returns", "return",
    "memory", "storage", "calldata", "payable", "external", "internal", "public", "private",
    "view", "pure", "if", "else", "for", "while", "do", "break", "continue", "new", "delete",
    "this", "super", "type", "var", "true", "false", "event", "error", "emit", "struct", "enum",
    "assembly",
];

fn identifier(name: &str) -> bool {
    let mut letters = name.chars();
    let starts = letters
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_');
    starts
        && letters.all(|c| c.is_ascii_alphanumeric() || c == '_')
        && !RESERVED.contains(&name)
        && !elementary(name)
}

fn selector(f: &Function) -> Option<u32> {
    let text = f.selector.as_deref()?;
    u32::from_str_radix(text.trim_start_matches("0x"), 16).ok()
}

// A header is only written when its signature hashes to the selector the code answers.
fn header(f: &Function, shape: &Shape) -> Option<String> {
    let names = shape.names;
    let signature = f.signature.as_deref()?;
    let (name, rest) = signature.split_once('(')?;
    let types = abi::split_top(rest.strip_suffix(')')?);
    let hashed = Some(keccak::selector_u32(signature)) == selector(f);
    if f.kind != FnKind::External || !hashed || !identifier(name) || name == "_original" {
        return None;
    }
    let mut seen = BTreeSet::new();
    let own = |i: usize| f.params.get(i).map(|p| p.name.as_str());
    let all_named =
        (0..types.len()).all(|i| own(i).is_some_and(|n| identifier(n) && seen.insert(n)));
    let mut params = Vec::new();
    let mut slots = 0;
    for (i, ty) in types.iter().enumerate() {
        let ty = written(ty, "calldata")?;
        slots += 1 + usize::from(ty.ends_with("calldata"));
        params.push(match own(i).filter(|_| names && all_named) {
            Some(name) => format!("{ty} {name}"),
            None => ty,
        });
    }
    // The compiler keeps every decoded argument on its stack and reaches only sixteen
    // deep. A function with many arguments can make the whole file fail to build.
    if shape.few_arguments && slots > FEW {
        return None;
    }
    let results: Option<Vec<String>> = f.returns.iter().map(|t| written(t, "memory")).collect();
    let returns = match results.filter(|r| !r.is_empty()) {
        Some(r) => format!(" returns ({})", r.join(", ")),
        None => String::new(),
    };
    let payable = match f.mutability {
        Mutability::Payable => " payable",
        _ => "",
    };
    Some(format!(
        "function {name}({}) external{payable}{returns}",
        params.join(", ")
    ))
}

// One odd event would make the compiler refuse the file and every name in it.
fn declarable(event: &str) -> bool {
    let Some((name, rest)) = event.split_once('(') else {
        return false;
    };
    let Some(inner) = rest.strip_suffix(')') else {
        return false;
    };
    let types = abi::split_top(inner).into_iter();
    let mut plain = types.map(|t| t.trim().trim_end_matches(" indexed").trim());
    identifier(name) && plain.all(|t| written(t, "memory").is_some())
}

fn contract_name(c: &Contract) -> &str {
    let lines = c.source.lines();
    let declared = lines.filter_map(|l| l.strip_prefix("contract ")).next();
    let name = declared.and_then(|rest| rest.split_whitespace().next());
    name.filter(|n| identifier(n)).unwrap_or("Contract")
}

#[must_use]
pub fn file(c: &Contract, shape: &Shape) -> String {
    let own = version(c).filter(|_| shape.own_version);
    let pragma = match own {
        Some((a, b, patch)) => format!("{a}.{b}.{patch}"),
        None => MODERN.to_string(),
    };
    let mut out = format!("// SPDX-License-Identifier: UNLICENSED\npragma solidity {pragma};\n\n");
    out.push_str(&format!("contract {} {{\n", contract_name(c)));
    if shape.events {
        let events: BTreeSet<&String> = c.events.iter().filter(|e| declarable(e)).collect();
        for event in &events {
            out.push_str(&format!("    event {event};\n"));
        }
        if !events.is_empty() {
            out.push('\n');
        }
    }
    let mut written = BTreeSet::new();
    for f in &c.functions {
        let kept = selector(f).filter(|s| !shape.outside.contains(s) && !shape.fallback_only);
        let Some(head) = kept.and_then(|_| header(f, shape)) else {
            continue;
        };
        if written.insert(head.clone()) {
            out.push_str(&format!("    {head} {{\n        _original();\n    }}\n\n"));
        }
    }
    out.push_str("    fallback() external payable {\n        _original();\n    }\n\n");
    out.push_str("    function _original() private {\n        assembly {\n");
    let code = &c.info.runtime;
    let end = c.info.metadata.as_ref().map_or(code.len(), |m| m.offset);
    out.push_str(&exact::translate(
        code,
        end,
        own.is_none_or(|v| v >= RENAMED),
    ));
    out.push_str("        }\n    }\n}\n");
    out
}

#[cfg(feature = "rpc")]
pub struct Output {
    pub source: String,
    pub compiler: String,
    pub report: crate::check::Report,
    pub headers: usize,
    pub refused: Vec<String>,
}

#[cfg(feature = "rpc")]
fn attempt(c: &Contract, mut shape: Shape, runs: usize) -> Result<Output, String> {
    use crate::check;
    // A header makes the compiler decode the arguments its own way before the code
    // runs. Where the original decodes differently, the function goes back behind the
    // fallback, which adds nothing.
    for _ in 0..4 {
        let source = file(c, &shape);
        // The optimizer takes minutes on a block this long and then gives up on it.
        let built = crate::solc::compile_with(&source, false)?;
        let built = built.into_iter().next().ok_or("nothing was built")?;
        let mut named: Vec<(u32, String)> = built.signatures.clone().into_iter().collect();
        named.sort();
        let entries = check::entries(c, &named);
        let report = check::compare(&c.info.runtime, &built.runtime, &entries, runs);
        let headed = |text: &Option<String>| {
            let s = text
                .as_deref()
                .and_then(|t| u32::from_str_radix(&t[2..], 16).ok());
            s.filter(|s| built.signatures.contains_key(s))
        };
        let differing = report.functions.iter().filter(|f| f.differs.is_some());
        let moved: Vec<u32> = differing.filter_map(|f| headed(&f.selector)).collect();
        if moved.is_empty() {
            return Ok(Output {
                source,
                compiler: built.compiler,
                report,
                headers: built.signatures.len(),
                refused: Vec::new(),
            });
        }
        shape.outside.extend(moved);
    }
    Err("headers kept differing".to_string())
}

#[cfg(feature = "rpc")]
pub fn exact_file(c: &Contract, runs: usize) -> Result<Output, String> {
    let full = Shape {
        names: true,
        events: true,
        ..Shape::default()
    };
    let few = Shape {
        few_arguments: true,
        ..Shape::default()
    };
    let bare = Shape {
        fallback_only: true,
        ..Shape::default()
    };
    let details = [full, Shape::default(), few];
    let versions: &[bool] = match version(c) {
        Some(_) => &[true, false],
        None => &[false],
    };
    let mut shapes = Vec::new();
    for own_version in versions {
        shapes.extend(details.iter().map(|d| Shape {
            own_version: *own_version,
            ..d.clone()
        }));
    }
    shapes.push(bare);
    let mut refused = Vec::new();
    for shape in shapes {
        match attempt(c, shape, runs) {
            Ok(output) => return Ok(Output { refused, ..output }),
            Err(why) => refused.push(why),
        }
    }
    Err(refused.pop().unwrap_or_default())
}
