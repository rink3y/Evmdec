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
fn header(f: &Function, shape: &Shape, whole: bool) -> Option<String> {
    let names = shape.names || whole;
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
    // A body reads its arguments by name, so one without all its names cannot be kept.
    if whole && !all_named {
        return None;
    }
    let mutability = match f.mutability {
        Mutability::Payable => " payable",
        Mutability::View if whole => " view",
        Mutability::Pure if whole => " pure",
        _ => "",
    };
    Some(format!(
        "function {name}({}) external{mutability}{returns}",
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

fn bytes_of(ty: &str) -> usize {
    let digits = |prefix: &str| {
        ty.strip_prefix(prefix)
            .and_then(|d| d.parse::<usize>().ok())
    };
    match ty {
        "address" => 20,
        "bool" => 1,
        _ if !elementary(ty) => 32,
        _ => digits("bytes").unwrap_or_else(|| digits("uint").or(digits("int")).unwrap_or(256) / 8),
    }
}

pub struct Layout {
    text: String,
    renamed: Vec<(String, String)>,
}

const WIDEST_GAP: u64 = 1 << 16;

/* Variables written down one after another so that each lands on the slot and the bytes
the code uses, for a contract's state and for the inside of a struct alike. The compiler
packs neighbours that fit into one slot, so a variable that sits alone in the original
gets padding before it wherever the compiler would pull it back. */
struct Packer {
    text: String,
    indent: &'static str,
    private: &'static str,
    next: u64,
    free: usize,
    pads: usize,
}

impl Packer {
    fn pad(&mut self, ty: &str) {
        self.pads += 1;
        let line = format!("{}{ty}{} _gap{};\n", self.indent, self.private, self.pads);
        self.text.push_str(&line);
    }

    fn reach(&mut self, at: u64, leading: usize, name: &str) -> Result<(), String> {
        if at < self.next || at - self.next > WIDEST_GAP {
            return Err(format!(
                "{name} is at slot {at:#x} after slot {:#x}",
                self.next
            ));
        }
        match at - self.next {
            0 if leading <= self.free => self.pad(&format!("bytes{}", self.free)),
            0 => {}
            1 => self.pad("uint256"),
            gap => self.pad(&format!("uint256[{gap}]")),
        }
        Ok(())
    }

    fn whole(&mut self, at: u64, ty: &str, name: &str, slots: u64) -> Result<(), String> {
        let size = bytes_of(ty);
        self.reach(at, size, name)?;
        self.text
            .push_str(&format!("{}{ty} {name};\n", self.indent));
        self.next = at + slots;
        self.free = 32 - size;
        Ok(())
    }

    fn fields(&mut self, at: u64, fields: &[(usize, usize, &str, String)]) -> Result<(), String> {
        let mut sorted: Vec<_> = fields.iter().collect();
        sorted.sort_by_key(|f| f.0);
        let first = sorted.first().map_or(32, |f| f.1);
        self.reach(at, first, sorted.first().map_or("", |f| f.3.as_str()))?;
        let mut cursor = 0usize;
        for (offset, size, ty, name) in sorted {
            if *offset < cursor || offset + size > 32 {
                return Err(format!("{name} does not fit its bytes of slot {at:#x}"));
            }
            if *offset > cursor {
                self.pad(&format!("bytes{}", offset - cursor));
            }
            self.text
                .push_str(&format!("{}{ty} {name};\n", self.indent));
            cursor = offset + size;
        }
        self.next = at + 1;
        self.free = 32 - cursor;
        Ok(())
    }
}

fn field_list<'a>(
    fields: &'a [crate::decompile::StorageField],
    name: &mut dyn FnMut(&str) -> Result<String, String>,
) -> Result<Vec<(usize, usize, &'a str, String)>, String> {
    let mut listed = Vec::new();
    for f in fields {
        let size = bytes_of(&f.ty);
        if f.bits as usize != 8 * size || !elementary(&f.ty) {
            return Err(format!("{} is {} bits of type {}", f.name, f.bits, f.ty));
        }
        listed.push((f.offset as usize, size, f.ty.as_str(), name(&f.name)?));
    }
    Ok(listed)
}

fn structure(v: &crate::decompile::StorageVar) -> Result<(String, u64), String> {
    let mut packer = Packer {
        text: String::new(),
        indent: "        ",
        private: "",
        next: 0,
        free: 0,
        pads: 0,
    };
    let mut used = BTreeSet::new();
    let mut name = |n: &str| match identifier(n) && used.insert(n.to_string()) {
        true => Ok(n.to_string()),
        false => Err(format!("{n} cannot be named in a struct")),
    };
    let mut members: Vec<_> = v.members.iter().collect();
    members.sort_by_key(|m| m.offset);
    for m in members {
        match m.fields.is_empty() {
            true => packer.whole(m.offset, &m.ty, &name(&m.name)?, 1)?,
            false => packer.fields(m.offset, &field_list(&m.fields, &mut name)?)?,
        }
    }
    let text = format!("    struct {} {{\n{}    }}\n", v.struct_name(), packer.text);
    Ok((text, packer.next))
}

fn place(
    packer: &mut Packer,
    structs: &mut String,
    at: u64,
    v: &crate::decompile::StorageVar,
    name: &mut dyn FnMut(&str) -> Result<String, String>,
) -> Result<(), String> {
    if !v.fields.is_empty() {
        return packer.fields(at, &field_list(&v.fields, name)?);
    }
    let mut slots = 1;
    let mut declared = String::new();
    if !v.members.is_empty() {
        let (text, span) = structure(v)?;
        declared = text;
        // Held directly, a struct takes all its slots. Behind a mapping or a list
        // it takes one.
        if !v.ty.contains("=>") && !v.ty.contains('[') {
            slots = span;
        }
    }
    if v.fixed_array {
        let (element, count) = v.ty.rsplit_once('[').unwrap_or((&v.ty, ""));
        let count = count.trim_end_matches(']').parse().ok();
        let whole_words = bytes_of(element) == 32 && v.members.is_empty();
        slots = count
            .filter(|_| whole_words)
            .ok_or_else(|| format!("{} is a fixed array of {}", v.name, v.ty))?;
    }
    packer.whole(at, &v.declared_type(), &name(&v.name)?, slots)?;
    structs.push_str(&declared);
    Ok(())
}

/* A variable this cannot express is left undeclared, and so is one at a slot too far to
count to. The next one is padded out to its own slot all the same. A function that
names an undeclared variable will not build, and stays in its exact form. */
fn layout(c: &Contract, taken: &BTreeSet<&str>) -> Layout {
    let slot = |text: &str| u64::from_str_radix(text.trim_start_matches("0x"), 16).ok();
    let placed = c.storage.iter().filter_map(|v| Some((slot(&v.slot)?, v)));
    let mut vars: Vec<(u64, &crate::decompile::StorageVar)> = placed.collect();
    vars.sort_by_key(|(at, _)| *at);
    let mut renamed = Vec::new();
    let mut used = BTreeSet::new();
    let mut name = |n: &str| {
        let fresh = match taken.contains(n) {
            true => format!("_{n}"),
            false => n.to_string(),
        };
        if !identifier(&fresh) || taken.contains(fresh.as_str()) || !used.insert(fresh.clone()) {
            return Err(format!("{n} cannot be named"));
        }
        if fresh != n {
            renamed.push((n.to_string(), fresh.clone()));
        }
        Ok(fresh)
    };
    let mut structs = String::new();
    let mut packer = Packer {
        text: String::new(),
        indent: "    ",
        private: " private",
        next: 0,
        free: 0,
        pads: 0,
    };
    let trace = std::env::var_os("EVMDEC_RAISE_TRACE").is_some();
    for (at, v) in vars {
        let before = packer.text.len();
        if let Err(why) = place(&mut packer, &mut structs, at, v, &mut name) {
            packer.text.truncate(before);
            if trace {
                eprintln!("left undeclared: {why}");
            }
        }
    }
    if !structs.is_empty() {
        structs.push('\n');
    }
    Layout {
        text: format!("{structs}{}", packer.text),
        renamed,
    }
}

fn renamed(text: &str, names: &[(String, String)]) -> String {
    let word = |c: char| c.is_ascii_alphanumeric() || c == '_';
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    let mut before = ' ';
    while let Some(c) = rest.chars().next() {
        if c == '"' {
            let end = rest[1..].find('"').map_or(rest.len(), |i| i + 2);
            out.push_str(&rest[..end]);
            rest = &rest[end..];
            before = '"';
            continue;
        }
        if !(c.is_ascii_alphabetic() || c == '_') || word(before) || before == '.' {
            out.push(c);
            before = c;
            rest = &rest[c.len_utf8()..];
            continue;
        }
        let end = rest.find(|c: char| !word(c)).unwrap_or(rest.len());
        let (name, after) = rest.split_at(end);
        let called = after.trim_start().starts_with('(');
        let new = names.iter().find(|(old, _)| old == name && !called);
        out.push_str(new.map_or(name, |(_, new)| new));
        before = 'a';
        rest = after;
    }
    out
}

pub struct Plain<'a> {
    functions: &'a BTreeSet<usize>,
    layout: &'a Layout,
}

fn body(c: &Contract, f: &Function, plain: &Plain<'_>) -> String {
    let payable = f.kind != FnKind::External || f.mutability == Mutability::Payable;
    // The compiler makes this test itself for a function that takes no ether, and
    // does not let such a function read the value.
    let own = |l: &&str| payable || l.trim() != "require(msg.value == 0);";
    let mut lines: Vec<String> = f.code.lines().filter(own).map(one_value).collect();
    if lines.last().is_some_and(|l| l == "        return;") {
        lines.pop();
    }
    let text = renamed(&lines.join("\n"), &plain.layout.renamed);
    let text = checksummed(&text);
    let text = match version(c).is_some_and(|v| v < RENAMED) {
        true => text.replace("block.prevrandao", "block.difficulty"),
        false => text,
    };
    let text = format!("{}{text}", declarations(f, &text));
    // Arithmetic before 0.8 wraps. In a current file only an unchecked block does.
    let wraps = ["+", "*", " - ", "-=", "(-"]
        .iter()
        .any(|sign| text.contains(sign));
    if version(c).is_some() || !wraps {
        return format!("{text}\n");
    }
    let inner: String = text.lines().map(|l| format!("    {l}\n")).collect();
    format!("        unchecked {{\n{inner}        }}\n")
}

// The compiler takes forty hex digits for an address and refuses one whose letters are
// not in the case the address's own hash gives them.
fn checksummed(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(at) = rest.find("0x") {
        let digits = &rest[at + 2..];
        let end = digits
            .find(|c: char| !c.is_ascii_hexdigit())
            .unwrap_or(digits.len());
        let joined = rest[..at]
            .chars()
            .next_back()
            .is_some_and(|c| c.is_ascii_alphanumeric());
        out.push_str(&rest[..at + 2]);
        if end == 40 && !joined {
            let lower = digits[..40].to_ascii_lowercase();
            let hash = keccak::keccak256(lower.as_bytes());
            for (i, c) in lower.chars().enumerate() {
                let nibble = (hash[i / 2] >> (4 * (1 - i % 2))) & 0xf;
                out.push(if nibble >= 8 {
                    c.to_ascii_uppercase()
                } else {
                    c
                });
            }
        } else {
            out.push_str(&digits[..end]);
        }
        rest = &digits[end..];
    }
    out.push_str(rest);
    out
}

fn one_value(line: &str) -> String {
    let code = line.trim_start();
    let inner = code
        .strip_prefix("return (")
        .and_then(|r| r.strip_suffix(");"));
    let Some(inner) = inner else {
        return line.to_string();
    };
    let mut depth = 0i32;
    for c in inner.chars() {
        depth += i32::from(c == '(') - i32::from(c == ')');
        // A comma at the top makes it a list, and a closed bracket means the outer
        // pair was two pairs, as in `(a) + (b)`.
        if depth < 0 || (depth == 0 && c == ',') {
            return line.to_string();
        }
    }
    let indent = &line[..line.len() - code.len()];
    format!("{indent}return {inner};")
}

/* The printer assigns a value that two paths give without declaring it, as the place
of the first assignment is not always in scope for the last use. Every such name is
declared once at the top. */
fn declarations(f: &Function, text: &str) -> String {
    let word = |c: char| c.is_ascii_alphanumeric() || c == '_';
    let words: BTreeSet<&str> = text.split(|c: char| !word(c)).collect();
    let numbered = |w: &str, prefix: &str| {
        let rest = w.strip_prefix(prefix);
        rest.is_some_and(|r| !r.is_empty() && r.chars().all(|c| c.is_ascii_digit() || c == '_'))
    };
    let mut out = String::new();
    for (name, ty) in f
        .locals
        .iter()
        .filter(|(name, _)| words.contains(name.as_str()))
    {
        out.push_str(&format!("        {ty} {name};\n"));
    }
    for name in words.iter().filter(|w| numbered(w, "ret_")) {
        out.push_str(&format!("        uint256 {name};\n"));
    }
    out
}

fn helpers(c: &Contract, plain: &BTreeSet<usize>) -> BTreeSet<usize> {
    let at = |pc: usize| {
        c.functions
            .iter()
            .position(|f| f.pc == pc && f.kind == FnKind::Internal)
    };
    let mut found = BTreeSet::new();
    let external = |i: &&usize| c.functions[**i].kind == FnKind::External;
    let mut work: Vec<usize> = plain.iter().filter(external).copied().collect();
    while let Some(i) = work.pop() {
        for callee in c.functions[i].calls.iter().filter_map(|pc| at(*pc)) {
            if plain.contains(&callee) && found.insert(callee) {
                work.push(callee);
            }
        }
    }
    found
}

pub struct Draft {
    pub text: String,
    spans: Vec<(usize, usize, usize)>,
}

fn compose(c: &Contract, shape: &Shape, plain: Option<&Plain<'_>>) -> Draft {
    let own = version(c).filter(|_| shape.own_version);
    let pragma = match own {
        Some((a, b, patch)) => format!("{a}.{b}.{patch}"),
        None => MODERN.to_string(),
    };
    let mut out = format!("// SPDX-License-Identifier: UNLICENSED\npragma solidity {pragma};\n\n");
    let mut spans = Vec::new();
    out.push_str(&format!("contract {} {{\n", contract_name(c)));
    if let Some(plain) = plain.filter(|p| !p.layout.text.is_empty()) {
        out.push_str(&plain.layout.text);
        out.push('\n');
    }
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
    for (i, f) in c.functions.iter().enumerate() {
        let whole = plain.filter(|p| p.functions.contains(&i) && f.kind == FnKind::External);
        if let Some((plain, head)) = whole.and_then(|p| Some((p, header(f, shape, true)?))) {
            if written.insert(head.clone()) {
                let start = out.len();
                out.push_str(&format!("    {head} {{\n{}    }}\n\n", body(c, f, plain)));
                spans.push((start, out.len(), i));
            }
            continue;
        }
        let kept = selector(f).filter(|s| !shape.outside.contains(s) && !shape.fallback_only);
        let Some(head) = kept.and_then(|_| header(f, shape, false)) else {
            continue;
        };
        if written.insert(head.clone()) {
            out.push_str(&format!("    {head} {{\n        _original();\n    }}\n\n"));
        }
    }
    out.push_str("    fallback() external payable {\n        _original();\n    }\n\n");
    if let Some(plain) = plain {
        for i in helpers(c, plain.functions) {
            let f = &c.functions[i];
            let start = out.len();
            let head = crate::decompile::fmt_function_header(f);
            out.push_str(&format!("{head}{}    }}\n\n", body(c, f, plain)));
            spans.push((start, out.len(), i));
        }
    }
    out.push_str("    function _original() private {\n        assembly {\n");
    let code = &c.info.runtime;
    let end = c.info.metadata.as_ref().map_or(code.len(), |m| m.offset);
    out.push_str(&exact::translate(
        code,
        end,
        own.is_none_or(|v| v >= RENAMED),
    ));
    out.push_str("        }\n    }\n}\n");
    Draft { text: out, spans }
}

#[must_use]
pub fn file(c: &Contract, shape: &Shape) -> String {
    compose(c, shape, None).text
}

#[cfg(feature = "rpc")]
pub struct Output {
    pub source: String,
    pub compiler: String,
    pub report: crate::check::Report,
    pub headers: usize,
    pub refused: Vec<String>,
    pub plain: Vec<String>,
    pub shape: Shape,
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
        let built = crate::solc::compile_with(&source, false).map_err(|r| r.message)?;
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
                plain: Vec::new(),
                shape,
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

/* The exact file with every function the printer's own text can stand in for written
out as plain Solidity. A function is written out only while the file still builds and
the function still does what the bytecode does. Whatever fails either test goes back
to the exact translation, and so does everything that calls it. */
#[cfg(feature = "rpc")]
pub fn raised_file(c: &Contract, runs: usize) -> Result<Output, String> {
    use crate::check;
    let floor = exact_file(c, runs)?;
    let names = c.functions.iter().map(|f| f.name.as_str());
    let events = c.events.iter().filter_map(|e| e.split('(').next());
    let taken: BTreeSet<&str> = names.chain(events).chain(["_original"]).collect();
    let trace = std::env::var_os("EVMDEC_RAISE_TRACE").is_some();
    let layout = layout(c, &taken);
    let mut shape = floor.shape.clone();
    let printable =
        |f: &&Function| !f.inlined && matches!(f.kind, FnKind::External | FnKind::Internal);
    let all = c.functions.iter().enumerate();
    let mut plain: BTreeSet<usize> = all.filter(|(_, f)| printable(f)).map(|(i, _)| i).collect();
    let callers = |of: usize| {
        let pc = c.functions[of].pc;
        let calling = c
            .functions
            .iter()
            .enumerate()
            .filter(move |(_, f)| f.calls.contains(&pc));
        calling.map(|(i, _)| i)
    };
    let mut depth = runs;
    for _ in 0..32 {
        let written = Plain {
            functions: &plain,
            layout: &layout,
        };
        let draft = compose(c, &shape, Some(&written));
        if draft.spans.is_empty() {
            break;
        }
        let mut failed: Vec<usize> = Vec::new();
        let report = match crate::solc::compile_with(&draft.text, false) {
            Err(refusal) => {
                let within = |at: &usize| {
                    let span = draft
                        .spans
                        .iter()
                        .find(|(from, to, _)| from <= at && at < to);
                    span.map(|(_, _, i)| *i)
                };
                failed.extend(refusal.places.iter().filter_map(within));
                if trace {
                    let named: Vec<&str> = failed
                        .iter()
                        .map(|i| c.functions[*i].name.as_str())
                        .collect();
                    eprintln!("refused in {named:?}: {}", refusal.message);
                }
                // An error outside every function is in what they all share.
                if failed.is_empty() {
                    break;
                }
                None
            }
            Ok(built) => {
                let built = built.into_iter().next().ok_or("nothing was built")?;
                let mut named: Vec<(u32, String)> = built.signatures.clone().into_iter().collect();
                named.sort();
                let whole: BTreeSet<u32> = draft
                    .spans
                    .iter()
                    .filter_map(|(_, _, i)| selector(&c.functions[*i]))
                    .collect();
                let mut entries = check::entries(c, &named);
                for e in &mut entries {
                    e.loose =
                        version(c).is_none() && e.selector.is_some_and(|s| whole.contains(&s));
                }
                let report = check::compare(&c.info.runtime, &built.runtime, &entries, depth);
                let chosen = |text: &Option<String>| {
                    text.as_deref()
                        .and_then(|t| u32::from_str_radix(&t[2..], 16).ok())
                };
                for differing in report.functions.iter().filter(|f| f.differs.is_some()) {
                    let Some(s) = chosen(&differing.selector) else {
                        continue;
                    };
                    let index = c.functions.iter().position(|f| selector(f) == Some(s));
                    if trace {
                        let why = differing.differs.as_deref().unwrap_or("");
                        eprintln!("{} differs: {why}", differing.signature);
                    }
                    match index.filter(|i| plain.contains(i)) {
                        Some(i) => failed.push(i),
                        None if built.signatures.contains_key(&s) => {
                            shape.outside.insert(s);
                            failed.push(usize::MAX);
                        }
                        None => {}
                    }
                }
                // A file that came through the quick comparison is put through a longer
                // one before it is given out.
                if failed.is_empty() && depth == runs {
                    depth = 4 * runs;
                    continue;
                }
                if failed.is_empty() {
                    let externals = draft.spans.iter().map(|(_, _, i)| &c.functions[*i]);
                    let plain = externals.filter(|f| f.kind == FnKind::External);
                    return Ok(Output {
                        source: draft.text,
                        compiler: built.compiler,
                        report,
                        headers: built.signatures.len(),
                        refused: floor.refused,
                        plain: plain.map(|f| f.name.clone()).collect(),
                        shape,
                    });
                }
                Some(report)
            }
        };
        drop(report);
        while let Some(i) = failed.pop() {
            if i != usize::MAX && plain.remove(&i) {
                failed.extend(callers(i));
            }
        }
    }
    Ok(floor)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_variable_is_renamed_and_a_call_or_a_member_of_that_name_is_not() {
        let names = [("balanceOf".to_string(), "_balanceOf".to_string())];
        let text = "balanceOf[a] = token.balanceOf(b) + balanceOf (c); require(x, \"balanceOf\");";
        let want = "_balanceOf[a] = token.balanceOf(b) + balanceOf (c); require(x, \"balanceOf\");";
        assert_eq!(renamed(text, &names), want);
    }

    #[test]
    fn an_address_gets_the_case_its_hash_gives() {
        let lower = "x = 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 + 0xff;";
        let mixed = "x = 0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2 + 0xff;";
        assert_eq!(checksummed(lower), mixed);
    }

    #[test]
    fn brackets_come_off_one_returned_value_only() {
        assert_eq!(one_value("    return (a[b(c)]);"), "    return a[b(c)];");
        assert_eq!(one_value("    return (a, b);"), "    return (a, b);");
        assert_eq!(one_value("    return (a) + (b);"), "    return (a) + (b);");
    }
}
