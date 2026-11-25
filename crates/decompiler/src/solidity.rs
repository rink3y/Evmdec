use crate::decompile::{Contract, Function};
use crate::function::{FnKind, Mutability};
use crate::{abi, exact, keccak};
use std::collections::{BTreeMap, BTreeSet};

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

/* An event as a file declares it. One known only by its first topic cannot be declared
by a name that hashes to the topic. It is declared anonymous with the topic as its first
indexed value and every other value a word, which is how the printer emits it. */
fn declared(event: &str) -> Option<String> {
    let Some((shape, _)) = event.split_once("; // topic0 ") else {
        return declarable(event).then(|| event.to_string());
    };
    let (name, rest) = shape.split_once('(')?;
    let values = abi::split_top(rest.strip_suffix(')')?);
    let word = |v: &str| match v.trim().ends_with(" indexed") {
        true => "uint256 indexed",
        false => "uint256",
    };
    let mut listed = vec!["bytes32 indexed"];
    listed.extend(values.into_iter().map(word));
    identifier(name).then(|| format!("{name}({}) anonymous", listed.join(", ")))
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
fn layout(c: &Contract, taken: &BTreeSet<&str>, public: &[(usize, String)]) -> Layout {
    let slot = |text: &str| u64::from_str_radix(text.trim_start_matches("0x"), 16).ok();
    let placed = c.storage.iter().filter_map(|v| Some((slot(&v.slot)?, v)));
    let mut vars: Vec<(u64, &crate::decompile::StorageVar)> = placed.collect();
    vars.sort_by_key(|(at, _)| *at);
    let mut renamed = Vec::new();
    let mut used = BTreeSet::new();
    let mut name = |n: &str| {
        let read_by = public.iter().find(|(_, var)| var == n);
        let fresh = match (read_by, taken.contains(n)) {
            (Some((getter, _)), _) => c.functions[*getter].name.clone(),
            (None, true) => format!("_{n}"),
            (None, false) => n.to_string(),
        };
        if !identifier(&fresh) || taken.contains(fresh.as_str()) || !used.insert(fresh.clone()) {
            return Err(format!("{n} cannot be named"));
        }
        if fresh != n {
            renamed.push((n.to_string(), fresh.clone()));
        }
        Ok(match read_by {
            Some(_) => format!("public {fresh}"),
            None => fresh,
        })
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
    // Functions that only read one variable. The variable is declared public under the
    // function's name and the compiler writes the function.
    public: &'a BTreeSet<usize>,
    // Nothing is left in its exact form, so the translation of the bytecode can go.
    clean: bool,
    // Functions the compiler found to read or write more than their header said.
    relaxed: &'a BTreeMap<usize, Reach>,
    // No compiler will see this text. A function no signature gives a header to is
    // then written under the name its selector has, where a checked file leaves it out.
    drafted: bool,
    // Functions the compiler found to hold more values at once than it can reach.
    packed: &'a BTreeSet<usize>,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Reach {
    Reads,
    Writes,
}

/* What a function may touch was worked out before its helpers were folded into it. The
compiler says where a header promises too little, and the header is then widened. */
fn widened(head: String, reach: Option<&Reach>) -> String {
    match reach {
        Some(Reach::Reads) => head.replacen(" pure", " view", 1),
        Some(Reach::Writes) => head.replacen(" pure", "", 1).replacen(" view", "", 1),
        None => head,
    }
}

fn reach_asked(message: &str) -> Option<Reach> {
    let declared = message.contains("Function declared as");
    let reads = message.contains("requires \"view\"");
    let writes = message.contains("requires non-payable");
    match (declared, reads, writes) {
        (true, true, _) => Some(Reach::Reads),
        (true, _, true) => Some(Reach::Writes),
        _ => None,
    }
}

/* A test a decoder makes on where a dynamic argument lies and how long it is. The
compiler makes these itself for a header that declares the argument. Such a test weighs
places in the call data against its length or the most a decoder allows, and nothing the
author named. */
fn decoder_test(code: &str) -> bool {
    let test = code
        .strip_prefix("require(")
        .and_then(|c| c.strip_suffix(");"));
    let Some(test) = test else {
        return false;
    };
    let bounds = ["msg.data.length", "type(uint64).max", "2**32"];
    let mut rest = test.to_string();
    for known in bounds.iter().chain(&["_calldata(", "int256("]) {
        rest = rest.replace(known, "");
    }
    // A test against the end of the call data may go through a length worked out before.
    let local = test.contains("msg.data.length");
    let plain = |c: char| c.is_ascii_digit() || " ()+-*<>=!&|".contains(c) || (local && c == 'v');
    bounds.iter().any(|b| test.contains(b)) && rest.chars().all(plain)
}

fn body(c: &Contract, f: &Function, plain: &Plain<'_>) -> String {
    let payable = f.kind == FnKind::Internal || f.mutability == Mutability::Payable;
    // The compiler makes this test itself for a function that takes no ether, and
    // does not let such a function read the value.
    let external = f.kind == FnKind::External;
    let own = |l: &&str| {
        let code = l.trim();
        // So is the test that the call data is long enough for the arguments.
        let long_enough = code.strip_prefix("require(msg.data.length - 4 >= ");
        let counted = long_enough.and_then(|rest| rest.strip_suffix(");"));
        let sized = counted.is_some_and(|n| n.parse::<usize>().is_ok());
        let made = external && (sized || decoder_test(code));
        (payable || code != "require(msg.value == 0);") && !made
    };
    let lines: Vec<String> = f.code.lines().filter(own).map(one_value).collect();
    // Data written only for a failure goes first. What is left is what the checks on a
    // block's taking have to account for.
    let lines = without_writes_before_failure(answers_kept(held_strings(lines)));
    let lines = scratch_taken_for_its_call(without_scratch_before_taking(lines));
    let lines = without_dead_stores(lines);
    let mut lines = without_unread_blocks(lines);
    if lines.last().is_some_and(|l| l == "        return;") {
        lines.pop();
    }
    let text = renamed(&lines.join("\n"), &plain.layout.renamed);
    let text = checksummed(&text);
    let text = match version(c).is_some_and(|v| v < RENAMED) {
        true => text.replace("block.prevrandao", "block.difficulty"),
        false => text,
    };
    let text = unused_answers(&text);
    let text = saved_as_stored(c, &plain.layout.renamed, &text);
    let declared = declarations(c, f, &text);
    let text = returned_as_declared(&f.returns, &declared, &text);
    let marked: Vec<String> = text.lines().map(unchecked_statement).collect();
    let text = placed(&marked.join("\n"), &declared);
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

/* A compiler keeps the values of a function on a stack it can reach sixteen deep, and
refuses a function that needs more at once. An author then moves values into a struct in
memory, and so does this: the values the body declares become the fields of one struct,
which is one value on the stack. A value an assembly line names stays where it is, as
assembly cannot name a field. */
fn locals_in_memory(function: &str, text: &str) -> Option<(String, String)> {
    let declared = |line: &str| -> Option<(String, String, Option<String>)> {
        let code = line.trim().strip_suffix(';')?;
        let (left, value) = match code.split_once(" = ") {
            Some((left, value)) => (left, Some(value.to_string())),
            None => (code, None),
        };
        let (ty, name) = left.rsplit_once(' ')?;
        let held = ty.strip_suffix(" memory").unwrap_or(ty);
        let typed = elementary(held) || matches!(held, "bytes" | "string");
        (typed && identifier(name)).then(|| (held.to_string(), name.to_string(), value))
    };
    let in_assembly = |name: &str| {
        let lines = text
            .lines()
            .filter(|l| l.trim_start().starts_with("assembly"));
        lines.clone().any(|l| mentions(l, name))
    };
    let mut fields: Vec<(String, String)> = Vec::new();
    let mut lines: Vec<String> = Vec::new();
    for line in text.lines() {
        let Some((ty, name, value)) = declared(line).filter(|(_, n, _)| !in_assembly(n)) else {
            lines.push(line.to_string());
            continue;
        };
        match fields.iter().find(|(_, field)| *field == name) {
            Some((as_before, _)) if *as_before != ty => return None,
            Some(_) => {}
            None => fields.push((ty, name.clone())),
        }
        if let Some(value) = value {
            let indent = &line[..line.len() - line.trim_start().len()];
            lines.push(format!("{indent}{name} = {value};"));
        }
    }
    if fields.is_empty() {
        return None;
    }
    let held = ["m", "locals", "held"]
        .into_iter()
        .find(|n| !mentions(text, n))?;
    let named: Vec<(String, String)> = fields
        .iter()
        .map(|(_, name)| (name.clone(), format!("{held}.{name}")))
        .collect();
    let members: String = fields
        .iter()
        .map(|(ty, name)| format!("        {ty} {name};\n"))
        .collect();
    let kept = format!("    struct Locals_{function} {{\n{members}    }}\n\n");
    let body = renamed(&lines.join("\n"), &named);
    let opened = format!("        Locals_{function} memory {held};\n{body}\n");
    Some((kept, opened))
}

fn packed_body(c: &Contract, f: &Function, i: usize, plain: &Plain<'_>) -> (String, String) {
    let text = body(c, f, plain);
    let packed = plain.packed.contains(&i);
    match packed.then(|| locals_in_memory(&f.name, &text)).flatten() {
        Some(moved) => moved,
        None => (String::new(), text),
    }
}

// An argument whose place in memory the body takes is declared as held in memory.
fn held_in_memory(head: &str, body: &str) -> String {
    let mut head = head.to_string();
    for line in body.lines() {
        let taken = line.trim_start().strip_prefix("assembly { ptr");
        let name = taken.and_then(|t| t.split_once(" := ")?.1.strip_suffix(" }"));
        if let Some(name) = name {
            head = head.replace(&format!(" calldata {name}"), &format!(" memory {name}"));
        }
    }
    head
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

// The data a call gave back is only kept where something reads it.
fn unused_answers(text: &str) -> String {
    let mut out = text.to_string();
    let mut from = 0;
    while let Some(at) = out[from..].find(", returned_") {
        let start = from + at;
        let digits = out[start + 11..]
            .chars()
            .take_while(char::is_ascii_digit)
            .count();
        let name = out[start + 2..start + 11 + digits].to_string();
        from = start + 2;
        let closes = out[start + 11 + digits..].starts_with(") = ");
        if closes && out.matches(name.as_str()).count() == 1 {
            out.replace_range(start + 2..start + 11 + digits, "");
        }
    }
    out
}

/* A string put in memory to be handed to a helper. The printer shows it as a block, or
as a length and the bytes after it. In source it is the string, and the helper takes
the place it lies at. */
fn held_strings(mut lines: Vec<String>) -> Vec<String> {
    let literal = |code: &str, block: &str| {
        let text = code
            .strip_prefix(block)?
            .strip_prefix(" = memory(")?
            .strip_suffix(");")?;
        let plain = text.len() >= 2 && text.starts_with('"') && text.ends_with('"');
        (plain && !text[1..text.len() - 1].contains('"')).then(|| text.to_string())
    };
    for i in 0..lines.len() {
        let indent = lines[i].len() - lines[i].trim_start().len();
        let code = lines[i].trim_start().to_string();
        let block = blocks_named(&code).first().map(|b| b.to_string());
        let Some(block) = block else {
            continue;
        };
        if let Some(text) = literal(&code, &block) {
            lines[i] = format!("{}{block} = _pointer({text});", " ".repeat(indent));
            continue;
        }
        let raw = code.strip_prefix(&format!("mem[{block}] = "));
        let stored = code.strip_prefix(&format!("_store({block}, "));
        let stored = stored.and_then(|l| l.strip_suffix(");"));
        let length = raw.and_then(|l| l.strip_suffix(';')).or(stored);
        let length = length.and_then(|l| l.parse::<usize>().ok());
        let bytes = format!("mem[{block} + 32:+{}] = \"", length.unwrap_or(0));
        let next = lines.get(i + 1).map(|l| l.trim_start().to_string());
        let text = next
            .as_deref()
            .and_then(|l| l.strip_prefix(bytes.as_str())?.strip_suffix("\";"));
        // An escape makes the text longer than the bytes it stands for.
        let Some(text) = text.filter(|t| Some(t.len()) == length && !t.contains('\\')) else {
            continue;
        };
        lines[i] = format!("{}{block} = _pointer(\"{text}\");", " ".repeat(indent));
        lines[i + 1] = String::new();
        // The string is its own block, so the taking of one for it goes too.
        let whole = 32 + text.len().div_ceil(32) * 32;
        let taking = format!("{block} = _free(); _take({block} + {whole});");
        if i > 0 && lines[i - 1].trim_start() == taking {
            lines[i - 1] = String::new();
        }
    }
    lines.retain(|l| !l.is_empty());
    lines
}

fn numbered_name<'a>(text: &'a str, prefix: &str) -> Option<&'a str> {
    let digits = text.strip_prefix(prefix)?;
    let count = digits.chars().take_while(char::is_ascii_digit).count();
    (count > 0).then(|| &text[..prefix.len() + count])
}

/* What a compiler writes for `(bool ok, bytes memory data) = target.call(...)`: where
the call answered nothing the data is the empty string every contract keeps, and
otherwise a block the answer is copied into. The code reads the data through the address
of whichever it was. In a file the call gives the data itself, so the copying goes and a
read through the address is a read of the data. */
fn answers_kept(lines: Vec<String>) -> Vec<String> {
    const EMPTY: &str = "96";
    let code: Vec<&str> = lines.iter().map(|l| l.trim()).collect();
    let copied = |at: usize, held: &str| -> Option<usize> {
        let taken = code.get(at)?.contains(" = _free(); _take(");
        let first = at + usize::from(taken);
        let kept = code.get(first + 2)?.strip_prefix(held)?;
        let block = kept.strip_prefix(" = ")?.strip_suffix(';')?;
        let size = "_returndatasize()";
        let stored = [
            format!("_store({block}, {size});"),
            format!("mem[{block}] = {size};"),
        ];
        let moved = [
            format!("_copy_returned({block} + 32, 0x0, {size});"),
            format!("mem[{block} + 32:+{size}] = returndata[0:+{size}];"),
        ];
        let shaped = numbered_name(block, "ptr") == Some(block)
            && stored.iter().any(|l| l == code[first])
            && moved.iter().any(|l| l == code[first + 1])
            && (!taken || code[at].starts_with(&format!("{block} = _free();")));
        shaped.then_some(3 + usize::from(taken))
    };
    let found = (0..code.len()).find_map(|i| {
        let empty_first = match code[i] {
            "if (_returndatasize() == 0) {" => true,
            "if (_returndatasize() != 0) {" => false,
            _ => return None,
        };
        let (none, some) = match empty_first {
            true => (i + 1, i + 3),
            false => (
                i + 1 + copied(i + 1, numbered_name(code.get(i + 2)?, "v")?)? + 1,
                i + 1,
            ),
        };
        let held = numbered_name(code.get(none)?, "v")?;
        let lines = copied(some, held)?;
        let other = match empty_first {
            true => i + 2,
            false => some + lines,
        };
        let end = i + 3 + lines;
        let shaped = code[none] == format!("{held} = {EMPTY};")
            && code.get(other) == Some(&"} else {")
            && code.get(end) == Some(&"}");
        let call = code[..i].iter().rev().find_map(|l| {
            let rest = &l[l.find("(success_")? + 1..];
            let flag = numbered_name(rest, "success_")?;
            Some(flag.trim_start_matches("success_"))
        })?;
        shaped.then(|| (i, end + 1 - i, held.to_string(), call.to_string()))
    });
    let Some((at, count, held, call)) = found else {
        return lines;
    };
    let data = format!("returned_{call}");
    let mut out: Vec<String> = Vec::new();
    let mut handed_on = false;
    for (i, line) in lines.iter().enumerate() {
        if i == at {
            out.push(String::new());
        }
        if (at..at + count).contains(&i) {
            continue;
        }
        let mut text = line.replace(&format!("_memory({held})"), &format!("{data}.length"));
        let word = format!("_memory({held} + ");
        while let Some(start) = text.find(&word) {
            let rest = &text[start + word.len()..];
            let digits = rest.chars().take_while(char::is_ascii_digit).count();
            let place = rest[..digits].parse::<u64>().ok().filter(|p| *p >= 32);
            let Some(place) = place.filter(|_| rest[digits..].starts_with(')')) else {
                break;
            };
            let read = format!("_word({data}, {})", place - 32);
            text.replace_range(start..start + word.len() + digits + 1, &read);
        }
        handed_on |= mentions(&text, &held);
        out.push(text);
    }
    // Where the code hands the address on, it is the address of the data the call gave.
    let pad = &lines[at][..lines[at].len() - lines[at].trim_start().len()];
    match handed_on {
        true => out[at] = format!("{pad}{held} = _place({data});"),
        false => drop(out.remove(at)),
    }
    answers_kept(out)
}

fn blocks_named(text: &str) -> Vec<&str> {
    let starts = text.match_indices("ptr").filter(|(at, _)| {
        let before = text[..*at].chars().next_back();
        !before.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_')
    });
    let named = starts.filter_map(|(at, _)| {
        let digits = text[at + 3..]
            .chars()
            .take_while(char::is_ascii_digit)
            .count();
        (digits > 0).then(|| &text[at..at + 3 + digits])
    });
    named.collect()
}

// Memory at a fixed place: the two scratch words and whatever old code keeps beside them.
const FIXED: &str = "fixed";

fn fixed_read(text: &str) -> bool {
    let readers = [
        "mem[", "_memory(", "_range(", "_bytes(", "_return(", "_revert(",
    ];
    readers.iter().any(|reader| {
        let mut reads = text.match_indices(reader);
        reads.any(|(at, held)| text[at + held.len()..].starts_with(|c: char| c.is_ascii_digit()))
    })
}

/* The block a line writes to, when the line is a write to memory and the block is one
this function took for itself or a fixed place. A write through any other address is
not counted as one. Nothing here can tell what it lands on. */
fn written_block(line: &str) -> Option<&str> {
    let code = line.trim_start();
    let (target, _) = code.split_once(" = ").filter(|_| code.ends_with(';'))?;
    let inside = target
        .strip_prefix("mem[")
        .filter(|_| target.ends_with(']'));
    let place = inside.unwrap_or(target);
    let named = blocks_named(place)
        .first()
        .copied()
        .filter(|b| place.starts_with(b));
    match (named, inside) {
        (Some(block), Some(_)) => Some(block),
        (Some(block), None) => (block == target).then_some(block),
        (None, Some(at)) => at
            .starts_with(|c: char| c.is_ascii_digit())
            .then_some(FIXED),
        (None, None) => None,
    }
}

/* A write to memory does nothing a caller can see. It matters through what reads it,
and the printer shows most readers by what they mean: an event with its values, a
call with its arguments, a return with its result. A block no line reads any more
has its writes left out. A block some line still reads as raw memory keeps them, and
the function then fails to build and stays exact. */
fn without_dead_stores(lines: Vec<String>) -> Vec<String> {
    fn read_by(line: &str) -> Vec<&str> {
        let mut read = blocks_named(line);
        read.extend(fixed_read(line).then_some(FIXED));
        read
    }
    let mut live: BTreeSet<&str> = BTreeSet::new();
    for line in lines.iter().filter(|l| written_block(l).is_none()) {
        live.extend(read_by(line));
    }
    // A write that is kept reads what it copies from, and that keeps other writes.
    loop {
        let before = live.len();
        for line in &lines {
            let Some(block) = written_block(line).filter(|b| live.contains(b)) else {
                continue;
            };
            let from = line.split_once(" = ").map_or("", |(_, value)| value);
            live.extend(read_by(from));
            live.insert(block);
        }
        if live.len() == before {
            break;
        }
    }
    let kept = |l: &String| written_block(l).is_none_or(|block| live.contains(block));
    let kept: Vec<bool> = lines.iter().map(kept).collect();
    let mut keep = kept.into_iter();
    lines
        .into_iter()
        .filter(|_| keep.next() == Some(true))
        .collect()
}

/* A failure undoes everything, memory included. A write to memory that nothing but the
failure after it can read does nothing, whatever else the block it lands in is used
for on another path. */
fn without_writes_before_failure(lines: Vec<String>) -> Vec<String> {
    let fails = |l: &str| {
        let code = l.trim_start();
        let handed_on =
            code.starts_with("assembly { returndatacopy(0, 0, returndatasize()) revert(");
        handed_on || code.starts_with("revert(\"") || code.starts_with("revert(_string(")
    };
    let mut kept = vec![true; lines.len()];
    for end in (0..lines.len()).filter(|i| fails(&lines[*i])) {
        let written = lines[..end].iter().enumerate().rev();
        let writes = |l: &str| l.starts_with("mem[") || WRITERS.iter().any(|w| l.starts_with(w));
        for (i, _) in written.take_while(|(_, l)| writes(l.trim_start())) {
            kept[i] = false;
        }
    }
    let mut keep = kept.into_iter();
    lines
        .into_iter()
        .filter(|_| keep.next() == Some(true))
        .collect()
}

const WRITERS: [&str; 5] = [
    "_store(",
    "_store8(",
    "_copy_calldata(",
    "_copy_returned(",
    "_copy(",
];

/* A block the text writes to but never reads, because what the block fed is shown by
its values, does nothing. Its writes are left out, and its taking where it has one. */
fn without_unread_blocks(lines: Vec<String>) -> Vec<String> {
    let named = lines.iter().flat_map(|l| blocks_named(l));
    let named: BTreeSet<String> = named.map(str::to_string).collect();
    let only_writes = |block: &str, line: &str| {
        let code = line.trim_start();
        let writer = WRITERS.iter().find(|w| {
            let to = code.strip_prefix(**w);
            to.is_some_and(|to| to.starts_with(block))
        });
        let to = writer.map(|w| &code[w.len() + block.len()..]);
        // The block may be named again only as the place written to, never as a value.
        code.starts_with(&format!("{block} = _free();"))
            || to.is_some_and(|rest| {
                !rest.starts_with(|c: char| c.is_ascii_digit()) && !mentions(rest, block)
            })
    };
    let unread = named.iter().find(|block| {
        let named = lines.iter().filter(|l| mentions(l, block));
        named.clone().count() > 0 && named.clone().all(|l| only_writes(block, l))
    });
    match unread {
        Some(block) => {
            let rest = lines.into_iter().filter(|l| !mentions(l, block)).collect();
            without_unread_blocks(rest)
        }
        None => lines,
    }
}

/* Before a block is taken its place is free memory, where the code lays out the data
of a call. The call shows that data by its values, so the writes are left out. That
holds where the taking comes first on every way to a line that names the block. Where
it does not, the taking is put back as raw memory. The function then fails to build
and stays exact. */
fn without_scratch_before_taking(mut lines: Vec<String>) -> Vec<String> {
    let indent = |l: &str| l.len() - l.trim_start().len();
    let calls = |l: &String| l.contains("call(") || l.contains("call{");
    let named = lines.iter().flat_map(|l| blocks_named(l));
    let named: BTreeSet<String> = named.map(str::to_string).collect();
    let mut dropped = vec![false; lines.len()];
    for block in named {
        let named = [
            format!("{block} = _free();"),
            format!("assembly {{ {block} := "),
        ];
        let takings: Vec<usize> = (0..lines.len())
            .filter(|i| named.iter().any(|t| lines[*i].trim_start().starts_with(t)))
            .collect();
        let after = |i: usize, t: usize| {
            let inside = |l: &String| indent(l) >= indent(&lines[t]);
            t <= i && lines[t..=i].iter().all(inside)
        };
        let scratch = |i: usize| {
            let value = lines[i].split_once(" = ").map_or("", |(_, value)| value);
            let next = takings.iter().find(|t| **t > i);
            lines[i].trim_start().starts_with("mem[")
                && written_block(&lines[i]) == Some(block.as_str())
                && !mentions(value, &block)
                && next.is_some_and(|t| lines[i..*t].iter().any(calls))
        };
        let loose: Vec<usize> = (0..lines.len())
            .filter(|i| mentions(&lines[*i], &block))
            .filter(|i| !takings.iter().any(|t| after(*i, *t)))
            .collect();
        if loose.iter().all(|i| scratch(*i)) {
            loose.into_iter().for_each(|i| dropped[i] = true);
        } else {
            for t in takings {
                lines[t] = format!("{}{block} = mem[64];", " ".repeat(indent(&lines[t])));
            }
        }
    }
    let mut drop = dropped.into_iter();
    lines
        .into_iter()
        .filter(|_| drop.next() == Some(false))
        .collect()
}

/* Data for a call that is not shown by its values is laid out in free memory and read
back as bytes. Free memory is whatever the compiler last left there, so a file may write
to it and read it back only with nothing in between that makes the compiler use it. Where
that holds the block is named as the writes start and taken as the call is made. Where
it does not the block stays unnamed, and the function fails to build and stays exact. */
fn scratch_taken_for_its_call(mut lines: Vec<String>) -> Vec<String> {
    const QUIET: [&str; 12] = [
        "_memory",
        "_store",
        "_store8",
        "_copy",
        "_copy_calldata",
        "_copy_returned",
        "_calldata",
        "_returndatasize",
        "_word",
        "require",
        "if",
        "while",
    ];
    let indent = |l: &str| l.len() - l.trim_start().len();
    let quiet = |l: &String| {
        let called = l.match_indices('(').map(|(at, _)| {
            let mut name = l[..at].rsplit(|c: char| !c.is_ascii_alphanumeric() && c != '_');
            name.next().unwrap_or("")
        });
        let mut called = called.filter(|name| !name.is_empty());
        !l.contains('"') && called.all(|name| QUIET.contains(&name) || elementary(name))
    };
    let named = lines.iter().flat_map(|l| blocks_named(l));
    let named: BTreeSet<String> = named.map(str::to_string).collect();
    for block in named {
        let given = format!("{block} = ");
        let read = format!("_range({block}, ");
        let reads: Vec<usize> = (0..lines.len())
            .filter(|i| lines[*i].contains(&read))
            .collect();
        let first = lines.iter().position(|l| mentions(l, &block));
        let (Some(first), [call]) = (first, reads.as_slice()) else {
            continue;
        };
        let call = *call;
        let length = lines[call].split_once(&read).and_then(|(_, rest)| {
            let end = close_of(rest)?;
            (!rest[end..].contains(&read)).then(|| rest[..end].to_string())
        });
        let Some(length) = length else {
            continue;
        };
        let assigned = lines.iter().any(|l| l.trim_start().starts_with(&given));
        let later = lines[call + 1..].iter().any(|l| mentions(l, &block));
        let within = lines[first..=call]
            .iter()
            .all(|l| indent(l) >= indent(&lines[first]));
        if assigned || later || !within || !lines[first..call].iter().all(quiet) {
            continue;
        }
        let taking = format!(
            "{}_take({block} + ({length}));",
            " ".repeat(indent(&lines[call]))
        );
        let naming = format!("{}{block} = _free();", " ".repeat(indent(&lines[first])));
        lines.insert(call, taking);
        lines.insert(first, naming);
    }
    lines
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
/* The printer saves a stored value it will need after the slot is written, and declares
the save a word. A variable that holds an address or a flag is saved as one. */
fn saved_as_stored(c: &Contract, renamed: &[(String, String)], text: &str) -> String {
    let shown = |name: &str| {
        let new = renamed.iter().find(|(old, _)| old == name);
        new.map_or(name.to_string(), |(_, new)| new.clone())
    };
    let stored = |value: &str| {
        let (name, keys) = value.split_at(value.find('[').unwrap_or(value.len()));
        let var = c
            .storage
            .iter()
            .find(|v| v.fields.is_empty() && shown(&v.name) == name)?;
        let ty = var.ty.rsplit(" => ").next()?.trim_end_matches(')');
        let depth = var.ty.matches(" => ").count();
        (keys.matches('[').count() == depth && matches!(ty, "address" | "bool")).then_some(ty)
    };
    let fixed = text.lines().map(|line| {
        let code = line.trim_start();
        let saved = code
            .strip_prefix("uint256 ")
            .and_then(|c| c.strip_suffix(';'));
        let ty = saved
            .and_then(|s| s.split_once(" = "))
            .and_then(|(_, value)| stored(value));
        match ty {
            Some(ty) => line.replacen("uint256", ty, 1),
            None => line.to_string(),
        }
    });
    fixed.collect::<Vec<_>>().join("\n")
}

fn mentions(line: &str, name: &str) -> bool {
    let word = |c: char| c.is_ascii_alphanumeric() || c == '_';
    line.match_indices(name)
        .any(|(at, _)| !line[..at].ends_with(word) && !line[at + name.len()..].starts_with(word))
}

/* A value is declared where it is given, when everything that reads it lies after that
in the same block. A value given afresh in several blocks is declared in each. The
compiler frees the place of a value when its block ends, which a long function needs to
stay within the sixteen values it can reach. A value read before it is given, or read
outside the block that gave it, is declared once at the top. */
fn placed(text: &str, declared: &str) -> String {
    let lines: Vec<&str> = text.lines().collect();
    let indent = |l: &str| l.len() - l.trim_start().len();
    let closes = |from: usize| {
        let depth = indent(lines[from]);
        let ends = |l: &&str| !l.trim().is_empty() && indent(l) < depth;
        let rest = lines[from + 1..].iter().position(ends);
        rest.map_or(lines.len(), |k| from + 1 + k)
    };
    let mut top = String::new();
    let mut inner: BTreeMap<usize, String> = BTreeMap::new();
    for declaration in declared.lines() {
        let stated = declaration.trim().trim_end_matches(';');
        let name = stated.rsplit(' ').next().unwrap_or(stated);
        let gives = |at: usize| {
            let (targets, value) = lines[at].trim().split_once(" = ").unwrap_or(("", ""));
            let listed = targets.starts_with('(') && targets.ends_with(')');
            let given = targets == name || (listed && mentions(targets, name));
            given && !mentions(value, name) && indent(lines[at]) > 8
        };
        let uses = (0..lines.len()).filter(|i| mentions(lines[*i], name));
        let mut given_at: Vec<usize> = Vec::new();
        let mut covered = 0;
        let mut scoped = true;
        for at in uses {
            if at < covered {
                continue;
            }
            scoped &= gives(at);
            given_at.push(at);
            covered = closes(at);
        }
        if !scoped || given_at.is_empty() {
            top.push_str(&format!("{declaration}\n"));
            continue;
        }
        for at in given_at {
            let pad = " ".repeat(indent(lines[at]));
            let here = inner.entry(at).or_default();
            here.push_str(&format!("{pad}{}\n", declaration.trim()));
        }
    }
    let mut out = top;
    for (i, line) in lines.iter().enumerate() {
        out.push_str(inner.get(&i).map_or("", String::as_str));
        out.push_str(line);
        if i + 1 < lines.len() {
            out.push('\n');
        }
    }
    out
}

fn close_of(text: &str) -> Option<usize> {
    let mut depth = 1i32;
    text.char_indices().find_map(|(i, c)| {
        depth += i32::from(c == '(') - i32::from(c == ')');
        (depth == 0).then_some(i)
    })
}

// A sum on an address in memory is the compiler's own, which it never tests.
fn past_addresses(code: &str) -> &str {
    if let Some((_, rest)) = code.split_once(" = _free(); _take(") {
        return past_addresses(rest.split_once("); ").map_or("", |(_, after)| after));
    }
    let helpers = [
        ("_take(", 1),
        ("_store(", 1),
        ("_store8(", 1),
        ("_copy(", 2),
        ("_copy_calldata(", 2),
        ("_copy_returned(", 2),
    ];
    let Some((name, addresses)) = helpers.iter().find(|(name, _)| code.starts_with(name)) else {
        return code;
    };
    let (mut depth, mut left) = (0i32, *addresses);
    for (i, c) in code[name.len()..].char_indices() {
        depth += i32::from(c == '(') - i32::from(c == ')');
        left -= usize::from(c == ',' && depth == 0);
        if left == 0 {
            return &code[name.len() + i..];
        }
    }
    code
}

/* The printer marks arithmetic the code does not test for overflow. A file can say so
only for a whole statement. A statement goes in an unchecked block when every sum in it
is marked, as a block around one that is tested would stop the test. */
fn unchecked_statement(line: &str) -> String {
    const MARK: &str = "unchecked(";
    let code = line.trim_start();
    if !code.contains(MARK) || !code.ends_with(';') || code.contains('"') {
        return line.to_string();
    }
    let (mut bare, mut outside, mut rest) = (String::new(), String::new(), code);
    while let Some(at) = rest.find(MARK) {
        let inner = &rest[at + MARK.len()..];
        let Some(end) = close_of(inner) else {
            return line.to_string();
        };
        outside.push_str(&rest[..at]);
        bare.push_str(&format!(
            "{}({})",
            &rest[..at],
            inner[..end].replace(MARK, "(")
        ));
        rest = &inner[end + 1..];
    }
    outside.push_str(rest);
    bare.push_str(rest);
    if past_addresses(&outside).contains(['+', '-', '*', '/', '%']) || bare.contains("checked(") {
        return line.to_string();
    }
    let indent = &line[..line.len() - code.len()];
    let declared = bare.split_once(" = ").and_then(|(left, value)| {
        let (ty, name) = left.split_once(' ')?;
        (elementary(ty) && identifier(name)).then_some((ty, name, value))
    });
    match declared {
        Some((ty, name, value)) => {
            format!("{indent}{ty} {name};\n{indent}unchecked {{ {name} = {value} }}")
        }
        None => format!("{indent}unchecked {{ {bare} }}"),
    }
}

/* A value a helper gave back can be a flag where this function returns a number, or a
number where it returns a flag. The types were worked out one function at a time. */
fn returned_as_declared(returns: &[String], declared: &str, text: &str) -> String {
    let [wanted] = returns else {
        return text.to_string();
    };
    let is = |ty: &str, name: &str| declared.contains(&format!("        {ty} {name};\n"));
    let fixed = text.lines().map(|line| {
        let code = line.trim_start();
        let indent = &line[..line.len() - code.len()];
        let value = code
            .strip_prefix("return ")
            .and_then(|c| c.strip_suffix(';'));
        // What the code returns from memory is held at an address, a number to the text.
        let held = value.filter(|v| is("uint256", v));
        match (value, wanted.as_str(), held) {
            (_, "uint256[]", Some(at)) => return format!("{indent}return _words({at});"),
            (_, "bytes", Some(at)) => return format!("{indent}return _bytes({at});"),
            (_, "string", Some(at)) => return format!("{indent}return string(_bytes({at}));"),
            _ => {}
        }
        match value {
            Some(v) if wanted.starts_with("uint") && is("bool", v) => {
                format!("{indent}return {v} ? 1 : 0;")
            }
            Some(v) if wanted == "bool" && is("uint256", v) => format!("{indent}return {v} != 0;"),
            _ => line.to_string(),
        }
    });
    fixed.collect::<Vec<_>>().join("\n")
}

// What a helper gives back has the type the helper declares for it.
fn result_type(c: &Contract, text: &str, name: &str) -> Option<String> {
    let (_, position) = name.rsplit_once('_')?;
    let given = text.lines().find_map(|l| {
        let (targets, value) = l.trim_start().split_once(" = ")?;
        let mut own = targets.split(|c: char| !c.is_ascii_alphanumeric() && c != '_');
        own.any(|t| t == name).then_some(value)
    })?;
    let callee = given.split('(').next()?;
    let called = |f: &&Function| f.kind == FnKind::Internal && f.name == callee;
    let helper = c.functions.iter().find(called)?;
    let ty = helper.returns.get(position.parse::<usize>().ok()?)?;
    written(ty, "memory").filter(|_| helper.returns.len() == helper.n_rets)
}

fn declarations(c: &Contract, f: &Function, text: &str) -> String {
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
    for (prefix, ty) in [("success_", "bool"), ("returned_", "bytes memory")] {
        for name in words.iter().filter(|w| numbered(w, prefix)) {
            out.push_str(&format!("        {ty} {name};\n"));
        }
    }
    // A block is a variable only where a string was put in it by name. Any other use of
    // one is memory this text does not account for, and has to fail to build.
    for name in words.iter().filter(|w| numbered(w, "ptr")) {
        let given = [
            format!("{name} = _pointer("),
            format!("{name} = _free()"),
            format!("assembly {{ {name} := "),
        ];
        if given.iter().any(|g| text.contains(g)) {
            out.push_str(&format!("        uint256 {name};\n"));
        }
    }
    // A word the function kept in memory for itself is a local value, and a run of them
    // a struct in memory.
    for name in words
        .iter()
        .filter(|w| numbered(w, "s") && w.ends_with("_0"))
    {
        out.push_str(&format!("        uint256 {name};\n"));
    }
    for name in words
        .iter()
        .filter(|w| numbered(w, "s") && !w.contains('_'))
    {
        let field = format!("{name}.w");
        let fields = text.match_indices(&field).filter_map(|(at, held)| {
            let apart = !text[..at].ends_with(word);
            let digits = text[at + held.len()..].split(|c: char| !c.is_ascii_digit());
            digits
                .take(1)
                .find_map(|d| d.parse::<u64>().ok())
                .filter(|_| apart)
        });
        if let Some(last) = fields.max() {
            out.push_str(&format!("        Words{} memory {name};\n", last + 1));
        }
    }
    for name in words.iter().filter(|w| numbered(w, "ret_")) {
        let ty = result_type(c, text, name).unwrap_or_else(|| "uint256".to_string());
        out.push_str(&format!("        {ty} {name};\n"));
    }
    out
}

// The helpers the functions written out reach. A helper only a function in its exact
// form calls is text nothing runs, and the check would never try it.
fn helpers(c: &Contract, plain: &BTreeSet<usize>, mut work: Vec<usize>) -> BTreeSet<usize> {
    let at = |pc: usize| {
        c.functions
            .iter()
            .position(|f| f.pc == pc && f.kind == FnKind::Internal)
    };
    let mut found = BTreeSet::new();
    while let Some(i) = work.pop() {
        for callee in c.functions[i].calls.iter().filter_map(|pc| at(*pc)) {
            if plain.contains(&callee) && found.insert(callee) {
                work.push(callee);
            }
        }
    }
    found
}

/* What plain Solidity has no word for, written once and called by name: a string taken
as the place it lies at and back, a word of the data a call gave back, and how much it
gave. */
const HELPERS: [(&str, &str); 21] = [
    (
        "_free(",
        "    function _free() private pure returns (uint256 at) {
        assembly {
            at := mload(0x40)
        }
    }

",
    ),
    (
        "_take(",
        "    function _take(uint256 end) private pure {
        assembly {
            if gt(end, mload(0x40)) {
                mstore(0x40, end)
            }
        }
    }

",
    ),
    (
        "_store(",
        "    function _store(uint256 at, uint256 word) private pure {
        assembly {
            mstore(at, word)
        }
    }

",
    ),
    (
        "_store8(",
        "    function _store8(uint256 at, uint256 word) private pure {
        assembly {
            mstore8(at, word)
        }
    }

",
    ),
    (
        "_copy_calldata(",
        "    function _copy_calldata(uint256 to, uint256 from, uint256 size) private pure {
        assembly {
            calldatacopy(to, from, size)
        }
    }

",
    ),
    (
        "_copy_returned(",
        "    function _copy_returned(uint256 to, uint256 from, uint256 size) private pure {
        assembly {
            returndatacopy(to, from, size)
        }
    }

",
    ),
    (
        "_copy(",
        "    function _copy(uint256 to, uint256 from, uint256 size) private pure {
        assembly {
            let i := 0
            for { } lt(add(i, 31), size) { i := add(i, 32) } {
                mstore(add(to, i), mload(add(from, i)))
            }
            if lt(i, size) {
                let kept := shr(mul(8, sub(size, i)), not(0))
                let last := and(mload(add(from, i)), not(kept))
                mstore(add(to, i), or(last, and(mload(add(to, i)), kept)))
            }
        }
    }

",
    ),
    (
        "_memory(",
        "    function _memory(uint256 at) private pure returns (uint256 word) {
        assembly {
            word := mload(at)
        }
    }

",
    ),
    (
        "_place(",
        "    function _place(bytes memory data) private pure returns (uint256 at) {
        assembly {
            at := data
        }
    }

",
    ),
    (
        "_words(",
        "    function _words(uint256 at) private pure returns (uint256[] memory held) {
        assembly {
            held := at
        }
    }

",
    ),
    (
        "_bytes(",
        "    function _bytes(uint256 at) private pure returns (bytes memory data) {
        assembly {
            data := at
        }
    }

",
    ),
    (
        "_range(",
        "    function _range(uint256 at, uint256 size) private pure returns (bytes memory data) {
        data = new bytes(size);
        assembly {
            for { let i := 0 } lt(i, size) { i := add(i, 32) } {
                mstore(add(add(data, 32), i), mload(add(at, i)))
            }
        }
    }

",
    ),
    (
        "_return(",
        "    function _return(uint256 at, uint256 size) private pure {
        assembly {
            return(at, size)
        }
    }

",
    ),
    (
        "_revert(",
        "    function _revert(uint256 at, uint256 size) private pure {
        assembly {
            revert(at, size)
        }
    }

",
    ),
    (
        "_calldata(",
        "    function _calldata(uint256 at) private pure returns (uint256 word) {
        assembly {
            word := calldataload(at)
        }
    }

",
    ),
    (
        "_panic(",
        "    function _panic(uint256 code) private pure {
        assembly {
            mstore(0, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
            mstore(4, code)
            revert(0, 36)
        }
    }

",
    ),
    (
        "_fail(",
        "    function _fail(bytes memory data) private pure {
        assembly {
            revert(add(data, 32), mload(data))
        }
    }

",
    ),
    (
        "_pointer(",
        "    function _pointer(string memory text) private pure returns (uint256 at) {
        assembly {
            at := text
        }
    }

",
    ),
    (
        "_string(",
        "    function _string(uint256 at) private pure returns (string memory text) {
        assembly {
            text := at
        }
    }

",
    ),
    (
        "_word(",
        "    function _word(bytes memory data, uint256 at) private pure returns (uint256 word) {
        assembly {
            word := mload(add(add(data, 32), at))
            let missing := sub(add(at, 32), mload(data))
            if slt(0, missing) {
                word := mul(lt(missing, 32), and(word, not(sub(shl(mul(8, missing), 1), 1))))
            }
        }
    }

",
    ),
    (
        "_returndatasize(",
        "    function _returndatasize() private pure returns (uint256 size) {
        assembly {
            size := returndatasize()
        }
    }

",
    ),
];

pub struct Draft {
    pub text: String,
    spans: Vec<(usize, usize, usize)>,
}

// A struct of plain words, for each length of one a function keeps in memory.
fn structs_declared(text: &str) -> String {
    let named = text.match_indices("Words").filter_map(|(at, held)| {
        let rest = &text[at + held.len()..];
        let digits = rest.split(|c: char| !c.is_ascii_digit()).next()?;
        let words = digits.parse::<u64>().ok()?;
        rest[digits.len()..]
            .starts_with(" memory ")
            .then_some(words)
    });
    let lengths: BTreeSet<u64> = named.collect();
    let mut out = String::new();
    for words in lengths {
        let fields: String = (0..words).map(|i| format!(" uint256 w{i};")).collect();
        out.push_str(&format!("    struct Words{words} {{{fields} }}\n"));
    }
    if !out.is_empty() {
        out.push('\n');
    }
    out
}

// An error the text fails with by name is one the printer knew by its whole signature.
fn errors_declared(text: &str) -> String {
    let mut found = BTreeSet::new();
    for (at, _) in text.match_indices("revert ") {
        let rest = &text[at + "revert ".len()..];
        let Some((name, given)) = rest.split_once('(') else {
            continue;
        };
        let values = close_of(given).map(|end| abi::split_top(&given[..end]).len());
        let known = values.and_then(|n| crate::sigs::error_named(name, n));
        found.extend(known.filter(|_| identifier(name)));
    }
    let mut out: String = found.iter().map(|e| format!("    error {e};\n")).collect();
    if !out.is_empty() {
        out.push('\n');
    }
    out
}

fn compose(c: &Contract, shape: &Shape, plain: Option<&Plain<'_>>) -> Draft {
    let own = version(c).filter(|_| shape.own_version);
    let pragma = match own {
        Some((a, b, patch)) => format!("{a}.{b}.{patch}"),
        None => MODERN.to_string(),
    };
    // The pragma names a compiler that reads this text, which for older code is not the
    // one the contract was built with.
    let built = match own {
        Some(_) => String::new(),
        None => format!("// Originally compiled with {}.\n", c.language),
    };
    let licence = "// SPDX-License-Identifier: UNLICENSED";
    let mut out = format!("{licence}\npragma solidity {pragma};\n{built}\n");
    let mut spans = Vec::new();
    out.push_str(&format!("contract {} {{\n", contract_name(c)));
    if let Some(plain) = plain.filter(|p| !p.layout.text.is_empty()) {
        out.push_str(&plain.layout.text);
        out.push('\n');
    }
    if shape.events {
        let events: BTreeSet<String> = c.events.iter().filter_map(|e| declared(e)).collect();
        for event in &events {
            out.push_str(&format!("    event {event};\n"));
        }
        if !events.is_empty() {
            out.push('\n');
        }
    }
    let errors_at = out.len();
    let mut written = BTreeSet::new();
    for (i, f) in c.functions.iter().enumerate() {
        if plain.is_some_and(|p| p.public.contains(&i)) {
            continue;
        }
        let whole = plain.filter(|p| p.functions.contains(&i) && f.kind == FnKind::External);
        if let Some((plain, head)) = whole.and_then(|p| Some((p, header(f, shape, true)?))) {
            let head = widened(head, plain.relaxed.get(&i));
            if written.insert(head.clone()) {
                let start = out.len();
                let (kept, text) = packed_body(c, f, i, plain);
                let head = held_in_memory(&head, &text);
                out.push_str(&format!("{kept}    {head} {{\n{text}    }}\n\n"));
                spans.push((start, out.len(), i));
            }
            continue;
        }
        let external = f.kind == FnKind::External && !f.inlined;
        if let Some(plain) = plain.filter(|p| p.drafted && external) {
            let head = crate::decompile::fmt_function_header(f);
            let start = out.len();
            out.push_str(&format!("{head}{}    }}\n\n", body(c, f, plain)));
            spans.push((start, out.len(), i));
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
    let clean = plain.is_some_and(|p| p.clean);
    if !clean {
        out.push_str("    fallback() external payable {\n        _original();\n    }\n\n");
    }
    if let Some(plain) = plain {
        let unnamed = |f: &Function| matches!(f.kind, FnKind::Fallback | FnKind::Receive);
        let all = c.functions.iter().enumerate();
        let own = all.filter(|(i, f)| clean && unnamed(f) && plain.functions.contains(i));
        let mut printed: Vec<usize> = own.map(|(i, _)| i).collect();
        let callers = printed.iter().chain(spans.iter().map(|(_, _, i)| i));
        printed.extend(helpers(c, plain.functions, callers.copied().collect()));
        for i in printed {
            let f = &c.functions[i];
            let start = out.len();
            let head = crate::decompile::fmt_function_header(f);
            let head = widened(head, plain.relaxed.get(&i));
            let (kept, text) = packed_body(c, f, i, plain);
            out.push_str(&format!("{kept}{head}{text}    }}\n\n"));
            spans.push((start, out.len(), i));
        }
    }
    for (used, helper) in HELPERS {
        if out.contains(used) {
            out.push_str(helper);
        }
    }
    let errors = format!(
        "{}{}",
        structs_declared(&out[errors_at..]),
        errors_declared(&out[errors_at..])
    );
    for span in &mut spans {
        *span = (span.0 + errors.len(), span.1 + errors.len(), span.2);
    }
    out.insert_str(errors_at, &errors);
    if clean {
        out.truncate(out.trim_end().len());
        out.push_str("\n}\n");
        return Draft { text: out, spans };
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

fn uncast(text: &str) -> &str {
    let inner = text.split_once('(').filter(|(ty, _)| elementary(ty));
    let inner = inner.and_then(|(_, rest)| rest.strip_suffix(')'));
    let whole = |i: &&str| {
        let mut depth = 0i32;
        i.chars().all(|c| {
            depth += i32::from(c == '(') - i32::from(c == ')');
            depth >= 0
        })
    };
    inner.filter(whole).unwrap_or(text)
}

fn getters(c: &Contract) -> Vec<(usize, String)> {
    let read = |(i, f): (usize, &Function)| Some((i, getter(c, f)?.to_string()));
    let mut public: Vec<(usize, String)> =
        c.functions.iter().enumerate().filter_map(read).collect();
    // Two functions can read one variable, as `owner` and `getOwner` do. The variable
    // takes the name an author is more likely to have given it.
    let plainness = |i: usize| {
        let name = &c.functions[i].name;
        (name.starts_with("get"), name.len())
    };
    public.sort_by_key(|(i, var)| (var.clone(), plainness(*i)));
    public.dedup_by(|later, first| later.1 == first.1);
    public
}

fn printable(c: &Contract) -> BTreeSet<usize> {
    let kinds = [
        FnKind::External,
        FnKind::Internal,
        FnKind::Fallback,
        FnKind::Receive,
    ];
    let shown = |f: &&Function| !f.inlined && kinds.contains(&f.kind);
    let all = c.functions.iter().enumerate();
    all.filter(|(_, f)| shown(f)).map(|(i, _)| i).collect()
}

/* The Solidity file as it is first written: every function in its plain form, with no
compiler asked and nothing run beside the bytecode. It reads as the checked file does,
and what a compiler would refuse or the check would find different is still in it. */
#[must_use]
pub fn draft(c: &Contract) -> String {
    let public = getters(c);
    let read: BTreeSet<usize> = public.iter().map(|(i, _)| *i).collect();
    let written = c
        .functions
        .iter()
        .enumerate()
        .filter(|(i, _)| !read.contains(i));
    let names = written.map(|(_, f)| f.name.as_str());
    let events = c.events.iter().filter_map(|e| e.split('(').next());
    let taken: BTreeSet<&str> = names.chain(events).collect();
    let layout = layout(c, &taken, &public);
    let shape = Shape {
        own_version: true,
        names: true,
        events: true,
        ..Shape::default()
    };
    let plain = Plain {
        functions: &printable(c),
        layout: &layout,
        public: &read,
        clean: true,
        relaxed: &BTreeMap::new(),
        drafted: true,
        packed: &BTreeSet::new(),
    };
    compose(c, &shape, Some(&plain)).text
}

// The variable a function returns and does nothing else, read under the function's own
// arguments in their order.
fn getter<'a>(c: &'a Contract, f: &Function) -> Option<&'a str> {
    // The compiler names the function it writes after the variable, so only a function
    // whose own name gives its selector can be handed over.
    let named = header(f, &Shape::default(), true).is_some();
    if !named || f.inlined || f.mutability != Mutability::View {
        return None;
    }
    let code = f.code.lines().map(str::trim);
    let lines: Vec<&str> = code
        .filter(|l| !l.is_empty() && *l != "require(msg.value == 0);")
        .collect();
    let [line] = lines.as_slice() else {
        return None;
    };
    let shown = one_value(line);
    let value = uncast(shown.strip_prefix("return ")?.strip_suffix(';')?);
    let (name, mut rest) = value.split_at(value.find('[').unwrap_or(value.len()));
    for p in &f.params {
        let (index, after) = rest.strip_prefix('[')?.split_once(']')?;
        if uncast(index) != p.name {
            return None;
        }
        rest = after;
    }
    let plain = c.storage.iter().filter(|v| v.members.is_empty());
    let mut names = plain.flat_map(|v| {
        let fields = v.fields.iter().map(|f| f.name.as_str());
        fields.chain(v.fields.is_empty().then_some(v.name.as_str()))
    });
    names.find(|n| rest.is_empty() && *n == name)
}

/* The exact file with every function the printer's own text can stand in for written
out as plain Solidity. A function is written out only while the file still builds and
the function still does what the bytecode does. Whatever fails either test goes back
to the exact translation, and so does everything that calls it. */
#[cfg(feature = "rpc")]
pub fn raised_file(c: &Contract, runs: usize) -> Result<Output, String> {
    use crate::check;
    let floor = exact_file(c, runs)?;
    let trace = std::env::var_os("EVMDEC_RAISE_TRACE").is_some();
    let trace_text = std::env::var("EVMDEC_RAISE_TRACE").is_ok_and(|v| v == "2");
    let mut public = getters(c);
    let mut shape = floor.shape.clone();
    let mut plain = printable(c);
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
    let mut relaxed: BTreeMap<usize, Reach> = BTreeMap::new();
    let mut packed: BTreeSet<usize> = BTreeSet::new();
    for _ in 0..48 {
        crate::clock::check();
        let read: BTreeSet<usize> = public.iter().map(|(i, _)| *i).collect();
        let written = c
            .functions
            .iter()
            .enumerate()
            .filter(|(i, _)| !read.contains(i));
        let names = written.map(|(_, f)| f.name.as_str());
        let events = c.events.iter().filter_map(|e| e.split('(').next());
        let taken: BTreeSet<&str> = names.chain(events).chain(["_original"]).collect();
        let layout = layout(c, &taken, &public);
        let written = Plain {
            functions: &plain,
            layout: &layout,
            public: &read,
            clean: false,
            relaxed: &relaxed,
            drafted: false,
            packed: &packed,
        };
        let draft = compose(c, &shape, Some(&written));
        if draft.spans.is_empty() && read.is_empty() {
            break;
        }
        let mut failed: Vec<usize> = Vec::new();
        match crate::solc::compile_with(&draft.text, false) {
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
                    let shown = draft
                        .spans
                        .iter()
                        .find(|(_, _, i)| failed.first() == Some(i));
                    if let Some((from, to, _)) = shown.filter(|_| trace_text) {
                        eprintln!("{}", &draft.text[*from..*to]);
                    }
                }
                let deep = refusal.message.contains("Stack too deep");
                if failed.first().is_some_and(|i| deep && packed.insert(*i)) {
                    continue;
                }
                let asked = reach_asked(&refusal.message).zip(failed.first().copied());
                if let Some((reach, i)) = asked.filter(|(r, i)| relaxed.get(i) < Some(r)) {
                    relaxed.insert(i, reach);
                    continue;
                }
                // An error outside every function is in what they all share. The public
                // variables are the part of that which can be taken back.
                if failed.is_empty() && public.is_empty() {
                    break;
                }
                if failed.is_empty() {
                    public.clear();
                    continue;
                }
            }
            Ok(built) => {
                let built = built.into_iter().next().ok_or("nothing was built")?;
                let mut named: Vec<(u32, String)> = built.signatures.clone().into_iter().collect();
                named.sort();
                let spans = draft.spans.iter().map(|(_, _, i)| *i);
                let whole: BTreeSet<u32> = spans
                    .chain(read.iter().copied())
                    .filter_map(|i| selector(&c.functions[i]))
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
                        let calls = index.map(|i| c.functions[i].calls.clone());
                        let called = |i: &usize| {
                            let helper = calls
                                .as_ref()
                                .is_some_and(|v| v.contains(&c.functions[*i].pc));
                            helper || selector(&c.functions[*i]) == Some(s)
                        };
                        let shown = draft.spans.iter().filter(|(_, _, i)| called(i));
                        for (from, to, _) in shown.filter(|_| trace_text) {
                            eprintln!("{}", &draft.text[*from..*to]);
                        }
                    }
                    if index.is_some_and(|i| read.contains(&i)) {
                        public.retain(|(i, _)| Some(*i) != index);
                        failed.push(usize::MAX);
                        continue;
                    }
                    // A selector no function of the original has was made by the compiler
                    // for a public variable.
                    if index.is_none() && !public.is_empty() {
                        public.clear();
                        failed.push(usize::MAX);
                        continue;
                    }
                    let shown = draft.spans.iter().find(|(_, _, i)| Some(*i) == index);
                    if let Some((from, to, _)) = shown.filter(|_| trace) {
                        eprintln!("{}", &draft.text[*from..*to]);
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
                    let named = externals.filter(|f| f.kind == FnKind::External);
                    let getters = read.iter().map(|i| &c.functions[*i]);
                    let names: Vec<String> = named.chain(getters).map(|f| f.name.clone()).collect();
                    let within = |i: usize| {
                        read.contains(&i) || draft.spans.iter().any(|(_, _, at)| *at == i)
                    };
                    let external = |f: &Function| f.kind == FnKind::External && !f.inlined;
                    let all = c.functions.iter().enumerate();
                    let every = all.filter(|(_, f)| external(f)).all(|(i, _)| within(i));
                    let whole = Plain {
                        functions: &plain,
                        layout: &layout,
                        public: &read,
                        clean: true,
                        relaxed: &relaxed,
                        drafted: false,
                        packed: &packed,
                    };
                    let clean = every.then(|| compose(c, &shape, Some(&whole)));
                    let tried = clean.and_then(|draft| {
                        let built = crate::solc::compile_with(&draft.text, false).ok()?;
                        let built = built.into_iter().next()?;
                        let report =
                            check::compare(&c.info.runtime, &built.runtime, &entries, depth);
                        report.equal().then_some((draft, built, report))
                    });
                    let (draft, built, report) = tried.unwrap_or((draft, built, report));
                    return Ok(Output {
                        source: draft.text,
                        compiler: built.compiler,
                        report,
                        headers: built.signatures.len(),
                        refused: floor.refused,
                        plain: names,
                        shape,
                    });
                }
            }
        }
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
    fn a_write_to_memory_goes_when_nothing_reads_its_block() {
        let line = |text: &str| format!("        {text}");
        let fed = vec![
            line("ptr1 = memory(\"2\");"),
            line("mem[ptr2 + 64:+32] = mem[ptr1 + 32:+32];"),
        ];
        let mut dead = fed.clone();
        dead.push(line("return \"2\";"));
        assert_eq!(without_dead_stores(dead), vec![line("return \"2\";")]);
        let mut read = fed.clone();
        read.push(line("v1 = mem[ptr2 + 64];"));
        assert_eq!(without_dead_stores(read.clone()), read);
        let mut other = fed.clone();
        other.extend([line("mem[ptr3] = 7;"), line("v1 = mem[ptr3] + mem[arg0];")]);
        assert_eq!(without_dead_stores(other.clone()), other[2..].to_vec());
    }

    #[test]
    fn a_string_put_in_memory_becomes_the_string() {
        let line = |text: &str| format!("        {text}");
        let block = vec![line("ptr1 = memory(\"overflow\");"), line("f(a, ptr1);")];
        assert_eq!(
            held_strings(block)[0],
            line("ptr1 = _pointer(\"overflow\");")
        );
        let words = vec![
            line("mem[ptr2] = 5;"),
            line("mem[ptr2 + 32:+5] = \"short\";"),
            line("f(a, ptr2);"),
        ];
        let want = vec![line("ptr2 = _pointer(\"short\");"), line("f(a, ptr2);")];
        assert_eq!(held_strings(words), want);
        let longer = vec![
            line("mem[ptr3] = 9;"),
            line("mem[ptr3 + 32:+5] = \"short\";"),
        ];
        assert_eq!(held_strings(longer.clone()), longer);
        let taken = vec![
            line("ptr4 = _free(); _take(ptr4 + 64);"),
            line("_store(ptr4, 5);"),
            line("mem[ptr4 + 32:+5] = \"short\";"),
        ];
        assert_eq!(held_strings(taken), [line("ptr4 = _pointer(\"short\");")]);
    }

    #[test]
    fn an_event_known_by_its_topic_is_declared_anonymous() {
        let known = "Transfer(address indexed, address indexed, uint256)";
        assert_eq!(declared(known).as_deref(), Some(known));
        let unknown = "Event_01b7c780(uint256 indexed, uint256); // topic0 0x01b7";
        let want = "Event_01b7c780(bytes32 indexed, uint256 indexed, uint256) anonymous";
        assert_eq!(declared(unknown).as_deref(), Some(want));
    }

    #[test]
    fn data_a_call_gave_back_is_kept_only_where_it_is_read() {
        let text = "(success_1, returned_1) = a.call(x);\n(success_2, returned_2) = b.call(y);\nv = _word(returned_2, 0);";
        let want = "(success_1, ) = a.call(x);\n(success_2, returned_2) = b.call(y);\nv = _word(returned_2, 0);";
        assert_eq!(unused_answers(text), want);
    }

    #[test]
    fn a_cast_comes_off_only_when_it_wraps_the_whole_value() {
        assert_eq!(uncast("address(account)"), "account");
        assert_eq!(uncast("uint8(a) + uint8(b)"), "uint8(a) + uint8(b)");
        assert_eq!(uncast("balanceOf(account)"), "balanceOf(account)");
    }

    #[test]
    fn a_statement_is_unchecked_only_when_all_its_sums_are() {
        let all = unchecked_statement("    x = unchecked(a + b);");
        assert_eq!(all, "    unchecked { x = (a + b); }");
        let declared = unchecked_statement("    uint256 t1 = unchecked(a - 1);");
        assert_eq!(declared, "    uint256 t1;\n    unchecked { t1 = (a - 1); }");
        let mixed = "    x = unchecked(a + b) + c;";
        assert_eq!(unchecked_statement(mixed), mixed);
        let placed = unchecked_statement("    _store(ptr1 + 32, unchecked(a + b));");
        assert_eq!(placed, "    unchecked { _store(ptr1 + 32, (a + b)); }");
        let tested = "    _store(ptr1 + 32, unchecked(a + b) + c);";
        assert_eq!(unchecked_statement(tested), tested);
    }

    #[test]
    fn data_laid_out_for_a_call_before_its_block_is_taken_is_left_out() {
        let lines = |text: &str| text.lines().map(str::to_string).collect::<Vec<_>>();
        let scratch = "mem[ptr2 + 4] = a;\nok = t.call(abi.encode(a));\nptr2 = _free(); _take(ptr2 + 64);\n_store(ptr2, b);\nf(ptr2);";
        let want = "ok = t.call(abi.encode(a));\nptr2 = _free(); _take(ptr2 + 64);\n_store(ptr2, b);\nf(ptr2);";
        assert_eq!(
            without_scratch_before_taking(lines(scratch)).join("\n"),
            want
        );
        let outside = "if (c) {\n    ptr2 = _free(); _take(ptr2 + 64);\n}\nf(ptr2);";
        let kept = without_scratch_before_taking(lines(outside)).join("\n");
        assert!(kept.contains("ptr2 = mem[64];"), "{kept}");
        let each = "if (c) {\n    ptr2 = _free(); _take(ptr2 + 64);\n    f(ptr2);\n} else {\n    ptr2 = _free(); _take(ptr2 + 64);\n    g(ptr2);\n}";
        assert_eq!(without_scratch_before_taking(lines(each)).join("\n"), each);
    }

    #[test]
    fn data_laid_out_for_a_call_is_taken_as_the_call_is_made() {
        let lines = |text: &str| text.lines().map(str::to_string).collect::<Vec<_>>();
        let laid = "_store(ptr1, a);\n_copy(ptr1 + 36, b + 32, _memory(b));\n(ok, ) = t.call(_range(ptr1, _memory(b) + 36));";
        let want = "ptr1 = _free();\n_store(ptr1, a);\n_copy(ptr1 + 36, b + 32, _memory(b));\n_take(ptr1 + (_memory(b) + 36));\n(ok, ) = t.call(_range(ptr1, _memory(b) + 36));";
        assert_eq!(scratch_taken_for_its_call(lines(laid)).join("\n"), want);
        let busy = laid.replace(
            "_copy(ptr1 + 36",
            "x = keccak256(abi.encode(a));\n_copy(ptr1 + 36",
        );
        assert_eq!(scratch_taken_for_its_call(lines(&busy)).join("\n"), busy);
    }

    #[test]
    fn the_values_a_long_function_declares_move_into_one_struct() {
        let body = "        uint256 v1;\n        bool ok;\n        uint256 ptr1;\n        \
                    assembly { ptr1 := a }\n        v1 = f(ptr1);\n        \
                    uint256 t1 = v1 + 1;\n        ok = t1 > v1;\n";
        let (kept, text) = locals_in_memory("g", body).unwrap();
        let fields = "        uint256 v1;\n        bool ok;\n        uint256 t1;\n";
        assert_eq!(kept, format!("    struct Locals_g {{\n{fields}    }}\n\n"));
        let want = "        Locals_g memory m;\n        uint256 ptr1;\n        \
                    assembly { ptr1 := a }\n        m.v1 = f(ptr1);\n        \
                    m.t1 = m.v1 + 1;\n        m.ok = m.t1 > m.v1;\n";
        assert_eq!(text, want);
        assert!(locals_in_memory("g", "        return a;\n").is_none());
    }

    #[test]
    fn an_argument_the_body_takes_from_memory_is_declared_in_memory() {
        let head = "function f(address a, bytes calldata arg1) external";
        let body = "        assembly { ptr1 := arg1 }\n        g(a, ptr1);\n";
        let want = "function f(address a, bytes memory arg1) external";
        assert_eq!(held_in_memory(head, body), want);
        assert_eq!(held_in_memory(head, "        g(a, 128);\n"), head);
    }

    #[test]
    fn an_address_returned_as_an_array_is_handed_back_as_one() {
        let returns = ["uint256[]".to_string()];
        let declared = "        uint256 ptr1;\n";
        let text = returned_as_declared(&returns, declared, "        return ptr1;");
        assert_eq!(text, "        return _words(ptr1);");
    }

    #[test]
    fn a_value_is_declared_in_the_block_that_gives_it() {
        let body =
            "        if (a) {\n            x = 1;\n            f(x);\n        }\n        y = 2;";
        let declared = "        uint256 x;\n        uint256 y;\n";
        let want = "        uint256 y;\n        if (a) {\n            uint256 x;\n            x = 1;\n            f(x);\n        }\n        y = 2;";
        assert_eq!(placed(body, declared), want);
        let read_after = "        if (a) {\n            x = 1;\n        }\n        f(x);";
        let top = format!("        uint256 x;\n{read_after}");
        assert_eq!(placed(read_after, "        uint256 x;\n"), top);
    }

    #[test]
    fn an_answer_copied_to_memory_is_read_as_the_data_the_call_gave() {
        let text = "(success_1, returned_1) = t.call(x);
if (_returndatasize() == 0) {
    v1 = 96;
} else {
    mem[ptr3] = _returndatasize();
    mem[ptr3 + 32:+_returndatasize()] = returndata[0:+_returndatasize()];
    v1 = ptr3;
}
require(_memory(v1) >= 32);
v2 = _memory(v1 + 32) != 0;";
        let lines: Vec<String> = text.lines().map(str::to_string).collect();
        let want = "(success_1, returned_1) = t.call(x);
require(returned_1.length >= 32);
v2 = _word(returned_1, 0) != 0;";
        assert_eq!(answers_kept(lines.clone()).join("\n"), want);
        let taken = text
            .replace(
                "    mem[ptr3] = _returndatasize();",
                "    ptr3 = _free(); _take(ptr3 + 64);\n    _store(ptr3, _returndatasize());",
            )
            .replace(
                "    mem[ptr3 + 32:+_returndatasize()] = returndata[0:+_returndatasize()];",
                "    _copy_returned(ptr3 + 32, 0x0, _returndatasize());",
            );
        let lines_taken: Vec<String> = taken.lines().map(str::to_string).collect();
        assert_eq!(answers_kept(lines_taken).join("\n"), want);
        let mut handed = lines.clone();
        handed.push("f(v1);".to_string());
        let kept = answers_kept(handed).join("\n");
        assert!(kept.contains("\nv1 = _place(returned_1);\n"), "{kept}");
        assert!(kept.ends_with("f(v1);"), "{kept}");
    }

    #[test]
    fn a_write_to_memory_just_before_a_failure_is_left_out() {
        let text = "mem[ptr1] = a;\nx = 1;\nmem[ptr1 + 4] = 32;\nmem[ptr1 + 68:+2] = \"no\";\nrevert(\"no\");";
        let lines: Vec<String> = text.lines().map(str::to_string).collect();
        let want = "mem[ptr1] = a;\nx = 1;\nrevert(\"no\");";
        assert_eq!(without_writes_before_failure(lines).join("\n"), want);
    }

    #[test]
    fn a_block_taken_and_written_but_never_read_is_left_out() {
        let text = "ptr1 = _free(); _take(ptr1 + 96);\n_store(ptr1, 3);\n_store(ptr1 + 32, a);\nptr2 = _free(); _take(ptr2 + 32);\n_store(ptr2, b);\nf(ptr2);";
        let lines: Vec<String> = text.lines().map(str::to_string).collect();
        let want = "ptr2 = _free(); _take(ptr2 + 32);\n_store(ptr2, b);\nf(ptr2);";
        assert_eq!(without_unread_blocks(lines).join("\n"), want);
    }

    #[test]
    fn a_decoder_test_is_told_from_a_test_the_author_wrote() {
        assert!(decoder_test("require(_calldata(4) <= type(uint64).max);"));
        assert!(decoder_test(
            "require(!(_calldata(36) + 36 + v1 > msg.data.length));"
        ));
        assert!(!decoder_test("require(v1 <= type(uint64).max);"));
        let fits = "require(_calldata(4) + 4 + (_calldata(_calldata(4) + 4) << 5) + 32 <= msg.data.length);";
        assert!(decoder_test(fits));
        assert!(decoder_test("require(msg.data.length >= 36);"));
        assert!(!decoder_test("require(_calldata(_calldata(4) + 4) <= 8);"));
        assert!(!decoder_test("require(amount <= msg.data.length);"));
    }

    #[test]
    fn a_named_error_is_declared_and_an_unnamed_one_is_not() {
        let text = "revert Unauthorized();\n_fail(abi.encodeWithSelector(bytes4(0x12345678)));";
        assert_eq!(errors_declared(text), "    error Unauthorized();\n\n");
    }

    #[test]
    fn brackets_come_off_one_returned_value_only() {
        assert_eq!(one_value("    return (a[b(c)]);"), "    return a[b(c)];");
        assert_eq!(one_value("    return (a, b);"), "    return (a, b);");
        assert_eq!(one_value("    return (a) + (b);"), "    return (a) + (b);");
    }
}
