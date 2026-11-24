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
        (payable || code != "require(msg.value == 0);") && !(external && sized)
    };
    let lines: Vec<String> = f.code.lines().filter(own).map(one_value).collect();
    let mut lines = without_dead_stores(held_strings(lines));
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
    let text = returned_as_declared(f, &declared, &text);
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
        let length = code.strip_prefix(&format!("mem[{block}] = "));
        let length = length.and_then(|l| l.strip_suffix(';')?.parse::<usize>().ok());
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
    }
    lines.retain(|l| !l.is_empty());
    lines
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
    let mut reads = text.match_indices("mem[");
    reads.any(|(at, _)| text[at + 4..].starts_with(|c: char| c.is_ascii_digit()))
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
    if outside.contains(['+', '-', '*', '/', '%']) || bare.contains("checked(") {
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
fn returned_as_declared(f: &Function, declared: &str, text: &str) -> String {
    let [wanted] = f.returns.as_slice() else {
        return text.to_string();
    };
    let is = |ty: &str, name: &str| declared.contains(&format!("        {ty} {name};\n"));
    let fixed = text.lines().map(|line| {
        let code = line.trim_start();
        let indent = &line[..line.len() - code.len()];
        let value = code
            .strip_prefix("return ")
            .and_then(|c| c.strip_suffix(';'));
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
        if text.contains(&format!("{name} = _pointer(")) {
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

fn helpers(c: &Contract, plain: &BTreeSet<usize>, clean: bool) -> BTreeSet<usize> {
    let at = |pc: usize| {
        c.functions
            .iter()
            .position(|f| f.pc == pc && f.kind == FnKind::Internal)
    };
    let mut found = BTreeSet::new();
    let external = |i: &&usize| match c.functions[**i].kind {
        FnKind::External => true,
        FnKind::Fallback | FnKind::Receive => clean,
        _ => false,
    };
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

/* What plain Solidity has no word for, written once and called by name: a string taken
as the place it lies at and back, a word of the data a call gave back, and how much it
gave. */
const HELPERS: [(&str, &str); 6] = [
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
    let mut out = format!("// SPDX-License-Identifier: UNLICENSED\npragma solidity {pragma};\n\n");
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
    let clean = plain.is_some_and(|p| p.clean);
    if !clean {
        out.push_str("    fallback() external payable {\n        _original();\n    }\n\n");
    }
    if let Some(plain) = plain {
        let unnamed = |f: &Function| matches!(f.kind, FnKind::Fallback | FnKind::Receive);
        let all = c.functions.iter().enumerate();
        let own = all.filter(|(i, f)| clean && unnamed(f) && plain.functions.contains(i));
        let mut printed: Vec<usize> = own.map(|(i, _)| i).collect();
        printed.extend(helpers(c, plain.functions, clean));
        for i in printed {
            let f = &c.functions[i];
            let start = out.len();
            let head = crate::decompile::fmt_function_header(f);
            let head = widened(head, plain.relaxed.get(&i));
            out.push_str(&format!("{head}{}    }}\n\n", body(c, f, plain)));
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
    let mut shape = floor.shape.clone();
    let kinds = [
        FnKind::External,
        FnKind::Internal,
        FnKind::Fallback,
        FnKind::Receive,
    ];
    let printable = |f: &&Function| !f.inlined && kinds.contains(&f.kind);
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
    let mut relaxed: BTreeMap<usize, Reach> = BTreeMap::new();
    for _ in 0..48 {
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
