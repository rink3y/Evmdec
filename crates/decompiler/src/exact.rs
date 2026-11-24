use crate::opcode as op;
use crate::U256;
use std::collections::BTreeMap;

/* Bytecode turned into an assembly block instruction by instruction, with no analysis in
between. It is the form every function can fall back to, so nothing here may guess.

The machine's stack is kept in memory below `SHIFT` and the program's own memory starts
at `SHIFT`. Variables would be simpler, but a compiler reaches only sixteen of them. */
const SHIFT: u64 = 0x8000;
const FAR: &str = "0xffffffff";
const LEAF: usize = 4;

struct Stack {
    top: i64,
    constants: BTreeMap<i64, U256>,
}

fn home(index: i64) -> String {
    match index {
        0 => "sp".to_string(),
        i if i > 0 => format!("add(sp, {:#x})", 32 * i),
        i => format!("sub(sp, {:#x})", -32 * i),
    }
}

impl Stack {
    fn pop(&mut self) -> String {
        self.top -= 1;
        match self.constants.remove(&self.top) {
            Some(c) => c.to_hex(),
            None => format!("mload({})", home(self.top)),
        }
    }

    fn constant(&self, depth: i64) -> Option<U256> {
        self.constants.get(&(self.top - 1 - depth)).copied()
    }

    fn push_constant(&mut self, value: U256) {
        self.constants.insert(self.top, value);
        self.top += 1;
    }

    fn push(&mut self, value: &str, out: &mut Vec<String>) {
        out.push(format!("mstore({}, {value})", home(self.top)));
        self.top += 1;
    }

    fn dup(&mut self, n: i64, out: &mut Vec<String>) {
        let from = self.top - n;
        match self.constants.get(&from).copied() {
            Some(c) => self.push_constant(c),
            None => self.push(&format!("mload({})", home(from)), out),
        }
    }

    fn swap(&mut self, n: i64, out: &mut Vec<String>) {
        let (a, b) = (self.top - 1, self.top - 1 - n);
        match (self.constants.remove(&a), self.constants.remove(&b)) {
            (Some(x), Some(y)) => {
                self.constants.insert(a, y);
                self.constants.insert(b, x);
            }
            (Some(x), None) => {
                out.push(format!("mstore({}, mload({}))", home(a), home(b)));
                self.constants.insert(b, x);
            }
            (None, Some(y)) => {
                out.push(format!("mstore({}, mload({}))", home(b), home(a)));
                self.constants.insert(a, y);
            }
            (None, None) => out.push(format!(
                "{{ let t := mload({}) mstore({}, mload({})) mstore({}, t) }}",
                home(a),
                home(a),
                home(b),
                home(b)
            )),
        }
    }

    fn settled(&self) -> Vec<String> {
        let stores = self.constants.iter();
        let mut out: Vec<String> = stores
            .map(|(i, c)| format!("mstore({}, {})", home(*i), c.to_hex()))
            .collect();
        if self.top != 0 {
            out.push(format!("sp := {}", home(self.top)));
        }
        out
    }
}

fn memory_operands(o: u8) -> &'static [(usize, Option<usize>)] {
    match o {
        op::MLOAD | op::MSTORE | op::MSTORE8 => &[(0, None)],
        op::KECCAK256 | op::RETURN | op::REVERT | op::LOG0..=op::LOG4 => &[(0, Some(1))],
        op::CALLDATACOPY | op::RETURNDATACOPY => &[(0, Some(2))],
        op::EXTCODECOPY => &[(1, Some(3))],
        op::MCOPY => &[(0, Some(2)), (1, Some(2))],
        op::CREATE | op::CREATE2 => &[(1, Some(2))],
        op::CALL | op::CALLCODE => &[(3, Some(4)), (5, Some(6))],
        op::DELEGATECALL | op::STATICCALL => &[(2, Some(3)), (4, Some(5))],
        _ => &[],
    }
}

fn placed(o: u8, mut operands: Vec<String>) -> Vec<String> {
    for (at, length) in memory_operands(o) {
        operands[*at] = match length {
            Some(n) => format!("ml({}, {})", operands[*at], operands[*n]),
            None => format!("m({})", operands[*at]),
        };
    }
    operands
}

struct Translation<'a> {
    code: &'a [u8],
    end: usize,
    prevrandao: bool,
    reads_code: bool,
    reads_size: bool,
}

fn word_at(code: &[u8], from: usize) -> U256 {
    let mut bytes = [0u8; 32];
    for (i, b) in bytes.iter_mut().enumerate() {
        *b = code.get(from.saturating_add(i)).copied().unwrap_or(0);
    }
    U256::from_be_bytes(&bytes)
}

impl Translation<'_> {
    fn copy_code(&mut self, st: &mut Stack, out: &mut Vec<String>) {
        let known = st.constant(1).zip(st.constant(2));
        let (dest, from, len) = (st.pop(), st.pop(), st.pop());
        let fixed = known.and_then(|(from, len)| from.as_usize().zip(len.as_usize()));
        let Some((from, len)) = fixed.filter(|(_, len)| *len <= self.code.len() + 64) else {
            self.reads_code = true;
            out.push(format!("cc(ml({dest}, {len}), {from}, {len})"));
            return;
        };
        if len == 0 {
            return;
        }
        let mut line = format!("{{ let d := ml({dest}, {len:#x})");
        for k in (0..len / 32 * 32).step_by(32) {
            let word = word_at(self.code, from + k).to_hex();
            line.push_str(&format!(" mstore(add(d, {k:#x}), {word})"));
        }
        let rest = len % 32;
        if rest != 0 {
            let k = len - rest;
            let keep = U256::MAX >> (8 * rest as u32);
            let word = word_at(self.code, from + k) & !keep;
            let at = format!("add(d, {k:#x})");
            let merged = format!("or(and(mload({at}), {}), {})", keep.to_hex(), word.to_hex());
            line.push_str(&format!(" mstore({at}, {merged})"));
        }
        line.push_str(" }");
        out.push(line);
    }

    fn block(&mut self, start: usize) -> Vec<String> {
        let code = self.code;
        let mut st = Stack {
            top: 0,
            constants: BTreeMap::new(),
        };
        let mut out = Vec::new();
        let mut pc = start + usize::from(code[start] == op::JUMPDEST);
        loop {
            if pc >= self.end {
                out.push("stop()".to_string());
                return out;
            }
            let o = code[pc];
            let at = pc;
            pc += 1;
            match o {
                op::JUMPDEST => {
                    out.extend(st.settled());
                    out.push(format!("ip := {at:#x}"));
                    return out;
                }
                op::PUSH0 => st.push_constant(U256::ZERO),
                op::PUSH1..=op::PUSH32 => {
                    let n = usize::from(o - op::PUSH1) + 1;
                    st.push_constant(word_at(code, pc) >> (8 * (32 - n as u32)));
                    pc += n;
                }
                0x80..=0x8f => st.dup(i64::from(o - 0x80) + 1, &mut out),
                0x90..=0x9f => st.swap(i64::from(o - 0x90) + 1, &mut out),
                op::POP => {
                    st.pop();
                }
                op::PC => st.push_constant(U256::from(at)),
                op::CODESIZE => st.push_constant(U256::from(code.len())),
                op::MSIZE => {
                    self.reads_size = true;
                    st.push("ms()", &mut out);
                }
                op::CODECOPY => self.copy_code(&mut st, &mut out),
                op::JUMP => {
                    out.push(format!("ip := {}", st.pop()));
                    out.extend(st.settled());
                    return out;
                }
                op::JUMPI => {
                    let (target, taken) = (st.pop(), st.pop());
                    let moved = st.settled().join(" ");
                    out.push(format!("if {taken} {{ ip := {target} {moved} continue }}"));
                }
                _ => {
                    let known = op::info(o).filter(|_| o != op::INVALID);
                    let Some(info) = known else {
                        out.push("invalid()".to_string());
                        return out;
                    };
                    let name = match o {
                        0x44 if !self.prevrandao => "difficulty".to_string(),
                        _ => info.name.to_ascii_lowercase(),
                    };
                    let operands: Vec<String> = (0..info.pops).map(|_| st.pop()).collect();
                    let call = format!("{name}({})", placed(o, operands).join(", "));
                    match info.pushes {
                        0 => out.push(call),
                        _ => st.push(&call, &mut out),
                    }
                    let ends = [op::STOP, op::RETURN, op::REVERT, op::SELFDESTRUCT];
                    if ends.contains(&o) {
                        return out;
                    }
                }
            }
        }
    }
}

/* A chain of comparisons would cost one test per block on every jump. Halving the range
keeps a jump at a dozen tests in the largest contract. The tests are `if` and never
`switch`: a switch keeps its value on the compiler's stack for as long as a case runs,
and a dozen of them nested leave no room to reach a variable. Every leaf ends in `done`,
so nothing runs on into the next test, and a key no leaf took ends in `missed`. */
fn tree(
    on: &str,
    keys: &[usize],
    leaf: &dyn Fn(usize) -> Vec<String>,
    (done, missed): (&str, &str),
    depth: usize,
) -> String {
    let pad = "    ".repeat(depth);
    if keys.len() <= LEAF {
        let mut text = String::new();
        for key in keys {
            let lines = leaf(*key).into_iter();
            let body: String = lines.map(|l| format!("{pad}    {l}\n")).collect();
            text.push_str(&format!(
                "{pad}if eq({on}, {key:#x}) {{\n{body}{pad}    {done}\n{pad}}}\n"
            ));
        }
        return text;
    }
    let (low, high) = keys.split_at(keys.len() / 2);
    let below = tree(on, low, leaf, (done, missed), depth + 1);
    let above = tree(on, high, leaf, (done, missed), depth);
    let edge = high[0];
    // A key in the lower half that no leaf took is a key that is not there. Going
    // round again with it would never end.
    format!("{pad}if lt({on}, {edge:#x}) {{\n{below}{pad}    {missed}\n{pad}}}\n{above}")
}

fn destinations(code: &[u8], end: usize) -> Vec<usize> {
    let mut found = vec![0];
    let mut pc = 0;
    while pc < end {
        let o = code[pc];
        if o == op::JUMPDEST && pc != 0 {
            found.push(pc);
        }
        pc += 1;
        if (op::PUSH1..=op::PUSH32).contains(&o) {
            pc += usize::from(o - op::PUSH1) + 1;
        }
    }
    found
}

const PLACES: &str = "            function m(x) -> y {
                if gt(x, FAR) { invalid() }
                y := add(x, SHIFT)
            }
            function ml(x, n) -> y {
                if n { if gt(x, FAR) { invalid() } }
                y := add(x, SHIFT)
            }
";

const SIZE: &str = "            function ms() -> s {
                s := msize()
                if lt(s, SHIFT) { s := SHIFT }
                s := sub(s, SHIFT)
            }
";

const COPY: &str = "            function cc(d, o, n) {
                for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                    let p := add(o, i)
                    if lt(p, o) { p := not(0) }
                    mstore8(add(d, i), byte(and(p, 31), cw(shr(5, p))))
                }
            }
";

// `prevrandao` is false for a compiler that only knows the instruction by its old name.
#[must_use]
pub fn translate(code: &[u8], end: usize, prevrandao: bool) -> String {
    if code.is_empty() {
        return "            stop()\n".to_string();
    }
    let mut t = Translation {
        code,
        end: end.min(code.len()),
        prevrandao,
        reads_code: false,
        reads_size: false,
    };
    let starts = destinations(code, t.end);
    let blocks: BTreeMap<usize, Vec<String>> = starts.iter().map(|s| (*s, t.block(*s))).collect();
    let body = |start: usize| blocks[&start].clone();
    let shift = format!("{SHIFT:#x}");
    let named = |text: &str| text.replace("SHIFT", &shift).replace("FAR", FAR);
    let mut out = named(PLACES);
    if t.reads_size {
        out.push_str(&named(SIZE));
    }
    if t.reads_code {
        let words: Vec<usize> = (0..code.len().div_ceil(32)).collect();
        let word = |i: usize| vec![format!("w := {}", word_at(code, 32 * i).to_hex())];
        out.push_str("            function cw(i) -> w {\n");
        out.push_str(&tree("i", &words, &word, ("leave", "leave"), 4));
        out.push_str("            }\n");
        out.push_str(COPY);
    }
    out.push_str("            let sp := 0\n            let ip := 0\n            for {} 1 {} {\n");
    out.push_str(&tree("ip", &starts, &body, ("continue", "invalid()"), 4));
    out.push_str("                invalid()\n");
    out.push_str("            }\n");
    out
}
