use crate::emit::{calldata_word_index, MappingLayout, SlotSpace};
use crate::expr::{self, ExprId, Node};
use crate::lift::{self, Lifted, Stmt, Term};
use crate::opcode as op;
use crate::ssa::{self, Shape, ShapeStep};
use crate::u256::U256;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum Ty {
    #[default]
    Unknown,
    Bool,
    Address,
    Uint(u32),
    Int(u32),
    Bytes(u32),
    Conflict,
}

impl Ty {
    pub fn join(self, other: Ty) -> Ty {
        match (self, other) {
            (Ty::Unknown, x) | (x, Ty::Unknown) => x,
            (Ty::Conflict, _) | (_, Ty::Conflict) => Ty::Conflict,
            (Ty::Bool, Ty::Bool) => Ty::Bool,
            (Ty::Bool, Ty::Uint(n)) | (Ty::Uint(n), Ty::Bool) => {
                if n <= 8 {
                    Ty::Bool
                } else {
                    Ty::Uint(n)
                }
            }
            (Ty::Address, Ty::Address) => Ty::Address,
            (Ty::Address, Ty::Uint(n)) | (Ty::Uint(n), Ty::Address) => {
                if n <= 160 {
                    Ty::Address
                } else {
                    Ty::Conflict
                }
            }
            (Ty::Uint(a), Ty::Uint(b)) => Ty::Uint(a.max(b)),
            (Ty::Int(a), Ty::Int(b)) => Ty::Int(a.max(b)),
            (Ty::Int(a), Ty::Uint(b)) | (Ty::Uint(b), Ty::Int(a)) => Ty::Int(a.max(b)),
            (Ty::Bytes(a), Ty::Bytes(b)) => Ty::Bytes(a.max(b)),
            _ => Ty::Conflict,
        }
    }

    pub fn solidity(&self) -> Option<String> {
        match *self {
            Ty::Bool => Some("bool".into()),
            Ty::Address => Some("address".into()),
            Ty::Uint(1) => Some("bool".into()),
            Ty::Uint(n) if n.is_multiple_of(8) && n < 256 => Some(format!("uint{}", n)),
            Ty::Int(n) if n.is_multiple_of(8) && n <= 256 => Some(format!("int{}", n)),
            Ty::Bytes(n) if (1..=32).contains(&n) => Some(format!("bytes{}", n)),
            _ => None,
        }
    }

    #[must_use]
    pub fn declared(name: &str) -> Option<Ty> {
        let width = |prefix: &str| {
            name.strip_prefix(prefix)
                .and_then(|n| n.parse::<u32>().ok())
        };
        match name {
            "address" | "address payable" => Some(Ty::Address),
            "bool" => Some(Ty::Bool),
            "int" => Some(Ty::Int(256)),
            _ => {
                if let Some(n) = width("uint") {
                    (n.is_multiple_of(8) && n > 0 && n < 256).then_some(Ty::Uint(n))
                } else if let Some(n) = width("int") {
                    (n.is_multiple_of(8) && n > 0 && n <= 256).then_some(Ty::Int(n))
                } else {
                    width("bytes")
                        .filter(|n| (1..=32).contains(n))
                        .map(Ty::Bytes)
                }
            }
        }
    }

    pub fn of_mask(bits: u32) -> Ty {
        match bits {
            0 => Ty::Unknown,
            1 => Ty::Bool,
            160 => Ty::Address,
            n => Ty::Uint(n),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Loc {
    Var {
        scope: usize,
        id: u32,
    },
    Arg {
        unit: usize,
        slot: u32,
    },
    Ret {
        unit: usize,
        index: u16,
    },
    Param {
        scope: usize,
        word: u32,
    },
    Slot(Shape),
    Field {
        shape: Shape,
        bit_offset: u32,
        bits: u32,
    },
    Key(Shape),
    Output {
        scope: usize,
        seq: u32,
        word: u32,
    },
}

impl Loc {
    fn is_storage(&self) -> bool {
        matches!(self, Loc::Slot(_) | Loc::Field { .. } | Loc::Key(_))
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Flags {
    arith: bool,
    scaled: bool,
    account: bool,
    tested: bool,
    one: bool,
    other: bool,
    cast: u32,
    signed_cmp: bool,
    unsigned_cmp: bool,
    arith_def: bool,
    word32: bool,
}

fn cast_checked(cast: u32, bits: u32) -> bool {
    bits.is_multiple_of(8) && bits / 8 < 32 && cast & (1 << (bits / 8)) != 0
}

impl Flags {
    fn checked(&self, bits: u32) -> bool {
        cast_checked(self.cast, bits)
    }

    fn absorb(&mut self, other: Flags) {
        self.arith |= other.arith;
        self.scaled |= other.scaled;
        self.account |= other.account;
        self.tested |= other.tested;
        self.cast |= other.cast;
        self.signed_cmp |= other.signed_cmp;
        self.unsigned_cmp |= other.unsigned_cmp;
        self.word32 |= other.word32;
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ClassInfo {
    pub ty: Ty,
    pub arith: bool,
    pub account: bool,
    pub signed_cmp: bool,
    pub unsigned_cmp: bool,
    pub arith_def: bool,
    cast: u32,
}

impl ClassInfo {
    #[must_use]
    pub fn checked(&self, bits: u32) -> bool {
        cast_checked(self.cast, bits)
    }
}

#[derive(Clone, Debug, Default)]
struct Class {
    hints: Ty,
    // A signed comparison with zero says the value is treated as signed here.
    // It does not say everything stored into it is signed.
    weak: Ty,
    flags: Flags,
    storage: bool,
    defs: Vec<(ExprId, usize)>,
    sources: Vec<usize>,
    from_defs: Ty,
    resolved: Ty,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Evidence {
    Flowing,
    Final,
}

const MAX_VISITED: usize = 50_000;
const MAX_ROUNDS: usize = 8;
const MAX_TYPE_DEPTH: u32 = 6;

#[derive(Clone, Debug)]
pub struct TypeEnv {
    layout: MappingLayout,
    // Vyper validates by range checks and never masks a value to its declared width.
    // A mask or shift there is the program's own arithmetic.
    vyper: bool,
    debug: bool,
    ids: HashMap<Loc, usize>,
    classes: Vec<Class>,
    // Sequence numbers are per lifted graph, so the function scopes them.
    callee_of: HashMap<(usize, u32), usize>,
    results_len: HashMap<usize, Option<usize>>,
}

pub type Declared = (usize, u32, Ty);

#[must_use]
pub fn declared_words(params: &[String]) -> Vec<(u32, Ty)> {
    let mut out = Vec::new();
    for (i, p) in params.iter().enumerate() {
        let dynamic = p == "bytes" || p == "string" || p.ends_with("[]");
        if p.starts_with('(') || (p.ends_with(']') && !dynamic) {
            break;
        }
        if let Some(t) = Ty::declared(p) {
            out.push((i as u32, t));
        }
    }
    out
}

pub fn solve(
    functions: &[(usize, &Lifted)],
    layout: MappingLayout,
    declared: &[Declared],
) -> TypeEnv {
    let mut env = TypeEnv {
        layout,
        vyper: layout == MappingLayout::Vyper,
        debug: std::env::var("EVMDEC_DEBUG_TYPES").is_ok(),
        ids: HashMap::new(),
        classes: Vec::new(),
        callee_of: HashMap::new(),
        results_len: HashMap::new(),
    };
    let units: HashMap<usize, &Lifted> = functions.iter().copied().collect();
    let arity = |pc: usize| units.get(&pc).map(|l| ssa::arity(l));
    for (pc, l) in functions {
        for site in ssa::call_sites(l, arity) {
            env.callee_of.insert((*pc, site.seq), site.callee);
            let n = site.results.len();
            env.results_len
                .entry(site.callee)
                .and_modify(|m| {
                    if *m != Some(n) {
                        *m = None;
                    }
                })
                .or_insert(Some(n));
        }
    }
    for (pc, l) in functions {
        env.index(*pc, l, arity);
    }
    for (pc, word, ty) in declared {
        env.hint(
            Some(Loc::Param {
                scope: *pc,
                word: *word,
            }),
            *ty,
        );
    }
    env.propagate();
    env.run();
    if env.keys_are_words() {
        env.propagate();
        env.run();
    }
    if env.debug {
        env.debug_dump();
    }
    env
}

impl TypeEnv {
    fn intern(&mut self, loc: Loc) -> usize {
        if let Some(i) = self.ids.get(&loc) {
            return *i;
        }
        let i = self.classes.len();
        // A packed field is as wide as its mask. Without this start a narrow number
        // had no type until some other use gave it one, and often none did.
        let hints = match &loc {
            Loc::Field { bits: 160, .. } => Ty::Address,
            Loc::Field { bits, .. } if (16..=128).contains(bits) && bits % 8 == 0 => {
                Ty::Uint(*bits)
            }
            _ => Ty::Unknown,
        };
        self.classes.push(Class {
            storage: loc.is_storage(),
            hints,
            ..Class::default()
        });
        self.ids.insert(loc, i);
        i
    }

    fn hint(&mut self, loc: Option<Loc>, t: Ty) {
        if let Some(loc) = loc {
            let i = self.intern(loc);
            self.classes[i].hints = self.classes[i].hints.join(t);
        }
    }

    fn weak(&mut self, loc: Option<Loc>, t: Ty) {
        if let Some(loc) = loc {
            let i = self.intern(loc);
            self.classes[i].weak = self.classes[i].weak.join(t);
        }
    }

    fn flag(&mut self, loc: Option<Loc>, f: impl Fn(&mut Flags)) {
        if let Some(loc) = loc {
            let i = self.intern(loc);
            f(&mut self.classes[i].flags);
        }
    }

    fn arith(&mut self, e: ExprId, scope: usize, by: u8) {
        let loc = self.location(e, scope);
        if self.debug {
            if let Some(l) = &loc {
                eprintln!("[types] arith on {:?} by {}", l, op::name(by));
            }
        }
        let scaled = matches!(
            by,
            op::MUL | op::DIV | op::SDIV | op::MOD | op::SMOD | op::EXP | op::MULMOD
        );
        self.flag(loc, |f| {
            f.arith = true;
            f.scaled |= scaled;
        });
    }

    fn def(&mut self, loc: Loc, val: ExprId, scope: usize) {
        let i = self.intern(loc);
        if let Some(src) = self.copy_source(val, scope) {
            let j = self.intern(src);
            if i != j && !self.classes[i].sources.contains(&j) {
                self.classes[i].sources.push(j);
            }
        }
        self.classes[i].defs.push((val, scope));
    }

    fn propagate(&mut self) {
        let mut work: Vec<usize> = (0..self.classes.len()).collect();
        while let Some(i) = work.pop() {
            let (hints, weak, flags) = (
                self.classes[i].hints,
                self.classes[i].weak,
                self.classes[i].flags,
            );
            let sources = self.classes[i].sources.clone();
            for j in sources {
                let c = &mut self.classes[j];
                let before = (c.hints, c.weak, c.flags);
                c.hints = c.hints.join(hints);
                if !c.storage {
                    c.weak = c.weak.join(weak);
                }
                c.flags.absorb(flags);
                if (c.hints, c.weak, c.flags) != before {
                    work.push(j);
                }
            }
        }
    }

    fn copy_source(&mut self, e: ExprId, scope: usize) -> Option<Loc> {
        if let Some(loc) = self.location(e, scope) {
            return Some(loc);
        }
        if let Node::Op(op::AND, v) = expr::node(e) {
            for (x, m) in [(v[0], v[1]), (v[1], v[0])] {
                if let Some(m) = expr::as_const(m) {
                    if m.is_low_mask() {
                        let loc = self.location(x, scope)?;
                        self.hint(Some(loc.clone()), Ty::of_mask(m.bits()));
                        return Some(loc);
                    }
                }
            }
        }
        None
    }

    #[must_use]
    pub fn location(&self, e: ExprId, scope: usize) -> Option<Loc> {
        if let Some(field) = ssa::field_read(e).filter(|_| !self.vyper) {
            let path = ssa::slot_path(field.key, self.layout)?;
            return Some(Loc::Field {
                shape: path.shape(SlotSpace::Persistent),
                bit_offset: field.bit_offset,
                bits: field.bits,
            });
        }
        match expr::node(e) {
            Node::Var(id) => Some(Loc::Var { scope, id }),
            Node::Arg(slot) => Some(Loc::Arg { unit: scope, slot }),
            Node::CallDataLoad(off) | Node::CopiedWord(op::CALLDATACOPY, off, _) => {
                calldata_word_index(off).map(|word| Loc::Param { scope, word })
            }
            Node::SLoad(key, transient, _) => {
                let path = ssa::slot_path(key, self.layout)?;
                Some(Loc::Slot(path.shape(ssa::space_of(transient))))
            }
            Node::IntRet(seq, index) => self
                .callee_of
                .get(&(scope, seq))
                .map(|unit| Loc::Ret { unit: *unit, index }),
            Node::ReturnData(seq, off) => expr::as_const(off)
                .filter(|o| o.fits_u64() && o.low_u64().is_multiple_of(32) && o.low_u64() < 1 << 16)
                .map(|o| Loc::Output {
                    scope,
                    seq,
                    word: (o.low_u64() / 32) as u32,
                }),
            _ => None,
        }
    }

    fn index(&mut self, pc: usize, l: &Lifted, arity: impl Fn(usize) -> Option<usize>) {
        for (var, vals) in ssa::phi_defs(l) {
            let Node::Var(id) = expr::node(var) else {
                continue;
            };
            for val in vals {
                self.def(Loc::Var { scope: pc, id }, val, pc);
            }
        }
        if l.ret_slot.is_some() {
            for slot in 0..ssa::arity(l) {
                self.intern(Loc::Arg {
                    unit: pc,
                    slot: slot as u32,
                });
            }
        }
        for site in ssa::call_sites(l, &arity) {
            let k = arity(site.callee).unwrap_or(0);
            for (idx, val) in site.args {
                if (idx as usize) < k {
                    let slot = (k - 1 - idx as usize) as u32;
                    self.def(
                        Loc::Arg {
                            unit: site.callee,
                            slot,
                        },
                        val,
                        pc,
                    );
                }
            }
        }
        let consumed = self.results_len.get(&pc).copied().flatten();
        for vals in ssa::returns(l) {
            if consumed != Some(vals.len()) {
                continue;
            }
            for (j, val) in vals.iter().enumerate() {
                self.def(
                    Loc::Ret {
                        unit: pc,
                        index: j as u16,
                    },
                    *val,
                    pc,
                );
            }
        }
        for assigns in l.edge_assigns.values() {
            for (_, val) in assigns {
                self.uses(*val, pc, None);
            }
        }
        for nd in &l.nodes {
            for s in &nd.stmts {
                self.index_stmt(s, pc);
            }
            self.index_layouts(&nd.stmts, pc);
            if let Term::SelfDestruct(a) = &nd.term {
                self.account(*a, pc);
            }
            if let Term::Branch {
                cond, t: Some(t), ..
            } = &nd.term
            {
                if lift::always_reverts(l, *t) {
                    self.shift_validator(*cond, pc);
                }
            }
            let conds: HashSet<ExprId> = condition_exprs(nd).into_iter().collect();
            for root in lift::roots(nd) {
                let context = if root.payload {
                    Some(op::OR)
                } else if conds.contains(&root.expr) {
                    Some(op::ISZERO)
                } else {
                    None
                };
                self.uses(root.expr, pc, context);
            }
        }
    }

    fn index_stmt(&mut self, s: &Stmt, pc: usize) {
        match s {
            Stmt::SStore {
                key,
                val,
                transient,
                ..
            } => {
                let Some(path) = ssa::slot_path(*key, self.layout) else {
                    return;
                };
                let space = ssa::space_of(*transient);
                let shape = path.shape(space);
                self.note_keys(&path, space, pc);
                let fields = match self.vyper {
                    true => Vec::new(),
                    false => ssa::field_writes(*key, *val),
                };
                if fields.is_empty() {
                    self.def(Loc::Slot(shape.clone()), *val, pc);
                }
                for w in fields {
                    let field = Loc::Field {
                        shape: shape.clone(),
                        bit_offset: w.bit_offset,
                        bits: w.bits,
                    };
                    self.def(field, w.value, pc);
                }
            }
            Stmt::Call {
                addr,
                value,
                input,
                input_head,
                ..
            } => {
                self.account(*addr, pc);
                if let Some(v) = value {
                    self.arith(*v, pc, op::CALLVALUE);
                }
                if expr::as_const(*addr) == Some(U256::ONE) {
                    let words: &[ExprId] = input.as_deref().unwrap_or(input_head);
                    for i in [0, 2, 3] {
                        if let Some(w) = words.get(i) {
                            self.word32(*w, pc);
                        }
                    }
                }
            }
            Stmt::Copy {
                kind: op::EXTCODECOPY,
                addr: Some(a),
                ..
            } => self.account(*a, pc),
            _ => {}
        }
    }

    fn index_layouts(&mut self, stmts: &[Stmt], scope: usize) {
        let words: Vec<(Option<ExprId>, U256, ExprId)> = stmts
            .iter()
            .filter_map(|s| match s {
                Stmt::MStore {
                    off,
                    val,
                    width: 32,
                    ..
                } => {
                    let (base, at) = expr::split_offset(*off);
                    Some((base, at, *val))
                }
                _ => None,
            })
            .collect();
        let at = |base: Option<ExprId>, addr: U256| {
            words
                .iter()
                .find(|(b, a, _)| *b == base && *a == addr)
                .map(|(_, _, v)| *v)
        };
        let step = |a: U256, by: u64| a.wrapping_add(U256::from_u64(by));
        let top_byte = |e: ExprId| match expr::node(e) {
            Node::Op(op::SHL, v) => expr::as_const(v[0]) == Some(U256::from_u64(248)),
            Node::Const(c) => !c.is_zero() && c.trailing_zeros() >= 248,
            _ => false,
        };
        let prefix = U256::from_u64(0x1901) << 240;
        for (base, addr, val) in &words {
            let found = match expr::as_const(*val) {
                Some(c) if c == U256::from_u64(65) => {
                    let v = at(*base, step(*addr, 96));
                    v.filter(|v| top_byte(*v))
                        .and(at(*base, step(*addr, 32)).zip(at(*base, step(*addr, 64))))
                }
                Some(c) if c == prefix => at(*base, step(*addr, 2)).zip(at(*base, step(*addr, 34))),
                _ => None,
            };
            if let Some((first, second)) = found {
                self.word32(first, scope);
                self.word32(second, scope);
            }
        }
    }

    fn account(&mut self, e: ExprId, scope: usize) {
        let inner = match expr::node(e) {
            Node::Op(op::AND, v) if expr::as_const(v[1]) == Some(expr::mask_bits(160)) => v[0],
            Node::Op(op::AND, v) if expr::as_const(v[0]) == Some(expr::mask_bits(160)) => v[1],
            _ => e,
        };
        let loc = self.location(inner, scope);
        self.hint(loc.clone(), Ty::Address);
        self.flag(loc, |f| f.account = true);
    }

    fn word32(&mut self, e: ExprId, scope: usize) {
        let loc = self.location(e, scope);
        self.flag(loc, |f| f.word32 = true);
    }

    fn note_keys(&mut self, path: &ssa::SlotPath, space: SlotSpace, scope: usize) {
        for (n, step) in path.steps.iter().enumerate() {
            if let ssa::Step::Key(k) = step {
                let prefix = ssa::SlotPath {
                    root: path.root,
                    steps: path.steps[..=n].to_vec(),
                };
                self.def(Loc::Key(prefix.shape(space)), *k, scope);
            }
        }
    }

    fn uses(&mut self, root: ExprId, scope: usize, context: Option<u8>) {
        let mut seen: HashSet<ExprId> = HashSet::new();
        let mut stack = vec![(root, context)];
        while let Some((x, parent)) = stack.pop() {
            if !seen.insert(x) || seen.len() > MAX_VISITED {
                continue;
            }
            let n = expr::node(x);
            match &n {
                Node::SLoad(key, transient, _) => {
                    if let Some(path) = ssa::slot_path(*key, self.layout) {
                        self.note_keys(&path, ssa::space_of(*transient), scope);
                    }
                }
                Node::Op(o, v) => self.op_use(*o, v, parent, scope),
                _ => {}
            }
            let o = match &n {
                Node::Op(o, _) => Some(*o),
                Node::Keccak(..) => Some(op::OR),
                _ => None,
            };
            stack.extend(expr::children(x).into_iter().map(|c| (c, o)));
        }
    }

    fn op_use(&mut self, o: u8, v: &[ExprId], parent: Option<u8>, scope: usize) {
        let konst = |e: ExprId| expr::as_const(e);
        match o {
            op::AND => self.mask_use(v, parent, scope),
            op::SIGNEXTEND => {
                if let Some(k) = konst(v[0]) {
                    if k < U256::from_u64(31) {
                        let loc = self.location(v[1], scope);
                        self.hint(loc, Ty::Int(8 * (k.low_u64() as u32 + 1)));
                    }
                }
            }
            op::ISZERO => match expr::node(v[0]) {
                Node::Op(op::ISZERO, w) => {
                    let loc = self.location(w[0], scope);
                    self.flag(loc, |f| f.tested = true);
                }
                Node::Op(op::SHR, _) => self.shift_validator(v[0], scope),
                _ => {}
            },
            op::EQ => {
                for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
                    if is_account(b) {
                        self.account(a, scope);
                    }
                    if is_word32(b) {
                        self.word32(a, scope);
                    }
                    if konst(b).is_some_and(|c| c.is_zero()) {
                        self.shift_validator(a, scope);
                    }
                }
            }
            op::LT | op::GT => {
                for (x, c, below) in [(v[0], v[1], o == op::LT), (v[1], v[0], o == op::GT)] {
                    match konst(c) {
                        Some(c) => self.bound_use(x, c, below, o, scope),
                        None => {
                            let loc = self.location(x, scope);
                            self.flag(loc, |f| f.unsigned_cmp = true);
                        }
                    }
                }
            }
            op::SLT | op::SGT => {
                for (x, c) in [(v[0], v[1]), (v[1], v[0])] {
                    let loc = self.location(x, scope);
                    let bound = konst(c);
                    match bound.and_then(signed_bound) {
                        Some(n) => self.hint(loc, Ty::Int(n)),
                        None => {
                            self.weak(loc.clone(), Ty::Int(256));
                            if bound.is_none_or(|c| !c.is_zero()) {
                                self.flag(loc, |f| f.signed_cmp = true);
                            }
                        }
                    }
                }
            }
            op::SDIV | op::SMOD | op::SAR => {
                // The first operand of a shift is the count, which is not signed.
                let signed = match o {
                    op::SAR => &v[1..],
                    _ => v,
                };
                for x in signed {
                    if konst(*x).is_none() {
                        let loc = self.location(*x, scope);
                        self.hint(loc.clone(), Ty::Int(256));
                        self.flag(loc, |f| f.signed_cmp = true);
                    }
                }
            }
            op::SUB | op::XOR if parent == Some(op::ISZERO) => {
                for (a, b) in [(v[0], v[1]), (v[1], v[0])] {
                    if is_account(b) {
                        self.account(a, scope);
                    }
                }
            }
            op::MUL if v.iter().any(|x| expr::is_boolean(*x)) => {}
            op::MUL | op::DIV if v.iter().any(|x| is_byte_shift(*x)) => {}
            op::ADD if v.iter().any(|x| is_masked_select(*x)) => {}
            op::ADD | op::SUB | op::MUL | op::DIV | op::MOD | op::EXP | op::ADDMOD | op::MULMOD => {
                for x in v {
                    self.arith(*x, scope, o);
                }
            }
            op::BALANCE | op::EXTCODESIZE | op::EXTCODEHASH => self.account(v[0], scope),
            op::SHL
                if konst(v[0]).is_some_and(|k| k.fits_u64() && (1..8).contains(&k.low_u64())) =>
            {
                self.arith(v[1], scope, o);
            }
            _ => {}
        }
    }

    fn mask_use(&mut self, v: &[ExprId], parent: Option<u8>, scope: usize) {
        if self.vyper {
            return;
        }
        let packing = matches!(parent, Some(op::OR) | Some(op::SHL) | Some(op::MUL));
        for (x, m) in [(v[0], v[1]), (v[1], v[0])] {
            let Some(m) = expr::as_const(m) else { continue };
            if m.is_low_mask() {
                if packing {
                    continue;
                }
                let loc = self.location(x, scope);
                if self.debug {
                    if let Some(l) = &loc {
                        eprintln!(
                            "[types] mask {} on {:?} under {:?}: {:?}",
                            m.bits(),
                            l,
                            parent.map(op::name),
                            expr::node(x)
                        );
                    }
                }
                self.hint(loc, Ty::of_mask(m.bits()));
            } else if let Some(bytes) = high_mask_bytes(m) {
                // Under an OR this mask keeps the rest of a packed word while one field is
                // written. It says nothing about the type of what it is applied to.
                if parent == Some(op::OR) {
                    continue;
                }
                let loc = self.location(x, scope);
                self.hint(loc, Ty::Bytes(bytes));
            }
        }
    }

    fn bound_use(&mut self, x: ExprId, c: U256, below: bool, by: u8, scope: usize) {
        let bound = if below {
            c.is_power_of_two().then(|| c.trailing_zeros())
        } else {
            c.is_low_mask().then(|| c.bits())
        };
        let typed_width = |n: u32| n == 1 || n == 160 || (n.is_multiple_of(8) && n > 0 && n < 256);
        match bound {
            Some(n) if self.vyper && typed_width(n) => {
                let loc = self.location(x, scope);
                self.hint(loc, Ty::of_mask(n));
            }
            Some(n) if n > 0 && n < 256 && n.is_multiple_of(8) => {
                let loc = self.location(x, scope);
                self.flag(loc, |f| f.cast |= 1 << (n / 8));
                self.arith(x, scope, by);
            }
            Some(_) => self.arith(x, scope, by),
            None => {
                let loc = self.location(x, scope);
                self.flag(loc, |f| f.unsigned_cmp = true);
                self.arith(x, scope, by);
            }
        }
    }

    fn shift_validator(&mut self, e: ExprId, scope: usize) {
        if !self.vyper {
            return;
        }
        let Node::Op(op::SHR, w) = expr::node(e) else {
            return;
        };
        let Some(n) = expr::as_const(w[0]) else {
            return;
        };
        if !n.fits_u64() || n.low_u64() >= 256 {
            return;
        }
        let n = n.low_u64() as u32;
        if n == 1 || n == 160 || (n.is_multiple_of(8) && n > 0) {
            let loc = self.location(w[1], scope);
            self.hint(loc, Ty::of_mask(n));
        }
    }

    fn keys_are_words(&mut self) -> bool {
        let keys: Vec<usize> = self
            .ids
            .iter()
            .filter(|(loc, _)| matches!(loc, Loc::Key(_)))
            .map(|(_, i)| *i)
            .collect();
        let mut learned = false;
        for i in keys {
            let c = &mut self.classes[i];
            if c.resolved == Ty::Bytes(32) && !c.flags.word32 {
                c.flags.word32 = true;
                learned = true;
            }
        }
        learned
    }

    // Forward types and backward hints are kept apart on purpose.
    // A slot holding unrelated values on two paths must join to a conflict.
    // It must not leak one value's type into the other.
    fn run(&mut self) {
        for _round in 0..MAX_ROUNDS {
            let mut changed = false;
            for i in 0..self.classes.len() {
                let defs = std::mem::take(&mut self.classes[i].defs);
                let mut t = Ty::Unknown;
                let mut flags = self.classes[i].flags;
                flags.one = false;
                flags.other = false;
                for (val, scope) in &defs {
                    match expr::as_const(*val) {
                        Some(c) if c.is_zero() => {}
                        Some(c) if c == U256::ONE => flags.one = true,
                        Some(c) => {
                            flags.other = true;
                            t = t.join(const_type(c));
                        }
                        None => {
                            let vt = self.type_of(*val, *scope);
                            if vt != Ty::Bool && !expr::is_boolean(*val) {
                                flags.other = true;
                            }
                            if is_arithmetic(*val) {
                                flags.arith_def = true;
                            }
                            t = t.join(vt);
                        }
                    }
                }
                let c = &mut self.classes[i];
                c.defs = defs;
                c.flags = flags;
                c.from_defs = t;
                let resolved = resolve(c, Evidence::Flowing);
                if resolved != c.resolved {
                    c.resolved = resolved;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
    }

    fn debug_dump(&self) {
        let mut locs: Vec<(&Loc, &usize)> = self.ids.iter().collect();
        locs.sort_by_key(|(_, i)| **i);
        for (loc, i) in locs {
            let c = &self.classes[*i];
            if c.resolved == Ty::Unknown && c.hints == Ty::Unknown && c.weak == Ty::Unknown {
                continue;
            }
            let defs: Vec<String> = c
                .defs
                .iter()
                .take(4)
                .map(|(e, _)| format!("{:?}", expr::node(*e)))
                .collect();
            eprintln!(
                "[types] #{} {:?}: {:?} (defs {:?} x{} {:?}, hints {:?}, weak {:?}, {:?}, from {:?})",
                i,
                loc,
                c.resolved,
                c.from_defs,
                c.defs.len(),
                defs,
                c.hints,
                c.weak,
                c.flags,
                c.sources
            );
        }
    }

    #[must_use]
    pub fn vyper(&self) -> bool {
        self.vyper
    }

    pub fn type_of(&self, e: ExprId, scope: usize) -> Ty {
        self.type_of_at(e, scope, 0)
    }

    fn type_of_at(&self, e: ExprId, scope: usize, depth: u32) -> Ty {
        if depth > MAX_TYPE_DEPTH {
            return Ty::Unknown;
        }
        if let Some(loc) = self.location(e, scope) {
            let own = self.resolved_of(&loc);
            return match loc {
                Loc::Field { bits, .. } if matches!(expr::node(e), Node::Op(op::AND, _)) => {
                    match own {
                        Ty::Uint(160) => own,
                        _ => own.join(Ty::of_mask(bits)),
                    }
                }
                _ => own,
            };
        }
        match expr::node(e) {
            Node::Const(c) => const_type(c),
            Node::Env(o, _) => match o {
                op::CALLER | op::ADDRESS | op::ORIGIN | op::COINBASE => Ty::Address,
                op::BLOCKHASH => Ty::Bytes(32),
                _ => Ty::Unknown,
            },
            Node::Keccak(..) | Node::KeccakMem(..) => Ty::Bytes(32),
            Node::Op(op::BLOCKHASH | op::EXTCODEHASH | op::BLOBHASH, _) => Ty::Bytes(32),
            Node::CallResult(_) => Ty::Bool,
            Node::CreateResult(_) => Ty::Address,
            Node::Op(op::AND, v) => self.masked_type(&v, scope, depth),
            Node::Op(op::SIGNEXTEND, v) => match expr::as_const(v[0]) {
                Some(k) if k < U256::from_u64(31) => Ty::Int(8 * (k.low_u64() as u32 + 1)),
                _ => Ty::Int(256),
            },
            Node::Op(op::ISZERO | op::LT | op::GT | op::SLT | op::SGT | op::EQ, _) => Ty::Bool,
            Node::Op(op::SHR | op::DIV | op::BYTE, _) => {
                let b = expr::value_bits(e);
                if !self.vyper && b > 0 && b < 256 && b.is_multiple_of(8) {
                    Ty::Uint(b)
                } else {
                    Ty::Unknown
                }
            }
            _ => Ty::Unknown,
        }
    }

    fn masked_type(&self, v: &[ExprId], scope: usize, depth: u32) -> Ty {
        for (x, m) in [(v[0], v[1]), (v[1], v[0])] {
            let Some(m) = expr::as_const(m) else { continue };
            if m.is_low_mask() {
                let inner = self.type_of_at(x, scope, depth + 1);
                if self.vyper {
                    return inner;
                }
                let masked = Ty::of_mask(m.bits());
                return match (inner, masked) {
                    (Ty::Address, Ty::Uint(n)) if n < 160 => Ty::Uint(n),
                    (Ty::Bool, Ty::Uint(_)) => Ty::Bool,
                    (Ty::Unknown, m) | (Ty::Conflict, m) => m,
                    (i, m) => i.join(m),
                };
            }
            if let Some(bytes) = high_mask_bytes(m) {
                return Ty::Bytes(bytes);
            }
        }
        Ty::Unknown
    }

    fn resolved_of(&self, loc: &Loc) -> Ty {
        match self.ids.get(loc) {
            Some(i) => self.classes[*i].resolved,
            None => Ty::Unknown,
        }
    }

    fn final_of(&self, loc: &Loc) -> Ty {
        match self.ids.get(loc) {
            Some(i) => resolve(&self.classes[*i], Evidence::Final),
            None => Ty::Unknown,
        }
    }

    pub fn solidity(&self, loc: &Loc) -> Option<String> {
        self.final_of(loc).solidity()
    }

    pub fn param_type(&self, pc: usize, word: u32) -> Option<String> {
        self.solidity(&Loc::Param { scope: pc, word })
    }

    pub fn param_is_numeric(&self, pc: usize, word: u32) -> bool {
        self.ids
            .get(&Loc::Param { scope: pc, word })
            .is_some_and(|c| self.classes[*c].flags.arith)
    }

    pub fn arg_type(&self, pc: usize, arity: usize, i: usize) -> Option<String> {
        if i >= arity {
            return None;
        }
        self.solidity(&Loc::Arg {
            unit: pc,
            slot: (arity - 1 - i) as u32,
        })
    }

    pub fn result_type(&self, pc: usize, index: u16) -> Option<String> {
        self.solidity(&Loc::Ret { unit: pc, index })
    }

    pub fn slot_type(&self, root: U256, steps: &[ShapeStep]) -> Option<String> {
        self.solidity(&Loc::Slot(persistent(root, steps)))
    }

    pub fn key_type(&self, root: U256, steps: &[ShapeStep]) -> Option<String> {
        let loc = Loc::Key(persistent(root, steps));
        match self.final_of(&loc) {
            Ty::Bool => None,
            _ => self.solidity(&loc),
        }
    }

    pub fn var_is_bool(&self, pc: usize, id: u32) -> bool {
        self.final_of(&Loc::Var { scope: pc, id }) == Ty::Bool
    }

    pub fn rebase(&mut self, base: usize) {
        if base == 0 {
            return;
        }
        let shift = |loc: Loc| match loc {
            Loc::Var { scope, id } => Loc::Var {
                scope: scope + base,
                id,
            },
            Loc::Arg { unit, slot } => Loc::Arg {
                unit: unit + base,
                slot,
            },
            Loc::Ret { unit, index } => Loc::Ret {
                unit: unit + base,
                index,
            },
            Loc::Param { scope, word } => Loc::Param {
                scope: scope + base,
                word,
            },
            Loc::Output { scope, seq, word } => Loc::Output {
                scope: scope + base,
                seq,
                word,
            },
            other => other,
        };
        self.ids = self.ids.drain().map(|(loc, id)| (shift(loc), id)).collect();
        self.callee_of = self
            .callee_of
            .drain()
            .map(|((pc, seq), callee)| ((pc + base, seq), callee + base))
            .collect();
        self.results_len = self
            .results_len
            .drain()
            .map(|(pc, n)| (pc + base, n))
            .collect();
        for c in &mut self.classes {
            for d in &mut c.defs {
                d.1 += base;
            }
        }
    }

    pub fn absorb(&mut self, other: TypeEnv) {
        let offset = self.classes.len();
        for mut c in other.classes {
            for s in &mut c.sources {
                *s += offset;
            }
            self.classes.push(c);
        }
        // Two parts of one contract can use the same storage. What the later part learned
        // about a shared place is added to the class the first part made for it, or a
        // rule that needs both sides would only ever see the first.
        let mut shared = false;
        for (loc, id) in other.ids {
            let theirs = id + offset;
            match self.ids.get(&loc).copied() {
                None => {
                    self.ids.insert(loc, theirs);
                }
                Some(mine) => {
                    let from = self.classes[theirs].clone();
                    let into = &mut self.classes[mine];
                    into.hints = into.hints.join(from.hints);
                    into.weak = into.weak.join(from.weak);
                    into.from_defs = into.from_defs.join(from.from_defs);
                    into.resolved = into.resolved.join(from.resolved);
                    into.flags.absorb(from.flags);
                    into.defs.extend(from.defs);
                    into.sources.extend(from.sources);
                    shared = true;
                }
            }
        }
        if shared {
            self.propagate();
        }
        self.callee_of.extend(other.callee_of);
        self.results_len.extend(other.results_len);
    }

    // Sorted. Reports must not depend on hash map iteration order.
    #[must_use]
    pub fn locations(&self) -> Vec<&Loc> {
        let mut locs: Vec<&Loc> = self.ids.keys().collect();
        locs.sort();
        locs
    }

    #[must_use]
    pub fn info(&self, loc: &Loc) -> Option<ClassInfo> {
        let c = &self.classes[*self.ids.get(loc)?];
        Some(ClassInfo {
            ty: resolve(c, Evidence::Final),
            arith: c.flags.arith,
            account: c.flags.account,
            signed_cmp: c.flags.signed_cmp,
            unsigned_cmp: c.flags.unsigned_cmp,
            arith_def: c.flags.arith_def,
            cast: c.flags.cast,
        })
    }

    #[must_use]
    pub fn defs(&self, loc: &Loc) -> &[(ExprId, usize)] {
        match self.ids.get(loc) {
            Some(i) => &self.classes[*i].defs,
            None => &[],
        }
    }
}

fn persistent(root: U256, steps: &[ShapeStep]) -> Shape {
    Shape {
        root,
        steps: steps.to_vec(),
        space: SlotSpace::Persistent,
    }
}

fn resolve(c: &Class, evidence: Evidence) -> Ty {
    let f = c.flags;
    let mut t = match c.from_defs.join(c.hints) {
        Ty::Uint(n) if f.checked(n) => Ty::Unknown,
        Ty::Address if f.checked(160) => Ty::Unknown,
        t => t,
    };
    if t == Ty::Unknown && evidence == Evidence::Final {
        t = c.weak;
    }
    if t == Ty::Unknown && f.tested && !f.arith && !f.other && !c.storage {
        t = Ty::Bool;
    }
    if f.word32 && !f.arith && !f.account && matches!(t, Ty::Unknown | Ty::Bytes(_)) {
        t = Ty::Bytes(32);
    }
    match t {
        Ty::Uint(n) if n <= 8 && f.one && !f.other && !f.arith => Ty::Bool,
        Ty::Address if f.scaled && f.account => Ty::Unknown,
        Ty::Address if f.arith && !f.account => Ty::Uint(160),
        Ty::Bool if f.arith => Ty::Unknown,
        t => t,
    }
}

fn condition_exprs(nd: &lift::LNode) -> Vec<ExprId> {
    let mut v: Vec<ExprId> = nd
        .stmts
        .iter()
        .filter_map(|s| match s {
            Stmt::Require { cond, .. } => Some(*cond),
            _ => None,
        })
        .collect();
    match &nd.term {
        Term::Branch { cond, .. } | Term::CondJump { cond, .. } => v.push(*cond),
        _ => {}
    }
    v
}

#[must_use]
pub fn is_arithmetic(e: ExprId) -> bool {
    match expr::node(e) {
        Node::Op(op::MUL, v) => {
            !v.iter().any(|x| expr::is_boolean(*x)) && !v.iter().any(|x| is_byte_shift(*x))
        }
        Node::Op(op::DIV, v) => !v.iter().any(|x| is_byte_shift(*x)),
        Node::Op(op::ADD, v) => !v.iter().any(|x| is_masked_select(*x)),
        Node::Op(op::SUB | op::MOD | op::EXP | op::ADDMOD | op::MULMOD, _) => true,
        _ => false,
    }
}

fn is_byte_shift(e: ExprId) -> bool {
    expr::as_const(e).is_some_and(|c| {
        c.is_power_of_two() && c.trailing_zeros() > 0 && c.trailing_zeros().is_multiple_of(8)
    })
}

fn is_masked_select(e: ExprId) -> bool {
    matches!(expr::node(e), Node::Op(op::MUL, v) if v.iter().any(|x| expr::is_boolean(*x)))
}

fn looks_like_account(c: U256) -> bool {
    c.byte_len() == 20 && (150..=160).contains(&c.bits())
}

fn is_account(e: ExprId) -> bool {
    match expr::node(e) {
        Node::Env(o, _) => matches!(o, op::CALLER | op::ADDRESS | op::ORIGIN),
        Node::Const(c) => looks_like_account(c),
        _ => false,
    }
}

fn const_type(c: U256) -> Ty {
    if looks_like_account(c) {
        return Ty::Address;
    }
    let tz = c.trailing_zeros();
    if !c.is_zero() && (192..256).contains(&tz) {
        return Ty::Bytes((256 - tz).div_ceil(8));
    }
    if looks_like_hash(c) {
        return Ty::Bytes(32);
    }
    Ty::Unknown
}

fn looks_like_hash(c: U256) -> bool {
    let bytes = c.to_be_bytes();
    let zeros = bytes.iter().filter(|b| **b == 0).count();
    let ones = bytes.iter().filter(|b| **b == 0xff).count();
    c.byte_len() >= 31 && zeros <= 2 && ones <= 2
}

fn looks_like_text(c: U256) -> bool {
    let bytes = c.to_be_bytes();
    let len = bytes
        .iter()
        .take_while(|b| (0x20..0x7f).contains(*b))
        .count();
    len >= 2 && bytes[len..].iter().all(|b| *b == 0)
}

fn is_word32(e: ExprId) -> bool {
    match expr::node(e) {
        Node::Keccak(..) | Node::KeccakMem(..) => true,
        Node::Op(op::BLOCKHASH | op::EXTCODEHASH | op::BLOBHASH, _) => true,
        Node::Const(c) => looks_like_hash(c) || looks_like_text(c),
        _ => false,
    }
}

fn high_mask_bytes(m: U256) -> Option<u32> {
    let tz = m.trailing_zeros();
    if tz == 0 || !tz.is_multiple_of(8) || tz >= 256 {
        return None;
    }
    ((m >> tz).is_low_mask() && m.bits() == 256).then(|| (256 - tz) / 8)
}

fn signed_bound(c: U256) -> Option<u32> {
    let pos = c.wrapping_add(U256::ONE);
    if pos.is_power_of_two() && pos.trailing_zeros() >= 7 && pos.trailing_zeros() < 256 {
        let n = pos.trailing_zeros() + 1;
        return n.is_multiple_of(8).then_some(n);
    }
    let neg = (!c).wrapping_add(U256::ONE);
    if neg.is_power_of_two() && c.bits() == 256 {
        let n = neg.trailing_zeros() + 1;
        return n.is_multiple_of(8).then_some(n);
    }
    None
}
