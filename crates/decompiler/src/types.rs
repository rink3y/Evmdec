//! Type recovery as constraint solving.
//!
//! Every typed location (phi variable, internal parameter or result, calldata parameter, storage
//! slot, packed field, mapping key) is a class. Values flow forward along copies (phi edges,
//! assignments, argument passing, result binding, storage writes): the type of a class is the
//! join of the types of the values flowing in. Evidence from uses (a mask, a comparison with an
//! address, a call target, a power-of-two bound, arithmetic) is a hint on the class and flows
//! backward along the same copies, since a use after a merge applies to every value that
//! reaches it. The two directions are kept apart on purpose: a stack slot that holds unrelated
//! values on different paths joins to a conflict instead of leaking one value's type into the
//! other's origin. The pseudo-Solidity printer turns the result into `address`, `bool`, `uintN`,
//! `intN` or `bytesN`; a class with no evidence, or contradictory evidence, keeps `uint256`.
//!
//! The solver refines the direct heuristics (masks on calldata words, return constants): it
//! fills in what they leave at `uint256` by following values through phis, helpers and storage,
//! which is where a mask applied to a merged value or a bound checked by a Vyper decoder would
//! otherwise be lost.

use crate::emit::{calldata_word_index, MappingLayout, SlotSpace};
use crate::expr::{self, ExprId, Node};
use crate::lift::{self, Lifted, Stmt, Term};
use crate::opcode as op;
use crate::ssa::{self, Shape, ShapeStep};
use crate::u256::U256;
use std::collections::{HashMap, HashSet};

/// A recovered type, as a lattice: `Unknown` below everything, `Conflict` above.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum Ty {
    /// No evidence yet.
    #[default]
    Unknown,
    /// Only ever 0 or 1.
    Bool,
    /// A 160-bit value used as an account.
    Address,
    /// Unsigned integer of this many bits.
    Uint(u32),
    /// Signed integer of this many bits.
    Int(u32),
    /// Left-aligned byte string of this many bytes (`bytes32` for hashes).
    Bytes(u32),
    /// Evidence that cannot be reconciled.
    Conflict,
}

impl Ty {
    /// Least upper bound.
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

    /// The Solidity spelling, or `None` when the type is unknown, contradictory or has a width
    /// no declaration can have (a `uint255` is a flag-stripped `uint256`).
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

    /// The type an elementary Solidity type name declares for one ABI word: `address`, `bool`,
    /// `uintN`, `intN` or `bytesN`. `None` for `uint256`, which says nothing more than a word,
    /// and for anything that is not one word.
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

    /// The type a low mask of `bits` bits cleans a value to.
    pub fn of_mask(bits: u32) -> Ty {
        match bits {
            0 => Ty::Unknown,
            1 => Ty::Bool,
            160 => Ty::Address,
            n => Ty::Uint(n),
        }
    }
}

/// A typed location.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Loc {
    /// A phi variable of one function.
    Var {
        /// Entry pc of the function.
        scope: usize,
        /// The `Var` id.
        id: u32,
    },
    /// An entry stack slot of an internal unit (`Arg(slot)`; parameter `k - 1 - slot` in
    /// declaration order for a unit with `k` parameters).
    Arg {
        /// Entry pc of the unit.
        unit: usize,
        /// Stack slot from the top at entry.
        slot: u32,
    },
    /// A result of an internal unit.
    Ret {
        /// Entry pc of the unit.
        unit: usize,
        /// Result index, deepest first.
        index: u16,
    },
    /// A calldata head word of one function.
    Param {
        /// Entry pc of the function.
        scope: usize,
        /// Head word index.
        word: u32,
    },
    /// The value of every element of a storage variable (whole slots).
    Slot(Shape),
    /// A packed field of every element of a storage variable.
    Field {
        /// The elements' shape.
        shape: Shape,
        /// Bit offset of the field within the slot.
        bit_offset: u32,
        /// Width of the field in bits.
        bits: u32,
    },
    /// The keys of a mapping: the shape of the entries it selects.
    Key(Shape),
    /// A word of the data an external call returned.
    Output {
        /// Entry pc of the function making the call.
        scope: usize,
        /// Sequence number of the call.
        seq: u32,
        /// Word index in the return data.
        word: u32,
    },
}

impl Loc {
    /// Storage locations hold a declared type; a cast at a reader says nothing about it.
    fn is_storage(&self) -> bool {
        matches!(self, Loc::Slot(_) | Loc::Field { .. } | Loc::Key(_))
    }
}

/// Evidence about one class beyond the lattice value.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Flags {
    /// Used as an arithmetic operand: not a `bool`, and a 160-bit value that is a number rather
    /// than an account.
    arith: bool,
    /// Multiplied, divided or taken modulo: a number, which no account ever is.
    scaled: bool,
    /// Used as an account: call target, compared with `msg.sender`, balance queried.
    account: bool,
    /// `x != 0` was tested on it.
    tested: bool,
    /// A constant `1` flows in.
    one: bool,
    /// A value that is neither a flag constant nor boolean-shaped flows in.
    other: bool,
    /// Widths (in bytes, as a bit set) the value was range-checked against by solc output: a
    /// mask of the same width that follows is a checked narrowing cast of a wider value, not
    /// the value's own width.
    cast: u32,
    /// Compared as a signed number (`slt`/`sgt` against something other than zero or a signed
    /// bound) or divided as one.
    signed_cmp: bool,
    /// Compared as an unsigned number against a value that is not a power-of-two bound.
    unsigned_cmp: bool,
    /// Receives the result of arithmetic (`add`, `sub`, `mul`, `div`, `mod`, `exp`).
    arith_def: bool,
    /// Used where only an opaque 32-byte word fits: a hash or signature half given to
    /// `ecrecover`, or compared for equality with a hash or a text literal.
    word32: bool,
}

/// Is width `bits` in the `cast` bit set (bit `bits / 8` for whole-byte widths)?
fn cast_checked(cast: u32, bits: u32) -> bool {
    bits.is_multiple_of(8) && bits / 8 < 32 && cast & (1 << (bits / 8)) != 0
}

impl Flags {
    fn checked(&self, bits: u32) -> bool {
        cast_checked(self.cast, bits)
    }

    /// Merge the use evidence of a class into one of its sources.
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

/// What the solver knows about one location, for rules that reason about widths and uses.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ClassInfo {
    /// The reported type.
    pub ty: Ty,
    /// Used as an arithmetic operand.
    pub arith: bool,
    /// Used as an account.
    pub account: bool,
    /// Compared or divided as a signed number.
    pub signed_cmp: bool,
    /// Compared as an unsigned number.
    pub unsigned_cmp: bool,
    /// Receives the result of arithmetic.
    pub arith_def: bool,
    /// Widths (bytes, as a bit set) the value was range-checked against before a cast.
    cast: u32,
}

impl ClassInfo {
    /// Was the value range-checked against `2^bits` (a checked cast to that width)?
    #[must_use]
    pub fn checked(&self, bits: u32) -> bool {
        cast_checked(self.cast, bits)
    }
}

#[derive(Clone, Debug, Default)]
struct Class {
    /// Use evidence that flows back to the values reaching this class.
    hints: Ty,
    /// Use evidence that stays with this class: a signed comparison with zero says the value is
    /// treated as signed here, not that everything stored into it is signed.
    weak: Ty,
    flags: Flags,
    /// A storage slot, field or mapping key.
    storage: bool,
    /// Values flowing in, with the function they are read in.
    defs: Vec<(ExprId, usize)>,
    /// Classes whose values flow in (location-valued defs): hints flow back to them.
    sources: Vec<usize>,
    /// Current type from the defs (recomputed every round).
    from_defs: Ty,
    /// The type that flows out to readers: strong evidence only.
    resolved: Ty,
}

/// Which evidence a resolution may use.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Evidence {
    /// Values and strong uses: what flows on to other classes.
    Flowing,
    /// Also the weak uses: what is reported for the class itself.
    Final,
}

/// Nodes visited per expression walk before giving up.
const MAX_VISITED: usize = 50_000;
/// Rounds of the def-type fixpoint.
const MAX_ROUNDS: usize = 8;
/// Nesting followed when typing an expression structurally.
const MAX_TYPE_DEPTH: u32 = 6;

/// The solver and, once solved, the environment later passes query.
#[derive(Clone, Debug)]
pub struct TypeEnv {
    layout: MappingLayout,
    /// Vyper validates decoded values by range checks (`x < 2^160`, `x >> 1 == 0`); solc masks
    /// them, so a range check in solc output is a cast or a user `require`. Vyper never masks a
    /// value to its declared width and never packs storage, so a mask or shift there is the
    /// program unpacking a word, not a narrower variable.
    vyper: bool,
    debug: bool,
    ids: HashMap<Loc, usize>,
    classes: Vec<Class>,
    /// `(function, sequence number of an internal call)` -> callee pc, for `IntRet(seq, j)`.
    /// Sequence numbers are per lifted graph, so the function scopes them.
    callee_of: HashMap<(usize, u32), usize>,
    /// Callee pc -> number of results its call sites consume, when every site agrees. A unit
    /// whose `InternalReturn`s list a different number of values (pass-through stack slots)
    /// cannot be aligned with `IntRet` positions.
    results_len: HashMap<usize, Option<usize>>,
}

/// A calldata head word whose type a known signature declares: the function's entry pc, the
/// word index and the type.
pub type Declared = (usize, u32, Ty);

/// The head words a signature's parameter list declares, as `(word index, type)`. Words are
/// counted while every parameter so far takes exactly one (elementary and dynamic types do; a
/// static tuple or fixed array takes several and ends the count).
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

/// Build the environment: index every function, then solve. `declared` carries what known
/// signatures state about calldata words; it is evidence like any use and flows on to the
/// storage, helpers and results the words reach.
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
    /// The class of `loc`, created on first sight.
    fn intern(&mut self, loc: Loc) -> usize {
        if let Some(i) = self.ids.get(&loc) {
            return *i;
        }
        let i = self.classes.len();
        let hints = match &loc {
            Loc::Field { bits: 160, .. } => Ty::Address,
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

    /// Record an arithmetic use of `e`.
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

    /// Record that `val` (read in `scope`) flows into `loc`.
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

    /// Flow use evidence backward: what is known about a class holds for every value that
    /// flows into it. Weak evidence stops at storage, whose declared type is what the values
    /// stored into it are cast to, not what a reader casts them to.
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

    /// The location `e` reads, if it is a plain read of one (a masked read counts: the mask is a
    /// cleanup of the same value and a width hint for it).
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

    /// The location `e` denotes when it is a location read: a phi variable, an entry stack
    /// slot, a calldata word, a storage slot or packed field, or a helper result.
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

    /// Index one function: copies, definitions and use evidence.
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

    /// Definitions and account uses a statement makes.
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

    /// Two byte layouts built in memory say what their words are. A 65-byte string of two
    /// words and one byte is a signature: its words are `r` and `s`. The two words after the
    /// two-byte prefix `0x1901` are the domain separator and the struct hash of a typed-data
    /// digest. All four are opaque 32-byte words.
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

    /// `e` is used as an account (through a 160-bit cleanup or not).
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

    /// `e` is used as an opaque 32-byte word.
    fn word32(&mut self, e: ExprId, scope: usize) {
        let loc = self.location(e, scope);
        self.flag(loc, |f| f.word32 = true);
    }

    /// Record the key types of every mapping step on `path`.
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

    /// Walk the expression DAG under `root` and record what each use says about its operands.
    /// `context` stands in for the root's parent: a payload word is a packing context from its
    /// root (its 4-byte tail is a bare mask), a branch condition a truth test (`a - b` as a
    /// condition is `a != b`).
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
                for x in v {
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

    /// `x & mask`: a low mask is a cleanup to a width, unless it carves a piece of a value for a
    /// packed payload word (`x & 0xffffffff << 224 | y >> 32`), which says nothing; a high
    /// mask keeps the top bytes of a `bytesN`. In Vyper a mask is the program's own arithmetic
    /// and says nothing about the declared type.
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
                let loc = self.location(x, scope);
                self.hint(loc, Ty::Bytes(bytes));
            }
        }
    }

    /// `x < 2^n` (`below`) or `x > 2^n - 1`: Vyper's decoder validates an n-bit type this way.
    /// In solc output the same check is a cast (`safe96`) or a user `require` on a wider value,
    /// and any other bound is an ordering of numbers.
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

    /// `x >> n == 0`: the value fits in n bits (Vyper's decoder validation of `address`, `bool`
    /// and narrow integers).
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

    /// A mapping has one key type. Where some key of a mapping is a hash, every value used as
    /// a key of that mapping is an opaque 32-byte word. Returns whether any class learned so.
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

    /// Iterate the def types to a fixpoint and resolve every class.
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

    /// Print every class with evidence (`EVMDEC_DEBUG_TYPES`).
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

    /// Whether the code is Vyper's, which validates by range checks and never masks a value to
    /// its declared width.
    #[must_use]
    pub fn vyper(&self) -> bool {
        self.vyper
    }

    /// The type of an expression read in `scope`, from the classes it reads and its shape.
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

    /// The type of `x & mask`: the mask narrows what is known about `x`.
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

    /// The type that flows out of a location to its readers: the strong evidence only.
    fn resolved_of(&self, loc: &Loc) -> Ty {
        match self.ids.get(loc) {
            Some(i) => self.classes[*i].resolved,
            None => Ty::Unknown,
        }
    }

    /// The type reported for a location: the weak evidence decides when nothing else does.
    fn final_of(&self, loc: &Loc) -> Ty {
        match self.ids.get(loc) {
            Some(i) => resolve(&self.classes[*i], Evidence::Final),
            None => Ty::Unknown,
        }
    }

    /// The Solidity type of a location, when the evidence names one.
    pub fn solidity(&self, loc: &Loc) -> Option<String> {
        self.final_of(loc).solidity()
    }

    /// The Solidity type of calldata head word `word` of the function at `pc`.
    pub fn param_type(&self, pc: usize, word: u32) -> Option<String> {
        self.solidity(&Loc::Param { scope: pc, word })
    }

    /// Is calldata head word `word` of the function at `pc` used in arithmetic (so not a `bool`)?
    pub fn param_is_numeric(&self, pc: usize, word: u32) -> bool {
        self.ids
            .get(&Loc::Param { scope: pc, word })
            .is_some_and(|c| self.classes[*c].flags.arith)
    }

    /// The Solidity type of parameter `i` (declaration order) of the internal unit at `pc`
    /// with `arity` parameters.
    pub fn arg_type(&self, pc: usize, arity: usize, i: usize) -> Option<String> {
        if i >= arity {
            return None;
        }
        self.solidity(&Loc::Arg {
            unit: pc,
            slot: (arity - 1 - i) as u32,
        })
    }

    /// The Solidity type of result `index` (deepest first) of the internal unit at `pc`.
    pub fn result_type(&self, pc: usize, index: u16) -> Option<String> {
        self.solidity(&Loc::Ret { unit: pc, index })
    }

    /// The element type of the storage variable at `root` reached through `steps`.
    pub fn slot_type(&self, root: U256, steps: &[ShapeStep]) -> Option<String> {
        self.solidity(&Loc::Slot(persistent(root, steps)))
    }

    /// The key type of the mapping step ending `steps` under `root`.
    pub fn key_type(&self, root: U256, steps: &[ShapeStep]) -> Option<String> {
        self.solidity(&Loc::Key(persistent(root, steps)))
    }

    /// Is the phi variable `id` of the function at `pc` a boolean?
    pub fn var_is_bool(&self, pc: usize, id: u32) -> bool {
        self.final_of(&Loc::Var { scope: pc, id }) == Ty::Bool
    }

    /// Add `base` to every function scope so this environment can sit next to another
    /// contract's without colliding (see [`crate::decompile::Contract::rebase`]).
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

    /// Take over every class of `other`, whose scopes must not overlap this environment's
    /// (rebase it first). A storage location both know keeps this environment's class.
    pub fn absorb(&mut self, other: TypeEnv) {
        let offset = self.classes.len();
        for mut c in other.classes {
            for s in &mut c.sources {
                *s += offset;
            }
            self.classes.push(c);
        }
        for (loc, id) in other.ids {
            self.ids.entry(loc).or_insert(id + offset);
        }
        self.callee_of.extend(other.callee_of);
        self.results_len.extend(other.results_len);
    }

    /// Every location the solver has a class for, in a deterministic order (the classes live in
    /// a hash map; reports must not depend on its iteration order).
    #[must_use]
    pub fn locations(&self) -> Vec<&Loc> {
        let mut locs: Vec<&Loc> = self.ids.keys().collect();
        locs.sort();
        locs
    }

    /// What is known about a location.
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

    /// The values flowing into a location, each with the function it is read in.
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

/// The resolved type of a class from its evidence. Weak evidence only decides when the values
/// and the strong uses say nothing, and never flows to other classes.
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

/// The expressions a node tests for truth: branch and guard conditions.
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

/// Arithmetic that produces a number: `add`, `sub`, `mul`, `div`, `mod`, `exp`, excluding the
/// shapes compilers use for other things (byte shifts by powers of two, branchless selects).
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

/// A power of two that moves a value by whole bytes.
fn is_byte_shift(e: ExprId) -> bool {
    expr::as_const(e).is_some_and(|c| {
        c.is_power_of_two() && c.trailing_zeros() > 0 && c.trailing_zeros().is_multiple_of(8)
    })
}

/// `cond * x`: one arm of a branchless select.
fn is_masked_select(e: ExprId) -> bool {
    matches!(expr::node(e), Node::Op(op::MUL, v) if v.iter().any(|x| expr::is_boolean(*x)))
}

/// A 20-byte constant with its top bits set: an account rather than a number.
fn looks_like_account(c: U256) -> bool {
    c.byte_len() == 20 && (150..=160).contains(&c.bits())
}

/// `CALLER`, `ADDRESS`, `ORIGIN` or a constant that looks like an account.
fn is_account(e: ExprId) -> bool {
    match expr::node(e) {
        Node::Env(o, _) => matches!(o, op::CALLER | op::ADDRESS | op::ORIGIN),
        Node::Const(c) => looks_like_account(c),
        _ => false,
    }
}

/// The type a constant value suggests: an account for 20-byte constants, `bytesN` for a short
/// left-aligned value (a selector), nothing otherwise.
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

/// A constant with the texture of a hash: nearly every byte significant, with no run of zero or
/// `0xff` bytes that a number, a mask or a scaled amount would have.
fn looks_like_hash(c: U256) -> bool {
    let bytes = c.to_be_bytes();
    let zeros = bytes.iter().filter(|b| **b == 0).count();
    let ones = bytes.iter().filter(|b| **b == 0xff).count();
    c.byte_len() >= 31 && zeros <= 2 && ones <= 2
}

/// A text literal held in a word: two or more printable ASCII bytes at the top, zeros below
/// (`"Line"` as a `bytes32`).
fn looks_like_text(c: U256) -> bool {
    let bytes = c.to_be_bytes();
    let len = bytes
        .iter()
        .take_while(|b| (0x20..0x7f).contains(*b))
        .count();
    len >= 2 && bytes[len..].iter().all(|b| *b == 0)
}

/// A hash, a hash-like constant or a text literal: what an opaque 32-byte word is compared with.
fn is_word32(e: ExprId) -> bool {
    match expr::node(e) {
        Node::Keccak(..) | Node::KeccakMem(..) => true,
        Node::Op(op::BLOCKHASH | op::EXTCODEHASH | op::BLOBHASH, _) => true,
        Node::Const(c) => looks_like_hash(c) || looks_like_text(c),
        _ => false,
    }
}

/// `n` for a mask keeping the top `n` bytes (`bytesN` cleanup), else `None`.
fn high_mask_bytes(m: U256) -> Option<u32> {
    let tz = m.trailing_zeros();
    if tz == 0 || !tz.is_multiple_of(8) || tz >= 256 {
        return None;
    }
    ((m >> tz).is_low_mask() && m.bits() == 256).then(|| (256 - tz) / 8)
}

/// `n` such that `c` is `2^(n-1) - 1` or `-2^(n-1)` (two's complement), the bounds of `intN`.
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
