use crate::emit::{self, Names};
use crate::expr::{self, ExprId, Node};
use crate::lift::{self, Lifted, Stmt, Term};
use std::collections::{HashMap, HashSet};

const WORD: u64 = 32;
const MOST_FIELDS: u64 = 64;

/* Something that can hold the address of a block of memory: an argument or a result of a
helper, one word of a block a function allocated, a value two paths give, or the block
itself. A helper is known by where its code starts. */
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Place {
    Param(usize, u32),
    Result(usize, usize),
    Field(usize, u32, u64),
    Var(usize, ExprId),
    Block(usize, u32),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Use {
    Word,
    Read,
    Write,
    Into(Place),
}

#[derive(Default)]
struct Seen {
    // Used as a number, which an address standing for its word cannot be.
    words: HashSet<Place>,
    // Read or written past its first word, or written through.
    offsets: HashSet<Place>,
    // The words a block is used as holding, for blocks of more than one.
    wide: HashMap<Place, u64>,
    stores: HashMap<Place, usize>,
    // Blocks a word is read from, or whose address is handed on. A block that is only
    // written is data laid out for a call or a failure, and is left as memory.
    read: HashSet<Place>,
    // Given something other than the address of a block.
    mixed: HashSet<Place>,
    flows: HashSet<(Place, Place)>,
    // A read through an address a place holds: the function it is in, the place, the
    // read and the address.
    reads: Vec<(usize, Place, ExprId, ExprId)>,
    // The address of a block given to a place, and the function that gives it.
    handed: Vec<(usize, Place, ExprId)>,
}

struct Walk<'a> {
    pc: usize,
    // An argument is numbered from the top of the stack, and a call lists what it hands
    // over in the order of the header. The count turns one into the other.
    arity: u32,
    fixed: bool,
    n: &'a Names,
    callees: HashMap<u32, usize>,
    seen: &'a mut Seen,
    done: HashSet<(ExprId, Use)>,
}

fn field(offset: u64) -> bool {
    offset.is_multiple_of(WORD) && offset < WORD * MOST_FIELDS
}

impl Walk<'_> {
    /* A block at a fixed address is the function's own only where the function starts
    with free memory at a fixed address, as one called from outside does. In a helper a
    fixed address is memory it shares with its callers. */
    fn own_block(&self, e: ExprId) -> Option<(u32, u64)> {
        if expr::split_offset(e).0.is_none() && !self.fixed {
            return None;
        }
        let (number, offset) = emit::block_ref(e, self.n)?;
        offset.fits_u64().then(|| (number, offset.low_u64()))
    }

    fn place(&self, e: ExprId) -> Option<Place> {
        if let Some((number, 0)) = self.own_block(e) {
            return Some(Place::Block(self.pc, number));
        }
        match expr::node(e) {
            Node::Arg(i) => Some(Place::Param(self.pc, self.arity.checked_sub(i + 1)?)),
            Node::IntRet(seq, k) => {
                let callee = self.callees.get(&seq)?;
                Some(Place::Result(*callee, usize::from(k)))
            }
            Node::Var(_) => Some(Place::Var(self.pc, e)),
            Node::MLoad(at, _) => {
                let (number, offset) = self.own_block(at)?;
                field(offset).then_some(Place::Field(self.pc, number, offset))
            }
            _ => None,
        }
    }

    fn reaches(&mut self, block: Place, offset: u64) {
        if offset != 0 {
            let words = self.seen.wide.entry(block).or_default();
            *words = (*words).max(offset / WORD + 1);
        }
    }

    fn visit(&mut self, e: ExprId, how: Use) {
        if !self.done.insert((e, how)) {
            return;
        }
        if let Some(p) = self.place(e) {
            if let Place::Field(pc, number, offset) = p {
                self.reaches(Place::Block(pc, number), offset);
                self.seen.read.insert(Place::Block(pc, number));
            }
            match (how, p) {
                (Use::Word, _) => {
                    self.seen.words.insert(p);
                }
                (Use::Read, _) => {}
                (Use::Write, Place::Block(..)) => {}
                (Use::Write, _) => {
                    self.seen.offsets.insert(p);
                }
                (Use::Into(q), _) => {
                    self.seen.flows.insert((p, q));
                    if let Place::Block(..) = p {
                        self.seen.handed.push((self.pc, p, e));
                        self.seen.read.insert(p);
                    }
                }
            }
            return;
        }
        match how {
            Use::Read | Use::Write => {
                if let Some((number, offset)) = self.own_block(e) {
                    // A word that lies across two fields is data laid out for a call
                    // before the block was taken. See `ranged` for why it is passed over.
                    if field(offset) {
                        self.reaches(Place::Block(self.pc, number), offset);
                    }
                    return;
                }
                let (base, offset) = expr::split_offset(e);
                let held = base.and_then(|b| self.place(b));
                if let Some(p) = held.filter(|_| !offset.is_zero()) {
                    self.seen.offsets.insert(p);
                    return;
                }
            }
            Use::Into(q) if expr::as_const(e).is_none_or(|c| !c.is_zero()) => {
                self.seen.mixed.insert(q);
            }
            Use::Into(_) | Use::Word => {}
        }
        match expr::node(e) {
            Node::KeccakMem(..) => {}
            Node::MLoad(at, _) => {
                if let Some(p) = self.place(at) {
                    self.seen.reads.push((self.pc, p, e, at));
                }
                self.visit(at, Use::Read);
            }
            _ => {
                for child in expr::children(e) {
                    self.visit(child, Use::Word);
                }
            }
        }
    }

    fn walk(&mut self, l: &Lifted) {
        let pc = self.pc;
        for nd in &l.nodes {
            for s in &nd.stmts {
                match s {
                    Stmt::MStore { off, .. } if emit::is_free_pointer(*off) => {}
                    Stmt::MStore {
                        off,
                        val,
                        width: 32,
                        ..
                    } => {
                        self.visit(*off, Use::Write);
                        if let Some(block @ Place::Block(..)) = self.place(*off) {
                            *self.seen.stores.entry(block).or_default() += 1;
                        }
                        let own = self.own_block(*off).filter(|(_, at)| field(*at));
                        match own {
                            Some((number, at)) => {
                                self.visit(*val, Use::Into(Place::Field(pc, number, at)))
                            }
                            None => self.visit(*val, Use::Word),
                        }
                    }
                    Stmt::Internal { callee, args, .. } => {
                        for (j, a) in args.iter().enumerate() {
                            self.visit(*a, Use::Into(Place::Param(*callee, j as u32)));
                        }
                    }
                    Stmt::Assign { var, value } => {
                        self.visit(*value, Use::Into(Place::Var(pc, *var)));
                    }
                    _ => {
                        let skipped = ranged(s);
                        let shown = lift::stmt_exprs(s).into_iter();
                        for e in shown.filter(|e| !skipped.contains(e)) {
                            self.visit(e, Use::Word);
                        }
                    }
                }
            }
            match &nd.term {
                Term::InternalReturn(vals) => {
                    for (k, v) in vals.iter().enumerate() {
                        self.visit(*v, Use::Into(Place::Result(pc, k)));
                    }
                }
                Term::Return { off, len, .. } | Term::Revert { off, len, .. } => {
                    let shown = lift::term_exprs(&nd.term).into_iter();
                    for e in shown.filter(|e| e != off && e != len) {
                        self.visit(e, Use::Word);
                    }
                }
                term => {
                    for e in lift::term_exprs(term) {
                        self.visit(e, Use::Word);
                    }
                }
            }
        }
        for (var, val) in l.edge_assigns.values().flatten() {
            self.visit(*val, Use::Into(Place::Var(pc, *var)));
        }
    }
}

/* The addresses a statement names a stretch of memory by. Data for a call, a log or a
failure is laid out in free memory that is not taken, so a block taken later starts at
the same address. The text shows such a stretch by the values in it, or as raw memory no
compiler takes, and in neither case holds the address as a number. */
fn ranged(s: &Stmt) -> Vec<ExprId> {
    match s {
        Stmt::Call {
            in_off,
            in_len,
            out_off,
            out_len,
            ..
        } => vec![*in_off, *in_len, *out_off, *out_len],
        Stmt::Copy { dest, src, .. } => vec![*dest, *src],
        Stmt::Log { off, len, .. } => vec![*off, *len],
        _ => Vec::new(),
    }
}

// How the printer shows an expression once the addresses are taken out.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Shown {
    // The first word of a block, where the address of the block is handed on. An address
    // can be a plain number, so this holds only where the text hands the value on.
    Word(u32),
    // What held the address, where the text read through it.
    As(ExprId),
}

#[derive(Default, Debug)]
pub struct Found {
    // Each block the function keeps to itself, with the number of words it holds.
    pub scalars: HashMap<u32, u64>,
    pub shown: Vec<(ExprId, Shown)>,
}

/* A struct of one word in memory is handed between helpers by its address. Where every
holder of the address only reads the word, the address stands for the word and the text
can hand over the word itself. A block whose address is not handed on at all is a set of
values local to its function. Both are found here for all functions of a contract at
once, as a helper and its callers have to agree on what is handed over. */
#[must_use]
pub fn find(units: &[(usize, &Lifted, &Names)]) -> Vec<Found> {
    let mut seen = Seen::default();
    for (pc, l, n) in units {
        let called = l.nodes.iter().flat_map(|nd| &nd.stmts);
        let callees = called.filter_map(|s| match s {
            Stmt::Internal { seq, callee, .. } => Some((*seq, *callee)),
            _ => None,
        });
        let mut walk = Walk {
            pc: *pc,
            arity: crate::ssa::arity(l) as u32,
            fixed: l.entry_free_pointer().is_some_and(expr::is_const),
            n,
            callees: callees.collect(),
            seen: &mut seen,
            done: HashSet::new(),
        };
        walk.walk(l);
    }
    let mut near: HashMap<Place, Vec<Place>> = HashMap::new();
    let mut fields: HashMap<Place, Vec<Place>> = HashMap::new();
    let mut boxes: HashSet<Place> = seen.reads.iter().map(|(_, p, _, _)| *p).collect();
    let mut lost: Vec<Place> = Vec::new();
    for (from, to) in &seen.flows {
        near.entry(*from).or_default().push(*to);
        near.entry(*to).or_default().push(*from);
        boxes.extend([*from, *to]);
        // A helper only borrows what it is handed. Kept, it could change under the keeper.
        let borrowed = matches!(from, Place::Param(..)) && !matches!(to, Place::Param(..));
        // A block written again after its address was kept would show the keeper the
        // new word, where a copy of the word would not.
        let kept = matches!(to, Place::Field(..) | Place::Var(..));
        let rewritten = kept && seen.stores.get(from).is_some_and(|n| *n > 1);
        if borrowed || rewritten {
            lost.push(*from);
        }
    }
    for p in &boxes {
        if let Place::Field(pc, number, _) = p {
            fields
                .entry(Place::Block(*pc, *number))
                .or_default()
                .push(*p);
        }
    }
    let plain = |p: &Place| {
        seen.words.contains(p)
            || seen.offsets.contains(p)
            || seen.mixed.contains(p)
            || (matches!(p, Place::Block(..)) && seen.wide.contains_key(p))
    };
    lost.extend(boxes.iter().filter(|p| plain(p)).copied());
    // A block used as a number is real memory, and so are its words.
    let numbers = seen.words.iter().filter(|p| matches!(p, Place::Block(..)));
    lost.extend(numbers.filter_map(|b| fields.get(b)).flatten().copied());
    while let Some(p) = lost.pop() {
        if !boxes.remove(&p) {
            continue;
        }
        lost.extend(near.get(&p).into_iter().flatten().copied());
        if near.contains_key(&p) {
            lost.extend(fields.get(&p).into_iter().flatten().copied());
        }
    }
    let real = |block: &Place| {
        let handed_on = near.contains_key(block) && !boxes.contains(block);
        seen.words.contains(block) || handed_on || !seen.read.contains(block)
    };
    let mut found: Vec<Found> = Vec::new();
    for (pc, l, n) in units {
        let fixed = l.entry_free_pointer().is_some_and(expr::is_const);
        let own = n.blocks.iter().flatten();
        let own = own.filter(|(base, _)| base.is_some() || fixed);
        let numbers = own.flat_map(|(_, at)| at.iter().map(|(_, number)| *number));
        let words = |number: u32| seen.wide.get(&Place::Block(*pc, number)).copied();
        let scalars: HashMap<u32, u64> = numbers
            .filter(|number| !real(&Place::Block(*pc, *number)))
            .map(|number| (number, words(number).unwrap_or(1)))
            .collect();
        let mut shown: Vec<(ExprId, Shown)> = Vec::new();
        for (at, p, e) in seen.handed.iter().filter(|(at, ..)| at == pc) {
            if let Place::Block(_, number) = p {
                if boxes.contains(p) && scalars.contains_key(number) {
                    shown.push((*e, Shown::Word(*number)));
                }
            }
            debug_assert_eq!(at, pc);
        }
        for (_, p, read, at) in seen.reads.iter().filter(|(at, ..)| at == pc) {
            let local = match p {
                Place::Block(..) => false,
                Place::Field(_, number, _) => scalars.contains_key(number),
                _ => true,
            };
            if local && boxes.contains(p) {
                shown.push((*read, Shown::As(*at)));
            }
        }
        found.push(Found { scalars, shown });
    }
    found
}
