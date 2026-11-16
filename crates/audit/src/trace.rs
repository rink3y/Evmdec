use evmdec::U256;
use std::collections::HashMap;

pub const CALLER: u16 = 1;
pub const ORIGIN: u16 = 1 << 1;
pub const VALUE: u16 = 1 << 2;
pub const DATA: u16 = 1 << 3;
pub const STORE: u16 = 1 << 4;
pub const OUT: u16 = 1 << 5;
pub const CLOCK: u16 = 1 << 6;
pub const BLOCK: u16 = 1 << 7;
pub const SELF: u16 = 1 << 8;
pub const BAL: u16 = 1 << 9;
pub const HASH: u16 = 1 << 10;
pub const MATH: u16 = 1 << 11;
pub const CMP: u16 = 1 << 12;
pub const SIZE: u16 = 1 << 13;
pub const EXT: u16 = 1 << 14;
// The first four bytes of the call data, which choose the function.
pub const CHOICE: u16 = 1 << 15;
// What only says how a word was worked on, not where it came from.
const WORKED: u16 = HASH | MATH | CMP;

const MANY: u16 = u16::MAX;
pub const DATA_WORDS: usize = 32;

/* Where a word came from. `words` says which words of the call data, `cell` which
storage cell of the run's table, `call` which call out, each counted from one. */
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Tag {
    pub bits: u16,
    pub words: u32,
    pub cell: u16,
    pub call: u16,
}

fn merge(a: u16, b: u16) -> u16 {
    match (a, b) {
        (0, x) | (x, 0) => x,
        (x, y) if x == y => x,
        _ => MANY,
    }
}

impl Tag {
    pub const NONE: Tag = Tag {
        bits: 0,
        words: 0,
        cell: 0,
        call: 0,
    };

    #[must_use]
    pub const fn of(bits: u16) -> Tag {
        Tag {
            bits,
            words: 0,
            cell: 0,
            call: 0,
        }
    }

    #[must_use]
    pub fn data(byte: usize) -> Tag {
        match byte.checked_sub(4).map(|b| b / 32) {
            None => Tag::of(CHOICE),
            Some(word) => Tag {
                words: Some(word).filter(|w| *w < DATA_WORDS).map_or(0, |w| 1 << w),
                ..Tag::of(DATA)
            },
        }
    }

    // A word worked out from constants alone is a constant.
    #[must_use]
    pub fn settled(self) -> Tag {
        match self.bits & !WORKED {
            0 => Tag::NONE,
            _ => self,
        }
    }

    #[must_use]
    pub fn join(self, other: Tag) -> Tag {
        Tag {
            bits: self.bits | other.bits,
            words: self.words | other.words,
            cell: merge(self.cell, other.cell),
            call: merge(self.call, other.call),
        }
    }

    #[must_use]
    pub fn with(self, bits: u16) -> Tag {
        Tag {
            bits: self.bits | bits,
            ..self
        }
    }

    #[must_use]
    pub fn has(self, bits: u16) -> bool {
        self.bits & bits != 0
    }

    #[must_use]
    pub fn is_none(self) -> bool {
        self.bits == 0
    }

    // The word is that source and nothing else, whatever was compared or masked on the way.
    #[must_use]
    pub fn only(self, bits: u16) -> bool {
        self.bits & !CMP == bits
    }

    #[must_use]
    pub fn word(self) -> Option<usize> {
        (self.words.count_ones() == 1).then(|| self.words.trailing_zeros() as usize)
    }

    #[must_use]
    pub fn cell(self) -> Option<usize> {
        (self.cell != 0 && self.cell != MANY).then(|| self.cell as usize - 1)
    }

    #[must_use]
    pub fn call(self) -> Option<usize> {
        (self.call != 0 && self.call != MANY).then(|| self.call as usize - 1)
    }
}

#[must_use]
pub fn join_all(tags: &[Tag]) -> Tag {
    tags.iter().fold(Tag::NONE, |a, b| a.join(*b))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Key {
    pub value: U256,
    pub tag: Tag,
}

/* A storage cell as the code reaches it: the slot the compiler gave the variable, the
keys hashed onto it, and a field offset. A plain variable has no keys. */
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cell {
    pub account: U256,
    pub slot: U256,
    pub root: U256,
    pub keys: Vec<Key>,
    pub offset: u64,
}

impl Cell {
    // The variable, whichever entry of it this is.
    #[must_use]
    pub fn place(&self) -> Place {
        Place {
            account: self.account,
            root: self.root,
            depth: self.keys.len(),
            offset: self.offset,
        }
    }

    #[must_use]
    pub fn keyed_by(&self, who: U256) -> bool {
        self.keys.iter().any(|k| k.value == who)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Place {
    pub account: U256,
    pub root: U256,
    pub depth: usize,
    pub offset: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Answered {
    Code,
    Books,
    Blank,
    BuiltIn,
    Taken,
}

#[derive(Clone, Debug)]
pub struct CallOut {
    pub depth: usize,
    pub pc: usize,
    pub kind: u8,
    pub from: U256,
    pub to: U256,
    pub value: U256,
    pub input: Vec<u8>,
    pub to_tag: Tag,
    pub value_tag: Tag,
    pub arg_tags: Vec<Tag>,
    // Where the first byte of what was sent came from.
    pub input_from: Tag,
    pub ok: bool,
    pub by: Answered,
    // Whether the code looked at how the call went before it ended.
    pub checked: bool,
    pub output: Vec<u8>,
}

#[derive(Clone, Debug)]
pub enum Event {
    Load {
        cell: usize,
        value: U256,
    },
    Store {
        cell: usize,
        old: U256,
        new: U256,
        tag: Tag,
        pc: usize,
    },
    Cmp {
        pc: usize,
        op: u8,
        a: U256,
        b: U256,
        ta: Tag,
        tb: Tag,
    },
    Branch {
        pc: usize,
        taken: bool,
        tag: Tag,
        depth: usize,
    },
    Call(usize),
    Returned(usize),
    Pay {
        asset: Option<U256>,
        from: U256,
        to: U256,
        amount: U256,
        to_tag: Tag,
        amount_tag: Tag,
    },
    Destroy {
        account: U256,
        to: U256,
        tag: Tag,
    },
    Overflow {
        pc: usize,
        op: u8,
        tag: Tag,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Halt {
    Done,
    Reverted,
    Invalid,
    Steps,
    Fault,
}

// One message from outside with everything it led to.
#[derive(Clone, Debug)]
pub struct Run {
    pub ok: bool,
    pub halt: Halt,
    pub output: Vec<u8>,
    pub events: Vec<Event>,
    pub cells: Vec<Cell>,
    pub calls: Vec<CallOut>,
    pub edges: Vec<u32>,
    pub steps: u64,
    pub hooked: bool,
}

impl Run {
    #[must_use]
    pub fn cell_of(&self, tag: Tag) -> Option<&Cell> {
        tag.cell().and_then(|i| self.cells.get(i))
    }

    pub fn stores(&self) -> impl Iterator<Item = (&Cell, U256, U256, Tag, usize)> {
        self.events.iter().filter_map(|e| match e {
            Event::Store {
                cell,
                old,
                new,
                tag,
                pc,
            } => Some((&self.cells[*cell], *old, *new, *tag, *pc)),
            _ => None,
        })
    }

    /* What each cell held when the call began and when it ended, for the cells that ended
    different. A cell written twice in one call is judged by where it ended, since a
    record that falls and then rises higher has not been given up. */
    #[must_use]
    pub fn changes(&self) -> Vec<(&Cell, U256, U256, Tag, usize)> {
        let mut order: Vec<usize> = Vec::new();
        let mut ends: HashMap<usize, (U256, U256, Tag, usize)> = HashMap::new();
        for event in &self.events {
            if let Event::Store {
                cell,
                old,
                new,
                tag,
                pc,
            } = event
            {
                let seen = ends.entry(*cell).or_insert_with(|| {
                    order.push(*cell);
                    (*old, *new, *tag, *pc)
                });
                (seen.1, seen.2, seen.3) = (*new, *tag, *pc);
            }
        }
        let net = order.into_iter().map(|cell| (cell, ends[&cell]));
        net.filter(|(_, (old, new, _, _))| old != new)
            .map(|(cell, (old, new, tag, pc))| (&self.cells[cell], old, new, tag, pc))
            .collect()
    }

    pub fn loads(&self) -> impl Iterator<Item = (&Cell, U256)> {
        self.events.iter().filter_map(|e| match e {
            Event::Load { cell, value } => Some((&self.cells[*cell], *value)),
            _ => None,
        })
    }
}
