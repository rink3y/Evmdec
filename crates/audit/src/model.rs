use crate::trace::{Event, Place, Run, CALLER, DATA, MATH, ORIGIN, STORE, VALUE};
use crate::world::{Addr, Msg, ALLY, OWNER};
use evmdec::opcode as op;
use evmdec::U256;
use std::collections::{BTreeMap, BTreeSet};

/* What the runs showed a storage variable is used for. Nothing here comes from a
name or a known layout. A variable is an identity because the code compared it with
the caller, a ledger because its entries moved with value. */
#[derive(Clone, Debug, Default)]
pub struct PlaceFacts {
    pub loads: u32,
    pub stores: u32,
    pub writers: BTreeSet<usize>,
    pub open_writers: BTreeSet<usize>,
    pub readers: BTreeSet<usize>,
    pub keyed_by_caller: bool,
    pub keyed_by_account: bool,
    pub identity: bool,
    pub gate: bool,
    pub arithmetic: bool,
    pub moved_with_value: bool,
    pub transfers: bool,
    pub target: bool,
    pub assumed: bool,
}

impl PlaceFacts {
    #[must_use]
    pub fn ledger(&self) -> bool {
        self.keyed_by_account && self.arithmetic && (self.moved_with_value || self.transfers)
    }
}

#[derive(Clone, Debug, Default)]
pub struct EntryFacts {
    pub ended: BTreeSet<Addr>,
    pub refused: BTreeSet<Addr>,
    pub checks_caller: bool,
    pub pays_out: bool,
    pub takes_in: bool,
    pub calls_out: bool,
    pub runs_other_code: bool,
    pub target_words: BTreeSet<usize>,
    pub reads: BTreeSet<Place>,
    pub writes: BTreeSet<Place>,
}

#[derive(Clone, Debug, Default)]
pub struct Facts {
    pub places: BTreeMap<Place, PlaceFacts>,
    pub entries: Vec<EntryFacts>,
}

fn names_account(value: U256, known: &[Addr]) -> bool {
    !value.is_zero() && value.bits() <= 160 && known.contains(&value)
}

impl Facts {
    #[must_use]
    pub fn new(entries: usize) -> Facts {
        Facts {
            places: BTreeMap::new(),
            entries: vec![EntryFacts::default(); entries],
        }
    }

    #[allow(clippy::too_many_lines)]
    pub fn observe(&mut self, entry: usize, msg: &Msg, run: &Run, subject: Addr, known: &[Addr]) {
        let who = msg.from;
        let facts = &mut self.entries[entry];
        match run.ok {
            true => facts.ended.insert(who),
            false => facts.refused.insert(who),
        };
        for cell in &run.cells {
            if cell.account != subject {
                continue;
            }
            let place = self.places.entry(cell.place()).or_default();
            let by_caller = |t: &crate::trace::Tag| t.only(CALLER) || t.only(ORIGIN);
            place.keyed_by_caller |= cell.keys.iter().any(|k| by_caller(&k.tag));
            let account =
                |k: &crate::trace::Key| by_caller(&k.tag) || names_account(k.value, known);
            place.keyed_by_account |= cell.keys.iter().any(account);
        }
        for event in &run.events {
            match event {
                Event::Load { cell, .. } => {
                    let cell = &run.cells[*cell];
                    if cell.account == subject {
                        let place = self.places.entry(cell.place()).or_default();
                        place.loads += 1;
                        place.readers.insert(entry);
                        facts.reads.insert(cell.place());
                    }
                }
                Event::Cmp { op: o, ta, tb, .. } if *o == op::EQ => {
                    for (caller, other) in [(ta, tb), (tb, ta)] {
                        // Older compilers divide a packed slot down to the address before comparing it.
                        let stored = other.has(STORE) && !other.has(DATA) && other.cell().is_some();
                        if !caller.only(CALLER) || !stored {
                            continue;
                        }
                        facts.checks_caller = true;
                        if let Some(cell) = run.cell_of(*other).filter(|c| c.account == subject) {
                            self.places.entry(cell.place()).or_default().identity = true;
                        }
                    }
                }
                Event::Branch { tag, .. } => {
                    facts.checks_caller |= tag.has(CALLER);
                    let alone = tag.has(STORE) && !tag.has(DATA | VALUE | MATH);
                    let cell = run.cell_of(*tag).filter(|c| c.account == subject);
                    if let Some(cell) = cell.filter(|_| alone) {
                        if cell.keys.iter().any(|k| k.tag.only(CALLER)) {
                            facts.checks_caller = true;
                            self.places.entry(cell.place()).or_default().gate = true;
                        }
                    }
                }
                _ => {}
            }
        }
        for call in &run.calls {
            facts.calls_out = true;
            facts.runs_other_code |= matches!(call.kind, op::DELEGATECALL | op::CALLCODE);
            if let Some(word) = call.to_tag.word().filter(|_| call.to_tag.has(DATA)) {
                facts.target_words.insert(word);
            }
            let cell = run.cell_of(call.to_tag).filter(|c| c.account == subject);
            if let Some(cell) = cell.filter(|_| call.to_tag.has(STORE)) {
                self.places.entry(cell.place()).or_default().target = true;
            }
        }
        if !run.ok {
            return;
        }
        let mut movers: Vec<Addr> = Vec::new();
        if !msg.value.is_zero() {
            facts.takes_in = true;
            movers.push(who);
        }
        for event in &run.events {
            if let Event::Pay { from, to, .. } = event {
                facts.pays_out |= *from == subject;
                facts.takes_in |= *to == subject;
                movers.extend([*from, *to]);
            }
        }
        let mut moved: BTreeMap<Place, (bool, bool)> = BTreeMap::new();
        for (cell, old, new, tag, _) in run.stores() {
            if cell.account != subject {
                continue;
            }
            let place = self.places.entry(cell.place()).or_default();
            place.stores += 1;
            place.writers.insert(entry);
            if who != OWNER {
                place.open_writers.insert(entry);
            }
            facts.writes.insert(cell.place());
            place.arithmetic |= tag.has(MATH) && tag.has(STORE);
            let holder = |a: &Addr| *a != subject && cell.keyed_by(*a);
            place.moved_with_value |= movers.iter().any(holder);
            let seen = moved.entry(cell.place()).or_default();
            seen.0 |= new < old;
            seen.1 |= new > old;
        }
        for (place, (down, up)) in moved {
            let facts = self.places.entry(place).or_default();
            facts.transfers |= down && up && place.depth > 0;
        }
    }

    // The accounts a party controls, for telling its own entries from another's.
    #[must_use]
    pub fn same_party(a: Addr, b: Addr) -> bool {
        a == b || (a.0[2] == b.0[2] && a.0[2] == ALLY.0[2])
    }
}
