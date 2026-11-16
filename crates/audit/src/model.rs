use crate::trace::{Event, Place, Run, Tag, BAL, CALLER, DATA, MATH, ORIGIN, OUT, STORE, VALUE};
use crate::world::{Addr, Msg, ALLY, OWNER};
use evmdec::decompile::Contract;
use evmdec::expr;
use evmdec::lift::Stmt;
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
    // An account's entry rose in a call in which that account paid the contract.
    pub rose_on_payment: bool,
    // An account's entry fell in a call in which the contract paid that account.
    pub fell_on_payout: bool,
    // One entry fell and another rose by the same amount in one call.
    pub conserved: bool,
    pub target: bool,
    pub assumed: bool,
    // Some call changed it and put the old value back before it ended.
    pub scoped: bool,
}

impl PlaceFacts {
    #[must_use]
    pub fn ledger(&self) -> bool {
        self.keyed_by_account && (self.rose_on_payment || self.fell_on_payout || self.conserved)
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
    // What an owner-only function pays out of the contract, so what it is meant to hold. None is ether.
    pub keeps: BTreeSet<Option<Addr>>,
}

/* The slots some function writes one fixed value to and then another, on one path, with
the values each is left at. That is a flag raised for the length of a call and lowered
again, such as a lock. Between calls it holds what it is left at, whatever a failed call
seemed to need. */
#[must_use]
pub fn raised_within_a_call(c: &Contract) -> BTreeMap<U256, BTreeSet<U256>> {
    let mut rests: BTreeMap<U256, BTreeSet<U256>> = BTreeMap::new();
    for lifted in c.functions.iter().filter_map(|f| f.lifted.as_ref()) {
        let mut writes: Vec<(usize, usize, U256, U256)> = Vec::new();
        for node in &lifted.nodes {
            for (i, stmt) in node.stmts.iter().enumerate() {
                let Stmt::SStore {
                    key,
                    val,
                    transient: false,
                    ..
                } = stmt
                else {
                    continue;
                };
                if let (Some(slot), Some(value)) = (expr::as_const(*key), expr::as_const(*val)) {
                    writes.push((node.id, i, slot, value));
                }
            }
        }
        let mut raised: BTreeSet<U256> = BTreeSet::new();
        let mut left: Vec<(U256, U256)> = Vec::new();
        for (node, i, slot, value) in &writes {
            let mut ahead = lifted.nodes[*node].succs.clone();
            let mut seen: BTreeSet<usize> = BTreeSet::new();
            while let Some(next) = ahead.pop() {
                if seen.insert(next) {
                    ahead.extend(lifted.nodes[next].succs.iter().copied());
                }
            }
            let later = |(n, j, s, v): &(usize, usize, U256, U256)| {
                s == slot && v != value && (seen.contains(n) || (n == node && j > i))
            };
            if writes.iter().any(later) {
                raised.insert(*slot);
            } else {
                left.push((*slot, *value));
            }
        }
        for (slot, value) in left.into_iter().filter(|(slot, _)| raised.contains(slot)) {
            rests.entry(slot).or_default().insert(value);
        }
    }
    rests
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
            keeps: BTreeSet::new(),
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
            // Ether sent with no message is a payment to an account, not a call to a contract.
            let spoken_to = call.to_tag.has(DATA) && !call.input.is_empty();
            if let Some(word) = call.to_tag.word().filter(|_| spoken_to) {
                facts.target_words.insert(word);
            }
            let cell = run.cell_of(call.to_tag).filter(|c| c.account == subject);
            if let Some(cell) = cell.filter(|_| call.to_tag.has(STORE)) {
                self.places.entry(cell.place()).or_default().target = true;
            }
        }
        let mut ends: BTreeMap<usize, (U256, U256, bool)> = BTreeMap::new();
        for event in &run.events {
            if let Event::Store { cell, old, new, .. } = event {
                let seen = ends.entry(*cell).or_insert((*old, *new, false));
                seen.2 |= seen.1 != *old || new != old;
                seen.1 = *new;
            }
        }
        for (cell, (first, last, moved)) in ends {
            let cell = &run.cells[cell];
            if cell.account == subject && moved && first == last {
                self.places.entry(cell.place()).or_default().scoped = true;
            }
        }
        if !run.ok {
            return;
        }
        let mut payers: Vec<(Addr, Tag)> = Vec::new();
        let mut payees: Vec<(Addr, Tag)> = Vec::new();
        if !msg.value.is_zero() {
            facts.takes_in = true;
            payers.push((who, Tag::of(VALUE)));
        }
        for event in &run.events {
            if let Event::Pay {
                from,
                to,
                amount,
                amount_tag,
                ..
            } = event
            {
                facts.pays_out |= *from == subject;
                facts.takes_in |= *to == subject;
                if *to == subject && !amount.is_zero() {
                    payers.push((*from, *amount_tag));
                }
                if *from == subject && !amount.is_zero() {
                    payees.push((*to, *amount_tag));
                }
            }
        }
        let mut moved: BTreeMap<Place, (Vec<U256>, Vec<U256>)> = BTreeMap::new();
        for event in &run.events {
            let Event::Store {
                cell: index,
                old,
                new,
                tag,
                ..
            } = event
            else {
                continue;
            };
            let cell = &run.cells[*index];
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
            /* The entry and the payment have to be about the same amount. An entry that
            changes in a call that also happens to carry ether is not a record of it. */
            let this = u16::try_from(index + 1).unwrap_or(u16::MAX);
            let about = |paid: &Tag| {
                tag.words & paid.words != 0
                    || (tag.has(VALUE) && paid.has(VALUE))
                    || paid.cell == this
                    || tag.has(OUT | BAL)
            };
            let of_holder =
                |(a, paid): &(Addr, Tag)| *a != subject && cell.keyed_by(*a) && about(paid);
            place.rose_on_payment |= new > old && payers.iter().any(of_holder);
            place.fell_on_payout |= new < old && payees.iter().any(of_holder);
            let seen = moved.entry(cell.place()).or_default();
            if new < old {
                seen.0.push(*old - *new);
            }
            if new > old {
                seen.1.push(*new - *old);
            }
        }
        for (place, (down, up)) in moved {
            let facts = self.places.entry(place).or_default();
            facts.conserved |= place.depth > 0 && down.iter().any(|d| up.contains(d));
        }
    }

    // The accounts a party controls, for telling its own entries from another's.
    #[must_use]
    pub fn same_party(a: Addr, b: Addr) -> bool {
        a == b || (a.0[2] == b.0[2] && a.0[2] == ALLY.0[2])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_lock_rests_at_the_value_it_is_put_back_to_and_a_setting_is_not_a_lock() {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../testdata/source/Locked.hex"
        );
        let hex = std::fs::read_to_string(path).expect("fixture");
        let code = evmdec::hex::decode(hex.trim()).expect("hex");
        let contract = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default());
        let raised = raised_within_a_call(&contract);
        let lock = raised.get(&U256::ONE).expect("slot 1 is the lock");
        assert_eq!(lock.iter().copied().collect::<Vec<_>>(), vec![U256::ONE]);
        assert_eq!(
            raised.len(),
            1,
            "the owner's setting in slot 2 is written once"
        );
    }
}
