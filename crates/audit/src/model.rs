use crate::trace::{Event, Place, Run, Tag, BAL, CALLER, DATA, MATH, ORIGIN, OUT, STORE, VALUE};
use crate::world::{Addr, Msg, ALLY, OWNER};
use evmdec::decompile::Contract;
use evmdec::expr;
use evmdec::expr::Node;
use evmdec::lift::{Stmt, Term};
use evmdec::opcode as op;
use evmdec::U256;
use serde::Serialize;
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

/* What the code of one entry function can do, read from the decompiler's lifted form
together with every helper it calls. The facts from runs say what happened. These say
what can, and they cover a function no run got to the end of. */
#[derive(Clone, Debug, Default, Serialize)]
pub struct InCode {
    pub tests_caller: bool,
    pub writes: Vec<String>,
    pub writes_under_keys: bool,
    pub calls_out: bool,
    pub sends_value: bool,
    pub runs_other_code: bool,
    pub destroys: bool,
}

/* A condition tests the caller when it compares the caller's address with something,
or asks whether an entry kept under the caller is set. A balance kept under the caller
that is weighed against an amount is a test of the balance, and anyone can have one. */
fn tests_caller(cond: expr::ExprId) -> bool {
    let caller = |n: &Node| matches!(n, Node::Env(o, _) if *o == op::CALLER);
    let mut direct = false;
    let mut keyed = false;
    let mut weighed = false;
    let mut todo = vec![cond];
    let mut seen: BTreeSet<expr::ExprId> = BTreeSet::new();
    while let Some(e) = todo.pop() {
        if !seen.insert(e) {
            continue;
        }
        match expr::node(e) {
            Node::SLoad(key, ..) => keyed |= expr::contains(key, &caller),
            n if caller(&n) => direct = true,
            Node::Op(op::LT | op::GT | op::SLT | op::SGT, _) => {
                weighed = true;
                todo.extend(expr::children(e));
            }
            _ => todo.extend(expr::children(e)),
        }
    }
    direct || (keyed && !weighed)
}

/* How one fixed storage slot is used across the entry functions, read from the code.
This is the flow of state between functions: what one writes, another compares its
caller with, calls, or sends. Entries kept under keys are not followed here. */
#[derive(Clone, Debug, Default, Serialize)]
pub struct SlotInCode {
    pub slot: String,
    pub written_by: Vec<String>,
    pub read_by: Vec<String>,
    pub compared_with_caller_in: Vec<String>,
    pub called_in: Vec<String>,
    pub sent_as_amount_in: Vec<String>,
}

fn fixed_slots(e: expr::ExprId, out: &mut BTreeSet<U256>) {
    let mut todo = vec![e];
    let mut seen: BTreeSet<expr::ExprId> = BTreeSet::new();
    while let Some(x) = todo.pop() {
        if !seen.insert(x) {
            continue;
        }
        if let Node::SLoad(key, false, _) = expr::node(x) {
            out.extend(expr::as_const(key));
        }
        todo.extend(expr::children(x));
    }
}

#[must_use]
pub fn slots_in_code(c: &Contract, entries: &[(usize, String)]) -> Vec<SlotInCode> {
    let mut all: BTreeMap<U256, SlotInCode> = BTreeMap::new();
    for (function, name) in entries {
        let mut uses: [BTreeSet<U256>; 5] = Default::default();
        let mut seen: BTreeSet<usize> = BTreeSet::new();
        let mut todo = vec![*function];
        while let Some(index) = todo.pop() {
            let Some(lifted) = c.functions.get(index).and_then(|f| f.lifted.as_ref()) else {
                continue;
            };
            if !seen.insert(index) {
                continue;
            }
            for node in &lifted.nodes {
                for e in evmdec::lift::node_exprs(node) {
                    fixed_slots(e, &mut uses[1]);
                }
                for stmt in &node.stmts {
                    match stmt {
                        Stmt::SStore {
                            key,
                            transient: false,
                            ..
                        } => {
                            uses[0].extend(expr::as_const(*key));
                        }
                        Stmt::Call { addr, value, .. } => {
                            fixed_slots(*addr, &mut uses[3]);
                            if let Some(value) = value {
                                fixed_slots(*value, &mut uses[4]);
                            }
                        }
                        Stmt::Require { cond, .. } if tests_caller(*cond) => {
                            fixed_slots(*cond, &mut uses[2]);
                        }
                        Stmt::Internal { callee, .. } => {
                            todo.extend(c.functions.iter().position(|f| f.pc == *callee));
                        }
                        _ => {}
                    }
                }
                if let Term::Branch { cond, .. } | Term::CondJump { cond, .. } = &node.term {
                    if tests_caller(*cond) {
                        fixed_slots(*cond, &mut uses[2]);
                    }
                }
            }
        }
        for (kind, slots) in uses.iter().enumerate() {
            for slot in slots {
                let entry = all.entry(*slot).or_insert_with(|| SlotInCode {
                    slot: slot.to_hex(),
                    ..SlotInCode::default()
                });
                let list = match kind {
                    0 => &mut entry.written_by,
                    1 => &mut entry.read_by,
                    2 => &mut entry.compared_with_caller_in,
                    3 => &mut entry.called_in,
                    _ => &mut entry.sent_as_amount_in,
                };
                list.push(name.clone());
            }
        }
    }
    all.into_values().collect()
}

#[must_use]
pub fn in_code(c: &Contract, function: usize) -> InCode {
    let mut found = InCode::default();
    let mut slots: BTreeSet<U256> = BTreeSet::new();
    let mut seen: BTreeSet<usize> = BTreeSet::new();
    let mut todo = vec![function];
    let names_caller = tests_caller;
    while let Some(index) = todo.pop() {
        let Some(lifted) = c.functions.get(index).and_then(|f| f.lifted.as_ref()) else {
            continue;
        };
        if !seen.insert(index) {
            continue;
        }
        for node in &lifted.nodes {
            for stmt in &node.stmts {
                match stmt {
                    Stmt::SStore {
                        key,
                        transient: false,
                        ..
                    } => match expr::as_const(*key) {
                        Some(slot) => drop(slots.insert(slot)),
                        None => found.writes_under_keys = true,
                    },
                    Stmt::Call {
                        kind, addr, value, ..
                    } => {
                        // The built-in contracts sit at the lowest addresses and are part of the machine.
                        let built_in = expr::as_const(*addr).is_some_and(|a| a.bits() <= 8);
                        if built_in || *kind == op::STATICCALL {
                            continue;
                        }
                        found.calls_out = true;
                        found.runs_other_code |= matches!(*kind, op::DELEGATECALL | op::CALLCODE);
                        let nothing = |v: &expr::ExprId| expr::as_const(*v) == Some(U256::ZERO);
                        found.sends_value |= value.as_ref().is_some_and(|v| !nothing(v));
                    }
                    Stmt::Create { .. } => found.calls_out = true,
                    Stmt::Require { cond, .. } => found.tests_caller |= names_caller(*cond),
                    Stmt::Internal { callee, .. } => {
                        todo.extend(c.functions.iter().position(|f| f.pc == *callee));
                    }
                    _ => {}
                }
            }
            match &node.term {
                Term::SelfDestruct(_) => found.destroys = true,
                Term::Branch { cond, .. } | Term::CondJump { cond, .. } => {
                    found.tests_caller |= names_caller(*cond);
                }
                _ => {}
            }
        }
    }
    found.writes = slots.iter().map(U256::to_hex).collect();
    found
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
    fn the_code_says_which_functions_test_their_caller_and_what_each_can_do() {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../testdata/source/Vault.hex"
        );
        let hex = std::fs::read_to_string(path).expect("fixture");
        let code = evmdec::hex::decode(hex.trim()).expect("hex");
        let contract = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default());
        let of = |selector: &str| {
            let at = |f: &evmdec::decompile::Function| f.selector.as_deref() == Some(selector);
            in_code(
                &contract,
                contract.functions.iter().position(at).expect("function"),
            )
        };
        // rescue(address) is the guarded twin of sweep(address).
        let (rescue, sweep, set_owner) = (of("0x839006f2"), of("0x01681a62"), of("0x13af4035"));
        assert!(rescue.tests_caller && rescue.sends_value);
        assert!(!sweep.tests_caller && sweep.sends_value);
        assert!(!set_owner.tests_caller && set_owner.writes == vec!["0x0".to_string()]);
        // deposit() weighs the caller's balance in an overflow check, which tests nobody.
        assert!(!of("0xd0e30db0").tests_caller);
        let entry = |selector: &str| {
            let at = |f: &evmdec::decompile::Function| f.selector.as_deref() == Some(selector);
            let index = contract.functions.iter().position(at).expect("function");
            (index, selector.to_string())
        };
        let slots = slots_in_code(&contract, &[entry("0x13af4035"), entry("0x839006f2")]);
        // The open setter writes the slot the guarded function compares its caller with.
        assert_eq!(slots[0].slot, "0x0");
        assert_eq!(slots[0].written_by, vec!["0x13af4035".to_string()]);
        assert_eq!(
            slots[0].compared_with_caller_in,
            vec!["0x839006f2".to_string()]
        );
    }

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
