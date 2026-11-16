use crate::model::Facts;
use crate::trace::{Cell, Event, Run, DATA};
use crate::world::{Addr, World, ACTOR, ALLY, OWNER, USER};
use evmdec::opcode as op;
use evmdec::U256;
use serde::Serialize;

/* What an account with no role must not be able to bring about. Each is a consequence
seen in a run, not a shape in the code. */
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Kind {
    // The account ends with more than it started with and gave nothing for it.
    Gain,
    // Another account ends with less of what it holds outside the contract.
    Loss,
    // The contract's own records credit the account with value it did not pay for.
    Credit,
    // The contract's own records of another account are lowered.
    Debit,
    // A cell the contract compares its caller with now names the account.
    Takeover,
    // The same cell no longer names anyone.
    RoleCleared,
    // The contract ran, as itself, code at an address the account chose.
    ForeignCode,
    // The contract's code was destroyed.
    Destroyed,
}

#[derive(Clone, Debug)]
pub struct Breach {
    pub kind: Kind,
    // The asset that moved. None is ether.
    pub asset: Option<Addr>,
    pub amount: U256,
    // What the record holds after the call, where the breach is about a record.
    pub total: U256,
    pub victim: Option<Addr>,
    pub cell: Option<Cell>,
    pub call: Option<usize>,
}

/* What the account gained in a call somebody else made. A user's own call that pays
the account does so because of something the account did before. */
#[must_use]
pub fn diverted(before: &World, after: &World) -> Option<Breach> {
    let mut kinds: Vec<Option<Addr>> = vec![None];
    kinds.extend(after.assets().into_iter().map(Some));
    let none_less = kinds
        .iter()
        .all(|a| of_party(after, *a) >= of_party(before, *a));
    let most = kinds
        .iter()
        .filter(|a| of_party(after, **a) > of_party(before, **a))
        .map(|a| (of_party(after, *a).wrapping_sub(of_party(before, *a)), *a))
        .max();
    let (amount, asset) = most.filter(|_| none_less)?;
    Some(Breach {
        asset,
        amount,
        ..bare(Kind::Gain)
    })
}

fn of_party(world: &World, asset: Option<Addr>) -> U256 {
    let of = |who: Addr| match asset {
        Some(asset) => world.asset_of(asset, who),
        None => world.ether_of(who),
    };
    of(ACTOR).wrapping_add(of(ALLY))
}

fn of_one(world: &World, asset: Option<Addr>, who: Addr) -> U256 {
    match asset {
        Some(asset) => world.asset_of(asset, who),
        None => world.ether_of(who),
    }
}

fn low_address(value: U256) -> Addr {
    value & ((U256::ONE << 160) - U256::ONE)
}

fn bare(kind: Kind) -> Breach {
    Breach {
        kind,
        asset: None,
        amount: U256::ZERO,
        total: U256::ZERO,
        victim: None,
        cell: None,
        call: None,
    }
}

/* `base` is the world before the account made its first call, `before` and `after`
are around its latest call, and `run` is that call. */
// How much of its own recorded claims the account gave up in a call.
#[must_use]
pub fn claims_lowered(run: &Run, subject: Addr) -> U256 {
    let own = run.stores().filter(|(c, old, new, _, _)| {
        c.account == subject && (c.keyed_by(ACTOR) || c.keyed_by(ALLY)) && new < old
    });
    own.fold(U256::ZERO, |sum, (_, old, new, _, _)| {
        sum.wrapping_add(old - new)
    })
}

/* `spent` is what the account gave up of its own recorded claims in earlier calls. An
account that is paid what its entry was lowered by took out what was its own. */
#[must_use]
pub fn check(
    base: &World,
    before: &World,
    after: &World,
    run: &Run,
    facts: &Facts,
    spent: U256,
) -> Vec<Breach> {
    let mut found = Vec::new();
    let subject = after.subject;
    let mut kinds: Vec<Option<Addr>> = vec![None];
    kinds.extend(after.assets().into_iter().map(Some));

    let change = |asset: &Option<Addr>| (of_party(base, *asset), of_party(after, *asset));
    let none_less = kinds.iter().all(|a| change(a).1 >= change(a).0);
    let stepped = kinds
        .iter()
        .any(|a| of_party(after, *a) > of_party(before, *a));
    let most = kinds
        .iter()
        .map(|a| (change(a).1.wrapping_sub(change(a).0), *a))
        .filter(|(_, a)| change(a).1 > change(a).0)
        .max();
    let own = spent.wrapping_add(claims_lowered(run, subject));
    /* What a contract passes on because another contract said it had just sent that
    much is not the contract's own. Here nobody keeps books for such an answer, so a
    payment sized by one shows nothing. */
    let made_up = |tag: &crate::trace::Tag| {
        let asked = tag.call().and_then(|k| run.calls.get(k));
        tag.has(crate::trace::OUT) && asked.is_none_or(|c| c.by != crate::trace::Answered::Books)
    };
    let to_party = |e: &&Event| match e {
        Event::Pay { to, amount, .. } => Facts::same_party(*to, ACTOR) && !amount.is_zero(),
        _ => false,
    };
    let sized_by_answer =
        |e: &Event| matches!(e, Event::Pay { amount_tag, .. } if made_up(amount_tag));
    let pays: Vec<&Event> = run.events.iter().filter(to_party).collect();
    let rests_on_answer = !pays.is_empty() && pays.iter().all(|e| sized_by_answer(e));
    if let (true, true, Some((amount, asset))) = (
        none_less,
        stepped && !rests_on_answer,
        most.filter(|(amount, _)| *amount > own),
    ) {
        found.push(Breach {
            asset,
            amount,
            ..bare(Kind::Gain)
        });
    }

    let ledger = |cell: &Cell| facts.places.get(&cell.place()).is_some_and(|p| p.ledger());
    let own = |cell: &Cell| cell.account == subject;
    let rose_for = |who: Addr| {
        let mut stores = run.stores();
        stores.any(|(c, old, new, _, _)| own(c) && ledger(c) && c.keyed_by(who) && new > old)
    };
    for victim in [USER, OWNER] {
        for asset in &kinds {
            let (was, now) = (
                of_one(before, *asset, victim),
                of_one(after, *asset, victim),
            );
            // An account whose payment was credited to it in the contract's records lost nothing.
            if now < was && !rose_for(victim) {
                found.push(Breach {
                    asset: *asset,
                    amount: was - now,
                    victim: Some(victim),
                    ..bare(Kind::Loss)
                });
            }
        }
    }

    let paid_nothing = kinds
        .iter()
        .all(|a| of_party(after, *a) >= of_party(base, *a));
    let actor_keyed = |c: &Cell| c.keyed_by(ACTOR) || c.keyed_by(ALLY);
    let mut stores = run.stores();
    let gave_up =
        stores.any(|(c, old, new, _, _)| own(c) && ledger(c) && actor_keyed(c) && new < old);
    for (cell, old, new, _, _) in run.stores() {
        if !own(cell) {
            continue;
        }
        let place = facts.places.get(&cell.place());
        // Whether a record that rose is worth anything is for the caller to show by using it.
        let others = cell.keyed_by(USER) || cell.keyed_by(OWNER);
        if actor_keyed(cell) && !others && new > old && paid_nothing && !gave_up {
            found.push(Breach {
                amount: new - old,
                total: new,
                cell: Some(cell.clone()),
                ..bare(Kind::Credit)
            });
        }
        if ledger(cell) {
            let victim = [USER, OWNER].into_iter().find(|v| cell.keyed_by(*v));
            let paid_out = |v: Addr| {
                kinds
                    .iter()
                    .any(|a| of_one(after, *a, v) > of_one(before, *a, v))
            };
            if let Some(victim) =
                victim.filter(|v| !actor_keyed(cell) && new < old && !paid_out(*v))
            {
                found.push(Breach {
                    amount: old - new,
                    total: old,
                    victim: Some(victim),
                    cell: Some(cell.clone()),
                    ..bare(Kind::Debit)
                });
            }
        }
        if place.is_some_and(|p| p.identity) {
            let (was, now) = (low_address(old), low_address(new));
            // An entry kept for the account itself is its own to set.
            let own_entry = cell.keys.iter().any(|k| Facts::same_party(k.value, ACTOR));
            let held_by_other = (was == OWNER || was == USER) && !own_entry;
            // A place that is bought, such as the highest bid, changes hands by design.
            let free = kinds
                .iter()
                .all(|a| of_party(after, *a) >= of_party(before, *a));
            if held_by_other && now != was && free {
                let kind = match now.is_zero() {
                    true => Kind::RoleCleared,
                    false => Kind::Takeover,
                };
                found.push(Breach {
                    victim: Some(was),
                    cell: Some(cell.clone()),
                    ..bare(kind)
                });
            }
        }
    }

    for (index, call) in run.calls.iter().enumerate() {
        let in_own_storage =
            matches!(call.kind, op::DELEGATECALL | op::CALLCODE) && call.from == subject;
        let chosen = call.to_tag.has(DATA) || Facts::same_party(call.to, ACTOR);
        if in_own_storage && chosen {
            found.push(Breach {
                call: Some(index),
                ..bare(Kind::ForeignCode)
            });
        }
    }
    let destroyed = |e: &Event| matches!(e, Event::Destroy { account, .. } if *account == subject);
    if run.events.iter().any(destroyed) {
        found.push(bare(Kind::Destroyed));
    }
    found
}
