use crate::model::Facts;
use crate::trace::{Cell, Event, Run, Tag, DATA};
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
    PayoutOnReading,
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
    pub paid_before: U256,
    pub victim: Option<Addr>,
    pub cell: Option<Cell>,
    pub call: Option<usize>,
}

/* What the account gained in a call somebody else made. A user's own call that pays
the account does so because of something the account did before. `base` is the world
before the account first acted. Being handed back what it paid in since is no gain. */
#[must_use]
pub fn diverted(base: &World, before: &World, after: &World) -> Option<Breach> {
    let mut kinds: Vec<Option<Addr>> = vec![None];
    kinds.extend(after.assets().into_iter().map(Some));
    let floor = |a: Option<Addr>| of_party(before, a).max(of_party(base, a));
    let none_less = kinds.iter().all(|a| {
        of_party(after, *a) >= of_party(before, *a) && of_party(after, *a) >= of_party(base, *a)
    });
    let most = kinds
        .iter()
        .filter(|a| of_party(after, **a) > floor(**a))
        .map(|a| (of_party(after, *a).wrapping_sub(floor(*a)), *a))
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
        paid_before: U256::ZERO,
        victim: None,
        cell: None,
        call: None,
    }
}

/* `base` is the world before the account made its first call, `before` and `after`
are around its latest call, and `run` is that call. */
/* How much the account gave up, in a call, of the claims it held before it first
acted. A record it built by paying in during these calls is already counted as what it
paid, so only the part of a fall that goes below the starting level counts here. */
#[must_use]
pub fn claims_lowered(run: &Run, subject: Addr, base: &World) -> U256 {
    let changes = run.changes();
    let own = changes.iter().filter(|(c, old, new, _, _)| {
        c.account == subject && (c.keyed_by(ACTOR) || c.keyed_by(ALLY)) && new < old
    });
    own.fold(U256::ZERO, |sum, (cell, old, new, _, _)| {
        let started = base.stored(subject, cell.slot);
        sum.wrapping_add(*old.min(&started) - *new.min(&started))
    })
}

fn party(who: Addr) -> bool {
    Facts::same_party(who, ACTOR)
}

fn own_record(cell: &Cell) -> bool {
    cell.keyed_by(ACTOR) || cell.keyed_by(ALLY)
}

struct Paid {
    asset: Option<Addr>,
    other: Addr,
    sum: U256,
    largest: U256,
    tag_of_largest: Tag,
}

fn payments(run: &Run, to_account: bool) -> Vec<Paid> {
    let mut all: Vec<Paid> = Vec::new();
    for event in &run.events {
        let Event::Pay {
            asset,
            from,
            to,
            amount,
            amount_tag,
            ..
        } = event
        else {
            continue;
        };
        if amount.is_zero() || party(*from) == party(*to) || party(*to) != to_account {
            continue;
        }
        let other = if to_account { *from } else { *to };
        match all
            .iter_mut()
            .find(|p| (p.asset, p.other) == (*asset, other))
        {
            Some(paid) => {
                paid.sum = paid.sum.wrapping_add(*amount);
                if *amount > paid.largest {
                    (paid.largest, paid.tag_of_largest) = (*amount, *amount_tag);
                }
            }
            None => all.push(Paid {
                asset: *asset,
                other,
                sum: *amount,
                largest: *amount,
                tag_of_largest: *amount_tag,
            }),
        }
    }
    all
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Moved {
    taken: Vec<Option<Addr>>,
    given: Vec<Option<Addr>>,
    raised: bool,
    lowered: bool,
}

impl Moved {
    #[must_use]
    pub fn nothing(&self) -> bool {
        *self == Moved::default()
    }
}

#[must_use]
pub fn moved(run: &Run) -> Moved {
    let assets = |to_account: bool| {
        let paid = payments(run, to_account);
        let mut assets: Vec<Option<Addr>> = paid.iter().map(|p| p.asset).collect();
        assets.sort();
        assets.dedup();
        assets
    };
    let changes = run.changes();
    let own = changes.iter().filter(|(c, ..)| own_record(c));
    Moved {
        taken: assets(true),
        given: assets(false),
        raised: own.clone().any(|(_, old, new, _, _)| new > old),
        lowered: own.clone().any(|(_, old, new, _, _)| new < old),
    }
}

/* `first` and `second` are the same call by the account, before and after its own step
on the accounts in `acted_on`. Ending ahead is not asked for. The step here is a plain
gift that costs more than the call pays, and on a live chain the same reading is moved
with borrowed value that is taken back afterwards. */
#[must_use]
pub fn swayed(first: &Run, second: &Run, after: &World, acted_on: &[Addr]) -> Vec<Breach> {
    let subject = after.subject;
    let (took, takes) = (payments(first, true), payments(second, true));
    let gave = |run: &Run| {
        let given = payments(run, false).into_iter();
        let mut given: Vec<_> = given.map(|p| (p.asset, p.other, p.sum)).collect();
        given.sort();
        given
    };
    let lowered = |run: &Run| {
        let changes = run.changes();
        let falls = changes
            .iter()
            .filter(|(c, old, new, _, _)| own_record(c) && new < old);
        falls.fold(U256::ZERO, |sum, (_, old, new, _, _)| {
            sum.wrapping_add(*old - *new)
        })
    };
    let same_given = gave(first) == gave(second) && lowered(first) == lowered(second);
    /* Where an account the step was made on pays out more than before, the extra may be
    what the step put there or set free there. That is not taken from the contract,
    whoever hands it on. */
    let paid_by = |run: &Run, kind: Option<Addr>| {
        let pays = run.events.iter().filter_map(|e| match e {
            Event::Pay {
                asset,
                from,
                amount,
                ..
            } if *asset == kind && acted_on.contains(from) => Some(*amount),
            _ => None,
        });
        pays.fold(U256::ZERO, |sum, amount| sum.wrapping_add(amount))
    };
    let mut kinds: Vec<Option<Addr>> = vec![None];
    kinds.extend(after.assets().into_iter().map(Some));
    let from_there = kinds
        .iter()
        .any(|k| paid_by(second, *k) > paid_by(first, *k));
    if !first.ok || !second.ok || !same_given || from_there {
        return Vec::new();
    }
    /* A payout that falls is sized by the reading as much as one that rises. It is told
    apart from an account acted on handing on less by asking that those pay the same. */
    let same_there = kinds
        .iter()
        .all(|k| paid_by(second, *k) == paid_by(first, *k));
    let moved = |now: U256, before: U256| now > before || (same_there && now < before);
    let mut found = Vec::new();
    for paid in takes {
        let (asset, payer, amount) = (paid.asset, paid.other, paid.sum);
        let theirs = payer == subject || !after.runs_code(payer);
        let before = took.iter().find(|t| (t.asset, t.other) == (asset, payer));
        let paid_before = before.map_or(U256::ZERO, |t| t.sum);
        let sized = paid.tag_of_largest.read_outside();
        if theirs && !acted_on.contains(&payer) && moved(amount, paid_before) && sized {
            found.push(Breach {
                asset,
                amount,
                paid_before,
                ..bare(Kind::PayoutOnReading)
            });
        }
    }
    let top = U256::ONE << 255;
    /* What another contract mints the account at this one's word is paid out as much
    as what this one records. An asset's own books are left out where the move was
    already seen as a payment. */
    let rises = |run: &Run| -> Vec<(Cell, U256, Tag)> {
        let paid = payments(run, true);
        let seen = |c: &Cell| paid.iter().any(|p| p.asset == Some(c.account));
        let changes = run.changes();
        let up = changes.iter().filter(|(c, old, new, _, _)| {
            let elsewhere = c.account != subject;
            let counted = elsewhere && (seen(c) || acted_on.contains(&c.account));
            own_record(c) && !counted && new > old && *new < top
        });
        up.map(|(c, old, new, tag, _)| ((*c).clone(), *new - *old, *tag))
            .collect()
    };
    let rose = rises(first);
    for (cell, amount, tag) in rises(second) {
        let same = |r: &&(Cell, U256, Tag)| (r.0.account, r.0.slot) == (cell.account, cell.slot);
        let before = rose.iter().find(same);
        let paid_before = before.map_or(U256::ZERO, |r| r.1);
        if amount > paid_before && tag.read_outside() {
            found.push(Breach {
                amount,
                paid_before,
                total: after.stored(cell.account, cell.slot),
                cell: Some(cell),
                ..bare(Kind::PayoutOnReading)
            });
        }
    }
    found
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
    /* No deployed contract sits at an address that is a small number. Where the code
    spoke to one as an asset it read an amount as an address, and more of that is no
    gain. What was paid there still counts as paid. */
    let real = |asset: &Option<Addr>| asset.is_none_or(|a| a.bits() > 96);

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
    let own = spent.wrapping_add(claims_lowered(run, subject, base));
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
        /* A payout for a claim the account gave up is measured in other units than the
        claim, so the two cannot be weighed. Where the claim is one the set-up handed
        out, the payout shows nothing. Where the account built it by paying in, what it
        paid is already counted. */
        most.filter(|(_, asset)| own.is_zero() && real(asset)),
    ) {
        found.push(Breach {
            asset,
            amount,
            ..bare(Kind::Gain)
        });
    }

    let ledger = |cell: &Cell| facts.places.get(&cell.place()).is_some_and(|p| p.ledger());
    let own = |cell: &Cell| cell.account == subject;
    let changes = run.changes();
    let rose_for = |who: Addr| {
        let mut stores = changes.iter();
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
    let mut stores = changes.iter();
    let gave_up =
        stores.any(|(c, old, new, _, _)| own(c) && ledger(c) && actor_keyed(c) && new < old);
    /* The contract told another contract to do something with the caller's address in
    hand, and nobody here keeps books for what that was. It may have been the payment. */
    let paid_elsewhere = run.calls.iter().any(|c| {
        let acted = c.kind == op::CALL && c.ok && c.by == crate::trace::Answered::Blank;
        acted && c.arg_tags.iter().any(|t| t.only(crate::trace::CALLER))
    });
    let top = U256::ONE << 255;
    /* What fell, in this call, in records kept under the account's own address. A rise
    in one of its records that is no more than that is its own claim moved from one
    record to another. So is a rise no more than what it drew down in earlier calls,
    put back. */
    let moved = changes
        .iter()
        .filter(|(c, old, new, _, _)| own(c) && actor_keyed(c) && new < old && *old < top)
        .fold(U256::ZERO, |sum, (_, old, new, _, _)| {
            sum.wrapping_add(*old - *new)
        });
    for (cell, old, new, tag, _) in changes.iter().copied() {
        // A value past half the range is a signed number below zero, not a holding.
        if !own(cell) || old >= top || new >= top {
            continue;
        }
        let place = facts.places.get(&cell.place());
        // Whether a record that rose is worth anything is for the caller to show by using it.
        let others = cell.keyed_by(USER) || cell.keyed_by(OWNER);
        if actor_keyed(cell)
            && !others
            && new > old
            && new - old > moved.wrapping_add(spent)
            && paid_nothing
            && !gave_up
            && !paid_elsewhere
            && !made_up(&tag)
        {
            found.push(Breach {
                amount: new - old,
                total: new,
                cell: Some(cell.clone()),
                ..bare(Kind::Credit)
            });
        }
        if ledger(cell) {
            let person = [USER, OWNER].into_iter().find(|v| cell.keyed_by(*v));
            /* A contract read from the chain has holders this world did not make. One
            that is on neither side of the call, and has no other record rise in it, is
            an account like the user. */
            let stranger = |v: &U256| {
                (97..=160).contains(&v.bits()) && !Facts::same_party(*v, ACTOR) && *v != subject
            };
            let mut keyed = cell.keys.iter().map(|k| k.value);
            // What a contract called on the way lowers of its own record it spent itself.
            let spent = run.spent_by_holder.iter().any(|i| &run.cells[*i] == cell);
            let bystander = keyed.find(stranger).filter(|v| !spent && !rose_for(*v));
            let victim = person.or(bystander);
            let paid_out = |v: Addr| {
                kinds
                    .iter()
                    .any(|a| of_one(after, *a, v) > of_one(before, *a, v))
            };
            let real = !made_up(&tag);
            // A record that passes to the account for a payment was bought.
            let bought = kinds
                .iter()
                .any(|a| of_party(after, *a) < of_party(before, *a));
            if let Some(victim) = victim
                .filter(|v| real && !bought && !actor_keyed(cell) && new < old && !paid_out(*v))
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::SUBJECT;

    #[test]
    fn being_handed_back_what_it_paid_in_is_no_gain_for_the_account() {
        let base = World::new();
        let mut paid = base.clone();
        assert!(paid.give(None, ACTOR, SUBJECT, U256::from_u64(5)));
        let mut refunded = paid.clone();
        assert!(refunded.give(None, SUBJECT, ACTOR, U256::from_u64(5)));
        assert!(diverted(&base, &paid, &refunded).is_none());
        let mut more = refunded.clone();
        assert!(more.give(None, USER, ACTOR, U256::from_u64(2)));
        let gain = diverted(&base, &paid, &more).expect("two more than it started with");
        assert_eq!(gain.amount, U256::from_u64(2));
    }
}
