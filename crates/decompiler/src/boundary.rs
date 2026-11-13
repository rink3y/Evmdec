use crate::abi::{self, SEL_BALANCE_OF, SEL_TRANSFER, SEL_TRANSFER_FROM};
use crate::analyze::{push, Confidence, Finding, Severity};
use crate::decompile::{Contract, Function};
use crate::deploy;
use crate::exec::{self, FrameRun};
use crate::function::FnKind;
use crate::hex;
use crate::interp::Outcome;
use crate::opcode as op;
use crate::path::{self, Explorers, Limits, Path};
use crate::solve::{word, Free, Inputs};
use crate::u256::U256;
use std::collections::HashMap;

pub const WORK: u64 = 2 * exec::WORK_PER_SECOND;

const LIMITS: Limits = Limits {
    paths: 12,
    runs: 36,
};
const WORDS: usize = 6;
const MAX_ENTRIES: usize = 24;
const MAX_PAY_INS: usize = 3;
// A queue that pays its head from each new payment needs several payments before the
// payer's own entries reach the head.
const MAX_REPEATS: usize = 8;
// Enough beyond what the first account paid that a rule which hands the surplus to
// whoever comes next shows a gain within the repeats above.
const SURPLUS_FACTOR: u64 = 4;
const HOLDER: U256 = U256::from_u64(0xbbbb_bbbb_bbbb_bbbb);
const OUTSIDER: U256 = exec::CALLER;
const UNUSED_SELECTOR: u32 = 0xffff_ffff;
const FIRST_VALUE: u64 = 0x1001;
const SIZES: u32 = 6;
// Another function is tried after these many repeats. After every repeat would spend
// the whole limit on the first pay-in of a large contract.
const CLOSING_AFTER: [usize; 4] = [0, 1, 3, 7];
const MAX_SIZED_CALLS: usize = 3;

// Only what crosses the contract's edge is counted. How the contract records what it
// owes is never read, so a queue, a mapping and a packed record are all judged alike.
#[derive(Clone, Copy, Default)]
struct Moved {
    ether_in: U256,
    ether_out: U256,
    tokens_in: U256,
    tokens_out: U256,
}

impl Moved {
    fn plus(self, other: Moved) -> Moved {
        Moved {
            ether_in: sum(self.ether_in, other.ether_in),
            ether_out: sum(self.ether_out, other.ether_out),
            tokens_in: sum(self.tokens_in, other.tokens_in),
            tokens_out: sum(self.tokens_out, other.tokens_out),
        }
    }

    // More of one asset came back than went in, and the other asset did not pay for it.
    fn gains(self) -> bool {
        let ether = self.ether_out > self.ether_in && self.tokens_out >= self.tokens_in;
        let tokens = self.tokens_out > self.tokens_in && self.ether_out >= self.ether_in;
        ether || tokens
    }

    fn pays_in_only(self) -> bool {
        let pays = !self.ether_in.is_zero() || !self.tokens_in.is_zero();
        pays && self.ether_out.is_zero() && self.tokens_out.is_zero()
    }
}

fn sum(a: U256, b: U256) -> U256 {
    a.checked_add(b).unwrap_or(U256::MAX)
}

#[derive(Clone)]
struct Held {
    storage: HashMap<U256, U256>,
    ether: U256,
    tokens: U256,
}

struct Entry<'a> {
    function: &'a Function,
    calldata: Vec<u8>,
    fixed: Vec<usize>,
}

#[derive(Clone)]
struct Call<'a> {
    function: &'a Function,
    who: U256,
    calldata: Vec<u8>,
    value: U256,
}

type Gain<'a> = (Vec<Call<'a>>, Ran, Moved);

struct Ran {
    inputs: Inputs,
    run: FrameRun,
}

struct Found<'a> {
    calls: Vec<Call<'a>>,
    last: Ran,
    net: Moved,
    first_paid: U256,
    surplus: U256,
    in_ether: bool,
}

fn selector(input: &[u8]) -> Option<u32> {
    let b = input.get(..4)?;
    Some(u32::from_be_bytes([b[0], b[1], b[2], b[3]]))
}

fn token_moves(p: &Ran) -> impl Iterator<Item = (U256, U256, U256)> + '_ {
    let this = p.inputs.address;
    p.run.calls.iter().filter_map(move |c| {
        if c.kind != op::CALL {
            return None;
        }
        match selector(&c.input) {
            Some(SEL_TRANSFER) if c.input.len() >= 68 => {
                Some((this, word(&c.input, 4), word(&c.input, 36)))
            }
            Some(SEL_TRANSFER_FROM) if c.input.len() >= 100 => {
                Some((word(&c.input, 4), word(&c.input, 36), word(&c.input, 68)))
            }
            _ => None,
        }
    })
}

fn moved(p: &Ran) -> Moved {
    let (who, this) = (p.inputs.caller, p.inputs.address);
    let paid = p
        .run
        .calls
        .iter()
        .filter(|c| c.kind == op::CALL && c.addr == who);
    let mut out = Moved {
        ether_in: p.inputs.callvalue,
        ether_out: paid.fold(U256::ZERO, |all, c| sum(all, c.value)),
        ..Moved::default()
    };
    for (from, to, amount) in token_moves(p) {
        if from == who && to == this {
            out.tokens_in = sum(out.tokens_in, amount);
        }
        if from == this && to == who {
            out.tokens_out = sum(out.tokens_out, amount);
        }
    }
    out
}

// The run engine answers every call with success. A payment the contract could not
// have covered would have failed on chain, so such a run is not counted.
fn settle(p: &Ran, held: &Held) -> Option<Held> {
    if !matches!(p.run.outcome, Outcome::Stop | Outcome::Return(_)) {
        return None;
    }
    let this = p.inputs.address;
    let had = sum(held.ether, p.inputs.callvalue);
    let sends = p.run.calls.iter().filter(|c| c.kind == op::CALL);
    let ether_out = sends.fold(U256::ZERO, |all, c| sum(all, c.value));
    let (mut tokens_in, mut tokens_out) = (U256::ZERO, U256::ZERO);
    for (from, to, amount) in token_moves(p) {
        if to == this && from != this {
            tokens_in = sum(tokens_in, amount);
        }
        if from == this && to != this {
            tokens_out = sum(tokens_out, amount);
        }
    }
    let tokens_had = sum(held.tokens, tokens_in);
    if ether_out > had || tokens_out > tokens_had {
        return None;
    }
    Some(Held {
        storage: p.run.storage.clone(),
        ether: had - ether_out,
        tokens: tokens_had - tokens_out,
    })
}

struct Pass<'a> {
    c: &'a Contract,
    explorers: Explorers,
    entries: Vec<Entry<'a>>,
}

impl<'a> Pass<'a> {
    fn new(c: &'a Contract) -> Pass<'a> {
        let reached = |f: &&Function| {
            matches!(
                f.kind,
                FnKind::External | FnKind::Fallback | FnKind::Receive
            )
        };
        let entry = |f: &'a Function| {
            let selector = exec::selector_of(f);
            let types: Vec<String> = f.params.iter().map(|p| p.ty.clone()).collect();
            let shaped = abi::layout(selector, &types);
            let (calldata, fixed) = match f.kind {
                FnKind::Receive => (Vec::new(), Vec::new()),
                FnKind::Fallback => {
                    let unused = Some(UNUSED_SELECTOR);
                    (path::inputs_for(unused, WORDS).calldata, Vec::new())
                }
                _ if shaped.fixed.is_empty() => {
                    (path::inputs_for(selector, WORDS).calldata, Vec::new())
                }
                _ => (shaped.calldata, shaped.fixed),
            };
            Entry {
                function: f,
                calldata,
                fixed,
            }
        };
        let functions = c.functions.iter().filter(reached).take(MAX_ENTRIES);
        Pass {
            c,
            explorers: Explorers::default(),
            entries: functions.map(entry).collect(),
        }
    }

    fn inputs(&self, call: &Call, held: &Held) -> Inputs {
        let one = U256::ONE.to_be_bytes().to_vec();
        let holds = held.tokens.to_be_bytes().to_vec();
        Inputs {
            calldata: call.calldata.clone(),
            caller: call.who,
            callvalue: call.value,
            storage: held.storage.clone(),
            balance: sum(held.ether, call.value),
            returned: one.clone(),
            spends_balance: true,
            replies: vec![
                (SEL_TRANSFER, one.clone()),
                (SEL_TRANSFER_FROM, one),
                (SEL_BALANCE_OF, holds),
            ],
            ..path::inputs_for(None, 0)
        }
    }

    fn step(&mut self, call: &Call, held: &Held) -> Option<(Ran, Held)> {
        let inputs = self.inputs(call, held);
        let code = self.c.code_of(call.function);
        let run = self.explorers.of(code).run_only(&inputs);
        let p = Ran { inputs, run };
        let next = settle(&p, held)?;
        Some((p, next))
    }

    fn explore(
        &mut self,
        index: usize,
        who: U256,
        value: Option<U256>,
        held: &Held,
        fill: impl Fn(usize) -> U256,
    ) -> Vec<Call<'a>> {
        if exec::spent() {
            return Vec::new();
        }
        let entry = &self.entries[index];
        let function = entry.function;
        let start = Call {
            function,
            who,
            calldata: path::fill_words(&entry.calldata, &entry.fixed, fill),
            value: value.unwrap_or(U256::from_u64(FIRST_VALUE)),
        };
        let free = Free {
            words: start.calldata.len() / 32,
            // The amount a function accepts is whatever its own checks ask for.
            value: value.is_none(),
            storage: false,
            fixed: entry.fixed.clone(),
        };
        let inputs = self.inputs(&start, held);
        let code = self.c.code_of(function);
        let found = self.explorers.of(code).explore(&inputs, &free, LIMITS);
        let ended = found.into_iter().filter(Path::succeeded);
        let calls = ended.map(|p| Call {
            function,
            who,
            calldata: p.inputs.calldata,
            value: p.inputs.callvalue,
        });
        calls.collect()
    }

    fn pay_ins(&mut self, start: &Held) -> Vec<Call<'a>> {
        let mut out = Vec::new();
        for index in 0..self.entries.len() {
            if out.len() >= MAX_PAY_INS {
                break;
            }
            let tried = self.explore(index, HOLDER, None, start, path::varied_word);
            let paying = tried.into_iter().find(|call| {
                let ran = self.step(call, start);
                ran.is_some_and(|(p, next)| {
                    moved(&p).pays_in_only() && next.storage != start.storage
                })
            });
            out.extend(paying);
        }
        out
    }

    fn search(&mut self, pay_in: &Call<'a>, start: &Held, factor: u64) -> Option<Found<'a>> {
        let (first, mut held) = self.step(pay_in, start)?;
        let paid = moved(&first);
        let in_ether = !paid.ether_in.is_zero();
        let first_paid = if in_ether {
            paid.ether_in
        } else {
            paid.tokens_in
        };
        let surplus = first_paid.wrapping_mul(U256::from_u64(factor));
        match in_ether {
            true => held.ether = sum(held.ether, surplus),
            false => held.tokens = sum(held.tokens, surplus),
        }
        let found = |(calls, last, net): Gain<'a>| Found {
            calls,
            last,
            net,
            first_paid,
            surplus,
            in_ether,
        };
        let opening = vec![pay_in.clone()];
        let repeated = self.repeats(pay_in, &held, opening.clone());
        let sized = || match in_ether {
            true => self.sizes(pay_in, &held, Moved::default(), opening, MAX_SIZED_CALLS),
            false => None,
        };
        repeated.or_else(sized).map(found)
    }

    // The same payment again and again, with one other call tried after each.
    fn repeats(
        &mut self,
        pay_in: &Call<'a>,
        from: &Held,
        mut calls: Vec<Call<'a>>,
    ) -> Option<Gain<'a>> {
        let mut held = from.clone();
        let mut net = Moved::default();
        let again = Call {
            who: OUTSIDER,
            ..pay_in.clone()
        };
        let senders: Vec<usize> = (0..self.entries.len())
            .filter(|i| self.entries[*i].function.effects.calls)
            .collect();
        for round in 0..MAX_REPEATS {
            if exec::spent() {
                return None;
            }
            let (p, next) = self.step(&again, &held)?;
            net = net.plus(moved(&p));
            held = next;
            calls.push(again.clone());
            if net.gains() {
                return Some((calls, p, net));
            }
            if !CLOSING_AFTER.contains(&round) {
                continue;
            }
            // An amount is asked for in the sizes that crossed the edge so far. What the
            // contract records is not read.
            let paid = sum(net.ether_in, net.tokens_in);
            let holds = sum(held.ether, held.tokens);
            let amounts = [U256::ZERO, paid, sum(paid, paid), holds];
            for index in &senders {
                let varied =
                    self.explore(*index, OUTSIDER, Some(U256::ZERO), &held, path::varied_word);
                let sized = amounts.iter().flat_map(|amount| {
                    self.explore(*index, OUTSIDER, Some(U256::ZERO), &held, |_| *amount)
                });
                let tried: Vec<Call<'a>> = sized.chain(varied).collect();
                for call in tried {
                    let Some((p, _)) = self.step(&call, &held) else {
                        continue;
                    };
                    let total = net.plus(moved(&p));
                    if total.gains() {
                        calls.push(call);
                        return Some((calls, p, total));
                    }
                }
            }
        }
        None
    }

    // A rule can accept a payment only at some sizes, or pay out only when a later
    // payment is smaller than an earlier one. So a few payments of different sizes are
    // tried, each a multiple of the smallest one the function accepts.
    fn sizes(
        &mut self,
        pay_in: &Call<'a>,
        held: &Held,
        net: Moved,
        calls: Vec<Call<'a>>,
        left: usize,
    ) -> Option<Gain<'a>> {
        for doublings in 0..SIZES {
            if exec::spent() {
                return None;
            }
            let call = Call {
                who: OUTSIDER,
                value: pay_in.value.wrapping_mul(U256::ONE << doublings),
                ..pay_in.clone()
            };
            let Some((p, next)) = self.step(&call, held) else {
                continue;
            };
            let total = net.plus(moved(&p));
            let mut made = calls.clone();
            made.push(call);
            if total.gains() {
                return Some((made, p, total));
            }
            if left > 1 {
                let deeper = self.sizes(pay_in, &next, total, made, left - 1);
                if deeper.is_some() {
                    return deeper;
                }
            }
        }
        None
    }

    fn gains_without_surplus(&mut self, calls: &[Call<'a>], start: &Held) -> bool {
        let mut held = start.clone();
        let mut net = Moved::default();
        for call in calls {
            let Some((p, next)) = self.step(call, &held) else {
                return false;
            };
            if call.who == OUTSIDER {
                net = net.plus(moved(&p));
            }
            held = next;
        }
        net.gains()
    }
}

fn report(out: &mut Vec<Finding>, found: &Found, from: &str, needs_surplus: bool) {
    let Some((last, earlier)) = found.calls.split_last() else {
        return;
    };
    let asset = if found.in_ether { "ether" } else { "a token" };
    let (paid, got) = match found.in_ether {
        true => (found.net.ether_in, found.net.ether_out),
        false => (found.net.tokens_in, found.net.tokens_out),
    };
    let own_calls = found.calls.iter().filter(|c| c.who == OUTSIDER).count();
    let opening = format!(
        "Starting from {from}, a first account pays in {} of {asset} through `{}`.",
        found.first_paid.to_hex(),
        earlier[0].function.name,
    );
    let outcome = format!(
        "A second account, with no role and nothing paid in before, then makes {own_calls} call(s), the last to `{}`. Every call ends normally and no payment is larger than what the contract holds. In all it pays in {} and is paid {}.",
        last.function.name,
        paid.to_hex(),
        got.to_hex(),
    );
    let (id, title, cause, advice) = match needs_surplus {
        true => (
            "surplus-open-to-any-account",
            "An account with no stake collects what the contract holds beyond its records",
            format!(
                " The contract is given {} more than its accounts paid in. The same calls without that surplus leave the second account with no gain, so what it gains is the surplus. Nothing ties that balance to the account that collects it.",
                found.surplus.to_hex(),
            ),
            "Pay an account only what is recorded for it, and decide who may collect a balance the records do not cover.",
        ),
        false => (
            "payment-taken-by-other-account",
            "An account takes out more than it paid in, from what another account paid",
            String::from(
                " The contract holds only what the two accounts paid in, so the gain comes out of the first account's payment.",
            ),
            "Bound what an account can take out by what is recorded for that account.",
        ),
    };
    push(
        out,
        id,
        title,
        Severity::High,
        Confidence::High,
        Some(last.function),
        None,
        format!("{opening} {outcome}{cause}"),
        Vec::new(),
        advice,
    );
    if let Some(finding) = out.last_mut() {
        let shown = |c: &Call| {
            let data = hex::encode(&c.calldata);
            format!(
                "{data} with value {} from {}",
                c.value.to_hex(),
                c.who.to_hex()
            )
        };
        finding.setup = earlier.iter().map(shown).collect();
        finding.confirmed = true;
        finding.witness = Some(hex::encode(&found.last.inputs.calldata));
        finding.observed = crate::evidence::observed(&found.last.inputs, &found.last.run);
    }
}

pub fn findings(c: &Contract, out: &mut Vec<Finding>) {
    if std::env::var("EVMDEC_NO_CONFIRM").is_ok() || c.info.runtime.is_empty() {
        return;
    }
    let start = Held {
        storage: deploy::storage(c),
        ether: U256::ZERO,
        tokens: U256::ZERO,
    };
    let from = deploy::start_text(&start.storage);
    let mut pass = Pass::new(c);
    let trace = crate::debug::on("EVMDEC_DEBUG_BOUNDARY");
    if trace {
        let names: Vec<&str> = pass
            .entries
            .iter()
            .map(|e| e.function.name.as_str())
            .collect();
        eprintln!("[boundary] entries {names:?}");
    }
    for pay_in in pass.pay_ins(&start) {
        if trace {
            let (name, value) = (&pay_in.function.name, pay_in.value.to_hex());
            eprintln!("[boundary] pay-in {name} value {value}");
        }
        let Some(found) = pass.search(&pay_in, &start, SURPLUS_FACTOR) else {
            continue;
        };
        let needs_surplus = !pass.gains_without_surplus(&found.calls, &start);
        report(out, &found, from, needs_surplus);
        return;
    }
}
