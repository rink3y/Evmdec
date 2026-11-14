use crate::abi::{self, SEL_BALANCE_OF, SEL_TRANSFER, SEL_TRANSFER_FROM};
use crate::analyze::{push, Confidence, Finding, Severity};
use crate::decompile::{Contract, Function};
use crate::deploy;
use crate::exec::{self, FrameRun};
use crate::function::FnKind;
use crate::hex;
use crate::interp::{self, CallRecord, Outcome};
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
// A reading is tried a thousand times higher and a thousand times lower. A price pushed
// for the length of one transaction moves by such factors, not by a few percent.
const SWING: u64 = 1_000;
// An answer of one is the smallest that reads as true. Some code only works with an
// amount at the scale tokens are counted in, so that scale is tried as well.
const UNIT_SCALES: [u64; 2] = [1, 1_000_000_000_000_000_000];
const MAX_READINGS: usize = 12;
const MAX_READ_WORDS: usize = 4;
const MAX_TAKES: usize = 4;
const LAST_BUILT_IN: u64 = 0x0a;

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
    unit: U256,
}

// One word of what an outside call answered.
#[derive(Clone)]
struct Reading {
    call: usize,
    word: usize,
    was: U256,
    to: U256,
    selector: Option<u32>,
    // The caller can move it: an asset's count of what another account holds follows any
    // transfer to that account, and a contract named in the call data is the caller's
    // choice.
    movable: bool,
}

struct Swung<'a> {
    calls: Vec<Call<'a>>,
    during: usize,
    reading: Reading,
    now: U256,
    last: Ran,
    net: Moved,
}

fn names(data: &[u8], who: U256) -> bool {
    let bytes = who.to_be_bytes();
    let short = bytes.iter().position(|b| *b != 0).unwrap_or(31);
    data.windows(32 - short).any(|w| w == &bytes[short..])
}

fn swings(was: U256) -> Vec<U256> {
    let by = U256::from_u64(SWING);
    let scaled = was.wrapping_mul(by);
    let fits = scaled.div_rem(by).0 == was && !scaled.is_zero();
    let up = if fits { scaled } else { by };
    let down = was.div_rem(by).0;
    [up, down].into_iter().filter(|v| *v != was).collect()
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
            unit: U256::ONE,
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
            returned: self.unit.to_be_bytes().to_vec(),
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
        self.step_with(call, held, None)
    }

    // The same call, with one word of one answer changed for this call only.
    fn step_with(
        &mut self,
        call: &Call,
        held: &Held,
        swung: Option<(&Reading, &[u8], U256)>,
    ) -> Option<(Ran, Held)> {
        let mut inputs = self.inputs(call, held);
        if let Some((reading, answer, now)) = swung {
            let mut data = answer.to_vec();
            let at = 32 * reading.word;
            data.get_mut(at..at + 32)?
                .copy_from_slice(&now.to_be_bytes());
            inputs.answers.push((reading.call, data));
        }
        let code = self.c.code_of(call.function);
        let run = self.explorers.of(code).run_only(&inputs);
        let p = Ran { inputs, run };
        let next = settle(&p, held)?;
        Some((p, next))
    }

    fn answered(&self, p: &Ran, call: &CallRecord) -> Vec<u8> {
        let inputs = &p.inputs;
        interp::answer(
            &inputs.signed,
            &inputs.replies,
            &inputs.returned,
            call.addr,
            &call.input,
        )
    }

    // What the contract learns from outside during a run. A transfer answers whether it
    // went through, which is not a quantity. A question that names this contract is about
    // what it holds itself, and that is counted here, not answered freely.
    fn readings(&self, p: &Ran) -> Vec<(Reading, Vec<u8>)> {
        let mut out = Vec::new();
        for (index, call) in p.run.calls.iter().enumerate() {
            let selector = selector(&call.input);
            let moves = matches!(selector, Some(SEL_TRANSFER | SEL_TRANSFER_FROM));
            let built_in = call.addr.fits_u64() && call.addr.low_u64() <= LAST_BUILT_IN;
            let own = names(&call.input, p.inputs.address);
            if moves || built_in || own || !call.value.is_zero() {
                continue;
            }
            let answer = self.answered(p, call);
            let chosen = !call.addr.is_zero() && names(&p.inputs.calldata, call.addr);
            let movable = selector == Some(SEL_BALANCE_OF) || chosen;
            for word_at in 0..(answer.len() / 32).min(MAX_READ_WORDS) {
                let reading = Reading {
                    call: index,
                    word: word_at,
                    was: word(&answer, 32 * word_at),
                    to: call.addr,
                    selector,
                    movable,
                };
                out.push((reading, answer.clone()));
            }
        }
        out.truncate(MAX_READINGS);
        out
    }

    // The calls by which the account gets something back, as found with nothing moved.
    fn takes(&mut self, held: &Held, paid: Moved) -> Vec<Call<'a>> {
        let amount = sum(paid.ether_in, paid.tokens_in);
        let senders: Vec<usize> = (0..self.entries.len())
            .filter(|i| self.entries[*i].function.effects.calls)
            .collect();
        let mut out: Vec<Call<'a>> = Vec::new();
        for index in senders {
            if out.len() >= MAX_TAKES || exec::spent() {
                break;
            }
            let mut tried = self.explore(index, OUTSIDER, Some(U256::ZERO), held, |_| amount);
            tried.extend(self.explore(index, OUTSIDER, Some(U256::ZERO), held, path::varied_word));
            let pays = tried.into_iter().find(|call| {
                self.step(call, held).is_some_and(|(p, _)| {
                    let got = moved(&p);
                    !got.ether_out.is_zero() || !got.tokens_out.is_zero()
                })
            });
            out.extend(pays);
        }
        out
    }

    // An account pays in and takes out. With every answer as first given it gets back no
    // more than it paid. One answered word is then different for the length of one of
    // its two calls and as first given for the other. If the account now ends with more
    // than it paid, a change that lasted one call left a gain that stays.
    fn swing(&mut self, pay_in: &Call<'a>, start: &Held) -> Option<Swung<'a>> {
        let trace = crate::debug::on("EVMDEC_DEBUG_BOUNDARY");
        let said = |what: String| {
            if trace {
                eprintln!("[swing] {}: {what}", pay_in.function.name);
            }
        };
        let (_, funded) = self.step(pay_in, start)?;
        let own = Call {
            who: OUTSIDER,
            ..pay_in.clone()
        };
        let Some((paying, after)) = self.step(&own, &funded) else {
            said("a second account cannot pay in the same way".into());
            return None;
        };
        let paid = moved(&paying);
        if !paid.pays_in_only() {
            said("the second pay-in also pays out".into());
            return None;
        }
        let takes = self.takes(&after, paid);
        said(format!(
            "{} ways to take out, {} readings while paying in",
            takes.len(),
            self.readings(&paying).len()
        ));
        let unmoved: Vec<(Call<'a>, Ran)> = takes
            .iter()
            .filter_map(|take| self.step(take, &after).map(|(p, _)| (take.clone(), p)))
            .collect();
        if unmoved.iter().any(|(_, p)| paid.plus(moved(p)).gains()) {
            return None;
        }
        let amount = sum(paid.ether_in, paid.tokens_in);
        for (reading, answer) in self.readings(&paying) {
            for now in swings(reading.was) {
                if exec::spent() {
                    return None;
                }
                let swung = Some((&reading, &answer[..], now));
                let Some((p, held)) = self.step_with(&own, &funded, swung) else {
                    continue;
                };
                let paid_now = moved(&p);
                for take in takes.iter().flat_map(|take| larger(take, amount)) {
                    let Some((last, _)) = self.step(&take, &held) else {
                        continue;
                    };
                    let net = paid_now.plus(moved(&last));
                    if net.gains() {
                        return Some(Swung {
                            calls: vec![pay_in.clone(), own, take],
                            during: 1,
                            reading,
                            now,
                            last,
                            net,
                        });
                    }
                }
            }
        }
        for (take, taken) in &unmoved {
            for (reading, answer) in self.readings(taken) {
                for now in swings(reading.was) {
                    if exec::spent() {
                        return None;
                    }
                    let swung = Some((&reading, &answer[..], now));
                    let Some((last, _)) = self.step_with(take, &after, swung) else {
                        continue;
                    };
                    let net = paid.plus(moved(&last));
                    if net.gains() {
                        return Some(Swung {
                            calls: vec![pay_in.clone(), own, take.clone()],
                            during: 2,
                            reading,
                            now,
                            last,
                            net,
                        });
                    }
                }
            }
        }
        None
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
            answers: true,
            settings: None,
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

// A pay-in made while a reading is moved can credit more than the same pay-in did before.
// The take-out found earlier asks for the earlier amount, so it is also tried for more.
fn larger<'a>(take: &Call<'a>, amount: U256) -> Vec<Call<'a>> {
    let mut out = vec![take.clone()];
    if amount.is_zero() {
        return out;
    }
    for factor in [2, SWING] {
        let more = amount.wrapping_mul(U256::from_u64(factor));
        let mut call = take.clone();
        let mut changed = false;
        for at in (4..call.calldata.len().saturating_sub(31)).step_by(32) {
            if word(&call.calldata, at) == amount {
                call.calldata[at..at + 32].copy_from_slice(&more.to_be_bytes());
                changed = true;
            }
        }
        if changed {
            out.push(call);
        }
    }
    out
}

fn report_swing(out: &mut Vec<Finding>, found: &Swung, from: &str) {
    let Some((last, earlier)) = found.calls.split_last() else {
        return;
    };
    let in_ether = !found.net.ether_in.is_zero();
    let asset = if in_ether { "ether" } else { "a token" };
    let (paid, got) = match in_ether {
        true => (found.net.ether_in, found.net.ether_out),
        false => (found.net.tokens_in, found.net.tokens_out),
    };
    let reading = &found.reading;
    let during = &found.calls[found.during].function.name;
    let asked = reading.selector.map_or(String::from("no selector"), |s| {
        format!("selector {s:#010x}")
    });
    let (severity, how) = match reading.movable {
        true => (
            Severity::High,
            "The caller can move that answer: it is either what an asset reports another account holds, which follows any transfer to that account, or the answer of a contract the call data names.",
        ),
        false => (
            Severity::Medium,
            "Whether that answer can be moved within one transaction depends on the contract that gives it, which was not read. If it can, this is how the gain is taken.",
        ),
    };
    push(
        out,
        "one-call-reading-leaves-a-gain",
        "A reading that differs for one call leaves the caller with a gain that stays",
        severity,
        Confidence::High,
        Some(last.function),
        None,
        format!(
            "Starting from {from}, a first account pays in through `{}`. A second account, with no role, pays in the same way and takes out through `{}`. With every outside answer as first given it gets back no more than it paid. When word {} of the answer to call {} made during `{during}` (to {}, {asked}) is {} instead of {} for that one call, and as first given for every other call, the same two calls leave it with {} of {asset} against {} paid. No payment is larger than what the contract holds, so the difference comes out of what the first account paid in. {how}",
            earlier[0].function.name,
            last.function.name,
            reading.word,
            reading.call,
            reading.to.to_hex(),
            found.now.to_hex(),
            reading.was.to_hex(),
            got.to_hex(),
            paid.to_hex(),
        ),
        Vec::new(),
        "Do not let an amount that is credited or paid follow a quantity read at the moment of the call. Use the contract's own records, or a value that one transaction cannot move, and bound what an account takes out by what is recorded for it.",
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

pub fn swing_findings(c: &Contract, out: &mut Vec<Finding>) {
    if std::env::var("EVMDEC_NO_CONFIRM").is_ok() || c.info.runtime.is_empty() {
        return;
    }
    let start = Held {
        storage: deploy::start(c),
        ether: U256::ZERO,
        tokens: U256::ZERO,
    };
    let from = deploy::started_from(c);
    let mut pass = Pass::new(c);
    for unit in UNIT_SCALES {
        pass.unit = U256::from_u64(unit);
        let pay_ins = pass.pay_ins(&start);
        if crate::debug::on("EVMDEC_DEBUG_BOUNDARY") {
            eprintln!("[swing] answers of {unit}: {} pay-ins", pay_ins.len());
        }
        for pay_in in pay_ins {
            if exec::spent() {
                return;
            }
            if let Some(found) = pass.swing(&pay_in, &start) {
                report_swing(out, &found, from);
                return;
            }
        }
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
        storage: deploy::start(c),
        ether: U256::ZERO,
        tokens: U256::ZERO,
    };
    let from = deploy::started_from(c);
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
