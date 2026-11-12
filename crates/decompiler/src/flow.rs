use crate::abi;
use crate::analyze::{display_name, push, Confidence, Finding, Severity};
use crate::cross::World;
use crate::decompile::{Contract, Function};
use crate::deploy;
use crate::emit::MappingLayout;
use crate::exec;
use crate::function::FnKind;
use crate::hex;
use crate::interp::CallRecord;
use crate::opcode as op;
use crate::path::{self, Explorer, Limits, Path};
use crate::solve::{self, word, Free, Inputs, Step};
use crate::ssa;
use crate::u256::U256;
use std::collections::HashMap;
use std::time::{Duration, Instant};

const SEL_TRANSFER: u32 = 0xa905_9cbb;
const SEL_TRANSFER_FROM: u32 = 0x23b8_72dd;

const LIMITS: Limits = Limits {
    paths: 12,
    runs: 48,
    until: None,
};
const PROBE: Limits = Limits {
    paths: 6,
    runs: 16,
    until: None,
};
const WORDS: usize = 8;
const MAX_FUNCTIONS: usize = 32;
const MAX_DEPOSITS: usize = 6;
const BUDGET: Duration = Duration::from_secs(4);

const SECOND_CALLER: U256 = U256::from_u64(0xbbbb_bbbb_bbbb_bbbb);
// About twice the amounts the second account pays in.
// Raising the balance by that much costs about as much as the payment it is tested against.
const RAISED_BALANCE: u64 = 0x4000;
// A payment that passes on no more gas than this cannot make a call from the receiver.
const STIPEND: u64 = 2_300;

type Fill = fn(usize) -> U256;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Asset {
    Ether,
    Token(U256),
}

fn selector(input: &[u8]) -> Option<u32> {
    let b = input.get(..4)?;
    Some(u32::from_be_bytes([b[0], b[1], b[2], b[3]]))
}

fn taken(p: &Path) -> Vec<(Asset, U256)> {
    let mut out = Vec::new();
    if !p.inputs.callvalue.is_zero() {
        out.push((Asset::Ether, p.inputs.callvalue));
    }
    for call in &p.run.calls {
        let pulls = call.kind == op::CALL
            && selector(&call.input) == Some(SEL_TRANSFER_FROM)
            && call.input.len() >= 100
            && word(&call.input, 4) == p.inputs.caller
            && word(&call.input, 36) == p.inputs.address;
        if pulls {
            out.push((Asset::Token(call.addr), word(&call.input, 68)));
        }
    }
    out
}

fn sent(p: &Path) -> Vec<(Asset, U256)> {
    let mut out = Vec::new();
    for call in p.run.calls.iter().filter(|c| c.kind == op::CALL) {
        if call.addr == p.inputs.caller && !call.value.is_zero() {
            out.push((Asset::Ether, call.value));
        }
        let pays = selector(&call.input) == Some(SEL_TRANSFER)
            && call.input.len() >= 68
            && word(&call.input, 4) == p.inputs.caller;
        if pays {
            out.push((Asset::Token(call.addr), word(&call.input, 36)));
        }
    }
    out
}

fn sum(a: U256, b: U256) -> U256 {
    let out = a.wrapping_add(b);
    if out < a {
        U256::MAX
    } else {
        out
    }
}

fn total(moves: &[(Asset, U256)], asset: Asset) -> U256 {
    let same = moves.iter().filter(|(a, _)| *a == asset);
    same.fold(U256::ZERO, |all, (_, amount)| sum(all, *amount))
}

fn credited(p: &Path, layout: MappingLayout) -> Option<U256> {
    let steps = solve::steps(&p.effects, &p.inputs);
    let mut best = None;
    for step in &steps {
        let Step::Write {
            key, before, after, ..
        } = step
        else {
            continue;
        };
        let Some(slot) = ssa::slot_path(*key, layout) else {
            continue;
        };
        let keyed = slot.steps.iter().any(|s| match s {
            ssa::Step::Key(k) => solve::value_of(*k, &p.inputs) == Some(p.inputs.caller),
            _ => false,
        });
        if keyed && after > before {
            best = best.max(Some(*after - *before));
        }
    }
    best
}

fn entry_moves(p: &Path, layout: MappingLayout) -> (U256, U256) {
    let mut ends: HashMap<U256, (U256, U256)> = HashMap::new();
    for step in solve::steps(&p.effects, &p.inputs) {
        let Step::Write {
            key,
            slot,
            before,
            after,
        } = step
        else {
            continue;
        };
        let keyed = ssa::slot_path(key, layout).is_some_and(|path| {
            path.steps.iter().any(|s| match s {
                ssa::Step::Key(k) => solve::value_of(*k, &p.inputs) == Some(p.inputs.caller),
                _ => false,
            })
        });
        if keyed {
            ends.entry(slot).or_insert((before, after)).1 = after;
        }
    }
    let (mut rise, mut fall) = (U256::ZERO, U256::ZERO);
    for (before, after) in ends.into_values() {
        if after > before {
            rise = sum(rise, after - before);
        } else {
            fall = sum(fall, before - after);
        }
    }
    (rise, fall)
}

fn all_sent(p: &Path) -> U256 {
    let moved = sent(p).into_iter();
    moved.fold(U256::ZERO, |all, (_, amount)| sum(all, amount))
}

fn all_taken(p: &Path) -> U256 {
    let moved = taken(p).into_iter();
    moved.fold(U256::ZERO, |all, (_, amount)| sum(all, amount))
}

// Small amounts, so a proportion that divides shows its rounding in every one.
const PARTS: [(u64, u64); 4] = [(3, 3), (5, 6), (7, 9), (10, 13)];
const MAX_AMOUNT_WORDS: usize = 4;

fn word_reply(value: U256) -> Vec<u8> {
    value.to_be_bytes().to_vec()
}

fn filled(calldata: &[u8], fixed: &[usize], value: impl Fn(usize) -> U256) -> Vec<u8> {
    let mut out = calldata.to_vec();
    for index in (0..calldata.len().saturating_sub(4) / 32).filter(|i| !fixed.contains(i)) {
        let at = 4 + 32 * index;
        out[at..at + 32].copy_from_slice(&value(index).to_be_bytes());
    }
    out
}

struct Deposit<'a> {
    function: &'a Function,
    path: Path,
    taken: Vec<(Asset, U256)>,
    credit: U256,
    unit: bool,
}

struct Pass<'a> {
    c: &'a Contract,
    explorers: HashMap<*const u8, Explorer>,
    start: HashMap<U256, U256>,
    deadline: Instant,
}

impl<'a> Pass<'a> {
    fn externals(&self) -> impl Iterator<Item = &'a Function> {
        let external = |f: &&Function| f.kind == FnKind::External;
        self.c.functions.iter().filter(external).take(MAX_FUNCTIONS)
    }

    fn explore(&mut self, f: &Function, start: &Inputs, free: &Free, limits: Limits) -> Vec<Path> {
        if Instant::now() >= self.deadline {
            return Vec::new();
        }
        let code = self.c.code_of(f);
        let explorer = self
            .explorers
            .entry(code.as_ptr())
            .or_insert_with(|| Explorer::new(code));
        let limits = Limits {
            until: Some(self.deadline),
            ..limits
        };
        explorer.explore(start, free, limits)
    }

    fn base(&self, f: &Function, words: impl Fn(usize) -> U256) -> (Inputs, Free) {
        let selector = exec::selector_of(f);
        let types: Vec<String> = f.params.iter().map(|p| p.ty.clone()).collect();
        let shaped = abi::layout(selector, &types);
        let flat = path::inputs_for(selector, WORDS);
        let dynamic = !shaped.fixed.is_empty();
        let (calldata, fixed) = if dynamic {
            (shaped.calldata, shaped.fixed)
        } else {
            (flat.calldata.clone(), Vec::new())
        };
        let one = word_reply(U256::ONE);
        let inputs = Inputs {
            calldata: filled(&calldata, &fixed, words),
            returned: one.clone(),
            replies: vec![(SEL_TRANSFER, one.clone()), (SEL_TRANSFER_FROM, one)],
            storage: self.start.clone(),
            ..flat
        };
        let free = Free {
            words: inputs.calldata.len() / 32,
            value: false,
            storage: false,
            fixed,
        };
        (inputs, free)
    }

    fn deposits(&mut self, layout: MappingLayout) -> Vec<Deposit<'a>> {
        let mut out: Vec<Deposit<'a>> = Vec::new();
        for f in self.externals() {
            // One check needs a single unit paid in. The others need room to pay out in parts.
            let sizes: [(u64, Fill); 2] = [
                (1, |_| U256::ONE),
                (0x1001, |i| U256::from_u64(0x1001 + 2 * i as u64)),
            ];
            for (value, words) in sizes {
                let (mut start, free) = self.base(f, words);
                start.callvalue = U256::from_u64(value);
                start.balance = start.callvalue;
                let found = self.explore(f, &start, &free, LIMITS);
                let paid = found.into_iter().find_map(|path| {
                    let taken = taken(&path);
                    let credit = credited(&path, layout)?;
                    let pays = path.succeeded() && !taken.is_empty() && sent(&path).is_empty();
                    pays.then_some((path, taken, credit))
                });
                if let Some((path, taken, credit)) = paid {
                    out.push(Deposit {
                        function: f,
                        path,
                        taken,
                        credit,
                        unit: value == 1,
                    });
                }
            }
            if out.len() >= MAX_DEPOSITS {
                break;
            }
        }
        out
    }

    fn after(&mut self, d: &Deposit, g: &Function) -> Vec<Path> {
        let state = d.path.run.storage.clone();
        let credit = d.credit;
        let fills: [&dyn Fn(usize) -> U256; 3] = [&|_| credit, &|_| U256::ZERO, &|_| U256::MAX];
        let mut out = Vec::new();
        for (round, fill) in fills.iter().enumerate() {
            let (mut start, free) = self.base(g, fill);
            start.storage = state.clone();
            let limits = if round == 0 { PROBE } else { LIMITS };
            let found = self.explore(g, &start, &free, limits);
            if round == 0 && found.iter().all(|p| p.run.calls.is_empty()) {
                break;
            }
            out.extend(found.into_iter().filter(Path::succeeded));
        }
        out
    }

    fn gain(&mut self, d: &Deposit, g: &Function, paths: &[Path], out: &mut Vec<Finding>) -> bool {
        let better = paths.iter().find_map(|q| {
            let back = sent(q);
            let more = back.iter().find(|(asset, _)| {
                let paid = sum(total(&d.taken, *asset), total(&taken(q), *asset));
                total(&back, *asset) > paid
            })?;
            Some((more.0, total(&back, more.0), q))
        });
        let Some((asset, back, q)) = better else {
            return false;
        };
        if self.pays_from_nothing(g, q, asset, back) {
            return false;
        }
        report_gain(out, d, g, q, asset, back, deploy::start_text(&self.start));
        true
    }

    fn reenter(&mut self, d: &Deposit, g: &Function, paths: &[Path], out: &mut Vec<Finding>) {
        let pays_caller = |q: &&Path| {
            q.run.calls.iter().any(|c| {
                let to_caller = c.kind == op::CALL && c.addr == q.inputs.caller;
                to_caller && !c.value.is_zero() && c.gas > U256::from_u64(STIPEND)
            })
        };
        let Some(q) = paths.iter().find(pays_caller) else {
            return;
        };
        let once = total(&sent(q), Asset::Ether);
        let mut world = World::new();
        world.place(q.inputs.address, self.c.code_of(g).to_vec());
        for (slot, value) in &q.inputs.storage {
            world.seed(q.inputs.address, *slot, *value);
        }
        world.place(q.inputs.caller, calls_back(&q.inputs.calldata));
        let ended = world.run(
            q.inputs.address,
            q.inputs.caller,
            q.inputs.callvalue,
            q.inputs.calldata.clone(),
        );
        let paid_out = world
            .sent()
            .iter()
            .filter(|s| s.from == q.inputs.address && s.to == q.inputs.caller)
            .fold(U256::ZERO, |all, s| sum(all, s.value));
        if !ended || paid_out <= once {
            return;
        }
        let note = format!(
            " Confirmed by running it: after the attached earlier call, the attached call is made by an account whose code makes the same call again when it is paid. The run ends normally and the account is sent {} in all, where one call alone sends {}. The run assumes the contract holds enough to pay.",
            paid_out.to_hex(),
            once.to_hex(),
        );
        let setup = vec![hex::encode(&d.path.inputs.calldata)];
        let known = out.iter_mut().find(|f| {
            f.id.starts_with("reentrancy")
                && f.function.as_deref() == Some(display_name(g).as_str())
        });
        if let Some(f) = known {
            f.description.push_str(&note);
            f.confidence = Confidence::High;
            f.setup = setup;
            f.confirm(q);
            return;
        }
        push(
            out,
            "reentered-call-pays-again",
            "A call made again from inside its own payment is paid twice",
            Severity::High,
            Confidence::High,
            Some(g),
            None,
            format!(
                "`{}` pays its caller before it has finished recording the payment.{note}",
                g.name
            ),
            Vec::new(),
            "Finish every storage update before the payment, or hold a lock across it.",
        );
        if let Some(f) = out.last_mut() {
            f.setup = setup;
            f.confirm(q);
        }
    }

    fn run(&mut self, f: &Function, inputs: &Inputs) -> Path {
        let code = self.c.code_of(f);
        let explorer = self
            .explorers
            .entry(code.as_ptr())
            .or_insert_with(|| Explorer::new(code));
        explorer.run(inputs)
    }

    fn answers(&mut self, out: &mut Vec<Finding>) {
        let mut unanswered: Vec<String> = Vec::new();
        let mut first_unanswered = None;
        let functions: Vec<&Function> = self.externals().collect();
        for f in functions {
            let (start, free) = self.base(f, |i| U256::from_u64(0x1001 + 2 * i as u64));
            let found = self.explore(f, &start, &free, LIMITS);
            let asks = |p: &&Path| {
                let transfer = |c: &CallRecord| {
                    let s = selector(&c.input);
                    c.kind == op::CALL && (s == Some(SEL_TRANSFER) || s == Some(SEL_TRANSFER_FROM))
                };
                p.succeeded() && p.run.calls.iter().any(transfer)
            };
            let Some(p) = found.iter().find(asks) else {
                continue;
            };
            let with = |reply: Vec<u8>| Inputs {
                replies: vec![(SEL_TRANSFER, reply.clone()), (SEL_TRANSFER_FROM, reply)],
                ..p.inputs.clone()
            };
            let refused = self.run(f, &with(word_reply(U256::ZERO)));
            if refused.succeeded() && refused.run.storage != refused.inputs.storage {
                report_refused(out, f, &refused);
                continue;
            }
            let silent = self.run(f, &with(Vec::new()));
            if !silent.succeeded() {
                unanswered.push(format!("`{}`", f.name));
                first_unanswered.get_or_insert((f, silent));
            }
        }
        let Some((f, silent)) = first_unanswered else {
            return;
        };
        push(
            out,
            "transfer-without-answer-refused",
            "A transfer that returns no value makes these functions fail",
            Severity::Low,
            Confidence::High,
            Some(f),
            None,
            format!(
                "{} end normally when the asset they move answers a transfer with a true word, and fail when the same transfer succeeds and returns nothing. Some widely used assets return nothing, and these functions cannot be used with them.",
                unanswered.join(", "),
            ),
            Vec::new(),
            "Accept an empty answer as success and check a non-empty one, as the common safe-transfer wrappers do.",
        );
        if let Some(last) = out.last_mut() {
            last.sites = unanswered.len();
            last.confirm(&silent);
        }
    }

    fn moved_by_answer(&mut self, out: &mut [Finding]) {
        const MOVED: [&str; 2] = ["no-slippage-bound", "spot-balance-price"];
        let functions: Vec<&Function> = self.externals().collect();
        for finding in out.iter_mut() {
            if finding.confirmed || !MOVED.contains(&finding.id.as_str()) {
                continue;
            }
            let named = |f: &&&Function| Some(display_name(f)) == finding.function;
            let Some(f) = functions.iter().find(named) else {
                continue;
            };
            let (mut start, free) = self.base(f, |i| U256::from_u64(0x1001 + 2 * i as u64));
            let read = U256::from_u64(0x10_0000);
            (start.returned, start.balance) = (word_reply(read), read);
            let found = self.explore(f, &start, &free, LIMITS);
            let paid = |p: &Path| total(&sent(p), Asset::Ether).max(token_out(p));
            let Some(p) = found.iter().find(|p| p.succeeded() && !paid(p).is_zero()) else {
                continue;
            };
            let mut moved = p.inputs.clone();
            (moved.returned, moved.balance) = (word_reply(read >> 1), read >> 1);
            let q = self.run(f, &moved);
            if !q.succeeded() || paid(&q) == paid(p) {
                continue;
            }
            finding.description.push_str(&format!(
                " Confirmed by running it: the attached call ends normally and pays out {} when the value it reads from outside is {}, and pays out {} when that value is halved. Nothing in the call made the second run fail.",
                paid(p).to_hex(),
                read.to_hex(),
                paid(&q).to_hex(),
            ));
            finding.confidence = Confidence::High;
            finding.confirm(p);
        }
    }

    // What a call hands the caller should round down, and what it takes should round up.
    // For a rule that rounds down, two parts never come to more than the whole.
    // Every amount is tried from one and the same state, so only the rounding differs.
    fn rounding(
        &mut self,
        d: &Deposit,
        g: &Function,
        paths: &[Path],
        layout: MappingLayout,
        out: &mut Vec<Finding>,
    ) {
        let Some(base) = paths.first() else { return };
        let skew = sum(d.credit.wrapping_mul(U256::from_u64(3)), U256::ONE);
        let words = (base.inputs.calldata.len().saturating_sub(4) / 32).min(MAX_AMOUNT_WORDS);
        for index in 0..words {
            let mut measure = |amount: u64| {
                let mut inputs = base.inputs.clone();
                let at = 4 + 32 * index;
                inputs.calldata[at..at + 32].copy_from_slice(&U256::from_u64(amount).to_be_bytes());
                (inputs.balance, inputs.returned) = (skew, word_reply(skew));
                let run = self.run(g, &inputs);
                let (rise, fall) = entry_moves(&run, layout);
                let gets = sum(rise, all_sent(&run));
                let gives = sum(fall, all_taken(&run));
                run.succeeded().then_some((gets, gives, run))
            };
            let (mut over, mut under, mut shown) = (0, 0, None);
            for (a, b) in PARTS {
                let (Some(x), Some(y), Some(whole)) = (measure(a), measure(b), measure(a + b))
                else {
                    continue;
                };
                // One side of the exchange has to follow the amount exactly.
                // A call the word does not steer gives the same twice and proves nothing.
                let exact =
                    |part: U256, other: U256, all: U256| !all.is_zero() && sum(part, other) == all;
                let more_in_parts = sum(x.0, y.0) > whole.0 && exact(x.1, y.1, whole.1);
                let less_in_parts = sum(x.1, y.1) < whole.1 && exact(x.0, y.0, whole.0);
                over += usize::from(more_in_parts);
                under += usize::from(less_in_parts);
                if more_in_parts || less_in_parts {
                    shown.get_or_insert((a, b, x, y, whole));
                }
            }
            let Some((a, b, x, y, whole)) = shown.filter(|_| over >= 2 || under >= 2) else {
                continue;
            };
            let (what, parts, one) = if over >= 2 {
                ("hands the caller", sum(x.0, y.0), whole.0)
            } else {
                ("takes from the caller", sum(x.1, y.1), whole.1)
            };
            push(
                out,
                "rounding-favours-caller",
                "A division rounds in the caller's favour",
                Severity::Medium,
                Confidence::High,
                Some(g),
                None,
                format!(
                    "`{}` was run from one state with argument word {index} set to {a}, to {b} and to {}. What it {what} came to {} for the two parts together and {} for the whole. What a call hands out should round down and what it takes should round up, and then parts never beat the whole. Here they do, so the division rounds toward the caller and asking in small parts gains the difference each time. The state follows the attached earlier call, with the balance the contract reads set to {}.",
                    g.name,
                    a + b,
                    parts.to_hex(),
                    one.to_hex(),
                    skew.to_hex(),
                ),
                Vec::new(),
                "Round what the contract hands out down and what it takes up.",
            );
            if let Some(last) = out.last_mut() {
                last.setup = vec![hex::encode(&d.path.inputs.calldata)];
                last.confirm(&whole.2);
            }
            return;
        }
    }

    // A function that pays the same from empty storage is not a round trip.
    // Other rules cover a payment nothing was put in for.
    fn pays_from_nothing(&mut self, g: &Function, q: &Path, asset: Asset, back: U256) -> bool {
        let mut alone = q.inputs.clone();
        alone.storage = self.start.clone();
        let code = self.c.code_of(g);
        let explorer = self
            .explorers
            .entry(code.as_ptr())
            .or_insert_with(|| Explorer::new(code));
        let again = explorer.run(&alone);
        again.succeeded() && total(&sent(&again), asset) >= back
    }

    fn uncredited(&mut self, d: &Deposit, layout: MappingLayout, out: &mut Vec<Finding>) {
        let one_unit = d.taken.iter().all(|(_, amount)| *amount == U256::ONE);
        if !one_unit {
            return;
        }
        let f = d.function;
        let (mut start, free) = self.base(f, |i| U256::from_u64(0x1001 + 2 * i as u64));
        start.storage = d.path.run.storage.clone();
        start.caller = SECOND_CALLER;
        start.callvalue = match d.taken[0].0 {
            Asset::Ether => U256::from_u64(0x1001),
            Asset::Token(_) => U256::ZERO,
        };
        let raised = U256::from_u64(RAISED_BALANCE);
        start.returned = word_reply(raised);
        start.balance = raised;
        let found = self.explore(f, &start, &free, LIMITS);
        let lost = found.into_iter().find(|q| {
            let paid = taken(q);
            let real = paid.iter().any(|(_, amount)| *amount > U256::ONE);
            q.succeeded() && real && credited(q, layout).is_none()
        });
        let Some(q) = lost else { return };
        // With the balance left where the first payment put it the same call must be credited.
        // Otherwise the function simply records nothing for anyone.
        let mut honest = q.inputs.clone();
        honest.returned = word_reply(U256::ONE);
        honest.balance = U256::ONE;
        let code = self.c.code_of(f);
        let explorer = self
            .explorers
            .entry(code.as_ptr())
            .or_insert_with(|| Explorer::new(code));
        let plain = explorer.run(&honest);
        if !plain.succeeded() || credited(&plain, layout).is_none() {
            return;
        }
        push(
            out,
            "inflow-credits-nothing",
            "A payment is taken and nothing is credited once the read balance is raised",
            Severity::High,
            Confidence::High,
            Some(f),
            None,
            format!(
                "`{}` credits the payer in proportion to a balance it reads at the time of the call. After one earlier payment of a single unit, and with that balance raised from outside to {}, the attached call by a second account pays in more than a thousand units, ends normally and credits that account nothing. With the balance left alone the same call is credited. The function has no lower bound on the credit and no offset in the proportion that would keep it above zero.",
                f.name,
                raised.to_hex(),
            ),
            Vec::new(),
            "Require a non-zero credit, or add a fixed offset to both sides of the proportion, or track the balance in storage instead of reading it from the asset.",
        );
        if let Some(last) = out.last_mut() {
            last.setup = vec![hex::encode(&d.path.inputs.calldata)];
            last.confirm(&q);
        }
    }
}

fn calls_back(data: &[u8]) -> Vec<u8> {
    const HEAD: u16 = 37;
    const PUSH2: u8 = op::PUSH1 + 1;
    let len = (data.len() as u16).to_be_bytes();
    let off = HEAD.to_be_bytes();
    let mut code = vec![op::PUSH1, 0x00, op::SLOAD, op::PUSH1, 35, op::JUMPI];
    code.extend([op::PUSH1, 0x01, op::PUSH1, 0x00, op::SSTORE]);
    code.extend([PUSH2, len[0], len[1], PUSH2, off[0], off[1]]);
    code.extend([op::PUSH1, 0x00, op::CODECOPY]);
    code.extend([op::PUSH1, 0x00, op::PUSH1, 0x00, PUSH2, len[0], len[1]]);
    code.extend([
        op::PUSH1,
        0x00,
        op::PUSH1,
        0x00,
        op::CALLER,
        op::GAS,
        op::CALL,
        op::POP,
    ]);
    code.extend([op::JUMPDEST, op::STOP]);
    debug_assert_eq!(code.len(), usize::from(HEAD));
    code.extend_from_slice(data);
    code
}

fn token_out(p: &Path) -> U256 {
    let amounts = sent(p).into_iter().filter(|(a, _)| *a != Asset::Ether);
    amounts.fold(U256::ZERO, |all, (_, amount)| sum(all, amount))
}

fn report_refused(out: &mut Vec<Finding>, f: &Function, run: &Path) {
    const KNOWN: [&str; 2] = ["erc20-return-ignored", "unchecked-token-pull"];
    let note = " Confirmed by running it: with the attached input the transfer answers false, as an asset does when it refuses, and the function still ends normally and keeps its storage changes.";
    let name = display_name(f);
    let known = out
        .iter_mut()
        .find(|x| KNOWN.contains(&x.id.as_str()) && x.function.as_deref() == Some(name.as_str()));
    if let Some(x) = known {
        x.description.push_str(note);
        x.confidence = Confidence::High;
        x.confirm(run);
        return;
    }
    push(
        out,
        "refused-transfer-treated-as-done",
        "A transfer that answers false is treated as done",
        Severity::High,
        Confidence::High,
        Some(f),
        None,
        format!("`{}` moves an asset and records the result.{note}", f.name),
        Vec::new(),
        "Require the transfer's answer to be true, or empty for assets that return nothing.",
    );
    if let Some(x) = out.last_mut() {
        x.confirm(run);
    }
}

fn asset_text(asset: Asset) -> String {
    match asset {
        Asset::Ether => "ether".to_string(),
        Asset::Token(at) => format!("the asset at {}", at.to_hex()),
    }
}

fn report_gain(
    out: &mut Vec<Finding>,
    d: &Deposit,
    g: &Function,
    q: &Path,
    asset: Asset,
    back: U256,
    from: &str,
) {
    let paid = sum(total(&d.taken, asset), total(&taken(q), asset));
    push(
        out,
        "two-calls-return-more",
        "Two calls by one account return more than they took",
        Severity::High,
        Confidence::High,
        Some(g),
        None,
        format!(
            "Starting from {}, an account holding no role calls `{}` and pays in {} of {}. Its next call, to `{}`, ends normally and sends it {} of the same asset. The same second call made first sends nothing, so what comes back is decided by what the first call recorded, and it is more than was paid. The run assumes the contract holds enough to make the payment.",
            from,
            d.function.name,
            paid.to_hex(),
            asset_text(asset),
            g.name,
            back.to_hex(),
        ),
        Vec::new(),
        "Make what a call pays out no larger than what the same account paid in, after rounding in the contract's favour.",
    );
    if let Some(last) = out.last_mut() {
        last.setup = vec![hex::encode(&d.path.inputs.calldata)];
        last.confirm(q);
    }
}

pub fn findings(c: &Contract, out: &mut Vec<Finding>) {
    if std::env::var("EVMDEC_NO_CONFIRM").is_ok() || c.info.runtime.is_empty() {
        return;
    }
    let layout = c.compiler.layout;
    let mut pass = Pass {
        c,
        explorers: HashMap::new(),
        start: deploy::storage(c),
        deadline: Instant::now() + BUDGET,
    };
    let deposits = pass.deposits(layout);
    for d in &deposits {
        pass.uncredited(d, layout, out);
        let larger = |o: &Deposit| o.function.pc == d.function.pc && !o.unit;
        if d.unit && deposits.iter().any(larger) {
            continue;
        }
        let functions: Vec<&Function> = pass.externals().collect();
        let mut gained = false;
        for g in functions {
            let paths = pass.after(d, g);
            gained = gained || pass.gain(d, g, &paths, out);
            pass.reenter(d, g, &paths, out);
            pass.rounding(d, g, &paths, layout, out);
        }
    }
    pass.answers(out);
    pass.moved_by_answer(out);
}
