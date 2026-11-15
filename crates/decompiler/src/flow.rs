use crate::abi::{self, SEL_BALANCE_OF, SEL_OWNER_OF, SEL_TRANSFER, SEL_TRANSFER_FROM};
use crate::analyze::{display_name, push, Confidence, Finding, Severity};
use crate::decompile::{Contract, Function};
use crate::deploy;
use crate::emit::MappingLayout;
use crate::exec;
use crate::function::FnKind;
use crate::interp::CallRecord;
use crate::opcode as op;
use crate::path::{self, Explorers, Limits, Path};
use crate::solve::{self, word, Free, Inputs, Step};
use crate::ssa;
use crate::u256::U256;
use std::collections::HashMap;

const LIMITS: Limits = Limits {
    paths: 12,
    runs: 48,
};
const WORDS: usize = 8;
const MAX_FUNCTIONS: usize = 32;
pub const WORK: u64 = 4 * exec::WORK_PER_SECOND;

// A payment that passes on no more gas than this cannot make a call from the receiver.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Asset {
    Ether,
    Token(U256),
}

fn taken(p: &Path) -> Vec<(Asset, U256)> {
    let mut out = Vec::new();
    if !p.inputs.callvalue.is_zero() {
        out.push((Asset::Ether, p.inputs.callvalue));
    }
    for call in &p.run.calls {
        let pulls = call.kind == op::CALL
            && abi::selector(&call.input) == Some(SEL_TRANSFER_FROM)
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
        let pays = abi::selector(&call.input) == Some(SEL_TRANSFER)
            && call.input.len() >= 68
            && word(&call.input, 4) == p.inputs.caller;
        if pays {
            out.push((Asset::Token(call.addr), word(&call.input, 36)));
        }
    }
    out
}

fn sum(a: U256, b: U256) -> U256 {
    a.checked_add(b).unwrap_or(U256::MAX)
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

fn all_taken(p: &Path) -> U256 {
    let moved = taken(p).into_iter();
    moved.fold(U256::ZERO, |all, (_, amount)| sum(all, amount))
}

fn word_reply(value: U256) -> Vec<u8> {
    value.to_be_bytes().to_vec()
}

struct Pass<'a> {
    c: &'a Contract,
    explorers: Explorers,
    start: HashMap<U256, U256>,
}

impl<'a> Pass<'a> {
    fn externals(&self) -> impl Iterator<Item = &'a Function> {
        let external = |f: &&Function| f.kind == FnKind::External;
        self.c.functions.iter().filter(external).take(MAX_FUNCTIONS)
    }

    fn explore(&mut self, f: &Function, start: &Inputs, free: &Free, limits: Limits) -> Vec<Path> {
        if exec::spent() {
            return Vec::new();
        }
        let code = self.c.code_of(f);
        let explorer = self.explorers.of(code);
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
            calldata: path::fill_words(&calldata, &fixed, words),
            returned: one.clone(),
            replies: vec![(SEL_TRANSFER, one.clone()), (SEL_TRANSFER_FROM, one)],
            storage: self.start.clone(),
            ..flat
        };
        let free = Free {
            words: inputs.calldata.len() / 32,
            value: false,
            storage: false,
            answers: true,
            settings: None,
            fixed,
        };
        (inputs, free)
    }

    fn run(&mut self, f: &Function, inputs: &Inputs) -> Path {
        let code = self.c.code_of(f);
        let explorer = self.explorers.of(code);
        explorer.run(inputs)
    }

    fn answers(&mut self, layout: MappingLayout, out: &mut Vec<Finding>) {
        let mut unanswered: Vec<String> = Vec::new();
        let mut first_unanswered = None;
        let functions: Vec<&Function> = self.externals().collect();
        for f in functions {
            let (start, free) = self.base(f, path::varied_word);
            let found = self.explore(f, &start, &free, LIMITS);
            let asks = |p: &&Path| {
                // An asset that is asked who owns one item moves items, not amounts. Moving
                // an item returns nothing, so there is no answer it could refuse with.
                let items = |asset: U256| {
                    let owner = |c: &CallRecord| abi::selector(&c.input) == Some(SEL_OWNER_OF);
                    p.run.calls.iter().any(|c| c.addr == asset && owner(c))
                };
                let transfer = |c: &CallRecord| {
                    let s = abi::selector(&c.input);
                    let moves = s == Some(SEL_TRANSFER) || s == Some(SEL_TRANSFER_FROM);
                    c.kind == op::CALL && moves && !items(c.addr)
                };
                p.succeeded() && p.run.calls.iter().any(transfer)
            };
            let Some(p) = found.iter().find(asks) else {
                continue;
            };
            confirm_stated_amount(out, f, p, layout);
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
            let (mut start, free) = self.base(f, path::varied_word);
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
}

fn confirm_stated_amount(out: &mut [Finding], f: &Function, p: &Path, layout: MappingLayout) {
    let pulled = all_taken(p);
    let measured = |c: &CallRecord| abi::selector(&c.input) == Some(SEL_BALANCE_OF);
    let trusted = credited(p, layout) == Some(pulled) && !p.run.calls.iter().any(measured);
    let name = display_name(f);
    let known = out
        .iter_mut()
        .find(|x| x.id == "fee-on-transfer" && x.function.as_deref() == Some(name.as_str()));
    if let (true, false, Some(x)) = (trusted, pulled.is_zero(), known) {
        x.description.push_str(
            " Confirmed by running it: the attached call asks the asset for an amount, never reads its own balance, and credits the caller exactly the amount asked for.",
        );
        x.confidence = Confidence::High;
        x.confirm(p);
    }
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

pub fn findings(c: &Contract, out: &mut Vec<Finding>) {
    if std::env::var("EVMDEC_NO_CONFIRM").is_ok() || c.info.runtime.is_empty() {
        return;
    }
    let layout = c.compiler.layout;
    let mut pass = Pass {
        c,
        explorers: Explorers::default(),
        start: deploy::start(c),
    };
    pass.answers(layout, out);
    pass.moved_by_answer(out);
}
