use crate::abi::{self, SEL_BALANCE_OF, SEL_TRANSFER, SEL_TRANSFER_FROM};
use crate::analyze::{push, Confidence, Finding, Severity};
use crate::decompile::{Contract, Function};
use crate::deploy;
use crate::emit::MappingLayout;
use crate::exec;
use crate::function::FnKind;
use crate::interp::MovingBalance;
use crate::path::{self, Explorers, Limits, Path};
use crate::solve::{self, word, Free, Inputs, Step};
use crate::ssa;
use crate::u256::U256;
use std::collections::HashMap;

pub const WORK: u64 = exec::WORK_PER_SECOND;

const LIMITS: Limits = Limits { paths: 8, runs: 24 };
const WORDS: usize = 8;
const MAX_FUNCTIONS: usize = 24;
// Each call-data word gets its own value, so an asset the function asks is traced back
// to the word that named it.
const FIRST_MARK: u64 = 0x00a5_5e70_0000;
const HELD: u64 = 1_000_000;
const MOVED: u64 = 1_000;

struct Pass<'a> {
    c: &'a Contract,
    layout: MappingLayout,
    begin: HashMap<U256, U256>,
    explorers: Explorers,
}

struct Shape {
    calldata: Vec<u8>,
    fixed: Vec<usize>,
}

fn mark(index: usize) -> U256 {
    U256::from_u64(FIRST_MARK + index as u64)
}

fn selector(input: &[u8]) -> Option<u32> {
    let b = input.get(..4)?;
    Some(u32::from_be_bytes([b[0], b[1], b[2], b[3]]))
}

fn set_word(calldata: &mut [u8], index: usize, value: U256) {
    let at = 4 + 32 * index;
    if let Some(slot) = calldata.get_mut(at..at + 32) {
        slot.copy_from_slice(&value.to_be_bytes());
    }
}

// The words whose value the function used as an asset: it asked that address what this
// contract holds there.
fn asked_assets(p: &Path) -> Vec<usize> {
    let words = p.inputs.calldata.len().saturating_sub(4) / 32;
    let asked = |index: &usize| {
        let value = word(&p.inputs.calldata, 4 + 32 * index);
        p.run.calls.iter().any(|c| {
            let holder = c.input.len() >= 36 && word(&c.input, 4) == p.inputs.address;
            c.addr == value && selector(&c.input) == Some(SEL_BALANCE_OF) && holder
        })
    };
    (0..words).filter(asked).collect()
}

fn signed_gt(a: U256, b: U256) -> bool {
    let difference = a.wrapping_sub(b);
    !difference.is_zero() && (difference >> 255).is_zero()
}

impl<'a> Pass<'a> {
    fn shape(&self, f: &Function) -> Shape {
        let selector = exec::selector_of(f);
        let types: Vec<String> = f.params.iter().map(|p| p.ty.clone()).collect();
        let shaped = abi::layout_with(selector, &types, 2);
        let (calldata, fixed) = match shaped.fixed.is_empty() {
            true => (path::inputs_for(selector, WORDS).calldata, Vec::new()),
            false => (shaped.calldata, shaped.fixed),
        };
        Shape {
            calldata: path::fill_words(&calldata, &fixed, mark),
            fixed,
        }
    }

    fn inputs(&self, calldata: Vec<u8>, moving: Vec<MovingBalance>) -> Inputs {
        let one = U256::ONE.to_be_bytes().to_vec();
        Inputs {
            calldata,
            storage: self.begin.clone(),
            returned: one.clone(),
            replies: vec![
                (SEL_TRANSFER, one.clone()),
                (SEL_TRANSFER_FROM, one),
                (SEL_BALANCE_OF, U256::from_u64(HELD).to_be_bytes().to_vec()),
            ],
            moving,
            ..path::inputs_for(None, 0)
        }
    }

    fn ended(&mut self, f: &Function, shape: &Shape, start: Inputs) -> Vec<Path> {
        if exec::spent() {
            return Vec::new();
        }
        let free = Free {
            words: start.calldata.len() / 32,
            value: false,
            storage: false,
            answers: true,
            settings: None,
            fixed: shape.fixed.clone(),
        };
        let code = self.c.code_of(f);
        let found = self.explorers.of(code).explore(&start, &free, LIMITS);
        found.into_iter().filter(Path::succeeded).collect()
    }

    // What the run added to the entries kept under an asset, as one signed number.
    fn recorded(&self, p: &Path, asset: U256) -> Option<U256> {
        let mut net = None;
        for step in solve::steps(&p.effects, &p.inputs) {
            let Step::Write {
                key, before, after, ..
            } = step
            else {
                continue;
            };
            let keyed = ssa::slot_path(key, self.layout).is_some_and(|slot| {
                slot.steps.iter().any(|s| match s {
                    ssa::Step::Key(k) => solve::value_of(*k, &p.inputs) == Some(asset),
                    _ => false,
                })
            });
            if keyed {
                let change = after.wrapping_sub(before);
                net = Some(net.unwrap_or(U256::ZERO).wrapping_add(change));
            }
        }
        net
    }

    fn check(&mut self, f: &'a Function, out: &mut Vec<Finding>) {
        let shape = self.shape(f);
        let probe = self.inputs(shape.calldata.clone(), Vec::new());
        let assets = self
            .ended(f, &shape, probe)
            .iter()
            .map(asked_assets)
            .find(|words| words.len() >= 2);
        let Some(assets) = assets else { return };
        let (first, second) = (assets[0], assets[1]);
        let held = U256::from_u64(HELD);
        let less = held - U256::from_u64(MOVED);
        let more = held + U256::from_u64(MOVED);
        let moves = |asset: U256, after: U256| MovingBalance {
            asset,
            before: held,
            after,
        };
        // With two different assets the records have to follow what each one reports.
        // Only then is an entry known to be the record of an asset.
        let apart = [(less, more), (more, less)].into_iter().find_map(|(a, b)| {
            let moving = vec![moves(mark(first), a), moves(mark(second), b)];
            let start = self.inputs(shape.calldata.clone(), moving);
            let run = self.ended(f, &shape, start).into_iter().next()?;
            let follows = |index: usize, after: U256| {
                self.recorded(&run, mark(index)) == Some(after.wrapping_sub(held))
            };
            (follows(first, a) && follows(second, b)).then_some(run)
        });
        let Some(apart) = apart else { return };
        let mut same = apart.inputs.calldata.clone();
        set_word(&mut same, second, mark(first));
        let start = self.inputs(same, vec![moves(mark(first), more)]);
        let Some(together) = self.ended(f, &shape, start).into_iter().next() else {
            return;
        };
        let received = U256::from_u64(MOVED);
        let Some(credited) = self.recorded(&together, mark(first)) else {
            return;
        };
        if !signed_gt(credited, received) {
            return;
        }
        push(
            out,
            "ledger-credits-more-than-received",
            "The records credit more of an asset than the contract received",
            Severity::High,
            Confidence::High,
            Some(f),
            None,
            format!(
                "`{}` keeps a record per asset and takes the asset from words {first} and {second} of its call data. Run with two different assets, the record of each changed by exactly what that asset's balance changed during the call. Run again with both words naming one asset, whose balance rose by {} during the call, the record of that asset rose by {}. The two updates meant for two assets landed on one entry, so the contract now owes more of the asset than it holds, and the difference is paid from what others put in.",
                f.name,
                received.to_hex(),
                credited.to_hex(),
            ),
            Vec::new(),
            "Refuse a call whose two assets are the same, or work out one net change per asset before writing the record.",
        );
        if let Some(finding) = out.last_mut() {
            finding.confirm(&together);
        }
    }
}

pub fn findings(c: &Contract, out: &mut Vec<Finding>) {
    if std::env::var("EVMDEC_NO_CONFIRM").is_ok() || c.info.runtime.is_empty() {
        return;
    }
    let mut pass = Pass {
        c,
        layout: c.compiler.layout,
        begin: deploy::start(c),
        explorers: Explorers::default(),
    };
    let external = |f: &&Function| f.kind == FnKind::External && f.effects.writes_storage;
    for f in c.functions.iter().filter(external).take(MAX_FUNCTIONS) {
        pass.check(f, out);
    }
}
