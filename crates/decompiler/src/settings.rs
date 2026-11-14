use crate::abi;
use crate::decompile::{Contract, Function};
use crate::deploy;
use crate::exec;
use crate::function::FnKind;
use crate::lift::Stmt;
use crate::origin::Loc;
use crate::path::{self, Explorers, Limits, Path};
use crate::solve::{Free, Inputs, Settable};
use crate::u256::U256;
use std::collections::{BTreeMap, HashSet};
use std::rc::Rc;

pub const WORK: u64 = exec::WORK_PER_SECOND;

const LIMITS: Limits = Limits {
    paths: 10,
    runs: 30,
};
const WORDS: usize = 8;
const MAX_FUNCTIONS: usize = 48;
const MAX_SETTINGS: usize = 32;

fn acts(p: &Path) -> bool {
    let effect = |s: &Stmt| {
        matches!(
            s,
            Stmt::SStore { .. } | Stmt::Call { .. } | Stmt::Log { .. }
        )
    };
    p.succeeded() && p.effects.iter().any(effect)
}

fn chosen(start: &Inputs, p: &Path) -> Vec<(U256, U256)> {
    let new = |(slot, value): (&U256, &U256)| {
        (start.storage.get(slot) != Some(value)).then_some((*slot, *value))
    };
    let mut out: Vec<(U256, U256)> = p.inputs.storage.iter().filter_map(new).collect();
    out.sort();
    out
}

// Runtime code does not say how its contract was set up. A function that tests a flag, a
// limit or the code behind a stored address stops there when that storage is empty, and
// nothing after the test is ever measured. One set of values is taken here under which
// the functions any account may call do run, and every later check starts from it.
// Each function sees what the ones before it needed, so the set stays one configuration.
pub fn assume(c: &Contract, open: HashSet<Loc>) {
    if std::env::var("EVMDEC_NO_CONFIRM").is_ok() || c.info.runtime.is_empty() {
        return;
    }
    let settable = Rc::new(Settable {
        layout: c.compiler.layout,
        open,
    });
    let mut held = deploy::storage(c);
    let mut taken: BTreeMap<U256, U256> = BTreeMap::new();
    let mut explorers = Explorers::default();
    let external = |f: &&Function| f.kind == FnKind::External && f.effects.reads_storage;
    for f in c.functions.iter().filter(external).take(MAX_FUNCTIONS) {
        if exec::spent() || taken.len() >= MAX_SETTINGS {
            break;
        }
        let selector = exec::selector_of(f);
        let types: Vec<String> = f.params.iter().map(|p| p.ty.clone()).collect();
        let shaped = abi::layout(selector, &types);
        let flat = path::inputs_for(selector, WORDS);
        let starts = [
            (shaped.calldata, shaped.fixed),
            (flat.calldata.clone(), Vec::new()),
        ];
        for (calldata, fixed) in starts {
            let free = Free {
                words: WORDS.max(calldata.len() / 32),
                value: true,
                storage: false,
                answers: true,
                settings: Some(settable.clone()),
                fixed,
            };
            let start = Inputs {
                calldata,
                storage: held.clone(),
                returned: U256::ONE.to_be_bytes().to_vec(),
                ..flat.clone()
            };
            let paths = explorers.of(c.code_of(f)).explore(&start, &free, LIMITS);
            // The run that passed the most tests needed the most of the configuration.
            let Some(best) = paths
                .iter()
                .filter(|p| acts(p))
                .max_by_key(|p| p.truth.len())
            else {
                continue;
            };
            for (slot, value) in chosen(&start, best) {
                held.insert(slot, value);
                taken.insert(slot, value);
            }
            break;
        }
    }
    deploy::assume(c, taken.into_iter().collect());
}
