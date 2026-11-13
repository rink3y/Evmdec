use crate::analyze::Section;
use crate::decompile::Contract;
use crate::exec;
use crate::interp::{Host, Outcome};
use crate::keccak;
use crate::metadata::CodeKind;
use crate::u256::U256;
use std::cell::RefCell;
use std::collections::HashMap;

pub const DEPLOYER: U256 = U256::from_u64(0xdddd_dddd_dddd_dddd);
const STEP_BUDGET: usize = 400_000;

// Empty when only runtime code is known or the constructor does not finish.
// The passes that start from this then start from nothing, as before.
pub fn storage(c: &Contract) -> HashMap<U256, U256> {
    let info = &c.info;
    if info.kind != CodeKind::Creation || info.constructor.is_empty() {
        return HashMap::new();
    }
    let mut code = info.constructor.clone();
    code.extend_from_slice(&info.runtime);
    code.extend_from_slice(&info.constructor_args);
    // Every check that runs code starts from this, so the constructor would run ten
    // times for one report.
    let key = keccak::keccak256(&code);
    if let Some(known) = LAST.with(|last| {
        let last = last.borrow();
        last.as_ref()
            .filter(|(k, _)| *k == key)
            .map(|(_, s)| s.clone())
    }) {
        return known;
    }
    let host = Host::controlled(exec::SELF, DEPLOYER, Vec::new(), U256::ZERO);
    let run = exec::run_frame(&code, &host, HashMap::new(), STEP_BUDGET);
    let storage = match run.outcome {
        Outcome::Return(_) => run.storage,
        _ => HashMap::new(),
    };
    LAST.with(|last| *last.borrow_mut() = Some((key, storage.clone())));
    storage
}

type Stored = ([u8; 32], HashMap<U256, U256>);

thread_local! {
    static LAST: RefCell<Option<Stored>> = const { RefCell::new(None) };
}

const MAX_LINES: usize = 16;

pub fn section(c: &Contract) -> Option<Section> {
    let start = storage(c);
    let args: Vec<U256> = c
        .info
        .constructor_args
        .as_chunks::<32>()
        .0
        .iter()
        .map(|word| U256::from_be_bytes(word))
        .collect();
    let mut slots: Vec<(&U256, &U256)> = start.iter().filter(|(_, v)| !v.is_zero()).collect();
    slots.sort();
    let lines: Vec<String> = slots
        .into_iter()
        .take(MAX_LINES)
        .map(|(slot, value)| {
            let from = args.iter().position(|a| a == value && !a.is_zero());
            let what = match (from, *value == DEPLOYER) {
                (_, true) => "the deployer".to_string(),
                (Some(index), _) => format!("constructor argument {index}"),
                _ => value.to_hex(),
            };
            format!("slot {} is set to {what}", slot.to_hex())
        })
        .collect();
    (!lines.is_empty()).then_some(Section {
        title: "Deployment".to_string(),
        lines,
    })
}

pub fn start_text(start: &HashMap<U256, U256>) -> &'static str {
    if start.is_empty() {
        "empty storage"
    } else {
        "the storage its constructor leaves"
    }
}
