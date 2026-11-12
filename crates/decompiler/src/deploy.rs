use crate::decompile::Contract;
use crate::exec;
use crate::interp::{Host, Outcome};
use crate::metadata::CodeKind;
use crate::u256::U256;
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
    let host = Host::controlled(exec::SELF, DEPLOYER, Vec::new(), U256::ZERO);
    let run = exec::run_frame(&code, &host, HashMap::new(), STEP_BUDGET);
    match run.outcome {
        Outcome::Return(_) => run.storage,
        _ => HashMap::new(),
    }
}

pub fn start_text(start: &HashMap<U256, U256>) -> &'static str {
    if start.is_empty() {
        "empty storage"
    } else {
        "the storage its constructor leaves"
    }
}
