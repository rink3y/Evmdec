use crate::exec::FrameRun;
use crate::interp::Outcome;
use crate::solve::Inputs;
use crate::u256::U256;

const MAX_LINES: usize = 6;

fn listed(mut lines: Vec<String>, what: &str) -> Vec<String> {
    let extra = lines.len().saturating_sub(MAX_LINES);
    lines.truncate(MAX_LINES);
    if extra > 0 {
        lines.push(format!("and {extra} more {what}"));
    }
    lines
}

pub fn observed(inputs: &Inputs, run: &FrameRun) -> Vec<String> {
    let mut out = Vec::new();
    let value = match inputs.callvalue.is_zero() {
        true => String::new(),
        false => format!(" with value {}", inputs.callvalue.to_hex()),
    };
    out.push(format!("sent by {}{value}", inputs.caller.to_hex()));

    let mut slots: Vec<(U256, U256, U256)> = run
        .storage
        .iter()
        .map(|(slot, after)| {
            let before = inputs.storage.get(slot).copied().unwrap_or(U256::ZERO);
            (*slot, before, *after)
        })
        .filter(|(_, before, after)| before != after)
        .collect();
    slots.sort();
    let writes = slots.iter().map(|(slot, before, after)| {
        format!(
            "slot {}: {} becomes {}",
            slot.to_hex(),
            before.to_hex(),
            after.to_hex()
        )
    });
    out.extend(listed(writes.collect(), "slots"));

    let calls = run.calls.iter().map(|c| {
        let selector = match c.input.get(..4) {
            Some(b) => format!(
                " selector 0x{:02x}{:02x}{:02x}{:02x}",
                b[0], b[1], b[2], b[3]
            ),
            None => String::new(),
        };
        let value = match c.value.is_zero() {
            true => String::new(),
            false => format!(" value {}", c.value.to_hex()),
        };
        format!("calls {}{selector}{value}", c.addr.to_hex())
    });
    out.extend(listed(calls.collect(), "calls"));

    out.push(match &run.outcome {
        Outcome::Stop => "ends normally".to_string(),
        Outcome::Return(data) => format!("ends normally and returns {} bytes", data.len()),
        Outcome::SelfDestruct(to) => format!(
            "removes the contract and sends its balance to {}",
            to.to_hex()
        ),
        Outcome::Revert(_) => "reverts".to_string(),
        _ => "does not end normally".to_string(),
    });
    out
}
