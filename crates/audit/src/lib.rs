pub mod budget;
pub mod chain;
pub mod explore;
pub mod laws;
pub mod model;
pub mod report;
pub mod shape;
pub mod source;
pub mod trace;
pub mod world;

use evmdec::decompile::Contract;
pub use report::{markdown, merge, Report};
use std::rc::Rc;
use std::time::Instant;

// The interpreter steps one contract may cost, whatever machine it runs on.
pub const WORK: u64 = 40_000_000;

/* No EVM contract starts with 0xef. What does is a program for another machine or a
pointer to another account's code, and running it as EVM code would report nothing
found about a program that was never run. */
#[must_use]
pub fn not_runnable(code: &[u8]) -> Option<&'static str> {
    match code {
        [0xef, 0x01, 0x00, ..] => Some("This account holds no code of its own. It points at another account whose code it runs, and that is the code to audit."),
        [0xef, ..] => Some("This is not EVM bytecode. It starts with 0xef, which marks a program in another format, and this tool runs EVM code only."),
        _ => None,
    }
}

#[must_use]
pub fn audit(c: &Contract) -> Report {
    audit_within(c, WORK)
}

#[must_use]
pub fn audit_within(c: &Contract, work: u64) -> Report {
    let started = Instant::now();
    let before = budget::used();
    let mut explorer = explore::Explorer::new(c);
    if !c.info.runtime.is_empty() && not_runnable(&c.info.runtime).is_none() {
        explorer.explore(work);
    }
    report::build(
        &explorer,
        started.elapsed().as_millis(),
        budget::used() - before,
    )
}

#[must_use]
pub fn audit_read(c: &Contract, source: Rc<dyn world::Source>, number: u64, time: u64) -> Report {
    let started = Instant::now();
    let before = budget::used();
    let mut explorer = explore::Explorer::on_chain(c, source, number, time);
    if !c.info.runtime.is_empty() && not_runnable(&c.info.runtime).is_none() {
        explorer.explore(WORK);
    }
    let mut report = report::build(
        &explorer,
        started.elapsed().as_millis(),
        budget::used() - before,
    );
    report.stats.reads = explorer.states[0].world.reads();
    report
}

#[must_use]
pub fn audit_at(
    c: &Contract,
    client: evmdec::rpc::Client,
    chain: &str,
    number: u64,
    time: u64,
) -> Report {
    let node = Rc::new(chain::Node::new(client));
    let mut report = audit_read(c, node.clone(), number, time);
    report.state.push(format!(
        "The contract was run on the state of {chain} at block {number}. Its storage, and the code, storage and ether of every account its calls reached, were read from there."
    ));
    report.state.extend(node.trouble());
    /* The chain's state at one block is one world. A flaw that needs holders, balances
    or settings that block does not have shows only in a world built for it, so the
    contract is also run in the world guessed from its code, and what only that run
    shows is added and marked as such. */
    let guessed = audit(c);
    let shown = |f: &report::Finding| {
        let kinds = std::iter::once(f.kind).chain(f.also.iter().map(|a| a.kind));
        kinds.map(|k| (k, f.function.clone())).collect::<Vec<_>>()
    };
    let known: Vec<(laws::Kind, String)> = report.findings.iter().flat_map(shown).collect();
    let mut added = 0;
    for mut finding in guessed.findings {
        if known.contains(&(finding.kind, finding.function.clone())) {
            continue;
        }
        finding.rests_on.insert(
            0,
            "This was shown in a world guessed from the code alone, not on the chain's state at that block.".to_string(),
        );
        report.findings.push(finding);
        added += 1;
    }
    if added > 0 {
        let guessed_world = |a: String| format!("in the world guessed from the code: {a}");
        report
            .assumed
            .extend(guessed.assumed.into_iter().map(guessed_world));
        report.state.push(format!(
            "{added} finding(s) come from a second run in a world guessed from the code alone, and say so."
        ));
    }
    report
}

/* The report of a contract compiled from source. The code that is run is the code
the compiler produced, so a finding is the same as from the bytecode alone. The source
adds the names of the functions and the line each finding points at. */
#[must_use]
pub fn audit_compiled(built: &source::Compiled) -> Report {
    let options = evmdec::decompile::Options {
        extra_sigs: built.names.clone(),
        ..Default::default()
    };
    let c = evmdec::decompile::decompile(&built.runtime, &options);
    let mut report = audit(&c);
    report.subject = format!(
        "{} in {} (compiler {})",
        built.name, built.file, built.compiler
    );
    for finding in &mut report.findings {
        let at_instruction = finding.pc.and_then(|pc| built.line_of(pc));
        finding.source = at_instruction.or_else(|| built.declared_at(&finding.function));
    }
    report
}

// One report for a contract and the contracts fetched with it.
#[must_use]
pub fn audit_all(c: &Contract) -> Report {
    let mut reports = vec![audit(c)];
    reports.extend(c.linked.iter().map(|linked| audit_within(linked, WORK / 4)));
    merge(reports)
}
