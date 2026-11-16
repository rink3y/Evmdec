pub mod budget;
pub mod explore;
pub mod laws;
pub mod model;
pub mod report;
pub mod source;
pub mod trace;
pub mod world;

use evmdec::decompile::Contract;
pub use report::{markdown, merge, Report};
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
