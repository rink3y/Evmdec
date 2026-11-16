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

#[must_use]
pub fn audit(c: &Contract) -> Report {
    audit_within(c, WORK)
}

#[must_use]
pub fn audit_within(c: &Contract, work: u64) -> Report {
    let started = Instant::now();
    let before = budget::used();
    let mut explorer = explore::Explorer::new(c);
    if !c.info.runtime.is_empty() {
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
