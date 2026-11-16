pub mod budget;
pub mod explore;
pub mod laws;
pub mod model;
pub mod report;
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

// One report for a contract and the contracts fetched with it.
#[must_use]
pub fn audit_all(c: &Contract) -> Report {
    let mut reports = vec![audit(c)];
    reports.extend(c.linked.iter().map(|linked| audit_within(linked, WORK / 4)));
    merge(reports)
}
