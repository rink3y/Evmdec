use crate::explore::{Explorer, Step, Violation};
use crate::laws::Kind;
use crate::trace::{Cell, Event, Run, Tag, BAL, CALLER, CLOCK, DATA, MATH, OUT, STORE, VALUE};
use crate::world::{Addr, ACTOR, ALLY, OWNER, USER};
use evmdec::hex;
use evmdec::U256;
use serde::Serialize;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Severity {
    Medium,
    High,
    Critical,
}

#[derive(Clone, Debug, Serialize)]
pub struct Finding {
    pub kind: Kind,
    pub severity: Severity,
    pub function: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub selector: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub pc: Option<usize>,
    pub title: String,
    pub cause: String,
    pub shown: String,
    pub steps: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub rests_on: Vec<String>,
    pub reentered: bool,
}

#[derive(Clone, Debug, Serialize)]
pub struct FunctionModel {
    pub name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub selector: Option<String>,
    pub ends_for: Vec<&'static str>,
    pub tests_caller: bool,
    pub takes_value: bool,
    pub pays_out: bool,
    pub calls_out: bool,
    pub runs_other_code: bool,
    pub writes: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct CellModel {
    pub slot: String,
    pub keys: usize,
    pub used_as: Vec<&'static str>,
    pub written_by: Vec<String>,
    pub open_to_anyone: bool,
}

#[derive(Clone, Debug, Serialize)]
pub struct Chain {
    pub steps: Vec<usize>,
    pub summary: String,
}

#[derive(Clone, Debug, Default, Serialize)]
pub struct Stats {
    pub functions: usize,
    pub functions_ended: usize,
    pub calls_made: u64,
    pub states_kept: usize,
    pub work: u64,
    pub ms: u128,
}

#[derive(Clone, Debug, Serialize)]
pub struct Report {
    pub subject: String,
    pub code_size: usize,
    pub findings: Vec<Finding>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub chains: Vec<Chain>,
    pub functions: Vec<FunctionModel>,
    pub cells: Vec<CellModel>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub assumed: Vec<String>,
    pub stats: Stats,
}

fn who(account: Addr) -> &'static str {
    match account {
        a if a == OWNER => "the owner",
        a if a == USER => "a user",
        a if a == ACTOR => "an account with no role",
        a if a == ALLY => "a second address of the account with no role",
        _ => "another account",
    }
}

fn short(value: U256) -> String {
    match value {
        v if v == ACTOR => "<account>".to_string(),
        v if v == ALLY => "<account's second address>".to_string(),
        v if v == USER => "<user>".to_string(),
        v if v == OWNER => "<owner>".to_string(),
        v if v == U256::MAX => "<largest number>".to_string(),
        v => v.to_hex(),
    }
}

fn asset_name(asset: Option<Addr>) -> String {
    match asset {
        None => "ether".to_string(),
        Some(asset) => format!("the asset at {}", asset.to_hex()),
    }
}

fn cell_name(cell: &Cell) -> String {
    match cell.keys.len() {
        0 => format!("slot {}", cell.slot.to_hex()),
        n => format!(
            "the mapping at slot {} ({n} key{})",
            cell.root.to_hex(),
            if n == 1 { "" } else { "s" }
        ),
    }
}

// Where a word came from, in words a reader can check against the code.
fn source(tag: Tag, run: &Run) -> String {
    let mut parts: Vec<String> = Vec::new();
    if tag.has(CALLER) {
        parts.push("the caller's address".into());
    }
    if tag.has(DATA) {
        parts.push(match tag.word() {
            Some(word) => format!("word {word} of the call data"),
            None => "the call data".into(),
        });
    }
    if tag.has(VALUE) {
        parts.push("the ether sent with the call".into());
    }
    if tag.has(STORE) {
        parts.push(match run.cell_of(tag) {
            Some(cell) if cell.keys.iter().any(|k| k.tag.only(CALLER)) => {
                format!("the caller's entry in {}", cell_name(cell))
            }
            Some(cell) if cell.keys.iter().any(|k| k.tag.has(DATA)) => {
                format!("an entry of {} chosen by the call data", cell_name(cell))
            }
            Some(cell) => cell_name(cell),
            None => "storage".into(),
        });
    }
    if tag.has(BAL) {
        parts.push("a balance read at that moment".into());
    }
    if tag.has(OUT) {
        parts.push("an answer from another contract".into());
    }
    if tag.has(CLOCK) {
        parts.push("the block time".into());
    }
    match (parts.is_empty(), tag.has(MATH)) {
        (true, _) => "a value fixed in the code".into(),
        (false, true) => format!("a sum worked out from {}", parts.join(" and ")),
        (false, false) => parts.join(" and "),
    }
}

fn caller_tests(run: &Run) -> String {
    let mut against: Vec<String> = Vec::new();
    for event in &run.events {
        let tags = match event {
            Event::Cmp { ta, tb, .. } if ta.only(CALLER) => vec![*tb],
            Event::Cmp { ta, tb, .. } if tb.only(CALLER) => vec![*ta],
            Event::Branch { tag, .. } if tag.has(STORE) => {
                let keyed = run
                    .cell_of(*tag)
                    .is_some_and(|c| c.keys.iter().any(|k| k.tag.only(CALLER)));
                if keyed {
                    vec![*tag]
                } else {
                    Vec::new()
                }
            }
            _ => Vec::new(),
        };
        for tag in tags {
            let name = source(tag, run);
            if !against.contains(&name) {
                against.push(name);
            }
        }
    }
    match against.is_empty() {
        true => "Nothing on the way tests who the caller is.".to_string(),
        false => format!("The caller is tested only against {}.", against.join(", ")),
    }
}

fn step_text(ex: &Explorer, step: &Step) -> String {
    match step {
        Step::Wait { until } => format!("time passes until {}", until.to_decimal()),
        Step::Told {
            to,
            selector,
            answer,
        } => format!(
            "the contract at {} is taken to answer {selector:#010x} with {} bytes",
            to.to_hex(),
            answer.len()
        ),
        Step::Call { entry, msg } => {
            let e = &ex.entries[*entry];
            let words = msg.data.len().saturating_sub(4) / 32;
            let args: Vec<String> = (0..words.min(6))
                .map(|i| short(U256::from_be_bytes(&msg.data[4 + 32 * i..36 + 32 * i])))
                .collect();
            let value = match msg.value.is_zero() {
                true => String::new(),
                false => format!(" sending {} wei", msg.value.to_decimal()),
            };
            let back = match &msg.hook {
                Some(hook) => format!(
                    ", and when the contract calls it back it calls {}",
                    hex::encode(&hook.data[..hook.data.len().min(4)])
                ),
                None => String::new(),
            };
            format!(
                "{} calls `{}`({}){value}{back}",
                who(msg.from),
                e.name,
                args.join(", ")
            )
        }
    }
}

#[allow(clippy::too_many_lines)]
fn explain(v: &Violation, run: &Run, subject: Addr) -> (String, String, String, Option<usize>) {
    let party = |a: Addr| a == ACTOR || a == ALLY;
    let pays = run.events.iter().filter_map(|e| match e {
        Event::Pay {
            asset,
            from,
            to,
            amount,
            to_tag,
            amount_tag,
        } => Some((*asset, *from, *to, *amount, *to_tag, *amount_tag)),
        _ => None,
    });
    let tests = caller_tests(run);
    let again = match v.via_hook {
        true => " The contract hands control to the receiver before its own records are brought up to date, and the receiver calls in again while the old records still stand.",
        false => "",
    };
    match v.breach.kind {
        Kind::Gain => {
            let asset = v.breach.asset;
            let mut to_party: Vec<_> = pays.filter(|p| p.0 == asset && party(p.2)).collect();
            to_party.sort_by_key(|p| p.3);
            let amount = short(v.breach.amount);
            let shown = format!("The account ended with {amount} more of {} than it started with and with no less of anything else.", asset_name(asset));
            match to_party.last() {
                Some((_, from, _, _, to_tag, amount_tag)) => {
                    let whose = match *from == subject {
                        true => "out of the contract",
                        false => "out of another account",
                    };
                    let title = format!(
                        "An account with no role takes {} {whose}",
                        asset_name(asset)
                    );
                    let cause = format!(
                        "The payment goes to {} and its amount is {}. {tests}{again}",
                        source(*to_tag, run),
                        source(*amount_tag, run)
                    );
                    (title, cause, shown, None)
                }
                None => {
                    let title = format!(
                        "An account with no role ends with more {}",
                        asset_name(asset)
                    );
                    (title, format!("{tests}{again}"), shown, None)
                }
            }
        }
        Kind::Loss => {
            let asset = v.breach.asset;
            let victim = v.breach.victim.unwrap_or(USER);
            let moved = run.calls.iter().find(|c| {
                c.ok && c.input.len() >= 100 && U256::from_be_bytes(&c.input[4..36]) == victim
            });
            let named = match moved {
                Some(call) => format!(
                    "The account whose {} is moved is {}, the receiver is {} and the amount is {}.",
                    asset_name(asset),
                    source(call.arg_tags.first().copied().unwrap_or(Tag::NONE), run),
                    source(call.arg_tags.get(1).copied().unwrap_or(Tag::NONE), run),
                    source(call.arg_tags.get(2).copied().unwrap_or(Tag::NONE), run),
                ),
                None => "The account that pays did not make the call.".to_string(),
            };
            let title = format!(
                "An account with no role moves {} out of another account",
                asset_name(asset)
            );
            let shown = format!(
                "{} ended with {} less of {} and made no call.",
                capital(who(victim)),
                short(v.breach.amount),
                asset_name(asset)
            );
            (
                title,
                format!("{named} {tests}{again}"),
                shown,
                moved.map(|c| c.pc),
            )
        }
        Kind::Credit | Kind::Debit => {
            let cell = v.breach.cell.as_ref();
            let store = run.stores().find(|(c, ..)| Some(*c) == cell);
            let name = cell.map_or_else(|| "its records".to_string(), cell_name);
            let (tag, pc) = store.map_or((Tag::NONE, None), |s| (s.3, Some(s.4)));
            let key = cell.and_then(|c| {
                c.keys
                    .iter()
                    .find(|k| k.tag.has(DATA) || k.tag.only(CALLER))
            });
            let keyed = match key {
                Some(key) if key.tag.only(CALLER) => "the caller's own entry",
                Some(_) => "the entry of an account named in the call data",
                None => "an entry",
            };
            let (title, shown) = match v.breach.kind {
                Kind::Credit => (
                    format!("An account with no role is credited in {name} without paying"),
                    format!(
                        "Its entry rose by {} and it paid nothing in.",
                        short(v.breach.amount)
                    ),
                ),
                _ => (
                    format!("An account with no role lowers another account's entry in {name}"),
                    format!(
                        "{} had {} less recorded and made no call.",
                        capital(who(v.breach.victim.unwrap_or(USER))),
                        short(v.breach.amount)
                    ),
                ),
            };
            let cause = format!(
                "The call writes {keyed} in {name}. What it writes is {}. {tests}{again}",
                source(tag, run)
            );
            (title, cause, shown, pc)
        }
        Kind::Takeover | Kind::RoleCleared => {
            let cell = v.breach.cell.as_ref();
            let store = run.stores().find(|(c, ..)| Some(*c) == cell);
            let name = cell.map_or_else(|| "a slot".to_string(), cell_name);
            let (tag, pc) = store.map_or((Tag::NONE, None), |s| (s.3, Some(s.4)));
            let (title, shown) = match v.breach.kind {
                Kind::Takeover => (
                    format!("An account with no role replaces the account named in {name}"),
                    format!("{name} named the owner before the call and another address after it."),
                ),
                _ => (
                    format!("An account with no role clears the account named in {name}"),
                    format!("{name} named the owner before the call and nobody after it."),
                ),
            };
            let cause = format!(
                "Other functions let a caller through only when it is the address in {name}. This call stores {} there. {tests}",
                source(tag, run)
            );
            (title, cause, shown, pc)
        }
        Kind::ForeignCode => {
            let call = v.breach.call.and_then(|i| run.calls.get(i));
            let from = call.map_or_else(|| "the call data".to_string(), |c| source(c.to_tag, run));
            let title =
                "An account with no role chooses code the contract runs as itself".to_string();
            let cause = format!(
                "The call runs the code at an address that comes from {from}, in the contract's own storage and with its own balance. {tests}"
            );
            let shown = "The code that ran was at an address the account supplied.".to_string();
            (title, cause, shown, call.map(|c| c.pc))
        }
        Kind::Destroyed => {
            let to = run.events.iter().find_map(|e| match e {
                Event::Destroy { tag, .. } => Some(*tag),
                _ => None,
            });
            let title = "An account with no role destroys the contract".to_string();
            let cause = format!(
                "The call ends in the instruction that removes the contract and sends its ether to {}. {tests}",
                source(to.unwrap_or(Tag::NONE), run)
            );
            (
                title,
                cause,
                "The contract's code was destroyed.".to_string(),
                None,
            )
        }
    }
}

fn capital(text: &str) -> String {
    let mut chars = text.chars();
    match chars.next() {
        Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
        None => String::new(),
    }
}

fn finding(ex: &Explorer, v: &Violation) -> Finding {
    let e = &ex.entries[v.entry];
    let (title, cause, shown, pc) = explain(v, &v.run, ex.subject);
    let rests_on: Vec<String> = v
        .steps
        .iter()
        .filter(|s| matches!(s, Step::Told { .. }))
        .map(|s| step_text(ex, s))
        .collect();
    let severity = match v.breach.kind {
        Kind::RoleCleared => Severity::Medium,
        Kind::Gain | Kind::Loss | Kind::Takeover | Kind::ForeignCode | Kind::Destroyed => {
            Severity::Critical
        }
        Kind::Credit | Kind::Debit => Severity::High,
    };
    Finding {
        kind: v.breach.kind,
        severity,
        function: e.name.clone(),
        selector: e.selector.map(|s| format!("{s:#010x}")),
        pc,
        title: format!("`{}`: {title}", e.name),
        cause,
        shown,
        steps: v.steps.iter().map(|s| step_text(ex, s)).collect(),
        rests_on,
        reentered: v.via_hook,
    }
}

fn models(ex: &Explorer) -> (Vec<FunctionModel>, Vec<CellModel>) {
    let name = |i: &usize| ex.entries[*i].name.clone();
    let functions = ex.entries.iter().enumerate().map(|(i, e)| {
        let facts = &ex.facts.entries[i];
        let ends_for: Vec<&'static str> = [OWNER, USER, ACTOR]
            .into_iter()
            .filter(|w| facts.ended.contains(w))
            .map(who)
            .collect();
        FunctionModel {
            name: e.name.clone(),
            selector: e.selector.map(|s| format!("{s:#010x}")),
            ends_for,
            tests_caller: facts.checks_caller,
            takes_value: facts.takes_in,
            pays_out: facts.pays_out,
            calls_out: facts.calls_out,
            runs_other_code: facts.runs_other_code,
            writes: facts.writes.iter().map(|p| p.root.to_hex()).collect(),
        }
    });
    let cells = ex.facts.places.iter().map(|(place, facts)| {
        let mut used_as = Vec::new();
        for (holds, label) in [
            (facts.identity, "an account the caller is compared with"),
            (facts.gate, "a role held per account"),
            (facts.ledger(), "a ledger of value per account"),
            (facts.target, "the address of a contract that is called"),
            (facts.assumed, "taken to be set"),
        ] {
            if holds {
                used_as.push(label);
            }
        }
        CellModel {
            slot: place.root.to_hex(),
            keys: place.depth,
            used_as,
            written_by: facts.writers.iter().map(name).collect(),
            open_to_anyone: !facts.open_writers.is_empty(),
        }
    });
    (functions.collect(), cells.collect())
}

/* A finding reached only after an earlier call by the same account is one end of a
path. Where that earlier call is a finding too, the two are one attack. */
fn chains(ex: &Explorer, findings: &[Finding]) -> Vec<Chain> {
    let last_call = |v: &Violation| match v.steps.last() {
        Some(Step::Call { entry, msg }) => Some((*entry, msg.data.clone())),
        _ => None,
    };
    let mut out = Vec::new();
    for (i, v) in ex.found.iter().enumerate() {
        let earlier = &v.steps[..v.steps.len().saturating_sub(1)];
        let by_actor = earlier.iter().filter_map(|s| match s {
            Step::Call { entry, msg } if msg.from == ACTOR => Some((*entry, msg.data.clone())),
            _ => None,
        });
        let mut steps: Vec<usize> = by_actor
            .filter_map(|call| {
                ex.found
                    .iter()
                    .position(|w| last_call(w) == Some(call.clone()))
            })
            .collect();
        steps.dedup();
        if steps.is_empty() || steps.contains(&i) {
            continue;
        }
        steps.push(i);
        let names: Vec<&str> = steps.iter().map(|s| findings[*s].title.as_str()).collect();
        out.push(Chain {
            summary: names.join(", then "),
            steps,
        });
    }
    out
}

#[must_use]
pub fn build(ex: &Explorer, ms: u128, work: u64) -> Report {
    let findings: Vec<Finding> = ex.found.iter().map(|v| finding(ex, v)).collect();
    let chains = chains(ex, &findings);
    let (functions, cells) = models(ex);
    let ended = ex
        .facts
        .entries
        .iter()
        .filter(|f| !f.ended.is_empty())
        .count();
    Report {
        subject: ex
            .c
            .address
            .clone()
            .unwrap_or_else(|| "bytecode".to_string()),
        code_size: ex.c.info.runtime.len(),
        findings,
        chains,
        functions,
        cells,
        assumed: ex.assumed.clone(),
        stats: Stats {
            functions: ex.entries.len(),
            functions_ended: ended,
            calls_made: ex.runs,
            states_kept: ex.states.len(),
            work,
            ms,
        },
    }
}

#[must_use]
pub fn markdown(report: &Report) -> String {
    let mut out = format!(
        "# Audit of {}\n\nCode size: {} bytes\n\n",
        report.subject, report.code_size
    );
    let s = &report.stats;
    out.push_str(&format!(
        "{} of {} functions ended under some input, over {} calls and {} kept states, in {} ms.\n\n",
        s.functions_ended, s.functions, s.calls_made, s.states_kept, s.ms
    ));
    match report.findings.len() {
        0 => out.push_str("## Findings\n\nNo run showed an account with no role gaining, taking from another account, or taking the contract over. That is what was tried, not a proof that nothing can.\n\n"),
        n => out.push_str(&format!("## Findings ({n})\n\n")),
    }
    for (i, f) in report.findings.iter().enumerate() {
        out.push_str(&format!("### {}. {}\n\n", i + 1, f.title));
        out.push_str(&format!("- **Severity:** {:?}\n", f.severity));
        out.push_str(&format!("- **Why:** {}\n", f.cause));
        out.push_str(&format!("- **Shown by a run:** {}\n", f.shown));
        if !f.rests_on.is_empty() {
            out.push_str(&format!("- **Rests on:** {}\n", f.rests_on.join("; ")));
        }
        out.push_str("- **Steps:**\n");
        for (n, step) in f.steps.iter().enumerate() {
            out.push_str(&format!("  {}. {step}\n", n + 1));
        }
        out.push('\n');
    }
    if !report.chains.is_empty() {
        out.push_str("## Attack paths\n\n");
        for chain in &report.chains {
            out.push_str(&format!("- {}\n", chain.summary));
        }
        out.push('\n');
    }
    out.push_str("## What each function was seen to do\n\n| Function | Ends for | Tests caller | Takes value | Pays out | Calls out |\n|---|---|---|---|---|---|\n");
    let mark = |b: bool| if b { "yes" } else { "" };
    for f in &report.functions {
        out.push_str(&format!(
            "| `{}` | {} | {} | {} | {} | {} |\n",
            f.name,
            f.ends_for.join(", "),
            mark(f.tests_caller),
            mark(f.takes_value),
            mark(f.pays_out),
            mark(f.calls_out || f.runs_other_code)
        ));
    }
    out.push_str("\n## Storage as it was used\n\n| Slot | Keys | Used as | Written by | Anyone can write |\n|---|---|---|---|---|\n");
    for c in report.cells.iter().filter(|c| !c.used_as.is_empty()) {
        out.push_str(&format!(
            "| {} | {} | {} | {} | {} |\n",
            c.slot,
            c.keys,
            c.used_as.join(", "),
            c.written_by.join(", "),
            mark(c.open_to_anyone)
        ));
    }
    if !report.assumed.is_empty() {
        out.push_str("\n## Taken to hold\n\nRuntime code does not say how the contract was set up. These were taken to hold because the owner's own calls are refused without them.\n\n");
        for a in &report.assumed {
            out.push_str(&format!("- {a}\n"));
        }
    }
    out
}

// The reports of several contracts as one, each finding under its contract.
#[must_use]
pub fn merge(reports: Vec<Report>) -> Report {
    let mut all = reports.into_iter();
    let Some(mut first) = all.next() else {
        return Report {
            subject: String::new(),
            code_size: 0,
            findings: Vec::new(),
            chains: Vec::new(),
            functions: Vec::new(),
            cells: Vec::new(),
            assumed: Vec::new(),
            stats: Stats::default(),
        };
    };
    for mut next in all {
        let shift = first.findings.len();
        for f in &mut next.findings {
            f.title = format!("{} (in {})", f.title, next.subject);
        }
        for chain in &mut next.chains {
            chain.steps.iter_mut().for_each(|s| *s += shift);
        }
        first.findings.append(&mut next.findings);
        first.chains.append(&mut next.chains);
        first.assumed.append(&mut next.assumed);
        first.stats.functions += next.stats.functions;
        first.stats.functions_ended += next.stats.functions_ended;
        first.stats.calls_made += next.stats.calls_made;
        first.stats.states_kept += next.stats.states_kept;
        first.stats.work += next.stats.work;
        first.stats.ms += next.stats.ms;
    }
    first
}
