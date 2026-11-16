use crate::explore::{Explorer, Step, Violation};
use crate::laws::Kind;
use crate::trace::{
    Answered, Cell, Event, Run, Tag, BAL, CALLER, CLOCK, DATA, MATH, OUT, STORE, VALUE,
};
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
    // File and line, when the contract was given as source.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source: Option<String>,
    pub title: String,
    pub cause: String,
    pub shown: String,
    pub steps: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub rests_on: Vec<String>,
    pub reentered: bool,
    // What else the same run showed. One run is one finding however many laws it breaks.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub also: Vec<Also>,
}

#[derive(Clone, Debug, Serialize)]
pub struct Also {
    pub kind: Kind,
    pub title: String,
    pub shown: String,
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
    // What stopped the call that got furthest, for a function that never ended.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stopped_by: Option<String>,
    pub in_code: crate::model::InCode,
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
    #[serde(skip_serializing_if = "is_zero")]
    pub reads: u64,
}

#[allow(clippy::trivially_copy_pass_by_ref)]
fn is_zero(count: &u64) -> bool {
    *count == 0
}

#[derive(Clone, Debug, Serialize)]
pub struct Report {
    pub subject: String,
    pub code_size: usize,
    // Why nothing was run, for code this machine cannot run.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub not_run: Option<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub state: Vec<String>,
    pub findings: Vec<Finding>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub chains: Vec<Chain>,
    pub functions: Vec<FunctionModel>,
    pub cells: Vec<CellModel>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub slots_in_code: Vec<crate::model::SlotInCode>,
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

// An account this world did not make has no name but its address.
fn holder(account: Addr) -> String {
    match who(account) {
        "another account" => format!("the account at {}", account.to_hex()),
        known => known.to_string(),
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

// A cell another contract keeps is named with that contract, or it reads as the subject's own.
fn cell_name(cell: &Cell, run: &Run) -> String {
    let own = match cell.keys.len() {
        0 => format!("slot {}", cell.slot.to_hex()),
        n => format!(
            "the mapping at slot {} ({n} key{})",
            cell.root.to_hex(),
            if n == 1 { "" } else { "s" }
        ),
    };
    match cell.account == run.to {
        true => own,
        false => format!("{own} of the contract at {}", cell.account.to_hex()),
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
                format!("the caller's entry in {}", cell_name(cell, run))
            }
            Some(cell) if cell.keys.iter().any(|k| k.tag.has(DATA)) => {
                format!(
                    "an entry of {} chosen by the call data",
                    cell_name(cell, run)
                )
            }
            Some(cell) => cell_name(cell, run),
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

/* What the run tested its caller against. A comparison with a constant or with the
call data, and a test that the caller's own balance covers an amount, restrict nobody.
They are named as what they are so that they are not read as a permission check. */
fn caller_tests(run: &Run) -> String {
    let mut against: Vec<String> = Vec::new();
    let mut note = |text: String| {
        if !against.contains(&text) {
            against.push(text);
        }
    };
    for event in &run.events {
        match event {
            Event::Cmp { ta, tb, .. } if ta.only(CALLER) || tb.only(CALLER) => {
                let other = if ta.only(CALLER) { *tb } else { *ta };
                note(match other {
                    t if t.is_none() => "a comparison with a constant in the code".into(),
                    t if t.has(DATA) && !t.has(STORE) => {
                        "a comparison with an address the caller put in the call data".into()
                    }
                    t => format!("a comparison with {}", source(t, run)),
                });
            }
            Event::Branch { tag, .. } if tag.has(STORE) => {
                let own = run
                    .cell_of(*tag)
                    .filter(|c| c.keys.iter().any(|k| k.tag.only(CALLER)));
                if let Some(cell) = own {
                    let name = cell_name(cell, run);
                    note(match tag.has(DATA) || tag.has(VALUE) || tag.has(MATH) {
                        true => {
                            format!("whether the caller's own entry in {name} covers an amount")
                        }
                        false => format!("whether the caller's own entry in {name} is set"),
                    });
                }
            }
            _ => {}
        }
    }
    match against.is_empty() {
        true => "Nothing on the way tests who the caller is.".to_string(),
        false => format!(
            "The only tests that involve the caller are {}.",
            against.join(", ")
        ),
    }
}

// Whether two words were worked out from the same call data word or storage cell.
fn related(a: Tag, b: Tag) -> bool {
    a.words & b.words != 0 || (a.cell != 0 && a.cell == b.cell)
}

/* An addition, subtraction or multiplication that went past the end of the number
range in a call that still ended, on the way to the amount the finding is about. */
fn wrapped(run: &Run, amount: Tag) -> &'static str {
    let wraps = run.events.iter().find_map(|e| match e {
        Event::Overflow { tag, op, .. } if related(*tag, amount) => Some(*op),
        _ => None,
    });
    match wraps {
        Some(evmdec::opcode::SIGNEXTEND) => " On the way to that amount a number was read as a narrower signed one and came out negative, and nothing stopped the call, so a subtraction of it adds and an addition takes away.",
        Some(_) => " On the way to that amount an addition, subtraction or multiplication went past the end of the number range and nothing stopped the call, so the amount is not what the earlier checks were made on.",
        None => "",
    }
}

/* Moving or lowering what belongs to an account named in the call data is in order
when that account agreed to it. An agreement is a record kept under both that account
and the caller, and the run read none. */
fn consent(run: &Run, victim: Addr) -> &'static str {
    let read_both = run
        .loads()
        .any(|(cell, _)| cell.keyed_by(victim) && cell.keys.iter().any(|k| k.tag.only(CALLER)));
    match read_both {
        true => "",
        false => " The call reads no record kept under both that account and the caller, so nothing shows that the account agreed.",
    }
}

fn step_text(ex: &Explorer, step: &Step) -> String {
    match step {
        Step::Wait { until } => format!("time passes until {}", until.to_decimal()),
        Step::Funded => {
            "the contract already holds ether and assets that were sent to it".to_string()
        }
        Step::Holds => {
            "the account with no role holds a thousand units in the contract's own ledger, as anyone who came by some would".to_string()
        }
        Step::Told {
            to,
            selector,
            answer,
        } => {
            let said = match answer.len() {
                32 => short(U256::from_be_bytes(answer)),
                n => format!("{n} bytes"),
            };
            format!(
                "the contract at {} is taken to answer {selector:#010x} with {said}",
                to.to_hex()
            )
        }
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
            let at = match msg.to == ex.subject {
                true => String::new(),
                false => format!(" on the contract at {}", msg.to.to_hex()),
            };
            format!(
                "{} calls `{}`({}){at}{value}{back}",
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
                        "The payment goes to {} and its amount is {}.{} {tests}{again}",
                        source(*to_tag, run),
                        source(*amount_tag, run),
                        wrapped(run, *amount_tag)
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
            // The call that moved the asset is the one the books recorded, not the first that names the account.
            let paid = pays
                .clone()
                .find(|p| p.0 == asset && p.1 == victim && !p.3.is_zero());
            let moved = run.calls.iter().find(|c| {
                c.ok && c.input.len() >= 100
                    && U256::from_be_bytes(&c.input[4..36]) == victim
                    && paid.is_none_or(|p| U256::from_be_bytes(&c.input[68..100]) == p.3)
            });
            let named = match (paid, moved) {
                (Some((_, _, _, _, to_tag, amount_tag)), Some(call)) => format!(
                    "The account whose {} is moved is {}, the receiver is {} and the amount is {}.{}{}",
                    asset_name(asset),
                    source(call.arg_tags.first().copied().unwrap_or(Tag::NONE), run),
                    source(to_tag, run),
                    source(amount_tag, run),
                    wrapped(run, amount_tag),
                    consent(run, victim),
                ),
                _ => "The account that pays did not make the call.".to_string(),
            };
            let title = format!(
                "An account with no role moves {} out of another account",
                asset_name(asset)
            );
            let shown = format!(
                "{} ended with {} less of {} and made no call.",
                capital(&holder(victim)),
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
            let name = cell.map_or_else(|| "its records".to_string(), |c| cell_name(c, run));
            let (tag, pc) = store.map_or((Tag::NONE, None), |s| (s.3, Some(s.4)));
            let key = cell.and_then(|c| {
                c.keys
                    .iter()
                    .find(|k| k.tag.has(DATA) || k.tag.only(CALLER))
            });
            let keyed = match key {
                Some(key) if key.tag.only(CALLER) => "the caller's own entry",
                Some(_) => "the entry of an account named in the call data",
                None if v.breach.victim.is_some_and(|a| who(a) == "another account") => {
                    "the entry of an account that the call data does not name"
                }
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
                        capital(&holder(v.breach.victim.unwrap_or(USER))),
                        short(v.breach.amount)
                    ),
                ),
            };
            let agreed = match (v.breach.kind, v.breach.victim) {
                (Kind::Debit, Some(victim)) => consent(run, victim),
                _ => "",
            };
            /* The first write is lost only where the last one was worked out from a read
            made before it. A cell read again in between is updated twice on purpose. */
            let at = |e: &Event| match e {
                Event::Store { cell: c, .. } => (Some(&run.cells[*c]) == cell, true),
                Event::Load { cell: c, .. } => (Some(&run.cells[*c]) == cell, false),
                _ => (false, false),
            };
            let touched: Vec<bool> = run
                .events
                .iter()
                .map(at)
                .filter(|t| t.0)
                .map(|t| t.1)
                .collect();
            let first = touched.iter().position(|write| *write);
            let last = touched.iter().rposition(|write| *write);
            let stale = match (first, last) {
                (Some(first), Some(last)) => {
                    first < last && touched[first..last].iter().all(|w| *w)
                }
                _ => false,
            };
            let twice = match stale {
                true => " The call writes this one entry more than once, and the last write is worked out from what the entry held before the first, so the first write is lost. That happens when the call names the same account on both sides.",
                false => "",
            };
            let back = run
                .called_back
                .iter()
                .find(|(c, _)| Some(&run.cells[*c]) == cell);
            let back = back.map_or(String::new(), |(_, by)| {
                format!(" The write is made while the contract at {} calls back in, during the call the account made.", by.to_hex())
            });
            let cause = format!(
                "The call writes {keyed} in {name}. What it writes is {}.{}{twice}{back}{agreed} {tests}{again}",
                source(tag, run),
                wrapped(run, tag)
            );
            (title, cause, shown, pc)
        }
        Kind::Takeover | Kind::RoleCleared => {
            let cell = v.breach.cell.as_ref();
            let store = run.stores().find(|(c, ..)| Some(*c) == cell);
            let name = cell.map_or_else(|| "a slot".to_string(), |c| cell_name(c, run));
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

/* A function the account with no role never got through, whose code tests no caller
and can do something that matters. The runs say nothing about it either way. */
fn unsettled(f: &FunctionModel) -> bool {
    let c = &f.in_code;
    let matters = !c.writes.is_empty()
        || c.writes_under_keys
        || c.sends_value
        || c.runs_other_code
        || c.destroys;
    !f.ends_for.contains(&who(ACTOR)) && !c.tests_caller && matters
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
    let set_up = ex.states[0].steps.len();
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
        source: None,
        title: format!("`{}`: {title}", e.name),
        cause,
        shown,
        steps: v
            .steps
            .iter()
            .enumerate()
            .map(|(i, s)| match i < set_up {
                true => format!("taken to have been done at set-up: {}", step_text(ex, s)),
                false => step_text(ex, s),
            })
            .collect(),
        rests_on,
        reentered: v.via_hook,
        also: Vec::new(),
    }
}

fn models(ex: &Explorer) -> (Vec<FunctionModel>, Vec<CellModel>) {
    let name = |i: &usize| ex.entries[*i].name.clone();
    let own = &ex.entries[..ex.own];
    let functions = own.iter().enumerate().map(|(i, e)| {
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
            stopped_by: match facts.ended.is_empty() {
                true => ex.stopped.get(i).cloned().flatten().map(|(_, why)| why),
                false => None,
            },
            in_code: crate::model::in_code(ex.c, e.function),
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
/* The finding each consequence belongs to. Consequences of one run, reached by the
same steps, are one finding, and the first kind in the order of the laws leads it. */
fn grouped(ex: &Explorer) -> (Vec<usize>, Vec<usize>) {
    let steps =
        |v: &Violation| -> Vec<String> { v.steps.iter().map(|s| step_text(ex, s)).collect() };
    let same = |a: &Violation, b: &Violation| {
        (a.entry, a.via_hook, a.by_user) == (b.entry, b.via_hook, b.by_user) && steps(a) == steps(b)
    };
    let (mut leads, mut of): (Vec<usize>, Vec<usize>) = (Vec::new(), Vec::new());
    for (i, v) in ex.found.iter().enumerate() {
        let at = leads.iter().position(|l| same(&ex.found[*l], v));
        let at = at.unwrap_or_else(|| {
            leads.push(i);
            leads.len() - 1
        });
        if v.breach.kind < ex.found[leads[at]].breach.kind {
            leads[at] = i;
        }
        of.push(at);
    }
    (leads, of)
}

fn chains(ex: &Explorer, findings: &[Finding], of: &[usize]) -> Vec<Chain> {
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
                let mut found = ex.found.iter();
                let at = found.position(|w| last_call(w) == Some(call.clone()));
                at.map(|at| of[at])
            })
            .collect();
        steps.dedup();
        let i = of[i];
        if steps.is_empty() || steps.contains(&i) {
            continue;
        }
        steps.push(i);
        if out.iter().any(|c: &Chain| c.steps == steps) {
            continue;
        }
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
    let (leads, of) = grouped(ex);
    let mut findings: Vec<Finding> = leads.iter().map(|l| finding(ex, &ex.found[*l])).collect();
    for (i, v) in ex
        .found
        .iter()
        .enumerate()
        .filter(|(i, _)| leads[of[*i]] != *i)
    {
        let (kind, f) = (v.breach.kind, finding(ex, v));
        let (title, shown) = (f.title, f.shown);
        findings[of[i]].also.push(Also { kind, title, shown });
    }
    let chains = chains(ex, &findings, &of);
    let (functions, cells) = models(ex);
    let ended = ex.facts.entries[..ex.own]
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
        not_run: crate::not_runnable(&ex.c.info.runtime).map(str::to_string),
        state: Vec::new(),
        findings,
        chains,
        functions,
        cells,
        slots_in_code: crate::model::slots_in_code(
            ex.c,
            &ex.entries[..ex.own]
                .iter()
                .map(|e| (e.function, e.name.clone()))
                .collect::<Vec<_>>(),
        ),
        assumed: ex.assumed.iter().cloned().chain(stand_ins(ex)).collect(),
        stats: Stats {
            functions: ex.own,
            functions_ended: ended,
            calls_made: ex.runs,
            states_kept: ex.states.len(),
            work,
            ms,
            reads: 0,
        },
    }
}

/* An asset with no code here keeps honest books, and the people in this world hold a
purse of it and let the contract draw on it. A finding whose run moved such an asset
rests on that, so the report says it. */
fn stand_ins(ex: &Explorer) -> Vec<String> {
    let mut assets: Vec<Addr> = Vec::new();
    for found in &ex.found {
        let moved = found.run.calls.iter().filter(|c| c.by == Answered::Books);
        assets.extend(moved.map(|c| c.to));
    }
    assets.sort();
    assets.dedup();
    let line = |asset: &Addr| {
        format!(
            "the asset at {} has no code here and is taken to keep honest books. The owner, the user and the account with no role each hold a purse of it and let the contract draw on it",
            asset.to_hex()
        )
    };
    assets.iter().map(line).collect()
}

#[must_use]
pub fn markdown(report: &Report) -> String {
    let mut out = format!(
        "# Audit of {}\n\nCode size: {} bytes\n\n",
        report.subject, report.code_size
    );
    if let Some(why) = &report.not_run {
        out.push_str(&format!("## Not analysed\n\n{why}\n\n"));
        return out;
    }
    let s = &report.stats;
    out.push_str(&format!(
        "{} of {} functions ended under some input, over {} calls and {} kept states, in {} ms.\n\n",
        s.functions_ended, s.functions, s.calls_made, s.states_kept, s.ms
    ));
    for line in &report.state {
        out.push_str(&format!("{line}\n\n"));
    }
    match report.findings.len() {
        0 => out.push_str("## Findings\n\nNo run showed an account with no role gaining, taking from another account, or taking the contract over. That is what was tried, not a proof that nothing can.\n\n"),
        n => out.push_str(&format!("## Findings ({n})\n\n")),
    }
    for (i, f) in report.findings.iter().enumerate() {
        out.push_str(&format!("### {}. {}\n\n", i + 1, f.title));
        out.push_str(&format!("- **Severity:** {:?}\n", f.severity));
        if let Some(source) = &f.source {
            out.push_str(&format!("- **Source:** {source}\n"));
        }
        out.push_str(&format!("- **Why:** {}\n", f.cause));
        out.push_str(&format!("- **Shown by a run:** {}\n", f.shown));
        if !f.rests_on.is_empty() {
            out.push_str(&format!("- **Rests on:** {}\n", f.rests_on.join("; ")));
        }
        for also in &f.also {
            out.push_str(&format!(
                "- **The same run also showed:** {}. {}\n",
                also.title, also.shown
            ));
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
    out.push_str("\n## What each function's code can do\n\nRead from the code with every helper it calls. This covers the functions no run got to the end of. It says what is possible, not what a run showed.\n\n| Function | Tests caller | Writes slots | Writes under keys | Calls out | Sends value | Runs other code | Destroys |\n|---|---|---|---|---|---|---|---|\n");
    for f in &report.functions {
        let c = &f.in_code;
        out.push_str(&format!(
            "| `{}` | {} | {} | {} | {} | {} | {} | {} |\n",
            f.name,
            mark(c.tests_caller),
            c.writes.join(", "),
            mark(c.writes_under_keys),
            mark(c.calls_out),
            mark(c.sends_value),
            mark(c.runs_other_code),
            mark(c.destroys)
        ));
    }
    let open: Vec<&FunctionModel> = report.functions.iter().filter(|f| unsettled(f)).collect();
    if !open.is_empty() {
        out.push_str("\n## Not settled by a run\n\nNo call by the account with no role got to the end of these functions, and their code has no test of the caller while it can change state or move value. These are not findings: no run showed anything. They are where a reader should look first.\n\n");
        for f in open {
            let stopped = f
                .stopped_by
                .as_deref()
                .unwrap_or("it ended only for other accounts");
            out.push_str(&format!("- `{}`: {stopped}\n", f.name));
        }
    }
    if !report.slots_in_code.is_empty() {
        out.push_str("\n## How the code uses each fixed slot\n\nRead from the code. A slot one function writes and another compares its caller with, calls, or sends as an amount is where state flows between them. Entries kept under keys are not listed.\n\n| Slot | Written by | Compared with the caller in | Called in | Sent as an amount in | Read by |\n|---|---|---|---|---|---|\n");
        for s in &report.slots_in_code {
            out.push_str(&format!(
                "| {} | {} | {} | {} | {} | {} |\n",
                s.slot,
                s.written_by.join(", "),
                s.compared_with_caller_in.join(", "),
                s.called_in.join(", "),
                s.sent_as_amount_in.join(", "),
                s.read_by.join(", ")
            ));
        }
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
        out.push_str("\n## Taken to hold\n\n");
        out.push_str(match report.state.is_empty() {
            true => "Runtime code does not say how the contract was set up. These were taken to hold because the owner's own calls are refused without them.\n\n",
            false => "The chain holds nothing for the three accounts that act here. These were added to what was read so that they can use the contract.\n\n",
        });
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
            not_run: None,
            state: Vec::new(),
            findings: Vec::new(),
            chains: Vec::new(),
            functions: Vec::new(),
            cells: Vec::new(),
            slots_in_code: Vec::new(),
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
        first.state.append(&mut next.state);
        first.stats.functions += next.stats.functions;
        first.stats.functions_ended += next.stats.functions_ended;
        first.stats.calls_made += next.stats.calls_made;
        first.stats.states_kept += next.stats.states_kept;
        first.stats.work += next.stats.work;
        first.stats.ms += next.stats.ms;
        first.stats.reads += next.stats.reads;
    }
    first
}
