use crate::abi::{self, SEL_BALANCE_OF, SEL_TRANSFER, SEL_TRANSFER_FROM};
use crate::analyze::{push, Confidence, Finding, Section, Severity};
use crate::decompile::{Contract, Function};
use crate::deploy;
use crate::emit::MappingLayout;
use crate::exec;
use crate::expr::{self, ExprId, Node};
use crate::function::FnKind;
use crate::interp::Outcome;
use crate::lift::Term;
use crate::origin::Loc;
use crate::path::{self, Explorer, Explorers, Limits, Path};
use crate::props::amount_sized;
use crate::solve::{self, Free, Inputs, Item, Settable, Step};
use crate::ssa;
use crate::u256::U256;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::rc::Rc;

const SEL_TOTAL: u32 = 0x1816_0ddd;

const LIMITS: Limits = Limits {
    paths: 24,
    runs: 96,
};
pub const WORK: u64 = 2 * exec::WORK_PER_SECOND;
const HOLDER: U256 = U256::from_u64(0xf00d_f00d_f00d_f00d);
const RECEIVER: U256 = U256::from_u64(0x7070_7070_7070_7070);
const AMOUNT: U256 = U256::from_u64(0x1001);
const ACTOR: U256 = U256::from_u64(0xac70_ac70_ac70_ac70);
const RECOVER: U256 = U256::ONE;
const OTHER_LIMITS: Limits = Limits { paths: 8, runs: 24 };
const OTHER_WORDS: usize = 6;
const MAX_OTHERS: usize = 40;

// The field offset is part of the place. A balance and a time kept in one record are
// two values, not one.
type Root = (U256, u64);
type Entry = (Root, Vec<U256>);

// Several mappings can be keyed by one account.
// The one in which the payer's entry falls is the ledger.
fn ledger(moves: &BTreeMap<Entry, (U256, U256)>, payer: U256) -> Option<Root> {
    let falls = moves
        .iter()
        .filter(|((_, keys), pair)| keys[..] == [payer] && amount_sized(fell(**pair)));
    let exact = falls.clone().find(|(_, pair)| fell(**pair) == AMOUNT);
    exact.or(falls.clone().next()).map(|((root, _), _)| *root)
}

struct Bench<'a> {
    c: &'a Contract,
    layout: MappingLayout,
    begin: HashMap<U256, U256>,
    explorers: Explorers,
}

impl<'a> Bench<'a> {
    fn function(&self, selector: u32) -> Option<&'a Function> {
        let wanted =
            |f: &&Function| f.kind == FnKind::External && exec::selector_of(f) == Some(selector);
        self.c.functions.iter().find(wanted)
    }

    fn explorer(&mut self, f: &Function) -> &Explorer {
        let code = self.c.code_of(f);
        self.explorers.of(code)
    }

    // The arguments stay as given. Storage is left free so the run can be given a balance.
    fn finished(&mut self, f: &Function, args: &[U256]) -> Option<Path> {
        let mut start = path::inputs_for(exec::selector_of(f), args.len());
        start.calldata = exec::calldata(exec::selector_of(f), args);
        start.storage = self.begin.clone();
        let free = Free {
            words: 0,
            value: false,
            storage: true,
            answers: false,
            settings: None,
            fixed: Vec::new(),
        };
        let found = self.explorer(f).explore(&start, &free, LIMITS);
        let moved = |p: &Path| p.succeeded() && p.run.storage != p.inputs.storage;
        found.into_iter().find(moved)
    }

    // A state in which the contract reports a balance for the holder. A token that
    // divides by its own supply reports nothing for anyone until the supply is set, and
    // only its constructor did that. The solver is asked for storage under which the
    // answer is not zero, whatever the formula is.
    fn holding(&mut self) -> Option<HashMap<U256, U256>> {
        let f = self.function(SEL_BALANCE_OF)?;
        let mut start = path::inputs_for(Some(SEL_BALANCE_OF), 1);
        start.calldata = exec::calldata(Some(SEL_BALANCE_OF), &[HOLDER]);
        start.storage = self.begin.clone();
        let free = Free {
            storage: true,
            ..Free::default()
        };
        let mut found = self.explorer(f).explore(&start, &free, LIMITS);
        // The longest way through the function is the one that works the balance out.
        // A shorter one returns a field kept for accounts set apart from the rest.
        found.sort_by_key(|p| std::cmp::Reverse(p.truth.len()));
        for asked in found {
            let Some(Term::Return {
                data: Some(words), ..
            }) = &asked.end
            else {
                continue;
            };
            let Some(word) = words.first() else { continue };
            // Enough for the holder to pass half on and keep half.
            let enough = AMOUNT.wrapping_add(AMOUNT);
            let mut items = asked.items.clone();
            items.push(Item::Check {
                cond: expr::op2(crate::opcode::LT, *word, expr::konst(enough)),
                holds: true,
                pc: usize::MAX,
            });
            let mut want = asked.truth.clone();
            want.push(false);
            let reports = |bench: &mut Bench, storage: &HashMap<U256, U256>| {
                let reported = bench.answer(SEL_BALANCE_OF, &[HOLDER], storage);
                reported.is_some_and(|v| v >= enough)
            };
            if reports(self, &asked.inputs.storage) {
                return Some(asked.inputs.storage);
            }
            let chosen = solve::solve(&items, &want, &asked.inputs, &free).map(|i| i.storage);
            if let Some(chosen) = chosen.filter(|chosen| reports(self, chosen)) {
                return Some(chosen);
            }
        }
        None
    }

    // The holder passes part of what it holds to the account that will make the calls.
    // The entries that run changes show where the ledger is, and it leaves both accounts
    // holding tokens by a real transfer, whatever units the ledger is kept in.
    fn sent(&mut self, f: &Function, held: &HashMap<U256, U256>) -> Option<Path> {
        let args = [ACTOR, AMOUNT];
        let mut start = path::inputs_for(exec::selector_of(f), args.len());
        start.calldata = exec::calldata(exec::selector_of(f), &args);
        start.caller = HOLDER;
        start.storage = held.clone();
        let free = Free {
            storage: true,
            ..Free::default()
        };
        let found = self.explorer(f).explore(&start, &free, LIMITS);
        let moved = |p: &Path| p.succeeded() && p.run.storage != p.inputs.storage;
        let holds = |p: &Path, bench: &mut Bench| {
            let now = bench.answer(SEL_BALANCE_OF, &[HOLDER], &p.run.storage);
            now.is_some_and(|v| !v.is_zero())
        };
        found.into_iter().find(|p| moved(p) && holds(p, self))
    }

    fn answer(
        &mut self,
        selector: u32,
        args: &[U256],
        storage: &HashMap<U256, U256>,
    ) -> Option<U256> {
        let f = self.function(selector)?;
        let mut inputs = path::inputs_for(Some(selector), args.len());
        inputs.calldata = exec::calldata(Some(selector), args);
        inputs.storage = storage.clone();
        let run = self.explorer(f).run(&inputs).run;
        match run.outcome {
            Outcome::Return(data) if data.len() >= 32 => Some(solve::word(&data, 0)),
            _ => None,
        }
    }

    fn keys(&self, key: ExprId, inputs: &Inputs) -> Option<Entry> {
        let slot = ssa::slot_path(key, self.layout)?;
        let mut out = Vec::new();
        let mut offset = 0u64;
        for step in &slot.steps {
            match step {
                ssa::Step::Key(k) => out.push(solve::value_of(*k, inputs)?),
                ssa::Step::Offset(by) => offset = offset.wrapping_add(*by),
                ssa::Step::Index(_) => {}
            }
        }
        Some(((slot.root, offset), out))
    }

    fn moves(&self, p: &Path) -> BTreeMap<Entry, (U256, U256)> {
        let mut out: BTreeMap<Entry, (U256, U256)> = BTreeMap::new();
        for step in solve::steps(&p.effects, &p.inputs) {
            let Step::Write {
                key, before, after, ..
            } = step
            else {
                continue;
            };
            if let Some(entry) = self.keys(key, &p.inputs).filter(|(_, k)| !k.is_empty()) {
                out.entry(entry).or_insert((before, after)).1 = after;
            }
        }
        out
    }

    fn before(&self, p: &Path, root: Root) -> Vec<(U256, U256)> {
        let mut out = Vec::new();
        let mut seen = HashSet::new();
        for step in solve::steps(&p.effects, &p.inputs) {
            let Step::Write {
                key, slot, before, ..
            } = step
            else {
                continue;
            };
            let ledger = self.keys(key, &p.inputs).is_some_and(|(r, _)| r == root);
            if ledger && seen.insert(slot) {
                out.push((slot, before));
            }
        }
        out
    }

    fn reads(&self, p: &Path) -> Vec<Entry> {
        let mut seen = HashSet::new();
        let mut stack: Vec<ExprId> = Vec::new();
        for item in &p.items {
            match item {
                Item::Check { cond, .. } => stack.push(*cond),
                Item::Store { key, val, .. } => stack.extend([*key, *val]),
            }
        }
        let mut out = Vec::new();
        while let Some(e) = stack.pop() {
            if !seen.insert(e) || seen.len() > 8_000 {
                continue;
            }
            if let Node::SLoad(key, false, _) = expr::node(e) {
                out.extend(self.keys(key, &p.inputs));
            }
            stack.extend(expr::children(e));
        }
        out
    }
}

fn fell(pair: (U256, U256)) -> U256 {
    pair.0.wrapping_sub(pair.1)
}

fn rose(pair: (U256, U256)) -> U256 {
    pair.1.wrapping_sub(pair.0)
}

struct Report<'o> {
    out: &'o mut Vec<Finding>,
    lines: Vec<String>,
}

impl Report<'_> {
    fn differs_at(
        &mut self,
        id: &str,
        title: &str,
        severity: Severity,
        f: &Function,
        run: &Path,
        text: String,
    ) {
        self.lines.push(text.clone());
        push(
            self.out,
            id,
            title,
            severity,
            Confidence::High,
            Some(f),
            None,
            format!(
                "{text} This is what it did when it was run with the attached input, from a state in which a second account holds tokens, with the settings the call needs chosen among the storage no function open to every caller writes.",
            ),
            Vec::new(),
            "Let a function change only the balance of its caller, of an account that approved the caller, or of the contract itself, and move what it reports for others only through a transfer.",
        );
        if let Some(last) = self.out.last_mut() {
            last.confirm(run);
        }
    }

    fn differs(
        &mut self,
        id: &str,
        title: &str,
        severity: Severity,
        f: &Function,
        run: &Path,
        text: String,
    ) {
        self.lines.push(text.clone());
        push(
            self.out,
            id,
            title,
            severity,
            Confidence::High,
            Some(f),
            None,
            format!(
                "{text} The function has the selector of the standard call, and this is what it did when it was run with the attached input, sent by an account holding no role, from storage chosen so that the call can end normally.",
            ),
            Vec::new(),
            "Treat this contract by what it does, not by the interface it shows. Callers that assume the standard behaviour need to handle the difference.",
        );
        if let Some(last) = self.out.last_mut() {
            last.confirm(run);
        }
    }
}

fn transfer(bench: &mut Bench, report: &mut Report) {
    let Some(f) = bench.function(SEL_TRANSFER) else {
        return;
    };
    let Some(p) = bench.finished(f, &[RECEIVER, AMOUNT]) else {
        report
            .lines
            .push("`transfer` could not be run to a normal end, so it was not measured.".into());
        return;
    };
    let caller = p.inputs.caller;
    let moves = bench.moves(&p);
    let Some(root) = ledger(&moves, caller) else {
        report.lines.push(
            "`transfer` ended normally without lowering an entry keyed by the sender, so it was not measured."
                .into(),
        );
        return;
    };
    let of = |who: U256| moves.get(&(root, vec![who])).copied();
    let taken = of(caller).map_or(U256::ZERO, fell);
    let given = of(RECEIVER).map_or(U256::ZERO, rose);
    let name = &f.name;
    if taken == AMOUNT && given == AMOUNT {
        report.lines.push(format!(
            "`{name}` lowers the sender's entry and raises the receiver's entry by the amount asked."
        ));
    } else if given > taken {
        report.differs(
            "transfer-creates-value",
            "A transfer raises the receiver by more than it lowers the sender",
            Severity::High,
            f,
            &p,
            format!(
                "`{name}` was asked to move {}. It lowered the sender's entry by {} and raised the receiver's by {}.",
                AMOUNT.to_hex(),
                taken.to_hex(),
                given.to_hex()
            ),
        );
    } else if given < AMOUNT || taken != AMOUNT {
        report.differs(
            "transfer-delivers-less",
            "A transfer does not move the amount asked",
            Severity::Low,
            f,
            &p,
            format!(
                "`{name}` was asked to move {}. It lowered the sender's entry by {} and raised the receiver's by {}.",
                AMOUNT.to_hex(),
                taken.to_hex(),
                given.to_hex()
            ),
        );
    }
    let third = moves.iter().find(|((_, keys), pair)| {
        let party = keys.iter().all(|k| *k == caller || *k == RECEIVER);
        !party && (amount_sized(rose(**pair)) || amount_sized(fell(**pair)))
    });
    if let Some(((_, keys), pair)) = third {
        report.differs(
            "transfer-touches-third-entry",
            "A transfer changes the entry of an account that is neither party",
            Severity::Medium,
            f,
            &p,
            format!(
                "`{name}` between two accounts also changed the entry keyed by {} from {} to {}.",
                keys.iter()
                    .map(|k| k.to_hex())
                    .collect::<Vec<_>>()
                    .join(", "),
                pair.0.to_hex(),
                pair.1.to_hex()
            ),
        );
    }
    measured(bench, report, f, &p, given);
}

fn measured(bench: &mut Bench, report: &mut Report, f: &Function, p: &Path, given: U256) {
    let (before, after) = (p.inputs.storage.clone(), p.run.storage.clone());
    let held =
        |bench: &mut Bench, s: &HashMap<U256, U256>| bench.answer(SEL_BALANCE_OF, &[RECEIVER], s);
    if let (Some(was), Some(now)) = (held(bench, &before), held(bench, &after)) {
        let shown = now.wrapping_sub(was);
        if shown == given {
            report.lines.push(
                "`balanceOf` reports the receiver's rise by the same amount the transfer wrote."
                    .into(),
            );
        } else {
            report.differs(
                "reported-balance-differs",
                "The reported balance does not move by what the transfer wrote",
                Severity::Medium,
                f,
                p,
                format!(
                    "After a transfer that raised the receiver's entry by {}, `balanceOf` for the receiver moved by {}.",
                    given.to_hex(),
                    shown.to_hex()
                ),
            );
        }
    }
    let supply = |bench: &mut Bench, s: &HashMap<U256, U256>| bench.answer(SEL_TOTAL, &[], s);
    if let (Some(was), Some(now)) = (supply(bench, &before), supply(bench, &after)) {
        if was == now {
            report
                .lines
                .push("`totalSupply` is the same before and after a transfer.".into());
        } else {
            report.differs(
                "transfer-changes-supply",
                "A transfer changes the total supply",
                Severity::Low,
                f,
                p,
                format!(
                    "`totalSupply` answered {} before the transfer and {} after it.",
                    was.to_hex(),
                    now.to_hex()
                ),
            );
        }
    }
}

fn transfer_from(bench: &mut Bench, report: &mut Report) {
    let Some(f) = bench.function(SEL_TRANSFER_FROM) else {
        return;
    };
    let Some(p) = bench.finished(f, &[HOLDER, RECEIVER, AMOUNT]) else {
        return;
    };
    let caller = p.inputs.caller;
    let moves = bench.moves(&p);
    let Some(root) = ledger(&moves, HOLDER) else {
        return;
    };
    let taken = moves
        .get(&(root, vec![HOLDER]))
        .copied()
        .map_or(U256::ZERO, fell);
    let name = &f.name;
    let both = |entry: &Entry| entry.1.contains(&HOLDER) && entry.1.contains(&caller);
    if !bench.reads(&p).iter().any(both) {
        report.differs(
            "transferfrom-ignores-allowance",
            "A third party moves another account's entry and no allowance is read",
            Severity::High,
            f,
            &p,
            format!(
                "`{name}` was called by one account to move {} out of another account's entry. It ended normally and lowered that entry, and on the way it read no stored value keyed by both the holder and the caller.",
                AMOUNT.to_hex()
            ),
        );
        return;
    }
    let allowance = moves.iter().find(|(entry, _)| both(entry));
    // All ones in any width of 64 bits or more is the usual mark for no limit.
    let unlimited = |v: U256| {
        let ones = (v & v.wrapping_add(U256::ONE)).is_zero();
        ones && v >= U256::from_u64(u64::MAX)
    };
    match allowance {
        Some((_, pair)) if fell(*pair) == taken => report.lines.push(format!(
            "`{name}` reads an allowance keyed by holder and caller and lowers it by the amount moved."
        )),
        Some((_, pair)) if !unlimited(pair.0) => report.differs(
            "allowance-not-spent",
            "An allowance is not lowered by the amount moved",
            Severity::High,
            f,
            &p,
            format!(
                "`{name}` lowered the holder's entry by {} and changed the allowance from {} to {}.",
                taken.to_hex(),
                pair.0.to_hex(),
                pair.1.to_hex()
            ),
        ),
        None => {
            let held = p.inputs.storage.iter().any(|(_, v)| unlimited(*v));
            if held {
                report.lines.push(format!(
                    "`{name}` reads an allowance keyed by holder and caller and leaves one set to no limit as it is."
                ));
            } else {
                report.differs(
                    "allowance-not-spent",
                    "An allowance is not lowered by the amount moved",
                    Severity::High,
                    f,
                    &p,
                    format!(
                        "`{name}` lowered the holder's entry by {} and read the allowance without writing it back.",
                        taken.to_hex()
                    ),
                );
            }
        }
        _ => {}
    }
}

// A token that keeps balances in scaled units lowers the sender's entry by the amount
// times a rate, which is no longer the size of an amount.
fn scaled_ledger(moves: &BTreeMap<Entry, (U256, U256)>, payer: U256) -> Option<Root> {
    let falls =
        |((_, keys), pair): &(&Entry, &(U256, U256))| keys[..] == [payer] && pair.1 < pair.0;
    ledger(moves, payer).or_else(|| moves.iter().find(falls).map(|((root, _), _)| *root))
}

fn names(calldata: &[u8], who: U256) -> bool {
    let bytes = who.to_be_bytes();
    let short = bytes.iter().position(|b| *b != 0).unwrap_or(31);
    calldata.windows(32 - short).any(|w| w == &bytes[short..])
}

// What a token holds for an account is that account's. Two things are measured for every
// function any account may call, from a state in which a second account holds tokens and
// the caller is a third. An entry of the ledger that belongs to neither the caller nor
// the contract must not fall. And what the contract reports for the second account must
// not move while that account's entry stays as it was. A pool that holds the token is
// such an account, and its reserves follow its balance.
fn others(bench: &mut Bench, report: &mut Report, open: &HashSet<Loc>) {
    let Some(transfer) = bench.function(SEL_TRANSFER) else {
        return;
    };
    let trace = crate::debug::on("EVMDEC_DEBUG_OTHERS");
    let said = |what: &str| {
        if trace {
            eprintln!("[others] {what}");
        }
    };
    let Some(held) = bench.holding() else {
        return said("no state in which the holder is reported to hold tokens");
    };
    let Some(given) = bench.sent(transfer, &held) else {
        return said("the holder could not pass tokens on");
    };
    let Some(root) = scaled_ledger(&bench.moves(&given), HOLDER) else {
        return said("no ledger entry fell when the holder passed tokens on");
    };
    // Any account may hold tokens, so an entry of the ledger is left for the search to
    // fill. Without that a function that takes from an account stops for lack of a balance
    // and is never seen to take.
    let settable = Rc::new(Settable {
        layout: bench.layout,
        open: open.clone(),
        held: HashSet::from([(root.0, 1, root.1)]),
    });
    let state = given.run.storage.clone();
    let writes = |f: &&Function| f.kind == FnKind::External && f.effects.writes_storage;
    let functions: Vec<&Function> = bench.c.functions.iter().filter(writes).collect();
    for f in functions.into_iter().take(MAX_OTHERS) {
        if exec::spent() {
            break;
        }
        let selector = exec::selector_of(f);
        let types: Vec<String> = f.params.iter().map(|p| p.ty.clone()).collect();
        let shaped = abi::layout(selector, &types);
        let flat = path::inputs_for(selector, OTHER_WORDS);
        let free = Free {
            words: OTHER_WORDS.max(shaped.calldata.len() / 32),
            value: true,
            storage: false,
            answers: false,
            settings: Some(settable.clone()),
            fixed: shaped.fixed.clone(),
        };
        let start = Inputs {
            calldata: path::fill_words(&shaped.calldata, &shaped.fixed, path::varied_word),
            caller: ACTOR,
            storage: state.clone(),
            returned: U256::ONE.to_be_bytes().to_vec(),
            ..flat
        };
        let found = bench.explorer(f).explore(&start, &free, OTHER_LIMITS);
        let acted = |q: &&Path| q.succeeded() && q.run.storage != q.inputs.storage;
        said(&format!(
            "{}: {} runs changed storage",
            f.name,
            found.iter().filter(acted).count()
        ));
        for q in found {
            // A signed message is the holder's own permission, and no run here signs one.
            let signed = q.run.calls.iter().any(|c| c.addr == RECOVER);
            if !q.succeeded() || signed || q.run.storage == q.inputs.storage {
                continue;
            }
            // The state here stands for a contract in use. A call that works once and
            // never again is its set-up, which a contract in use has behind it. The
            // balances go back to what they were first, so that a call which spent one
            // is not taken for set-up.
            let mut again = q.inputs.clone();
            again.storage = q.run.storage.clone();
            again.storage.extend(bench.before(&q, root));
            if !bench.explorer(f).run_only(&again).succeeded() {
                continue;
            }
            if other_entry_falls(bench, report, f, &q, root)
                || report_moves(bench, report, f, &q, root)
            {
                break;
            }
        }
    }
}

fn other_entry_falls(
    bench: &Bench,
    report: &mut Report,
    f: &Function,
    q: &Path,
    root: Root,
) -> bool {
    let moves = bench.moves(q);
    let theirs = |keys: &[U256]| {
        let who = keys[0];
        keys.len() == 1 && who != q.inputs.caller && who != q.inputs.address
    };
    let fallen = moves
        .iter()
        .find(|((r, keys), pair)| *r == root && theirs(keys) && pair.1 < pair.0);
    let Some(((_, keys), pair)) = fallen else {
        return false;
    };
    let named = match names(&q.inputs.calldata, keys[0]) {
        true => "names that account, which gave the caller no allowance",
        false => "does not name that account",
    };
    report.differs_at(
        "call-lowers-another-accounts-balance",
        "A call lowers the balance of an account that took no part in it",
        Severity::High,
        f,
        q,
        format!(
            "`{}` was called by an account holding no role and lowered the balance entry of {} from {} to {}. The call data {named}.",
            f.name,
            keys[0].to_hex(),
            pair.0.to_hex(),
            pair.1.to_hex(),
        ),
    );
    true
}

fn report_moves(
    bench: &mut Bench,
    report: &mut Report,
    f: &Function,
    q: &Path,
    root: Root,
) -> bool {
    let entry = (root, vec![HOLDER]);
    let touched = bench
        .moves(q)
        .get(&entry)
        .is_some_and(|pair| pair.0 != pair.1);
    if touched || names(&q.inputs.calldata, HOLDER) {
        return false;
    }
    let before = bench.answer(SEL_BALANCE_OF, &[HOLDER], &q.inputs.storage);
    let after = bench.answer(SEL_BALANCE_OF, &[HOLDER], &q.run.storage);
    let (Some(before), Some(after)) = (before, after) else {
        return false;
    };
    if before == after || before.is_zero() {
        return false;
    }
    let (severity, way) = match after < before {
        true => (Severity::High, "fell"),
        false => (Severity::Medium, "rose"),
    };
    report.differs_at(
        "reported-balance-moved-by-another-account",
        "A call changes what the contract reports another account holds",
        severity,
        f,
        q,
        format!(
            "`{}` was called by an account holding no role. An account it does not name, whose balance entry it did not write, was reported to hold {} before the call and {} after it, so its balance {way} without a transfer. A pool that holds this token keeps reserves that no longer match what it holds, and whoever settles the difference takes it.",
            f.name,
            before.to_hex(),
            after.to_hex(),
        ),
    );
    true
}

pub fn findings(c: &Contract, open: &HashSet<Loc>, out: &mut Vec<Finding>) -> Option<Section> {
    if std::env::var("EVMDEC_NO_CONFIRM").is_ok() || c.info.runtime.is_empty() {
        return None;
    }
    let mut bench = Bench {
        c,
        layout: c.compiler.layout,
        begin: deploy::storage(c),
        explorers: Explorers::default(),
    };
    bench.function(SEL_BALANCE_OF)?;
    let mut report = Report {
        out,
        lines: Vec::new(),
    };
    transfer(&mut bench, &mut report);
    transfer_from(&mut bench, &mut report);
    others(&mut bench, &mut report, open);
    (!report.lines.is_empty()).then_some(Section {
        title: "Standard interface, as measured".to_string(),
        lines: report.lines,
    })
}
