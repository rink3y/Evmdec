use crate::analyze::{push, Confidence, Finding, Section, Severity};
use crate::decompile::{Contract, Function};
use crate::deploy;
use crate::emit::MappingLayout;
use crate::exec;
use crate::expr::{self, ExprId, Node};
use crate::function::FnKind;
use crate::interp::Outcome;
use crate::path::{self, Explorer, Limits, Path};
use crate::solve::{self, Free, Inputs, Item, Step};
use crate::ssa;
use crate::u256::U256;
use std::collections::{BTreeMap, HashMap, HashSet};

const SEL_TRANSFER: u32 = 0xa905_9cbb;
const SEL_TRANSFER_FROM: u32 = 0x23b8_72dd;
const SEL_BALANCE_OF: u32 = 0x70a0_8231;
const SEL_TOTAL: u32 = 0x1816_0ddd;

const LIMITS: Limits = Limits {
    paths: 24,
    runs: 96,
};
const HOLDER: U256 = U256::from_u64(0xf00d_f00d_f00d_f00d);
const RECEIVER: U256 = U256::from_u64(0x7070_7070_7070_7070);
const AMOUNT: U256 = U256::from_u64(0x1001);

type Entry = (U256, Vec<U256>);

// Several mappings can be keyed by one account.
// The one in which the payer's entry falls is the ledger.
fn ledger(moves: &BTreeMap<Entry, (U256, U256)>, payer: U256) -> Option<U256> {
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
    explorers: HashMap<*const u8, Explorer>,
}

impl<'a> Bench<'a> {
    fn function(&self, selector: u32) -> Option<&'a Function> {
        let wanted =
            |f: &&Function| f.kind == FnKind::External && exec::selector_of(f) == Some(selector);
        self.c.functions.iter().find(wanted)
    }

    fn explorer(&mut self, f: &Function) -> &Explorer {
        let code = self.c.code_of(f);
        self.explorers
            .entry(code.as_ptr())
            .or_insert_with(|| Explorer::new(code))
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
            fixed: Vec::new(),
        };
        let found = self.explorer(f).explore(&start, &free, LIMITS);
        let moved = |p: &Path| p.succeeded() && p.run.storage != p.inputs.storage;
        found.into_iter().find(moved)
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
        for step in &slot.steps {
            if let ssa::Step::Key(k) = step {
                out.push(solve::value_of(*k, inputs)?);
            }
        }
        Some((slot.root, out))
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

fn amount_sized(delta: U256) -> bool {
    let small = U256::from_u64(0xff);
    delta > small && U256::ZERO.wrapping_sub(delta) > small
}

struct Report<'o> {
    out: &'o mut Vec<Finding>,
    lines: Vec<String>,
}

impl Report<'_> {
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

pub fn findings(c: &Contract, out: &mut Vec<Finding>) -> Option<Section> {
    if std::env::var("EVMDEC_NO_CONFIRM").is_ok() || c.info.runtime.is_empty() {
        return None;
    }
    let mut bench = Bench {
        c,
        layout: c.compiler.layout,
        begin: deploy::storage(c),
        explorers: HashMap::new(),
    };
    bench.function(SEL_BALANCE_OF)?;
    let mut report = Report {
        out,
        lines: Vec::new(),
    };
    transfer(&mut bench, &mut report);
    transfer_from(&mut bench, &mut report);
    (!report.lines.is_empty()).then_some(Section {
        title: "Standard interface, as measured".to_string(),
        lines: report.lines,
    })
}
