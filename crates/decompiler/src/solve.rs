use crate::emit::MappingLayout;
use crate::expr::{self, ExprId, Node};
use crate::keccak;
use crate::lift::Stmt;
use crate::opcode as op;
use crate::origin::{self, Loc};
use crate::u256::U256;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Inputs {
    pub calldata: Vec<u8>,
    pub caller: U256,
    pub address: U256,
    pub callvalue: U256,
    pub timestamp: U256,
    pub number: U256,
    pub storage: HashMap<U256, U256>,
    pub returned: Vec<u8>,
    pub replies: Vec<(u32, Vec<u8>)>,
    pub answers: Vec<(usize, Vec<u8>)>,
    pub given: Vec<Given>,
    pub balance: U256,
    pub signed: Option<(Vec<u8>, U256)>,
    pub failing: Option<usize>,
    pub spends_balance: bool,
    pub moving: Vec<crate::interp::MovingBalance>,
}

// What one call of a run was answered. `size` is the name the code's read of the answer's
// length carries. `open` says nothing chose the answer, so a search may.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Given {
    pub seq: u32,
    pub size: u32,
    pub open: bool,
    pub data: Vec<u8>,
}

#[derive(Clone, Debug)]
pub enum Item {
    Store {
        key: ExprId,
        val: ExprId,
        gen: u32,
    },
    Check {
        cond: ExprId,
        holds: bool,
        pc: usize,
    },
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Free {
    pub words: usize,
    pub value: bool,
    pub storage: bool,
    pub answers: bool,
    pub settings: Option<Rc<Settable>>,
    pub fixed: Vec<usize>,
}

// Storage a search may choose without owning the contract: every place except those a
// function open to any caller writes. What only a constructor or an authorised account
// sets is how the contract was configured, and that is not in the runtime code.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Settable {
    pub layout: MappingLayout,
    pub open: HashSet<Loc>,
    pub held: HashSet<Loc>,
}

// A contract address a setting is given when the code asks for one that has code.
pub const SOME_CONTRACT: U256 = U256::from_u64(0x00c0_11ab_0000_0001);

fn names_someone(e: ExprId) -> bool {
    expr::contains(e, &|n| {
        let who = matches!(n, Node::Env(op::CALLER | op::ORIGIN, _));
        who || matches!(n, Node::ReturnData(..) | Node::CallResult(_))
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Place {
    Word(usize),
    Value,
    Slot(U256),
    Answer(usize, usize),
    AnswerSize(usize),
}

const MAX_ANSWER: usize = 2048;

const ROUNDS: usize = 96;
const LOOKAHEAD: usize = 8;

pub fn word(calldata: &[u8], offset: usize) -> U256 {
    let mut bytes = [0u8; 32];
    for (i, b) in bytes.iter_mut().enumerate() {
        let at = offset.checked_add(i);
        *b = at.and_then(|at| calldata.get(at)).copied().unwrap_or(0);
    }
    U256::from_be_bytes(&bytes)
}

fn set_word(calldata: &mut Vec<u8>, index: usize, value: U256) {
    let at = 4 + 32 * index;
    if calldata.len() < at + 32 {
        calldata.resize(at + 32, 0);
    }
    calldata[at..at + 32].copy_from_slice(&value.to_be_bytes());
}

struct Eval<'a> {
    inputs: &'a Inputs,
    writes: Vec<(u32, U256, U256, ExprId)>,
    memo: HashMap<ExprId, Option<U256>>,
}

// Valuing one node costs about as much as a dozen steps of a run. Counting it keeps a
// search with long conditions inside the same limit as the runs.
const NODE_COST: u64 = 12;

impl Drop for Eval<'_> {
    fn drop(&mut self) {
        crate::exec::spend(self.memo.len() as u64 * NODE_COST);
    }
}

impl Eval<'_> {
    fn stored(&self, key: U256, gen: u32) -> U256 {
        self.writes
            .iter()
            .rev()
            .find(|(g, k, ..)| *g < gen && *k == key)
            .map(|(_, _, v, _)| *v)
            .or_else(|| self.inputs.storage.get(&key).copied())
            .unwrap_or(U256::ZERO)
    }

    fn value(&mut self, e: ExprId) -> Option<U256> {
        if let Some(known) = self.memo.get(&e) {
            return *known;
        }
        let out = match expr::node(e) {
            Node::Const(c) => Some(c),
            Node::Env(o, stamp) => match o {
                op::CALLER | op::ORIGIN => Some(self.inputs.caller),
                op::ADDRESS => Some(self.inputs.address),
                op::CALLVALUE => Some(self.inputs.callvalue),
                op::CALLDATASIZE => Some(U256::from(self.inputs.calldata.len())),
                op::TIMESTAMP => Some(self.inputs.timestamp),
                op::NUMBER => Some(self.inputs.number),
                op::RETURNDATASIZE => {
                    let given = self.inputs.given.iter().find(|g| g.size == stamp);
                    let data = given.map_or(&self.inputs.returned, |g| &g.data);
                    Some(U256::from(data.len()))
                }
                op::SELFBALANCE => Some(self.inputs.balance),
                _ => crate::interp::fixed_in_a_run(o),
            },
            Node::CallDataLoad(off) | Node::CopiedWord(op::CALLDATACOPY, off, _) => self
                .value(off)
                .and_then(|o| o.as_usize())
                .map(|o| word(&self.inputs.calldata, o)),
            Node::SLoad(key, false, gen) => self.value(key).map(|k| self.stored(k, gen)),
            Node::CallResult(_) => Some(U256::ONE),
            Node::ReturnData(seq, off) => {
                let inputs = self.inputs;
                let given = inputs.given.iter().find(|g| g.seq == seq);
                let data = given.map_or(&inputs.returned, |g| &g.data);
                let at = self.value(off).and_then(|o| o.as_usize());
                at.filter(|o| o.checked_add(32).is_some_and(|end| end <= data.len()))
                    .map(|o| word(data, o))
            }
            Node::Keccak(words, tail) => {
                let mut bytes = Vec::with_capacity(32 * words.len());
                let last = words.len().saturating_sub(1);
                let mut known = true;
                for (i, w) in words.iter().enumerate() {
                    match self.value(*w) {
                        Some(v) if tail > 0 && i == last => {
                            bytes.extend_from_slice(&v.to_be_bytes()[32 - tail as usize..]);
                        }
                        Some(v) => bytes.extend_from_slice(&v.to_be_bytes()),
                        None => known = false,
                    }
                }
                known.then(|| U256::from_be_bytes(&keccak::keccak256(&bytes)))
            }
            Node::Op(op::EXTCODESIZE, v) => {
                let asked = self.value(v[0]).filter(|a| *a != self.inputs.address);
                asked.map(crate::interp::code_size_in_a_run)
            }
            Node::Op(o, v) => {
                let args: Option<Vec<ExprId>> =
                    v.iter().map(|x| self.value(*x).map(expr::konst)).collect();
                args.and_then(|a| match a[..] {
                    [x] => expr::as_const(expr::op1(o, x)),
                    [x, y] => expr::as_const(expr::op2(o, x, y)),
                    [x, y, z] => expr::as_const(expr::op3(o, x, y, z)),
                    _ => None,
                })
            }
            _ => None,
        };
        self.memo.insert(e, out);
        out
    }
}

pub fn value_of(e: ExprId, inputs: &Inputs) -> Option<U256> {
    let mut eval = Eval {
        inputs,
        writes: Vec::new(),
        memo: HashMap::new(),
    };
    eval.value(e)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Step {
    Write {
        key: ExprId,
        slot: U256,
        before: U256,
        after: U256,
    },
    Call {
        kind: u8,
        to: Option<U256>,
    },
    Unknown,
}

pub fn steps(effects: &[Stmt], inputs: &Inputs) -> Vec<Step> {
    let mut eval = Eval {
        inputs,
        writes: Vec::new(),
        memo: HashMap::new(),
    };
    let mut out = Vec::new();
    for st in effects {
        match st {
            Stmt::SStore {
                key,
                val,
                transient: false,
                gen,
            } => match (eval.value(*key), eval.value(*val)) {
                (Some(slot), Some(after)) => {
                    let before = eval.stored(slot, *gen);
                    eval.writes.push((*gen, slot, after, *val));
                    out.push(Step::Write {
                        key: *key,
                        slot,
                        before,
                        after,
                    });
                }
                _ => out.push(Step::Unknown),
            },
            Stmt::Call { kind, addr, .. } => out.push(Step::Call {
                kind: *kind,
                to: eval.value(*addr),
            }),
            _ => {}
        }
    }
    out
}

pub fn replay(items: &[Item], inputs: &Inputs) -> Vec<Option<bool>> {
    let mut eval = Eval {
        inputs,
        writes: Vec::new(),
        memo: HashMap::new(),
    };
    let mut truth = Vec::new();
    for item in items {
        match item {
            Item::Store { key, val, gen } => {
                if let (Some(k), Some(v)) = (eval.value(*key), eval.value(*val)) {
                    eval.writes.push((*gen, k, v, *val));
                }
            }
            Item::Check { cond, .. } => truth.push(eval.value(*cond).map(|v| !v.is_zero())),
        }
    }
    truth
}

struct Search<'a> {
    eval: Eval<'a>,
    free: &'a Free,
    out: Vec<(Place, U256)>,
    steps: usize,
    matching: u32,
}

// Forcing a value follows both sides of every operation, so one condition can cost two to
// the power of its depth. The cap ends such a search, and its steps count as work.
const MAX_SEARCH_STEPS: usize = 50_000;

impl Drop for Search<'_> {
    fn drop(&mut self) {
        crate::exec::spend(self.steps as u64 * NODE_COST);
    }
}

impl Search<'_> {
    fn place(&mut self, e: ExprId) -> Option<Place> {
        match expr::node(e) {
            Node::CallDataLoad(off) | Node::CopiedWord(op::CALLDATACOPY, off, _) => {
                let at = self.eval.value(off)?.as_usize()?;
                let index = at.checked_sub(4)? / 32;
                let open = index < self.free.words && !self.free.fixed.contains(&index);
                (at >= 4 && (at - 4) % 32 == 0 && open).then_some(Place::Word(index))
            }
            Node::Env(op::CALLVALUE, _) if self.free.value => Some(Place::Value),
            Node::ReturnData(seq, off) if self.free.answers => {
                let given = &self.eval.inputs.given;
                let call = given.iter().position(|g| g.seq == seq && g.open)?;
                let at = self.eval.value(off)?.as_usize()?;
                (at < MAX_ANSWER).then_some(Place::Answer(call, at))
            }
            Node::Env(op::RETURNDATASIZE, stamp) if self.free.answers => {
                let given = &self.eval.inputs.given;
                let call = given.iter().position(|g| g.size == stamp && g.open)?;
                Some(Place::AnswerSize(call))
            }
            Node::SLoad(key, false, gen) if self.free.storage || self.settable(key) => {
                let k = self.eval.value(key)?;
                let untouched = !self
                    .eval
                    .writes
                    .iter()
                    .any(|(g, w, ..)| *g < gen && *w == k);
                untouched.then_some(Place::Slot(k))
            }
            _ => None,
        }
    }

    fn settable(&self, key: ExprId) -> bool {
        let Some(settings) = &self.free.settings else {
            return false;
        };
        let by_caller =
            expr::contains(key, &|n| matches!(n, Node::Env(op::CALLER | op::ORIGIN, _)));
        let Some(loc) = origin::loc_of(key, settings.layout) else {
            return false;
        };
        // An entry keyed by the caller is usually a role the caller holds. In a ledger of
        // balances it is what the caller owns, and any account may own some.
        settings.held.contains(&loc) || (!by_caller && !settings.open.contains(&loc))
    }

    // A setting made equal to the caller, or to what a call answered, would hand out the
    // role the comparison protects. The owner slot then holds whoever asks, and a
    // recovered signer matches whatever was signed.
    fn force_against(&mut self, e: ExprId, target: U256, other: ExprId, depth: u32) {
        let named = self.free.settings.is_some() && names_someone(other);
        self.matching += u32::from(named);
        self.force(e, target, depth);
        self.matching -= u32::from(named);
    }

    fn force(&mut self, e: ExprId, target: U256, depth: u32) {
        self.steps += 1;
        if depth > 24 || self.steps > MAX_SEARCH_STEPS {
            return;
        }
        if let Some(place) = self.place(e) {
            let role = matches!(place, Place::Slot(_)) && !self.free.storage && self.matching > 0;
            if !role {
                self.out.push((place, target));
            }
            return;
        }
        let d = depth + 1;
        if let Node::SLoad(key, false, gen) = expr::node(e) {
            let written = self.eval.value(key).and_then(|k| {
                let hit = self.eval.writes.iter().rev();
                hit.clone()
                    .find(|(g, w, ..)| *g < gen && *w == k)
                    .map(|w| w.3)
            });
            if let Some(source) = written {
                self.force(source, target, d);
            }
            return;
        }
        let Node::Op(o, v) = expr::node(e) else {
            return;
        };
        let val = |s: &mut Self, x: ExprId| s.eval.value(x);
        match (o, &v[..]) {
            (op::ADD, [a, b]) => {
                if let Some(y) = val(self, *b) {
                    self.force(*a, target.wrapping_sub(y), d);
                }
                if let Some(x) = val(self, *a) {
                    self.force(*b, target.wrapping_sub(x), d);
                }
            }
            (op::SUB, [a, b]) => {
                if let Some(y) = val(self, *b) {
                    self.force_against(*a, target.wrapping_add(y), *b, d);
                }
                if let Some(x) = val(self, *a) {
                    self.force_against(*b, x.wrapping_sub(target), *a, d);
                }
            }
            (op::EXTCODESIZE, [a]) | (op::EXTCODESIZE, [a, _]) => {
                let holder = if target.is_zero() {
                    U256::ZERO
                } else {
                    SOME_CONTRACT
                };
                self.force(*a, holder, d);
            }
            (op::MUL, [a, b]) => {
                for (x, other) in [(*a, *b), (*b, *a)] {
                    let Some(k) = val(self, other).filter(|k| !k.is_zero()) else {
                        continue;
                    };
                    let (q, r) = target.div_rem(k);
                    if r.is_zero() {
                        self.force(x, q, d);
                        // An even factor loses the top bits, so a second value gives the same product.
                        let lost = k.trailing_zeros();
                        if lost > 0 {
                            self.force(x, q.wrapping_add(U256::ONE << (256 - lost)), d);
                        }
                    }
                }
            }
            (op::DIV, [a, b]) => {
                if let (Some(top), false) = (val(self, *a), target.is_zero()) {
                    self.force(*b, top.div_rem(target).0, d);
                }
                if let Some(k) = val(self, *b).filter(|k| !k.is_zero()) {
                    let wide = target.wrapping_mul(k);
                    if wide.div_rem(k).0 == target {
                        self.force(*a, wide, d);
                    }
                }
            }
            (op::AND, [a, b]) => {
                for (x, other) in [(*a, *b), (*b, *a)] {
                    let Some(mask) = expr::as_const(other) else {
                        continue;
                    };
                    if (target & !mask).is_zero() {
                        let keep = val(self, x).unwrap_or(U256::ZERO) & !mask;
                        self.force(x, target | keep, d);
                    }
                }
            }
            (op::XOR, [a, b]) => {
                if let Some(y) = val(self, *b) {
                    self.force_against(*a, target ^ y, *b, d);
                }
                if let Some(x) = val(self, *a) {
                    self.force_against(*b, target ^ x, *a, d);
                }
            }
            (op::NOT, [a]) => self.force(*a, !target, d),
            (op::SHL, [s, a]) => {
                if let Some(n) = val(self, *s).filter(|n| n.fits_u64() && n.low_u64() < 256) {
                    let n = n.low_u64() as u32;
                    if (target >> n) << n == target {
                        self.force(*a, target >> n, d);
                    }
                }
            }
            (op::SHR, [s, a]) => {
                if let Some(n) = val(self, *s).filter(|n| n.fits_u64() && n.low_u64() < 256) {
                    let n = n.low_u64() as u32;
                    if (target << n) >> n == target {
                        self.force(*a, target << n, d);
                    }
                }
            }
            (op::ISZERO | op::EQ | op::LT | op::GT | op::SLT | op::SGT, _) => {
                self.truth(e, !target.is_zero(), d);
            }
            _ => {}
        }
    }

    fn truth(&mut self, e: ExprId, want: bool, depth: u32) {
        if depth > 24 {
            return;
        }
        let d = depth + 1;
        let Node::Op(o, v) = expr::node(e) else {
            self.force(e, U256::from(want), d);
            return;
        };
        let val = |s: &mut Self, x: ExprId| s.eval.value(x);
        let one = U256::ONE;
        match (o, &v[..]) {
            (op::ISZERO, [a]) => self.truth(*a, !want, d),
            (op::EQ, [a, b]) => {
                let (x, y) = (val(self, *a), val(self, *b));
                let shift = if want { U256::ZERO } else { one };
                if let Some(y) = y {
                    self.force_against(*a, y.wrapping_add(shift), *b, d);
                }
                if let Some(x) = x {
                    self.force_against(*b, x.wrapping_add(shift), *a, d);
                }
            }
            (op::LT | op::SLT, [a, b]) => self.order(*a, *b, want, d),
            (op::GT | op::SGT, [a, b]) => self.order(*b, *a, want, d),
            (op::AND, [a, b]) if expr::is_boolean(*a) && expr::is_boolean(*b) => {
                self.truth(*a, want, d);
                self.truth(*b, want, d);
            }
            (op::OR, [a, b]) => {
                self.truth(*a, want, d);
                self.truth(*b, want, d);
            }
            _ => {
                if want {
                    for target in [one, U256::MAX] {
                        self.force(e, target, d);
                    }
                } else {
                    self.force(e, U256::ZERO, d);
                }
            }
        }
    }

    fn order(&mut self, low: ExprId, high: ExprId, want: bool, depth: u32) {
        let (x, y) = (self.eval.value(low), self.eval.value(high));
        let one = U256::ONE;
        if want {
            // The exact neighbour is often not reachable through a quotient or a product.
            // Half way is a second target with more preimages.
            if let Some(y) = y.filter(|y| !y.is_zero()) {
                self.force(low, y.wrapping_sub(one), depth);
                self.force(low, U256::ZERO, depth);
                self.force(low, y >> 1, depth);
            }
            if let Some(x) = x.filter(|x| *x != U256::MAX) {
                self.force(high, x.wrapping_add(one), depth);
                self.force(high, U256::MAX, depth);
                self.force(high, (x >> 1) | (one << 255), depth);
            }
        } else {
            if let Some(y) = y {
                self.force(low, y, depth);
                self.force(low, U256::MAX, depth);
            }
            if let Some(x) = x {
                self.force(high, x, depth);
                self.force(high, U256::ZERO, depth);
            }
        }
    }
}

impl Search<'_> {
    // A check on two keyed entries can turn on whether the keys are equal.
    // No inversion finds that, so each free word inside a key is also tried at its own value.
    fn distinct_keys(&mut self, cond: ExprId) {
        let mut seen = HashSet::new();
        let mut stack = vec![(cond, false)];
        while let Some((e, in_key)) = stack.pop() {
            if !seen.insert((e, in_key)) || seen.len() > 2_000 || self.out.len() > 64 {
                continue;
            }
            if let (true, Some(Place::Word(index))) = (in_key, self.place(e)) {
                self.out.push((
                    Place::Word(index),
                    U256::from_u64(0x1001 + 2 * index as u64),
                ));
                continue;
            }
            let keyed = in_key || matches!(expr::node(e), Node::SLoad(..));
            stack.extend(expr::children(e).into_iter().map(|c| (c, keyed)));
        }
    }
}

fn proposals(
    items: &[Item],
    inputs: &Inputs,
    free: &Free,
    at: usize,
    want: bool,
) -> Vec<(Place, U256)> {
    let mut search = Search {
        eval: Eval {
            inputs,
            writes: Vec::new(),
            memo: HashMap::new(),
        },
        free,
        out: Vec::new(),
        steps: 0,
        matching: 0,
    };
    let mut seen = 0;
    for item in items {
        match item {
            Item::Store { key, val, gen } => {
                if let (Some(k), Some(v)) = (search.eval.value(*key), search.eval.value(*val)) {
                    search.eval.writes.push((*gen, k, v, *val));
                }
            }
            Item::Check { cond, .. } => {
                if seen == at {
                    search.truth(*cond, want, 0);
                    search.distinct_keys(*cond);
                    break;
                }
                seen += 1;
            }
        }
    }
    std::mem::take(&mut search.out)
}

fn apply(inputs: &Inputs, place: Place, value: U256) -> Inputs {
    let mut next = inputs.clone();
    match place {
        Place::Word(index) => set_word(&mut next.calldata, index, value),
        Place::Value => next.callvalue = value,
        Place::Slot(key) => {
            next.storage.insert(key, value);
        }
        Place::Answer(call, at) => {
            let mut data = next.given[call].data.clone();
            if data.len() < at + 32 {
                data.resize(at + 32, 0);
            }
            data[at..at + 32].copy_from_slice(&value.to_be_bytes());
            answer_with(&mut next, call, data);
        }
        Place::AnswerSize(call) => {
            if let Some(size) = value.as_usize().filter(|size| *size <= MAX_ANSWER) {
                let mut data = next.given[call].data.clone();
                data.resize(size, 0);
                answer_with(&mut next, call, data);
            }
        }
    }
    next
}

// The record of what was answered is what the conditions are valued against. It has to
// change with the answer, or the next round would judge the old one.
fn answer_with(inputs: &mut Inputs, call: usize, data: Vec<u8>) {
    inputs.given[call].data = data.clone();
    inputs.answers.retain(|(at, _)| *at != call);
    inputs.answers.push((call, data));
}

fn agreed(truth: &[Option<bool>], want: &[bool], observed: &[bool]) -> usize {
    truth
        .iter()
        .zip(want)
        .zip(observed)
        .take_while(|((t, w), seen)| t.unwrap_or(**seen) == **w)
        .count()
}

// A generator, not a decision procedure. A caller must run what it returns.
pub fn solve(items: &[Item], want: &[bool], start: &Inputs, free: &Free) -> Option<Inputs> {
    let observed: Vec<bool> = items
        .iter()
        .filter_map(|i| match i {
            Item::Check { holds, .. } => Some(*holds),
            Item::Store { .. } => None,
        })
        .collect();
    let mut current = start.clone();
    let mut reached = agreed(&replay(items, &current), want, &observed);
    for _ in 0..ROUNDS {
        if reached >= want.len() {
            return Some(current);
        }
        if crate::exec::spent() {
            return None;
        }
        let mut better: Option<(usize, Inputs)> = None;
        let offer = |better: &mut Option<(usize, Inputs)>, next: Inputs| {
            let score = agreed(&replay(items, &next), want, &observed);
            if score > reached && better.as_ref().is_none_or(|(s, _)| score > *s) {
                *better = Some((score, next));
            }
        };
        let firsts = proposals(items, &current, free, reached, want[reached]);
        for (place, value) in &firsts {
            offer(&mut better, apply(&current, *place, *value));
        }
        // A condition over two words can need both moved before it agrees. And a value
        // that satisfies the wanted check can break an earlier one that bounds it, as a
        // balance does when it passes the total. The earlier check is then asked for its
        // own change.
        if better.is_none() {
            for (place, value) in firsts.iter().take(LOOKAHEAD) {
                let mid = apply(&current, *place, *value);
                let kept = agreed(&replay(items, &mid), want, &observed);
                let at = kept.min(reached);
                for (place, value) in proposals(items, &mid, free, at, want[at]) {
                    offer(&mut better, apply(&mid, place, value));
                }
            }
        }
        let (score, next) = better?;
        reached = score;
        current = next;
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn inputs() -> Inputs {
        Inputs {
            calldata: vec![0xaa, 0xaa, 0xaa, 0xaa],
            caller: U256::from_u64(0xc0),
            address: U256::from_u64(0xad),
            callvalue: U256::ZERO,
            timestamp: U256::from_u64(1_700_000_000),
            number: U256::from_u64(18_000_000),
            storage: HashMap::new(),
            returned: Vec::new(),
            replies: Vec::new(),
            answers: Vec::new(),
            given: Vec::new(),
            balance: U256::ZERO,
            signed: None,
            failing: None,
            spends_balance: false,
            moving: Vec::new(),
        }
    }

    fn arg(index: u64) -> ExprId {
        expr::calldataload(expr::konst_u64(4 + 32 * index))
    }

    fn check(cond: ExprId) -> Item {
        Item::Check {
            cond,
            holds: false,
            pc: 0,
        }
    }

    fn words() -> Free {
        Free {
            words: 4,
            ..Free::default()
        }
    }

    #[test]
    fn an_equality_with_a_sum_is_solved_by_inverting_the_sum() {
        let sum = expr::op2(op::ADD, arg(0), expr::konst_u64(7));
        let items = [check(expr::op2(op::EQ, sum, expr::konst_u64(100)))];
        let found = solve(&items, &[true], &inputs(), &words()).expect("solvable");
        assert_eq!(word(&found.calldata, 4), U256::from_u64(93));
    }

    #[test]
    fn two_checks_on_two_words_are_met_together() {
        let below = expr::op2(op::LT, arg(0), arg(1));
        let masked = expr::op2(op::AND, arg(1), expr::konst_u64(0xff));
        let items = [
            check(expr::op2(op::EQ, masked, expr::konst_u64(0x42))),
            check(below),
        ];
        let found = solve(&items, &[true, true], &inputs(), &words()).expect("solvable");
        let (a, b) = (word(&found.calldata, 4), word(&found.calldata, 36));
        assert!(a < b && (b & U256::from_u64(0xff)) == U256::from_u64(0x42));
    }

    #[test]
    fn a_stored_value_is_read_back_by_a_later_check() {
        let key = expr::konst_u64(5);
        let load = expr::intern(Node::SLoad(key, false, 1));
        let items = [
            Item::Store {
                key,
                val: arg(0),
                gen: 0,
            },
            check(expr::op2(op::EQ, load, expr::konst_u64(9))),
        ];
        let found = solve(&items, &[true], &inputs(), &words()).expect("solvable");
        assert_eq!(word(&found.calldata, 4), U256::from_u64(9));
    }

    #[test]
    fn prior_storage_is_chosen_only_when_it_is_free() {
        let load = expr::intern(Node::SLoad(expr::konst_u64(3), false, 0));
        let items = [check(expr::op2(op::EQ, load, expr::env(op::CALLER)))];
        assert!(solve(&items, &[true], &inputs(), &words()).is_none());
        let free = Free {
            storage: true,
            ..words()
        };
        let found = solve(&items, &[true], &inputs(), &free).expect("solvable");
        assert_eq!(
            found.storage.get(&U256::from_u64(3)),
            Some(&U256::from_u64(0xc0))
        );
    }

    #[test]
    fn a_check_that_depends_on_nothing_free_has_no_solution() {
        let items = [check(expr::op2(
            op::EQ,
            expr::env(op::CALLER),
            expr::konst_u64(1),
        ))];
        assert!(solve(&items, &[true], &inputs(), &words()).is_none());
    }
}
