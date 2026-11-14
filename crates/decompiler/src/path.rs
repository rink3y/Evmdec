use crate::cfg::Program;
use crate::exec::{self, FrameRun};
use crate::expr;
use crate::interp::{self, Host};
use crate::lift::{self, Lifter, Stmt, Term};
use crate::solve::{self, Free, Given, Inputs, Item};
use crate::u256::U256;
use std::cell::Cell;
use std::collections::{HashMap, HashSet, VecDeque};

const STEP_BUDGET: usize = 200_000;
const MAX_BLOCKS: usize = 2_048;
const MAX_LATE_RUNS: usize = 1024;
// Reading one block of a trace back into expressions costs about this many steps.
const BLOCK_COST: u64 = 40;
const DEFAULT_BALANCE: U256 = U256::from_u64(1_000_000_000_000_000_000);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    pub paths: usize,
    pub runs: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Limits {
            paths: 48,
            runs: 240,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Path {
    pub inputs: Inputs,
    pub items: Vec<Item>,
    pub truth: Vec<bool>,
    pub effects: Vec<Stmt>,
    pub end: Option<Term>,
    pub run: FrameRun,
}

impl Path {
    pub fn signature(&self) -> Vec<(usize, bool)> {
        let checks = self.items.iter().filter_map(|i| match i {
            Item::Check { pc, holds, .. } => Some((*pc, *holds)),
            Item::Store { .. } => None,
        });
        checks.collect()
    }

    pub fn succeeded(&self) -> bool {
        self.run.succeeded()
    }
}

pub struct Explorer {
    prog: Program,
    late: Cell<usize>,
}

// One explorer per piece of code. A contract made of several parts has several.
#[derive(Default)]
pub struct Explorers {
    by_code: HashMap<*const u8, Explorer>,
}

impl Explorers {
    pub fn of(&mut self, code: &[u8]) -> &Explorer {
        let made = || Explorer::new(code);
        self.by_code.entry(code.as_ptr()).or_insert_with(made)
    }
}

// Branches alone never ask for a non-zero amount, and a zero amount moves nothing.
// Every word differs, so two arguments are never equal by chance.
pub fn varied_word(index: usize) -> U256 {
    U256::from_u64(0x1001 + 2 * index as u64)
}

pub fn fill_words(calldata: &[u8], fixed: &[usize], value: impl Fn(usize) -> U256) -> Vec<u8> {
    let mut out = calldata.to_vec();
    for index in (0..calldata.len().saturating_sub(4) / 32).filter(|i| !fixed.contains(i)) {
        let at = 4 + 32 * index;
        out[at..at + 32].copy_from_slice(&value(index).to_be_bytes());
    }
    out
}

pub fn inputs_for(selector: Option<u32>, words: usize) -> Inputs {
    Inputs {
        calldata: exec::calldata(selector, &vec![U256::ZERO; words]),
        caller: exec::CALLER,
        address: exec::SELF,
        callvalue: U256::ZERO,
        timestamp: U256::from_u64(1_700_000_000),
        number: U256::from_u64(18_000_000),
        storage: HashMap::new(),
        returned: Vec::new(),
        replies: Vec::new(),
        answers: Vec::new(),
        given: Vec::new(),
        balance: DEFAULT_BALANCE,
        signed: None,
        failing: None,
        spends_balance: false,
        moving: Vec::new(),
    }
}

fn last_check(p: &Path) -> Option<expr::ExprId> {
    p.items.iter().rev().find_map(|item| match item {
        Item::Check { cond, .. } => Some(*cond),
        Item::Store { .. } => None,
    })
}

fn stopped_on(p: &Path) -> &'static str {
    let Some(cond) = last_check(p) else {
        return "nothing";
    };
    let env =
        |which: u8| expr::contains(cond, &|n| matches!(n, expr::Node::Env(o, _) if *o == which));
    let answer = expr::contains(cond, &|n| {
        matches!(n, expr::Node::ReturnData(..) | expr::Node::CallResult(_))
    });
    let stored = expr::contains(cond, &|n| matches!(n, expr::Node::SLoad(..)));
    let caller = env(crate::opcode::CALLER);
    match (answer || env(crate::opcode::RETURNDATASIZE), caller, stored) {
        (true, ..) => "answer",
        (_, true, true) => "caller-against-storage",
        (_, true, false) => "caller",
        (_, _, true) => "storage",
        _ if env(crate::opcode::CALLVALUE) => "value",
        _ => "input",
    }
}

impl Explorer {
    pub fn new(code: &[u8]) -> Explorer {
        Explorer {
            prog: Program::new(code.to_vec()),
            late: Cell::new(0),
        }
    }

    // A finding names where its statement starts. The instruction it is about comes
    // later in the same block.
    pub fn rest_of_block(&self, pc: usize) -> std::ops::Range<usize> {
        let block = self.prog.block_at_pc.range(..=pc).next_back();
        let end = block.map_or(pc + 1, |(_, id)| self.prog.blocks[*id].end);
        pc..end.max(pc + 1)
    }

    // The run alone, without reading it back into expressions. Reading back costs far
    // more than running, and a caller that only counts what moved has no use for it.
    pub fn run_only(&self, inputs: &Inputs) -> FrameRun {
        let mut host = Host::controlled(
            inputs.address,
            inputs.caller,
            inputs.calldata.clone(),
            inputs.callvalue,
        );
        host.timestamp = inputs.timestamp;
        host.number = inputs.number;
        host.forced_return = inputs.returned.clone();
        host.replies = inputs.replies.clone();
        host.answers = inputs.answers.clone();
        host.signed = inputs.signed.clone();
        host.failing = inputs.failing;
        host.spends_balance = inputs.spends_balance;
        host.moving = inputs.moving.clone();
        host.selfbalance = inputs.balance;
        exec::run_frame(&self.prog.code, &host, inputs.storage.clone(), STEP_BUDGET)
    }

    pub fn run(&self, inputs: &Inputs) -> Path {
        let mut run = self.run_only(inputs);
        // Thousands of paths are kept at once. Each would hold one entry per step it ran.
        let order = std::mem::take(&mut run.order);
        let blocks: Vec<usize> = order
            .iter()
            .filter_map(|pc| self.prog.block_at_pc.get(pc).copied())
            .take(MAX_BLOCKS)
            .collect();
        exec::spend(blocks.len() as u64 * BLOCK_COST);
        let lifter = Lifter {
            prog: &self.prog,
            root: true,
            summaries: HashMap::new(),
            footprints: HashMap::new(),
            oracle: true,
            copy_loops: Default::default(),
        };
        let nodes = lifter.lift_trace(&blocks);
        let mut items = Vec::new();
        let mut truth = Vec::new();
        let mut effects = Vec::new();
        let mut made = Vec::new();
        for (i, node) in nodes.iter().enumerate() {
            for (at, st) in node.stmts.iter().enumerate() {
                if let Stmt::Call { seq, .. } = st {
                    made.push((*seq, lift::call_stamp(i, at + 1)));
                }
                match st {
                    Stmt::SStore {
                        key,
                        val,
                        transient: false,
                        gen,
                    } => {
                        items.push(Item::Store {
                            key: *key,
                            val: *val,
                            gen: *gen,
                        });
                        effects.push(st.clone());
                    }
                    Stmt::Call { .. }
                    | Stmt::Create { .. }
                    | Stmt::Log { .. }
                    | Stmt::MStore { .. } => {
                        effects.push(st.clone());
                    }
                    _ => {}
                }
            }
            if let Term::CondJump { cond, target } = &node.term {
                let block = &self.prog.blocks[node.block];
                let next = blocks.get(i + 1).map(|b| self.prog.blocks[*b].start);
                // A jump to the instruction after it goes the same way whatever the test
                // says. Recording a side would ask the solver for a run that changes nothing.
                let to = expr::as_const(*target).and_then(|t| t.as_usize());
                if to == Some(block.end) {
                    continue;
                }
                // A long run is read back only up to a limit. The branch at the cut has
                // no block after it, so which way it went is not known.
                let Some(next) = next else { continue };
                let holds = next != block.end;
                items.push(Item::Check {
                    cond: *cond,
                    holds,
                    pc: self.prog.insns[block.last].pc,
                });
                truth.push(holds);
            }
        }
        let mut inputs = inputs.clone();
        let mut outside = 0;
        inputs.given = made
            .iter()
            .zip(&run.calls)
            .enumerate()
            .map(|(index, ((seq, size), call))| {
                let (signed, replies) = (&inputs.signed, &inputs.replies);
                let chosen = interp::own_answer(&inputs.answers, index);
                let moved = interp::moving_answer(&inputs.moving, outside, call.addr, &call.input);
                let went_out = interp::goes_outside(&inputs.moving, call.addr, &call.input);
                outside += usize::from(call.kind == crate::opcode::CALL && went_out);
                let by_default =
                    interp::answered_by_default(signed, replies, call.addr, &call.input);
                let open = moved.is_none() && by_default;
                let usual =
                    || interp::answer(signed, replies, &inputs.returned, call.addr, &call.input);
                let data = moved.unwrap_or_else(|| chosen.cloned().unwrap_or_else(usual));
                Given {
                    seq: *seq,
                    size: *size,
                    open,
                    data,
                }
            })
            .collect();
        Path {
            inputs,
            items,
            truth,
            effects,
            end: nodes.last().map(|n| n.term.clone()),
            run,
        }
    }

    // Each new path is only kept after the bytecode really ran it.
    pub fn explore(&self, start: &Inputs, free: &Free, limits: Limits) -> Vec<Path> {
        let paths = self.search(start, free, limits);
        if crate::debug::on("EVMDEC_DEBUG_STOPS") {
            let finished = paths.iter().any(Path::succeeded);
            let deepest = paths.iter().max_by_key(|p| p.truth.len());
            let stop = deepest.filter(|_| !finished).map_or("-", stopped_on);
            let last = deepest.filter(|_| !finished).and_then(last_check);
            let shown = last.map_or(String::new(), |c| {
                crate::emit::fmt_expr(c, &Default::default())
            });
            let shown: String = shown.chars().take(120).collect();
            eprintln!(
                "[stops] finished={finished} storage={} answers={} on={stop} last={shown}",
                free.storage, free.answers
            );
        }
        paths
    }

    fn search(&self, start: &Inputs, free: &Free, limits: Limits) -> Vec<Path> {
        // Past its limit a caller still gets one run of each function, so a slow first
        // function does not hide the rest. The count ends that for a contract with
        // thousands of functions, which would otherwise run every one of them.
        if exec::spent() {
            if self.late.get() >= MAX_LATE_RUNS {
                return Vec::new();
            }
            self.late.set(self.late.get() + 1);
        }
        let first = self.run(start);
        let mut seen: HashSet<Vec<(usize, bool)>> = HashSet::new();
        seen.insert(first.signature());
        let mut queue: VecDeque<(usize, usize)> = VecDeque::new();
        let mut paths = vec![first];
        queue.push_back((0, 0));
        let mut runs = 1;
        while let Some((index, bound)) = queue.pop_front() {
            let last = paths[index].truth.len();
            // A run that fails stops at its last check, so that is the one whose other side
            // leads further. Early checks mostly validate arguments and only add failing runs.
            for flip in (bound..last).rev() {
                if exec::spent() || runs >= limits.runs || paths.len() >= limits.paths {
                    return paths;
                }
                let base = &paths[index];
                let mut want = base.truth[..=flip].to_vec();
                want[flip] = !want[flip];
                let Some(inputs) = solve::solve(&base.items, &want, &base.inputs, free) else {
                    continue;
                };
                runs += 1;
                let path = self.run(&inputs);
                if seen.insert(path.signature()) {
                    queue.push_back((paths.len(), flip + 1));
                    paths.push(path);
                }
            }
        }
        paths
    }
}
