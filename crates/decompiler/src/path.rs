use crate::cfg::Program;
use crate::exec::{self, FrameRun};
use crate::interp::{self, Host};
use crate::lift::{Lifter, Stmt, Term};
use crate::solve::{self, Free, Inputs, Item};
use crate::u256::U256;
use std::collections::{HashMap, HashSet, VecDeque};
use std::time::Instant;

const STEP_BUDGET: usize = 200_000;
const MAX_BLOCKS: usize = 2_048;
const MAX_FLIPS_PER_PATH: usize = 48;
const DEFAULT_BALANCE: U256 = U256::from_u64(1_000_000_000_000_000_000);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    pub paths: usize,
    pub runs: usize,
    pub until: Option<Instant>,
}

impl Default for Limits {
    fn default() -> Self {
        Limits {
            paths: 48,
            runs: 240,
            until: None,
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
        given: Vec::new(),
        balance: DEFAULT_BALANCE,
        signed: None,
    }
}

impl Explorer {
    pub fn new(code: &[u8]) -> Explorer {
        Explorer {
            prog: Program::new(code.to_vec()),
        }
    }

    pub fn run(&self, inputs: &Inputs) -> Path {
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
        host.signed = inputs.signed.clone();
        host.selfbalance = inputs.balance;
        let run = exec::run_frame(&self.prog.code, &host, inputs.storage.clone(), STEP_BUDGET);
        let blocks: Vec<usize> = run
            .order
            .iter()
            .filter_map(|pc| self.prog.block_at_pc.get(pc).copied())
            .take(MAX_BLOCKS)
            .collect();
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
        for (i, node) in nodes.iter().enumerate() {
            for st in &node.stmts {
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
            if let Term::CondJump { cond, .. } = &node.term {
                let block = &self.prog.blocks[node.block];
                let next = blocks.get(i + 1).map(|b| self.prog.blocks[*b].start);
                let holds = next != Some(block.end);
                items.push(Item::Check {
                    cond: *cond,
                    holds,
                    pc: self.prog.insns[block.last].pc,
                });
                truth.push(holds);
            }
        }
        let mut inputs = inputs.clone();
        let made = effects.iter().filter_map(|st| match st {
            Stmt::Call { seq, .. } => Some(*seq),
            _ => None,
        });
        inputs.given = made
            .zip(&run.calls)
            .map(|(seq, call)| {
                let (replies, default) = (&inputs.replies, &inputs.returned);
                let data = interp::answer(&inputs.signed, replies, default, call.addr, &call.input);
                (seq, data)
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
        let first = self.run(start);
        let mut seen: HashSet<Vec<(usize, bool)>> = HashSet::new();
        seen.insert(first.signature());
        let mut queue: VecDeque<(usize, usize)> = VecDeque::new();
        let mut paths = vec![first];
        queue.push_back((0, 0));
        let mut runs = 1;
        while let Some((index, bound)) = queue.pop_front() {
            let last = paths[index].truth.len().min(bound + MAX_FLIPS_PER_PATH);
            for flip in bound..last {
                let late = limits.until.is_some_and(|t| Instant::now() >= t);
                if late || runs >= limits.runs || paths.len() >= limits.paths {
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
