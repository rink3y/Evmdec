# Verification methodology

`evmdec` is built from scratch (its own 256-bit arithmetic, keccak, disassembler, control-flow
recovery, lifter, structurer and interpreter), so it carries its own correctness checks. Every
number below is reproducible with the commands at the end.

## 1. Interface recovery against verified ABIs (`corpus/bench.py`)

`testdata/mainnet` holds the runtime bytecode of 22 unmodified mainnet contracts together with
their Sourcify-verified ABIs (solc 0.4.18 through 0.8.17, Vyper 0.2.4 and 0.3.9; tokens,
AMMs, a lending market, a multisig, proxies, routers, Seaport). The benchmark decompiles each
contract **with the signature dictionary disabled** and compares what was *inferred* with the ABI:

| metric | definition |
|---|---|
| selector recall / precision | external function selectors found vs. the ABI's functions |
| mutability | `view`/`pure` vs. `payable` vs. `nonpayable` agrees with the ABI (view and pure are not distinguished) |
| parameters | number of ABI head words matches the inferred parameter count |
| returns | number of returned values matches (dynamic returns count as one) |
| events | event topic hashes emitted by the code vs. the ABI's events |

## 2. Block-level oracle (`evmdec verify`)

The claim "the decompiled statements mean what the bytecode means" is checked per basic block,
on the whole program, reachable or not:

1. every basic block is lifted on its own with a symbolic entry stack (`arg0`, `arg1`, …);
2. a random state is drawn: stack values (small numbers, word-aligned offsets, addresses, full
   words), random memory, random calldata and environment, deterministic storage and a
   deterministic "world" (call results, return data, external code, balances);
3. the block is executed by the concrete interpreter (`interp.rs`) from that state;
4. the lifted statements are evaluated from the same state;
5. the exit stack, the whole memory, storage and transient-storage writes, logs, the sequence of
   external calls (kind, gas, target, value, input bytes, output region), contract creations and
   the control decision (jump target, branch condition and target, return/revert payload bytes,
   stop, selfdestruct, invalid) must all agree.

A run is **inconclusive** (never counted as agreement) when the reference interpreter itself
cannot execute from the drawn state (a random word used as a memory offset), when the lifted
expression refers to return data beyond what the call returned, or when the random state makes
two memory accesses with *different symbolic bases* overlap: the lifter assumes such accesses do
not alias (the standard assumption of EVM decompilers, which compiler output satisfies), so the
run says nothing about the lifter. Inconclusive states are redrawn up to ten times per run,
switching to small and then widely spread values.

A block is **verified** when at least one run agreed and none disagreed. A **mismatch** is a
decompiler bug by definition; `--verbose` prints the lifted block and both sides.

## 3. Random sample (`corpus/harvest.py`, `corpus/run_sample.sh`)

The hand-picked corpus could be lucky, so `corpus/harvest.py` draws random recent mainnet blocks
and fetches the runtime code of every distinct transaction target with code; `corpus/run_sample.sh`
decompiles each one with a 120 s limit and runs the block oracle. The addresses of the sample
reported in the README are in `corpus/sample_ids.txt`. Nothing about the sample was chosen by hand.

## 4. Analyzer recall (`corpus/vuln_bench.py`)

`testdata/vuln/*.hex` is the unmodified runtime bytecode of contracts whose exploits are public,
fetched from the chain they were deployed on (mostly mainnet; the Vyper lock-bug pool from its
mainnet address at the time of the incident). `testdata/vuln/manifest.json` records, per contract,
the year, the bug in one line, the rule ids that constitute "finding it" (any one suffices) and
the minimum severity. A contract counts as detected when one of its expected rules fires at or
above that severity in the analyzer's JSON report. `detectable: false` marks bugs that are not
visible as a bytecode pattern (an upgrade that initialised a storage slot to a value a check
treated as "trusted"); they are listed so the limitation is explicit, and excluded from recall.

The same script analyses the audited corpus of §1 and prints its high/critical findings. That
number is the false-positive budget: a rule change that raises recall but adds findings on
WETH, USDC, Uniswap, Permit2, Maker or ENS is a regression. Findings on Multicall3, the Gnosis
Safe, 1inch and Seaport are expected, as executing caller-supplied calls is what those contracts
do.

The analyzer works on the lifted IR, not on opcode sequences: every external function's
statements are collected together with those of the internal helpers it reaches (five levels
deep), with the helper's arguments replaced by the caller's actual values and the helper's
memory reads resolved against a replay of the writes seen so far. Rules are predicates over
that stream (an external call whose payload word 0 is `transferFrom` and whose `from` word
comes from calldata and is not `msg.sender`, in a function without a caller check, is
`arbitrary-transferfrom`).

A contract fetched by address is analysed as what it resolves to. A proxy is composed with its
implementation and a diamond with its facets (`fetch.rs`, `decompile::compose`): the parts'
functions join one list, each tagged with the address whose code holds it and given a distinct
pc range, their storage layouts and type environments are merged, and the analyzer runs once
over the whole. Rules that reason across functions (access-control policy, attack chains,
reentrancy locks) therefore see every entry point of the system, and the two execution passes
run each function's own code in the composite's storage, as `DELEGATECALL` does. A slot two
parts type differently is a `storage-collision` finding; a routed selector the shell answers
itself is reported as shadowed. Hard-coded call targets of every part are fetched one level
further and resolved the same way.

Two passes run the bytecode rather than match it. The confirmation pass (`confirm.rs`) takes
the findings whose sink is a concrete instruction (an open `selfdestruct`, an ether withdrawal,
an owner write, an arbitrary call) and searches for calldata under which a caller holding no
role, from a fresh state, enters the sink's block, ends the transaction normally and leaves the
effect the rule describes (the destruct outcome, a value-bearing call, a delegatecall, a
`transferFrom` payload, a storage write, or for a silent authorisation failure a normal return
that did nothing), using the whole-frame executor (`exec.rs`); a hit marks the finding
*Confirmed* and records the calldata as its witness. Entering the block alone is not enough: a
guard inlined ahead of the sink or a revert after it leaves no effect. The fresh state is all
zero, so a gate the constructor sets is open in this model; the zero address holds no code. The invariant pass (`invariant.rs`) checks
a property of whole transactions instead of one sink: no unprivileged caller may raise its own
entry in a balance ledger out of nothing. Ledgers are the `mapping(address => uint)` variables
that are also debited or paid out somewhere (counters and nonces are not), whose entries never
feed signed arithmetic (dividend offsets are not), and each state-changing entry point is run
from an empty state with zero value; a run that ends with the caller holding a balance is
`unprivileged-balance-credit`, with the calldata as witness. A balance that is the wrap of a
subtraction counts only when the contract compares that ledger unsigned elsewhere, since the
bytecode otherwise cannot tell an underflow from signed accounting going negative.

## 5. Coverage and control flow

Each contract reports the number of *potential code* blocks covered by some function (external,
internal, fallback, orphan) and the number of jumps whose target could not be resolved. A
potential code block is one the EVM can enter: the entry, a `JUMPDEST`-started block, or the
fall-through of a `JUMPI`; bytes after a terminator without a `JUMPDEST` cannot execute and are
data or dead by construction. Embedded creation code (`CREATE2` payloads) and the metadata
trailer are excluded. Computed jumps (targets built from calldata or shift-selected constants)
are resolved by enumerating the destinations compatible with the expression's shape. Code that
nothing references is still decompiled as `orphan_<pc>` functions, so nothing is silently dropped.

## Results

See the tables in [README.md](../README.md); regenerate with:

```sh
cargo build --release
python3 corpus/bench.py            # interface recovery (add --sigs to use the dictionary)
RUNS=8 ./corpus/verify_all.sh      # block oracle over the corpus
python3 corpus/harvest.py --out sample --blocks 12 --max 120   # random mainnet sample
DIR=sample RUNS=3 ./corpus/run_sample.sh                        # decompile + oracle on it
python3 corpus/vuln_bench.py       # analyzer recall on known exploits + false-positive load
cargo test -p evmdec               # unit + integration tests (corpus, oracle, analyzer)
```
