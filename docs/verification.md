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

## 3. Coverage and control flow

Each contract reports the number of code blocks covered by some function (external, internal,
fallback, orphan) and the number of jumps whose target could not be resolved. Code that nothing
references is still decompiled as `orphan_<pc>` functions, so nothing is silently dropped.

## Results

See the tables in [README.md](../README.md); regenerate with:

```sh
cargo build --release
python3 corpus/bench.py            # interface recovery (add --sigs to use the dictionary)
RUNS=8 ./corpus/verify_all.sh      # block oracle over the corpus
cargo test -p evmdec               # unit + integration tests
```
