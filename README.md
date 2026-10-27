# evmdec — EVM bytecode decompiler and security analyzer

`evmdec` turns any EVM contract — fetched by address from any EVM chain, or pasted as raw
bytecode before deployment — into structured, readable pseudo-Solidity, and then analyses it for
security issues. It is written from scratch in Rust (own 256-bit arithmetic, keccak, disassembler,
control-flow recovery, lifter, structurer, concrete interpreter) and ships its own correctness
oracle, so the accuracy claim below is measured, not asserted.

```
┌──────────┐  ┌──────────┐  ┌──────────────────┐  ┌──────────┐  ┌────────────┐  ┌───────────────┐
│ bytes /  │→ │ disasm + │→ │ summary-based CFG│→ │ symbolic │→ │ structurer │→ │ pseudo-Solidity│
│ RPC      │  │ metadata │  │ + internal funcs │  │ lifter   │  │            │  │ + report       │
└──────────┘  └──────────┘  └──────────────────┘  └──────────┘  └────────────┘  └───────────────┘
                                                        ↕ block oracle (concrete interpreter)
```

## What you get

* **Any bytecode, never a failure.** Runtime or creation code (constructor and runtime are
  split and both decompiled), solc 0.4 → 0.8.x, Vyper 0.2 → 0.3.x, hand-written and minimal
  proxies, embedded contracts (`CREATE`/`CREATE2` payloads, with `--embedded`). Jumps are resolved
  by a compositional summary analysis that recovers internal functions and their argument/return
  counts without exploding on nested calls; code nothing references is still decompiled as
  `orphan_<pc>` functions; anything unresolved is reported, not dropped.
* **Real decompilation.** Function dispatcher recovery (linear, binary-search, `XOR`/`SUB`
  compare, Vyper jump tables), parameter and return types inferred from use (ABI head checks,
  masks, sign extension, dynamic offsets — including decoding done in solc 0.8 helper functions,
  which are summarised and seen through), `view`/`pure`/`payable` from effects, storage layout
  with mappings and arrays (`stor_3[msg.sender][spender]`), events and custom errors by
  signature, `require(cond, "reason")`, `Panic(…)`, `if`/`else`/`while`/`break`/`continue`,
  ternaries and short-circuits, ABI-encoded external calls shown as `IERC20(t).transfer(to, amt)`
  style calls, `emit Transfer(from, to, amount)`, `event Transfer(address indexed, address indexed, uint256)`
  with `indexed` recovered from the topic count. Small helpers (SafeMath, ABI decoders and
  encoders, getters) are summarised and inlined at their call sites, the checks they contain
  survive as `require`/`assert` lines, and helpers left with no call site are not printed.
  Compiler idioms are folded: a storage `string` getter prints as `return name;` with the slot
  typed `string`, the dynamic-bytes return encoder (copy loop plus padding) becomes `return x;`,
  `success = to.call{value: v, gas: 2300}(""); require(success)` prints as
  `payable(to).transfer(v)`, and functions that only ever return the constants 0/1 return `bool`.
  A dictionary of ~1,250 function, event and error
  signatures (selectors computed with the built-in keccak, so every entry is correct) names what
  it can; everything else is named by selector.
* **Security report.** Reentrancy (with guard and gas-stipend awareness), ignored call return
  values, arbitrary calls and delegatecalls, selfdestruct exposure, authority slots writable
  without access control, `tx.origin` auth, weak randomness, unchecked arithmetic on pre-0.8
  compilers, storage-bounded loops, calls in loops, `msg.value` reuse in payable multicalls,
  ecrecover misuse, unprotected upgrades, proxy detection (EIP-1967 / beacon / ZeppelinOS /
  EIP-1167 / storage-slot) with on-chain implementation resolution, known compiler bugs for the
  detected solc version, revert strings, privileged functions, selectors called on other
  contracts. Rules look through internal helpers (a call in a shared `_safeTransfer` is
  attributed to every external function that reaches it), and findings are folded per defect:
  one entry per rule and function, with the number of sites, and one entry for a helper shared
  by several functions. Each finding carries severity, confidence, the function and program
  counter, evidence lines and a recommendation. Markdown and JSON.
* **Verified.** A concrete EVM interpreter executes every basic block from random states and the
  result is compared with the lifted statements (stack, memory, storage, logs, calls, control
  decision). See *Accuracy*.
* **CLI and web app.** `evmdec decompile <address|file|hex>` (with `--lookup` to resolve
  unknown selectors through openchain.xyz / 4byte.directory), `analyze`, `verify`, `disasm`,
  `info`, `cfg`; an axum server with a single-page UI (paste an address or bytecode, browse
  functions, read the report, download `.sol`). The CLI never fails on an input: if the
  decompiler hits an internal error it prints the disassembly instead.

## Layout

| path | what |
|---|---|
| `crates/decompiler` (`evmdec`) | the library: `u256`, `keccak`, `disasm`, `metadata`, `cfg` (summary analysis, units), `expr` (hash-consed IR + simplifier), `lift`, `structure`, `emit`, `function`, `sigs`, `decompile`, `analyze`, `interp`, `verify`, `rpc` |
| `crates/cli` (`evmdec`) | command line |
| `crates/server` (`evmdec-server`) | web service + UI (`crates/server/static/index.html`) |
| `testdata/mainnet` | 22 mainnet contracts (runtime bytecode + Sourcify ABI) used by the benchmark and the tests |
| `corpus/bench.py`, `corpus/verify_all.sh` | the measurements below |
| `docs/verification.md` | methodology and definitions |

## Quick start

```sh
cargo build --release

# by address (public RPC endpoints of the chain are tried in order; proxies are followed)
./target/release/evmdec decompile 0xdAC17F958D2ee523a2206206994597C13D831ec7 --report
./target/release/evmdec decompile 0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48 --chain mainnet   # USDC proxy → implementation
./target/release/evmdec decompile 0x... --chain arbitrum --rpc https://my.node/      # or EVMDEC_RPC_URL=url1,url2

# pre-deployment review: paste the compiled bytecode (creation or runtime)
solc --bin MyContract.sol | tail -1 > my.hex
./target/release/evmdec decompile my.hex --report        # code + security report
./target/release/evmdec analyze my.hex                   # report only (markdown; --json for machines)
./target/release/evmdec decompile my.hex --json          # everything: functions, storage, events, report

# other views
./target/release/evmdec decompile my.hex --lookup        # name unknown selectors via openchain / 4byte
./target/release/evmdec decompile my.hex --flat          # labels and gotos instead of structured code
./target/release/evmdec disasm my.hex
./target/release/evmdec verify my.hex --runs 8           # block oracle on this contract

# web app (default http://localhost:8080)
PORT=8080 ./target/release/evmdec-server
```

Or with Docker: `docker build -t evmdec . && docker run -p 8080:8080 evmdec`.

API: `POST /api/decompile` with `{"address": "0x…", "chain": "mainnet"}` or `{"bytecode": "0x…"}`,
`GET /api/address/{chain}/{address}`, `GET /api/chains`. Responses contain `contract` (functions,
storage, events, source), `report`, `report_markdown`, `disassembly` and, for proxies,
`implementation`.

## Accuracy: how it is measured

"Decompiles 100 % of any contract with ≥ 90 % accuracy" needs definitions, so `evmdec` measures
three things on 22 unmodified mainnet contracts (solc 0.4.18–0.8.17, Vyper 0.2.4 and 0.3.9;
WETH, USDT, USDC proxy + implementation, Uniswap V2 router/pair, Uniswap V3 factory, Permit2,
Universal Router, 1inch v5, Seaport 1.5, Gnosis Safe, Compound cETH, MakerDAO Vat, Aave v3 pool
proxy, ENS registry, Lido stETH proxy, Multicall3, Curve 3pool and TriCrypto-NG, the CREATE2
deployer, UNI). Everything is reproducible with `corpus/bench.py` and `corpus/verify_all.sh`
(details and definitions in [docs/verification.md](docs/verification.md)).

### 1. Interface recovery vs. verified ABIs (signature dictionary disabled)

| metric | result |
|---|---|
| external function selectors found | **515 / 515** (recall 100 %, precision 100 %) |
| state mutability (view/pure vs payable vs nonpayable) | 509 / 515 = **98.8 %** |
| parameter count | 513 / 515 = **99.6 %** |
| return count | 514 / 515 = **99.8 %** |
| events | 119 / 121 = **98.3 %** |
| code blocks covered by some function | 10,810 / 10,810 = **100 %** |
| unresolved jumps | **0** |
| total time | 2.2 s for the whole corpus |

"Code blocks" are blocks the EVM can actually enter (the entry, `JUMPDEST`-started blocks and
`JUMPI` fall-throughs); bytes after a terminator without a `JUMPDEST` are data or dead by
construction, and embedded creation code (`CREATE2` payloads) and metadata are excluded.

The six mutability misses are `view` functions that make external calls on a pre-0.5 compiler
(no `STATICCALL`) or `view` getters of transparent proxies that fall through to `delegatecall`;
the two parameter misses are in MakerDAO Vat (a `LogNote`-style modifier reading raw calldata
words) and Curve 3pool, the one return miss in Gnosis Safe.

### 2. Block-level semantics oracle (`evmdec verify`, 8 random states per block)

Every basic block of every contract — reachable or not — is executed by the concrete interpreter
and by the lifted statements from the same random state; stack, memory, storage, logs, calls and
the control decision are compared.

| | |
|---|---|
| blocks | 13,656 |
| runs | 109,011 |
| agree | 107,480 |
| **mismatch** | **0** |
| inconclusive runs (reference cannot execute the random state, or it makes two differently-based memory accesses alias) | 1,553 |
| blocks verified (≥ 1 agreeing run, no disagreement) | 13,610 / 13,656 |
| **instructions in verified blocks** | **158,380 / 159,940 = 99.03 %** |

A mismatch is a decompiler bug by definition; there are none. The 46 unverified blocks never
produced a conclusive run (they consume stack values as huge memory offsets in every drawn state).

### 3. Random sample: any contract people actually use

To check the "any contract" claim beyond the hand-picked set, `corpus/harvest.py` collects the
`to` address of every transaction in random recent mainnet blocks and fetches the runtime code
(no ABI needed). 120 distinct contracts from 12 blocks (`corpus/sample_ids.txt`; tokens,
routers, MEV bots with hand-written calldata-indexed jump tables, proxies, 0.4 → 0.8 solc,
Vyper) were run through `corpus/run_sample.sh`:

| | |
|---|---|
| contracts decompiled | **120 / 120** (0 failures, 0 timeouts; largest 24.5 KB in 0.4 s) |
| code blocks covered | 53,720 / 53,810 = 99.8 % |
| unresolved jumps | 0 |
| block oracle (3 states per block): mismatches | **0** in 592,999 instructions |
| instructions in verified blocks | 575,971 / 592,999 = 97.1 % |

### 4. What the numbers do not cover

The oracle checks blocks in isolation, so it validates the lifter and the simplifier on the whole
program but not the inter-block merging of values (phi placement) or the structuring. Those are
covered by the interface benchmark (which exercises the whole pipeline) and by reading the
output: the corpus decompiles into code whose logic matches the verified sources (WETH, USDT,
Uniswap V2, Permit2, Multicall3 were checked by hand). The signature dictionary only names
functions; it does not influence recovery.

## Known limitations

* Memory accesses through different symbolic bases are assumed not to alias (true for compiler
  output; a hand-written contract that relies on aliasing will decompile imprecisely — the
  oracle reports such states as inconclusive rather than hiding them).
* Internal functions are named `func_<pc>`; their parameter types are shown as `uint256`.
* Dynamic-type ABI encoding (`string` returns, `bytes` arguments) is shown as the memory
  operations the compiler emitted rather than as `abi.encode`.
* The analyzer is heuristic: findings carry a confidence level and should be read as leads.

## License

MIT.
