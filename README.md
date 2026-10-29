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
  Revert reasons are decoded even when several `require`s share one `revert(ptr, sub(end, ptr))`
  tail (solc 0.8 output), solc 0.8's checked arithmetic prints as the plain operation (the
  compiler's own overflow / division-by-zero panics are not shown), the ABI size checks print as
  `require(msg.data.length >= 36)`, events whose signature is unknown are declared and emitted
  as `Event_<topic prefix>(...)`, and the simultaneous copies on a loop's back edge are printed
  in an order that preserves their meaning.
  Packed storage slots are split into their fields (`uint112 stor_8_0; uint112 stor_8_14;
  uint32 stor_8_28;` for a Uniswap V2 pair's reserves, `address` + `bool` owner/paused pairs,
  signed fields via `signextend`), and reads and writes of a field print as the field.
  Fixed-size storage arrays (`uint[256] owners` laid out from slot 2, recognised by the bounds
  check on the index) print as `stor_2[i]`, and a dynamic array whose data slot the compiler
  precomputed (`keccak256(0x104)` appearing as a constant) prints as `stor_260[i]` rather than
  as a variable named after the hash. A slot read before it is overwritten and used afterwards
  (`pending.index = list.length++`) keeps its old value in a `prev_<slot>` temporary instead of
  printing as the slot twice; memory scratch stores overwritten before anything reads them are
  not printed; temporaries are declared in the block that uses them; and the continuation of a
  pre-0.4 modified function, which the compiler reaches both by falling through and by a jump
  with a return address, is shown once, inline, not again as a helper. A constant that is a
  precomputed `keccak256(slot) ± k` resolves to that array (`tokens[tokens.length - 1]`), a
  packed field cleared with a mask prints as `field = 0`, and an event whose data is the ABI
  encoding of calldata prints as `emit E(..., abi.encode(msg.data))` with `msg.sig` named.
  A dictionary of ~1,280 function, event and error
  signatures (selectors computed with the built-in keccak, so every entry is correct) names what
  it can; everything else is named by selector.
* **Security report.** 40+ rules over the lifted IR (not opcode patterns): reentrancy (ETH or
  token hook before a storage write; a guard counts only when a slot is tested before the call,
  set on entry and restored to a constant afterwards, whether the release writes the slot or
  clears a packed field of it, storage or transient; ERC721/1155/777 hook
  selectors raise confidence; "written after the call" is decided on the control flow of the
  helper the call sits in, not on the call site, and a function behind a msg.sender check is
  reported at medium severity with the exploit condition spelled out), ignored call results, ERC20 `transfer`/`transferFrom` results
  never decoded, arbitrary `call`/`delegatecall` with caller-controlled target and selector,
  run-time-dispatched calls (relayers, cross-chain executors), `transferFrom(from, …)` moving
  someone else's approved tokens on the caller's say-so, decisions trusted to the answers of a
  caller-supplied contract, Chainlink answers used without staleness/positivity checks,
  fee-on-transfer assumptions, spot balances used as a price, division before multiplication,
  `ecrecover` zero-address and malleability, signatures without a domain or without a nonce,
  weak randomness, `msg.value` reused in loops and payable multicalls, unchecked arithmetic on
  pre-0.8 compilers and inside `unchecked {}` blocks, authority slots and initializers writable
  without access control, ether withdrawable by anyone (caller-keyed accounting is recognised),
  state-changing functions callable by anyone, storage-bounded loops, calls in loops, `tx.origin`,
  `selfdestruct` (also when it sits in a helper behind a deadline, where the first caller after
  the deadline collects the balance), payout amounts computed with wrapping arithmetic from an
  unbounded parameter on pre-0.8 compilers, authorisation checks whose failing side returns
  normally instead of reverting (pre-0.4 modifiers, `if (!isOwner(msg.sender)) return;`),
  reverse-quoted amounts (the caller fixes the shares it mints or the tokens it withdraws while
  the amount it gives is computed through a division and only required to be nonzero: the
  Balancer V1 `joinswapPoolAmountOut` drain; forward-quoted joins are not flagged). Findings
  are ranked by severity and then confidence, a callee the function first looks up in storage
  (`require(isBound[token])`) is a registry entry rather than a caller-chosen contract, checking
  a token's `transfer` result is not "trusting the callee", loops over a storage counter the
  contract caps at a constant are informational, and lock-protected call-then-write paths are
  reported once for the contract rather than once per function, the Vyper 0.2.15–0.3.0 reentrancy-lock bug, locked
  ether, unprotected upgrades,
  proxy detection (EIP-1967 / beacon / ZeppelinOS / EIP-1167 / storage-slot) with on-chain
  implementation resolution, known compiler bugs for the detected solc version. Rules look
  through internal helpers (a call in a shared `_safeTransfer` is attributed to every external
  function that reaches it, with the helper's arguments substituted and its memory replayed, so
  `transferFrom(arg1, …)` is seen with the caller's actual `from`), and findings are folded per
  defect: one entry per rule and function, with the number of sites, and one entry for a helper
  shared by several functions. Each finding carries severity, confidence, the function and
  program counter, evidence lines and a recommendation; the risk score weighs the worst finding
  by its confidence. Markdown and JSON. Recall is measured on 24 known-exploited contracts
  (see *Accuracy*).
  Two passes read across functions. *Access control by intent*: when several state-changing
  functions compare `msg.sender` against the same slot, that is the contract's policy, and a
  state-changing function without the check that still does what the gated ones do (sends ether
  to a stored address, self-destructs, delegatecalls a stored address, writes a slot otherwise
  written only behind the check) is reported as `inconsistent-access-control`. *Attack chains*:
  a write anyone can make (`owner = msg.sender`, `payee = arg0`) is paired with the function
  that trusts the written slot (an owner-only drain, a payout to `payee`) into one
  `attack-chain` finding with the two steps spelled out; chains open only while a contract is
  uninitialised are reported at medium severity.
* **Verified.** A concrete EVM interpreter executes every basic block from random states and the
  result is compared with the lifted statements (stack, memory, storage, logs, calls, control
  decision). See *Accuracy*.
* **CLI and web app.** `evmdec decompile <address|file|hex>` (with `--lookup` to resolve
  unknown selectors through openchain.xyz / 4byte.directory), `analyze`, `verify`, `disasm`,
  `info`, `cfg`; an axum server with a single-page UI laid out as a drawing set: a title block
  (chain, address, compiler, code size, coverage, findings, risk), an indexed function list, the
  code as the drawing with numbered callouts keyed to the findings beside it (helper calls such
  as `func_0x29d(...)` link to the helper's definition within the current view, with a way back),
  and tabs for the
  report, storage and events, disassembly and JSON. Results are linkable
  (`/?chain=mainnet&address=0x…`), the page follows the system colour scheme with a manual
  override, and it meets WCAG 2.2 AA (contrast on both themes, keyboard operation of every
  control, visible focus, live status messages, severity always in words). No third-party
  scripts; the typefaces come from Google Fonts with system fallbacks. The CLI never fails on an input: if the decompiler hits an internal error it prints
  the disassembly instead.

## Layout

| path | what |
|---|---|
| `crates/decompiler` (`evmdec`) | the library: `u256`, `keccak`, `disasm`, `metadata`, `cfg` (summary analysis, units), `expr` (hash-consed IR + simplifier), `lift`, `structure`, `emit`, `function`, `sigs`, `decompile`, `analyze`, `interp`, `verify`, `rpc` |
| `crates/cli` (`evmdec`) | command line |
| `crates/server` (`evmdec-server`) | web service + UI (`crates/server/static/index.html`) |
| `testdata/mainnet` | 22 mainnet contracts (runtime bytecode + Sourcify ABI) used by the benchmark and the tests |
| `corpus/bench.py`, `corpus/verify_all.sh` | the measurements below |
| `docs/verification.md` | methodology and definitions |
| `rustfmt.toml`, `.claude/agents/rust-style-reviewer.md` | code style: Google's Rust style guide (see below) |

## Code style

The Rust crates follow [Google's Rust style guide](https://google.github.io/styleguide/rustguide.html).
`rustfmt.toml` carries the guide's formatter settings that are stable on the current toolchain
(`max_width = 100`); the guide's remaining rules (one `use` per module, no glob imports, free
functions called through their module, `expect` over `unwrap`, pattern matching over
check-then-unwrap, enums over `bool` parameters, documented public items, the standard operator
traits rather than `shl`/`div`-style inherent methods, no `catch_unwind` except as documented
defense in depth) are enforced by review. The crate root turns on `#![warn(missing_docs)]`, and
`cargo clippy --all-targets` is kept at zero warnings.

`.claude/agents/rust-style-reviewer.md` is a Claude Code agent that reviews a change against the
guide and reports findings as `path:line`, rule, fix. Ask for it by name (`rust-style-reviewer`)
before committing Rust changes.

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
four things, three of them on 22 unmodified mainnet contracts (solc 0.4.18–0.8.17, Vyper 0.2.4 and 0.3.9;
WETH, USDT, USDC proxy + implementation, Uniswap V2 router/pair, Uniswap V3 factory, Permit2,
Universal Router, 1inch v5, Seaport 1.5, Gnosis Safe, Compound cETH, MakerDAO Vat, Aave v3 pool
proxy, ENS registry, Lido stETH proxy, Multicall3, Curve 3pool and TriCrypto-NG, the CREATE2
deployer, UNI). Everything is reproducible with `corpus/bench.py`, `corpus/verify_all.sh` and `corpus/vuln_bench.py`
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

### 4. Analyzer recall on known-exploited contracts

`testdata/vuln` holds the unmodified runtime bytecode of 24 contracts whose exploits are public
(The DAO, Rubixi, King of the Ether, GovernMental, Fomo3D, BEC, SMT, PoWH, SpankChain, Lendf.me,
Bancor 2020, Opyn, Pickle, Furucombo, MISO, Cream crAMP, Visor, Umbrella, Revest, Anyswap 2022,
Poly Network, Curve pETH/Vyper lock bug, Nomad, BOB_POOL on Ethereum Classic). `testdata/vuln/manifest.json` names, for each,
the rule ids any of which must fire at or above a minimum severity for the bug to count as
found, and `corpus/vuln_bench.py` runs the analyzer over the set and over the 22 audited
mainnet contracts above:

| | |
|---|---|
| known bugs found | **23 / 23** (Nomad's bug is an upgrade-time state error outside bytecode patterns and is listed but not counted) |
| high/critical findings on the 22 audited contracts | 34, almost all on contracts whose purpose is to execute caller-supplied calls (Multicall3, 1inch, Gnosis Safe, Seaport) |

The analyzer is heuristic: findings are leads with a confidence level, and the audited corpus is
the running false-positive budget for every rule change.

### 5. What the numbers do not cover

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
* Dynamic-type ABI encoding is folded where the compiler's idiom is recognised (`string`
  literals and storage strings print as `return "…"` / `return name;`, copy loops become
  `mem[a:+n] = mem[b:+n]`); other dynamic encodings are shown as the memory operations the
  compiler emitted rather than as `abi.encode`.
* Vyper internal calls pass arguments through fixed memory slots; the lifter forgets memory
  across such calls, so some values in Vyper output print as `mem[0x…]` reads where the
  analyzer (which replays the callee) sees the value.
* The analyzer is heuristic: findings carry a confidence level and should be read as leads.

## License

MIT.
