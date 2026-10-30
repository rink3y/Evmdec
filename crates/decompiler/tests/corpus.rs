//! Integration tests over the mainnet corpus in `testdata/mainnet`.

use std::path::PathBuf;

fn corpus() -> Vec<(String, Vec<u8>)> {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testdata/mainnet");
    let mut out = Vec::new();
    for e in std::fs::read_dir(&dir).expect("testdata/mainnet") {
        let p = e.unwrap().path();
        if p.extension().is_some_and(|x| x == "hex") {
            let s = std::fs::read_to_string(&p).unwrap();
            out.push((
                p.file_stem().unwrap().to_string_lossy().into_owned(),
                evmdec::hex::decode(s.trim()).unwrap(),
            ));
        }
    }
    assert!(out.len() >= 20, "corpus missing");
    out
}

#[test]
fn every_contract_decompiles_with_full_jump_resolution() {
    for (name, code) in corpus() {
        let c = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default());
        assert!(!c.source.is_empty(), "{name}: empty output");
        assert!(
            c.stats.external_functions + c.stats.internal_functions > 0 || code.len() < 100,
            "{name}: no functions"
        );
        // The Uniswap V3 factory embeds the pool's creation code as data; its "jumps" are not code.
        if name != "univ3_factory" {
            assert_eq!(c.stats.unresolved_jumps, 0, "{name}: unresolved jumps");
            assert!(
                c.stats.covered_blocks * 100 >= c.stats.code_blocks * 90,
                "{name}: coverage {}/{}",
                c.stats.covered_blocks,
                c.stats.code_blocks
            );
        }
        let _ = evmdec::analyze::analyze(&c);
    }
}

#[test]
fn selectors_match_verified_abis() {
    // Compare against the Sourcify ABIs shipped next to the bytecode.
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testdata/mainnet");
    let mut total = 0;
    let mut found = 0;
    for (name, code) in corpus() {
        let abi_path = dir.join(format!("{name}.abi.json"));
        let Ok(txt) = std::fs::read_to_string(&abi_path) else {
            continue;
        };
        let v: serde_json::Value = serde_json::from_str(&txt).unwrap();
        let Some(abi) = v.get("abi").and_then(|a| a.as_array()) else {
            continue;
        };
        let c = evmdec::decompile::decompile(
            &code,
            &evmdec::decompile::Options {
                no_sigs: true,
                ..Default::default()
            },
        );
        let ours: std::collections::HashSet<String> = c
            .functions
            .iter()
            .filter_map(|f| f.selector.clone())
            .collect();
        for item in abi {
            if item["type"] != "function" {
                continue;
            }
            let sig = canonical(item);
            let sel = format!("{:#010x}", evmdec::keccak::selector_u32(&sig));
            total += 1;
            if ours.contains(&sel) {
                found += 1;
            } else {
                eprintln!("{name}: missing {sig} {sel}");
            }
        }
    }
    assert!(total > 400);
    assert!(found * 100 >= total * 98, "selector recall {found}/{total}");
}

fn canonical(item: &serde_json::Value) -> String {
    fn ty(t: &serde_json::Value) -> String {
        let s = t["type"].as_str().unwrap_or("");
        if s.starts_with("tuple") {
            let inner: Vec<String> = t["components"]
                .as_array()
                .map(|c| c.iter().map(ty).collect())
                .unwrap_or_default();
            format!(
                "({}){}",
                inner.join(","),
                s.strip_prefix("tuple").unwrap_or(s)
            )
        } else {
            s.to_string()
        }
    }
    let inputs: Vec<String> = item["inputs"]
        .as_array()
        .map(|a| a.iter().map(ty).collect())
        .unwrap_or_default();
    format!(
        "{}({})",
        item["name"].as_str().unwrap_or(""),
        inputs.join(",")
    )
}

#[test]
fn oracle_finds_no_mismatch_on_weth_and_permit2() {
    for name in ["weth9", "permit2", "curve_tricrypto_ng"] {
        let code = corpus().into_iter().find(|(n, _)| n == name).unwrap().1;
        let info = evmdec::metadata::analyze(&code);
        let st = evmdec::verify::verify(
            &info.runtime,
            &evmdec::verify::VerifyOptions {
                runs: 3,
                seed: 7,
                verbose: false,
            },
        );
        assert_eq!(st.mismatch, 0, "{name}: {:?}", st.mismatches);
        assert!(
            st.blocks_verified * 100 >= st.blocks * 75,
            "{name}: only {}/{} blocks verified",
            st.blocks_verified,
            st.blocks
        );
    }
}

#[test]
fn interpreter_matches_known_semantics() {
    // 0x60 0x01 0x60 0x02 0x01 (PUSH1 1 PUSH1 2 ADD) then STOP
    let code = [0x60, 0x01, 0x60, 0x02, 0x01, 0x00];
    let mut rng = evmdec::interp::Rng::new(1);
    let host = evmdec::interp::Host::random(&mut rng);
    let mut m = evmdec::interp::Machine::new(&code, &host);
    let out = m.run_block(0, code.len());
    assert_eq!(out, evmdec::interp::Outcome::Stop);
    assert_eq!(m.stack, vec![evmdec::U256::from_u64(3)]);
}

#[test]
fn creation_code_is_split_and_minimal_proxy_detected() {
    // EIP-1167 clone pointing at 0xbebebe...
    let hex = "363d3d373d3d3d363d73bebebebebebebebebebebebebebebebebebebebe5af43d82803e903d91602b57fd5bf3";
    let code = evmdec::hex::decode(hex).unwrap();
    assert_eq!(
        evmdec::rpc::minimal_proxy_target(&code).as_deref(),
        Some("0xbebebebebebebebebebebebebebebebebebebebe")
    );
    let c = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default());
    assert!(c.source.contains("delegatecall"));
    // A creation wrapper around it: PUSH1 len PUSH1 off PUSH1 0 CODECOPY PUSH1 len PUSH1 0 RETURN
    let rt = code.clone();
    let mut creation = vec![
        0x60,
        rt.len() as u8,
        0x60,
        0x0c,
        0x60,
        0x00,
        0x39,
        0x60,
        rt.len() as u8,
        0x60,
        0x00,
        0xf3,
    ];
    creation.extend_from_slice(&rt);
    let info = evmdec::metadata::analyze(&creation);
    assert_eq!(info.kind, evmdec::metadata::CodeKind::Creation);
    assert_eq!(info.runtime, rt);
}

/// `a && b` compiles to `v = a; if (a) { v = b }`; the structurer must print `&&`, not `||`.
#[test]
fn short_circuit_and_is_not_inverted() {
    fn asm(src: &str) -> Vec<u8> {
        let mut out: Vec<u8> = Vec::new();
        let mut labels = std::collections::HashMap::new();
        let mut fixups: Vec<(usize, String)> = Vec::new();
        let opcodes: std::collections::HashMap<&str, u8> = (0u8..=255)
            .filter_map(|o| evmdec::opcode::info(o).map(|i| (i.name, o)))
            .collect();
        for tok in src.split_whitespace() {
            if let Some(l) = tok.strip_prefix(':') {
                labels.insert(l.to_string(), out.len());
            } else if let Some(l) = tok.strip_prefix('@') {
                fixups.push((out.len(), l.to_string()));
                out.extend_from_slice(&[0, 0]);
            } else if let Some(h) = tok.strip_prefix("0x") {
                out.extend_from_slice(&evmdec::hex::decode(h).unwrap());
            } else {
                out.push(
                    *opcodes
                        .get(tok)
                        .unwrap_or_else(|| panic!("unknown mnemonic {tok}")),
                );
            }
        }
        for (pos, l) in fixups {
            let t = labels[&l] as u16;
            out[pos] = (t >> 8) as u8;
            out[pos + 1] = t as u8;
        }
        out
    }
    // require(arg0 > 0 && arg0 <= 100)
    let code = asm("PUSH1 0x80 PUSH1 0x40 MSTORE PUSH1 0x00 CALLDATALOAD PUSH1 0xe0 SHR PUSH4 0xaaaaaaaa EQ PUSH2 @f JUMPI PUSH1 0x00 DUP1 REVERT :f JUMPDEST PUSH1 0x04 CALLDATALOAD PUSH1 0x00 DUP2 GT DUP1 ISZERO PUSH2 @end JUMPI POP PUSH1 0x65 DUP2 LT :end JUMPDEST SWAP1 POP PUSH2 @ok JUMPI PUSH1 0x00 DUP1 REVERT :ok JUMPDEST STOP");
    let c = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default());
    assert!(
        c.source.contains(" && "),
        "expected a conjunction:\n{}",
        c.source
    );
    assert!(
        !c.source.contains(" || "),
        "no disjunction in this function:\n{}",
        c.source
    );
}

/// A solc 0.8 contract whose revert reasons go through a shared `revert(ptr, sub(end, ptr))`
/// tail, whose arithmetic is the compiler's checked helpers, and whose loop carries several
/// variables at once (BOB_POOL on Ethereum Classic).
#[test]
fn solc8_reverts_checked_arithmetic_and_loops_read_as_source() {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testdata/vuln/bob_pool.hex");
    let code = evmdec::hex::decode(std::fs::read_to_string(p).unwrap().trim()).unwrap();
    let c = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default());
    let src = &c.source;
    // Revert reasons decoded through the shared tail, including 31- and 34-byte strings.
    for s in [
        "\"No stake in game\"",
        "\"Input ETC must be larger then 0\"",
        "\"Cant remove more then total staked\"",
        "\"Input Token amount must be larger then 100\"",
    ] {
        assert!(src.contains(s), "missing {s}");
    }
    assert!(
        !src.contains("0x8c379a0"),
        "raw Error(string) selector left in the output"
    );
    // Checked arithmetic helpers are inlined and their panics are not printed on solc 0.8.
    assert!(
        !src.contains("Panic(arithmetic overflow)"),
        "compiler panic printed"
    );
    assert!(
        src.contains("stor_7 - stor_8[msg.sender]"),
        "checked_sub not inlined"
    );
    // The balanceOf helper returns the call's return data, not a raw memory read.
    assert!(
        src.contains("return (returndata_1[0]);"),
        "return data not resolved"
    );
    // ABI size checks print unsigned; address validators are not printed.
    assert!(src.contains("require(msg.data.length >= 36);"));
    assert!(!src.contains("int256(msg.data.length"));
    assert!(!src.contains("address(arg0))"), "ABI validator printed");
    // Unknown events are named by their topic.
    assert!(src.contains("emit Event_22e25c6d("));
    // The loop is a `while (i < steps)` whose parallel copies are ordered so that no copy reads a
    // variable already overwritten above it.
    let helper = src
        .split("function func_0x1331(")
        .nth(1)
        .expect("pricing helper");
    let (head, rest) = helper.split_once("while (").expect("while loop");
    assert!(!head.contains("while ("), "one loop expected");
    let cond = rest.split(") {").next().unwrap();
    assert!(
        cond.split(" < ").count() == 2
            && cond
                .chars()
                .all(|c| c.is_alphanumeric() || c == ' ' || c == '<'),
        "loop condition: {cond}"
    );
    let body = rest
        .split_once(") {")
        .expect("loop body opens")
        .1
        .split('}')
        .next()
        .expect("loop body closes");
    let lines: Vec<&str> = body
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .collect();
    // Two shared sub-expressions bound once each, then the four loop-carried updates.
    assert_eq!(lines.len(), 6, "loop body: {body}");
    let words = |s: &str| {
        s.split(|c: char| !c.is_alphanumeric())
            .filter(|w| !w.is_empty())
            .map(str::to_string)
            .collect::<Vec<_>>()
    };
    let parsed: Vec<(&str, &str)> = lines
        .iter()
        .map(|l| l.split_once(" = ").expect("an assignment"))
        .collect();
    // A loop-carried copy reads its variable before assigning it; the rest are bindings.
    let is_copy = |i: usize| {
        let var = parsed[i].0;
        parsed[..=i]
            .iter()
            .any(|(_, rhs)| words(rhs).iter().any(|w| w == var))
    };
    let mut assigned: Vec<&str> = Vec::new();
    for (i, (var, rhs)) in parsed.iter().enumerate() {
        if !is_copy(i) {
            continue;
        }
        for a in &assigned {
            assert!(
                !words(rhs).iter().any(|w| w == a),
                "copy reads an overwritten variable: {body}"
            );
        }
        assigned.push(var);
    }
    // No string piece in the inventory.
    assert!(
        !c.strings
            .iter()
            .any(|s| s == "C balance" || s == "r then 100" || s == "NH{q"),
        "{:?}",
        c.strings
    );
}

/// The original multi-owner wallet (Gav Wood's Wallet.sol as deployed on mainnet, no metadata):
/// pre-0.4 modifiers reach the rest of a function both by falling through and by a jump with a
/// return address, the owner list is a fixed-size array, and the pending-operation index is a
/// dynamic array whose data slot the compiler precomputed.
#[test]
fn old_multiowned_wallet_reads_as_source() {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../testdata/regress/parity_wallet_v1.hex");
    let code = evmdec::hex::decode(std::fs::read_to_string(p).unwrap().trim()).unwrap();
    let c = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default());
    let src = &c.source;
    // Dictionary: the wallet's selectors and events are known.
    for s in [
        "function confirm(bytes32 arg0)",
        "function revoke(bytes32 arg0)",
        "function changeOwner(address arg0, address arg1)",
        "function kill(address arg0)",
        "event ConfirmationNeeded(",
        "event MultiTransact(",
    ] {
        assert!(src.contains(s), "missing {s}");
    }
    assert!(
        !src.contains("unknown signature"),
        "every selector of the wallet is in the dictionary"
    );
    // Storage: `uint[256] m_owners` at slot 2, `bytes32[] m_pendingIndex` at slot 0x104 with
    // its elements at keccak256(0x104) + i; no variable named after the hash.
    assert!(
        src.contains("uint256[] stor_2; // slot 0x2, fixed-size array"),
        "{src}"
    );
    assert!(
        src.contains("stor_2[isOwner[address(arg0)]]"),
        "owners[ownerIndex]"
    );
    assert!(
        src.contains("bytes32[] stor_260; // slot 0x104"),
        "pending index array of hashes"
    );
    assert!(
        src.contains("stor_260[prev_stor_260_length]"),
        "pendingIndex[pending.index]"
    );
    assert!(
        !src.contains("stor_0x4c0be602"),
        "precomputed hash printed as a variable"
    );
    // A slot read before it is incremented keeps its old value under a temporary; the bare slot
    // of a dynamic array is its length.
    assert!(
        src.contains("uint256 prev_stor_260_length = stor_260.length;"),
        "{src}"
    );
    assert!(src.contains("stor_260.length = prev_stor_260_length + 1;"));
    // The type solver: `execute` returns the operation hash it computes, `hasConfirmed` a flag,
    // and the pending-operation mappings are keyed by hash.
    assert!(
        src.contains("function execute(address arg0, uint256 arg1, bytes arg2) external payable returns (bytes32)"),
        "{src}"
    );
    assert!(src.contains(
        "function hasConfirmed(bytes32 arg0, address arg1) external payable returns (bool)"
    ));
    assert!(src.contains("mapping(bytes32 => uint256) stor_259;"));
    assert!(src.contains("require(prev_stor_260_length < stor_260.length);"));
    assert!(
        !src.contains("require(stor_260.length < stor_260.length)"),
        "stale read printed as the slot"
    );
    // The scratch loads of the precomputed hash and no-op stores are not printed.
    assert!(!src.contains("code[4056"), "dead CODECOPY printed");
    assert!(!src.contains("mem[0x0] = mem[0x0]"), "no-op store printed");
    // Continuations of modified functions are not printed as separate helpers.
    for h in [
        "func_0x7be",
        "func_0x965",
        "func_0xa05",
        "func_0xadb",
        "func_0xbdd",
    ] {
        assert!(
            !src.contains(&format!("function {h}(")),
            "{h} printed twice"
        );
    }
    // Every temporary is declared before it is used, in the function that uses it.
    for body in src.split("\n    function ").skip(1) {
        let mut declared: Vec<String> = Vec::new();
        for line in body.lines() {
            for (i, _) in line.match_indices('t') {
                let rest = &line[i..];
                if i > 0 && line.as_bytes()[i - 1].is_ascii_alphanumeric() {
                    continue;
                }
                let name: String = rest
                    .chars()
                    .take_while(|ch| ch.is_ascii_alphanumeric())
                    .collect();
                if name.len() < 2 || !name[1..].chars().all(|ch| ch.is_ascii_digit()) {
                    continue;
                }
                if line.contains(&format!("uint256 {name} =")) {
                    declared.push(name);
                } else {
                    assert!(
                        declared.contains(&name),
                        "{name} used before declaration:\n{line}"
                    );
                }
            }
        }
    }
    // Report: one real reentrancy per path (confirm's delete-after-call), behind the owner
    // gate, and the silent modifier failure.
    let r = evmdec::analyze::analyze(&c);
    let re: Vec<_> = r.findings.iter().filter(|f| f.id == "reentrancy").collect();
    assert_eq!(
        re.len(),
        2,
        "{:?}",
        re.iter().map(|f| &f.function).collect::<Vec<_>>()
    );
    assert!(re
        .iter()
        .all(|f| f.severity == evmdec::analyze::Severity::Medium && f.sites == 1));
    assert!(r.findings.iter().any(|f| f.id == "silent-auth-failure"));
}

/// Balancer V1 BPool (solc 0.5.12): a `_lock_` modifier released through a packed-field mask,
/// a `_logs_` modifier that ABI-encodes `msg.data` into an event, pool-token list elements
/// addressed as `keccak256(9) - 1`, and the 2026 reverse-quote rounding drain.
#[test]
fn balancer_bpool_reads_as_source() {
    let p =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testdata/regress/balancer_bpool.hex");
    let code = evmdec::hex::decode(std::fs::read_to_string(p).unwrap().trim()).unwrap();
    let c = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default());
    let src = &c.source;
    for s in [
        "function joinswapPoolAmountOut(address arg0, uint256 arg1, uint256 arg2)",
        "function swapExactAmountIn(",
        "function calcSingleInGivenPoolOut(",
        "event LOG_SWAP(",
    ] {
        assert!(src.contains(s), "missing {s}");
    }
    assert!(
        !src.contains("unknown signature"),
        "BPool selectors are in the dictionary"
    );
    // The lock release prints as the bool field, not as a whole-slot mask.
    assert!(src.contains("stor_5_1 = false;"), "{src}");
    assert!(!src.contains("& 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff"));
    // `_logs_`: emit of the ABI-encoded calldata, with `msg.sig` as a topic.
    assert!(
        src.contains("log2(msg.sig, msg.sender, abi.encode(msg.data));"),
        "{src}"
    );
    assert!(
        !src.contains("mem[mem[0x40] + 32] = msg.data.length;"),
        "encoding stores printed"
    );
    // `_tokens[_tokens.length - 1]` through the folded hash constant.
    assert!(src.contains("stor_9[stor_9.length - 1]"), "{src}");
    assert!(!src.contains("0x6e1540171b6c0c960b71a7020d9f60077f6af931a8bbf590da0223dacf75c7ae"));
    let r = evmdec::analyze::analyze(&c);
    // The lock is recognised: every reentrancy entry is informational.
    assert!(r
        .findings
        .iter()
        .filter(|f| f.id == "reentrancy")
        .all(|f| f.severity == evmdec::analyze::Severity::Info));
    // The reverse-quote rounding on both single-sided paths.
    let rq: Vec<String> = r
        .findings
        .iter()
        .filter(|f| f.id == "reverse-quote-rounding")
        .map(|f| f.function.clone().unwrap_or_default())
        .collect();
    assert!(
        rq.iter().any(|f| f.starts_with("joinswapPoolAmountOut")),
        "{rq:?}"
    );
    assert!(
        rq.iter().any(|f| f.starts_with("exitswapExternAmountOut")),
        "{rq:?}"
    );
    assert!(
        !rq.iter().any(|f| f.starts_with("joinswapExternAmountIn")),
        "forward-quoted join must not be flagged: {rq:?}"
    );
}

/// A solc 0.4 contract (a lobby-created "tribe" on Ethereum Classic) whose `BuyIn(address)`
/// reassigns its parameter on one path: control-flow recovery used to duplicate the whole body
/// per path. Its `members`/`waiting` state is an `address[]` and a `mapping(address => bool)`
/// written through the compiler's resize helper and byte masks.
#[test]
fn tribe_reads_as_source_and_is_rated_by_its_logic() {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testdata/regress/tribe.hex");
    let code = evmdec::hex::decode(std::fs::read_to_string(p).unwrap().trim()).unwrap();
    let c = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default());
    let src = &c.source;
    for s in [
        "mapping(address => bool) stor_3;",
        "address[] stor_4;",
        "require(!stor_3[address(v1)]);",
        "stor_4.push(address(v1));",
        "stor_3[address(v1)] = true;",
        "if (stor_4.length < stor_7) {",
        // `find`: one loop, no peeled first iteration, parameters not turned into phis.
        "while (v1 < stor[arg0]) {",
    ] {
        assert!(src.contains(s), "missing {s}\n{src}");
    }
    // One body per function: `BuyIn` and `Refund` each self-destruct once.
    assert_eq!(src.matches("selfdestruct(msg.sender);").count(), 2, "{src}");
    let r = evmdec::analyze::analyze(&c);
    // The destructs come after the payout: no Critical. The real risk is the payout loop over an
    // array anyone can extend.
    assert!(
        r.findings
            .iter()
            .all(|f| f.severity != evmdec::analyze::Severity::Critical),
        "{:?}",
        r.findings
            .iter()
            .map(|f| (&f.id, f.severity))
            .collect::<Vec<_>>()
    );
    assert!(
        r.findings
            .iter()
            .any(|f| f.id == "blocking-payout-loop"
                && f.severity == evmdec::analyze::Severity::Medium)
    );
    assert!(r
        .findings
        .iter()
        .any(|f| f.id == "selfdestruct" && f.severity == evmdec::analyze::Severity::Low));
    assert!(
        !r.findings
            .iter()
            .any(|f| f.id == "unprotected-ether-withdrawal"),
        "waiting[user] is the caller's accounting"
    );
}

/// The lobby that deploys tribes from its own embedded code and calls the new contract: that
/// callee is as fixed as the contract itself, and the embedded code's metadata is not a string.
#[test]
fn lobby_calls_into_its_own_deployment() {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testdata/regress/lobby.hex");
    let code = evmdec::hex::decode(std::fs::read_to_string(p).unwrap().trim()).unwrap();
    let c = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default());
    let src = &c.source;
    assert!(src.contains("deployed_2 = create("), "{src}");
    // The mapping entry is an address: no preserving mask.
    assert!(src.contains("stor_0[stor_1] = deployed_2;"), "{src}");
    assert!(c.strings.is_empty(), "{:?}", c.strings);
    let r = evmdec::analyze::analyze(&c);
    assert!(r
        .findings
        .iter()
        .all(|f| f.severity == evmdec::analyze::Severity::Info));
    assert!(r.findings.iter().any(|f| f.id == "reentrancy-fixed-callee"));
}

#[test]
fn types_follow_values_through_helpers_and_range_checks() {
    // Vyper validates decoded values by range checks; solc helpers decode and mask them. With the
    // dictionary disabled every type below comes from the solver.
    let opts = evmdec::decompile::Options {
        no_sigs: true,
        ..evmdec::decompile::Options::default()
    };
    let by_name = |name: &str| -> Vec<u8> {
        corpus()
            .into_iter()
            .find(|(n, _)| n == name)
            .map(|(_, code)| code)
            .expect("fixture present")
    };
    let curve = evmdec::decompile::decompile(&by_name("curve_3pool_vyper"), &opts).source;
    assert!(
        curve.contains(
            "function func_3df02124(int128 arg0, int128 arg1, uint256 arg2, uint256 arg3)"
        ),
        "{curve}"
    );
    assert!(curve.contains("function func_6b441a40(address arg0) external"));
    assert!(curve.contains("function func_8da5cb5b() external view returns (address)"));
    let compound = evmdec::decompile::decompile(&by_name("compound_ceth"), &opts).source;
    // The 4-byte tail of a call payload is a bare `& 0xffffffff`, not a uint32 parameter.
    assert!(
        compound
            .contains("function func_a9059cbb(address arg0, uint256 arg1) external returns (bool)"),
        "{compound}"
    );
    assert!(
        compound.contains("function func_0xe3c(address arg0, address arg1, uint256 arg2) internal")
    );
    let ens = evmdec::decompile::decompile(&by_name("ens_registry"), &opts).source;
    assert!(ens.contains("mapping(bytes32 => "), "{ens}");
    assert!(ens.contains("external returns (bytes32)"), "{ens}");
}
