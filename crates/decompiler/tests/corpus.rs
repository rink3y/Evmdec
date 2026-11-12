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
    let hex = "363d3d373d3d3d363d73bebebebebebebebebebebebebebebebebebebebe5af43d82803e903d91602b57fd5bf3";
    let code = evmdec::hex::decode(hex).unwrap();
    assert_eq!(
        evmdec::rpc::minimal_proxy_target(&code).as_deref(),
        Some("0xbebebebebebebebebebebebebebebebebebebebe")
    );
    let c = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default());
    assert!(c.source.contains("delegatecall"));
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
    assert!(
        !src.contains("Panic(arithmetic overflow)"),
        "compiler panic printed"
    );
    assert!(
        src.contains("stor_7 - stor_8[msg.sender]"),
        "checked_sub not inlined"
    );
    assert!(
        src.contains("return (returndata_1[0]);"),
        "return data not resolved"
    );
    assert!(src.contains("require(msg.data.length >= 36);"));
    assert!(!src.contains("int256(msg.data.length"));
    assert!(!src.contains("address(arg0))"), "ABI validator printed");
    assert!(src.contains("emit Event_22e25c6d("));
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
    for s in [
        "function confirm(bytes32 key)",
        "function revoke(bytes32 key)",
        "function changeOwner(address account, address account2)",
        "function kill(address recipient)",
        "event ConfirmationNeeded(",
        "event MultiTransact(",
    ] {
        assert!(src.contains(s), "missing {s}");
    }
    assert!(
        !src.contains("unknown signature"),
        "every selector of the wallet is in the dictionary"
    );
    assert!(
        src.contains("uint256[] stor_2; // slot 0x2, fixed-size array"),
        "{src}"
    );
    assert!(
        src.contains("stor_2[isOwner[address(account)]]"),
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
    assert!(
        src.contains("uint256 prev_stor_260_length = stor_260.length;"),
        "{src}"
    );
    assert!(src.contains("stor_260.length = prev_stor_260_length + 1;"));
    assert!(
        src.contains("function execute(address target, uint256 amount, bytes arg2) external payable returns (bytes32)"),
        "{src}"
    );
    assert!(src.contains(
        "function hasConfirmed(bytes32 arg0, address account) external payable returns (bool)"
    ));
    assert!(src.contains("mapping(bytes32 => Struct_259) stor_259;"));
    assert!(src.contains("require(prev_stor_260_length < stor_260.length);"));
    assert!(
        !src.contains("require(stor_260.length < stor_260.length)"),
        "stale read printed as the slot"
    );
    assert!(!src.contains("code[4056"), "dead CODECOPY printed");
    assert!(!src.contains("mem[0x0] = mem[0x0]"), "no-op store printed");
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
        "function joinswapPoolAmountOut(address target, uint256 amount, uint256 arg2)",
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
    assert!(src.contains("stor_5_1 = false;"), "{src}");
    assert!(!src.contains("& 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff"));
    assert!(
        src.contains("log2(msg.sig, msg.sender, abi.encode(msg.data));"),
        "{src}"
    );
    assert!(
        !src.contains("mem[mem[0x40] + 32] = msg.data.length;"),
        "encoding stores printed"
    );
    assert!(src.contains("stor_9[stor_9.length - 1]"), "{src}");
    assert!(!src.contains("0x6e1540171b6c0c960b71a7020d9f60077f6af931a8bbf590da0223dacf75c7ae"));
    let r = evmdec::analyze::analyze(&c);
    assert!(r
        .findings
        .iter()
        .filter(|f| f.id == "reentrancy")
        .all(|f| f.severity == evmdec::analyze::Severity::Info));
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
        "while (v1 < stor[arg0]) {",
    ] {
        assert!(src.contains(s), "missing {s}\n{src}");
    }
    assert_eq!(src.matches("selfdestruct(msg.sender);").count(), 2, "{src}");
    let r = evmdec::analyze::analyze(&c);
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
    assert!(
        compound.contains(
            "function func_a9059cbb(address account, uint256 arg1) external returns (bool)"
        ),
        "{compound}"
    );
    assert!(compound
        .contains("function func_0xe3c(address account, address account2, uint256 arg2) internal"));
    let ens = evmdec::decompile::decompile(&by_name("ens_registry"), &opts).source;
    assert!(ens.contains("mapping(bytes32 => "), "{ens}");
    assert!(ens.contains("external returns (bytes32)"), "{ens}");
}

/// Evidence the bytecode carries beyond masks: a Vyper range check whose failing side reverts,
/// an index scaled to a word offset, a word another contract returned and validated, the
/// arguments of `ecrecover`, a block hash, and a comparison with a text literal.
#[test]
fn types_use_validators_precompiles_and_literals() {
    let opts = evmdec::decompile::Options {
        no_sigs: true,
        ..evmdec::decompile::Options::default()
    };
    let source = |name: &str| -> String {
        let code = corpus()
            .into_iter()
            .find(|(n, _)| n == name)
            .map(|(_, code)| code)
            .expect("fixture present");
        evmdec::decompile::decompile(&code, &opts).source
    };
    let tricrypto = source("curve_tricrypto_ng");
    for header in [
        "function func_a9059cbb(address arg0, uint256 arg1) external returns (bool)",
        "function func_cab4d3db() external view returns (address)",
        "function func_59189017(uint256 arg0) external view returns (uint256)",
        "function func_ddca3f43() external view returns (uint256)",
    ] {
        assert!(tricrypto.contains(header), "missing `{header}`");
    }
    let uni = source("uni_token");
    assert!(
        uni.contains("uint256 deadline, uint8 v, bytes32 r, bytes32 s) external"),
        "ecrecover arguments"
    );
    let multicall = source("multicall3");
    assert!(
        multicall.contains("function func_ee82ac5e(uint256 arg0) external view returns (bytes32)"),
        "blockhash result"
    );
    let vat = source("maker_vat");
    assert!(
        vat.contains("function func_1a0b287e(uint256 key, bytes32 arg1, uint256 value) external"),
        "text literal comparison"
    );
}

/// What a known signature declares about a calldata word reaches the storage it keys.
#[test]
fn declared_types_flow_into_storage() {
    use evmdec::types::{declared_words, Ty};
    let params = |list: &[&str]| -> Vec<String> { list.iter().map(|s| s.to_string()).collect() };
    assert_eq!(
        declared_words(&params(&[
            "bytes32", "address", "uint256", "uint64", "bytes", "bool"
        ])),
        vec![
            (0, Ty::Bytes(32)),
            (1, Ty::Address),
            (3, Ty::Uint(64)),
            (5, Ty::Bool)
        ]
    );
    assert_eq!(
        declared_words(&params(&["address", "(uint256,address)", "bool"])),
        vec![(0, Ty::Address)],
        "a static tuple takes several words and ends the count"
    );
    assert_eq!(declared_words(&params(&["uint256[3]", "address"])), vec![]);
}

/// Names the code implies where no signature supplies one: storage by role, helpers by what
/// they do, parameters by how they are used.
#[test]
fn defaults_give_way_to_names_the_code_implies() {
    let source = |name: &str| -> String {
        let code = corpus()
            .into_iter()
            .find(|(n, _)| n == name)
            .map(|(_, code)| code)
            .expect("fixture present");
        evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default()).source
    };
    let usdt = source("usdt");
    for line in [
        "address owner; // slot 0x0 bytes 0..20",
        "uint256 totalSupply; // slot 0x1",
        "mapping(address => uint256) balances; // slot 0x2",
        "mapping(address => mapping(address => uint256)) allowances; // slot 0x5",
        "function _transfer(address from, address to, uint256 amount) internal",
        "function _pause() internal",
    ] {
        assert!(usdt.contains(line), "usdt: missing `{line}`");
    }
    let pair = source("univ2_pair");
    assert!(
        pair.contains("uint256 reentrancyLock; // slot 0xc"),
        "lock by its toggling"
    );
    let weth = source("weth9");
    for line in [
        "function transferFrom(address from, address to, uint256 amount) external",
        "function balanceOf(address account) external view",
        "function _withdrawal(uint256 amount) internal",
    ] {
        assert!(weth.contains(line), "weth9: missing `{line}`");
    }
    let uni = source("uni_token");
    assert!(
        uni.contains("uint256 deadline, uint8 v, bytes32 r, bytes32 s) external"),
        "signature parts and deadline are named"
    );
}

/// A statement in a helper shared by two external functions is one finding, whatever each
/// caller names the argument it passes: the Safe's two module entry points reach the same
/// call and the same delegatecall.
#[test]
fn a_shared_helper_site_is_one_finding_under_any_parameter_names() {
    let code = corpus()
        .into_iter()
        .find(|(n, _)| n == "safe_l2_130")
        .map(|(_, code)| code)
        .expect("fixture present");
    let c = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default());
    let report = evmdec::analyze::analyze(&c);
    let shared: Vec<&evmdec::analyze::Finding> = report
        .findings
        .iter()
        .filter(|f| f.id == "arbitrary-delegatecall")
        .filter(|f| f.function.as_deref().is_some_and(|n| n.contains("(+1)")))
        .collect();
    assert_eq!(
        shared.len(),
        1,
        "{:?}",
        report
            .findings
            .iter()
            .map(|f| (&f.id, &f.function))
            .collect::<Vec<_>>()
    );
    assert!(shared[0]
        .description
        .contains("The same code is reached from"));
}

/// Every allocation moves the free memory pointer, including one made inside a helper the
/// lifter inlines: three structs decoded from calldata are three blocks, the outer one holding
/// pointers to the other two. Before the pointer updates were kept in the helper's summary, all
/// three were written to the same address.
#[test]
fn allocations_in_inlined_helpers_are_separate_blocks() {
    let path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testdata/vuln/fence_usdc_pool.hex");
    let code = evmdec::hex::decode(std::fs::read_to_string(path).unwrap().trim()).unwrap();
    let src = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default()).source;
    for line in [
        "ptr1 = memory(arg0, arg1, ptr2, arg4, arg5, arg6, arg7, arg8, ptr3);",
        "ptr2 = memory(arg2, arg3);",
        "ptr3 = memory(arg9, arg10, arg11, arg12);",
    ] {
        assert!(src.contains(line), "missing `{line}`");
    }
    assert!(
        !src.contains("mem[mem[0x40]"),
        "the free pointer is never printed as an address of its own"
    );
    assert!(src.contains("// Memory: ptrN is a block"), "legend");
}

/// Payloads that are not a fixed list of words still read as what they are: the calldata a
/// proxy forwards, and a string literal built in memory.
#[test]
fn payloads_and_literals_read_as_values() {
    let source = |name: &str| -> String {
        let code = corpus()
            .into_iter()
            .find(|(n, _)| n == name)
            .map(|(_, code)| code)
            .expect("fixture present");
        evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default()).source
    };
    let proxy = source("usdc_proxy");
    assert!(proxy.contains(".delegatecall(msg.data);"), "{proxy}");
    assert!(!proxy.contains("mem[0:msg.data.length]"), "{proxy}");
    let permit2 = source("permit2");
    assert!(
        permit2.contains("= memory(\"PermitWitnessTransferFrom(TokenPermissions permitted,"),
        "string literal block"
    );
    let uni = source("uni_token");
    assert!(
        uni.contains("= ecrecover.staticcall(abi.encode("),
        "precompile by name"
    );
}

/// Elements with members at several slot offsets are declared as structs and read by member:
/// plain members, members packed into one slot, a byte string, and an array and a mapping held
/// inside the element.
#[test]
fn struct_elements_are_declared_and_read_by_member() {
    let source = |path: &str| {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(path);
        let code = evmdec::hex::decode(std::fs::read_to_string(path).unwrap().trim()).unwrap();
        evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default())
    };
    let wallet = source("../../testdata/regress/parity_wallet_v1.hex");
    for line in [
        "struct Struct_264 {",
        "address field0; // slot +0",
        "bytes field2; // slot +2",
        "mapping(bytes32 => Struct_264) stor_264;",
        "stor_264[key].field0.call{value: stor_264[key].field1}",
    ] {
        assert!(wallet.source.contains(line), "wallet: missing `{line}`");
    }
    let pending = wallet
        .storage
        .iter()
        .find(|v| v.name == "stor_259")
        .expect("the pending-operation mapping");
    assert_eq!(pending.ty, "mapping(bytes32 => Struct_259)");
    assert_eq!(pending.members.len(), 3);
    assert!(pending.members.iter().all(|m| m.ty == "uint256"));

    let registry = source("../../testdata/mainnet/ens_registry.hex").source;
    for line in [
        "address field1_0; // slot +1 bytes 0..20",
        "uint64 field1_20; // slot +1 bytes 20..28",
        "mapping(bytes32 => Struct_0) stor_0;",
        "stor_0[key].field1_0",
    ] {
        assert!(registry.contains(line), "registry: missing `{line}`");
    }

    let vat = source("../../testdata/mainnet/maker_vat.hex").source;
    assert!(vat.contains("require(stor_2[key].field1 == 0, \"Vat/ilk-already-init\");"));
    assert!(vat.contains("stor_3[key][address(account)].field0"));

    let roles = source("../../testdata/vuln/miso_batch_impl.hex");
    let role = roles
        .storage
        .iter()
        .find(|v| v.slot == "0x0")
        .expect("the role registry");
    let types: Vec<&str> = role.members.iter().map(|m| m.ty.as_str()).collect();
    assert_eq!(
        types,
        ["address[]", "mapping(address => uint256)", "bytes32"]
    );
    assert!(
        role.members[0].name != "roleMemberCount",
        "a count getter reads the head of the array, it does not name the array"
    );
}

/// Vyper keeps each variable at a fixed memory address, so a word there prints as a local and
/// a word-scaled index from one as an element of the list that starts there. Byte ranges and
/// unaligned addresses stay memory.
#[test]
fn vyper_fixed_addresses_read_as_locals() {
    let path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testdata/vuln/curve_peth_impl.hex");
    let code = evmdec::hex::decode(std::fs::read_to_string(path).unwrap().trim()).unwrap();
    let src = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default()).source;
    for line in [
        "// Memory: loc_N is the variable kept at the fixed memory address 0xN",
        "while (loc_280 < 2) {",
        "loc_240[loc_280] = loc_240[loc_280] + loc_2a0;",
        "identity.call(mem[640:740])",
    ] {
        assert!(src.contains(line), "missing `{line}`");
    }
    assert!(
        !src.contains("mem[0x280]"),
        "an aligned fixed address is a local"
    );
    assert!(src.contains("mem[0x2a4] = "), "an unaligned address is not");
}

/// Types that take evidence from more than one place: a mapping keyed by a hash somewhere types
/// every key of it, a 160-bit field used in arithmetic is an amount and so is what is stored
/// into it, the words of a packed signature and of a typed-data digest are 32-byte words, and
/// a multiplied value is not an account whatever it later flows into.
#[test]
fn types_join_evidence_across_keys_fields_and_layouts() {
    let source = |name: &str| {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../testdata/mainnet")
            .join(name);
        let code = evmdec::hex::decode(std::fs::read_to_string(path).unwrap().trim()).unwrap();
        let opts = evmdec::decompile::Options {
            no_sigs: true,
            ..Default::default()
        };
        evmdec::decompile::decompile(&code, &opts).source
    };
    for (file, header) in [
        (
            "ens_registry.hex",
            "function func_5b0fc9c3(bytes32 key, address arg1) external {",
        ),
        (
            "permit2.hex",
            "function func_87517c45(address account, address account2, uint160 arg2, uint48 arg3)",
        ),
        (
            "permit2.hex",
            "function func_927da105(address account, address account2, address account3) external view returns (uint160, uint48, uint48)",
        ),
        (
            "usdc_impl.hex",
            "uint8 arg4, bytes32 arg5, bytes32 arg6) external {",
        ),
        (
            "univ2_pair.hex",
            "function func_3644e515() external view returns (bytes32) {",
        ),
        (
            "oneinch_v5.hex",
            "function func_62e238bb(bytes arg0, bytes arg1, bytes arg2, uint256 arg3, uint256 arg4, uint256 arg5)",
        ),
    ] {
        assert!(source(file).contains(header), "{file}: missing `{header}`");
    }
}

/// A store to a fixed address is printed only when something that runs afterwards can read
/// it: a later load in the function, a byte range handed on, or an internal function that
/// loads the address before writing it. Values the lifter already forwarded need no store.
#[test]
fn stores_nothing_reads_are_left_out() {
    let source = |path: &str| {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(path);
        let code = evmdec::hex::decode(std::fs::read_to_string(path).unwrap().trim()).unwrap();
        evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default()).source
    };
    let pool = source("../../testdata/vuln/curve_peth_impl.hex");
    let start = pool.find("function get_virtual_price()").expect("the view");
    let body = &pool[start..start + pool[start..].find("\n    }").unwrap()];
    assert!(
        !body.contains("loc_140 = ") && !body.contains("loc_260 = "),
        "locals no one reads after the helper calls are not stored: {body}"
    );
    assert!(
        body.contains("loc_1c0 = ") && body.contains("func_0x3349("),
        "what the helper may still read is: {body}"
    );
    assert!(body.contains("return (ret_3_0 * 1e18 / totalSupply);"));

    assert!(
        pool.contains("loc_220 = loc_220 + 1;\n            if (loc_220 != 2) {"),
        "a counter tested after its increment reads as the counter"
    );
    assert!(
        pool.contains("if (loc_2c0 <= prev_loc_2c0) {"),
        "the value before a store is held in a local where it is compared with the new one"
    );

    let old = source("../../testdata/vuln/kotet.hex");
    assert!(
        !old.contains("mem[0x0] = 6;"),
        "the scratch word of a hash the lifter resolved is not printed"
    );
}
