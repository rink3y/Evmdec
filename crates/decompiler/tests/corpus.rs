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
        assert_eq!(c.stats.unresolved_jumps, 0, "{name}: unresolved jumps");
        for call in c.source.split("func_0x").skip(1) {
            let digits = call.chars().take_while(char::is_ascii_hexdigit).count();
            let helper = format!("function func_0x{}(", &call[..digits]);
            assert!(
                !call[digits..].starts_with('(') || c.source.contains(&helper),
                "{name}: {helper} is called and has no body"
            );
        }
        assert!(
            c.stats.covered_blocks * 100 >= c.stats.code_blocks * 90,
            "{name}: coverage {}/{}",
            c.stats.covered_blocks,
            c.stats.code_blocks
        );
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
    for h in ["func_0x965", "func_0xa05", "func_0xadb", "func_0xbdd"] {
        assert!(src.contains(&format!("{h}(")), "{h} is no longer called");
        assert!(
            src.contains(&format!("function {h}(")),
            "{h} is called and has no body"
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
}

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
}

#[test]
fn tribe_reads_as_source() {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testdata/regress/tribe.hex");
    let code = evmdec::hex::decode(std::fs::read_to_string(p).unwrap().trim()).unwrap();
    let c = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default());
    let src = &c.source;
    for s in [
        "mapping(address => bool) stor_3;",
        "address[] stor_4;",
        "require(!stor_3[address(v2)]);",
        "stor_4.push(address(v2));",
        "stor_3[address(v2)] = true;",
        "if (stor_4.length < stor_7) {",
        "assert(v1 < stor[arg0]);",
    ] {
        assert!(src.contains(s), "missing {s}\n{src}");
    }
    assert_eq!(src.matches("selfdestruct(msg.sender);").count(), 2, "{src}");
}

#[test]
fn lobby_calls_into_its_own_deployment() {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testdata/regress/lobby.hex");
    let code = evmdec::hex::decode(std::fs::read_to_string(p).unwrap().trim()).unwrap();
    let c = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default());
    let src = &c.source;
    assert!(src.contains("deployed_2 = create("), "{src}");
    assert!(src.contains("stor_0[stor_1] = deployed_2;"), "{src}");
    assert!(c.strings.is_empty(), "{:?}", c.strings);
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
        "address owner; // slot +0",
        "address resolver; // slot +1 bytes 0..20",
        "uint64 ttl; // slot +1 bytes 20..28",
        "mapping(bytes32 => Struct_0) stor_0;",
        "stor_0[key].resolver",
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

#[test]
fn vyper_fixed_addresses_read_as_locals() {
    let path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testdata/vuln/curve_peth_impl.hex");
    let code = evmdec::hex::decode(std::fs::read_to_string(path).unwrap().trim()).unwrap();
    let src = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default()).source;
    for line in [
        "// Memory: loc_N is the variable kept at the fixed memory address 0xN",
        "while (true) {\n            require(loc_280 < 2);",
        "loc_240[loc_280] = loc_240[loc_280] + loc_2a0;",
        "identity.call(mem[0x280:0x2e4])",
    ] {
        assert!(src.contains(line), "missing `{line}`");
    }
    assert!(
        !src.contains("mem[0x280]"),
        "an aligned fixed address is a local"
    );
    assert!(src.contains("mem[0x2a4] = "), "an unaligned address is not");
}

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
            "function func_62e238bb((uint256,address,address,address,address,address,uint256,uint256,uint256,bytes) arg0, bytes arg1, bytes arg2, uint256 arg3, uint256 arg4, uint256 arg5)",
        ),
    ] {
        assert!(source(file).contains(header), "{file}: missing `{header}`");
    }
}

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
        pool.contains("loc_240 = loc_2c0;") && pool.contains("if (loc_2c0 <= loc_240) {"),
        "the value before a store is read from the word the code saved it in"
    );

    let old = source("../../testdata/vuln/kotet.hex");
    assert!(
        !old.contains("mem[0x0] = 6;"),
        "the scratch word of a hash the lifter resolved is not printed"
    );
}

#[test]
fn what_a_helper_writes_and_what_was_read_before_it_stay_in_the_text() {
    let source = |path: &str| {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(path);
        let code = evmdec::hex::decode(std::fs::read_to_string(path).unwrap().trim()).unwrap();
        evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default()).source
    };
    let proxy = source("../../testdata/regress/swap_proxy.hex");
    let start = proxy.find("function func_0x379(").expect("the copy helper");
    let body = &proxy[start..start + proxy[start..].find("\n    }").unwrap()];
    assert!(
        body.contains("mem[arg0] = arg1;") && body.contains("= msg.data[arg2:+arg1];"),
        "the helper fills memory its caller sends on: {body}"
    );
    let token = source("../../testdata/regress/minime_token.hex");
    assert!(
        token.contains("uint256 prev_stor_arg0 = stor[arg0];\n            func_0x1ca7("),
        "the length read before the resize is named before the helper changes it"
    );
    assert!(!token.contains("require(stor[arg0] < stor[arg0]"));
}

#[test]
fn a_field_read_before_its_slot_is_written_keeps_the_old_value() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../testdata/regress/umbrella_batch_helper.hex");
    let code = evmdec::hex::decode(std::fs::read_to_string(path).unwrap().trim()).unwrap();
    let helper = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default()).source;
    assert!(
        helper.contains(
            "uint256 prev_owner = owner;\n        owner = newOwner;\n        \
             emit OwnershipTransferred(prev_owner, address(newOwner));"
        ),
        "the event carries the owner read before the store"
    );
}

#[test]
fn a_merged_value_is_assigned_on_every_way_in() {
    let source = |path: &str| {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(path);
        let code = evmdec::hex::decode(std::fs::read_to_string(path).unwrap().trim()).unwrap();
        evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default()).source
    };
    let helper = source("../../testdata/regress/umbrella_batch_helper.hex");
    assert!(
        helper.contains("if (!ret_1_0) {\n            v1 = arg2;\n        L1236:"),
        "the branch that skips the swap still hands its amount to the join"
    );
    let token = source("../../testdata/regress/minime_token.hex");
    assert!(
        token.contains(
            "v1 = arg0;\n        v2 = arg1;\n        while (v1 > v2) {\n            \
             stor[v2] = 0;\n            v2 = v2 + 1;\n        }"
        ),
        "a helper that starts on a loop counts from what its caller passed"
    );
    assert!(!token.contains("stor[arg1 + 23] = 0;"));
}

#[test]
fn a_test_settled_on_one_way_in_is_still_made_after_a_join() {
    let path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testdata/regress/layerzero_dvn.hex");
    let code = evmdec::hex::decode(std::fs::read_to_string(path).unwrap().trim()).unwrap();
    let dvn = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default()).source;
    let start = dvn.find("function func_0x176e(").expect("the batch call");
    let body = &dvn[start..start + dvn[start..].find("\n    }").unwrap()];
    let cleared = body.split("if (ret_5_0) {\n").skip(1);
    assert_eq!(
        cleared
            .filter(|rest| rest.trim_start().starts_with("stor_8[ret_3_0] = false;"))
            .count(),
        2,
        "a failed call frees its hash again on both ways out: {body}"
    );
}

#[test]
fn both_ways_into_a_join_keep_their_own_call_after_it() {
    let path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testdata/regress/oneinch_v6.hex");
    let code = evmdec::hex::decode(std::fs::read_to_string(path).unwrap().trim()).unwrap();
    let router = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default()).source;
    let start = router
        .find("function func_0x216b(")
        .expect("the swap callback");
    let body = &router[start..start + router[start..].find("\n    }").unwrap()];
    let after = &body[body.find("L21be:").expect("the join")..];
    assert!(
        after.contains("token1.selector") && after.contains("token0.selector"),
        "the pool is asked for the other token whichever one was paid: {after}"
    );
}

#[test]
fn a_selector_compared_in_place_is_read_from_the_high_bytes() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../testdata/regress/transparent_proxy.hex");
    let code = evmdec::hex::decode(std::fs::read_to_string(path).unwrap().trim()).unwrap();
    let proxy = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default()).source;
    assert!(
        proxy.contains("require(msg.sig == 0x4f1ef286 /* upgradeToAndCall(address,bytes) */"),
        "the admin may only call the upgrade: {proxy}"
    );
    assert!(!proxy.contains("msg.sig == 0x00000000"));
}

#[test]
fn a_call_data_word_read_in_a_helper_is_not_named_like_its_parameters() {
    let path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testdata/regress/oneinch_v6.hex");
    let code = evmdec::hex::decode(std::fs::read_to_string(path).unwrap().trim()).unwrap();
    let router = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default()).source;
    let start = router
        .find("function func_0x216b(int256 arg0, int256 arg1)")
        .expect("the callback");
    let body = &router[start..start + router[start..].find("\n    }").unwrap()];
    assert!(
        body.contains("if (calldata[132] == address(this)) {"),
        "the payer comes from the call data, not from what the caller passed: {body}"
    );
    assert!(!body.contains("arg4") && !body.contains("arg5"));
}

#[test]
fn an_argument_is_bound_to_the_parameter_that_receives_it() {
    let path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testdata/regress/oneinch_v6.hex");
    let code = evmdec::hex::decode(std::fs::read_to_string(path).unwrap().trim()).unwrap();
    let router = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default()).source;
    let start = router
        .find("function func_0x4e5e(")
        .expect("the call helper");
    let head = &router[start..start + router[start..].find('\n').unwrap()];
    assert!(
        head.contains("address target, uint256 arg6, uint256 arg7,"),
        "the two factors of the value sent are numbers, whatever sits below them: {head}"
    );
}

fn regress(name: &str) -> evmdec::decompile::Contract {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testdata/regress");
    let text = std::fs::read_to_string(path.join(name)).unwrap();
    let code = evmdec::hex::decode(text.trim()).unwrap();
    evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default())
}

fn selectors(c: &evmdec::decompile::Contract) -> Vec<u32> {
    let hex = c.functions.iter().filter_map(|f| f.selector.as_deref());
    hex.map(|s| u32::from_str_radix(&s[2..], 16).unwrap())
        .collect()
}

#[test]
fn a_selector_table_read_from_the_code_gives_every_function() {
    const ABI: [u32; 47] = [
        0x0335_d99f,
        0x07ee_a7a7,
        0x099c_0d8e,
        0x17f7_182a,
        0x1d27_47d4,
        0x268c_a11c,
        0x292b_6f0a,
        0x2e1a_7d4d,
        0x33fd_6f74,
        0x3792_7b6b,
        0x44a3_ead6,
        0x4641_257d,
        0x514e_cd6c,
        0x53d1_a3b7,
        0x54c4_9fe9,
        0x584d_b835,
        0x69e2_99ed,
        0x6b44_1a40,
        0x6e55_3f65,
        0x70a0_8231,
        0x72da_cffa,
        0x7386_1fb3,
        0x82c6_3066,
        0x88b7_006e,
        0x93f7_aa67,
        0x963c_94b9,
        0x9ba8_a1b8,
        0xa491_8944,
        0xa972_985e,
        0xaada_d2f7,
        0xaf75_68dd,
        0xb5ab_3c1e,
        0xb6b5_5f25,
        0xc34d_01a4,
        0xc481_8351,
        0xca42_f2cd,
        0xcab4_d3db,
        0xcc00_adec,
        0xdaf1_50f8,
        0xe152_2536,
        0xe41a_b771,
        0xe5ea_47b8,
        0xe6f1_daf2,
        0xf05c_c058,
        0xf106_8454,
        0xf851_a440,
        0xfcb5_fbcb,
    ];
    let sparse = regress("vyper_sparse_table.hex");
    assert_eq!(selectors(&sparse), ABI, "one bucket of the table per jump");
    assert!(!sparse.source.contains("orphan_"));
    let dense = selectors(&regress("vyper_dense_table.hex"));
    assert_eq!(dense.len(), 61, "the table holds the selectors themselves");
    assert!(dense.contains(&0x3df0_2124) && dense.contains(&0x095e_a7b3));
}

#[test]
fn a_function_behind_the_table_is_printed_to_its_end() {
    let source = regress("vyper_sparse_table.hex").source;
    let start = source.find("function func_37927b6b(").expect("the import");
    let body = &source[start..start + source[start..].find("\n    }").unwrap()];
    assert!(
        body.contains("func_0x1e68(1728);\n") && body.contains("tstor_0 = 0;\n"),
        "the rewards are imported and the lock is released: {body}"
    );
    assert!(!source.contains("unreachable"));
}

#[test]
fn a_selector_tested_for_zero_is_the_zero_selector() {
    let router = regress("via_ir_router.hex");
    assert!(selectors(&router).contains(&0), "the test is its dispatch");
    assert!(router.source.contains("\"3ebt\""));
}

fn undeclared_old_values(source: &str) -> Vec<String> {
    let mut missing = Vec::new();
    let mut declared: Vec<(String, usize)> = Vec::new();
    let word = |text: &str| -> String {
        let end = text.find(|c: char| !c.is_ascii_alphanumeric() && c != '_');
        text[..end.unwrap_or(text.len())].to_string()
    };
    for line in source.lines().filter(|l| !l.trim().is_empty()) {
        let depth = line.len() - line.trim_start().len();
        declared.retain(|(_, at)| *at <= depth);
        let made = line.trim_start().strip_prefix("uint256 prev").map(word);
        let read = match &made {
            Some(_) => &line[line.find('=').unwrap()..],
            None => line,
        };
        for (at, _) in read.match_indices("prev") {
            let name = word(&read[at..]);
            let old_value = name[4..]
                .trim_start_matches(char::is_numeric)
                .starts_with('_');
            let before = read[..at].chars().next_back();
            let starts = before.is_none_or(|c| !c.is_ascii_alphanumeric() && c != '_');
            if starts && old_value && !declared.iter().any(|(d, _)| *d == name) {
                missing.push(format!("{name} in {}", line.trim()));
            }
        }
        declared.extend(made.map(|rest| (format!("prev{rest}"), depth)));
    }
    missing
}

#[test]
fn an_old_value_is_named_where_every_use_of_it_passes() {
    let files = [
        "vyper_gauge.hex",
        "univ3_pool.hex",
        "layerzero_dvn.hex",
        "rango_diamond.hex",
        "oneinch_v6.hex",
    ];
    let [gauge, pool, dvn, diamond, router] = files.map(|name| regress(name).source);
    for source in [&gauge, &pool, &dvn, &diamond, &router] {
        assert_eq!(undeclared_old_values(source), Vec::<String>::new());
    }
    assert!(
        gauge.contains(
            "uint256 prev_stor_14 = stor_14;\n        \
             uint256 prev_timestamp_15_stor_14 = timestamp_15[prev_stor_14];"
        ) && gauge.contains("if (prev_stor_5 >= prev_timestamp_15_stor_14) {"),
        "the period is read once, ahead of both branches"
    );
    let burn = &pool[pool
        .find("function func_0x4acf(")
        .expect("the position update")..];
    let named = burn.find("uint256 prev_feeGrowthGlobal0X128 = feeGrowthGlobal0X128;");
    assert!(
        named.expect("the fee growth is kept") < burn.find("if (int128(arg3) != 0) {").unwrap(),
        "a burn of nothing still has the fee growth it read"
    );
    assert!(
        !pool.contains("prev2_stor_0 &"),
        "the last write reads slot 0 anew"
    );
    assert!(
        dvn.contains("require(uint64(stor_6) <= uint64(stor_4),"),
        "the quorum is checked against the size after the change"
    );
    assert!(dvn.contains("if (!stor_8[ret_3_0]) {"));
    let add = &diamond[diamond
        .find("function orphan_0x36d(")
        .expect("addFunctions")..];
    let named = add.find("uint256 prev").expect("the position is kept");
    assert!(named < add.find("if (uint96(").expect("the first facet test"));
    assert!(
        router.contains(
            "require(stor_5[address(calldata[arg4 + 32])][ret_2_0] == 0, CustomError_c5f2be51());"
        ),
        "the lock is read after the permit ran"
    );
}

#[test]
fn a_read_made_before_a_write_is_not_printed_as_one_made_after() {
    let ramp = regress("vyper_sparse_table.hex").source;
    assert!(
        ramp.contains("loc_180 = loc_e0 * (1320 - loc_180);")
            && ramp.contains("stor_8 = stor_8 + loc_180;"),
        "a word at a fixed address is read again after it is written: {ramp}"
    );
    let router = regress("via_ir_router.hex").source;
    let start = router.find("function uniswapV3SwapCallback(").unwrap();
    let callback = &router[start..start + router[start..].find("\n    }").unwrap()];
    let cleared = callback.find("tstor_0xd879").expect("the pool slot");
    let checked = callback.find("require(msg.sender == address(prev_tstor_0xd879");
    assert!(
        checked.is_some_and(|at| at > cleared),
        "the caller is compared with the pool read before the slot was cleared: {callback}"
    );
    assert!(router.contains("0 - prev_tstor_0xcf25"));
    assert_eq!(undeclared_old_values(&ramp), Vec::<String>::new());
    assert_eq!(undeclared_old_values(&router), Vec::<String>::new());
}

#[test]
fn the_ir_pipeline_is_told_by_its_call_data_test() {
    assert!(regress("via_ir_router.hex").compiler.via_ir);
    assert!(!regress("layerzero_dvn.hex").compiler.via_ir);
}

#[test]
fn a_helper_declares_every_stack_place_it_reads_and_returns_what_it_makes() {
    let router = regress("oneinch_v6.hex").source;
    assert!(!router.contains("caller_stack") && !router.contains("__return_pc"));
    let line = |with: &str| router.lines().find(|l| l.contains(with)).expect("the line");
    let head = line("function func_0x11e0(");
    let params = &head[head.find('(').unwrap()..head.find(')').unwrap()];
    assert_eq!(params.split(", ").count(), 7, "{head}");
    assert!(head.ends_with("internal returns (uint256, uint256) {"));
    let call = line("= func_0x11e0(").trim();
    assert!(
        call.starts_with("(ret_10_0, ret_10_1) = func_0x11e0(calldata[arg2 + 192], ")
            && call.ends_with(", arg2, target, arg0, arg1, ret_1_0);"),
        "the call passes the seven places the helper reads and binds its two results: {call}"
    );
    assert!(router.contains("return (calldata[arg2 + 128], mem[0x0]);"));
    let gauge = regress("vyper_gauge.hex").source;
    assert!(gauge.contains("function _transfer(uint256 amount, address to, address from)"));
    assert!(gauge.contains("_transfer(amount, to, msg.sender);"));
}

#[test]
fn copies_of_one_block_have_labels_of_their_own() {
    let staking = regress("vyper_sparse_table.hex").source;
    let start = staking
        .find("function func_0x2cfc(")
        .expect("the checkpoint helper");
    let body = &staking[start..start + staking[start..].find("\n    }").unwrap()];
    let mut labels: Vec<&str> = body
        .lines()
        .filter_map(|l| l.trim().strip_suffix(':'))
        .filter(|l| l.starts_with('L'))
        .collect();
    let defined = labels.len();
    labels.sort_unstable();
    labels.dedup();
    assert_eq!(labels.len(), defined, "a label is defined once: {labels:?}");
    for goto in body.split("goto ").skip(1) {
        let target = goto.split(';').next().unwrap();
        assert!(labels.contains(&target), "goto {target} has its label");
    }
}

#[test]
fn call_data_is_the_bytes_the_writes_left_under_one_pointer_name() {
    let router = regress("oneinch_v6.hex").source;
    assert!(
        router.contains("(abi.encodePacked(bytes4(0x27a9b424), arg5, arg4, ")
            && router.contains(", 288, 5, bytes5(0x31494e4348)));"),
        "a selector, ten words and the five bytes of the tag"
    );
    let helper = regress("umbrella_batch_helper.hex").source;
    assert!(helper.contains(
        ".call(abi.encodeWithSelector(bytes4(uint32(v2)), returndata_2[0], msg.sender, address(this)));"
    ));
    assert!(helper.contains("abi.encodeWithSelector(deposit.selector, arg2, address(this))"));
    let gauge = regress("vyper_gauge.hex").source;
    assert!(
        gauge.contains("stor_21.call(abi.encodePacked(bytes4(mem[0x3c8])));"),
        "a call of four bytes is not a word"
    );
    let proxy = regress("swap_proxy.hex").source;
    assert!(proxy.contains("mem[ptr1 + 68] = arg5;") && proxy.contains(".call(mem[ptr1:v2]);"));
    let token = regress("minime_token.hex").source;
    assert!(
        token.contains("mem[ptr1 + 68] = address(this);")
            && token
                .contains("address(target).call(abi.encodeWithSelector(func_8f4ffcb1.selector, "),
        "the buffer written is the buffer sent"
    );
    let dvn = regress("layerzero_dvn.hex").source;
    assert!(
        dvn.contains("calldata[v3 + calldata[v3 + 64]], ptr3);")
            && dvn.contains(".call(mem[ptr3:ret_7_0]);")
    );
}

#[test]
fn untested_arithmetic_is_marked_and_gas_is_named_where_it_is_read() {
    let router = regress("via_ir_router.hex").source;
    let tested = |l: &str| l.contains(" = ret_1_0 - v") && !l.contains("unchecked(");
    assert!(
        router.lines().any(tested),
        "a difference the code tests before it is printed bare"
    );
    assert!(router.contains(" = arg7 * v") && router.contains(" << 144) - v"));
    let used = router.find(" + 33000)").expect("the use");
    let name = router[..used].rsplit("unchecked(").next().unwrap();
    let read = router[..used]
        .rfind(&format!("{name} = gasleft();"))
        .expect("the read");
    assert!(
        router[read..used].contains(".call("),
        "the gas is read before the swap and used after it"
    );
    let proxy = regress("swap_proxy.hex").source;
    assert!(proxy.contains("v5 = unchecked(v5 + 1);"));
    assert!(
        !proxy.contains("unchecked(arg"),
        "an offset into the call data is not arithmetic of the source"
    );
    assert!(!regress("minime_token.hex").source.contains("unchecked("));
}

#[test]
fn element_checks_field_masks_and_the_vyper_compiler_are_kept() {
    let bot = regress("mev_bot.hex").source;
    let element =
        |l: &str| l.contains("require(address(calldata[v") && l.contains("]) == calldata[v");
    assert!(
        bot.lines().any(element),
        "an address in an array is tested where it is decoded"
    );
    assert!(bot.contains("Panic(memory allocation too large));"));
    let pool = regress("univ3_pool.hex").source;
    assert!(
        pool.contains(" / (stor_0 >> 232 & 15);") && pool.contains(" = stor_0_29 % 16;"),
        "the low four bits of the protocol fee are not the whole byte"
    );
    assert!(regress("vyper_gauge.hex")
        .language
        .starts_with("vyper < 0.3.10"));
    assert!(regress("vyper_sparse_table.hex")
        .language
        .starts_with("vyper >= 0.3.10"));
}

#[test]
fn a_memory_write_that_is_read_later_is_printed() {
    let router = regress("oneinch_v6.hex").source;
    let start = router.find("function func_0x216b(").expect("the callback");
    let first = router[start..].lines().nth(1).expect("its first statement");
    assert_eq!(
        first.trim(),
        "mem[ptr1] = 0xdfe1681d21220a7ddca3f43a9059cbb23b872dd36c785160000000000000000;",
        "the selectors a helper sends later are stored at entry"
    );
    let gauge = regress("vyper_gauge.hex").source;
    assert!(
        gauge.contains(
            "identity.call(mem[0x204:0x228]);\n                mem[0x1a0:+36] = mem[0x204:+36];"
        ),
        "the built-in copies over the word the next test reads"
    );
}

#[test]
fn a_slot_read_before_an_outside_call_is_not_printed_as_read_after_it() {
    let router = regress("via_ir_router.hex").source;
    let key = "tstor_0xe67bd0676d46b7f9f34e582d927d908e16216dd24bc46c5aab4cb6b3dda7fd31";
    let kept = router
        .find(&format!("uint256 prev_{key} = {key};"))
        .expect("the slot is named when it is read");
    let called = router[kept..].find(".call(").expect("the swap") + kept;
    let used = router[kept..]
        .find(&format!("if (prev_{key} >> 208 & 15 != 3) {{"))
        .expect("the test made after the calls");
    assert!(
        kept + used > called,
        "the old value is what the later test reads"
    );
    assert_eq!(undeclared_old_values(&router), Vec::<String>::new());
    let gauge = regress("vyper_gauge.hex").source;
    let read = gauge
        .find("loc_240 = stor_13;")
        .expect("the supply is kept");
    let called = gauge[read..].find(".call(").expect("the controller") + read;
    let divided = gauge[called..]
        .find(" / loc_240 >= loc_1c0);")
        .expect("the division");
    assert!(
        !gauge[read + 1..called + divided].contains("loc_240 = "),
        "the supply read before the controller is called is the one divided by after"
    );
    assert_eq!(undeclared_old_values(&gauge), Vec::<String>::new());
}

#[test]
fn an_operator_the_code_does_not_test_is_marked_wherever_it_is_printed() {
    let diamond = regress("rango_diamond.hex").source;
    assert!(
        diamond.contains("stor[arg0 + 2] = unchecked(prev_stor_arg0_2 + 1);"),
        "a length kept beside a hashed array is a count, not a place"
    );
    let router = regress("oneinch_v6.hex").source;
    assert!(router.contains("return (unchecked(0 - mem[v1]));"));
    let via_ir = regress("via_ir_router.hex").source;
    assert!(
        !via_ir.contains(" = 0 / "),
        "a tested quotient is printed only where the code makes it"
    );
}

#[test]
fn a_tested_difference_is_made_before_the_transfer_that_follows_it() {
    let router = regress("oneinch_v6.hex").source;
    let lines: Vec<&str> = router.lines().map(str::trim).collect();
    let refund = lines
        .iter()
        .position(|l| l.starts_with("_sendValue(") && l.ends_with(", msg.sender, calldata[arg2]);"))
        .expect("the refund of what was not spent");
    let spent = lines[..refund]
        .iter()
        .rposition(|l| l.starts_with("v8 = v2 - v"))
        .expect("the amount spent");
    assert!(refund - spent <= 2, "{:?}", &lines[spent..=refund]);
}

#[test]
fn a_loop_is_printed_once_with_its_tests_inside_it() {
    let body = |source: &str, name: &str| -> String {
        let start = source.find(name).expect("the helper");
        source[start..start + source[start..].find("\n    }").unwrap()].to_string()
    };
    let gauge = body(&regress("vyper_gauge.hex").source, "function func_0x71d(");
    assert_eq!(
        gauge.matches("func_d3078c94.selector").count(),
        1,
        "{gauge}"
    );
    assert!(!gauge.contains("goto "), "{gauge}");
    assert!(gauge.contains("while (true) {\n                require(loc_2a0 >= loc_280);"));
    let staking = body(
        &regress("vyper_sparse_table.hex").source,
        "function func_0x2cfc(",
    );
    assert_eq!(staking.matches("transfer.selector").count(), 1, "{staking}");
}

#[test]
fn what_calls_return_into_memory_that_is_hashed_is_printed() {
    let router = regress("oneinch_v6.hex").source;
    let start = router.find("function func_0x216b(").expect("the callback");
    let body = &router[start..start + router[start..].find("\n    }").unwrap()];
    for at in [21, 53, 85] {
        let line = format!("mem[ptr1 + {at}:+min(32, returndatasize())] = returndata[0:+");
        assert!(body.contains(&line), "{line}\n{body}");
    }
}

#[test]
fn a_store_past_a_length_rounded_down_does_not_hide_the_head_of_call_data() {
    let token = regress("minime_token.hex").source;
    assert!(
        token.contains(".call(abi.encodeWithSelector(func_8f4ffcb1.selector, msg.sender, value, address(this), ...));"),
        "{token}"
    );
}

#[test]
fn a_block_handed_to_a_helper_that_reads_it_is_named_as_the_block() {
    let router = regress("oneinch_v6.hex").source;
    assert!(
        router.contains("= func_0x1ba9(ptr1, calldata["),
        "the helper is handed the block, not the number where it starts"
    );
}
