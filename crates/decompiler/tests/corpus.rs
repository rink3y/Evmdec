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
    // Unknown events are named by their topic, and the loop is a `while (cond)` whose parallel
    // copies are ordered so that no copy reads a variable already overwritten above it.
    assert!(src.contains("emit Event_22e25c6d("));
    assert!(src.contains("while (v8 < v3) {"));
    let body = src
        .split("while (v8 < v3) {")
        .nth(1)
        .unwrap()
        .split('}')
        .next()
        .unwrap();
    let lines: Vec<&str> = body
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .collect();
    assert_eq!(lines.len(), 4, "loop body: {body}");
    let pos = |needle: &str| {
        lines
            .iter()
            .position(|l| l.starts_with(needle))
            .unwrap_or_else(|| panic!("no {needle} in {body}"))
    };
    assert!(
        pos("v7 = ") < pos("v5 = ") && pos("v5 = ") < pos("v4 = "),
        "parallel copies out of order: {body}"
    );
    // No string piece in the inventory.
    assert!(
        !c.strings
            .iter()
            .any(|s| s == "C balance" || s == "r then 100" || s == "NH{q"),
        "{:?}",
        c.strings
    );
}
