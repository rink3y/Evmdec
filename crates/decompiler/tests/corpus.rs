//! Integration tests over the mainnet corpus in `testdata/mainnet`.

use std::path::PathBuf;

fn corpus() -> Vec<(String, Vec<u8>)> {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testdata/mainnet");
    let mut out = Vec::new();
    for e in std::fs::read_dir(&dir).expect("testdata/mainnet") {
        let p = e.unwrap().path();
        if p.extension().map_or(false, |x| x == "hex") {
            let s = std::fs::read_to_string(&p).unwrap();
            out.push((p.file_stem().unwrap().to_string_lossy().into_owned(), evmdec::hex::decode(s.trim()).unwrap()));
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
        assert!(c.stats.external_functions + c.stats.internal_functions > 0 || code.len() < 100, "{name}: no functions");
        // The Uniswap V3 factory embeds the pool's creation code as data; its "jumps" are not code.
        if name != "univ3_factory" {
            assert_eq!(c.stats.unresolved_jumps, 0, "{name}: unresolved jumps");
            assert!(c.stats.covered_blocks * 100 >= c.stats.code_blocks * 90, "{name}: coverage {}/{}", c.stats.covered_blocks, c.stats.code_blocks);
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
        let Ok(txt) = std::fs::read_to_string(&abi_path) else { continue };
        let v: serde_json::Value = serde_json::from_str(&txt).unwrap();
        let Some(abi) = v.get("abi").and_then(|a| a.as_array()) else { continue };
        let c = evmdec::decompile::decompile(&code, &evmdec::decompile::Options { no_sigs: true, ..Default::default() });
        let ours: std::collections::HashSet<String> = c.functions.iter().filter_map(|f| f.selector.clone()).collect();
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
            let inner: Vec<String> = t["components"].as_array().map(|c| c.iter().map(ty).collect()).unwrap_or_default();
            format!("({}){}", inner.join(","), &s[5..])
        } else {
            s.to_string()
        }
    }
    let inputs: Vec<String> = item["inputs"].as_array().map(|a| a.iter().map(ty).collect()).unwrap_or_default();
    format!("{}({})", item["name"].as_str().unwrap_or(""), inputs.join(","))
}

#[test]
fn oracle_finds_no_mismatch_on_weth_and_permit2() {
    for name in ["weth9", "permit2", "curve_tricrypto_ng"] {
        let code = corpus().into_iter().find(|(n, _)| n == name).unwrap().1;
        let info = evmdec::metadata::analyze(&code);
        let st = evmdec::verify::verify(&info.runtime, &evmdec::verify::VerifyOptions { runs: 3, seed: 7, verbose: false });
        assert_eq!(st.mismatch, 0, "{name}: {:?}", st.mismatches);
        assert!(st.blocks_verified * 100 >= st.blocks * 75, "{name}: only {}/{} blocks verified", st.blocks_verified, st.blocks);
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
    assert_eq!(evmdec::rpc::minimal_proxy_target(&code).as_deref(), Some("0xbebebebebebebebebebebebebebebebebebebebe"));
    let c = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default());
    assert!(c.source.contains("delegatecall"));
    // A creation wrapper around it: PUSH1 len PUSH1 off PUSH1 0 CODECOPY PUSH1 len PUSH1 0 RETURN
    let rt = code.clone();
    let mut creation = vec![0x60, rt.len() as u8, 0x60, 0x0c, 0x60, 0x00, 0x39, 0x60, rt.len() as u8, 0x60, 0x00, 0xf3];
    creation.extend_from_slice(&rt);
    let info = evmdec::metadata::analyze(&creation);
    assert_eq!(info.kind, evmdec::metadata::CodeKind::Creation);
    assert_eq!(info.runtime, rt);
}
