use std::path::PathBuf;
use std::process::{Command, Output};

fn evmdec(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_evmdec"))
        .args(args)
        .output()
        .expect("the binary runs")
}

fn sample() -> String {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../testdata/mainnet/weth9.hex"
    );
    std::fs::read_to_string(path).expect("the sample is in the repository")
}

fn file(name: &str, contents: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!("evmdec-cli-{}-{name}", std::process::id()));
    std::fs::write(&path, contents).expect("a temporary file can be written");
    path
}

#[test]
fn hex_folded_into_lines_reads_as_the_same_code() {
    let plain = sample();
    let digits = plain.trim().trim_start_matches("0x");
    let lines: Vec<&str> = digits
        .as_bytes()
        .chunks(64)
        .map(|c| std::str::from_utf8(c).unwrap())
        .collect();
    let folded = file("folded.hex", &lines.join("\n"));
    let whole = file("whole.hex", &plain);
    let of = |path: &PathBuf| evmdec(&["disasm", path.to_str().unwrap()]);
    let (a, b) = (of(&folded), of(&whole));
    assert!(a.status.success() && b.status.success());
    assert!(!a.stdout.is_empty());
    assert_eq!(a.stdout, b.stdout);
    for path in [folded, whole] {
        let _ = std::fs::remove_file(path);
    }
}

#[test]
fn a_file_with_no_code_is_an_error() {
    for (name, contents) in [
        ("empty.hex", ""),
        ("blank.hex", "\n \n"),
        ("prefix.hex", "0x"),
    ] {
        let path = file(name, contents);
        let out = evmdec(&["disasm", path.to_str().unwrap()]);
        let _ = std::fs::remove_file(&path);
        assert!(!out.status.success(), "{name} was accepted");
        let said = String::from_utf8_lossy(&out.stderr);
        assert!(said.contains("holds no code"), "{name}: {said}");
        assert!(out.stdout.is_empty(), "{name} still printed a listing");
    }
}

#[test]
fn the_default_output_is_a_solidity_file_that_names_the_original_compiler() {
    let code = file("weth.hex", &sample());
    let out = evmdec(&["decompile", code.to_str().unwrap()]);
    let text = String::from_utf8_lossy(&out.stdout);
    let head = "// SPDX-License-Identifier: UNLICENSED\npragma solidity ^0.8.24;\n\
                // Originally compiled with solc";
    assert!(text.starts_with(head), "{text}");
    assert!(
        text.contains("function withdraw(uint256 amount) external {"),
        "{text}"
    );
}

#[test]
fn an_empty_hex_argument_is_an_error() {
    let out = evmdec(&["decompile", "0x"]);
    assert!(!out.status.success());
}

#[test]
fn a_source_is_equal_to_its_own_code_and_a_changed_one_is_not() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../../testdata/source");
    let code = format!("{dir}/Packed.hex");
    let source = format!("{dir}/Packed.sol");
    let same = evmdec(&["check", &code, &source]);
    let said = String::from_utf8_lossy(&same.stderr);
    assert!(same.status.success(), "{said}");
    let text = std::fs::read_to_string(&source).expect("the fixture is in the repository");
    assert!(text.contains("amount <= a.amount"));
    let changed = file(
        "changed.sol",
        &text.replace("amount <= a.amount", "amount < a.amount"),
    );
    let other = evmdec(&["check", &code, changed.to_str().unwrap()]);
    let _ = std::fs::remove_file(&changed);
    assert!(!other.status.success());
    let lines = String::from_utf8_lossy(&other.stdout);
    assert!(
        lines.contains("spend(address,uint160)") && lines.contains("DIFFERS"),
        "{lines}"
    );
}

#[test]
fn the_solidity_file_compiles_and_does_what_the_code_does() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../../testdata/source");
    let out = evmdec(&["decompile", &format!("{dir}/Packed.hex"), "--sol"]);
    let said = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "{said}");
    assert!(said.contains("5 of 5 equal"), "{said}");
    let file = String::from_utf8_lossy(&out.stdout);
    assert!(file.starts_with("// SPDX-License-Identifier: UNLICENSED\npragma solidity 0.8."));
    assert!(file.contains("fallback() external payable {"));
}

#[test]
fn a_jump_to_no_destination_fails_in_the_solidity_file_too() {
    // Jumps to an instruction that is not a destination, with five destinations after it.
    let code = file("nowhere.hex", "6002565b5b5b5b5b00");
    let out = evmdec(&["decompile", code.to_str().unwrap(), "--sol"]);
    let _ = std::fs::remove_file(&code);
    let said = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "{said}");
    assert!(said.contains("1 of 1 equal"), "{said}");
}
