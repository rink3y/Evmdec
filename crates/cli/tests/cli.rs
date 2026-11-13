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
        let out = evmdec(&["analyze", path.to_str().unwrap()]);
        let _ = std::fs::remove_file(&path);
        assert!(!out.status.success(), "{name} was accepted");
        let said = String::from_utf8_lossy(&out.stderr);
        assert!(said.contains("holds no code"), "{name}: {said}");
        assert!(out.stdout.is_empty(), "{name} still printed a report");
    }
}

#[test]
fn an_empty_hex_argument_is_an_error() {
    let out = evmdec(&["decompile", "0x"]);
    assert!(!out.status.success());
}

#[test]
fn a_report_names_the_code_it_read() {
    let whole = file("report.hex", &sample());
    let out = evmdec(&["analyze", whole.to_str().unwrap()]);
    let _ = std::fs::remove_file(&whole);
    assert!(out.status.success());
    let report = String::from_utf8_lossy(&out.stdout);
    assert!(report.contains("Code size: 3124 bytes"), "{report}");
}
