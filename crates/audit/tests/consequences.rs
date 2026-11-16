use audit::laws::Kind;
use std::path::PathBuf;

fn report(name: &str) -> audit::Report {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../testdata/source")
        .join(name);
    let hex = std::fs::read_to_string(path).expect("fixture");
    let code = evmdec::hex::decode(hex.trim()).expect("hex");
    let contract = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default());
    audit::audit(&contract)
}

#[test]
fn a_send_before_the_record_is_cleared_lets_the_receiver_take_twice() {
    let report = report("Bank.hex");
    let found: Vec<_> = report
        .findings
        .iter()
        .filter(|f| f.kind == Kind::Gain)
        .collect();
    assert_eq!(found.len(), 1, "{:?}", report.findings);
    assert!(found[0].reentered, "the gain needs the nested call");
    assert_eq!(found[0].selector.as_deref(), Some("0x3ccfd60b"));
}

#[test]
fn the_same_code_with_the_record_cleared_first_shows_nothing() {
    let report = report("SafeBank.hex");
    assert!(report.findings.is_empty(), "{:?}", report.findings);
}

#[test]
fn an_open_setter_and_an_open_sweep_are_each_found_and_the_guarded_twin_is_not() {
    let report = report("Vault.hex");
    let at = |kind: Kind| -> Vec<&str> {
        let of_kind = report.findings.iter().filter(|f| f.kind == kind);
        of_kind.filter_map(|f| f.selector.as_deref()).collect()
    };
    // setOwner(address) and sweep(address). rescue(address) tests the caller and stays out.
    assert_eq!(at(Kind::Takeover), ["0x13af4035"], "{:?}", report.findings);
    assert_eq!(at(Kind::Gain), ["0x01681a62"], "{:?}", report.findings);
}

#[test]
fn a_report_is_the_same_every_time() {
    let first = serde_json::to_string(&report("Vault.hex").findings).expect("json");
    let second = serde_json::to_string(&report("Vault.hex").findings).expect("json");
    assert_eq!(first, second);
}

#[test]
fn an_open_burn_lowers_a_holder_and_moving_between_own_records_credits_nobody() {
    let report = report("Token.hex");
    let kinds: Vec<Kind> = report.findings.iter().map(|f| f.kind).collect();
    assert_eq!(kinds, vec![Kind::Debit], "{:?}", report.findings);
    // burn(address,uint256). It only runs with a total that covers the holders' balances.
    assert_eq!(report.findings[0].selector.as_deref(), Some("0x9dc29fac"));
}
