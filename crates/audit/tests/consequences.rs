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

#[test]
fn a_record_written_twice_in_one_call_is_judged_by_where_it_ends() {
    // transfer reads both balances first, so sending to itself leaves the sender with more.
    let report = report("Cached.hex");
    let kinds: Vec<Kind> = report.findings.iter().map(|f| f.kind).collect();
    assert_eq!(kinds, vec![Kind::Credit], "{:?}", report.findings);
    assert_eq!(report.findings[0].selector.as_deref(), Some("0xa9059cbb"));
}

#[test]
fn what_an_owner_only_door_pays_out_is_held_and_an_open_door_beside_it_is_found() {
    // No function takes ether in. The owner's guarded withdrawal is what says the contract holds some.
    let report = report("Treasury.hex");
    let kinds: Vec<Kind> = report.findings.iter().map(|f| f.kind).collect();
    assert_eq!(kinds, vec![Kind::Gain], "{:?}", report.findings);
    // emergency(address)
    assert_eq!(report.findings[0].selector.as_deref(), Some("0x45941ee0"));
}
