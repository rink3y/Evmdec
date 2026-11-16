use audit::laws::Kind;
use evmdec::U256;
use std::path::PathBuf;
use std::rc::Rc;

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

const DEPLOYED_AT: &str = "0x3333333333333333333333333333333333333333";

fn report_on_chain(name: &str, chain: audit::chain::Table) -> audit::Report {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../testdata/source")
        .join(name);
    let hex = std::fs::read_to_string(path).expect("fixture");
    let code = evmdec::hex::decode(hex.trim()).expect("hex");
    let mut contract = evmdec::decompile::decompile(&code, &evmdec::decompile::Options::default());
    contract.address = Some(DEPLOYED_AT.to_string());
    audit::audit_read(&contract, Rc::new(chain), 100, 1_700_000_000)
}

#[test]
fn a_contract_read_from_a_chain_is_run_on_what_the_chain_holds_and_not_on_a_guess() {
    let (vault, deployer) = (
        U256::from_hex_str(DEPLOYED_AT).expect("address"),
        U256::from_hex_str("0x4444444444444444444444444444444444444444").expect("address"),
    );
    let mut chain = audit::chain::Table::default();
    chain.storage.insert((vault, U256::ZERO), deployer);
    chain.ether.insert(vault, U256::from_u64(5));
    let report = report_on_chain("Vault.hex", chain);
    let at = |kind: Kind| report.findings.iter().find(|f| f.kind == kind);
    // The deployer the chain names is the owner an open setOwner(address) replaces.
    assert!(at(Kind::Takeover).is_some(), "{:?}", report.findings);
    assert!(report
        .assumed
        .iter()
        .any(|a| a.contains(&deployer.to_hex())));
    // sweep(address) pays out the ether the chain says the vault holds. Nobody has to pay in first.
    let sweep = at(Kind::Gain).expect("the open sweep");
    assert_eq!(sweep.steps.len(), 1, "{:?}", sweep.steps);
    assert!(!report.assumed.iter().any(|a| a.contains("ledger at slot")));
}

#[test]
fn interest_paid_at_the_rate_the_chain_holds_is_not_a_gain() {
    let savings = U256::from_hex_str(DEPLOYED_AT).expect("address");
    let mut chain = audit::chain::Table::default();
    // ratePerDay. A guessed world leaves it at zero and close() pays back what was paid in.
    chain
        .storage
        .insert((savings, U256::ZERO), U256::from_u64(10));
    chain.ether.insert(savings, U256::from_u64(1) << 80);
    let report = report_on_chain("Savings.hex", chain);
    let close = report
        .functions
        .iter()
        .find(|f| f.selector.as_deref() == Some("0x43d726d6"));
    let ended = &close.expect("close()").ends_for;
    assert!(ended.contains(&"an account with no role"), "{ended:?}");
    assert!(report.findings.is_empty(), "{:?}", report.findings);
}

#[test]
fn a_byte_string_is_grown_to_the_record_the_code_reads_in_it() {
    // claim(uint256,bytes). The byte string has to hold one word, a time not yet passed.
    let report = report("Relay.hex");
    let kinds: Vec<Kind> = report.findings.iter().map(|f| f.kind).collect();
    assert_eq!(kinds, vec![Kind::Gain], "{:?}", report.findings);
    assert_eq!(report.findings[0].selector.as_deref(), Some("0x38926b6d"));
}

#[test]
fn a_record_in_a_byte_string_is_filled_by_what_its_words_are_used_for() {
    let report = report("Courier.hex");
    let at = |kind: Kind| -> Vec<&str> {
        let shows =
            |f: &&audit::report::Finding| f.kind == kind || f.also.iter().any(|a| a.kind == kind);
        let of_kind = report.findings.iter().filter(shows);
        of_kind.filter_map(|f| f.selector.as_deref()).collect()
    };
    // deliver(bytes) pays the address its record names. relay(address,bytes) ends with any
    // bytes, and is found only by passing on the message that moves a user's asset.
    assert_eq!(
        at(Kind::Gain),
        ["0x22133eaf", "0xc28e83fd"],
        "{:?}",
        report.findings
    );
    assert_eq!(at(Kind::Loss), ["0xc28e83fd"], "{:?}", report.findings);
    let stated = |a: &String| a.contains("keep honest books") && a.contains("draw on it");
    assert!(report.assumed.iter().any(stated), "{:?}", report.assumed);
}

#[test]
fn a_caller_that_has_to_be_a_contract_is_the_accounts_own() {
    // settle(uint256,bytes). The caller must be the pool its bytes name, have code, and say
    // which asset to pull from the payer the bytes name.
    let report = report("Payer.hex");
    // The user's loss and the account's gain are one run, so they are one finding.
    let [taken] = &report.findings[..] else {
        panic!("{:?}", report.findings);
    };
    let also: Vec<Kind> = taken.also.iter().map(|a| a.kind).collect();
    assert_eq!((taken.kind, also), (Kind::Gain, vec![Kind::Loss]));
}

#[test]
fn words_an_amount_paid_is_worked_out_from_are_all_amounts() {
    // pay(bytes) sends one word of its record and then, unchecked, the second less the first.
    let report = report("Split.hex");
    let kinds: Vec<Kind> = report.findings.iter().map(|f| f.kind).collect();
    assert_eq!(kinds, vec![Kind::Gain], "{:?}", report.findings);
    assert_eq!(report.findings[0].selector.as_deref(), Some("0x6eda12f8"));
}

#[test]
fn what_a_call_shows_without_nesting_is_not_found_again_by_nesting_it() {
    // approveAndCall(address,uint256) records an allowance the caller gives its own contract
    // and calls that contract. The record buys nothing, called once or from within itself.
    let report = report("Allow.hex");
    assert!(report.findings.is_empty(), "{:?}", report.findings);
}

#[test]
fn a_list_is_not_emptied_to_end_a_call_its_items_could_end() {
    // write((uint256,uint256,uint256)[]) pays for each cell whose two places are in range.
    // With no cells it ends and pays nothing.
    let report = report("Board.hex");
    let kinds: Vec<Kind> = report.findings.iter().map(|f| f.kind).collect();
    assert_eq!(kinds, vec![Kind::Gain], "{:?}", report.findings);
    assert_eq!(report.findings[0].selector.as_deref(), Some("0xac41fdb5"));
}

#[test]
fn a_call_that_cuts_what_a_third_account_holds_is_found_on_the_side_of_a_test_it_ends_without() {
    let (token, pool) = (
        U256::from_hex_str(DEPLOYED_AT).expect("address"),
        U256::from_hex_str("0x5555555555555555555555555555555555555555").expect("address"),
    );
    let mut key = pool.to_be_bytes().to_vec();
    key.extend_from_slice(&U256::ZERO.to_be_bytes());
    let held_at = U256::from_be_bytes(&evmdec::keccak::keccak256(&key));
    let held = U256::from_u64(1) << 70;
    let mut chain = audit::chain::Table::default();
    chain.storage.insert((token, held_at), held);
    chain.storage.insert((token, U256::from_u64(1)), pool);
    chain.storage.insert((token, U256::from_u64(2)), held);
    // transfer(address,uint256) to the dead address takes a tenth out of the pool's record.
    // The account has to hold some, and a plain transfer ends without reaching the cut.
    let report = report_on_chain("Levy.hex", chain);
    let cut = report.findings.iter().find(|f| f.kind == Kind::Debit);
    let cut = cut.unwrap_or_else(|| panic!("{:?}", report.findings));
    assert_eq!(cut.selector.as_deref(), Some("0xa9059cbb"));
    assert!(cut.shown.contains(&pool.to_hex()), "{}", cut.shown);
    assert!(
        cut.steps[0].contains("holds a thousand units"),
        "{:?}",
        cut.steps
    );
}

#[test]
fn a_setting_one_call_needs_is_not_taken_where_it_stops_another_call_sooner() {
    // tune(uint256) is refused unless testing is set. draw(uint256) is refused once it is,
    // and never ends either way, so only how far it gets tells.
    let report = report("Gate.hex");
    let set = |a: &String| a.contains("slot 0x1 is set");
    assert!(!report.assumed.iter().any(set), "{:?}", report.assumed);
    let tune = report
        .functions
        .iter()
        .find(|f| f.selector.as_deref() == Some("0xbecda0ea"));
    let tune = tune.expect("tune(uint256)");
    // A call that only ended in a world that was tried and not kept did not end.
    assert!(tune.ends_for.is_empty(), "{:?}", tune.ends_for);
    assert!(report.findings.is_empty(), "{:?}", report.findings);
}

#[test]
fn an_answer_decoded_after_an_earlier_one_is_given_the_length_its_decoder_asks_for() {
    // ask() decodes one word from the first answer and three from the second. The place
    // the second is copied to is worked out from the length of the first.
    let report = report("Asker.hex");
    let ask = report
        .functions
        .iter()
        .find(|f| f.selector.as_deref() == Some("0x4a896384"));
    let ask = ask.expect("ask()");
    assert!(ask.ends_for.contains(&"a user"), "{:?}", ask.stopped_by);
    assert!(report.findings.is_empty(), "{:?}", report.findings);
}
