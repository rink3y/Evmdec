use evmdec::decompile::{decompile, Options};

fn text(code_hex: &str) -> String {
    let code = evmdec::hex::decode(code_hex).expect("valid hex");
    decompile(&code, &Options::default()).source
}

#[test]
fn a_store_that_a_later_hash_reads_stays_in_the_output() {
    let out = text(
        "60075f526004355f20600155 60095f5200"
            .replace(' ', "")
            .as_str(),
    );
    let store = out
        .find("mem[0x0] = 7;")
        .expect("the hashed store is printed");
    let hash = out.find("keccak256(").expect("the hash is printed");
    assert!(store < hash, "{out}");
}

#[test]
fn the_count_leading_zeros_opcode_is_read_and_folded() {
    let out = text("5f351e5f5500");
    assert!(out.contains("stor_0 = clz("), "{out}");
    let folded = text("60011e5f5533ff");
    assert!(folded.contains("stor_0 = 255;"), "{folded}");
    assert!(folded.contains("selfdestruct(msg.sender);"), "{folded}");
}

#[test]
fn a_jump_through_memory_that_a_copy_wrote_is_not_taken_to_go_to_zero() {
    for code in [
        "60205f5f375f51565b33ff",
        "6020365f375f51565b33ff",
        "5f5f5f5f335afa5060205f5f3e5f51565b33ff",
        "60205f5f5f335afa505f51565b33ff",
    ] {
        let out = text(code);
        assert!(out.contains("selfdestruct(msg.sender);"), "{out}");
    }
}

#[test]
fn a_computed_jump_is_followed_for_every_state_that_reaches_it() {
    for code in [
        "366009576002600c565b60005b601101565b005b33ff",
        "366009576000600c565b60025b601101565b005b33ff",
    ] {
        let out = text(code);
        assert!(out.contains("selfdestruct(msg.sender);"), "{out}");
        assert!(out.contains("return;"), "{out}");
    }
}

#[test]
fn another_accounts_balance_is_read_again_after_a_call() {
    let out = text("60043580315f5f5f5f6001865af1509031035f5260205ff3");
    assert!(!out.contains("return (0);"), "{out}");
    assert!(
        out.contains("prev_account_balance = arg0.balance;"),
        "{out}"
    );
    assert!(
        out.contains("return (arg0.balance - prev_account_balance);"),
        "{out}"
    );
}

#[test]
fn a_read_is_not_equal_to_itself_across_a_store_that_may_overlap() {
    let out = text("60043580516001602435529051145f5260205ff3");
    assert!(!out.contains("return (1);"), "{out}");
    assert!(out.contains("return (mem[arg0] == prev_mem);"), "{out}");
}

#[test]
fn a_loop_that_needs_many_rounds_does_not_keep_what_early_rounds_believed() {
    let mut code = vec![0x32, 0x5f, 0x52];
    for word in 1..=30usize {
        let at = 32 * word;
        code.extend([0x33, 0x61, (at >> 8) as u8, at as u8, 0x52]);
    }
    code.extend([0x60, 0x04, 0x35]);
    let head = code.len();
    code.push(0x5b);
    for word in (1..=30usize).rev() {
        let (from, to) = (32 * (word - 1), 32 * word);
        code.extend([0x61, (from >> 8) as u8, from as u8, 0x51]);
        code.extend([0x61, (to >> 8) as u8, to as u8, 0x52]);
    }
    code.extend([
        0x60,
        0x01,
        0x90,
        0x03,
        0x80,
        0x61,
        (head >> 8) as u8,
        head as u8,
        0x57,
    ]);
    code.extend([0x50, 0x60, 0x20, 0x61, 0x03, 0xc0, 0xf3]);
    let out = decompile(&code, &Options::default()).source;
    assert!(!out.contains("return (msg.sender);"), "{out}");
}

#[test]
fn a_store_a_hash_consumed_stays_when_a_later_plain_read_needs_it() {
    let out = text("600435608052600160206080205560243561001957610020565b6044356080525b60206080f3");
    assert!(out.contains("mem[0x80] = arg0;"), "{out}");
    assert!(out.contains("return mem[128:160];"), "{out}");
}

#[test]
fn the_tail_of_a_memory_copy_comes_from_the_matching_source_bytes() {
    let out = text("5f3560805260203560a052603060806101005e6030610100f3");
    assert!(
        out.contains("return (msg.data[0:32], mem[160] >> 128);"),
        "{out}"
    );
}

#[test]
fn two_overlapping_writes_in_a_different_order_per_path_are_not_trusted() {
    let out = text(
        "60443561001757600435609052602435608052610024565b6024356080526004356090525b60206090f3",
    );
    assert!(!out.contains("return (arg0);"), "{out}");
    assert!(out.contains("return mem[144:176];"), "{out}");
}

#[test]
fn copies_made_on_the_way_out_of_a_loop_are_printed_after_it() {
    let out = text("600060043561001f575b5b806024351461001f5760018155600101610009565b60645500");
    let after_loop = out
        .split("v1 = v1 + 1;")
        .nth(1)
        .expect("the loop body is printed");
    assert!(after_loop.contains("v2 = v1;"), "{out}");
}

#[test]
fn a_slot_just_below_an_arrays_data_is_not_printed_as_its_first_element() {
    let below = "b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf5";
    let first = "b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6";
    let out = text(&format!("6004357f{first}556024357f{below}5500"));
    assert_eq!(out.matches("stor_1[0] = ").count(), 1, "{out}");
}

#[test]
fn a_comparison_under_a_bitwise_operator_is_bracketed_as_solidity_reads_it() {
    let out = text("604035602035105f35175f5500");
    assert!(
        out.contains("msg.data[0:32] | (calldata[32] < calldata[64]);"),
        "{out}"
    );
}

#[test]
fn a_loop_test_too_long_to_print_in_place_is_worked_out_inside_the_loop() {
    let out = text(
        "60005b8061002435016100443501610064350161008435016100a435016100c435016100e43501610104350161012435016101443501610164350161018435016101a435016101c435016101e43501610204350161022435016102443501610264350161028435016102a435016102c435016102e43501811061007e57005b6001815560010161000256",
    );
    let (before, inside) = out.split_once("while (true) {").expect("a plain loop");
    assert!(!before.contains("uint256 t1 ="), "{out}");
    assert!(inside.contains("uint256 t1 ="), "{out}");
}

#[test]
fn a_helper_checking_its_own_call_does_not_cover_the_callers_unchecked_call() {
    let code = evmdec::hex::decode(
        "608060405260003560e01c8063aaaaaaaa146100245763bbbbbbbb1461003857600080fd5b600080808080335af150610036610042565b005b610040610042565b005b6000808080806004355af161005657600080fd5b56",
    )
    .expect("valid hex");
    let contract = decompile(&code, &Options::default());
    let report = evmdec::analyze::analyze(&contract);
    assert!(report.findings.iter().any(|f| f.id == "unchecked-call"));
}

fn finding_text(code_hex: &str, id: &str) -> Option<String> {
    let code = evmdec::hex::decode(code_hex).expect("valid hex");
    let contract = decompile(&code, &Options::default());
    let report = evmdec::analyze::analyze(&contract);
    report
        .findings
        .into_iter()
        .find(|f| f.id == id)
        .map(|f| f.description)
}

#[test]
fn only_the_shifted_value_of_an_arithmetic_shift_is_signed() {
    let out = text("60003560e01c8063aaaaaaaa1461001557600080fd5b6004356024351d60005500");
    assert!(out.contains("(int256 arg0, uint256 arg1)"), "{out}");
}

#[test]
fn a_packed_counter_is_seen_as_narrow() {
    let found = finding_text(
        "60003560e01c8063aaaaaaaa14610020578063bbbbbbbb1461004157600080fd5b6000548063ffffffff1660010163ffffffff169063ffffffff191617600055005b60005463ffffffff1660005260206000f3",
        "narrow-counter",
    );
    assert!(found.is_some_and(|text| text.contains("uint32")));
}

#[test]
fn a_sixteen_bit_timestamp_is_said_to_wrap_in_hours_not_in_2106() {
    let found = finding_text(
        "60003560e01c8063aaaaaaaa1461001557600080fd5b4261ffff1660005500",
        "narrow-counter",
    )
    .expect("the narrow timestamp is reported");
    assert!(found.contains("wraps every 18 hours"), "{found}");
    assert!(!found.contains("2106"), "{found}");
}
