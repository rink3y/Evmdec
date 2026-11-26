use evmdec::decompile::{decompile, Options};

fn text(code_hex: &str) -> String {
    let code = evmdec::hex::decode(code_hex).expect("valid hex");
    decompile(&code, &Options::default()).source
}

/* The file leaves out a write to memory that none of its lines reads. What the printer made
of each function still has it. */
fn bodies(code_hex: &str) -> String {
    let code = evmdec::hex::decode(code_hex).expect("valid hex");
    let made = decompile(&code, &Options::default());
    made.functions.iter().map(|f| f.code.as_str()).collect()
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
    assert!(
        folded.contains("selfdestruct(payable(msg.sender));"),
        "{folded}"
    );
}

#[test]
fn a_jump_through_memory_that_a_copy_wrote_is_not_taken_to_go_to_zero() {
    for code in [
        "60205f5f375f51565b33ff",
        "5f5f5f5f335afa5060205f5f3e5f51565b33ff",
        "60205f5f5f335afa505f51565b33ff",
    ] {
        let out = text(code);
        assert!(out.contains("selfdestruct(payable(msg.sender));"), "{out}");
    }
    // Past the end of the call data the copy reads zeros, and nothing can be jumped to at 0.
    let zeros = text("6020365f375f51565b33ff");
    assert!(!zeros.contains("selfdestruct"), "{zeros}");
}

#[test]
fn a_computed_jump_is_followed_for_every_state_that_reaches_it() {
    for code in [
        "366009576002600c565b60005b601101565b005b33ff",
        "366009576000600c565b60025b601101565b005b33ff",
    ] {
        let out = text(code);
        assert!(out.contains("selfdestruct(payable(msg.sender));"), "{out}");
        assert!(out.contains("return;"), "{out}");
    }
}

#[test]
fn another_accounts_balance_is_read_again_after_a_call() {
    let out = text("60043580315f5f5f5f6001865af1509031035f5260205ff3");
    assert!(!out.contains("return 0;"), "{out}");
    assert!(
        out.contains("prev_account_balance = _calldata(4).balance;"),
        "{out}"
    );
    assert!(
        out.contains("return _calldata(4).balance - prev_account_balance;"),
        "{out}"
    );
}

#[test]
fn a_read_is_not_equal_to_itself_across_a_store_that_may_overlap() {
    let out = text("60043580516001602435529051145f5260205ff3");
    assert!(
        !out.contains("return 1;") && !out.contains("return true;"),
        "{out}"
    );
    assert!(
        out.contains("return _memory(_calldata(4)) == prev_mem;"),
        "{out}"
    );
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
    assert!(!out.contains("return msg.sender;"), "{out}");
}

#[test]
fn a_store_a_hash_consumed_stays_when_a_later_plain_read_needs_it() {
    let out = text("600435608052600160206080205560243561001957610020565b6044356080525b60206080f3");
    assert!(out.contains("mem[0x80] = _calldata(4);"), "{out}");
    assert!(out.contains("_return(0x80, 32);"), "{out}");
}

#[test]
fn the_tail_of_a_memory_copy_comes_from_the_matching_source_bytes() {
    let out = text("5f3560805260203560a052603060806101005e6030610100f3");
    assert!(
        out.contains("return (_calldata(0), _memory(0xa0) >> 128);"),
        "{out}"
    );
}

#[test]
fn two_overlapping_writes_in_a_different_order_per_path_are_not_trusted() {
    let out = text(
        "60443561001757600435609052602435608052610024565b6024356080526004356090525b60206090f3",
    );
    assert!(!out.contains("return _calldata(4);"), "{out}");
    assert!(out.contains("_return(0x90, 32);"), "{out}");
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
        out.contains("_calldata(0) | (_calldata(32) < _calldata(64));"),
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
fn a_copy_by_the_identity_built_in_of_any_length_is_a_write() {
    let out = text(
        "6000356102205260203561001557604035610220525b6060356102205161024001526102205160200161022052\
         61022051602001806102a082610220600060045af150506102a0516000556102c05160015500",
    );
    assert!(
        out.contains("success_1 = identity.call(_range(0x220, _memory(0x220) + 32));"),
        "{out}"
    );
    assert!(
        out.contains("mem[0x2a0:+_memory(0x220) + 32] = mem[0x220:+_memory(0x220) + 32];"),
        "{out}"
    );
}

#[test]
fn a_word_read_before_a_store_over_part_of_it_keeps_the_old_value() {
    let out = text(
        "6000356102045260203561001557604035610204525b61020451606035610200526000556102045160015500",
    );
    let named = out
        .find("uint256 prev__memory_0x204 = _memory(0x204);")
        .expect("the old word is named");
    let store = out.find("mem[0x200] = _calldata(96);").expect("the store");
    assert!(named < store, "{out}");
    assert!(
        out.contains("stor_0 = prev__memory_0x204;") && out.contains("stor_1 = _memory(0x204);")
    );
}

#[test]
fn what_a_call_returns_into_a_fixed_word_is_a_write() {
    let out = text(
        "600035610ac05260005b610ac05181556020610ac0600060006000335af15060010180602035116100095700",
    );
    assert!(
        out.contains(
            "_copy_returned(0xac0, 0x0, _returndatasize() < 32 ? _returndatasize() : 32);"
        ),
        "{out}"
    );
}

#[test]
fn a_revert_folded_into_a_require_takes_the_values_its_ways_in_give() {
    let out = text(
        "6000356020358082116100185790604035811161002357005b606035811161002357005b\
         63064a4ec660e01b60005260045260245260446000fd",
    );
    assert!(
        out.contains("(bytes4(0x064a4ec6), _calldata(32), _calldata(0)));")
            && out.contains("(bytes4(0x064a4ec6), _calldata(0), _calldata(32)));"),
        "{out}"
    );
}

#[test]
fn a_word_read_after_a_loop_wrote_it_is_not_the_value_stored_in_the_loop() {
    let out = text(
        "6000608052600060a0525b60a051356080510160805260a05160200160a052606060a0511061000a57\
         60805160005500",
    );
    assert!(
        out.contains("mem[0x80] = _memory(0x80) + _calldata(_memory(0xa0));"),
        "{out}"
    );
    assert!(out.contains("stor_0 = _memory(0x80);"), "{out}");
}

#[test]
fn a_word_a_loop_may_have_written_through_an_index_is_not_the_fill_before_it() {
    let out = text(
        "6060366080376000610100525b33610100516020026080015261010051600101610100526003610100\
         511061000c5760a05160005500",
    );
    assert!(out.contains("stor_0 = _memory(0xa0);"), "{out}");
}

#[test]
fn a_stored_value_is_not_read_back_after_a_helper_wrote_what_it_was_made_from() {
    let out = text(
        "610007610020565b60805160010160a052610018610020565b60a051600055005b6020356100315733\
         60805233600155565b3260805256",
    );
    assert!(out.contains("mem[0xa0] = _memory(0x80) + 1;"), "{out}");
    assert!(out.contains("stor_0 = _memory(0xa0);"), "{out}");
}

#[test]
fn what_a_call_returns_is_a_write_for_a_later_read_of_the_same_memory() {
    let written = "_copy_returned(0x80, 0x0, _returndatasize() < 32 ? _returndatasize() : 32);";
    let as_data = text("60206080600060006000335af1506000600060003560806000305af15000");
    assert!(as_data.contains(written), "{as_data}");
    assert!(
        as_data.contains(".call(_range(0x80, _calldata(0)));"),
        "{as_data}"
    );
    // An address the call data gives is taken to lie apart from a fixed one.
    let by_pointer = text("60206080600060006000335af1506000355160005500");
    assert!(!by_pointer.contains("_copy_returned("), "{by_pointer}");
    assert!(
        by_pointer.contains("stor_0 = _memory(_calldata(0));"),
        "{by_pointer}"
    );
}

#[test]
fn a_word_of_the_output_area_is_read_from_the_answer_the_call_gave() {
    let untested = text("60206080600060006000335af15060805160005500");
    assert!(
        untested.contains("stor_0 = _word(returned_1, 0);"),
        "{untested}"
    );
    assert!(!untested.contains("_copy_returned("), "{untested}");
    let tested = text("60206080600060006000335af15060203d101561001c5760006000fd5b60805160005500");
    assert!(
        tested.contains("require(_returndatasize() >= 32);"),
        "{tested}"
    );
    assert!(
        tested.contains("stor_0 = _word(returned_1, 0);"),
        "{tested}"
    );
}

#[test]
fn a_constant_masked_into_a_higher_byte_is_the_value_of_the_field_at_that_byte() {
    use evmdec::expr::{calldataload, intern, konst, konst_u64, op2, Node};
    use evmdec::opcode as op;
    let key = calldataload(konst_u64(4));
    let old = intern(Node::SLoad(key, false, 0));
    let keep = konst(!evmdec::U256::from_u64(0xff00));
    let stored = op2(op::OR, op2(op::AND, old, keep), konst_u64(0x100));
    let write = evmdec::ssa::field_write(key, stored).expect("a field write");
    assert_eq!((write.bit_offset, write.bits), (8, 8));
    assert_eq!(write.value, konst_u64(1));
    let low = op2(
        op::OR,
        op2(op::AND, old, konst(!evmdec::U256::from_u64(0xff))),
        konst_u64(1),
    );
    let write = evmdec::ssa::field_write(key, low).expect("a field write");
    assert_eq!(
        (write.bit_offset, write.bits, write.value),
        (0, 8, konst_u64(1))
    );
}

#[test]
fn a_message_padded_with_zeros_from_past_the_call_data_is_printed_as_its_text() {
    let out = text(
        "60003561004857600d60c0527f696e76616c696420737461746500000000000000000000000000000000\
         00000060e05260133660ed376308c379a0608052602060a0526064609cfd5b00",
    );
    assert!(
        out.contains("require(_calldata(0) != 0, \"invalid state\");"),
        "{out}"
    );
    assert!(!out.contains("msg.data.length"), "{out}");
    let read = text("60203660803760a05160005500");
    assert!(read.contains("stor_0 = 0;"), "{read}");
}

#[test]
fn a_literal_copied_from_the_code_is_printed_as_its_text() {
    let out = text(
        "6028600e6080396000356080a00045524332303a207472616e7366657220616d6f756e742065786365\
         65647320616c6c6f77616e6365",
    );
    assert!(
        out.contains("mem[0x80:+40] = \"ERC20: transfer amount exceeds allowance\";"),
        "{out}"
    );
}

#[test]
fn a_call_is_printed_with_the_parts_its_head_points_at() {
    let copied = text(
        "63aabbccdd60e01b608052600435608452604060a45260443560c452604435606460e43760006000604435\
         60640160806000335af15000",
    );
    assert!(
        copied.contains(
            ".call(abi.encodeWithSelector(bytes4(0xaabbccdd), _calldata(4), msg.data[100:100 + _calldata(68)]));"
        ),
        "{copied}"
    );
    assert!(!copied.contains("mem[0x"), "{copied}");
    let fixed = text(
        "63aabbccdd60e01b608052600435608452606060a45260a060c452600560e4527f68656c6c6f0000000000\
         0000000000000000000000000000000000000000000061010452600261012452336101445230610164\
         526000600061010460806000335af15000",
    );
    assert!(
        fixed.contains(
            "bytes4(0xaabbccdd), _calldata(4), \"hello\", [msg.sender, address(this)]));"
        ),
        "{fixed}"
    );
}

#[test]
fn a_word_that_only_looks_like_a_pointer_leaves_the_call_as_its_words() {
    let out = text(
        "63a9059cbb60e01b608052336084526040 60a45260006000604460806000335af15000"
            .replace(' ', "")
            .as_str(),
    );
    assert!(
        out.contains("abi.encodeWithSignature(\"transfer(address,uint256)\", msg.sender, 64)"),
        "{out}"
    );
}

#[test]
fn a_hash_of_values_written_at_odd_places_is_printed_as_those_values() {
    let out = text("61190160f01b60805260043560825260243560a252604260802060005500");
    assert!(
        out.contains("stor_0 = uint256(keccak256(abi.encodePacked(bytes2(0x1901), _calldata(4), _calldata(36))));"),
        "{out}"
    );
}

#[test]
fn a_hash_of_whole_words_is_printed_as_an_encoding_that_pads_each_value() {
    // mstore(0, caller); mstore(0x20, 4); sstore(0, keccak256(0, 64))
    let out = text("336000526004602052604060002060005500");
    assert!(
        out.contains("keccak256(abi.encode(msg.sender, 4))"),
        "{out}"
    );
}

#[test]
fn a_whole_word_in_a_packed_hash_is_not_printed_as_a_narrower_type() {
    // mstore8(0x80, 0xff); mstore(0x81, calldataload(4) & 0xffffffffffffffff); sstore(0, keccak256(0x80, 33))
    let out = text("60ff60805360043567ffffffffffffffff16608152602160802060005500");
    assert!(out.contains("uint256(uint64(_calldata(4)))"), "{out}");
}

#[test]
fn the_arguments_of_a_call_stop_before_the_first_word_no_write_is_known_for() {
    let out =
        text("63aabbccdd60e01b60805260043560845236600060a437600060003660240160806000335af15000");
    assert!(
        out.contains(".call(_range(0x80, msg.data.length + 36));"),
        "{out}"
    );
    assert!(
        out.contains("mem[0xa4:+msg.data.length] = msg.data[0:+msg.data.length];"),
        "{out}"
    );
}

#[test]
fn a_test_that_ends_in_the_invalid_opcode_is_an_assert_with_no_panic_data() {
    let out = text("60003561000857fe5b3360005500");
    assert!(out.contains("assert(_calldata(0) != 0);"), "{out}");
    assert!(!out.contains("_panic("), "{out}");
}

#[test]
fn the_selector_stored_where_the_data_of_a_call_starts_is_named() {
    let out = text("63a9059cbb60e01b608052366000608437600060003660040160806000335af15000");
    assert!(
        out.contains("mem[0x80] = bytes32(transfer.selector);"),
        "{out}"
    );
    assert!(
        out.contains(".call(_range(0x80, msg.data.length + 4));"),
        "{out}"
    );
}

#[test]
fn the_address_a_helper_that_never_returns_was_to_go_back_to_is_no_function() {
    let repeated = text("61000761000e565b5b33600055005b6000356100085760006000fd");
    assert!(!repeated.contains("orphan_"), "{repeated}");
    assert_eq!(
        repeated.matches("stor_0 = msg.sender;").count(),
        1,
        "{repeated}"
    );
    let own = text("61000761000d565b33600055005b60006000fd");
    assert!(own.contains("function orphan_0x7("), "{own}");
    assert!(own.contains("stor_0 = msg.sender;"), "{own}");
}

#[test]
fn a_value_tested_against_zero_and_ordered_against_another_is_a_number() {
    let out = text(
        "60003560e01c6312345678146100155760006000fd5b6004358015156100255760006000fd5b806000\
         5410156100355760006000fd5b60005260056020523360406000205500",
    );
    assert!(out.contains("function func_12345678(uint256 key)"), "{out}");
    assert!(out.contains("require(stor_0 >= key);"), "{out}");
}

#[test]
fn the_cut_a_selector_makes_through_an_argument_is_no_field_of_storage() {
    let out = text(
        "63aabbccdd60e01b6080523360845273ffffffffffffffffffffffffffffffffffffffff6000541660\
         a4524260c45260006000606460806000335af15000",
    );
    assert!(out.contains("address stor_0;"), "{out}");
    assert!(!out.contains("uint32"), "{out}");
}

#[test]
fn a_write_through_an_index_tested_to_be_small_does_not_reach_the_words_past_its_list() {
    let tested = text(
        "33610200526003600035106100145760006000fd5b426000356020026080015261020051600055600035\
         6020026080015160015500",
    );
    assert!(tested.contains("require(_calldata(0) < 3);"), "{tested}");
    assert!(tested.contains("stor_0 = msg.sender;"), "{tested}");
    let untested =
        text("33610200524260003560200260800152610200516000556000356020026080015160015500");
    assert!(untested.contains("stor_0 = _memory(0x200);"), "{untested}");
}

#[test]
fn a_value_under_the_mask_one_is_a_bit_test_and_no_logical_and() {
    let out = text("335f52601b60205260405f20546001165f5260205ff3");
    assert!(out.contains("return stor_27[msg.sender] & 1;"), "{out}");
    assert!(!out.contains("&&"), "{out}");
}

#[test]
fn the_overflow_test_of_a_folded_helper_is_told_by_its_sum_or_printed() {
    let sum = text(
        "60806040526100114280506001610025565b5f556100206024356003610025565b600155005b8067ffff\
         ffffffffffff03821161003a570190565b634e487b7160e01b5f52601160045260245ffd",
    );
    assert!(
        sum.contains("stor_0 = uint64(block.timestamp) + 1;"),
        "{sum}"
    );
    // A whole word is no 64-bit number, so a sum of it does not tell the 64-bit test.
    in_order(
        &sum,
        &[
            "if (_calldata(36) > 0xfffffffffffffffc) _panic(0x11);",
            "unchecked { stor_1 = (_calldata(36) + 3); }",
        ],
    );
    let product = text(
        "60806040526100116004356001610025565b5f556100206024356003610025565b600155005b8067ffff\
         ffffffffffff03821161003a570290565b634e487b7160e01b5f52601160045260245ffd",
    );
    let test = "if (_calldata(36) > 0xfffffffffffffffc) _panic(0x11);";
    assert!(product.contains(test), "{product}");
    assert!(
        product.contains("unchecked { stor_1 = (_calldata(36) * 3); }"),
        "{product}"
    );
}

#[test]
fn a_variable_stored_in_a_loop_is_advanced_under_its_own_name() {
    let out = text("6004355f5b8061010011610013576101005ff35b8181529060a0019060200161000456");
    assert!(out.contains("_store(v2, v1);"), "{out}");
    assert!(out.contains("v1 = v1 + 160;"), "{out}");
    assert!(!out.contains("_store(v2, _memory(v2) + 160);"), "{out}");
}

#[test]
fn a_hash_of_memory_written_again_before_its_use_is_named_where_it_was_taken() {
    let out = bodies("600435806024359052600560205260408120604435825260205260409020545f5260205ff3");
    let chain = [
        "_store(_calldata(4), _calldata(36));",
        "mem[0x20] = 5;",
        "v1 = uint256(keccak256(_range(_calldata(4), 64)));",
        "_store(_calldata(4), _calldata(68));",
        "mem[0x20] = v1;",
        "return (stor[uint256(keccak256(_range(_calldata(4), 64)))]);",
    ];
    let mut from = 0;
    for line in chain {
        let at = out[from..].find(line);
        from += at.unwrap_or_else(|| panic!("{line} is missing or out of order in\n{out}"));
    }
}

#[test]
fn a_store_through_an_index_into_the_fixed_words_reaches_a_later_hash_of_them() {
    let out =
        text("60806040526119015f52602435602052600435602016604435905260405f205f55604051602090f3");
    assert!(
        out.contains("_store(_calldata(4) & 32, _calldata(68));"),
        "{out}"
    );
    assert!(
        out.contains("stor_0 = uint256(keccak256(_range(0x0, 64)));"),
        "{out}"
    );
    assert!(
        !out.contains("keccak256(abi.encodePacked(6401, _calldata(36)))"),
        "{out}"
    );
}

#[test]
fn each_part_of_a_packed_slot_the_code_reads_has_a_name_or_the_slot_stays_whole() {
    let member = text(
        "335f52603560205260405f2060010180546fffffffffffffffffffffffffffffffff166080525460801c\
         60a05260406080f3",
    );
    assert!(member.contains("uint128 field1_0;"), "{member}");
    assert!(member.contains("uint128 field1_16;"), "{member}");
    assert!(
        member.contains("return (stor_53[msg.sender].field1_0, stor_53[msg.sender].field1_16);"),
        "{member}"
    );
    let value = text("335f52600160205260405f20805460ff166080525460881c60a05260406080f3");
    assert!(
        value.contains("mapping(address => uint256) stor_1;"),
        "{value}"
    );
    assert!(
        value.contains("return (uint8(stor_1[msg.sender]), stor_1[msg.sender] >> 136);"),
        "{value}"
    );
}

#[test]
fn the_words_stored_for_a_call_are_its_arguments_or_stay_as_stores() {
    let counted = text(
        "6080604052608435600435816020015260243581604001526044358160600152606435816080015260208182\
         602001806084350360a0019060015afa50602090f3",
    );
    let call = "(success_1, ) = address(0x0000000000000000000000000000000000000001).staticcall(\
                abi.encode(_calldata(4), _calldata(36), _calldata(68), _calldata(100)));";
    assert!(counted.contains(call), "{counted}");
    let raw = text(
        "608060405260843560043581526024358160200152604435816040015260208160a4358360015afa610056\
         576308c379a060e01b815260208160040152600581602401526468656c6c6f60d81b8160440152606490fd\
         5b602090f3",
    );
    for line in [
        "_store(_calldata(132), _calldata(4));",
        "_store(_calldata(132) + 32, _calldata(36));",
        "_store(_calldata(132) + 64, _calldata(68));",
        ".staticcall(_range(_calldata(132), _calldata(164)));",
    ] {
        assert!(raw.contains(line), "{line} is missing in\n{raw}");
    }
}

fn in_order(out: &str, lines: &[&str]) {
    let mut from = 0;
    for line in lines {
        let at = out[from..].find(line);
        from += at.unwrap_or_else(|| panic!("{line} is missing or out of order in\n{out}"));
    }
}

#[test]
fn a_read_is_printed_on_the_side_of_a_store_or_a_create_the_code_made_it_on() {
    let created =
        text("60806040525f5f5ff061001190610021565b5f5561001c33610021565b600155005b3f9056");
    in_order(
        &created,
        &["deployed_1 = create(", "stor_0 = deployed_1.codehash;"],
    );
    assert!(!created.contains("prev_code_hash"), "{created}");
    let tested = text(
        "6080604052610012600435602435610027565b610020604435606435610027565b6020600435f35b8151\
         610031575f5ffd5b905256",
    );
    in_order(
        &tested,
        &[
            "require(_memory(_calldata(4)) != 0);",
            "_store(_calldata(4), _calldata(36));",
            "require(_memory(_calldata(68)) != 0);",
            "_store(_calldata(68), _calldata(100));",
        ],
    );
    let shortened = text(
        "6080604052600435806001815103602001015160f81c61002382600181510361003e565b61002b575f5f\
         fd5b61003960443560243561003e565b602090f35b905256",
    );
    in_order(
        &shortened,
        &[
            "uint256 prev__memory__calldata_4 = _memory(_calldata(4));",
            "_store(_calldata(4), _memory(_calldata(4)) - 1);",
            "require(_memory(prev__memory__calldata_4 + 31 + _calldata(4)) >> 248 != 0);",
        ],
    );
    let gathered = text(
        "608060405261000c61002d565b6040518051600435826020015260243582525f5561002861002d565b60\
         4090f35b5f5f5f5f5f335af15056",
    );
    in_order(
        &gathered,
        &[
            "uint256 prev_s1_w0 = s1.w0;",
            "s1.w0 = _calldata(36);",
            "stor_0 = prev_s1_w0;",
        ],
    );
}

#[test]
fn the_sum_a_folded_helper_hands_back_is_the_sum_it_tested() {
    let out = text(
        "60806040526004355161001061004c565b61001b906001610037565b5f5561002a6024356003610037565b\
         60015561003561004c565b005b8067ffffffffffffffff038211610057570190565b5f5f5f5f5f335af150\
         565b634e487b7160e01b5f52601160045260245ffd",
    );
    in_order(
        &out,
        &[
            "if (_memory(_calldata(4)) > 0xfffffffffffffffe) _panic(0x11);",
            "unchecked { stor_0 = (_memory(_calldata(4)) + 1); }",
        ],
    );
    assert!(!out.contains("prev_"), "{out}");
}

#[test]
fn a_word_read_before_a_store_keeps_its_old_value_in_the_blocks_after_it() {
    let branched = text("6004358051600182526024356012575f55005b60015500");
    in_order(
        &branched,
        &[
            "uint256 prev__memory__calldata_4 = _memory(_calldata(4));",
            "_store(_calldata(4), 1);",
            "stor_1 = prev__memory__calldata_4;",
            "stor_0 = prev__memory__calldata_4;",
        ],
    );
    let stored_twice = text("6004358051602435600f57600182525b600282525f5500");
    in_order(
        &stored_twice,
        &[
            "uint256 prev__memory__calldata_4 = _memory(_calldata(4));",
            "_store(_calldata(4), 1);",
            "_store(_calldata(4), 2);",
            "stor_0 = prev__memory__calldata_4;",
        ],
    );
}

#[test]
fn a_store_that_puts_an_old_word_back_is_printed_after_the_hash_taken_before_it() {
    let plain = text("600435805160078252604082209082525f5500");
    in_order(
        &plain,
        &[
            "uint256 prev__memory__calldata_4 = _memory(_calldata(4));",
            "_store(_calldata(4), 7);",
            "v1 = uint256(keccak256(_range(_calldata(4), 64)));",
            "_store(_calldata(4), prev__memory__calldata_4);",
            "stor_0 = v1;",
        ],
    );
    let folded = text(
        "6080604052600d600435601d565b5f556018602435601d565b600155005b80516007825260408220908252\
         90509056",
    );
    in_order(
        &folded,
        &[
            "_store(_calldata(4), 7);",
            "v1 = uint256(keccak256(_range(_calldata(4), 64)));",
            "_store(_calldata(4), prev__memory__calldata_4);",
            "stor_0 = v1;",
            "_store(_calldata(36), 7);",
            "v2 = uint256(keccak256(_range(_calldata(36), 64)));",
            "_store(_calldata(36), prev__memory__calldata_36);",
            "stor_1 = v2;",
        ],
    );
    // Stored back with nothing stored to it in between, a word is unchanged.
    let unchanged = text("6004358051815200");
    assert!(!unchanged.contains("_store("), "{unchanged}");
}

#[test]
fn a_sum_tested_in_a_type_narrower_than_a_word_is_printed_in_that_type() {
    let narrow = text(
        "6080604052438067fffffffffffffffe10601a576001015f55005b634e487b7160e01b5f52601160045260\
         245ffd",
    );
    assert!(
        narrow.contains("stor_0 = uint64(block.number) + 1;"),
        "{narrow}"
    );
    // A whole word held to the same limit is no 64-bit number, so its test stays.
    let wide = text(
        "60806040526004358067fffffffffffffffe10601c576001015f55005b634e487b7160e01b5f5260116004\
         5260245ffd",
    );
    in_order(
        &wide,
        &[
            "if (0xfffffffffffffffe < _calldata(4)) _panic(0x11);",
            "unchecked { stor_0 = (_calldata(4) + 1); }",
        ],
    );
    let product = text(
        "6080604052438067555555555555555510601a576003025f55005b634e487b7160e01b5f52601160045260\
         245ffd",
    );
    assert!(
        product.contains("stor_0 = uint64(block.number) * 3;"),
        "{product}"
    );
}

#[test]
fn a_folded_helper_stores_and_copies_in_the_order_its_code_does() {
    let out = text("6080604052601260a06004356024356018565b604060a0f35b8082845e5f8184015250505056");
    in_order(
        &out,
        &[
            "mem[ptr1 + 32:+_calldata(36)] = mem[_calldata(4):+_calldata(36)];",
            "mem[_calldata(36) + 160] = 0;",
        ],
    );
}

#[test]
fn a_head_word_a_folded_encoder_stores_after_its_copy_still_gives_the_call_its_arguments() {
    let out = text(
        "60806040526040516020815260043581602001528060400163aabbccdd60e01b8152604081600401526036\
         81604401836024356044565b5f5f6084835f6044355af150005b81518084528083602001856020015e8184\
         60209003525050505056",
    );
    let call = "address(uint160(_calldata(68))).call(abi.encodeWithSelector(bytes4(0xaabbccdd), abi.encode(_calldata(4)), _calldata(36)));";
    assert!(out.contains(call), "{out}");
}

#[test]
fn a_step_that_wraps_in_a_range_test_is_marked_as_untested() {
    let out = text(
        "60806040526004358051808201515f55606381036102e29010600155602435602357005b634e487b7160e0\
         1b5f52601160045260245ffd",
    );
    // The length is also an offset into memory, which is why its sums print bare elsewhere.
    assert!(
        out.contains("stor_0 = _memory(_calldata(4) + _memory(_calldata(4)));"),
        "{out}"
    );
    assert!(
        out.contains("unchecked { stor_1 = (_memory(_calldata(4)) - 99) < 738; }"),
        "{out}"
    );
}

#[test]
fn a_call_with_two_parts_of_a_length_the_code_works_out_is_printed_with_both() {
    let out = text(
        "608060405260405163aabbccdd60e01b815260408160040152600435808260440152806100648360640137\
         601f01601f191680606001826024015260243580828401606401528061020083850160840137601f01601f\
         1916016084015f5f82845f6044355af15000",
    );
    let call = "abi.encodeWithSelector(bytes4(0xaabbccdd), msg.data[100:100 + _calldata(4)], \
                msg.data[512:512 + _calldata(36)])";
    assert!(out.contains(call), "{out}");
    assert!(
        !out.contains("mem[ptr1") && !out.contains("_store(ptr1"),
        "{out}"
    );
}

#[test]
fn a_whole_word_in_packed_call_data_is_not_printed_as_a_narrower_type() {
    let out = text(
        "60806040526040516327a9b42460e01b815260043573ffffffffffffffffffffffffffffffffffffffff16\
         81600401526431494e434860d81b81602401525f5f6029835f6024355af15000",
    );
    let data = "abi.encodePacked(bytes4(0x27a9b424), uint256(address(uint160(_calldata(4)))), bytes5(0x31494e4348))";
    assert!(out.contains(data), "{out}");
}

#[test]
fn a_slot_a_scaled_index_past_a_mapping_value_names_is_a_field_of_one_record_in_a_list() {
    // mstore(0, 5); mstore(0x20, caller); sstore(keccak256(0, 64) + calldataload(4) * 3 + 1, 42)
    let out = text("600560005233602052604060002060043560030201600101602a905500");
    assert!(out.contains("[_calldata(4)].field1 = 42"), "{out}");
    assert!(!out.contains(".fieldarg0"), "{out}");
}

#[test]
fn a_value_stored_to_a_slot_is_not_printed_as_the_slot_after_a_call() {
    let out = text("600c5460010180600c555f5f5f5f5f335af150600c54145f5260205ff3");
    assert!(!out.contains("stor_12 == stor_12"), "{out}");
    assert!(out.contains("stor_12 = prev_stor_12 + 1;"), "{out}");
    assert!(out.contains("return stor_12 == prev_stor_12 + 1;"), "{out}");
}

#[test]
fn a_word_read_before_a_store_a_few_bytes_off_it_is_named_before_that_store() {
    let out = text("6004358060040151601182526022826004015260005260205ff3");
    in_order(
        &out,
        &[
            "uint256 prev__memory__calldata_4_4 = _memory(_calldata(4) + 4);",
            "_store(_calldata(4), 17);",
            "_store(_calldata(4) + 4, 34);",
            "mem[0x0] = prev__memory__calldata_4_4;",
        ],
    );
}

#[test]
fn a_pointer_handed_to_a_helper_is_the_one_read_before_the_free_pointer_moved() {
    let out = bodies(
        "6080604052600a6015565b60106015565b60205ff35b5f5b600101803560175750\
         604051806040016040526031816038565b5f35905250565b6020019056",
    );
    assert!(out.contains("_store(ptr1 + 32, _calldata(0));"), "{out}");
    assert!(!out.contains("ptr2"), "{out}");
}

#[test]
fn a_helper_parameter_is_a_whole_word_when_a_caller_or_the_body_shows_more_bits() {
    let negated = text(
        "6080604052601f6004356fffffffffffffffffffffffffffffffff16602c565b602a6004355f03602c56\
         5b005b5f5b6001018035602e57506fffffffffffffffffffffffffffffffff165f5556",
    );
    assert!(negated.contains("function func_0x2c(uint256 "), "{negated}");
    let shifted = text(
        "6080604052600d6004356018565b60166024356018565b005b5f5b6001018035601a5750\
         8073ffffffffffffffffffffffffffffffffffffffff165f5560a01c60015556",
    );
    assert!(shifted.contains("function func_0x18(uint256 "), "{shifted}");
}

#[test]
fn a_copy_from_the_end_of_the_call_data_is_printed_as_the_zeros_it_writes() {
    let out = text("60403660a0375f3560a0f3");
    assert!(out.contains("mem[0xa0] = 0; mem[0xc0] = 0;"), "{out}");
    assert!(!out.contains("msg.data.length"), "{out}");
}

#[test]
fn a_parameter_declared_narrow_is_a_whole_word_in_packed_call_data() {
    let out = text(
        "6080604052600d6004356018565b60166024356018565b005b5f5b6001018035601a5750631122334460e01b\
         6080528060845264313131313160d81b60a4525f5f602960805f855af1505056",
    );
    assert!(out.contains("function func_0x18(address target)"), "{out}");
    assert!(
        out.contains("abi.encodePacked(bytes4(0x11223344), uint256(target), bytes5(0x3131313131))"),
        "{out}"
    );
}

#[test]
fn a_folded_helper_that_reads_a_word_it_stored_reads_it_after_the_store() {
    let out = text(
        "6080604052600c5f356013565b6020355f35f35b8051816020015260058152806020015181604001525056",
    );
    assert!(!out.contains("prev_"), "{out}");
    in_order(
        &out,
        &[
            "_store(_calldata(0) + 32, _memory(_calldata(0)));",
            "_store(_calldata(0), 5);",
            "_store(_calldata(0) + 64, _memory(_calldata(0) + 32));",
        ],
    );
}

#[test]
fn a_mapping_of_mappings_is_declared_with_its_keys_in_the_order_they_are_used() {
    let out = text(
        "335f52600160205260405f2060205260043577ffffffffffffffffffffffffffffffffffffffffffffffff\
         165f5260405f206001905500",
    );
    assert!(
        out.contains("mapping(address => mapping(uint192 => uint256)) stor_1;"),
        "{out}"
    );
    assert!(
        out.contains("stor_1[msg.sender][uint192(_calldata(4))] = 1;"),
        "{out}"
    );
}

#[test]
fn a_temporary_made_on_one_arm_is_not_used_on_the_other() {
    let out = text(
        "5f35608c5760043560243502604435016000526064356084350260a4350160205260c43560e43502\
         60043501604052602435604435026064350160605260843560a4350260c4350160805260e4356004\
         35026024350160a052604435606435026084350160c05260a43560c4350260e4350160e052610100\
         5f2060016020356085575b55005b5060026082565b5f6003608256",
    );
    let arms: Vec<&str> = out.split("} else {").collect();
    let last = arms.last().expect("an else arm");
    let used = last.contains("v1 = t");
    assert!(!used || last.contains("uint256 t"), "{out}");
}

fn fixture(name: &str) -> String {
    let path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testdata/source");
    let hex = std::fs::read_to_string(path.join(name)).expect("fixture");
    text(hex.trim())
}

#[test]
fn a_word_read_above_its_first_field_is_declared_as_the_whole_word() {
    // allowed[a][b] packs an amount, an expiry and a nonce. The code reads all three.
    let out = fixture("Packed.hex");
    assert!(
        out.contains("mapping(address => mapping(address => uint256)) stor_0"),
        "{out}"
    );
}

#[test]
fn a_stored_number_written_past_its_top_bits_is_declared_as_the_whole_word() {
    // receipts[voter] packs a flag, a small number and a vote count into one word.
    let out = fixture("Ballot.hex");
    assert!(out.contains("mapping(address => uint256) field2"), "{out}");
    assert!(!out.contains("mapping(address => uint8)"), "{out}");
}

#[test]
fn a_stored_word_tested_at_its_lowest_bit_and_also_shifted_down_is_no_flag() {
    // signatures is a list of strings, and each string's head word keeps its length above bit 0.
    let out = fixture("Calls.hex");
    assert!(!out.contains("bool[] field1"), "{out}");
}

#[test]
fn the_fields_of_a_struct_parameter_take_the_types_the_signature_gives_them() {
    // exactInputSingle takes one static struct of eight fields, the last a uint160.
    let out = fixture("Swap.hex");
    assert!(out.contains("uint256 arg6, uint160 arg7)"), "{out}");
    assert!(
        out.contains("(address arg0, address arg1, uint24 arg2"),
        "{out}"
    );
}

#[test]
fn a_function_the_selector_table_marks_as_refusing_value_is_not_payable() {
    // Runtime code of a Vyper 0.3.10 pool. Its table gives each entry a flag that rejects value.
    let out = fixture("StableSwapNG.hex");
    assert!(!out.contains("external payable"), "{out}");
    assert!(out.contains("function exchange(int128 arg0, int128 arg1, uint256 arg2, uint256 arg3) external returns"), "{out}");
}

#[test]
fn a_call_given_only_the_stipend_whose_result_is_kept_is_a_send() {
    let kept = text("6000600060006000602435600435602435156108fc02f160005500");
    let send = "success_1 = payable(address(uint160(_calldata(4)))).send(_calldata(36));";
    assert!(kept.contains(send), "{kept}");
    // With all the gas left it is a plain call, which a receiver may spend freely.
    let plain = text("60006000600060006024356004355af160005500");
    assert!(
        plain.contains(".call{value: _calldata(36)}(\"\");"),
        "{plain}"
    );
    assert!(!plain.contains(".send("), "{plain}");
}
