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
