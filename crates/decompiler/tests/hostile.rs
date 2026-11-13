use evmdec::decompile::{decompile, Options};
use std::time::Duration;

fn hex(text: &str) -> Vec<u8> {
    evmdec::hex::decode(text).expect("valid hex")
}

fn repeated(start: &str, unit: &str, times: usize, end: &str) -> Vec<u8> {
    hex(&format!("{start}{}{end}", unit.repeat(times)))
}

// A server worker has a 2 MiB stack, so every input here has to finish on one.
fn survives(code: Vec<u8>) {
    let worker = std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(move || {
            evmdec::clock::run(Duration::from_secs(120), || {
                let contract = decompile(&code, &Options::default());
                evmdec::analyze::analyze(&contract).findings.len()
            })
        })
        .expect("thread");
    let finished = worker.join().expect("no panic and no stack overflow");
    assert!(finished.is_some(), "the input did not finish in time");
}

#[test]
fn a_long_chain_of_blocks_that_jump_to_the_next() {
    let mut code = Vec::new();
    for i in 0..1500usize {
        let next = 5 * (i + 1);
        code.extend([0x5b, 0x61, (next >> 8) as u8, next as u8, 0x56]);
    }
    code.extend([0x5b, 0x00]);
    survives(code);
}

#[test]
fn thousands_of_empty_blocks_in_a_row() {
    survives(repeated("", "5b", 5000, "00"));
}

#[test]
fn a_long_run_of_checks_one_after_another() {
    let mut code = Vec::new();
    for i in 0..3000usize {
        let next = code.len() + 11;
        code.extend([0x61, (i >> 8) as u8, i as u8, 0x35]);
        code.extend([0x61, (next >> 8) as u8, next as u8, 0x57]);
        code.extend([0x5f, 0x5f, 0xfd, 0x5b]);
    }
    code.push(0x00);
    survives(code);
}

#[test]
fn thousands_of_branches_to_one_shared_end() {
    let count = 3000usize;
    let end = count * 8;
    let mut code = Vec::new();
    for i in 0..count {
        code.extend([0x61, (i >> 8) as u8, i as u8, 0x35]);
        code.extend([0x61, (end >> 8) as u8, end as u8, 0x57]);
    }
    code.extend([0x5b, 0x00]);
    survives(code);
}

#[test]
fn a_value_nested_thousands_of_levels_deep() {
    survives(repeated("6000", "35", 7000, "60005500"));
    survives(repeated("34", "3318", 16000, "60ff1660005500"));
}

#[test]
fn empty_blocks_that_jump_to_each_other_in_a_ring() {
    survives(hex("3460065700005b600a565b600656"));
}

#[test]
fn a_value_that_shares_itself_on_both_sides_at_every_level() {
    survives(repeated("34", "8060011c18", 34, "60ff1660005500"));
    survives(repeated("34", "8060011b17", 30, "60005500"));
    survives(repeated("5f35", "8060011c01", 40, "5600"));
}

#[test]
fn a_swap_reached_after_more_pops_than_the_stack_holds() {
    survives(repeated("", "50", 1023, "90"));
}

#[test]
fn a_call_to_the_signature_check_with_no_input() {
    survives(hex("6000600060006000600060015af15000"));
}

#[test]
fn a_code_copy_whose_offset_and_length_wrap() {
    survives(hex("606e67ffffffffffffff9c60003900"));
}

#[test]
fn a_loop_that_hashes_megabytes_on_every_pass() {
    survives(hex("5f3560e01c631122334414600f57005b62ffffff5f2050600f56"));
}

#[test]
fn a_loop_that_logs_megabytes_on_every_pass() {
    survives(hex(
        "5f3560e01c631122334414600f57005b600162ffffff536101005b62ffffff5fa06001900380601a5700",
    ));
}

#[test]
fn many_reads_through_a_deep_pointer_after_many_writes() {
    let mut code = repeated("5f35", "34810201", 1000, "");
    for word in 0..256usize {
        let at = 32 * word;
        code.extend([0x33, 0x81, 0x61, (at >> 8) as u8, at as u8, 0x01, 0x52]);
    }
    code.extend(repeated("", "5f5150", 1000, "5000"));
    survives(code);
}

#[test]
fn hundreds_of_calls_before_hundreds_of_stores() {
    let (calls, stores) = (300usize, 300usize);
    let mut code = vec![0x36, 0x62, 0, 0, 0, 0x57];
    for i in 0..calls {
        let next = 6 + (i + 1) * 23;
        code.push(0x5b);
        code.extend([0x60, 0x00].repeat(5));
        code.extend([0x33, 0x5a, 0xf1, 0x50, 0x34, 0x62]);
        code.extend([
            (next >> 16) as u8,
            (next >> 8) as u8,
            next as u8,
            0x57,
            0x34,
            0x50,
        ]);
    }
    code.extend([0x5b, 0x00]);
    let branch = code.len();
    code[2..5].copy_from_slice(&[(branch >> 16) as u8, (branch >> 8) as u8, branch as u8]);
    code.push(0x5b);
    code.extend([0x34, 0x34, 0x55].repeat(stores));
    code.push(0x00);
    survives(code);
}

#[test]
fn thousands_of_stores_in_one_block() {
    let mut memory = Vec::new();
    let mut storage = Vec::new();
    for i in 0..6000usize {
        let at = 0x10000 + 32 * i;
        memory.extend([
            0x60,
            0x01,
            0x62,
            (at >> 16) as u8,
            (at >> 8) as u8,
            at as u8,
            0x52,
        ]);
        storage.extend([0x60, 0x01, 0x61, (i >> 8) as u8, i as u8, 0x55]);
    }
    memory.extend([0x60, 0x00, 0x60, 0x00, 0xf3]);
    storage.push(0x00);
    survives(memory);
    survives(storage);
}

#[test]
fn tens_of_thousands_of_code_copies_or_empty_blocks() {
    survives(repeated("", "39", 30_000, ""));
    survives(repeated("", "5b", 30_000, "00"));
}

#[test]
fn a_dispatcher_with_thousands_of_entries() {
    let count = 3000u32;
    let end = 4 + count as usize * 11;
    let mut code = vec![0x5f, 0x35, 0x60, 0xe0, 0x1c];
    for i in 0..count {
        code.extend([0x80, 0x63]);
        code.extend(i.wrapping_mul(0x9e37_79b1).to_be_bytes());
        code.extend([0x14, 0x61, (end >> 8) as u8, end as u8, 0x57]);
    }
    assert_eq!(code.len(), end + 1);
    code.extend([0x00, 0x5b, 0x00]);
    code[end + 1] = 0x5b;
    survives(code);
}
