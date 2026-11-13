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
