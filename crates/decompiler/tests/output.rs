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
