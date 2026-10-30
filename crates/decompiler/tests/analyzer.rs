//! The analyzer on hand-assembled contracts with known defects.

use evmdec::analyze::{self, Severity};
use evmdec::decompile::{self, Options};

/// Tiny assembler: mnemonics with immediates, e.g. "PUSH1 0x80". Labels: `:name` defines,
/// `PUSH2 @name` references (patched to 2 bytes).
fn asm(src: &str) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    let mut labels = std::collections::HashMap::new();
    let mut fixups: Vec<(usize, String)> = Vec::new();
    let opcodes: std::collections::HashMap<&str, u8> = (0u8..=255)
        .filter_map(|o| evmdec::opcode::info(o).map(|i| (i.name, o)))
        .collect();
    for tok in src.split_whitespace() {
        if let Some(l) = tok.strip_prefix(':') {
            labels.insert(l.to_string(), out.len());
            continue;
        }
        if let Some(l) = tok.strip_prefix('@') {
            fixups.push((out.len(), l.to_string()));
            out.extend_from_slice(&[0, 0]);
            continue;
        }
        if let Some(h) = tok.strip_prefix("0x") {
            let bytes = evmdec::hex::decode(h).unwrap();
            out.extend_from_slice(&bytes);
            continue;
        }
        out.push(
            *opcodes
                .get(tok)
                .unwrap_or_else(|| panic!("unknown mnemonic {tok}")),
        );
    }
    for (pos, l) in fixups {
        let t = labels[&l] as u16;
        out[pos] = (t >> 8) as u8;
        out[pos + 1] = t as u8;
    }
    out
}

/// Dispatcher: selector 0xaaaaaaaa -> body at label `f`, anything else reverts.
fn dispatcher(body: &str) -> Vec<u8> {
    asm(&format!(
        "PUSH1 0x80 PUSH1 0x40 MSTORE PUSH1 0x00 CALLDATALOAD PUSH1 0xe0 SHR PUSH4 0xaaaaaaaa EQ PUSH2 @f JUMPI PUSH1 0x00 DUP1 REVERT :f JUMPDEST {body}"
    ))
}

#[test]
fn reentrancy_is_reported_and_cei_is_not() {
    // withdraw(): balance = sload(caller); call{value: balance}(caller); sstore(caller, 0)
    let vulnerable = dispatcher("CALLER SLOAD DUP1 PUSH1 0x00 DUP1 DUP1 DUP5 CALLER GAS CALL POP POP PUSH1 0x00 CALLER SSTORE STOP");
    let c = decompile::decompile(&vulnerable, &Options::default());
    let r = analyze::analyze(&c);
    let f = r
        .findings
        .iter()
        .find(|f| f.id == "reentrancy")
        .expect("reentrancy finding");
    assert!(
        matches!(f.severity, Severity::High | Severity::Medium),
        "{:?}",
        f.severity
    );
    // Checks-effects-interactions: sstore before the call.
    let safe = dispatcher("CALLER SLOAD PUSH1 0x00 CALLER SSTORE DUP1 PUSH1 0x00 DUP1 DUP1 DUP5 CALLER GAS CALL POP POP STOP");
    let c = decompile::decompile(&safe, &Options::default());
    let r = analyze::analyze(&c);
    assert!(
        !r.findings.iter().any(|f| f.id == "reentrancy"),
        "false reentrancy on CEI code"
    );
    assert!(
        r.findings.iter().any(|f| f.id == "unchecked-call"),
        "ignored success flag should be reported"
    );
}

#[test]
fn unprotected_selfdestruct_and_tx_origin() {
    let code = dispatcher("CALLER SELFDESTRUCT");
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    let f = r.findings.iter().find(|f| f.id == "selfdestruct").unwrap();
    assert_eq!(f.severity, Severity::Critical);
    // Guarded by owner == msg.sender (slot 0): severity drops.
    let guarded = dispatcher("PUSH1 0x00 SLOAD CALLER EQ PUSH2 @ok JUMPI PUSH1 0x00 DUP1 REVERT :ok JUMPDEST CALLER SELFDESTRUCT");
    let r = analyze::analyze(&decompile::decompile(&guarded, &Options::default()));
    let f = r.findings.iter().find(|f| f.id == "selfdestruct").unwrap();
    assert_eq!(f.severity, Severity::Medium);
    assert!(r.privileged_functions.len() == 1);
    // tx.origin authorization
    let origin = dispatcher("PUSH1 0x00 SLOAD ORIGIN EQ PUSH2 @ok JUMPI PUSH1 0x00 DUP1 REVERT :ok JUMPDEST PUSH1 0x01 PUSH1 0x05 SSTORE STOP");
    let r = analyze::analyze(&decompile::decompile(&origin, &Options::default()));
    assert!(r.findings.iter().any(|f| f.id == "tx-origin"));
}

#[test]
fn arbitrary_delegatecall_and_owner_write() {
    // delegatecall to calldata[4]
    let dc =
        dispatcher("PUSH1 0x00 DUP1 DUP1 DUP1 PUSH1 0x04 CALLDATALOAD GAS DELEGATECALL POP STOP");
    let r = analyze::analyze(&decompile::decompile(&dc, &Options::default()));
    let f = r
        .findings
        .iter()
        .find(|f| f.id == "arbitrary-delegatecall")
        .unwrap();
    assert_eq!(f.severity, Severity::Critical);
    // Two functions: 0xaaaaaaaa writes slot 0 from calldata without a check; 0xbbbbbbbb is gated by slot 0 == caller.
    let two = asm("PUSH1 0x80 PUSH1 0x40 MSTORE PUSH1 0x00 CALLDATALOAD PUSH1 0xe0 SHR DUP1 PUSH4 0xaaaaaaaa EQ PUSH2 @a JUMPI PUSH4 0xbbbbbbbb EQ PUSH2 @b JUMPI PUSH1 0x00 DUP1 REVERT :a JUMPDEST PUSH1 0x04 CALLDATALOAD PUSH1 0x00 SSTORE STOP :b JUMPDEST PUSH1 0x00 SLOAD CALLER EQ PUSH2 @ok JUMPI PUSH1 0x00 DUP1 REVERT :ok JUMPDEST PUSH1 0x01 PUSH1 0x07 SSTORE STOP");
    let r = analyze::analyze(&decompile::decompile(&two, &Options::default()));
    assert!(
        r.findings
            .iter()
            .any(|f| f.id == "unprotected-owner-write" && f.severity == Severity::Critical),
        "{:?}",
        r.findings.iter().map(|f| &f.id).collect::<Vec<_>>()
    );
}

#[test]
fn report_renders() {
    let code = dispatcher("CALLER SELFDESTRUCT");
    let c = decompile::decompile(&code, &Options::default());
    let r = analyze::analyze(&c);
    let md = evmdec::analyze::render_markdown(&c, &r, "test");
    assert!(md.contains("[CRITICAL]"));
    assert!(serde_json::to_string(&r).is_ok());
}

/// solc < 0.5.9 metadata trailer: `{"bzzr0": <32 bytes>}` followed by its 2-byte length.
fn bzzr0_trailer() -> Vec<u8> {
    let mut t = vec![0xa1, 0x65, b'b', b'z', b'z', b'r', b'0', 0x58, 0x20];
    t.extend(std::iter::repeat_n(0x11, 32));
    t.extend_from_slice(&[0x00, 0x29]);
    t
}

#[test]
fn safemath_guard_in_inlined_helper_is_kept() {
    // f(x): slot0 = add(slot0, x) where add() is an internal helper. The checked variant asserts
    // on overflow (a > a + b -> INVALID), the unchecked one does not.
    let call = "PUSH1 0x04 CALLDATALOAD PUSH1 0x00 SLOAD PUSH2 @ret SWAP2 PUSH2 @add JUMP :ret JUMPDEST PUSH1 0x00 SSTORE STOP";
    let checked = format!("{call} :add JUMPDEST DUP2 DUP2 ADD DUP3 DUP2 GT PUSH2 @bad JUMPI SWAP2 POP POP SWAP1 JUMP :bad JUMPDEST INVALID");
    let unchecked = format!("{call} :add JUMPDEST DUP2 DUP2 ADD SWAP2 POP POP SWAP1 JUMP");

    let mut code = dispatcher(&checked);
    code.extend(bzzr0_trailer());
    let c = decompile::decompile(&code, &Options::default());
    assert!(
        c.source.contains("assert("),
        "the helper's overflow check must survive inlining:\n{}",
        c.source
    );
    let r = analyze::analyze(&c);
    assert!(
        r.findings.iter().any(|f| f.id == "legacy-compiler"),
        "bzzr0-only metadata implies solc < 0.5.9"
    );
    assert!(
        !r.findings.iter().any(|f| f.id == "unchecked-arithmetic"),
        "guarded addition must not be flagged:\n{}",
        c.source
    );

    let mut code = dispatcher(&unchecked);
    code.extend(bzzr0_trailer());
    let c = decompile::decompile(&code, &Options::default());
    let r = analyze::analyze(&c);
    assert!(
        r.findings.iter().any(|f| f.id == "unchecked-arithmetic"),
        "unguarded addition must be flagged:\n{}",
        c.source
    );
}

#[test]
fn reentrancy_guard_is_recognised_only_when_it_locks() {
    // lock: require(slot1 == 1); slot1 = 0; call; slot1 = 1; slot_caller = 0
    let locked = dispatcher("PUSH1 0x01 SLOAD PUSH1 0x01 EQ PUSH2 @go JUMPI PUSH1 0x00 DUP1 REVERT :go JUMPDEST PUSH1 0x00 PUSH1 0x01 SSTORE CALLER SLOAD DUP1 PUSH1 0x00 DUP1 DUP1 DUP5 CALLER GAS CALL POP POP PUSH1 0x01 PUSH1 0x01 SSTORE PUSH1 0x00 CALLER SSTORE STOP");
    let r = analyze::analyze(&decompile::decompile(&locked, &Options::default()));
    let f = r
        .findings
        .iter()
        .find(|f| f.id == "reentrancy")
        .expect("reentrancy finding");
    assert_eq!(
        f.severity,
        Severity::Info,
        "a lock written before and after the call is a guard"
    );
    // No lock, but the function still writes two slots twice after the call: not a guard.
    let unlocked = dispatcher("CALLER SLOAD DUP1 PUSH1 0x00 DUP1 DUP1 DUP5 CALLER GAS CALL POP POP PUSH1 0x05 PUSH1 0x07 SSTORE PUSH1 0x00 CALLER SSTORE PUSH1 0x06 PUSH1 0x07 SSTORE STOP");
    let r = analyze::analyze(&decompile::decompile(&unlocked, &Options::default()));
    let f = r
        .findings
        .iter()
        .find(|f| f.id == "reentrancy")
        .expect("reentrancy finding");
    assert!(
        matches!(f.severity, Severity::High | Severity::Medium),
        "writes after the call without a tested lock are not a guard: {:?}",
        f.severity
    );
}

#[test]
fn erc20_transfer_result_ignored_is_reported() {
    // token.transfer(caller, 1) with out_len 0 and only the success flag checked.
    let body = "PUSH4 0xa9059cbb PUSH1 0xe0 SHL PUSH1 0x00 MSTORE CALLER PUSH1 0x04 MSTORE PUSH1 0x01 PUSH1 0x24 MSTORE PUSH1 0x00 PUSH1 0x00 PUSH1 0x44 PUSH1 0x00 PUSH1 0x00 PUSH1 0x04 CALLDATALOAD GAS CALL PUSH2 @ok JUMPI PUSH1 0x00 DUP1 REVERT :ok JUMPDEST STOP";
    let r = analyze::analyze(&decompile::decompile(
        &dispatcher(body),
        &Options::default(),
    ));
    assert!(
        r.findings.iter().any(|f| f.id == "erc20-return-ignored"),
        "{:?}",
        r.findings.iter().map(|f| f.id.clone()).collect::<Vec<_>>()
    );
}

/// Three selectors -> three bodies, anything else reverts.
fn dispatcher3(a: &str, b: &str, c: &str) -> Vec<u8> {
    asm(&format!(
        "PUSH1 0x80 PUSH1 0x40 MSTORE PUSH1 0x00 CALLDATALOAD PUSH1 0xe0 SHR DUP1 PUSH4 0xaaaaaaaa EQ PUSH2 @a JUMPI DUP1 PUSH4 0xbbbbbbbb EQ PUSH2 @b JUMPI PUSH4 0xcccccccc EQ PUSH2 @c JUMPI PUSH1 0x00 DUP1 REVERT :a JUMPDEST POP {a} :b JUMPDEST POP {b} :c JUMPDEST {c}"
    ))
}

const OWNER_GATE: &str =
    "PUSH1 0x00 SLOAD CALLER EQ PUSH2 @ok JUMPI PUSH1 0x00 DUP1 REVERT :ok JUMPDEST";

fn ids(r: &evmdec::analyze::Report) -> Vec<String> {
    r.findings.iter().map(|f| f.id.clone()).collect()
}

#[test]
fn selfdestruct_in_a_time_gated_helper_is_critical() {
    // f(): helper(); helper: if (block.number >= slot5) selfdestruct(msg.sender); return
    let body = "PUSH2 @ret PUSH2 @helper JUMP :ret JUMPDEST STOP :helper JUMPDEST PUSH1 0x05 SLOAD NUMBER LT PUSH2 @back JUMPI CALLER SELFDESTRUCT :back JUMPDEST JUMP";
    let c = decompile::decompile(&dispatcher(body), &Options::default());
    let r = analyze::analyze(&c);
    let f = r
        .findings
        .iter()
        .find(|f| f.id == "selfdestruct")
        .unwrap_or_else(|| {
            panic!(
                "selfdestruct must be seen through the helper: {:?}\n{}",
                ids(&r),
                c.source
            )
        });
    assert_eq!(f.severity, Severity::Critical);
    assert!(
        f.title.contains("collect its balance") && f.description.contains("time condition"),
        "{} / {}",
        f.title,
        f.description
    );
}

#[test]
fn access_control_policy_flags_the_odd_one_out() {
    // a, b: owner-only setters of slots 7 and 8; c: writes slot 7 with no check at all.
    let a = format!("{OWNER_GATE} PUSH1 0x04 CALLDATALOAD PUSH1 0x07 SSTORE STOP");
    let b = "PUSH1 0x00 SLOAD CALLER EQ PUSH2 @ok2 JUMPI PUSH1 0x00 DUP1 REVERT :ok2 JUMPDEST PUSH1 0x04 CALLDATALOAD PUSH1 0x08 SSTORE STOP";
    let c = "PUSH1 0x04 CALLDATALOAD PUSH1 0x07 SSTORE STOP";
    let r = analyze::analyze(&decompile::decompile(
        &dispatcher3(&a, b, c),
        &Options::default(),
    ));
    let f = r
        .findings
        .iter()
        .find(|f| f.id == "inconsistent-access-control")
        .unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert_eq!(f.severity, Severity::Medium);
    assert!(
        f.function
            .as_deref()
            .unwrap_or_default()
            .contains("cccccccc"),
        "{:?}",
        f.function
    );
    assert!(
        f.description.contains("2 state-changing functions"),
        "{}",
        f.description
    );
}

#[test]
fn attack_chains_are_assembled_across_functions() {
    // Rubixi: a() sets owner = msg.sender unguarded; b() is owner-only and pays the balance out.
    let a = "CALLER PUSH1 0x00 SSTORE STOP";
    let b = format!("{OWNER_GATE} PUSH1 0x00 DUP1 DUP1 DUP1 SELFBALANCE CALLER GAS CALL POP STOP");
    let r = analyze::analyze(&decompile::decompile(
        &dispatcher3(a, &b, "STOP"),
        &Options::default(),
    ));
    let f = r
        .findings
        .iter()
        .find(|f| f.id == "attack-chain")
        .unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert_eq!(f.severity, Severity::Critical);
    assert!(
        f.description.contains("Step 1") && f.description.contains("Step 2"),
        "{}",
        f.description
    );

    // Set the payout address from calldata in a(), then b() sends the balance to it.
    let a = "PUSH1 0x04 CALLDATALOAD PUSH1 0x05 SSTORE STOP";
    let b = "PUSH1 0x00 DUP1 DUP1 DUP1 SELFBALANCE PUSH1 0x05 SLOAD GAS CALL POP STOP";
    let r = analyze::analyze(&decompile::decompile(
        &dispatcher3(a, b, "STOP"),
        &Options::default(),
    ));
    let f = r
        .findings
        .iter()
        .find(|f| f.id == "attack-chain")
        .unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert!(
        f.description
            .contains("sends ether to the address stored there"),
        "{}",
        f.description
    );

    // Storing msg.sender (a depositor) and paying it later is a pull payment, not a chain.
    let a = "CALLER PUSH1 0x05 SSTORE STOP";
    let r = analyze::analyze(&decompile::decompile(
        &dispatcher3(a, b, "STOP"),
        &Options::default(),
    ));
    assert!(
        !r.findings.iter().any(|f| f.id == "attack-chain"),
        "{:?}",
        ids(&r)
    );
}

#[test]
fn wrapping_payout_arithmetic_needs_a_bound() {
    // send((1000 - arg) * balance / 1000) to slot1, compiled before 0.8.
    let payout = "PUSH1 0x00 DUP1 DUP1 DUP1 PUSH1 0x04 CALLDATALOAD PUSH2 0x03e8 SUB SELFBALANCE MUL PUSH2 0x03e8 SWAP1 DIV PUSH1 0x01 SLOAD GAS CALL POP STOP";
    let mut code = dispatcher(payout);
    code.extend(bzzr0_trailer());
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    let f = r
        .findings
        .iter()
        .find(|f| f.id == "unbounded-payout-parameter")
        .unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert_eq!(f.severity, Severity::Medium);

    // require(arg <= 1000) first: bounded.
    let bounded = format!(
        "PUSH1 0x04 CALLDATALOAD PUSH2 0x03e9 GT PUSH2 @ok JUMPI PUSH1 0x00 DUP1 REVERT :ok JUMPDEST {payout}"
    );
    let mut code = dispatcher(&bounded);
    code.extend(bzzr0_trailer());
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    assert!(
        !r.findings
            .iter()
            .any(|f| f.id == "unbounded-payout-parameter"),
        "{:?}",
        ids(&r)
    );

    // Same code with no metadata at all: the compiler era is unknown, so no claim is made.
    let r = analyze::analyze(&decompile::decompile(
        &dispatcher(payout),
        &Options::default(),
    ));
    assert!(!r
        .findings
        .iter()
        .any(|f| f.id == "unbounded-payout-parameter"));
}

fn finding<'a>(r: &'a evmdec::analyze::Report, id: &str) -> Option<&'a evmdec::analyze::Finding> {
    r.findings.iter().find(|f| f.id == id)
}

#[test]
fn unchecked_downcast_of_a_wide_parameter_is_reported_unless_range_checked() {
    // x = arg0; slot1 = x + 1 (x is a number); slot0 = uint32(x) with no check.
    let truncating = dispatcher(
        "PUSH1 0x04 CALLDATALOAD DUP1 PUSH1 0x01 ADD PUSH1 0x01 SSTORE PUSH4 0xffffffff AND PUSH1 0x00 SSTORE STOP",
    );
    let r = analyze::analyze(&decompile::decompile(&truncating, &Options::default()));
    let f = finding(&r, "unchecked-downcast").unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert_eq!(f.severity, Severity::Medium, "{f:?}");
    assert!(f.description.contains("32 bits"), "{}", f.description);

    // require(x < 2**32) first: a checked cast.
    let checked = dispatcher(
        "PUSH1 0x04 CALLDATALOAD DUP1 PUSH5 0x0100000000 GT PUSH2 @ok JUMPI PUSH1 0x00 DUP1 REVERT :ok JUMPDEST DUP1 PUSH1 0x01 ADD PUSH1 0x01 SSTORE PUSH4 0xffffffff AND PUSH1 0x00 SSTORE STOP",
    );
    let r = analyze::analyze(&decompile::decompile(&checked, &Options::default()));
    assert!(finding(&r, "unchecked-downcast").is_none(), "{:?}", ids(&r));
}

#[test]
fn a_value_compared_signed_and_unsigned_is_reported() {
    // require(b <s a); require(b <u a); store both.
    let code = dispatcher(
        "PUSH1 0x04 CALLDATALOAD PUSH1 0x24 CALLDATALOAD DUP2 DUP2 SLT PUSH2 @s JUMPI PUSH1 0x00 DUP1 REVERT :s JUMPDEST DUP2 DUP2 LT PUSH2 @u JUMPI PUSH1 0x00 DUP1 REVERT :u JUMPDEST PUSH1 0x00 SSTORE PUSH1 0x01 SSTORE STOP",
    );
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    let f = finding(&r, "signed-unsigned-confusion").unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert!(f.description.contains("arg"), "{}", f.description);
}

#[test]
fn narrow_storage_counter_is_reported() {
    // slot0 = uint32(slot0 + 1)
    let code =
        dispatcher("PUSH1 0x00 SLOAD PUSH1 0x01 ADD PUSH4 0xffffffff AND PUSH1 0x00 SSTORE STOP");
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    let f = finding(&r, "narrow-counter").unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert!(f.description.contains("uint32"), "{}", f.description);
    assert!(f.description.contains("wraps"), "{}", f.description);
}

#[test]
fn an_account_computed_with_arithmetic_is_reported() {
    // call(slot0); slot0 = arg0 + 1 (the load comes first so it is not forwarded from the store)
    let code = dispatcher(
        "PUSH1 0x00 DUP1 DUP1 DUP1 DUP1 PUSH1 0x00 SLOAD GAS CALL POP PUSH1 0x04 CALLDATALOAD PUSH1 0x01 ADD PUSH1 0x00 SSTORE STOP",
    );
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    let f = finding(&r, "address-from-arithmetic").unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert!(
        f.evidence.iter().any(|e| e.contains("+ 1")),
        "{:?}",
        f.evidence
    );
}

#[test]
fn a_hash_used_in_arithmetic_is_reported() {
    // slot1 = slot0 + 1; slot0 = keccak256(arg0)
    let code = dispatcher(
        "PUSH1 0x00 SLOAD PUSH1 0x01 ADD PUSH1 0x01 SSTORE PUSH1 0x04 CALLDATALOAD PUSH1 0x00 MSTORE PUSH1 0x20 PUSH1 0x00 KECCAK256 PUSH1 0x00 SSTORE STOP",
    );
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    assert!(finding(&r, "hash-as-number").is_some(), "{:?}", ids(&r));
}

#[test]
fn an_unguarded_selfdestruct_is_confirmed_but_a_guarded_one_is_not() {
    // kill(): selfdestruct(msg.sender) with no access check.
    let open = dispatcher("CALLER SELFDESTRUCT");
    let r = analyze::analyze(&decompile::decompile(&open, &Options::default()));
    let f = finding(&r, "selfdestruct").unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert!(
        f.confirmed,
        "an open selfdestruct should be confirmed: {f:?}"
    );
    assert!(f.witness.as_ref().is_some_and(|w| w.starts_with("0x")));

    // require(msg.sender == slot0) first. In a fresh state slot0 == 0 and the attacker is
    // non-zero, so the sink is unreachable and nothing is confirmed.
    let guarded = dispatcher(
        "PUSH1 0x00 SLOAD CALLER EQ PUSH2 @ok JUMPI PUSH1 0x00 DUP1 REVERT :ok JUMPDEST CALLER SELFDESTRUCT",
    );
    let r = analyze::analyze(&decompile::decompile(&guarded, &Options::default()));
    assert!(
        !r.findings.iter().any(|f| f.confirmed),
        "a guarded selfdestruct must not be confirmed: {:?}",
        r.findings
            .iter()
            .filter(|f| f.confirmed)
            .map(|f| &f.id)
            .collect::<Vec<_>>()
    );
}

#[test]
fn a_free_self_credit_is_reported_and_a_paid_one_is_not() {
    // balances[msg.sender] on the stack as `key`, then `key = key + 1` / `key = key - 1`.
    const ENTRY: &str =
        "CALLER PUSH1 0x00 MSTORE PUSH1 0x00 PUSH1 0x20 MSTORE PUSH1 0x40 PUSH1 0x00 KECCAK256";
    let credit = format!("{ENTRY} DUP1 SLOAD PUSH1 0x01 ADD SWAP1 SSTORE STOP");
    // burn(amount): require(balance >= amount) then subtract. The comparison against a value
    // (not a constant) is what pins the ledger as unsigned.
    let debit = format!(
        "{ENTRY} PUSH1 0x04 CALLDATALOAD DUP2 SLOAD DUP2 GT ISZERO PUSH2 @okb JUMPI PUSH1 0x00 DUP1 REVERT :okb JUMPDEST DUP2 SLOAD SUB SWAP1 SSTORE STOP"
    );
    let hits = |code: &[u8]| -> Vec<String> {
        let r = analyze::analyze(&decompile::decompile(code, &Options::default()));
        r.findings
            .iter()
            .filter(|f| f.id == "unprivileged-balance-credit")
            .map(|f| f.function.as_deref().unwrap_or_default().to_owned())
            .collect()
    };

    // mint(): a free credit with no payment and no access check, next to burn().
    let free = dispatcher3(&credit, &debit, "STOP");
    let r = analyze::analyze(&decompile::decompile(&free, &Options::default()));
    let f = finding(&r, "unprivileged-balance-credit").unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert_eq!(f.severity, Severity::High);
    assert!(
        f.function
            .as_deref()
            .is_some_and(|n| n.contains("aaaaaaaa")),
        "{f:?}"
    );
    assert!(f
        .evidence
        .iter()
        .any(|e| e.starts_with("witness calldata: 0xaaaaaaaa")));
    assert_eq!(
        hits(&free).len(),
        1,
        "burn() is checked and must not be reported"
    );

    // deposit(): the same credit behind require(msg.value > 0). A zero-value call reverts, so
    // the caller cannot end with a balance it did not pay for.
    let paid = dispatcher3(
        &format!("CALLVALUE PUSH2 @ok JUMPI PUSH1 0x00 DUP1 REVERT :ok JUMPDEST {credit}"),
        &debit,
        "STOP",
    );
    assert!(
        hits(&paid).is_empty(),
        "a paid credit must not be reported: {:?}",
        hits(&paid)
    );

    // An unchecked burn wraps 0 - 1 to 2^256 - 1 while the checked burn next to it shows the
    // ledger is unsigned: the unchecked debit path itself mints the balance.
    let unchecked = format!("{ENTRY} DUP1 SLOAD PUSH1 0x01 SWAP1 SUB SWAP1 SSTORE STOP");
    let wrapping = dispatcher3(
        &format!("CALLVALUE PUSH2 @ok JUMPI PUSH1 0x00 DUP1 REVERT :ok JUMPDEST {credit}"),
        &unchecked,
        &debit,
    );
    assert_eq!(
        hits(&wrapping),
        vec!["func_bbbbbbbb [0xbbbbbbbb]".to_string()]
    );

    // The same wrap on a mapping nothing ever compares unsigned may be signed accounting that
    // legitimately goes negative, so it is not reported.
    let signed_like = dispatcher3(
        &format!("CALLVALUE PUSH2 @ok JUMPI PUSH1 0x00 DUP1 REVERT :ok JUMPDEST {credit}"),
        &unchecked,
        "STOP",
    );
    assert!(hits(&signed_like).is_empty(), "{:?}", hits(&signed_like));

    // nonces[msg.sender] += 1 with no debit anywhere: a counter, not a ledger.
    let counter = dispatcher3(&credit, "STOP", "STOP");
    assert!(
        hits(&counter).is_empty(),
        "a counter must not be reported: {:?}",
        hits(&counter)
    );
}
