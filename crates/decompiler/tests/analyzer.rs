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
    let md = analyze::render_markdown(&c, &r, "test");
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

fn ids(r: &analyze::Report) -> Vec<String> {
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

fn finding<'a>(r: &'a analyze::Report, id: &str) -> Option<&'a analyze::Finding> {
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

#[test]
fn a_composite_merges_facets_and_keeps_their_functions_apart() {
    use evmdec::decompile::{compose, PartInput, PartRole};
    // Shell: a router is not needed for composition; a contract with no functions will do
    // (a shell that answered a routed selector itself would shadow the facet's function).
    let shell_code = asm("PUSH1 0x00 DUP1 REVERT");
    // Facet A at selector 0xaaaaaaaa: an open selfdestruct (confirmable sink).
    let a_code = dispatcher("CALLER SELFDESTRUCT");
    // Facet B at selector 0xbbbbbbbb: writes slot 0 with the caller (an address).
    let b_code = dispatcher3("STOP", "CALLER PUSH1 0x00 SSTORE STOP", "STOP");
    let mut shell = decompile::decompile(&shell_code, &Options::default());
    shell.address = Some("0x00000000000000000000000000000000000000d1".into());
    let a = decompile::decompile(&a_code, &Options::default());
    let b = decompile::decompile(&b_code, &Options::default());
    let a_pc = a
        .functions
        .iter()
        .find(|f| f.selector.is_some())
        .map(|f| f.pc)
        .unwrap();
    let c = compose(
        shell,
        "EIP-2535 diamond (2 facets)",
        None,
        vec![
            PartInput {
                role: PartRole::Facet,
                address: "0x000000000000000000000000000000000000000a".into(),
                selectors: vec!["0xaaaaaaaa".into()],
                contract: a,
            },
            PartInput {
                role: PartRole::Facet,
                address: "0x000000000000000000000000000000000000000b".into(),
                selectors: vec!["0xbbbbbbbb".into()],
                contract: b,
            },
        ],
    );
    assert_eq!(c.parts.len(), 3);
    // Only routed externals come across: facet B's 0xaaaaaaaa and 0xcccccccc are dropped.
    let externals: Vec<(&str, usize)> = c
        .functions
        .iter()
        .filter(|f| f.selector.is_some())
        .map(|f| (f.selector.as_deref().unwrap(), f.part))
        .collect();
    assert_eq!(
        externals,
        vec![("0xaaaaaaaa", 1), ("0xbbbbbbbb", 2)],
        "{externals:?}"
    );
    // pcs are unique across parts and translate back to the part's own code.
    let fa = c
        .functions
        .iter()
        .find(|f| f.part == 1 && f.selector.is_some())
        .unwrap();
    assert_eq!(fa.pc, a_pc + decompile::PART_STRIDE);
    assert_eq!(c.local_pc(fa, fa.pc), a_pc);
    assert_eq!(c.code_of(fa), &a_code[..]);
    assert!(
        c.source
            .contains("// ==== 0x000000000000000000000000000000000000000a — facet: 1 selectors"),
        "{}",
        c.source
    );

    let r = analyze::analyze(&c);
    assert!(finding(&r, "composite").is_some(), "{:?}", ids(&r));
    // The facet's sink is confirmed by running the facet's code, and the finding names the facet.
    let sd = finding(&r, "selfdestruct").unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert!(sd.confirmed, "{sd:?}");
    assert!(sd
        .function
        .as_deref()
        .unwrap()
        .ends_with("@ 0x000000000000000000000000000000000000000a"));
    let md = analyze::render_markdown(&c, &r, "diamond");
    assert!(md.contains("## Parts"), "{md}");
    assert!(md.contains(&format!(
        "at pc {:#x}",
        sd.pc.map(|p| c.local_pc(fa, p)).unwrap()
    )));
}

#[test]
fn a_proxy_composite_takes_every_implementation_function_and_flags_slot_collisions() {
    use evmdec::decompile::{compose, PartInput, PartRole};
    // Shell: writes slot 0 as an address (an owner). Implementation: slot 0 is a balance
    // mapping (its entry key hashes slot 0), and slot 1 is read narrow where the shell reads
    // it wide, which is not a collision.
    let shell_code = dispatcher("CALLER PUSH1 0x00 SSTORE PUSH1 0x01 SLOAD POP STOP");
    let impl_code = dispatcher3(
        "STOP",
        "CALLER PUSH1 0x00 MSTORE PUSH1 0x00 PUSH1 0x20 MSTORE PUSH1 0x40 PUSH1 0x00 KECCAK256 DUP1 SLOAD PUSH1 0x01 ADD SWAP1 SSTORE STOP",
        "PUSH1 0x01 SLOAD PUSH1 0xff AND PUSH1 0x00 MSTORE PUSH1 0x20 PUSH1 0x00 RETURN",
    );
    let mut shell = decompile::decompile(&shell_code, &Options::default());
    shell.address = Some("0x00000000000000000000000000000000000000d1".into());
    let im = decompile::decompile(&impl_code, &Options::default());
    let c = compose(
        shell,
        "EIP-1967 proxy",
        Some("0x00000000000000000000000000000000000000ad".into()),
        vec![PartInput {
            role: PartRole::Implementation,
            address: "0x0000000000000000000000000000000000000001".into(),
            selectors: Vec::new(),
            contract: im,
        }],
    );
    // Every implementation external comes across except the one the shell answers itself.
    let sels: Vec<(&str, usize)> = c
        .functions
        .iter()
        .filter(|f| f.selector.is_some())
        .map(|f| (f.selector.as_deref().unwrap(), f.part))
        .collect();
    assert_eq!(
        sels,
        vec![("0xaaaaaaaa", 0), ("0xbbbbbbbb", 1), ("0xcccccccc", 1)],
        "{sels:?}"
    );
    let comp = c.composite.as_ref().unwrap();
    assert_eq!(comp.shadowed, vec!["0xaaaaaaaa".to_string()]);
    assert_eq!(comp.collisions.len(), 1, "{:?}", comp.collisions);
    assert_eq!(comp.collisions[0].slot, "0x0");
    let r = analyze::analyze(&c);
    assert!(finding(&r, "storage-collision").is_some(), "{:?}", ids(&r));
}

/// `CALL(gas, SLOAD(slot), 0, mem[0..len], out 0)` with the 4-byte `selector` at memory 0 and
/// `extra` assembled before the call (for payload words after the selector).
fn call_stored(slot: u8, selector: u32, extra: &str, len: u8) -> String {
    format!(
        "PUSH4 {selector:#010x} PUSH1 0xe0 SHL PUSH1 0x00 MSTORE {extra} PUSH1 0x00 PUSH1 0x00 PUSH1 {len:#04x} PUSH1 0x00 PUSH1 0x00 PUSH1 {slot:#04x} SLOAD GAS CALL POP STOP"
    )
}

#[test]
fn a_debit_of_the_stored_pair_is_critical_and_own_or_allowed_debits_are_not() {
    // balanceOf[SLOAD(9)] -= calldata[4] in a function anyone can call; another function
    // calls sync() on SLOAD(9), which marks slot 9 as the pair.
    let debit_pair = "PUSH1 0x09 SLOAD PUSH1 0x00 MSTORE PUSH1 0x03 PUSH1 0x20 MSTORE PUSH1 0x40 PUSH1 0x00 KECCAK256 DUP1 SLOAD PUSH1 0x04 CALLDATALOAD SWAP1 SUB SWAP1 SSTORE STOP";
    let sync_pair = call_stored(9, 0xfff6cae9, "", 4);
    let code = dispatcher3(debit_pair, &sync_pair, "STOP");
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    let f = finding(&r, "third-party-balance-debit").unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert_eq!(f.severity, Severity::Critical, "{f:?}");
    assert!(
        f.description.contains("liquidity pair"),
        "{}",
        f.description
    );

    // The same debit, but the pool is known only from the token singling the address out in a
    // transfer guard (`to == SLOAD(9)` in the fee path), no pool selector anywhere: the shape a
    // token trading on V3, V4 or any other venue has.
    const MASK: &str = "PUSH20 0xffffffffffffffffffffffffffffffffffffffff AND";
    let fee_guard = format!(
        "PUSH1 0x04 CALLDATALOAD {MASK} PUSH1 0x09 SLOAD {MASK} EQ ISZERO PUSH2 @nofee JUMPI PUSH1 0x01 PUSH1 0x02 SSTORE :nofee JUMPDEST STOP"
    );
    let debit_masked = format!(
        "PUSH1 0x09 SLOAD {MASK} PUSH1 0x00 MSTORE PUSH1 0x03 PUSH1 0x20 MSTORE PUSH1 0x40 PUSH1 0x00 KECCAK256 DUP1 SLOAD PUSH1 0x04 CALLDATALOAD SWAP1 SUB SWAP1 SSTORE STOP"
    );
    let code = dispatcher3(&debit_masked, &fee_guard, "STOP");
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    let f = finding(&r, "third-party-balance-debit").unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert_eq!(f.severity, Severity::Critical, "{f:?}");
    assert_eq!(f.confidence, analyze::Confidence::Medium, "{f:?}");

    // balanceOf[msg.sender] -= amount: the caller's own balance.
    let debit_self = "CALLER PUSH1 0x00 MSTORE PUSH1 0x03 PUSH1 0x20 MSTORE PUSH1 0x40 PUSH1 0x00 KECCAK256 DUP1 SLOAD PUSH1 0x04 CALLDATALOAD SWAP1 SUB SWAP1 SSTORE STOP";
    let code = dispatcher3(debit_self, "STOP", "STOP");
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    assert!(
        finding(&r, "third-party-balance-debit").is_none(),
        "{:?}",
        ids(&r)
    );

    // balanceOf[from] -= amount after reading allowance[from][msg.sender]: a transferFrom.
    let debit_allowed = "PUSH1 0x04 CALLDATALOAD PUSH1 0x00 MSTORE PUSH1 0x04 PUSH1 0x20 MSTORE PUSH1 0x40 PUSH1 0x00 KECCAK256 PUSH1 0x20 MSTORE CALLER PUSH1 0x00 MSTORE PUSH1 0x40 PUSH1 0x00 KECCAK256 SLOAD PUSH1 0x24 CALLDATALOAD GT ISZERO PUSH2 @ok JUMPI PUSH1 0x00 DUP1 REVERT :ok JUMPDEST PUSH1 0x04 CALLDATALOAD PUSH1 0x00 MSTORE PUSH1 0x03 PUSH1 0x20 MSTORE PUSH1 0x40 PUSH1 0x00 KECCAK256 DUP1 SLOAD PUSH1 0x24 CALLDATALOAD SWAP1 SUB SWAP1 SSTORE STOP";
    let code = dispatcher3(debit_allowed, "STOP", "STOP");
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    assert!(
        finding(&r, "third-party-balance-debit").is_none(),
        "{:?}",
        ids(&r)
    );
}

#[test]
fn a_gate_on_an_address_the_contract_calls_publicly_is_a_trust_loop() {
    // x: require(msg.sender == SLOAD(11)); slot1 = 1.  y: calls SLOAD(11) with msg.sender.
    let gated = "PUSH1 0x0b SLOAD CALLER EQ PUSH2 @ok JUMPI PUSH1 0x00 DUP1 REVERT :ok JUMPDEST PUSH1 0x01 PUSH1 0x01 SSTORE STOP";
    let hook = call_stored(11, 0x11111111, "CALLER PUSH1 0x04 MSTORE", 0x24);
    let code = dispatcher3(gated, &hook, "STOP");
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    let f = finding(&r, "trusted-callee-loop").unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert_eq!(f.severity, Severity::Medium);
    assert!(f.function.as_deref().unwrap().contains("aaaaaaaa"), "{f:?}");
    assert!(
        f.description.contains("passing the sender"),
        "{}",
        f.description
    );

    // The same gate without any public call to that address is an ordinary privileged function.
    let code = dispatcher3(gated, "STOP", "STOP");
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    assert!(
        finding(&r, "trusted-callee-loop").is_none(),
        "{:?}",
        ids(&r)
    );
}

#[test]
fn a_sync_after_a_state_changing_call_is_reported() {
    // transfer(...) on SLOAD(10), then sync() on SLOAD(9).
    let first = call_stored(10, 0xa9059cbb, "", 4)
        .trim_end_matches(" STOP")
        .to_string();
    let then_sync = call_stored(9, 0xfff6cae9, "", 4);
    let code = dispatcher3(&format!("{first} {then_sync}"), "STOP", "STOP");
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    let f = finding(&r, "pair-sync-after-state-change").unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert_eq!(f.severity, Severity::High);

    // sync() alone, nothing moved before it: not reported.
    let code = dispatcher3(&then_sync, "STOP", "STOP");
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    assert!(
        finding(&r, "pair-sync-after-state-change").is_none(),
        "{:?}",
        ids(&r)
    );
}

/// `mapping[slot][calldata[4]]` read, ending in SLOAD. Key is a calldata word so the entry is
/// pooled (a `ShapeStep::Key`), the shape the rule looks for.
fn mread(slot: u8) -> String {
    format!(
        "PUSH1 0x04 CALLDATALOAD PUSH1 0x00 MSTORE PUSH1 0x{slot:02x} PUSH1 0x20 MSTORE PUSH1 0x40 PUSH1 0x00 KECCAK256 SLOAD"
    )
}

/// A payout limited by `avail >= calldata[0x24]`, then `calldata[0x24]` wei sent to the caller.
fn bounded_payout(avail: &str, bad: &str) -> String {
    limited_payout(avail, "0x24", bad)
}

/// `avail >= calldata[cmp]`, then `calldata[0x24]` wei sent to the caller: the limit caps the
/// payout only when `cmp` is `0x24`.
fn limited_payout(avail: &str, cmp: &str, bad: &str) -> String {
    format!(
        "{avail} PUSH1 {cmp} CALLDATALOAD GT PUSH2 @{bad} JUMPI \
         PUSH1 0x00 PUSH1 0x00 PUSH1 0x00 PUSH1 0x00 PUSH1 0x24 CALLDATALOAD CALLER GAS CALL POP STOP \
         :{bad} JUMPDEST PUSH1 0x00 DUP1 REVERT"
    )
}

/// The low 128 bits of `x`.
fn low128(x: &str) -> String {
    format!("{x} PUSH16 0xffffffffffffffffffffffffffffffff AND")
}

/// The high 128 bits of `x`.
fn high128(x: &str) -> String {
    format!("{x} PUSH1 0x80 SHR")
}

#[test]
fn payout_omitting_a_liability_another_path_subtracts_is_flagged() {
    // deposits = slot 0, borrowed = slot 1, matured = slot 2, all keyed by calldata[4].
    // draw() (0xaaaaaaaa): avail = deposits - borrowed            (omits matured)
    // exit() (0xbbbbbbbb): avail = deposits - (borrowed + matured)
    let draw = bounded_payout(&format!("{} {} SUB", mread(1), mread(0)), "bad_a");
    let exit = bounded_payout(
        &format!("{} {} ADD {} SUB", mread(2), mread(1), mread(0)),
        "bad_b",
    );
    let code = dispatcher3(&draw, &exit, "STOP");
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    let f =
        finding(&r, "inconsistent-liability-accounting").unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert_eq!(f.severity, Severity::High, "{f:?}");
    // The deficient path is the one subtracting fewer liabilities (draw), not exit.
    assert_eq!(
        f.function.as_deref(),
        Some("func_aaaaaaaa [0xaaaaaaaa]"),
        "{f:?}"
    );

    // Both paths subtract the same set: no inconsistency.
    let draw2 = bounded_payout(
        &format!("{} {} ADD {} SUB", mread(2), mread(1), mread(0)),
        "bad_c",
    );
    let code = dispatcher3(&draw2, &exit, "STOP");
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    assert!(
        finding(&r, "inconsistent-liability-accounting").is_none(),
        "{:?}",
        ids(&r)
    );

    // A single payout path has nothing to disagree with.
    let code = dispatcher3(&draw, "STOP", "STOP");
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    assert!(
        finding(&r, "inconsistent-liability-accounting").is_none(),
        "{:?}",
        ids(&r)
    );
}

#[test]
fn packed_halves_are_separate_liabilities() {
    // One slot holds two liabilities in its halves. draw() subtracts the low half only;
    // exit() subtracts both. Reading the slot as one field would make the two limits equal.
    let m1 = mread(1);
    let draw = bounded_payout(&format!("{} {} SUB", low128(&m1), mread(0)), "bad_a");
    let exit = bounded_payout(
        &format!("{} {} ADD {} SUB", high128(&m1), low128(&m1), mread(0)),
        "bad_b",
    );
    let code = dispatcher3(&draw, &exit, "STOP");
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    let f =
        finding(&r, "inconsistent-liability-accounting").unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert_eq!(
        f.function.as_deref(),
        Some("func_aaaaaaaa [0xaaaaaaaa]"),
        "{f:?}"
    );
}

#[test]
fn a_limit_that_does_not_cap_the_payout_is_not_compared() {
    // draw() compares its smaller limit with calldata[0x44] but pays calldata[0x24]: the
    // limit does not bound what leaves, so there is nothing to hold against exit().
    let draw = limited_payout(&format!("{} {} SUB", mread(1), mread(0)), "0x44", "bad_a");
    let exit = bounded_payout(
        &format!("{} {} ADD {} SUB", mread(2), mread(1), mread(0)),
        "bad_b",
    );
    let code = dispatcher3(&draw, &exit, "STOP");
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    assert!(
        finding(&r, "inconsistent-liability-accounting").is_none(),
        "{:?}",
        ids(&r)
    );
}

/// The high 128 bits of `x`, read in place with a high mask and no shift.
fn high128_in_place(x: &str) -> String {
    format!("{x} PUSH32 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000 AND")
}

#[test]
fn a_field_read_with_a_high_mask_is_a_liability() {
    // exit() subtracts the slot's high half through a mask, not a shift. Unrecognised, that
    // read would drop out and the two limits would look the same.
    let m1 = mread(1);
    let draw = bounded_payout(&format!("{} {} SUB", low128(&m1), mread(0)), "bad_a");
    let exit = bounded_payout(
        &format!(
            "{} {} ADD {} SUB",
            high128_in_place(&m1),
            low128(&m1),
            mread(0)
        ),
        "bad_b",
    );
    let code = dispatcher3(&draw, &exit, "STOP");
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    let f =
        finding(&r, "inconsistent-liability-accounting").unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert_eq!(
        f.function.as_deref(),
        Some("func_aaaaaaaa [0xaaaaaaaa]"),
        "{f:?}"
    );
}

#[test]
fn a_liability_added_back_once_and_subtracted_twice_still_counts() {
    // exit(): deposits - borrowed - matured - matured + matured. Net, matured is subtracted
    // once; cancelling by set membership would lose it and make the limits look equal.
    let draw = bounded_payout(&format!("{} {} SUB", mread(1), mread(0)), "bad_a");
    let exit = bounded_payout(
        &format!(
            "{m2} {m2} ADD {m1} ADD {m0} SUB {m2} ADD",
            m0 = mread(0),
            m1 = mread(1),
            m2 = mread(2)
        ),
        "bad_b",
    );
    let code = dispatcher3(&draw, &exit, "STOP");
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    let f =
        finding(&r, "inconsistent-liability-accounting").unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert_eq!(
        f.function.as_deref(),
        Some("func_aaaaaaaa [0xaaaaaaaa]"),
        "{f:?}"
    );
}

#[test]
fn a_view_reporting_the_full_limit_is_a_reference() {
    // available() (0xbbbbbbbb) only returns deposits - (borrowed + matured); it moves nothing.
    // draw() pays against deposits - borrowed.
    let draw = bounded_payout(&format!("{} {} SUB", mread(1), mread(0)), "bad_a");
    let view = format!(
        "{} {} ADD {} SUB PUSH1 0x00 MSTORE PUSH1 0x20 PUSH1 0x00 RETURN",
        mread(2),
        mread(1),
        mread(0)
    );
    let code = dispatcher3(&draw, &view, "STOP");
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    let f =
        finding(&r, "inconsistent-liability-accounting").unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert_eq!(
        f.function.as_deref(),
        Some("func_aaaaaaaa [0xaaaaaaaa]"),
        "{f:?}"
    );
}
