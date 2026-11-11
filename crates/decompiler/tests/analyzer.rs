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
    let guarded = dispatcher("PUSH1 0x00 SLOAD CALLER EQ PUSH2 @ok JUMPI PUSH1 0x00 DUP1 REVERT :ok JUMPDEST CALLER SELFDESTRUCT");
    let r = analyze::analyze(&decompile::decompile(&guarded, &Options::default()));
    let f = r.findings.iter().find(|f| f.id == "selfdestruct").unwrap();
    assert_eq!(f.severity, Severity::Medium);
    assert!(r.privileged_functions.len() == 1);
    let origin = dispatcher("PUSH1 0x00 SLOAD ORIGIN EQ PUSH2 @ok JUMPI PUSH1 0x00 DUP1 REVERT :ok JUMPDEST PUSH1 0x01 PUSH1 0x05 SSTORE STOP");
    let r = analyze::analyze(&decompile::decompile(&origin, &Options::default()));
    assert!(r.findings.iter().any(|f| f.id == "tx-origin"));
}

#[test]
fn arbitrary_delegatecall_and_owner_write() {
    let dc =
        dispatcher("PUSH1 0x00 DUP1 DUP1 DUP1 PUSH1 0x04 CALLDATALOAD GAS DELEGATECALL POP STOP");
    let r = analyze::analyze(&decompile::decompile(&dc, &Options::default()));
    let f = r
        .findings
        .iter()
        .find(|f| f.id == "arbitrary-delegatecall")
        .unwrap();
    assert_eq!(f.severity, Severity::Critical);
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
    let truncating = dispatcher(
        "PUSH1 0x04 CALLDATALOAD DUP1 PUSH1 0x01 ADD PUSH1 0x01 SSTORE PUSH4 0xffffffff AND PUSH1 0x00 SSTORE STOP",
    );
    let r = analyze::analyze(&decompile::decompile(&truncating, &Options::default()));
    let f = finding(&r, "unchecked-downcast").unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert_eq!(f.severity, Severity::Medium, "{f:?}");
    assert!(f.description.contains("32 bits"), "{}", f.description);

    let checked = dispatcher(
        "PUSH1 0x04 CALLDATALOAD DUP1 PUSH5 0x0100000000 GT PUSH2 @ok JUMPI PUSH1 0x00 DUP1 REVERT :ok JUMPDEST DUP1 PUSH1 0x01 ADD PUSH1 0x01 SSTORE PUSH4 0xffffffff AND PUSH1 0x00 SSTORE STOP",
    );
    let r = analyze::analyze(&decompile::decompile(&checked, &Options::default()));
    assert!(finding(&r, "unchecked-downcast").is_none(), "{:?}", ids(&r));
}

#[test]
fn a_value_compared_signed_and_unsigned_is_reported() {
    let code = dispatcher(
        "PUSH1 0x04 CALLDATALOAD PUSH1 0x24 CALLDATALOAD DUP2 DUP2 SLT PUSH2 @s JUMPI PUSH1 0x00 DUP1 REVERT :s JUMPDEST DUP2 DUP2 LT PUSH2 @u JUMPI PUSH1 0x00 DUP1 REVERT :u JUMPDEST PUSH1 0x00 SSTORE PUSH1 0x01 SSTORE STOP",
    );
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    let f = finding(&r, "signed-unsigned-confusion").unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert!(
        f.description.contains("Parameter `arg0`"),
        "the finding names the parameter as the code prints it: {}",
        f.description
    );
}

#[test]
fn narrow_storage_counter_is_reported() {
    let code =
        dispatcher("PUSH1 0x00 SLOAD PUSH1 0x01 ADD PUSH4 0xffffffff AND PUSH1 0x00 SSTORE STOP");
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    let f = finding(&r, "narrow-counter").unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert!(f.description.contains("uint32"), "{}", f.description);
    assert!(f.description.contains("wraps"), "{}", f.description);
}

#[test]
fn an_account_computed_with_arithmetic_is_reported() {
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
    let code = dispatcher(
        "PUSH1 0x00 SLOAD PUSH1 0x01 ADD PUSH1 0x01 SSTORE PUSH1 0x04 CALLDATALOAD PUSH1 0x00 MSTORE PUSH1 0x20 PUSH1 0x00 KECCAK256 PUSH1 0x00 SSTORE STOP",
    );
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    assert!(finding(&r, "hash-as-number").is_some(), "{:?}", ids(&r));
}

#[test]
fn an_unguarded_selfdestruct_is_confirmed_but_a_guarded_one_is_not() {
    let open = dispatcher("CALLER SELFDESTRUCT");
    let r = analyze::analyze(&decompile::decompile(&open, &Options::default()));
    let f = finding(&r, "selfdestruct").unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert!(
        f.confirmed,
        "an open selfdestruct should be confirmed: {f:?}"
    );
    assert!(f.witness.as_ref().is_some_and(|w| w.starts_with("0x")));

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
    const ENTRY: &str =
        "CALLER PUSH1 0x00 MSTORE PUSH1 0x00 PUSH1 0x20 MSTORE PUSH1 0x40 PUSH1 0x00 KECCAK256";
    let credit = format!("{ENTRY} DUP1 SLOAD PUSH1 0x01 ADD SWAP1 SSTORE STOP");
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

    let signed_like = dispatcher3(
        &format!("CALLVALUE PUSH2 @ok JUMPI PUSH1 0x00 DUP1 REVERT :ok JUMPDEST {credit}"),
        &unchecked,
        "STOP",
    );
    assert!(hits(&signed_like).is_empty(), "{:?}", hits(&signed_like));

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
    let shell_code = asm("PUSH1 0x00 DUP1 REVERT");
    let a_code = dispatcher("CALLER SELFDESTRUCT");
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

    let debit_self = "CALLER PUSH1 0x00 MSTORE PUSH1 0x03 PUSH1 0x20 MSTORE PUSH1 0x40 PUSH1 0x00 KECCAK256 DUP1 SLOAD PUSH1 0x04 CALLDATALOAD SWAP1 SUB SWAP1 SSTORE STOP";
    let code = dispatcher3(debit_self, "STOP", "STOP");
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    assert!(
        finding(&r, "third-party-balance-debit").is_none(),
        "{:?}",
        ids(&r)
    );

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
    let first = call_stored(10, 0xa9059cbb, "", 4)
        .trim_end_matches(" STOP")
        .to_string();
    let then_sync = call_stored(9, 0xfff6cae9, "", 4);
    let code = dispatcher3(&format!("{first} {then_sync}"), "STOP", "STOP");
    let r = analyze::analyze(&decompile::decompile(&code, &Options::default()));
    let f = finding(&r, "pair-sync-after-state-change").unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert_eq!(f.severity, Severity::High);

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
    assert_eq!(
        f.function.as_deref(),
        Some("func_aaaaaaaa [0xaaaaaaaa]"),
        "{f:?}"
    );

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

fn source_of(code: &[u8]) -> String {
    decompile::decompile(code, &Options::default()).source
}

#[test]
fn names_come_from_roles_the_code_shows() {
    const OWNER_ONLY: &str =
        "PUSH1 0x07 SLOAD CALLER EQ PUSH2 @ok JUMPI PUSH1 0x00 DUP1 REVERT :ok JUMPDEST";
    // Two functions compare the caller with slot 7; a third moves an amount between two
    // entries of the mapping at slot 3.
    let gated_a = OWNER_ONLY.replace("@ok", "@oka").replace(":ok", ":oka");
    let gated_b = OWNER_ONLY.replace("@ok", "@okb").replace(":ok", ":okb");
    let entry = |word: &str| {
        format!("PUSH1 {word} CALLDATALOAD PUSH20 0xffffffffffffffffffffffffffffffffffffffff AND PUSH1 0x00 MSTORE PUSH1 0x03 PUSH1 0x20 MSTORE PUSH1 0x40 PUSH1 0x00 KECCAK256")
    };
    let moved = format!(
        "{from} DUP1 SLOAD PUSH1 0x44 CALLDATALOAD SWAP1 SUB SWAP1 SSTORE \
         {to} DUP1 SLOAD PUSH1 0x44 CALLDATALOAD ADD SWAP1 SSTORE STOP",
        from = entry("0x04"),
        to = entry("0x24"),
    );
    let code = dispatcher3(
        &format!("{gated_a} PUSH1 0x01 PUSH1 0x09 SSTORE STOP"),
        &format!("{gated_b} PUSH1 0x02 PUSH1 0x0a SSTORE STOP"),
        &moved,
    );
    let src = source_of(&code);
    assert!(
        src.contains(" owner; // slot 0x7"),
        "caller guard names the slot: {src}"
    );
    assert!(
        src.contains(" balances; // slot 0x3"),
        "two-sided mapping is a ledger: {src}"
    );
    let header = src
        .lines()
        .find(|l| l.contains("function func_cccccccc("))
        .unwrap_or_else(|| panic!("{src}"));
    assert_eq!(
        header.trim(),
        "function func_cccccccc(address from, address to, uint256 amount) external payable {"
    );
}

#[test]
fn a_one_sided_entry_is_not_a_transfer_party() {
    // records[key] += amount, with nothing lowered anywhere: the key is not a recipient.
    let credit = "PUSH1 0x04 CALLDATALOAD PUSH1 0x00 MSTORE PUSH1 0x03 PUSH1 0x20 MSTORE PUSH1 0x40 PUSH1 0x00 KECCAK256 DUP1 SLOAD PUSH1 0x24 CALLDATALOAD ADD SWAP1 SSTORE STOP";
    let src = source_of(&dispatcher(credit));
    assert!(!src.contains(" to,") && !src.contains(" from,"), "{src}");
    assert!(src.contains("uint256 amount) external"), "{src}");
    assert!(!src.contains(" balances;"), "{src}");
}

/// The slot of the mapping-at-3 entry keyed by the address in calldata word `word`.
fn account_entry(word: &str) -> String {
    format!("PUSH1 {word} CALLDATALOAD PUSH20 0xffffffffffffffffffffffffffffffffffffffff AND PUSH1 0x00 MSTORE PUSH1 0x03 PUSH1 0x20 MSTORE PUSH1 0x40 PUSH1 0x00 KECCAK256")
}

const AMOUNT: &str = "PUSH1 0x44 CALLDATALOAD";

fn conservation_ids(code: &[u8]) -> Vec<String> {
    let r = analyze::analyze(&decompile::decompile(code, &Options::default()));
    let ours = [
        "stale-ledger-write",
        "unbalanced-ledger-move",
        "ledger-total-mismatch",
    ];
    r.findings
        .iter()
        .filter(|f| ours.contains(&f.id.as_str()))
        .map(|f| format!("{} {}", f.id, f.function.as_deref().unwrap_or_default()))
        .collect()
}

#[test]
fn an_entry_raised_from_a_value_read_before_the_other_was_lowered_is_reported() {
    let (from, to) = (account_entry("0x04"), account_entry("0x24"));
    let both_read_first = format!(
        "{from} DUP1 SLOAD {to} DUP1 SLOAD SWAP2 {AMOUNT} SWAP1 SUB DUP4 SSTORE \
         SWAP1 {AMOUNT} ADD SWAP1 SSTORE STOP"
    );
    let hits = conservation_ids(&dispatcher(&both_read_first));
    assert_eq!(
        hits,
        ["stale-ledger-write func_aaaaaaaa [0xaaaaaaaa]"],
        "{hits:?}"
    );

    let read_in_turn = format!(
        "{from} DUP1 SLOAD {AMOUNT} SWAP1 SUB SWAP1 SSTORE \
         {to} DUP1 SLOAD {AMOUNT} ADD SWAP1 SSTORE STOP"
    );
    assert!(conservation_ids(&dispatcher(&read_in_turn)).is_empty());

    let keys_differ =
        "PUSH1 0x04 CALLDATALOAD PUSH20 0xffffffffffffffffffffffffffffffffffffffff AND \
         PUSH1 0x24 CALLDATALOAD PUSH20 0xffffffffffffffffffffffffffffffffffffffff AND \
         EQ ISZERO PUSH2 @go JUMPI PUSH1 0x00 DUP1 REVERT :go JUMPDEST";
    let guarded = format!("{keys_differ} {both_read_first}");
    assert!(conservation_ids(&dispatcher(&guarded)).is_empty());
}

#[test]
fn a_credit_nothing_pays_for_is_reported_when_no_total_records_it() {
    const CALLER_ENTRY: &str =
        "CALLER PUSH1 0x00 MSTORE PUSH1 0x03 PUSH1 0x20 MSTORE PUSH1 0x40 PUSH1 0x00 KECCAK256";
    let (from, to) = (account_entry("0x04"), account_entry("0x24"));
    let moved = format!(
        "{from} DUP1 SLOAD {AMOUNT} SWAP1 SUB SWAP1 SSTORE \
         {to} DUP1 SLOAD {AMOUNT} ADD SWAP1 SSTORE"
    );
    let extra = format!("{CALLER_ENTRY} DUP1 SLOAD PUSH1 0x64 CALLDATALOAD ADD SWAP1 SSTORE");
    let hits = conservation_ids(&dispatcher(&format!("{moved} {extra} STOP")));
    assert_eq!(
        hits,
        ["unbalanced-ledger-move func_aaaaaaaa [0xaaaaaaaa]"],
        "{hits:?}"
    );
    assert!(conservation_ids(&dispatcher(&format!("{moved} STOP"))).is_empty());

    let recorded = "PUSH1 0x05 SLOAD PUSH1 0x64 CALLDATALOAD ADD PUSH1 0x05 SSTORE";
    let with_total = format!("{moved} {extra} {recorded} STOP");
    assert!(conservation_ids(&dispatcher(&with_total)).is_empty());
}

#[test]
fn an_entry_raised_without_the_total_that_moves_with_it_is_reported() {
    let to = account_entry("0x04");
    let amount = "PUSH1 0x24 CALLDATALOAD";
    let credit = format!("{to} DUP1 SLOAD {amount} ADD SWAP1 SSTORE");
    let total = format!("PUSH1 0x05 SLOAD {amount} ADD PUSH1 0x05 SSTORE");
    let code = dispatcher3(
        &format!("{credit} {total} STOP"),
        &format!("{credit} STOP"),
        "STOP",
    );
    let hits = conservation_ids(&code);
    assert_eq!(
        hits,
        ["ledger-total-mismatch func_bbbbbbbb [0xbbbbbbbb]"],
        "{hits:?}"
    );

    let counter = format!("{to} DUP1 SLOAD PUSH1 0x01 ADD SWAP1 SSTORE");
    let counted = "PUSH1 0x05 SLOAD PUSH1 0x01 ADD PUSH1 0x05 SSTORE";
    let code = dispatcher3(
        &format!("{counter} {counted} STOP"),
        &format!("{counter} STOP"),
        "STOP",
    );
    assert!(
        conservation_ids(&code).is_empty(),
        "a step of one is a counter, not an amount"
    );
}

const LINKED: &str = "0x00000000000000000000000000000000000000b1";

/// A call with the four-byte payload `selector` and `value` wei to the fixed address `to`.
fn call_fixed(to: &str, selector: &str, value: &str) -> String {
    format!(
        "PUSH4 {selector} PUSH1 0xe0 SHL PUSH1 0x80 MSTORE PUSH1 0x00 PUSH1 0x00 PUSH1 0x04 \
         PUSH1 0x80 {value} PUSH20 {to} GAS CALL POP"
    )
}

/// Findings of the linked-contract rules on `root` analysed with `linked` fetched at `LINKED`.
fn link_ids(root: &[u8], linked: &[u8]) -> Vec<String> {
    let mut c = decompile::decompile(root, &Options::default());
    let mut lc = decompile::decompile(linked, &Options::default());
    lc.address = Some(LINKED.into());
    c.linked = vec![lc];
    let ours = [
        "linked-call-unanswered",
        "value-to-non-payable",
        "linked-callee-defect",
        "approval-to-open-spender",
    ];
    analyze::analyze(&c)
        .findings
        .iter()
        .filter(|f| ours.contains(&f.id.as_str()))
        .map(|f| format!("{} {:?}", f.id, f.severity))
        .collect()
}

#[test]
fn a_call_is_held_against_the_code_of_the_contract_it_reaches() {
    let plain = dispatcher("STOP");
    let rejects_value =
        dispatcher("CALLVALUE ISZERO PUSH2 @np JUMPI PUSH1 0x00 DUP1 REVERT :np JUMPDEST STOP");
    let no_value = "PUSH1 0x00";
    let one_wei = "PUSH1 0x01";
    let root = |body: String| dispatcher(&format!("{body} STOP"));

    let known = root(call_fixed(LINKED, "0xaaaaaaaa", no_value));
    assert!(link_ids(&known, &plain).is_empty());
    assert!(
        link_ids(&known, &[]).is_empty(),
        "nothing is said about a contract whose code is not there"
    );

    let unknown = root(call_fixed(LINKED, "0x12345678", no_value));
    assert_eq!(
        link_ids(&unknown, &plain),
        ["linked-call-unanswered Medium"]
    );

    let paid = root(call_fixed(LINKED, "0xaaaaaaaa", one_wei));
    assert!(link_ids(&paid, &plain).is_empty());
    assert_eq!(
        link_ids(&paid, &rejects_value),
        ["value-to-non-payable Medium"]
    );

    let bare = root(format!(
        "PUSH1 0x00 PUSH1 0x00 PUSH1 0x00 PUSH1 0x00 {one_wei} PUSH20 {LINKED} GAS CALL POP"
    ));
    assert_eq!(link_ids(&bare, &plain), ["value-to-non-payable Medium"]);
}

#[test]
fn a_called_function_brings_its_own_serious_findings() {
    let root = dispatcher(&format!(
        "{} STOP",
        call_fixed(LINKED, "0xaaaaaaaa", "PUSH1 0x00")
    ));
    let destroys = dispatcher("CALLER SELFDESTRUCT");
    assert_eq!(link_ids(&root, &destroys), ["linked-callee-defect High"]);
    assert!(link_ids(&root, &dispatcher("STOP")).is_empty());
}

#[test]
fn an_approval_is_held_against_what_the_spender_lets_callers_do() {
    let approve = format!(
        "PUSH4 0x095ea7b3 PUSH1 0xe0 SHL PUSH1 0x80 MSTORE PUSH20 {LINKED} PUSH1 0x84 MSTORE \
         PUSH1 0x01 PUSH1 0xa4 MSTORE PUSH1 0x00 PUSH1 0x00 PUSH1 0x44 PUSH1 0x80 PUSH1 0x00 \
         PUSH1 0x04 CALLDATALOAD GAS CALL POP STOP"
    );
    let root = dispatcher(&approve);
    let pulls_from_anyone = dispatcher(
        "PUSH4 0x23b872dd PUSH1 0xe0 SHL PUSH1 0x80 MSTORE PUSH1 0x04 CALLDATALOAD PUSH1 0x84 \
         MSTORE CALLER PUSH1 0xa4 MSTORE PUSH1 0x24 CALLDATALOAD PUSH1 0xc4 MSTORE PUSH1 0x00 \
         PUSH1 0x00 PUSH1 0x64 PUSH1 0x80 PUSH1 0x00 PUSH1 0x44 CALLDATALOAD GAS CALL POP STOP",
    );
    assert_eq!(
        link_ids(&root, &pulls_from_anyone),
        ["approval-to-open-spender High"]
    );
    assert!(link_ids(&root, &dispatcher("STOP")).is_empty());
}
