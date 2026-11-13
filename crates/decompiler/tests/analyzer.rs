use evmdec::analyze::{self, Severity};
use evmdec::decompile::{self, Options};

thread_local! {
    static PADDED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static GUARDS_SEEN: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static GUARD_TO_DROP: std::cell::Cell<Option<usize>> = const { std::cell::Cell::new(None) };
}

const DISPATCH_LABELS: [&str; 5] = ["@f", "@a", "@b", "@c", "@t"];

fn asm(src: &str) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    let mut labels = std::collections::HashMap::new();
    let mut fixups: Vec<(usize, String)> = Vec::new();
    let opcodes: std::collections::HashMap<&str, u8> = (0u8..=255)
        .filter_map(|o| evmdec::opcode::info(o).map(|i| (i.name, o)))
        .collect();
    let mut previous = "";
    for tok in src.split_whitespace() {
        let guard = tok == "JUMPI" && !DISPATCH_LABELS.contains(&previous);
        previous = tok;
        if guard {
            let index = GUARDS_SEEN.with(|g| g.replace(g.get() + 1));
            if GUARD_TO_DROP.with(std::cell::Cell::get) == Some(index) {
                out.extend_from_slice(&[0x90, 0x50, 0x56]);
                continue;
            }
        }
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
        if tok == "JUMPDEST" && PADDED.with(std::cell::Cell::get) {
            out.extend_from_slice(&[0x60, 0x00, 0x50]);
        }
    }
    for (pos, l) in fixups {
        let t = labels[&l] as u16;
        out[pos] = (t >> 8) as u8;
        out[pos + 1] = t as u8;
    }
    out
}

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

fn mread(slot: u8) -> String {
    format!(
        "PUSH1 0x04 CALLDATALOAD PUSH1 0x00 MSTORE PUSH1 0x{slot:02x} PUSH1 0x20 MSTORE PUSH1 0x40 PUSH1 0x00 KECCAK256 SLOAD"
    )
}

fn bounded_payout(avail: &str, bad: &str) -> String {
    limited_payout(avail, "0x24", bad)
}

fn limited_payout(avail: &str, cmp: &str, bad: &str) -> String {
    format!(
        "{avail} PUSH1 {cmp} CALLDATALOAD GT PUSH2 @{bad} JUMPI \
         PUSH1 0x00 PUSH1 0x00 PUSH1 0x00 PUSH1 0x00 PUSH1 0x24 CALLDATALOAD CALLER GAS CALL POP STOP \
         :{bad} JUMPDEST PUSH1 0x00 DUP1 REVERT"
    )
}

fn low128(x: &str) -> String {
    format!("{x} PUSH16 0xffffffffffffffffffffffffffffffff AND")
}

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
    let credit = "PUSH1 0x04 CALLDATALOAD PUSH1 0x00 MSTORE PUSH1 0x03 PUSH1 0x20 MSTORE PUSH1 0x40 PUSH1 0x00 KECCAK256 DUP1 SLOAD PUSH1 0x24 CALLDATALOAD ADD SWAP1 SSTORE STOP";
    let src = source_of(&dispatcher(credit));
    assert!(!src.contains(" to,") && !src.contains(" from,"), "{src}");
    assert!(src.contains("uint256 amount) external"), "{src}");
    assert!(!src.contains(" balances;"), "{src}");
}

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

fn call_fixed(to: &str, selector: &str, value: &str) -> String {
    format!(
        "PUSH4 {selector} PUSH1 0xe0 SHL PUSH1 0x80 MSTORE PUSH1 0x00 PUSH1 0x00 PUSH1 0x04 \
         PUSH1 0x80 {value} PUSH20 {to} GAS CALL POP"
    )
}

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

#[test]
fn a_memory_word_used_after_it_is_overwritten_keeps_its_old_value() {
    let code = dispatcher(
        "PUSH1 0x01 PUSH1 0x24 CALLDATALOAD MSTORE PUSH1 0x80 MLOAD PUSH1 0x07 PUSH1 0x80 MSTORE \
         PUSH1 0x00 SSTORE PUSH1 0x44 CALLDATALOAD PUSH1 0x80 LOG0 STOP",
    );
    let src = source_of(&code);
    let body: Vec<&str> = src.lines().map(str::trim).collect();
    let at = |line: &str| {
        body.iter()
            .position(|l| *l == line)
            .unwrap_or_else(|| panic!("missing `{line}` in {src}"))
    };
    let saved = at("uint256 prev_mem_ptr1 = mem[ptr1];");
    let stored = at("mem[ptr1] = 7;");
    let used = at("stor_0 = prev_mem_ptr1;");
    assert!(saved < stored && stored < used, "{src}");
}

#[test]
fn a_jump_to_no_destination_is_an_abort() {
    let code = dispatcher(
        "PUSH1 0x04 CALLDATALOAD PUSH1 0x02 JUMPI PUSH1 0x01 PUSH1 0x00 SSTORE PUSH1 0x24 \
         CALLDATALOAD ISZERO PUSH2 @bad JUMPI STOP :bad JUMPDEST PUSH1 0x02 JUMP",
    );
    let c = decompile::decompile(&code, &Options::default());
    assert_eq!(c.stats.unresolved_jumps, 0);
    assert!(!c.source.contains("unresolved target"), "{}", c.source);
    assert!(c.source.contains("require(arg0 == 0);"), "{}", c.source);
    assert!(c.source.contains("require(arg1 != 0);"), "{}", c.source);
}

#[test]
fn a_library_call_is_not_a_proxy() {
    let library = "0x00000000000000000000000000000000000000c7";
    let built = dispatcher(&format!(
        "PUSH4 0x12345678 PUSH1 0xe0 SHL PUSH1 0x80 MSTORE PUSH1 0x20 PUSH1 0x80 PUSH1 0x04 \
         PUSH1 0x80 PUSH20 {library} GAS DELEGATECALL POP PUSH1 0x80 MLOAD PUSH1 0x00 SSTORE STOP"
    ));
    let c = decompile::decompile(&built, &Options::default());
    assert!(
        c.delegatecall_targets.is_empty(),
        "{:?}",
        c.delegatecall_targets
    );
    assert_eq!(c.library_targets, [library]);

    let forwards = asm(&format!(
        "CALLDATASIZE PUSH1 0x00 PUSH1 0x00 CALLDATACOPY PUSH1 0x00 PUSH1 0x00 CALLDATASIZE \
         PUSH1 0x00 PUSH20 {library} GAS DELEGATECALL POP RETURNDATASIZE PUSH1 0x00 RETURN"
    ));
    let c = decompile::decompile(&forwards, &Options::default());
    assert_eq!(c.delegatecall_targets, [library]);
    assert!(c.library_targets.is_empty());
}

const ROOT: &str = "0x00000000000000000000000000000000000000a0";
const LIBRARY: &str = "0x00000000000000000000000000000000000000b2";

fn call_with_words(first: &str, second: &str) -> String {
    format!(
        "PUSH4 0xaaaaaaaa PUSH1 0xe0 SHL PUSH1 0x80 MSTORE {first} PUSH1 0x84 MSTORE {second} \
         PUSH1 0xa4 MSTORE PUSH1 0x00 PUSH1 0x00 PUSH1 0x44 PUSH1 0x80 PUSH1 0x00 PUSH20 {LINKED} \
         GAS CALL POP"
    )
}

fn passed_on(
    root: &[u8],
    linked: &[u8],
    library: Option<&[u8]>,
    admits: Option<bool>,
) -> Vec<String> {
    let mut c = decompile::decompile(root, &Options::default());
    c.address = Some(ROOT.into());
    let mut lc = decompile::decompile(linked, &Options::default());
    lc.address = Some(LINKED.into());
    if let Some(admitted) = admits {
        lc.gates_read = true;
        if admitted {
            lc.admits.push(ROOT.into());
        }
    }
    c.linked.push(lc);
    if let Some(code) = library {
        let mut lib = decompile::decompile(code, &Options::default());
        lib.address = Some(LIBRARY.into());
        c.linked.push(lib);
    }
    analyze::analyze(&c)
        .findings
        .iter()
        .filter(|f| f.id.starts_with("unbound-"))
        .map(|f| format!("{} {:?}/{:?}", f.id, f.severity, f.confidence))
        .collect()
}

#[test]
fn an_account_passed_on_unbound_is_held_against_the_function_that_receives_it() {
    let word0 = "PUSH1 0x04 CALLDATALOAD";
    let word1 = "PUSH1 0x24 CALLDATALOAD";
    let lower = format!(
        "{} DUP1 SLOAD {word1} SWAP1 SUB SWAP1 SSTORE STOP",
        account_entry("0x04")
    );
    let gated = dispatcher(&format!("{OWNER_GATE} {lower}"));
    let open = dispatcher(&lower);
    let passes = dispatcher(&format!("{} STOP", call_with_words(word0, word1)));
    let lowered = "unbound-account-passed-on High/Medium";

    assert_eq!(passed_on(&passes, &gated, None, None), [lowered]);
    assert_eq!(
        passed_on(&passes, &gated, None, Some(true)),
        ["unbound-account-passed-on High/High"],
        "the called contract's storage approves the root"
    );
    assert!(
        passed_on(&passes, &gated, None, Some(false)).is_empty(),
        "the called contract does not approve the root, so the call cannot get through"
    );
    assert!(
        passed_on(&passes, &open, None, None).is_empty(),
        "a function anyone can call is its own contract's finding"
    );

    let me =
        "PUSH1 0x04 CALLDATALOAD CALLER EQ PUSH2 @me JUMPI PUSH1 0x00 DUP1 REVERT :me JUMPDEST";
    let bound = dispatcher(&format!("{me} {} STOP", call_with_words(word0, word1)));
    assert!(
        passed_on(&bound, &gated, None, None).is_empty(),
        "the account is the caller"
    );
    let own = dispatcher(&format!("{} STOP", call_with_words("CALLER", word1)));
    assert!(passed_on(&own, &gated, None, None).is_empty());

    let kept = dispatcher(&format!(
        "PUSH1 0x40 PUSH1 0x04 PUSH1 0x60 CALLDATACOPY {} STOP",
        call_with_words("PUSH1 0x60 MLOAD", "PUSH1 0x80 MLOAD")
    ));
    assert_eq!(
        passed_on(&kept, &gated, None, None),
        [lowered],
        "parameters kept in fixed memory words are the same parameters"
    );
}

#[test]
fn a_value_computed_by_a_linked_library_is_read_through_the_call() {
    let word1 = "PUSH1 0x24 CALLDATALOAD";
    let through_library = format!(
        "{} DUP1 SLOAD PUSH4 0xaaaaaaaa PUSH1 0xe0 SHL PUSH1 0x80 MSTORE PUSH1 0x84 MSTORE {word1} \
         PUSH1 0xa4 MSTORE PUSH1 0x20 PUSH1 0x00 PUSH1 0x44 PUSH1 0x80 PUSH20 {LIBRARY} GAS \
         DELEGATECALL POP PUSH1 0x00 MLOAD SWAP1 SSTORE STOP",
        account_entry("0x04")
    );
    let gated = dispatcher(&format!("{OWNER_GATE} {through_library}"));
    let difference = dispatcher(
        "PUSH1 0x24 CALLDATALOAD PUSH1 0x04 CALLDATALOAD SUB PUSH1 0x00 MSTORE PUSH1 0x20 \
         PUSH1 0x00 RETURN",
    );
    let sum = dispatcher(
        "PUSH1 0x24 CALLDATALOAD PUSH1 0x04 CALLDATALOAD ADD PUSH1 0x00 MSTORE PUSH1 0x20 \
         PUSH1 0x00 RETURN",
    );
    let passes = dispatcher(&format!(
        "{} STOP",
        call_with_words("PUSH1 0x04 CALLDATALOAD", word1)
    ));
    assert_eq!(
        passed_on(&passes, &gated, Some(&difference), None),
        ["unbound-account-passed-on High/Medium"],
        "the library returns the old value less the amount"
    );
    assert!(
        passed_on(&passes, &gated, Some(&sum), None).is_empty(),
        "the library returns the old value plus the amount"
    );
    assert!(
        passed_on(&passes, &gated, None, None).is_empty(),
        "without the library's code the stored value is unknown"
    );
}

#[test]
fn a_word_passed_on_into_a_gate_slot_is_reported() {
    let sets_gate = dispatcher(&format!(
        "{OWNER_GATE} PUSH1 0x04 CALLDATALOAD PUSH1 0x00 SSTORE STOP"
    ));
    let sets_other = dispatcher(&format!(
        "{OWNER_GATE} PUSH1 0x04 CALLDATALOAD PUSH1 0x09 SSTORE STOP"
    ));
    let passes = dispatcher(&format!(
        "{} STOP",
        call_with_words("PUSH1 0x04 CALLDATALOAD", "PUSH1 0x00")
    ));
    assert_eq!(
        passed_on(&passes, &sets_gate, None, None),
        ["unbound-address-made-privileged High/Medium"]
    );
    assert!(passed_on(&passes, &sets_other, None, None).is_empty());
}

#[test]
fn gate_locations_are_read_off_the_access_checks() {
    use evmdec::U256;
    let by_slot = decompile::decompile(
        &dispatcher(&format!("{OWNER_GATE} STOP")),
        &Options::default(),
    );
    let gates = analyze::gates(&by_slot);
    assert_eq!(gates.slots, [U256::ZERO]);
    assert!(gates.keys.is_empty());

    let by_flag = dispatcher(
        "CALLER PUSH1 0x00 MSTORE PUSH1 0x01 PUSH1 0x20 MSTORE PUSH1 0x40 PUSH1 0x00 KECCAK256 \
         SLOAD PUSH2 @ok JUMPI PUSH1 0x00 DUP1 REVERT :ok JUMPDEST PUSH1 0x01 PUSH1 0x09 SSTORE \
         STOP",
    );
    let by_flag = decompile::decompile(&by_flag, &Options::default());
    let gates = analyze::gates(&by_flag);
    assert!(gates.slots.is_empty());
    assert_eq!(gates.keys.len(), 1, "{}", by_flag.source);
    let caller = U256::from_hex_str(ROOT).unwrap();
    let mut preimage = caller.to_be_bytes().to_vec();
    preimage.extend_from_slice(&U256::ONE.to_be_bytes());
    assert_eq!(
        analyze::key_for(gates.keys[0], caller),
        Some(U256::from_be_bytes(&evmdec::keccak::keccak256(&preimage))),
        "the entry of the mapping at slot 1 under the caller"
    );

    let balance_test = dispatcher(
        "CALLER PUSH1 0x00 MSTORE PUSH1 0x01 PUSH1 0x20 MSTORE PUSH1 0x40 PUSH1 0x00 KECCAK256 \
         SLOAD PUSH1 0x04 CALLDATALOAD GT PUSH2 @ok JUMPI STOP :ok JUMPDEST PUSH1 0x00 DUP1 REVERT",
    );
    let balance_test = decompile::decompile(&balance_test, &Options::default());
    assert!(
        analyze::gates(&balance_test).keys.is_empty(),
        "an entry compared with an amount is not a flag"
    );
}

#[test]
fn targets_only_read_are_told_from_targets_a_call_may_change() {
    let read = "0x00000000000000000000000000000000000000c1";
    let code = dispatcher(&format!(
        "{} PUSH1 0x00 PUSH1 0x00 PUSH1 0x04 PUSH1 0x80 PUSH20 {read} GAS STATICCALL POP STOP",
        call_fixed(LINKED, "0xaaaaaaaa", "PUSH1 0x00")
    ));
    let c = decompile::decompile(&code, &Options::default());
    assert_eq!(c.call_targets, [LINKED, read], "{}", c.source);
    assert_eq!(c.written_targets, [LINKED]);
}

fn call_words_to(target: &str, first: &str, second: &str, out: &str) -> String {
    format!(
        "PUSH4 0xaaaaaaaa PUSH1 0xe0 SHL PUSH1 0x80 MSTORE {first} PUSH1 0x84 MSTORE {second} \
         PUSH1 0xa4 MSTORE {out} PUSH1 0x00 PUSH1 0x44 PUSH1 0x80 PUSH1 0x00 {target} GAS CALL POP"
    )
}

fn world_ids(root: &[u8], others: &[(&str, &[u8])]) -> Vec<String> {
    let opts = Options {
        embedded: true,
        ..Options::default()
    };
    let mut c = decompile::decompile(root, &opts);
    c.address = Some(ROOT.into());
    for (address, code) in others {
        let mut lc = decompile::decompile(code, &opts);
        lc.address = Some((*address).into());
        c.linked.push(lc);
    }
    analyze::analyze(&c)
        .findings
        .iter()
        .filter(|f| f.id.starts_with("unbound-"))
        .map(|f| format!("{} {:?}/{:?}", f.id, f.severity, f.confidence))
        .collect()
}

#[test]
fn a_library_call_is_folded_into_the_function_that_makes_it() {
    let position = "PUSH1 0x04 CALLDATALOAD PUSH1 0x03 ADD";
    let gate =
        format!("{position} SLOAD CALLER EQ PUSH2 @ok JUMPI PUSH1 0x00 DUP1 REVERT :ok JUMPDEST");
    let store = format!("PUSH1 0x24 CALLDATALOAD {position} SSTORE STOP");
    let gated_library = dispatcher(&format!("{gate} {store}"));
    let open_library = dispatcher(&store);
    let shell = dispatcher(&format!(
        "PUSH4 0xaaaaaaaa PUSH1 0xe0 SHL PUSH1 0x80 MSTORE PUSH1 0x05 PUSH1 0x84 MSTORE PUSH1 0x04 \
         CALLDATALOAD PUSH1 0xa4 MSTORE PUSH1 0x00 PUSH1 0x00 PUSH1 0x44 PUSH1 0x80 PUSH20 \
         {LIBRARY} GAS DELEGATECALL POP STOP"
    ));
    let passes = dispatcher(&format!(
        "{} STOP",
        call_with_words("PUSH1 0x04 CALLDATALOAD", "PUSH1 0x00")
    ));
    assert_eq!(
        world_ids(&passes, &[(LINKED, &shell), (LIBRARY, &gated_library)]),
        ["unbound-address-made-privileged High/Medium"],
        "the library compares the caller with slot 5 + 3 of the shell and writes the word there"
    );
    assert!(
        world_ids(&passes, &[(LINKED, &shell), (LIBRARY, &open_library)]).is_empty(),
        "no check reads the slot"
    );
    assert!(
        world_ids(&passes, &[(LINKED, &shell)]).is_empty(),
        "without the library's code the shell does nothing visible"
    );
}

#[test]
fn a_contract_created_during_the_call_is_read_like_a_linked_one() {
    let made = dispatcher3(
        "PUSH1 0x04 CALLDATALOAD PUSH1 0x00 SSTORE STOP",
        &format!("{OWNER_GATE} PUSH1 0x01 PUSH1 0x09 SSTORE STOP"),
        "STOP",
    );
    assert!(made.len() < 244, "{}", made.len());
    let mut creation = vec![0x60, made.len() as u8, 0x60, 0x0c, 0x60, 0x00, 0x39];
    creation.extend_from_slice(&[0x60, made.len() as u8, 0x60, 0x00, 0xf3]);
    creation.extend_from_slice(&made);
    let size = format!("PUSH1 0x{:02x}", creation.len());
    let maker = dispatcher(&format!(
        "{size} PUSH2 @blob PUSH1 0x80 CODECOPY {size} PUSH1 0x80 PUSH1 0x00 CREATE PUSH1 0x00 \
         MSTORE PUSH1 0x20 PUSH1 0x00 RETURN :blob 0x{}",
        evmdec::hex::encode(&creation)
    ));
    let ledger = dispatcher(&format!(
        "{OWNER_GATE} {} DUP1 SLOAD PUSH1 0x24 CALLDATALOAD SWAP1 SUB SWAP1 SSTORE STOP",
        account_entry("0x04")
    ));
    let word = |n: u32| format!("PUSH1 0x{:02x} CALLDATALOAD", 4 + 32 * n);
    let none = "PUSH1 0x00";
    let lowers = call_words_to(&format!("PUSH20 {LIBRARY}"), &word(0), &word(1), none);
    let makes = call_words_to(&format!("PUSH20 {LINKED}"), none, none, "PUSH1 0x20");
    let configures = call_words_to("PUSH1 0x00 MLOAD", &word(2), none, none);
    let world: [(&str, &[u8]); 2] = [(LINKED, &maker), (LIBRARY, &ledger)];

    let both = dispatcher(&format!("{lowers} {makes} {configures} STOP"));
    assert_eq!(
        world_ids(&both, &world),
        [
            "unbound-account-passed-on High/Medium",
            "unbound-address-made-privileged High/Medium"
        ]
    );
    let only_configures = dispatcher(&format!("{makes} {configures} STOP"));
    assert!(
        world_ids(&only_configures, &world).is_empty(),
        "choosing who controls a contract one creates for oneself is ordinary"
    );
}

#[test]
fn a_clone_created_during_the_call_runs_the_code_it_forwards_to() {
    let implementation = dispatcher3(
        "PUSH1 0x04 CALLDATALOAD PUSH1 0x00 SSTORE STOP",
        &format!("{OWNER_GATE} PUSH1 0x01 PUSH1 0x09 SSTORE STOP"),
        "STOP",
    );
    let ledger = dispatcher(&format!(
        "{OWNER_GATE} {} DUP1 SLOAD PUSH1 0x24 CALLDATALOAD SWAP1 SUB SWAP1 SSTORE STOP",
        account_entry("0x04")
    ));
    let target = LINKED.trim_start_matches("0x");
    let clones = format!(
        "PUSH32 0x3d602d80600a3d3981f3363d3d373d3d3d363d73{} PUSH1 0x80 MSTORE \
         PUSH32 0x{}5af43d82803e903d91602b57fd5bf3000000000000000000 PUSH1 0xa0 MSTORE \
         PUSH1 0x37 PUSH1 0x80 PUSH1 0x00 CREATE PUSH1 0x00 MSTORE",
        &target[..24],
        &target[24..]
    );
    let word = |n: u32| format!("PUSH1 0x{:02x} CALLDATALOAD", 4 + 32 * n);
    let none = "PUSH1 0x00";
    let lowers = call_words_to(&format!("PUSH20 {LIBRARY}"), &word(0), &word(1), none);
    let configures = call_words_to("PUSH1 0x00 MLOAD", &word(2), none, none);
    let root = dispatcher(&format!("{lowers} {clones} {configures} STOP"));
    let c = decompile::decompile(&root, &Options::default());
    assert_eq!(c.clone_targets, [LINKED], "{}", c.source);
    assert_eq!(
        world_ids(&root, &[(LINKED, &implementation), (LIBRARY, &ledger)]),
        [
            "unbound-account-passed-on High/Medium",
            "unbound-address-made-privileged High/Medium"
        ]
    );
}

fn passed_on_finding(
    root: &[u8],
    linked: &[u8],
    library: Option<&[u8]>,
    approved: bool,
) -> analyze::Finding {
    let mut c = decompile::decompile(root, &Options::default());
    c.address = Some(ROOT.into());
    let mut lc = decompile::decompile(linked, &Options::default());
    lc.address = Some(LINKED.into());
    if approved {
        lc.gates_read = true;
        lc.admits.push(ROOT.into());
    }
    c.linked.push(lc);
    if let Some(code) = library {
        let mut lib = decompile::decompile(code, &Options::default());
        lib.address = Some(LIBRARY.into());
        c.linked.push(lib);
    }
    let r = analyze::analyze(&c);
    finding(&r, "unbound-account-passed-on")
        .unwrap_or_else(|| panic!("{:?}", ids(&r)))
        .clone()
}

#[test]
fn a_composed_finding_is_confirmed_by_running_across_contracts() {
    let word0 = "PUSH1 0x04 CALLDATALOAD";
    let word1 = "PUSH1 0x24 CALLDATALOAD";
    let lower = format!(
        "{} DUP1 SLOAD {word1} SWAP1 SUB SWAP1 SSTORE STOP",
        account_entry("0x04")
    );
    let gated = dispatcher(&format!("{OWNER_GATE} {lower}"));
    let passes = dispatcher(&format!("{} STOP", call_with_words(word0, word1)));

    let run = passed_on_finding(&passes, &gated, None, true);
    assert!(run.confirmed, "{}", run.description);
    assert_eq!(run.confidence, analyze::Confidence::High);
    let witness = run.witness.expect("a confirmed finding carries its input");
    assert!(
        witness.starts_with("0xaaaaaaaa") && witness.contains("1111222233334444"),
        "the input calls the function and names an account that is not the caller: {witness}"
    );

    let unread = passed_on_finding(&passes, &gated, None, false);
    assert!(
        !unread.confirmed && unread.witness.is_none(),
        "a gate nobody was read to pass stays shut in the run"
    );
    assert_eq!(unread.confidence, analyze::Confidence::Medium);
}

#[test]
fn the_run_follows_a_library_call_into_the_calling_contract_s_storage() {
    let word1 = "PUSH1 0x24 CALLDATALOAD";
    let through_library = format!(
        "{} DUP1 SLOAD PUSH4 0xaaaaaaaa PUSH1 0xe0 SHL PUSH1 0x80 MSTORE PUSH1 0x84 MSTORE {word1} \
         PUSH1 0xa4 MSTORE PUSH1 0x20 PUSH1 0x00 PUSH1 0x44 PUSH1 0x80 PUSH20 {LIBRARY} GAS \
         DELEGATECALL POP PUSH1 0x00 MLOAD SWAP1 SSTORE STOP",
        account_entry("0x04")
    );
    let gated = dispatcher(&format!("{OWNER_GATE} {through_library}"));
    let difference = dispatcher(
        "PUSH1 0x24 CALLDATALOAD PUSH1 0x04 CALLDATALOAD SUB PUSH1 0x00 MSTORE PUSH1 0x20 \
         PUSH1 0x00 RETURN",
    );
    let passes = dispatcher(&format!(
        "{} STOP",
        call_with_words("PUSH1 0x04 CALLDATALOAD", word1)
    ));
    let run = passed_on_finding(&passes, &gated, Some(&difference), true);
    assert!(
        run.confirmed,
        "the entry ends lower only if the library's code ran: {}",
        run.description
    );
}

#[test]
fn every_path_of_a_function_is_found_by_solving_its_branches() {
    use evmdec::path::{inputs_for, Explorer, Limits};
    use evmdec::solve::{self, Free, Item};
    use evmdec::U256;

    let revert = "PUSH1 0x00 DUP1 REVERT";
    let code = dispatcher(&format!(
        "PUSH1 0x04 CALLDATALOAD PUSH2 0x1234 EQ PUSH2 @a JUMPI {revert} :a JUMPDEST \
         PUSH1 0x04 CALLDATALOAD PUSH1 0x24 CALLDATALOAD GT PUSH2 @b JUMPI {revert} :b JUMPDEST \
         PUSH1 0x07 SLOAD PUSH1 0x44 CALLDATALOAD PUSH1 0x01 OR EQ PUSH2 @c JUMPI \
         PUSH1 0x01 PUSH1 0x01 SSTORE STOP :c JUMPDEST PUSH1 0x02 PUSH1 0x01 SSTORE STOP"
    ));
    let explorer = Explorer::new(&code);
    let start = inputs_for(Some(0xaaaa_aaaa), 3);
    let words = Free {
        words: 3,
        ..Free::default()
    };
    let paths = explorer.explore(&start, &words, Limits::default());

    for p in &paths {
        let replayed = solve::replay(&p.items, &p.inputs);
        for (lifted, real) in replayed.iter().zip(&p.truth) {
            assert!(
                lifted.is_none_or(|t| t == *real),
                "the lifted path disagrees with the run"
            );
        }
    }
    let stored = |p: &evmdec::path::Path| p.run.storage.get(&U256::ONE).copied();
    let finished: Vec<_> = paths.iter().filter(|p| p.succeeded()).collect();
    assert!(
        finished.iter().any(|p| stored(p) == Some(U256::ONE)),
        "the first two guards are passed"
    );
    assert!(
        !finished
            .iter()
            .any(|p| stored(p) == Some(U256::from_u64(2))),
        "slot 7 holds zero and a word with its low bit set is never zero"
    );
    let checks = |p: &evmdec::path::Path| {
        p.items
            .iter()
            .filter(|i| matches!(i, Item::Check { .. }))
            .count()
    };
    assert!(
        paths.iter().map(checks).max() >= Some(4),
        "the dispatcher and three guards"
    );

    let with_state = Free {
        storage: true,
        ..words.clone()
    };
    let paths = explorer.explore(&start, &with_state, Limits::default());
    assert!(
        paths
            .iter()
            .any(|p| p.succeeded() && stored(p) == Some(U256::from_u64(2))),
        "with prior storage free, slot 7 is chosen to match"
    );
}

#[test]
fn a_call_that_needs_earlier_storage_is_reached_through_the_call_that_writes_it() {
    use evmdec::path::Explorer;
    use evmdec::seq::{self, Entry};
    use evmdec::solve;
    use evmdec::U256;

    let revert = "PUSH1 0x00 DUP1 REVERT";
    let own_entry =
        "CALLER PUSH1 0x00 MSTORE PUSH1 0x03 PUSH1 0x20 MSTORE PUSH1 0x40 PUSH1 0x00 KECCAK256";
    let marks = "PUSH1 0x01 PUSH1 0x09 SSTORE STOP";
    let entry = |selector: u32, words: usize| Entry {
        selector: Some(selector),
        words,
    };
    let entries = [
        entry(0xaaaa_aaaa, 1),
        entry(0xbbbb_bbbb, 1),
        entry(0xcccc_cccc, 1),
    ];
    let marked = |p: &evmdec::path::Path| {
        p.succeeded() && p.run.storage.get(&U256::from_u64(9)) == Some(&U256::ONE)
    };
    let none = std::collections::HashMap::new();

    let by_entry = dispatcher3(
        &format!("PUSH1 0x04 CALLDATALOAD {own_entry} SSTORE STOP"),
        &format!("{own_entry} SLOAD PUSH1 0x07 EQ PUSH2 @ok JUMPI {revert} :ok JUMPDEST {marks}"),
        "STOP",
    );
    let explorer = Explorer::new(&by_entry);
    let plan =
        seq::reach(&explorer, &entries, entries[1], &none, &marked).expect("two calls reach it");
    assert_eq!(plan.steps.len(), 1);
    assert_eq!(&plan.steps[0].calldata[..4], [0xaa; 4]);
    assert_eq!(solve::word(&plan.steps[0].calldata, 4), U256::from_u64(7));

    let by_owner = dispatcher3(
        &format!("PUSH1 0x00 SLOAD ISZERO PUSH2 @new JUMPI {revert} :new JUMPDEST CALLER PUSH1 0x00 SSTORE STOP"),
        &format!("{OWNER_GATE} {marks}"),
        "STOP",
    );
    let explorer = Explorer::new(&by_owner);
    let plan =
        seq::reach(&explorer, &entries, entries[1], &none, &marked).expect("claim, then call");
    assert_eq!(plan.steps.len(), 1);
    assert_eq!(&plan.steps[0].calldata[..4], [0xaa; 4]);

    let closed = dispatcher3("STOP", &format!("{OWNER_GATE} {marks}"), "STOP");
    let explorer = Explorer::new(&closed);
    assert!(
        seq::reach(&explorer, &entries, entries[1], &none, &marked).is_none(),
        "nothing writes the owner slot"
    );
}

fn property_ids(code: &[u8]) -> Vec<String> {
    let ours = [
        "entries-total-out-of-step",
        "total-open-at-call",
        "lock-left-set",
        "changed-copy-dropped",
    ];
    analyze::analyze(&decompile::decompile(code, &Options::default()))
        .findings
        .iter()
        .filter(|f| ours.contains(&f.id.as_str()))
        .map(|f| {
            let function = f.function.as_deref().unwrap_or_default();
            format!("{} {} {:?}", f.id, function, f.confidence)
        })
        .collect()
}

#[test]
fn a_run_that_breaks_an_inferred_property_is_reported_with_its_input() {
    let amount = "PUSH1 0x24 CALLDATALOAD";
    let entry = account_entry("0x04");
    let entry_up = format!("{entry} DUP1 SLOAD {amount} ADD SWAP1 SSTORE");
    let entry_down = format!("{entry} DUP1 SLOAD {amount} SWAP1 SUB SWAP1 SSTORE");
    let total_up = format!("PUSH1 0x05 SLOAD {amount} ADD PUSH1 0x05 SSTORE");
    let total_down = format!("PUSH1 0x05 SLOAD {amount} SWAP1 SUB PUSH1 0x05 SSTORE");

    let leaves_total = dispatcher3(
        &format!("{entry_up} {total_up} STOP"),
        &format!("{entry_down} {total_down} STOP"),
        &format!("{entry_up} STOP"),
    );
    assert_eq!(
        property_ids(&leaves_total),
        ["entries-total-out-of-step func_cccccccc [0xcccccccc] High"],
        "two functions keep the pair in step and the third moves the entries alone"
    );
    let r = analyze::analyze(&decompile::decompile(&leaves_total, &Options::default()));
    let f = finding(&r, "entries-total-out-of-step").unwrap();
    assert!(
        f.confirmed
            && f.witness
                .as_deref()
                .is_some_and(|w| w.starts_with("0xcccccccc"))
    );

    let in_step = dispatcher3(
        &format!("{entry_up} {total_up} STOP"),
        &format!("{entry_down} {total_down} STOP"),
        "STOP",
    );
    assert!(property_ids(&in_step).is_empty());

    let call_out = "PUSH1 0x00 DUP1 DUP1 DUP1 DUP1 PUSH1 0x04 CALLDATALOAD GAS CALL POP";
    let open = dispatcher3(
        &format!("{entry_up} {total_up} STOP"),
        &format!("{entry_down} {call_out} {total_down} STOP"),
        "STOP",
    );
    assert_eq!(
        property_ids(&open),
        ["total-open-at-call func_bbbbbbbb [0xbbbbbbbb] High"]
    );
    let closed = dispatcher3(
        &format!("{entry_up} {total_up} STOP"),
        &format!("{entry_down} {total_down} {call_out} STOP"),
        "STOP",
    );
    assert!(
        property_ids(&closed).is_empty(),
        "both are updated before the call"
    );
}

#[test]
fn a_path_that_leaves_a_toggled_slot_set_is_reported() {
    let take = "PUSH1 0x01 PUSH1 0x09 SSTORE";
    let release = "PUSH1 0x00 PUSH1 0x09 SSTORE";
    let work = "PUSH1 0x04 CALLDATALOAD PUSH1 0x02 SSTORE";
    let early = "PUSH1 0x04 CALLDATALOAD PUSH1 0x07 EQ PUSH2 @out JUMPI";
    let leaks = dispatcher(&format!(
        "{take} {early} {work} {release} STOP :out JUMPDEST STOP"
    ));
    assert_eq!(
        property_ids(&leaks),
        ["lock-left-set func_aaaaaaaa [0xaaaaaaaa] High"]
    );
    let restores = dispatcher(&format!(
        "{take} {early} {work} {release} STOP :out JUMPDEST {release} STOP"
    ));
    assert!(property_ids(&restores).is_empty());
}

fn origin_ids(code: &[u8]) -> Vec<String> {
    let ours = ["stored-input-call-target", "gate-on-open-slot"];
    analyze::analyze(&decompile::decompile(code, &Options::default()))
        .findings
        .iter()
        .filter(|f| ours.contains(&f.id.as_str()))
        .map(|f| {
            format!(
                "{} {} {:?}",
                f.id,
                f.function.as_deref().unwrap_or_default(),
                f.severity
            )
        })
        .collect()
}

#[test]
fn a_value_is_followed_back_through_the_slots_it_is_copied_from() {
    let marks = "PUSH1 0x01 PUSH1 0x09 SSTORE STOP";
    let proposes = "PUSH1 0x04 CALLDATALOAD PUSH1 0x01 SSTORE STOP";
    let accepts = "PUSH1 0x01 SLOAD PUSH1 0x00 SSTORE STOP";
    let two_hops = dispatcher3(proposes, accepts, &format!("{OWNER_GATE} {marks}"));
    assert_eq!(
        origin_ids(&two_hops),
        ["gate-on-open-slot func_cccccccc [0xcccccccc] High"],
        "slot 0 is filled from slot 1, which anyone fills"
    );
    let gate_b = OWNER_GATE.replace("@ok", "@okb").replace(":ok", ":okb");
    let guarded = dispatcher3(
        proposes,
        &format!("{gate_b} {accepts}"),
        &format!("{OWNER_GATE} {marks}"),
    );
    assert!(
        origin_ids(&guarded).is_empty(),
        "the copy is behind the gate"
    );

    let entry = account_entry("0x04");
    let own_entry =
        "CALLER PUSH1 0x00 MSTORE PUSH1 0x03 PUSH1 0x20 MSTORE PUSH1 0x40 PUSH1 0x00 KECCAK256";
    let call =
        |target: &str| format!("PUSH1 0x00 DUP1 DUP1 DUP1 DUP1 {target} SLOAD GAS CALL POP STOP");
    let registry = dispatcher3(
        &format!("PUSH1 0x24 CALLDATALOAD {entry} SSTORE STOP"),
        &call(&entry),
        "STOP",
    );
    assert_eq!(
        origin_ids(&registry),
        ["stored-input-call-target func_bbbbbbbb [0xbbbbbbbb] Medium"],
        "anyone fills any entry and anyone triggers the call"
    );
    let self_service = dispatcher3(
        &format!("PUSH1 0x04 CALLDATALOAD {own_entry} SSTORE STOP"),
        &call(own_entry),
        "STOP",
    );
    assert!(
        origin_ids(&self_service).is_empty(),
        "a caller that reads back its own entry chose it"
    );
}

#[test]
fn a_stored_product_is_confirmed_with_an_input_that_wraps_it() {
    use evmdec::solve::word;
    use evmdec::U256;

    let wrap_ids = ["unchecked-arithmetic", "unchecked-block-arithmetic"];
    let product = "PUSH1 0x04 CALLDATALOAD PUSH1 0x24 CALLDATALOAD MUL PUSH1 0x00 SSTORE STOP";
    let r = analyze::analyze(&decompile::decompile(
        &dispatcher(product),
        &Options::default(),
    ));
    let f = r
        .findings
        .iter()
        .find(|f| wrap_ids.contains(&f.id.as_str()))
        .unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert!(f.confirmed, "{}", f.description);
    let data = evmdec::hex::decode(f.witness.as_deref().unwrap()).unwrap();
    let (a, b) = (word(&data, 4), word(&data, 36));
    assert!(!b.is_zero() && a > U256::MAX / b, "the witness must wrap");

    let sum = "PUSH1 0x04 CALLDATALOAD PUSH1 0x01 SLOAD ADD PUSH1 0x00 SSTORE STOP";
    let r = analyze::analyze(&decompile::decompile(&dispatcher(sum), &Options::default()));
    let f = r
        .findings
        .iter()
        .find(|f| wrap_ids.contains(&f.id.as_str()))
        .unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert!(!f.confirmed, "nothing stored yet, so the sum cannot wrap");
}

const CALLER_ENTRY: &str =
    "CALLER PUSH1 0x00 MSTORE PUSH1 0x00 PUSH1 0x20 MSTORE PUSH1 0x40 PUSH1 0x00 KECCAK256";

fn flow_ids(code: &[u8]) -> Vec<String> {
    let ours = ["two-calls-return-more", "inflow-credits-nothing"];
    analyze::analyze(&decompile::decompile(code, &Options::default()))
        .findings
        .iter()
        .filter(|f| ours.contains(&f.id.as_str()))
        .map(|f| {
            assert!(f.confirmed && f.witness.is_some() && f.setup.len() == 1);
            f.id.clone()
        })
        .collect()
}

#[test]
fn a_pair_of_calls_that_returns_more_than_it_took_is_reported() {
    let pay_out = pay_out_checked();
    let doubled = dispatcher3(&pay_in("CALLVALUE PUSH1 0x02 MUL"), &pay_out, "STOP");
    assert_eq!(flow_ids(&doubled), ["two-calls-return-more"]);

    let exact = dispatcher3(&pay_in("CALLVALUE"), &pay_out, "STOP");
    assert!(flow_ids(&exact).is_empty(), "{:?}", flow_ids(&exact));
}

#[test]
fn a_share_of_a_balance_read_from_outside_can_round_a_payment_to_nothing() {
    let vault = share_vault;
    assert_eq!(flow_ids(&vault("")), ["inflow-credits-nothing"]);

    let floor = "DUP1 PUSH2 @some JUMPI PUSH1 0x00 DUP1 REVERT :some JUMPDEST";
    assert!(flow_ids(&vault(floor)).is_empty());
}

#[test]
fn a_change_made_to_a_memory_copy_of_storage_and_then_dropped_is_reported() {
    let copy_and_change =
        "PUSH1 0x05 SLOAD PUSH1 0x80 MSTORE PUSH1 0x04 CALLDATALOAD PUSH1 0x80 MSTORE";
    let dropped = dispatcher(&format!("{copy_and_change} STOP"));
    assert_eq!(
        property_ids(&dropped),
        ["changed-copy-dropped func_aaaaaaaa [0xaaaaaaaa] High"]
    );

    let stored = dispatcher(&format!(
        "{copy_and_change} PUSH1 0x80 MLOAD PUSH1 0x05 SSTORE STOP"
    ));
    assert!(property_ids(&stored).is_empty());

    let returned = dispatcher(&format!("{copy_and_change} PUSH1 0x20 PUSH1 0x80 RETURN"));
    assert!(property_ids(&returned).is_empty());
}

#[test]
fn a_confirmation_starts_from_the_storage_the_constructor_leaves() {
    let runtime = dispatcher(
        "PUSH1 0x00 SLOAD ISZERO PUSH2 @ok JUMPI PUSH1 0x00 DUP1 REVERT :ok JUMPDEST \
         CALLER SELFDESTRUCT",
    );
    let r = analyze::analyze(&decompile::decompile(&runtime, &Options::default()));
    let alone = finding(&r, "selfdestruct").unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert!(
        alone.confirmed,
        "slot 0 is unset when only runtime code is known"
    );

    let mut creation = asm(&format!(
        "PUSH1 0x01 PUSH1 0x00 SSTORE PUSH2 {len:#06x} DUP1 PUSH2 0x0012 PUSH1 0x00 CODECOPY \
         PUSH1 0x00 RETURN",
        len = runtime.len()
    ));
    assert_eq!(creation.len(), 0x12);
    creation.extend(&runtime);
    let c = decompile::decompile(&creation, &Options::default());
    assert!(
        c.constructor.is_some(),
        "the fixture must be seen as creation code"
    );
    let r = analyze::analyze(&c);
    assert!(
        !r.findings.iter().any(|f| f.confirmed),
        "the constructor sets slot 0, so the guard holds for every later caller"
    );
}

#[test]
fn a_signed_call_with_no_counter_in_its_digest_is_accepted_twice() {
    let twice = |code: &[u8]| {
        let r = analyze::analyze(&decompile::decompile(code, &Options::default()));
        finding(&r, "signed-message-accepted-twice").cloned()
    };
    let f = twice(&signed_payment(false)).expect("nothing takes the message out of use");
    assert!(f.confirmed && f.severity == Severity::High);
    assert!(
        !f.observed.is_empty(),
        "a confirmed finding says what the run did"
    );
    assert!(
        twice(&signed_payment(true)).is_none(),
        "the counter changes the digest"
    );
}

const REVERT: &str = "PUSH1 0x00 DUP1 REVERT";

fn report_of(code: &[u8]) -> analyze::Report {
    analyze::analyze(&decompile::decompile(code, &Options::default()))
}

#[test]
fn phases_are_recovered_and_one_that_is_never_entered_is_reported() {
    let step = |at: u8, then: &str| {
        format!(
            "PUSH1 0x03 SLOAD PUSH1 {at:#04x} EQ PUSH2 @at{at} JUMPI {REVERT} \
             :at{at} JUMPDEST {then} STOP"
        )
    };
    let machine = |last: u8| {
        dispatcher3(
            &step(0, "PUSH1 0x01 PUSH1 0x03 SSTORE"),
            &step(1, "PUSH1 0x02 PUSH1 0x03 SSTORE"),
            &step(last, "PUSH1 0x01 PUSH1 0x07 SSTORE"),
        )
    };
    let r = report_of(&machine(5));
    let phases = r
        .maps
        .iter()
        .find(|s| s.title == "Phases")
        .expect("a phase map");
    let line = &phases.lines[0];
    assert!(
        line.contains("from 0 to 1") && line.contains("from 1 to 2"),
        "{line}"
    );
    assert!(
        finding(&r, "phase-never-entered").is_some(),
        "{:?}",
        ids(&r)
    );

    assert!(finding(&report_of(&machine(2)), "phase-never-entered").is_none());
}

fn deployed(constructor: &str, runtime: &[u8]) -> Vec<u8> {
    let tail = "DUP1 PUSH2 @code PUSH1 0x00 CODECOPY PUSH1 0x00 RETURN :code";
    let mut code = asm(&format!(
        "{constructor} PUSH2 {:#06x} {tail}",
        runtime.len()
    ));
    code.extend(runtime);
    code
}

#[test]
fn a_caller_check_on_a_slot_nothing_sets_is_reported_with_the_authority_map() {
    let runtime = dispatcher(&format!("{OWNER_GATE} CALLER SELFDESTRUCT"));
    let marks = "PUSH1 0x01 PUSH1 0x09 SSTORE";

    let r = report_of(&deployed(marks, &runtime));
    assert!(finding(&r, "gate-never-set").is_some(), "{:?}", ids(&r));
    let map = r
        .maps
        .iter()
        .find(|s| s.title == "Authority map")
        .expect("a map");
    assert!(map.lines[0].contains("No function in the runtime code writes it"));

    let owned = format!("{marks} CALLER PUSH1 0x00 SSTORE");
    let r = report_of(&deployed(&owned, &runtime));
    assert!(finding(&r, "gate-never-set").is_none());
    let deployment = r.maps.iter().find(|s| s.title == "Deployment");
    let lines = &deployment.expect("a section").lines;
    assert!(lines.contains(&"slot 0x0 is set to the deployer".to_string()));
}

fn entry_of(account: &str) -> String {
    format!(
        "{account} PUSH1 0x00 MSTORE PUSH1 0x00 PUSH1 0x20 MSTORE PUSH1 0x40 PUSH1 0x00 KECCAK256"
    )
}

fn lowered(account: &str, label: &str) -> String {
    format!(
        "{} DUP1 SLOAD DUP3 DUP2 LT ISZERO PUSH2 @{label} JUMPI {REVERT} :{label} JUMPDEST \
         DUP3 SWAP1 SUB SWAP1 SSTORE",
        entry_of(account)
    )
}

fn ledger(credit: &str, allowance: &str) -> Vec<u8> {
    let raised = |account: &str| format!("{} DUP1 SLOAD DUP3 ADD SWAP1 SSTORE", entry_of(account));
    let first = "PUSH1 0x04 CALLDATALOAD";
    let second = "PUSH1 0x24 CALLDATALOAD";
    let transfer = format!(
        "{second} {} {credit} {} POP POP STOP",
        lowered("CALLER", "paid"),
        raised(first)
    );
    let transfer_from = format!(
        "PUSH1 0x44 CALLDATALOAD {allowance} {} {} POP STOP",
        lowered(first, "held"),
        raised(second)
    );
    let balance_of = format!(
        "{} SLOAD PUSH1 0x80 MSTORE PUSH1 0x20 PUSH1 0x80 RETURN",
        entry_of(first)
    );
    asm(&format!(
        "PUSH1 0x80 PUSH1 0x40 MSTORE PUSH1 0x00 CALLDATALOAD PUSH1 0xe0 SHR \
         DUP1 PUSH4 0xa9059cbb EQ PUSH2 @t JUMPI DUP1 PUSH4 0x23b872dd EQ PUSH2 @f JUMPI \
         PUSH4 0x70a08231 EQ PUSH2 @b JUMPI {REVERT} \
         :t JUMPDEST POP {transfer} :f JUMPDEST POP {transfer_from} :b JUMPDEST {balance_of}"
    ))
}

#[test]
fn a_standard_interface_is_measured_and_not_taken_on_trust() {
    let spends = SPENDS;
    let measured = |code: &[u8]| {
        let ours = [
            "transfer-creates-value",
            "transfer-delivers-less",
            "transfer-touches-third-entry",
            "reported-balance-differs",
            "transferfrom-ignores-allowance",
            "allowance-not-spent",
        ];
        let r = report_of(code);
        let section = r
            .maps
            .iter()
            .any(|s| s.title.starts_with("Standard interface"));
        assert!(section, "the interface is present, so it must be measured");
        let found = r.findings.iter().filter(|f| ours.contains(&f.id.as_str()));
        found.map(|f| f.id.clone()).collect::<Vec<_>>()
    };

    assert!(measured(&ledger("DUP1", spends)).is_empty());
    assert_eq!(
        measured(&ledger("DUP1 PUSH1 0x02 MUL", spends)),
        ["transfer-creates-value"]
    );
    assert_eq!(
        measured(&ledger("PUSH1 0x0a DUP2 DIV DUP2 SUB", spends)),
        ["transfer-delivers-less"]
    );
    assert_eq!(
        measured(&ledger("DUP1", "")),
        ["transferfrom-ignores-allowance"]
    );
}

#[test]
fn a_slot_number_taken_from_the_call_is_reported_unless_it_is_bounded() {
    let write = "PUSH1 0x24 CALLDATALOAD PUSH1 0x04 CALLDATALOAD SSTORE STOP";
    let aimed = report_of(&dispatcher(write));
    assert!(
        finding(&aimed, "input-picks-storage-slot").is_some(),
        "{:?}",
        ids(&aimed)
    );

    let bounded = dispatcher(&format!(
        "PUSH1 0x0a PUSH1 0x04 CALLDATALOAD LT PUSH2 @in JUMPI {REVERT} :in JUMPDEST {write}"
    ));
    assert!(finding(&report_of(&bounded), "input-picks-storage-slot").is_none());

    let hashed = dispatcher(&format!(
        "PUSH1 0x24 CALLDATALOAD {} SSTORE STOP",
        entry_of("PUSH1 0x04 CALLDATALOAD")
    ));
    assert!(finding(&report_of(&hashed), "input-picks-storage-slot").is_none());
}

struct Case {
    rule: &'static str,
    flawed: bool,
    confirmed: bool,
    build: fn() -> Vec<u8>,
}

fn pay_in(credit: &str) -> String {
    format!("{credit} {CALLER_ENTRY} DUP1 SLOAD DUP3 ADD SWAP1 SSTORE POP STOP")
}

fn pay_out_checked() -> String {
    format!(
        "PUSH1 0x04 CALLDATALOAD {CALLER_ENTRY} DUP1 SLOAD \
         DUP3 DUP2 LT ISZERO PUSH2 @ok JUMPI {REVERT} :ok JUMPDEST \
         DUP3 SWAP1 SUB SWAP1 SSTORE \
         PUSH1 0x00 DUP1 DUP1 DUP1 DUP5 CALLER GAS CALL POP STOP"
    )
}

fn pay_out_all(clear_first: bool) -> String {
    let pays = "PUSH1 0x00 DUP1 DUP1 DUP1 DUP5 CALLER GAS CALL POP";
    match clear_first {
        true => format!("{CALLER_ENTRY} DUP1 SLOAD PUSH1 0x00 DUP3 SSTORE {pays} POP POP STOP"),
        false => format!("{CALLER_ENTRY} DUP1 SLOAD {pays} POP PUSH1 0x00 SWAP1 SSTORE STOP"),
    }
}

fn share_vault(guard: &str) -> Vec<u8> {
    let asset = "PUSH2 0xb1b1";
    dispatcher(&format!(
        "PUSH4 0x70a08231 PUSH1 0xe0 SHL PUSH1 0x80 MSTORE ADDRESS PUSH1 0x84 MSTORE \
         PUSH1 0x20 PUSH1 0x80 PUSH1 0x24 PUSH1 0x80 {asset} GAS STATICCALL POP \
         PUSH1 0x80 MLOAD PUSH1 0x01 SLOAD PUSH1 0x04 CALLDATALOAD \
         DUP2 ISZERO PUSH2 @first JUMPI DUP3 DUP3 DUP3 MUL DIV PUSH2 @join JUMP \
         :first JUMPDEST DUP1 :join JUMPDEST {guard} \
         PUSH4 0x23b872dd PUSH1 0xe0 SHL PUSH1 0x80 MSTORE CALLER PUSH1 0x84 MSTORE \
         ADDRESS PUSH1 0xa4 MSTORE DUP2 PUSH1 0xc4 MSTORE \
         PUSH1 0x00 DUP1 PUSH1 0x64 PUSH1 0x80 PUSH1 0x00 {asset} GAS CALL POP \
         {CALLER_ENTRY} DUP1 SLOAD DUP3 ADD SWAP1 SSTORE \
         DUP3 ADD PUSH1 0x01 SSTORE STOP"
    ))
}

fn signed_payment(counted: bool) -> Vec<u8> {
    let (extra, len, after) = match counted {
        true => (
            "PUSH1 0x01 SLOAD PUSH1 0xa0 MSTORE",
            "0x40",
            "PUSH1 0x01 SLOAD PUSH1 0x01 ADD PUSH1 0x01 SSTORE",
        ),
        false => ("", "0x20", ""),
    };
    dispatcher(&format!(
        "PUSH1 0x64 CALLDATALOAD PUSH1 0x80 MSTORE {extra} \
         PUSH1 {len} PUSH1 0x80 KECCAK256 PUSH1 0x80 MSTORE \
         PUSH1 0x04 CALLDATALOAD PUSH1 0xa0 MSTORE PUSH1 0x24 CALLDATALOAD PUSH1 0xc0 MSTORE \
         PUSH1 0x44 CALLDATALOAD PUSH1 0xe0 MSTORE \
         PUSH1 0x20 PUSH1 0x80 PUSH1 0x80 PUSH1 0x80 PUSH1 0x01 GAS STATICCALL POP \
         PUSH1 0x80 MLOAD PUSH1 0x00 SLOAD EQ PUSH2 @ok JUMPI {REVERT} \
         :ok JUMPDEST {after} \
         PUSH1 0x00 DUP1 DUP1 DUP1 PUSH1 0x64 CALLDATALOAD CALLER GAS CALL POP STOP"
    ))
}

fn signed_to(receiver_signed: bool) -> Vec<u8> {
    let (extra, len) = match receiver_signed {
        true => ("PUSH1 0x84 CALLDATALOAD PUSH1 0xa0 MSTORE", "0x40"),
        false => ("", "0x20"),
    };
    dispatcher(&format!(
        "PUSH1 0x64 CALLDATALOAD PUSH1 0x80 MSTORE {extra} \
         PUSH1 {len} PUSH1 0x80 KECCAK256 PUSH1 0x80 MSTORE \
         PUSH1 0x04 CALLDATALOAD PUSH1 0xa0 MSTORE PUSH1 0x24 CALLDATALOAD PUSH1 0xc0 MSTORE \
         PUSH1 0x44 CALLDATALOAD PUSH1 0xe0 MSTORE \
         PUSH1 0x20 PUSH1 0x80 PUSH1 0x80 PUSH1 0x80 PUSH1 0x01 GAS STATICCALL POP \
         PUSH1 0x80 MLOAD PUSH1 0x00 SLOAD EQ PUSH2 @ok JUMPI {REVERT} :ok JUMPDEST \
         PUSH1 0x00 DUP1 DUP1 DUP1 PUSH1 0x64 CALLDATALOAD PUSH1 0x84 CALLDATALOAD GAS CALL POP \
         STOP"
    ))
}

fn timed(setter_gate: &str, relation: &str, with_setter: bool) -> Vec<u8> {
    let setter = match with_setter {
        true => format!("{setter_gate} PUSH1 0x04 CALLDATALOAD PUSH1 0x05 SSTORE STOP"),
        false => "STOP".to_string(),
    };
    dispatcher3(
        &setter,
        &format!(
            "PUSH1 0x05 SLOAD TIMESTAMP {relation} PUSH2 @open JUMPI {REVERT} :open JUMPDEST \
             PUSH1 0x01 PUSH1 0x06 SSTORE STOP"
        ),
        "STOP",
    )
}

fn stored_product(narrowed: &str) -> Vec<u8> {
    dispatcher(&format!(
        "PUSH1 0x04 CALLDATALOAD {narrowed} PUSH1 0x24 CALLDATALOAD {narrowed} MUL \
         PUSH1 0x00 SSTORE STOP"
    ))
}

#[test]
fn a_product_of_two_narrow_words_is_shown_to_stay_in_range() {
    let r = report_of(&stored_product("PUSH2 0xffff AND"));
    let wraps = ["unchecked-arithmetic", "unchecked-block-arithmetic"];
    let f = r.findings.iter().find(|f| wraps.contains(&f.id.as_str()));
    let f = f.unwrap_or_else(|| panic!("{:?}", ids(&r)));
    assert!(
        !f.confirmed && f.severity == Severity::Info,
        "{:?}",
        f.severity
    );
    assert!(f.description.contains("Range analysis"));
}

fn proportional(burn: &str) -> Vec<u8> {
    let pay_in = format!(
        "CALLVALUE {CALLER_ENTRY} DUP1 SLOAD DUP3 ADD SWAP1 SSTORE \
         PUSH1 0x01 SLOAD ADD PUSH1 0x01 SSTORE STOP"
    );
    let pay_out = format!(
        "PUSH1 0x04 CALLDATALOAD {burn} {CALLER_ENTRY} DUP1 SLOAD \
         DUP3 DUP2 LT ISZERO PUSH2 @has JUMPI {REVERT} :has JUMPDEST \
         DUP3 SWAP1 SUB SWAP1 SSTORE \
         PUSH1 0x01 SLOAD SUB PUSH1 0x01 SSTORE \
         PUSH1 0x00 DUP1 DUP1 DUP1 PUSH1 0x04 CALLDATALOAD CALLER GAS CALL POP STOP"
    );
    dispatcher3(&pay_in, &pay_out, "STOP")
}

const BURN_ROUNDED_DOWN: &str = "SELFBALANCE PUSH1 0x01 SLOAD DUP3 MUL DIV SWAP1 POP";
const BURN_ROUNDED_UP: &str = "SELFBALANCE PUSH1 0x01 DUP2 SUB PUSH1 0x01 SLOAD DUP4 MUL ADD DIV \
     SWAP1 POP";

const PAY_IN_COUNTED: &str = "CALLVALUE CALLER PUSH1 0x00 MSTORE PUSH1 0x00 PUSH1 0x20 MSTORE \
     PUSH1 0x40 PUSH1 0x00 KECCAK256 DUP1 SLOAD DUP3 ADD SWAP1 SSTORE \
     PUSH1 0x01 SLOAD ADD PUSH1 0x01 SSTORE STOP";

fn pooled(limited_by_own_entry: bool) -> Vec<u8> {
    let by_total = format!(
        "PUSH1 0x04 CALLDATALOAD PUSH1 0x01 SLOAD \
         DUP2 DUP2 LT ISZERO PUSH2 @cov JUMPI {REVERT} :cov JUMPDEST \
         DUP2 SWAP1 SUB PUSH1 0x01 SSTORE \
         PUSH1 0x00 DUP1 DUP1 DUP1 DUP5 CALLER GAS CALL POP POP STOP"
    );
    let take = match limited_by_own_entry {
        true => pay_out_checked(),
        false => by_total,
    };
    dispatcher3(PAY_IN_COUNTED, &take, "STOP")
}

fn cut_payout(floor: bool) -> Vec<u8> {
    let floor = match floor {
        true => format!(
            "DUP1 PUSH1 0x04 CALLDATALOAD GT ISZERO PUSH2 @floor JUMPI {REVERT} :floor JUMPDEST"
        ),
        false => String::new(),
    };
    let cash_out = format!(
        "{CALLER_ENTRY} DUP1 SLOAD PUSH1 0x02 SLOAD \
         DUP1 DUP3 LT ISZERO PUSH2 @enough JUMPI {REVERT} :enough JUMPDEST \
         SWAP1 SUB {floor} PUSH1 0x00 DUP3 SSTORE \
         PUSH1 0x00 DUP1 DUP1 DUP1 DUP5 CALLER GAS CALL POP POP POP STOP"
    );
    dispatcher3(
        &pay_in("CALLVALUE"),
        "PUSH1 0x04 CALLDATALOAD PUSH1 0x02 SSTORE STOP",
        &cash_out,
    )
}

fn pays_two(each_required: bool) -> Vec<u8> {
    let pay = |slot: u8, label: &str| {
        let after = match each_required {
            true => format!("PUSH2 @{label} JUMPI {REVERT} :{label} JUMPDEST"),
            false => "POP".to_string(),
        };
        format!("PUSH1 0x00 DUP1 DUP1 DUP1 PUSH1 0x01 PUSH1 {slot:#04x} SLOAD GAS CALL {after}")
    };
    dispatcher(&format!(
        "{} {} PUSH1 0x01 PUSH1 0x07 SSTORE STOP",
        pay(5, "first"),
        pay(6, "second")
    ))
}

fn asset_vault(clear_first: bool) -> Vec<u8> {
    let asset = "PUSH2 0xb1b1";
    let pull = format!(
        "PUSH4 0x23b872dd PUSH1 0xe0 SHL PUSH1 0x80 MSTORE CALLER PUSH1 0x84 MSTORE \
         ADDRESS PUSH1 0xa4 MSTORE PUSH1 0x04 CALLDATALOAD PUSH1 0xc4 MSTORE \
         PUSH1 0x20 PUSH1 0x80 PUSH1 0x64 PUSH1 0x80 PUSH1 0x00 {asset} GAS CALL POP \
         PUSH1 0x04 CALLDATALOAD {CALLER_ENTRY} DUP1 SLOAD DUP3 ADD SWAP1 SSTORE POP STOP"
    );
    let send = format!(
        "PUSH4 0xa9059cbb PUSH1 0xe0 SHL PUSH1 0x80 MSTORE CALLER PUSH1 0x84 MSTORE \
         DUP1 PUSH1 0xa4 MSTORE \
         PUSH1 0x20 PUSH1 0x80 PUSH1 0x44 PUSH1 0x80 PUSH1 0x00 {asset} GAS CALL POP"
    );
    let give_back = match clear_first {
        true => format!("{CALLER_ENTRY} DUP1 SLOAD PUSH1 0x00 DUP3 SSTORE {send} POP POP STOP"),
        false => format!("{CALLER_ENTRY} DUP1 SLOAD {send} POP PUSH1 0x00 SWAP1 SSTORE STOP"),
    };
    dispatcher3(&pull, &give_back, "STOP")
}

fn limits_with_a_copied_record(draw_subtracts_both: bool) -> Vec<u8> {
    let draw = match draw_subtracts_both {
        true => format!("{} {} ADD {} SUB", mread(2), mread(1), mread(0)),
        false => format!("{} {} SUB", mread(1), mread(0)),
    };
    let copied = "PUSH1 0x00 :cp JUMPDEST DUP1 PUSH1 0x03 GT ISZERO PUSH2 @cpd JUMPI \
         PUSH1 0x04 CALLDATALOAD PUSH1 0x00 MSTORE DUP1 PUSH1 0x20 MSTORE \
         PUSH1 0x40 PUSH1 0x00 KECCAK256 SLOAD \
         DUP2 PUSH1 0x20 MUL PUSH1 0x80 ADD MSTORE PUSH1 0x01 ADD PUSH2 @cp JUMP \
         :cpd JUMPDEST POP \
         PUSH1 0xc0 MLOAD PUSH1 0xa0 MLOAD ADD PUSH1 0x80 MLOAD SUB";
    dispatcher3(
        &bounded_payout(&draw, "bad_draw"),
        &bounded_payout(copied, "bad_exit"),
        "STOP",
    )
}

fn clocked(clock: &str) -> Vec<u8> {
    dispatcher3(
        &format!("{clock} PUSH1 0x04 CALLDATALOAD ADD PUSH1 0x05 SSTORE STOP"),
        &format!(
            "PUSH1 0x05 SLOAD TIMESTAMP GT PUSH2 @ok JUMPI {REVERT} :ok JUMPDEST \
             PUSH1 0x01 PUSH1 0x06 SSTORE STOP"
        ),
        "STOP",
    )
}

fn phased(last: u8) -> Vec<u8> {
    let step = |at: u8, then: &str| {
        format!(
            "PUSH1 0x03 SLOAD PUSH1 {at:#04x} EQ PUSH2 @at{at} JUMPI {REVERT} \
             :at{at} JUMPDEST {then} STOP"
        )
    };
    dispatcher3(
        &step(0, "PUSH1 0x01 PUSH1 0x03 SSTORE"),
        &step(1, "PUSH1 0x02 PUSH1 0x03 SSTORE"),
        &step(last, "PUSH1 0x01 PUSH1 0x07 SSTORE"),
    )
}

fn gated_after(constructor: &str) -> Vec<u8> {
    let runtime = dispatcher(&format!("{OWNER_GATE} CALLER SELFDESTRUCT"));
    deployed(constructor, &runtime)
}

fn pulls(check: &str) -> Vec<u8> {
    dispatcher(&format!(
        "PUSH4 0x23b872dd PUSH1 0xe0 SHL PUSH1 0x80 MSTORE CALLER PUSH1 0x84 MSTORE \
         ADDRESS PUSH1 0xa4 MSTORE PUSH1 0x04 CALLDATALOAD PUSH1 0xc4 MSTORE \
         PUSH1 0x20 PUSH1 0x80 PUSH1 0x64 PUSH1 0x80 PUSH1 0x00 PUSH2 0xb1b1 GAS CALL POP \
         {check} \
         PUSH1 0x04 CALLDATALOAD {CALLER_ENTRY} DUP1 SLOAD DUP3 ADD SWAP1 SSTORE POP STOP"
    ))
}

const ANSWER_TRUE: &str = "PUSH1 0x80 MLOAD PUSH2 @yes JUMPI PUSH1 0x00 DUP1 REVERT :yes JUMPDEST";

fn answer_full() -> String {
    format!("RETURNDATASIZE PUSH1 0x20 EQ PUSH2 @full JUMPI {REVERT} :full JUMPDEST {ANSWER_TRUE}")
}

fn walked(bound: &str) -> Vec<u8> {
    dispatcher3(
        "PUSH1 0x05 SLOAD PUSH1 0x01 ADD PUSH1 0x05 SSTORE STOP",
        &format!(
            "PUSH1 0x00 :top JUMPDEST {bound} DUP2 LT ISZERO PUSH2 @done JUMPI \
             DUP1 SLOAD POP PUSH1 0x01 ADD PUSH2 @top JUMP :done JUMPDEST POP STOP"
        ),
        "STOP",
    )
}

const SPENDS: &str = "PUSH1 0x04 CALLDATALOAD PUSH1 0x00 MSTORE PUSH1 0x01 PUSH1 0x20 MSTORE \
     PUSH1 0x40 PUSH1 0x00 KECCAK256 PUSH1 0x20 MSTORE CALLER PUSH1 0x00 MSTORE \
     PUSH1 0x40 PUSH1 0x00 KECCAK256 DUP1 SLOAD DUP3 DUP2 LT ISZERO \
     PUSH2 @allowed JUMPI PUSH1 0x00 DUP1 REVERT :allowed JUMPDEST \
     DUP3 SWAP1 SUB SWAP1 SSTORE";

const COPY_AND_CHANGE: &str =
    "PUSH1 0x05 SLOAD PUSH1 0x80 MSTORE PUSH1 0x04 CALLDATALOAD PUSH1 0x80 MSTORE";
const AIMED_WRITE: &str = "PUSH1 0x24 CALLDATALOAD PUSH1 0x04 CALLDATALOAD SSTORE STOP";
const STORE_WORD: &str = "PUSH1 0x04 CALLDATALOAD PUSH1 0x01 SSTORE STOP";
const MARKS: &str = "PUSH1 0x01 PUSH1 0x09 SSTORE";

fn cases() -> Vec<Case> {
    let pair = |rule, confirmed, flawed: fn() -> Vec<u8>, sound: fn() -> Vec<u8>| {
        [(true, flawed), (false, sound)].map(|(flawed, build)| Case {
            rule,
            flawed,
            confirmed,
            build,
        })
    };
    let all = [
        pair(
            "two-calls-return-more",
            true,
            || {
                dispatcher3(
                    &pay_in("CALLVALUE PUSH1 0x02 MUL"),
                    &pay_out_checked(),
                    "STOP",
                )
            },
            || dispatcher3(&pay_in("CALLVALUE"), &pay_out_checked(), "STOP"),
        ),
        pair(
            "reentrancy|reentered-call-pays-again",
            true,
            || dispatcher3(&pay_in("CALLVALUE"), &pay_out_all(false), "STOP"),
            || dispatcher3(&pay_in("CALLVALUE"), &pay_out_all(true), "STOP"),
        ),
        pair(
            "inflow-credits-nothing",
            true,
            || share_vault(""),
            || share_vault("DUP1 PUSH2 @some JUMPI PUSH1 0x00 DUP1 REVERT :some JUMPDEST"),
        ),
        pair(
            "changed-copy-dropped",
            true,
            || dispatcher(&format!("{COPY_AND_CHANGE} STOP")),
            || {
                dispatcher(&format!(
                    "{COPY_AND_CHANGE} PUSH1 0x80 MLOAD PUSH1 0x05 SSTORE STOP"
                ))
            },
        ),
        pair(
            "signed-message-accepted-twice",
            true,
            || signed_payment(false),
            || signed_payment(true),
        ),
        pair(
            "clock-units-mixed",
            true,
            || clocked("NUMBER"),
            || clocked("TIMESTAMP"),
        ),
        pair(
            "signed-call-leaves-word-unsigned",
            true,
            || signed_to(false),
            || signed_to(true),
        ),
        pair(
            "time-bound-set-by-anyone",
            true,
            || timed("", "GT", true),
            || timed(OWNER_GATE, "GT", true),
        ),
        pair(
            "time-window-never-opens",
            false,
            || timed("", "LT", false),
            || timed(OWNER_GATE, "LT", true),
        ),
        pair(
            "unchecked-arithmetic|unchecked-block-arithmetic",
            true,
            || stored_product(""),
            || stored_product("PUSH2 0xffff AND"),
        ),
        pair(
            "rounding-favours-caller",
            true,
            || proportional(BURN_ROUNDED_DOWN),
            || proportional(BURN_ROUNDED_UP),
        ),
        pair(
            "reentrancy|reentered-call-pays-again",
            true,
            || asset_vault(false),
            || asset_vault(true),
        ),
        pair(
            "payout-grows-with-other-payment",
            true,
            || pooled(false),
            || pooled(true),
        ),
        pair(
            "earlier-call-lowers-payout",
            true,
            || cut_payout(false),
            || cut_payout(true),
        ),
        pair(
            "one-refusal-blocks-all|blocking-payout-loop|fixed-payee-can-block",
            true,
            || pays_two(true),
            || pays_two(false),
        ),
        pair(
            "inconsistent-liability-accounting",
            false,
            || limits_with_a_copied_record(false),
            || limits_with_a_copied_record(true),
        ),
        pair("phase-never-entered", false, || phased(5), || phased(2)),
        pair(
            "gate-never-set",
            false,
            || gated_after(MARKS),
            || gated_after(&format!("{MARKS} CALLER PUSH1 0x00 SSTORE")),
        ),
        pair(
            "refused-transfer-treated-as-done|erc20-return-ignored|unchecked-token-pull",
            true,
            || pulls(""),
            || pulls(ANSWER_TRUE),
        ),
        pair(
            "transfer-without-answer-refused",
            true,
            || pulls(&answer_full()),
            || pulls(ANSWER_TRUE),
        ),
        pair(
            "cost-grows-with-open-list",
            true,
            || walked("PUSH1 0x05 SLOAD"),
            || walked("PUSH1 0x03"),
        ),
        pair(
            "transfer-creates-value",
            true,
            || ledger("DUP1 PUSH1 0x02 MUL", SPENDS),
            || ledger("DUP1", SPENDS),
        ),
        pair(
            "transfer-delivers-less",
            true,
            || ledger("PUSH1 0x0a DUP2 DIV DUP2 SUB", SPENDS),
            || ledger("DUP1", SPENDS),
        ),
        pair(
            "transferfrom-ignores-allowance",
            true,
            || ledger("DUP1", ""),
            || ledger("DUP1", SPENDS),
        ),
        pair(
            "input-picks-storage-slot",
            true,
            || dispatcher(AIMED_WRITE),
            || {
                dispatcher(&format!(
                    "PUSH1 0x0a PUSH1 0x04 CALLDATALOAD LT PUSH2 @in JUMPI {REVERT} \
                     :in JUMPDEST {AIMED_WRITE}"
                ))
            },
        ),
        pair(
            "short-input-accepted",
            true,
            || dispatcher(STORE_WORD),
            || {
                dispatcher(&format!(
                    "PUSH1 0x23 CALLDATASIZE GT PUSH2 @long JUMPI {REVERT} \
                     :long JUMPDEST {STORE_WORD}"
                ))
            },
        ),
    ];
    all.into_iter().flatten().collect()
}

fn shown(case: &Case, code: &[u8]) -> bool {
    let wanted: Vec<&str> = case.rule.split('|').collect();
    report_of(code)
        .findings
        .iter()
        .any(|f| wanted.contains(&f.id.as_str()) && (f.confirmed || !case.confirmed))
}

#[test]
fn the_labelled_fixtures_score_every_rule_at_full_precision_and_recall() {
    let mut score: std::collections::BTreeMap<&str, [usize; 4]> = Default::default();
    let out_dir = std::env::var("EVMDEC_WRITE_FIXTURES").ok();
    let mut manifest = Vec::new();
    for (index, case) in cases().iter().enumerate() {
        let code = (case.build)();
        let found = shown(case, &code);
        let cell = match (case.flawed, found) {
            (true, true) => 0,
            (true, false) => 1,
            (false, true) => 2,
            (false, false) => 3,
        };
        score.entry(case.rule).or_default()[cell] += 1;
        if let Some(dir) = &out_dir {
            let name = format!(
                "{index:02}-{}.hex",
                if case.flawed { "flawed" } else { "sound" }
            );
            std::fs::write(format!("{dir}/{name}"), evmdec::hex::encode(&code)).unwrap();
            manifest.push(format!(
                "  {{\"file\": \"{name}\", \"rule\": \"{}\", \"flawed\": {}, \"confirmed\": {}}}",
                case.rule, case.flawed, case.confirmed
            ));
        }
    }
    if let Some(dir) = &out_dir {
        let text = format!("[\n{}\n]\n", manifest.join(",\n"));
        std::fs::write(format!("{dir}/manifest.json"), text).unwrap();
    }
    println!("{:<72} found missed false-alarm quiet", "rule");
    for (rule, [hit, missed, alarm, quiet]) in &score {
        println!("{rule:<72} {hit:>5} {missed:>6} {alarm:>11} {quiet:>5}");
        assert_eq!((*missed, *alarm), (0, 0), "{rule}");
    }
}

#[test]
fn padding_the_code_changes_no_labelled_result() {
    for case in cases() {
        let plain = shown(&case, &(case.build)());
        PADDED.with(|p| p.set(true));
        let padded = (case.build)();
        PADDED.with(|p| p.set(false));
        assert_eq!(
            shown(&case, &padded),
            plain,
            "{} ({}) changes when every jump destination is followed by a push and a pop",
            case.rule,
            if case.flawed { "flawed" } else { "sound" },
        );
    }
}

const SOUND_BY_A_GUARD: [&str; 6] = [
    "inflow-credits-nothing",
    "refused-transfer-treated-as-done|erc20-return-ignored|unchecked-token-pull",
    "input-picks-storage-slot",
    "short-input-accepted",
    "earlier-call-lowers-payout",
    "time-bound-set-by-anyone",
];

fn without_guard(case: &Case, index: Option<usize>) -> (Vec<u8>, usize) {
    GUARDS_SEEN.with(|g| g.set(0));
    GUARD_TO_DROP.with(|d| d.set(index));
    let code = (case.build)();
    GUARD_TO_DROP.with(|d| d.set(None));
    (code, GUARDS_SEEN.with(std::cell::Cell::get))
}

#[test]
fn removing_the_guard_that_makes_a_fixture_sound_is_noticed() {
    println!("{:<72} guards noticed", "rule");
    for case in cases().iter().filter(|c| !c.flawed) {
        let (_, guards) = without_guard(case, None);
        let noticed = (0..guards)
            .filter(|n| shown(case, &without_guard(case, Some(*n)).0))
            .count();
        println!("{:<72} {guards:>6} {noticed:>7}", case.rule);
        if SOUND_BY_A_GUARD.contains(&case.rule) {
            assert!(
                noticed >= 1,
                "{}: no removed guard makes the rule fire",
                case.rule
            );
        }
    }
}
