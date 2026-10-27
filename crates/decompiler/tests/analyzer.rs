//! The analyzer on hand-assembled contracts with known defects.

use evmdec::analyze::{analyze, Severity};
use evmdec::decompile::{decompile, Options};

/// Tiny assembler: mnemonics with immediates, e.g. "PUSH1 0x80". Labels: `:name` defines,
/// `PUSH2 @name` references (patched to 2 bytes).
fn asm(src: &str) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    let mut labels = std::collections::HashMap::new();
    let mut fixups: Vec<(usize, String)> = Vec::new();
    let opcodes: std::collections::HashMap<&str, u8> = (0u8..=255).filter_map(|o| evmdec::opcode::info(o).map(|i| (i.name, o))).collect();
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
        out.push(*opcodes.get(tok).unwrap_or_else(|| panic!("unknown mnemonic {tok}")));
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
    let c = decompile(&vulnerable, &Options::default());
    let r = analyze(&c);
    let f = r.findings.iter().find(|f| f.id == "reentrancy").expect("reentrancy finding");
    assert!(matches!(f.severity, Severity::High | Severity::Medium), "{:?}", f.severity);
    // Checks-effects-interactions: sstore before the call.
    let safe = dispatcher("CALLER SLOAD PUSH1 0x00 CALLER SSTORE DUP1 PUSH1 0x00 DUP1 DUP1 DUP5 CALLER GAS CALL POP POP STOP");
    let c = decompile(&safe, &Options::default());
    let r = analyze(&c);
    assert!(!r.findings.iter().any(|f| f.id == "reentrancy"), "false reentrancy on CEI code");
    assert!(r.findings.iter().any(|f| f.id == "unchecked-call"), "ignored success flag should be reported");
}

#[test]
fn unprotected_selfdestruct_and_tx_origin() {
    let code = dispatcher("CALLER SELFDESTRUCT");
    let r = analyze(&decompile(&code, &Options::default()));
    let f = r.findings.iter().find(|f| f.id == "selfdestruct").unwrap();
    assert_eq!(f.severity, Severity::Critical);
    // Guarded by owner == msg.sender (slot 0): severity drops.
    let guarded = dispatcher("PUSH1 0x00 SLOAD CALLER EQ PUSH2 @ok JUMPI PUSH1 0x00 DUP1 REVERT :ok JUMPDEST CALLER SELFDESTRUCT");
    let r = analyze(&decompile(&guarded, &Options::default()));
    let f = r.findings.iter().find(|f| f.id == "selfdestruct").unwrap();
    assert_eq!(f.severity, Severity::Medium);
    assert!(r.privileged_functions.len() == 1);
    // tx.origin authorization
    let origin = dispatcher("PUSH1 0x00 SLOAD ORIGIN EQ PUSH2 @ok JUMPI PUSH1 0x00 DUP1 REVERT :ok JUMPDEST PUSH1 0x01 PUSH1 0x05 SSTORE STOP");
    let r = analyze(&decompile(&origin, &Options::default()));
    assert!(r.findings.iter().any(|f| f.id == "tx-origin"));
}

#[test]
fn arbitrary_delegatecall_and_owner_write() {
    // delegatecall to calldata[4]
    let dc = dispatcher("PUSH1 0x00 DUP1 DUP1 DUP1 PUSH1 0x04 CALLDATALOAD GAS DELEGATECALL POP STOP");
    let r = analyze(&decompile(&dc, &Options::default()));
    let f = r.findings.iter().find(|f| f.id == "arbitrary-delegatecall").unwrap();
    assert_eq!(f.severity, Severity::Critical);
    // Two functions: 0xaaaaaaaa writes slot 0 from calldata without a check; 0xbbbbbbbb is gated by slot 0 == caller.
    let two = asm("PUSH1 0x80 PUSH1 0x40 MSTORE PUSH1 0x00 CALLDATALOAD PUSH1 0xe0 SHR DUP1 PUSH4 0xaaaaaaaa EQ PUSH2 @a JUMPI PUSH4 0xbbbbbbbb EQ PUSH2 @b JUMPI PUSH1 0x00 DUP1 REVERT :a JUMPDEST PUSH1 0x04 CALLDATALOAD PUSH1 0x00 SSTORE STOP :b JUMPDEST PUSH1 0x00 SLOAD CALLER EQ PUSH2 @ok JUMPI PUSH1 0x00 DUP1 REVERT :ok JUMPDEST PUSH1 0x01 PUSH1 0x07 SSTORE STOP");
    let r = analyze(&decompile(&two, &Options::default()));
    assert!(r.findings.iter().any(|f| f.id == "unprotected-owner-write" && f.severity == Severity::Critical), "{:?}", r.findings.iter().map(|f| &f.id).collect::<Vec<_>>());
}

#[test]
fn report_renders() {
    let code = dispatcher("CALLER SELFDESTRUCT");
    let c = decompile(&code, &Options::default());
    let r = analyze(&c);
    let md = evmdec::analyze::render_markdown(&c, &r, "test");
    assert!(md.contains("[CRITICAL]"));
    assert!(serde_json::to_string(&r).is_ok());
}
