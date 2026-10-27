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

/// solc < 0.5.9 metadata trailer: `{"bzzr0": <32 bytes>}` followed by its 2-byte length.
fn bzzr0_trailer() -> Vec<u8> {
    let mut t = vec![0xa1, 0x65, b'b', b'z', b'z', b'r', b'0', 0x58, 0x20];
    t.extend(std::iter::repeat(0x11).take(32));
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
    let c = decompile(&code, &Options::default());
    assert!(c.source.contains("assert("), "the helper's overflow check must survive inlining:\n{}", c.source);
    let r = analyze(&c);
    assert!(r.findings.iter().any(|f| f.id == "legacy-compiler"), "bzzr0-only metadata implies solc < 0.5.9");
    assert!(!r.findings.iter().any(|f| f.id == "unchecked-arithmetic"), "guarded addition must not be flagged:\n{}", c.source);

    let mut code = dispatcher(&unchecked);
    code.extend(bzzr0_trailer());
    let c = decompile(&code, &Options::default());
    let r = analyze(&c);
    assert!(r.findings.iter().any(|f| f.id == "unchecked-arithmetic"), "unguarded addition must be flagged:\n{}", c.source);
}
