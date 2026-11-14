#!/usr/bin/env python3
import argparse, json, os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIN = os.environ.get("BIN", os.path.join(ROOT, "target", "release", "evmdec"))
HELD = os.path.join(ROOT, "testdata", "heldout")
SEV = {"info": 0, "low": 1, "medium": 2, "high": 3, "critical": 4}
HIGH = SEV["high"]

# This table was written before any contract of the set was analysed. Changing it to turn
# a miss into a hit defeats the set. A new rule goes into the family it belongs to and
# nowhere else.
FAMILIES = {
    "access": [
        "unprotected-owner-write", "unprotected-initializer", "unprotected-upgrade",
        "unprotected-ether-withdrawal", "arbitrary-call", "arbitrary-delegatecall",
        "arbitrary-transferfrom", "delegatecall-user-target", "delegatecall-dynamic-target",
        "dynamic-call", "inconsistent-access-control", "gate-on-open-slot", "gate-never-set",
        "stored-input-call-target", "attack-chain", "tx-origin", "selfdestruct",
        "unbound-address-made-privileged", "unbound-account-passed-on",
        "approval-to-open-spender", "third-party-balance-debit", "unprivileged-balance-credit",
        "trusted-callee-loop", "silent-auth-failure", "storage-collision",
    ],
    "reentry": [
        "reentrancy", "reentered-call-pays-again", "control-handed-out-mid-update",
        "total-open-at-call", "vyper-reentrancy-lock-bug", "lock-left-set",
    ],
    "price": [
        "spot-balance-price", "oracle-unchecked", "no-slippage-bound",
        "pair-sync-after-state-change", "untrusted-return-data", "reverse-quote-rounding",
    ],
    "accounting": [
        "two-calls-return-more", "inflow-credits-nothing", "payout-grows-with-other-payment",
        "earlier-call-lowers-payout", "rounding-favours-caller", "surplus-open-to-any-account",
        "payment-taken-by-other-account", "ledger-credits-more-than-received",
        "ledger-total-mismatch", "entries-total-out-of-step", "inconsistent-liability-accounting",
        "unbalanced-ledger-move", "stale-ledger-write", "changed-copy-dropped",
        "division-before-multiplication", "fee-on-transfer", "transfer-creates-value",
        "transfer-delivers-less", "transfer-touches-third-entry", "transfer-changes-supply",
        "transferfrom-ignores-allowance", "allowance-not-spent", "reported-balance-differs",
        "unbounded-payout-parameter", "unchecked-token-pull", "erc20-return-ignored",
        "refused-transfer-treated-as-done", "msg-value-in-loop", "msg-value-multicall",
    ],
    "arithmetic": [
        "unchecked-arithmetic", "unchecked-block-arithmetic", "unchecked-downcast",
        "narrow-counter", "signed-unsigned-confusion", "rounding-favours-caller",
        "division-before-multiplication", "reverse-quote-rounding",
    ],
    "signature": [
        "ecrecover-zero", "signature-malleability", "signature-replay-domain",
        "signature-replay-nonce", "signed-message-accepted-twice",
        "signed-call-leaves-word-unsigned",
    ],
    "randomness": ["weak-randomness"],
    "input": [
        "input-picks-storage-slot", "input-picks-memory-offset", "short-input-accepted",
        "arbitrary-call", "arbitrary-transferfrom", "untrusted-return-data",
        "unbounded-payout-parameter", "address-from-arithmetic", "hash-as-number",
    ],
    "time": ["clock-units-mixed", "time-bound-set-by-anyone", "time-window-never-opens"],
    "blocking": [
        "blocking-payout-loop", "fixed-payee-can-block", "one-refusal-blocks-all",
        "cost-grows-with-open-list", "storage-bounded-loop", "call-in-loop", "locked-ether",
    ],
}

# The longest prefix that matches a class decides its families.
CLASSES = [
    ("vuln/access-control/", ["access"]),
    ("vuln/auth/signature", ["signature"]),
    ("vuln/auth/", ["access", "signature"]),
    ("vuln/reentrancy/", ["reentry"]),
    ("vuln/oracle/", ["price"]),
    ("vuln/defi/price", ["price"]),
    ("vuln/defi/slippage", ["price"]),
    ("vuln/defi/flash-loan", ["price", "accounting"]),
    ("vuln/defi/", ["accounting"]),
    ("vuln/logic/price", ["price", "accounting"]),
    ("vuln/logic/missing-check", ["access", "input", "accounting"]),
    ("vuln/logic/missing-validation", ["access", "input", "accounting"]),
    ("vuln/logic/wrong-condition", ["access", "accounting"]),
    ("vuln/logic/", ["accounting"]),
    ("vuln/arithmetic/", ["arithmetic", "accounting"]),
    ("vuln/input-validation/", ["input", "access"]),
    ("vuln/dependency/", ["access", "reentry"]),
    ("vuln/governance/", ["access", "price", "accounting"]),
    ("vuln/bridge/", ["access", "signature", "input"]),
    ("vuln/randomness/", ["randomness"]),
    ("vuln/dos/", ["blocking"]),
    ("vuln/time/", ["time"]),
    ("vuln/data/", ["input", "access"]),
    ("vuln/accounting/", ["accounting"]),
    ("vuln/proxy/", ["access"]),
]


def families_of(classes):
    longest_first = sorted(CLASSES, key=lambda entry: -len(entry[0]))
    out = set()
    for c in classes:
        out.update(next((fams for prefix, fams in longest_first if (c + "/").startswith(prefix)), []))
    return out


def analyze(path):
    try:
        out = subprocess.run([BIN, "analyze", "--json", path], capture_output=True, text=True, timeout=300)
    except subprocess.TimeoutExpired:
        return None
    if out.returncode != 0 or not out.stdout.strip():
        return None
    return json.loads(out.stdout)


def worst(rep):
    found = {}
    for f in rep["findings"]:
        found[f["id"]] = max(found.get(f["id"], 0), SEV[f["severity"]])
    return found


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-v", action="store_true")
    ap.add_argument("--jobs", type=int, default=3)
    a = ap.parse_args()
    manifest = json.load(open(os.path.join(HELD, "manifest.json")))
    flawed, sound = manifest["flawed"], manifest["sound"]
    paths = [os.path.join(HELD, "flawed", n + ".hex") for n in flawed]
    paths += [os.path.join(HELD, "sound", n + ".hex") for n in sound]
    with ThreadPoolExecutor(a.jobs) as pool:
        reports = dict(zip(paths, pool.map(analyze, paths)))

    strict = named = loose = failed = 0
    by_family = {}
    for name, m in flawed.items():
        rep = reports[os.path.join(HELD, "flawed", name + ".hex")]
        if rep is None:
            failed += 1
            print(f"{name:<34} ERROR")
            continue
        found = worst(rep)
        fams = families_of(m["classes"])
        wanted = {rule for fam in fams for rule in FAMILIES[fam]}
        hit = any(found.get(rule, -1) >= HIGH for rule in wanted)
        seen = any(found.get(rule, -1) >= SEV["medium"] for rule in wanted)
        any_high = any(sev >= HIGH for sev in found.values())
        strict += hit
        named += seen
        loose += any_high
        for fam in fams or {"unmapped"}:
            cell = by_family.setdefault(fam, [0, 0])
            cell[0] += 1
            cell[1] += hit
        if a.v:
            high = " ".join(sorted(k for k, v in found.items() if v >= HIGH))
            print(f"{name:<34} {'HIT ' if hit else 'MISS'} {','.join(sorted(fams)) or '-':<28} {high}")
    total = len(flawed)
    print(f"\nflawed contracts: {total}  (not analysed: {failed})")
    print(f"  right kind of finding at high or above: {strict}/{total} = {100 * strict / max(1, total):.1f}%")
    print(f"  right kind of finding at medium or above: {named}/{total} = {100 * named / max(1, total):.1f}%")
    print(f"  any finding at high or above: {loose}/{total} = {100 * loose / max(1, total):.1f}%")
    print(f"\n{'family':<12}{'labelled':>9}{'hit':>5}{'recall':>8}")
    for fam, (n, h) in sorted(by_family.items()):
        print(f"{fam:<12}{n:>9}{h:>5}{h / n:>8.2f}")

    clean = alarms = failed = 0
    by_rule = {}
    for name in sound:
        rep = reports[os.path.join(HELD, "sound", name + ".hex")]
        if rep is None:
            failed += 1
            print(f"{name:<34} ERROR")
            continue
        high = [f["id"] for f in rep["findings"] if SEV[f["severity"]] >= HIGH]
        clean += not high
        alarms += len(high)
        for rule in set(high):
            by_rule[rule] = by_rule.get(rule, 0) + 1
        if a.v and high:
            print(f"{name:<34} {len(high):>2} {' '.join(sorted(set(high)))}")
    total = len(sound)
    print(f"\ncontracts with no known flaw: {total}  (not analysed: {failed})")
    print(f"  none at high or above: {clean}/{total} = {100 * clean / max(1, total):.1f}%")
    print(f"  findings at high or above: {alarms}")
    print(f"\n{'rule':<36}contracts with no known flaw it marks high")
    for rule, n in sorted(by_rule.items(), key=lambda x: -x[1]):
        print(f"{rule:<36}{n}")


if __name__ == "__main__":
    sys.exit(main())
