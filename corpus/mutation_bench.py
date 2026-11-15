#!/usr/bin/env python3
import argparse, json, os, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIN = os.environ.get("BIN", os.path.join(ROOT, "target", "release", "evmdec"))
SEV = {"info": 0, "low": 1, "medium": 2, "high": 3, "critical": 4}
CALLER, CODESIZE, EQ, OR, AND, JUMPDEST = 0x33, 0x38, 0x14, 0x17, 0x16, 0x5B
ENDS = {0x00, 0x56, 0x57, 0xF3, 0xFD, 0xFE, 0xFF}
# How many words each opcode takes and leaves. An opcode not listed ends the tracking of
# the block, which only costs a candidate.
SHAPE = {0x01: (2, 1), 0x02: (2, 1), 0x03: (2, 1), 0x04: (2, 1), 0x10: (2, 1), 0x11: (2, 1),
         0x14: (2, 1), 0x15: (1, 1), 0x16: (2, 1), 0x17: (2, 1), 0x18: (2, 1), 0x19: (1, 1),
         0x1B: (2, 1), 0x1C: (2, 1), 0x0A: (2, 1), 0x30: (0, 1), 0x32: (0, 1), 0x33: (0, 1),
         0x34: (0, 1), 0x35: (1, 1), 0x36: (0, 1), 0x50: (1, 0), 0x51: (1, 1), 0x52: (2, 0),
         0x54: (1, 1), 0x5A: (0, 1), 0x20: (2, 1), 0x5F: (0, 1)}


def sites(code):
    out, stack, shared, pc = [], [], set(), 0
    while pc < len(code):
        op = code[pc]
        if op == JUMPDEST or op in ENDS:
            stack = []
        elif 0x60 <= op <= 0x7F:
            stack.append(None)
            pc += op - 0x5F
        elif 0x80 <= op <= 0x8F:
            n = op - 0x7F
            copied = stack[-n] if len(stack) >= n else None
            shared.add(copied)
            stack.append(copied)
        elif 0x90 <= op <= 0x9F:
            n = op - 0x8F
            while len(stack) <= n:
                stack.insert(0, None)
            stack[-1], stack[-1 - n] = stack[-1 - n], stack[-1]
        elif op in SHAPE:
            takes, leaves = SHAPE[op]
            args = [stack.pop() if stack else None for _ in range(takes)]
            origin = next((a for a in args if a is not None), None)
            if op == EQ and origin is not None:
                out.append((pc, origin))
            kept = pc if op == CALLER else origin if op == AND else None
            stack.extend([kept] * leaves)
        else:
            stack = []
        pc += 1
    # A caller that is read once and copied is used again after the test. Replacing
    # that read would change more than the test.
    return [(at, origin) for at, origin in out if origin not in shared]


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
        key = (f["id"], f.get("function") or "")
        found[key] = max(found.get(key, 0), SEV[f["severity"]])
    return found


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", default=os.path.join(ROOT, "testdata", "incidents", "sound"))
    ap.add_argument("--per-contract", type=int, default=4)
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("-v", action="store_true")
    a = ap.parse_args()
    work = tempfile.mkdtemp(prefix="mutants-")
    jobs = []
    for name in sorted(os.listdir(a.dir)):
        if not name.endswith(".hex"):
            continue
        text = open(os.path.join(a.dir, name)).read().strip()
        code = bytearray.fromhex(text[2:] if text.startswith("0x") else text)
        found = sites(code)
        # Evenly spread, so that a contract with many checks is not sampled from one end.
        step = max(1, len(found) // a.per_contract)
        for at, origin in found[::step][: a.per_contract]:
            # The test becomes one that always passes and no longer reads the caller.
            mutant = bytearray(code)
            mutant[at], mutant[origin] = OR, CODESIZE
            path = os.path.join(work, f"{name[:-4]}@{at:x}.hex")
            open(path, "w").write(mutant.hex())
            jobs.append((os.path.join(a.dir, name), path, at))
    originals = sorted({j[0] for j in jobs})
    with ThreadPoolExecutor(a.jobs) as pool:
        base = dict(zip(originals, pool.map(analyze, originals)))
        reports = list(pool.map(analyze, [j[1] for j in jobs]))
    rows = {"opened": 0, "high": 0, "medium": 0, "silent": 0, "no effect": 0}
    silent = []
    for (orig, path, at), rep in zip(jobs, reports):
        before = base[orig]
        if rep is None or before is None:
            continue
        gated = set(before["privileged_functions"]) - set(rep["privileged_functions"])
        was, now = worst(before), worst(rep)
        new = {k: s for k, s in now.items() if s > was.get(k, -1)}
        top = max(new.values(), default=-1)
        if not gated and top < SEV["medium"]:
            rows["no effect"] += 1
            continue
        rows["opened"] += 1
        if top >= SEV["high"]:
            rows["high"] += 1
        elif top >= SEV["medium"]:
            rows["medium"] += 1
        else:
            rows["silent"] += 1
            silent.append((os.path.basename(path), sorted(gated)))
        if a.v:
            names = sorted(k[0] for k, s in new.items() if s >= SEV["medium"])
            print(f"{os.path.basename(path):<40} opened={len(gated)} new={names}")
    n = rows["opened"] or 1
    print(f"\nmutants made: {len(jobs)}   with no visible effect: {rows['no effect']}")
    print(f"mutants that open something: {rows['opened']}")
    print(f"  a new finding at high or above: {rows['high']}/{rows['opened']} = {100 * rows['high'] / n:.1f}%")
    print(f"  a new finding at medium only:   {rows['medium']}/{rows['opened']}")
    print(f"  nothing new at medium or above: {rows['silent']}/{rows['opened']}")
    if a.v:
        for name, gated in silent:
            print(f"   silent {name}: {gated[:4]}")


if __name__ == "__main__":
    main()
