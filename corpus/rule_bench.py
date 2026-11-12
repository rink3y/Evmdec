#!/usr/bin/env python3
import json, os, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIN = os.environ.get("BIN", os.path.join(ROOT, "target", "release", "evmdec"))
RULES = os.path.join(ROOT, "testdata", "rules")


def findings(path):
    out = subprocess.run([BIN, "analyze", "--json", path], capture_output=True, text=True, timeout=180)
    return json.loads(out.stdout)["findings"] if out.returncode == 0 and out.stdout.strip() else []


def main():
    cases = json.load(open(os.path.join(RULES, "manifest.json")))
    score = {}
    for case in cases:
        wanted = case["rule"].split("|")
        found = any(
            f["id"] in wanted and (f.get("confirmed") or not case["confirmed"])
            for f in findings(os.path.join(RULES, case["file"]))
        )
        row = score.setdefault(case["rule"], {"found": 0, "missed": 0, "alarm": 0, "quiet": 0})
        key = {(True, True): "found", (True, False): "missed", (False, True): "alarm", (False, False): "quiet"}
        row[key[(case["flawed"], found)]] += 1
    print(f"{'rule':<34}{'flawed':>7}{'sound':>6}{'precision':>10}{'recall':>8}")
    bad = 0
    for rule, r in sorted(score.items()):
        name = rule.split("|")[0]
        flagged = r["found"] + r["alarm"]
        precision = r["found"] / flagged if flagged else 1.0
        flawed = r["found"] + r["missed"]
        recall = r["found"] / flawed if flawed else 1.0
        bad += r["missed"] + r["alarm"]
        print(f"{name:<34}{flawed:>7}{r['alarm'] + r['quiet']:>6}{precision:>10.2f}{recall:>8.2f}")
    print(f"\n{len(cases)} labelled fixtures, {len(score)} rules, {bad} wrong")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
