#!/usr/bin/env python3
import argparse, json, os, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIN = os.environ.get("BIN", os.path.join(ROOT, "target", "release", "evmdec"))
SEV = {"info": 0, "low": 1, "medium": 2, "high": 3, "critical": 4}
NOISE = {"compiler-bug", "revert-strings", "unknown-selectors", "legacy-compiler", "no-metadata", "coverage", "unresolved-jump", "proxy", "contract-creation"}

def analyze(path):
    try:
        out = subprocess.run([BIN, "analyze", "--json", path], capture_output=True, text=True, timeout=180)
    except subprocess.TimeoutExpired:
        return None, "timeout"
    if out.returncode != 0 or not out.stdout.strip():
        return None, "rc=%d %s" % (out.returncode, out.stderr.strip().splitlines()[-1:] )
    return json.loads(out.stdout), None

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-v", action="store_true")
    a = ap.parse_args()
    manifest = json.load(open(os.path.join(ROOT, "testdata", "vuln", "manifest.json")))["contracts"]
    print(f"{'contract':<20}{'year':>5} {'result':<8} {'score':>5}  expected -> found")
    hits = total = 0
    undetectable = []
    labelled, caught, alerts = {}, {}, {}
    for name, m in manifest.items():
        path = os.path.join(ROOT, "testdata", "vuln", name + ".hex")
        if not os.path.exists(path):
            print(f"{name:<20}{m['year']:>5} MISSING FILE"); continue
        rep, err = analyze(path)
        if rep is None:
            print(f"{name:<20}{m['year']:>5} ERROR    {err}"); 
            if m.get("detectable", True): total += 1
            continue
        found = {}
        for f in rep["findings"]:
            found[f["id"]] = max(found.get(f["id"], 0), SEV[f["severity"]])
        need = SEV[m["min_severity"]]
        hit = any(found.get(e, -1) >= need for e in m["expected"])
        if not m.get("detectable", True):
            undetectable.append(name)
            res = "n/a"
        else:
            total += 1
            hits += hit
            res = "HIT" if hit else "MISS"
            for e in m["expected"]:
                labelled[e] = labelled.get(e, 0) + 1
                caught[e] = caught.get(e, 0) + (found.get(e, -1) >= need)
        got = " ".join(f"{k}:{'ilmhc'[v]}" for k, v in sorted(found.items()) if k not in NOISE)
        print(f"{name:<20}{m['year']:>5} {res:<8} {rep['risk_score']:>5}  {','.join(m['expected']) or '-'} -> {got}")
        if a.v:
            for f in rep["findings"]:
                if f["id"] not in NOISE:
                    print(f"      [{f['severity']}] {f['id']} {f.get('function','')}")
    print(f"\nrecall: {hits}/{total} = {100*hits/max(1,total):.1f}%   (not counted, outside pattern rules: {', '.join(undetectable) or 'none'})")
    good = sorted(f for f in os.listdir(os.path.join(ROOT, "testdata", "mainnet")) if f.endswith(".hex"))
    print(f"\n{'audited contract':<22}{'score':>5}  high/critical findings")
    hc_total = 0
    for f in good:
        rep, err = analyze(os.path.join(ROOT, "testdata", "mainnet", f))
        if rep is None:
            print(f"{f[:-4]:<22} ERROR {err}"); continue
        hc = [x for x in rep["findings"] if SEV[x["severity"]] >= 3]
        hc_total += len(hc)
        for x in rep["findings"]:
            if SEV[x["severity"]] >= 2 and x["id"] not in NOISE:
                alerts[x["id"]] = alerts.get(x["id"], 0) + 1
        print(f"{f[:-4]:<22}{rep['risk_score']:>5}  {len(hc):>2}  {' '.join(sorted(set(x['id'] for x in hc)))}")
    print(f"\nhigh/critical findings on the audited corpus: {hc_total} across {len(good)} contracts")
    print(f"\n{'rule':<34}{'labelled':>9}{'caught':>7}{'recall':>8}  medium or higher on audited code")
    for rule in sorted(set(labelled) | set(alerts)):
        n, c = labelled.get(rule, 0), caught.get(rule, 0)
        recall = f"{c / n:.2f}" if n else "-"
        print(f"{rule:<34}{n:>9}{c:>7}{recall:>8}  {alerts.get(rule, 0)}")

if __name__ == "__main__":
    main()
