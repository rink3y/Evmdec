#!/usr/bin/env python3
import argparse, collections, json, os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIN = os.environ.get("BIN", os.path.join(ROOT, "target", "release", "evmdec"))
SEV = {"info": 0, "low": 1, "medium": 2, "high": 3, "critical": 4}
SCORED = ("incidents", "heldout", "fresh")
PLAIN = ("mainnet", "vuln", "false_alarms")


def contracts():
    out = []
    data = os.path.join(ROOT, "testdata")
    for name in SCORED:
        for kind in ("flawed", "sound"):
            d = os.path.join(data, name, kind)
            if os.path.isdir(d):
                out += [(f"{name}/{kind}", n[:-4], os.path.join(d, n)) for n in sorted(os.listdir(d)) if n.endswith(".hex")]
    for name in PLAIN:
        d = os.path.join(data, name)
        out += [(name, n[:-4], os.path.join(d, n)) for n in sorted(os.listdir(d)) if n.endswith(".hex")]
    return out


def dump(a):
    # Each rule is compared as it rated its own finding, before the report is rated as a whole.
    env = dict(os.environ, EVMDEC_AS_FOUND="1")
    if a.static:
        env["EVMDEC_NO_CONFIRM"] = "1"

    def run(item):
        group, name, path = item
        try:
            out = subprocess.run([BIN, "analyze", "--json", path], capture_output=True, text=True, timeout=300, env=env)
            report = json.loads(out.stdout)
        except (subprocess.TimeoutExpired, ValueError):
            return f"{group}/{name}", None
        rows = sorted((f["id"], f["severity"], bool(f.get("confirmed"))) for f in report["findings"])
        return f"{group}/{name}", rows

    with ThreadPoolExecutor(a.jobs) as pool:
        found = dict(pool.map(run, contracts()))
    json.dump(found, open(a.out, "w"))
    failed = sorted(name for name, rows in found.items() if rows is None)
    print(len(found), "contracts,", len(failed), "not analysed")
    # A contract with no report is a crash or a hang, and neither is a finding that went away.
    for name in failed:
        print("  not analysed:", name)
    return 1 if failed else 0


def diff(a):
    before, after = json.load(open(a.before)), json.load(open(a.after))
    floor = SEV[a.min]
    gone, new = collections.defaultdict(collections.Counter), collections.defaultdict(collections.Counter)
    for name in before:
        if before[name] is None or after.get(name) is None:
            continue
        group = name.rsplit("/", 1)[0]
        was = collections.Counter((i, s) for i, s, _ in before[name] if SEV[s] >= floor)
        now = collections.Counter((i, s) for i, s, _ in after[name] if SEV[s] >= floor)
        for key in was - now:
            gone[key][group] += 1
        for key in now - was:
            new[key][group] += 1
    for sign, table in (("-", gone), ("+", new)):
        for (rule, sev), groups in sorted(table.items(), key=lambda kv: -sum(kv[1].values())):
            print(f"{sign} {rule:<40}{sev:<9}{sum(groups.values()):>4}  {dict(groups)}")
    # A finding that leaves a contract known to be flawed has to be explained. One that
    # appears on a contract with no known flaw has to be read.
    lost = sum(n for groups in gone.values() for g, n in groups.items() if g == "vuln")
    raised = sum(n for (_, s), groups in new.items() for g, n in groups.items() if g.endswith("sound") or g == "mainnet" if SEV[s] >= 3)
    print(f"\nleft the known-vulnerable corpus: {lost}   new at high on contracts with no known flaw: {raised}")


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="command", required=True)
    p = sub.add_parser("dump", help="write what every rule finds on every contract of every set")
    p.add_argument("out")
    p.add_argument("--static", action="store_true", help="skip the checks made by running the code")
    p.add_argument("--jobs", type=int, default=4)
    p = sub.add_parser("diff", help="say which findings two dumps differ in, by rule and by set")
    p.add_argument("before")
    p.add_argument("after")
    p.add_argument("--min", default="medium", choices=sorted(SEV, key=SEV.get))
    a = ap.parse_args()
    return {"dump": dump, "diff": diff}[a.command](a)


if __name__ == "__main__":
    sys.exit(main())
