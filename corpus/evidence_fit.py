#!/usr/bin/env python3
import argparse, collections, json, math, os, random, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.abspath(__file__)) + "/.."
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import heldout_bench as hb

BIN = os.environ.get("BIN", os.path.join(ROOT, "target", "release", "evmdec"))
OUT = os.path.join(ROOT, "crates", "decompiler", "src", "weights.tsv")
SEV = hb.SEV
NAMES = {4: "critical", 3: "high", 2: "medium"}
FOLDS, SHUFFLES = 5, 4


def found(path):
    # The weights are fitted on what each rule said, before any of them is rated again.
    env = dict(os.environ, EVMDEC_AS_FOUND="1")
    try:
        out = subprocess.run([BIN, "analyze", "--json", path], capture_output=True, text=True, timeout=300, env=env)
        report = json.loads(out.stdout)
    except (subprocess.TimeoutExpired, ValueError):
        return {}
    worst = {}
    for f in report["findings"]:
        if SEV[f["severity"]] >= 2:
            worst[f["id"]] = max(worst.get(f["id"], 0), SEV[f["severity"]])
    return worst


def fit(flawed, sound):
    in_flawed, in_sound = collections.Counter(), collections.Counter()
    for worst, _ in flawed:
        in_flawed.update(worst.items())
    for worst, _ in sound:
        in_sound.update(worst.items())
    rate = lambda count, of: math.log((count + 0.5) / (len(of) + 1))
    seen = set(in_flawed) | set(in_sound)
    return {key: rate(in_flawed[key], flawed) - rate(in_sound[key], sound) for key in seen}


def rated(weights, worst, raise_at):
    raised = sum(weights.get(item, 0.0) for item in worst.items()) >= raise_at
    up = lambda rule, sev: raised and sev == 2 and weights.get((rule, sev), 0.0) > 0
    return {rule: 3 if up(rule, sev) else sev for rule, sev in worst.items()}


def judge(weights, flawed, sound, raise_at):
    hit = clean = 0
    for worst, wanted in flawed:
        now = rated(weights, worst, raise_at)
        hit += any(now.get(rule, 0) >= 3 for rule in wanted)
    for worst, _ in sound:
        clean += max(rated(weights, worst, raise_at).values(), default=0) < 3
    return hit, clean


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--write", action="store_true", help="write the fitted weights into the crate")
    a = ap.parse_args()
    dev = os.path.join(ROOT, "testdata", "incidents")
    manifest = json.load(open(os.path.join(dev, "manifest.json")))
    audited = os.path.join(ROOT, "testdata", "mainnet")
    paths = [os.path.join(dev, "flawed", n + ".hex") for n in manifest["flawed"]]
    paths += [os.path.join(dev, "sound", n + ".hex") for n in manifest["sound"]]
    paths += sorted(os.path.join(audited, n) for n in os.listdir(audited) if n.endswith(".hex"))
    with ThreadPoolExecutor(a.jobs) as pool:
        reports = dict(zip(paths, pool.map(found, paths)))
    flawed = []
    for name, entry in manifest["flawed"].items():
        wanted = {rule for fam in hb.families_of(entry["classes"]) for rule in hb.FAMILIES[fam]}
        flawed.append((reports[os.path.join(dev, "flawed", name + ".hex")], wanted))
    sound = [(reports[p], set()) for p in paths[len(flawed):]]

    # Each fold is scored with weights fitted on the other folds, so that a setting is
    # never chosen on the contracts that gave it its weights.
    grid = [99, 5, 4.5, 4, 3.5, 3, 2.5, 2]
    total = {g: [0, 0] for g in grid}
    for seed in range(SHUFFLES):
        rng = random.Random(seed)
        f, s = flawed[:], sound[:]
        rng.shuffle(f)
        rng.shuffle(s)
        for k in range(FOLDS):
            part = lambda rows, kept: [x for i, x in enumerate(rows) if (i % FOLDS != k) == kept]
            weights = fit(part(f, True), part(s, True))
            for g in grid:
                hit, clean = judge(weights, part(f, False), part(s, False), g)
                total[g][0] += hit
                total[g][1] += clean
    print(f"{len(flawed)} flawed, {len(sound)} sound, mean of {SHUFFLES} shuffles of {FOLDS} folds")
    print(f"{'raise at':>9}{'found':>8}{'sound clean':>13}")
    for g in grid:
        print(f"{g:>9}{total[g][0] / SHUFFLES:>8.1f}{total[g][1] / SHUFFLES:>13.1f}")

    weights = fit(flawed, sound)
    lines = [f"{rule}\t{NAMES[sev]}\t{round(1000 * w)}" for (rule, sev), w in sorted(weights.items())]
    if a.write:
        open(OUT, "w").write("\n".join(lines) + "\n")
        print("wrote", len(lines), "weights to", os.path.relpath(OUT, ROOT))


if __name__ == "__main__":
    main()
