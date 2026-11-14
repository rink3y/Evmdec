#!/usr/bin/env python3
import argparse, collections, glob, hashlib, html, json, os, random, re, shutil, sys, time, urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SITE = "https://crypto.training/hacks/"
AGENT = "research-client"
CHAINS = {
    "Ethereum": ("mainnet", "ethereum-rpc"),
    "BNB Chain": ("bsc", "bsc-rpc"),
    "Polygon": ("polygon", "polygon-bor-rpc"),
    "Base": ("base", "base-rpc"),
    "Arbitrum": ("arbitrum", "arbitrum-one-rpc"),
    "Avalanche": ("avalanche", "avalanche-c-chain-rpc"),
    "Optimism": ("optimism", "optimism-rpc"),
    "Gnosis": ("gnosis", "gnosis-rpc"),
    "Linea": ("linea", "linea-rpc"),
    "Scroll": ("scroll", "scroll-rpc"),
    "Mantle": ("mantle", "mantle-rpc"),
    "Sonic": ("sonic", "sonic-rpc"),
    "Celo": ("celo", "celo-rpc"),
    "Cronos": ("cronos", "cronos-evm-rpc"),
}
HOSTS = {chain: host for chain, host in CHAINS.values()}
KEYS = [
    "Loss", "Vulnerable contract", "Attacker EOA", "Attack contract", "Attack tx", "Chain / block / date",
    "Compiler", "Bug class", "Victim", "Attacker", "Root cause",
]
IMPLEMENTATION_SLOT = "0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc"
FORWARDER_MAX = 3000
SMALLEST = 700
# A leaked key or an owner who takes the funds leaves nothing in the code to find.
NOT_IN_CODE = {"vuln/access-control/secret-exposure", "vuln/access-control/centralization"}


def get(url):
    req = urllib.request.Request(url, headers={"user-agent": AGENT})
    with urllib.request.urlopen(req, timeout=60) as r:
        return r.read().decode("utf-8", "replace")


def rpc(host, method, params):
    body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}).encode()
    headers = {"content-type": "application/json", "user-agent": AGENT}
    req = urllib.request.Request(f"https://{host}.publicnode.com", data=body, headers=headers)
    for attempt in range(4):
        try:
            with urllib.request.urlopen(req, timeout=60) as r:
                return json.load(r).get("result")
        except Exception:
            time.sleep(2 + 3 * attempt)
    return None


def digest(path):
    return hashlib.sha256(open(path).read().strip().lower().encode()).hexdigest()


def forwarder(code):
    return len(code) < FORWARDER_MAX and b"\xf4" in code


def pages(a):
    os.makedirs(a.work + "/pages", exist_ok=True)
    slugs = sorted(set(re.findall(r'href="/hacks/(\d{4}-\d{2}-[^"/]+)/"', get(SITE))))
    for slug in slugs[a.offset :: a.step]:
        out = f"{a.work}/pages/{slug}.html"
        if os.path.exists(out) and os.path.getsize(out) > 5000:
            continue
        try:
            open(out, "w").write(get(SITE + slug + "/"))
        except Exception as e:
            print("failed", slug, e, file=sys.stderr)
        time.sleep(1.2)
    print("pages", len(os.listdir(a.work + "/pages")), "of", len(slugs), "dated incidents")


def record(path):
    text = open(path, encoding="utf-8", errors="replace").read()
    main = re.search(r"<main.*?</main>", text, re.S)
    body = re.sub(r"<(script|style)[^>]*>.*?</\1>", "", main.group(0) if main else text, flags=re.S)
    lines = [l.strip() for l in html.unescape(re.sub(r"<[^>]+>", "\n", body)).split("\n") if l.strip()]
    r = {"slug": os.path.basename(path)[:-5], "chain": "", "classes": [], "candidates": []}
    for i, line in enumerate(lines[:60]):
        if line == "Chain" and i + 1 < len(lines):
            r["chain"] = lines[i + 1]
            break
    for i, line in enumerate(lines):
        if line.startswith("Vulnerability classes"):
            r["classes"] = re.findall(r"vuln/[a-z0-9/-]+", " ".join(lines[i : i + 3]))
            break
    if "Key info" not in lines:
        return r
    info = lines[lines.index("Key info") :][:140]
    if "Vulnerable contract" not in info:
        return r
    start = info.index("Vulnerable contract")
    end = next((i for i in range(start + 1, len(info)) if info[i] in KEYS), len(info))
    r["candidates"] = [l.lower() for l in info[start + 1 : end] if re.fullmatch(r"0x[0-9a-fA-F]{40}", l)]
    return r


# One set never shares a contract with another, or with what the rules were built on.
def used_elsewhere(own):
    known = set()
    address = re.compile(r"0x[0-9a-fA-F]{40}")
    files = glob.glob(ROOT + "/corpus/*.txt") + glob.glob(ROOT + "/testdata/**/*", recursive=True)
    for f in files:
        if f"/{own}/" in f or not os.path.isfile(f):
            continue
        known |= {x.lower() for x in address.findall(os.path.basename(f))}
        if not f.endswith(".hex"):
            known |= {x.lower() for x in address.findall(open(f, errors="replace").read())}
    return known


def flawed(a):
    out = a.work + "/flawed"
    os.makedirs(out, exist_ok=True)
    records = [record(f) for f in sorted(glob.glob(a.work + "/pages/*.html"))]
    json.dump(records, open(a.work + "/records.json", "w"), indent=1)
    known, kept, why = used_elsewhere(a.set), [], collections.Counter()
    listed = set()
    for other in glob.glob(ROOT + "/testdata/*/manifest.json"):
        if f"/{a.set}/" not in other:
            listed |= set(json.load(open(other)).get("flawed", {}))
    for r in records:
        if r["slug"] in listed:
            why["incident already in another set"] += 1
        elif not r["candidates"]:
            why["no contract listed"] += 1
        elif r["chain"] not in CHAINS:
            why["chain not reachable: " + r["chain"]] += 1
        elif any(c in known for c in r["candidates"]):
            why["already used in development"] += 1
        else:
            chain, host = CHAINS[r["chain"]]
            reason = "no code today"
            # The page lists the flawed contract first and what it relies on after it.
            for address in r["candidates"][:4]:
                code = rpc(host, "eth_getCode", [address, "latest"])
                time.sleep(0.15)
                raw = bytes.fromhex((code or "0x")[2:])
                if raw and forwarder(raw):
                    reason = "only a forwarder listed"
                elif raw:
                    open(f"{out}/{r['slug']}.hex", "w").write(code + "\n")
                    kept.append({"name": r["slug"], "chain": chain, "address": address, "classes": r["classes"]})
                    break
            else:
                why[reason] += 1
    json.dump(kept, open(out + "/kept.json", "w"), indent=1)
    print("flawed kept", len(kept), "of", len(records), dict(why))


def called(host, numbers):
    seen = collections.Counter()
    for n in numbers:
        block = rpc(host, "eth_getBlockByNumber", [hex(n), True]) or {}
        calls = {t.get("to") for t in block.get("transactions", []) if t.get("to") and t.get("input", "0x") != "0x"}
        seen.update(x.lower() for x in calls)
        time.sleep(0.1)
    return seen


def sound(a):
    out = a.work + "/sound"
    os.makedirs(out, exist_ok=True)
    host = HOSTS[a.chain]
    rng = random.Random(a.seed)
    latest = int(rpc(host, "eth_blockNumber", []), 16)
    old = called(host, [rng.randrange(a.old_from, a.old_to) for _ in range(a.blocks)])
    new = called(host, [latest - rng.randrange(0, 200000) for _ in range(a.blocks)])
    ranked = sorted(((min(old[x], new[x]), x) for x in old if x in new), reverse=True)
    exclude = used_elsewhere(a.set)
    for r in json.load(open(a.work + "/records.json")):
        exclude |= set(r["candidates"])
    kept, seen, why = [], set(), collections.Counter()
    for uses, address in ranked:
        if len(kept) >= a.limit or uses < 2:
            break
        if address in exclude:
            why["used in development or listed in an incident"] += 1
            continue
        code = rpc(host, "eth_getCode", [address, "latest"])
        raw, behind = bytes.fromhex((code or "0x")[2:]), None
        if raw and forwarder(raw):
            slot = rpc(host, "eth_getStorageAt", [address, IMPLEMENTATION_SLOT, "latest"]) or "0x0"
            behind = "0x" + slot[-40:]
            if int(slot, 16) == 0 or behind in exclude:
                why["forwarder with no usable implementation"] += 1
                continue
            code = rpc(host, "eth_getCode", [behind, "latest"])
            raw = bytes.fromhex((code or "0x")[2:])
        if len(raw) < SMALLEST or hashlib.sha256(raw).hexdigest() in seen:
            why["no code, too small, or same code as another"] += 1
            continue
        seen.add(hashlib.sha256(raw).hexdigest())
        name = f"{a.chain}_{address[2:10]}"
        open(f"{out}/{name}.hex", "w").write(code + "\n")
        kept.append({"name": name, "chain": a.chain, "address": address, "implementation": behind})
    json.dump(kept, open(f"{out}/kept_{a.chain}.json", "w"), indent=1)
    print(a.chain, "sound kept", len(kept), dict(why))


def assemble(a):
    held = os.path.join(ROOT, "testdata", a.set)
    for sub in ("flawed", "sound"):
        shutil.rmtree(os.path.join(held, sub), ignore_errors=True)
        os.makedirs(os.path.join(held, sub))
    kept = json.load(open(a.work + "/flawed/kept.json"))
    count = collections.Counter(digest(f"{a.work}/flawed/{e['name']}.hex") for e in kept)
    flawed_set, dropped = {}, collections.Counter()
    for e in kept:
        path = f"{a.work}/flawed/{e['name']}.hex"
        # Code that several incidents list first is a router or a pool they share, not the flaw.
        if count[digest(path)] > 1:
            dropped["code shared by several incidents"] += 1
        elif not e["classes"]:
            dropped["no class given"] += 1
        elif all(c in NOT_IN_CODE for c in e["classes"]):
            dropped["flaw is not in the code"] += 1
        else:
            shutil.copy(path, f"{held}/flawed/{e['name']}.hex")
            flawed_set[e["name"]] = {
                "address": e["address"],
                "chain": e["chain"],
                "year": int(e["name"][:4]),
                "classes": e["classes"],
            }
    taken = {digest(f"{held}/flawed/{n}.hex") for n in flawed_set}
    sound_set = {}
    for f in sorted(glob.glob(a.work + "/sound/kept_*.json")):
        for e in json.load(open(f)):
            path = f"{a.work}/sound/{e['name']}.hex"
            if digest(path) in taken:
                dropped["sound code equal to a flawed one"] += 1
                continue
            shutil.copy(path, f"{held}/sound/{e['name']}.hex")
            row = {"address": e["address"], "chain": e["chain"]}
            if e.get("implementation"):
                row["implementation"] = e["implementation"]
            sound_set[e["name"]] = row
    json.dump({"flawed": flawed_set, "sound": sound_set}, open(held + "/manifest.json", "w"), indent=2)
    print("flawed", len(flawed_set), "sound", len(sound_set), dict(dropped))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--work", required=True, help="directory for fetched pages and code, outside the repository")
    ap.add_argument("--set", default="heldout", help="the directory under testdata this set is written to")
    sub = ap.add_subparsers(dest="command", required=True)
    p = sub.add_parser("pages", help="fetch every STEP-th dated incident page, starting at OFFSET")
    p.add_argument("--step", type=int, default=3)
    p.add_argument("--offset", type=int, default=0)
    sub.add_parser("flawed", help="read the pages and fetch the code of each flawed contract")
    p = sub.add_parser("sound", help="fetch contracts called often in old blocks and still called often now")
    p.add_argument("--chain", default="mainnet", choices=sorted(HOSTS))
    p.add_argument("--old-from", type=int, default=15_500_000)
    p.add_argument("--old-to", type=int, default=17_000_000)
    p.add_argument("--blocks", type=int, default=300)
    p.add_argument("--limit", type=int, default=90)
    p.add_argument("--seed", type=int, default=20261114)
    sub.add_parser("assemble", help="write the set under testdata from what was fetched")
    a = ap.parse_args()
    {"pages": pages, "flawed": flawed, "sound": sound, "assemble": assemble}[a.command](a)


if __name__ == "__main__":
    main()
