#!/usr/bin/env python3
import argparse, json, os, sys, random

def rpc(url, method, params):
    import subprocess
    body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params})
    out = subprocess.run(["curl", "-sS", "--max-time", "40", "-X", "POST", "-H", "content-type: application/json", "--data", body, url], capture_output=True, text=True)
    if out.returncode != 0: raise RuntimeError(out.stderr.strip())
    j = json.loads(out.stdout)
    if "error" in j: raise RuntimeError(j["error"])
    return j["result"]

CHAINS = {
    "mainnet": "https://ethereum-rpc.publicnode.com",
    "base": "https://base-rpc.publicnode.com",
    "bsc": "https://bsc-rpc.publicnode.com",
    "arbitrum": "https://arbitrum-one-rpc.publicnode.com",
    "polygon": "https://polygon-bor-rpc.publicnode.com",
}

def fetch_listed(ids, out, default_rpc):
    got = 0
    for line in open(ids):
        words = line.split()
        if not words: continue
        chain, address = (words[0], words[1]) if len(words) > 1 else ("mainnet", words[0])
        url = CHAINS.get(chain, default_rpc) if len(words) > 1 else default_rpc
        name = address.lower() if len(words) == 1 else f"{chain}_{address.lower()}"
        path = os.path.join(out, name + ".hex")
        if os.path.exists(path): continue
        try:
            code = rpc(url, "eth_getCode", [address, "latest"])
        except Exception as e:
            print("code", chain, address, "failed:", e, file=sys.stderr); continue
        if len(code) <= 2:
            print("no code now at", chain, address, file=sys.stderr); continue
        open(path, "w").write(code)
        got += 1
    print(f"fetched {got} listed contracts", file=sys.stderr)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True); ap.add_argument("--blocks", type=int, default=20)
    ap.add_argument("--ids", help="fetch the addresses in this file (one per line, or 'chain address') instead of sampling blocks")
    ap.add_argument("--rpc", default=os.environ.get("EVMDEC_RPC_URL", "https://ethereum-rpc.publicnode.com").split(",")[0])
    ap.add_argument("--max", type=int, default=150); ap.add_argument("--seed", type=int, default=1)
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    if a.ids:
        return fetch_listed(a.ids, a.out, a.rpc)
    random.seed(a.seed)
    latest = int(rpc(a.rpc, "eth_blockNumber", []), 16)
    seen = set(x[:-4].lower() for x in os.listdir(a.out) if x.endswith(".hex"))
    got = 0
    for _ in range(a.blocks):
        n = latest - random.randint(1, 2_000_000)
        try:
            blk = rpc(a.rpc, "eth_getBlockByNumber", [hex(n), True])
        except Exception as e:
            print("block", n, "failed:", e, file=sys.stderr); continue
        for tx in blk["transactions"]:
            to = (tx.get("to") or "").lower()
            if not to or to in seen: continue
            seen.add(to)
            try:
                code = rpc(a.rpc, "eth_getCode", [to, "latest"])
            except Exception as e:
                print("code", to, "failed:", e, file=sys.stderr); continue
            if len(code) <= 2: continue
            open(os.path.join(a.out, to + ".hex"), "w").write(code)
            got += 1
            print(f"{to} {len(code)//2-1} bytes (block {n})")
            if got >= a.max: return
    print(f"harvested {got} contracts", file=sys.stderr)

if __name__ == "__main__":
    main()
