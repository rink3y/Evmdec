#!/usr/bin/env python3
"""Build the local signature index (`sigs.idx`) from Sourcify's signature export.

Run once when the product is built or deployed; the output is a single file that
`evmdec` searches in place (see `crates/decompiler/src/sigdb.rs` for the format).

    python3 corpus/build_sigs.py --out sigs.idx

Downloads the Parquet shards of https://export.sourcify.dev/?prefix=v2/signatures/
(about 540 MB, cached under --cache so a rerun only fetches new shards), then writes
the index in one pass. Needs `pyarrow` and `numpy`; peak memory is about 1.5 GB.
"""

from __future__ import annotations

import argparse
import os
import struct
import sys
import time
import urllib.request
import xml.etree.ElementTree as ET
from pathlib import Path

LISTING = "https://export.sourcify.dev/?prefix=v2/signatures/"
BASE = "https://export.sourcify.dev/"
MAGIC = b"EVMSIG1\n"
HEADER = 24
ENTRY = 12
# Signatures longer than this are not useful to a decompiler and bloat the pool.
MAX_SIG = 4096


def log(msg: str) -> None:
    print(msg, file=sys.stderr, flush=True)


def shard_keys() -> list[str]:
    """Names of the Parquet shards in the export bucket."""
    with urllib.request.urlopen(LISTING, timeout=60) as r:
        root = ET.fromstring(r.read())
    keys = []
    for el in root.iter():
        if el.tag.endswith("Key") and el.text and el.text.endswith(".parquet"):
            keys.append(el.text)
    if not keys:
        raise SystemExit("no Parquet shards found in the export listing")
    return sorted(keys)


def download(key: str, cache: Path) -> Path:
    """Fetch one shard into the cache, skipping shards already there."""
    dest = cache / Path(key).name
    if dest.exists() and dest.stat().st_size > 0:
        return dest
    tmp = dest.with_suffix(".part")
    log(f"  downloading {key}")
    for attempt in range(5):
        try:
            with urllib.request.urlopen(BASE + key, timeout=120) as r, open(tmp, "wb") as f:
                while True:
                    chunk = r.read(1 << 20)
                    if not chunk:
                        break
                    f.write(chunk)
            tmp.rename(dest)
            return dest
        except OSError as e:
            if attempt == 4:
                raise
            log(f"    retrying after {e}")
            time.sleep(2 ** (attempt + 1))
    raise AssertionError("unreachable")


def build(shards: list[Path], out: Path) -> int:
    import numpy as np
    import pyarrow.parquet as pq

    prefixes: list[np.ndarray] = []
    offsets: list[np.ndarray] = []
    pool = bytearray()
    seen: set[bytes] = set()
    for shard in shards:
        log(f"  reading {shard.name}")
        table = pq.read_table(shard, columns=["signature_hash_32", "signature"])
        hashes = table.column("signature_hash_32").to_pylist()
        sigs = table.column("signature").to_pylist()
        p = np.empty(len(sigs), dtype=np.uint64)
        o = np.empty(len(sigs), dtype=np.uint32)
        n = 0
        for h, s in zip(hashes, sigs):
            if not s or len(s) > MAX_SIG:
                continue
            b = s.encode("utf-8")
            if b in seen or b"\0" in b:
                continue
            seen.add(b)
            raw = bytes.fromhex(h[2:] if h.startswith("0x") else h) if isinstance(h, str) else bytes(h)
            p[n] = int.from_bytes(raw[:8], "big")
            if len(pool) >= 0xFFFFFFFF:
                raise SystemExit("string pool exceeds 4 GiB")
            o[n] = len(pool)
            pool += b
            pool.append(0)
            n += 1
        prefixes.append(p[:n])
        offsets.append(o[:n])
        del table, hashes, sigs
    seen.clear()
    p = np.concatenate(prefixes) if prefixes else np.empty(0, dtype=np.uint64)
    o = np.concatenate(offsets) if offsets else np.empty(0, dtype=np.uint32)
    log(f"  sorting {len(p):,} entries")
    order = np.lexsort((o, p))
    p = p[order]
    o = o[order]
    entries = np.empty(len(p), dtype=[("p", "<u8"), ("o", "<u4")])
    entries["p"] = p
    entries["o"] = o
    tmp = out.with_suffix(out.suffix + ".part")
    with open(tmp, "wb") as f:
        f.write(MAGIC)
        f.write(struct.pack("<QQ", len(p), HEADER + len(p) * ENTRY))
        f.write(entries.tobytes())
        f.write(pool)
    tmp.replace(out)
    return len(p)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out", default="sigs.idx", help="index file to write (default sigs.idx)")
    ap.add_argument("--cache", default=".sigs-cache", help="where downloaded shards are kept")
    ap.add_argument("--shards", nargs="*", help="use these local Parquet files instead of downloading")
    args = ap.parse_args()
    cache = Path(args.cache)
    cache.mkdir(parents=True, exist_ok=True)
    started = time.time()
    if args.shards:
        shards = [Path(s) for s in args.shards]
    else:
        log("listing export shards")
        shards = [download(k, cache) for k in shard_keys()]
    n = build(shards, Path(args.out))
    size = os.path.getsize(args.out)
    log(f"wrote {args.out}: {n:,} signatures, {size / 1e6:.0f} MB in {time.time() - started:.0f}s")


if __name__ == "__main__":
    main()
