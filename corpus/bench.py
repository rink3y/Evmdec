#!/usr/bin/env python3
"""Accuracy benchmark: compare evmdec's recovered interface against verified ABIs.

Usage: corpus/bench.py [--bin target/release/evmdec] [--dir testdata/mainnet] [--sigs]

For every `<name>.hex` with a `<name>.abi.json` (Sourcify format) it reports selector
recall/precision, state-mutability accuracy, parameter-count and return-count accuracy and
event recall. The signature dictionary is disabled by default so that *inference* is measured.
"""
import argparse, json, os, subprocess, sys

# --- keccak256 (so the script has no dependencies) ---
RC = [0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000, 0x000000000000808b, 0x0000000080000001,
      0x8000000080008081, 0x8000000000008009, 0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
      0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
      0x000000000000800a, 0x800000008000000a, 0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]
ROT = [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44]
PIL = [10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1]
M = (1 << 64) - 1
def rol(x, n): return ((x << n) | (x >> (64 - n))) & M
def keccakf(st):
    for r in range(24):
        bc = [st[i] ^ st[i+5] ^ st[i+10] ^ st[i+15] ^ st[i+20] for i in range(5)]
        for i in range(5):
            t = bc[(i+4) % 5] ^ rol(bc[(i+1) % 5], 1)
            for j in range(0, 25, 5): st[j+i] ^= t
        t = st[1]
        for i in range(24):
            j = PIL[i]; st[j], t = rol(t, ROT[i]), st[j]
        for j in range(0, 25, 5):
            b = st[j:j+5]
            for i in range(5): st[j+i] ^= (~b[(i+1) % 5]) & b[(i+2) % 5]
        st[0] ^= RC[r]
def keccak256(data):
    st = [0]*25; rate = 136
    data = bytearray(data); data.append(1)
    while len(data) % rate: data.append(0)
    data[-1] |= 0x80
    for off in range(0, len(data), rate):
        for i in range(rate // 8): st[i] ^= int.from_bytes(data[off+i*8:off+i*8+8], 'little')
        keccakf(st)
    return b''.join(st[i].to_bytes(8, 'little') for i in range(4))

def canon(t):
    if t['type'].startswith('tuple'):
        inner = ','.join(canon(c) for c in t['components'])
        return '(' + inner + ')' + t['type'][5:]
    return t['type']

def sig(item):
    return item['name'] + '(' + ','.join(canon(i) for i in item.get('inputs', [])) + ')'

def mut(item):
    m = item.get('stateMutability')
    if m: return m
    if item.get('constant'): return 'view'
    if item.get('payable'): return 'payable'
    return 'nonpayable'

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--bin', default='target/release/evmdec')
    ap.add_argument('--dir', default='testdata/mainnet')
    ap.add_argument('--sigs', action='store_true', help='enable the signature dictionary')
    ap.add_argument('-v', action='store_true')
    a = ap.parse_args()
    tot = dict(abi=0, found=0, match=0, mut_ok=0, mut_n=0, par_ok=0, par_n=0, ret_ok=0, ret_n=0, ev=0, ev_found=0, time=0.0, blocks=0, covered=0, unresolved=0)
    # Type accuracy: ABI head words whose inferred Solidity type equals the declared one.
    ty = dict(par_words=0, par_exact=0, ret_words=0, ret_exact=0)
    wrong = []
    rows = []
    for f in sorted(os.listdir(a.dir)):
        if not f.endswith('.hex'): continue
        name = f[:-4]
        abi_path = os.path.join(a.dir, name + '.abi.json')
        if not os.path.exists(abi_path): continue
        abi = json.load(open(abi_path)).get('abi')
        if not abi: continue
        cmd = [a.bin, 'decompile', '--json', os.path.join(a.dir, f)] + ([] if a.sigs else ['--no-sigs'])
        import time; t = time.time()
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
        dt = time.time() - t
        if out.returncode != 0:
            print(f'{name}: FAILED {out.stderr[:200]}'); continue
        c = json.loads(out.stdout)
        funcs = {int(x['selector'], 16): x for x in c['functions'] if x['kind'] == 'external'}
        abi_f = {}
        for it in abi:
            if it['type'] == 'function':
                abi_f[int.from_bytes(keccak256(sig(it).encode())[:4], 'big')] = it
        abi_sel = set(abi_f); got = set(funcs)
        match = abi_sel & got
        mut_ok = par_ok = ret_ok = 0
        for s in match:
            it = abi_f[s]; fx = funcs[s]
            m = mut(it); ours = fx['mutability']
            ok = (m in ('view', 'pure') and ours in ('view', 'pure')) or (m == 'payable' and ours == 'payable') or (m == 'nonpayable' and ours in ('non_payable', 'nonpayable'))
            mut_ok += ok
            # parameter count: ABI head words (dynamic = 1 word each)
            n_in = len(it.get('inputs', []))
            # tuples occupy several words when static; count ABI head words
            def is_dynamic(t):
                ty = t['type']
                if ty in ('string', 'bytes') or ty.endswith('[]'): return True
                if ty.startswith('tuple'):
                    return any(is_dynamic(c) for c in t['components'])
                import re
                m2 = re.match(r'(.*)\[(\d+)\]$', ty)
                if m2:
                    base = dict(t); base['type'] = m2.group(1)
                    return is_dynamic(base)
                return False
            def head_words(t):
                if is_dynamic(t): return 1
                if t['type'].startswith('tuple') and not t['type'].endswith(']'):
                    return sum(head_words(c) for c in t['components'])
                if t['type'].endswith(']') and not t['type'].endswith('[]'):
                    import re
                    m2 = re.match(r'(.*)\[(\d+)\]$', t['type'])
                    base = dict(t); base['type'] = m2.group(1)
                    return int(m2.group(2)) * head_words(base)
                return 1
            hw = sum(head_words(x) for x in it.get('inputs', []))
            par_ok += (len(fx['params']) == hw)
            def word_types(t):
                # Declared type of every head word of `t`; dynamic values are one word.
                if is_dynamic(t): return ['dynamic']
                tt = t['type']
                if tt.startswith('tuple') and not tt.endswith(']'):
                    return [w for c in t['components'] for w in word_types(c)]
                import re
                m2 = re.match(r'(.*)\[(\d+)\]$', tt)
                if m2:
                    base = dict(t); base['type'] = m2.group(1)
                    return word_types(base) * int(m2.group(2))
                return [{'uint': 'uint256', 'int': 'int256'}.get(tt, tt)]
            def same(decl, ours):
                if decl == 'dynamic': return ours in ('bytes', 'string') or ours.endswith('[]')
                return decl == ours
            decl_in = [w for x in it.get('inputs', []) for w in word_types(x)]
            if len(decl_in) == len(fx['params']):
                for d, p in zip(decl_in, fx['params']):
                    ty['par_words'] += 1
                    if same(d, p['ty']): ty['par_exact'] += 1
                    else: wrong.append(f"{name} {sig(it)} param {p['name']}: abi={d} ours={p['ty']}")
            decl_out = [w for x in it.get('outputs', []) for w in word_types(x)]
            if decl_out and len(decl_out) == len(fx['returns']) and 'dynamic' not in decl_out:
                for d, r in zip(decl_out, fx['returns']):
                    ty['ret_words'] += 1
                    if same(d, r): ty['ret_exact'] += 1
                    else: wrong.append(f"{name} {sig(it)} return: abi={d} ours={r}")
            n_out = len(it.get('outputs', []))
            ret_ok += (len(fx['returns']) == n_out) or (n_out > 0 and any(o['type'] in ('string', 'bytes') or o['type'].endswith(']') for o in it['outputs']) and len(fx['returns']) >= 1)
            if a.v and (not ok or len(fx['params']) != hw):
                print(f"   {name} {sig(it)}: abi={m} ours={ours} params abi={hw} ours={len(fx['params'])} rets abi={n_out} ours={fx['returns']}")
        abi_ev = set()
        for it in abi:
            if it['type'] == 'event':
                abi_ev.add(keccak256(sig(it).encode()).hex())
        got_ev = set()
        for e in c['events']:
            if '// topic0 0x' in e: got_ev.add(e.split('// topic0 0x')[1].strip())
            elif e.startswith('0x') and ' ' in e: got_ev.add(e.split()[0][2:])
            else:
                # Declarations carry `indexed` markers; the topic hash uses the bare signature.
                bare = e.replace(' indexed', '').replace(', ', ',')
                got_ev.add(keccak256(bare.encode()).hex())
        ev_found = len(abi_ev & got_ev)
        st = c['stats']
        rows.append((name, len(abi_sel), len(got), len(match), mut_ok, par_ok, ret_ok, len(abi_ev), ev_found, st['covered_blocks'], st['code_blocks'], st['unresolved_jumps'], dt))
        tot['abi'] += len(abi_sel); tot['found'] += len(got); tot['match'] += len(match)
        tot['mut_ok'] += mut_ok; tot['par_ok'] += par_ok; tot['ret_ok'] += ret_ok; tot['mut_n'] += len(match)
        tot['ev'] += len(abi_ev); tot['ev_found'] += ev_found; tot['time'] += dt
        tot['blocks'] += st['code_blocks']; tot['covered'] += st['covered_blocks']; tot['unresolved'] += st['unresolved_jumps']
        if a.v:
            miss = abi_sel - got; extra = got - abi_sel
            for s in sorted(miss): print(f'   missing {name}: {sig(abi_f[s])}')
            for s in sorted(extra): print(f'   extra   {name}: {funcs[s]["selector"]}')
    print(f"{'contract':<22}{'abi':>5}{'found':>6}{'match':>6}{'mut':>5}{'params':>7}{'rets':>5}{'events':>8}{'blocks':>12}{'unres':>6}{'time':>7}")
    for r in rows:
        print(f"{r[0]:<22}{r[1]:>5}{r[2]:>6}{r[3]:>6}{r[4]:>5}{r[5]:>7}{r[6]:>5}{r[8]:>4}/{r[7]:<3}{r[9]:>6}/{r[10]:<5}{r[11]:>6}{r[12]:>7.2f}")
    n = tot['match'] or 1
    print(f"\nselectors: recall {tot['match']}/{tot['abi']} = {100*tot['match']/max(1,tot['abi']):.1f}%  precision {tot['match']}/{tot['found']} = {100*tot['match']/max(1,tot['found']):.1f}%")
    print(f"mutability: {tot['mut_ok']}/{n} = {100*tot['mut_ok']/n:.1f}%   params: {tot['par_ok']}/{n} = {100*tot['par_ok']/n:.1f}%   returns: {tot['ret_ok']}/{n} = {100*tot['ret_ok']/n:.1f}%")
    print(f"param types: {ty['par_exact']}/{ty['par_words']} = {100*ty['par_exact']/max(1,ty['par_words']):.1f}%   return types: {ty['ret_exact']}/{ty['ret_words']} = {100*ty['ret_exact']/max(1,ty['ret_words']):.1f}%")
    if a.v:
        for w in wrong: print('   ' + w)
    print(f"events: {tot['ev_found']}/{tot['ev']} = {100*tot['ev_found']/max(1,tot['ev']):.1f}%   blocks covered: {tot['covered']}/{tot['blocks']} = {100*tot['covered']/max(1,tot['blocks']):.2f}%   unresolved jumps: {tot['unresolved']}   total time {tot['time']:.2f}s")

if __name__ == '__main__':
    main()
