"""A small emulator of the A64 instructions used here, to check the lab's bodies."""
import re
M = 2**64
def run(body, regs, mem, flags=None):
    V = {}
    C = 0; N = 0; Z = 0
    def g(x):
        x = x.strip()
        if x.startswith('#'): return int(x[1:], 0)
        if x in ('xzr','wzr'): return 0
        return regs[int(x[1:])] % (M if x[0] == 'x' else 2**32)
    def w(x, v):
        if x in ('xzr','wzr'): return
        regs[int(x[1:])] = v % (M if x[0] == 'x' else 2**32)
    for l in body:
        op, _, rest = l.partition(' ')
        if re.match(r'q\d', rest):
            vec(op, rest, V, mem, regs); continue
        m = re.match(r'(.*?),\s*\[(\w+)(?:,\s*#(-?\d+))?\]$', rest)
        if m:
            rs = [r.strip() for r in m.group(1).split(',')]; a = regs[int(m.group(2)[1:])] + int(m.group(3) or 0)
            for k, r in enumerate(rs):
                if op in ('ldr','ldp'): w(r, int.from_bytes(mem[a+8*k:a+8*k+8], 'little'))
                elif op in ('str','stp'): mem[a+8*k:a+8*k+8] = g(r).to_bytes(8, 'little')
                elif op == 'ldrb': w(r, mem[a])
                else: raise Exception(l)
            continue
        if re.match(r'[vq]\d', rest):
            vec(op, rest, V, mem, regs); continue
        o = [x.strip() for x in rest.split(',')]
        sh = 0
        if len(o) > 2 and o[-1].startswith('lsl'): sh = int(o[-1].split('#')[1]); o = o[:-1]
        if op in ('mov','movz'): w(o[0], g(o[1]) << sh)
        elif op == 'movk': w(o[0], (g(o[0]) & ~(0xffff << sh)) | (g(o[1]) << sh))
        elif op == 'mul': w(o[0], g(o[1]) * g(o[2]))
        elif op == 'umulh': w(o[0], (g(o[1]) * g(o[2])) >> 64)
        elif op == 'umull': w(o[0], g(o[1]) * g(o[2]))
        elif op == 'madd': w(o[0], g(o[1]) * g(o[2]) + g(o[3]))
        elif op in ('add','adds','adc','adcs','sub','subs','sbc','sbcs'):
            x, y = g(o[1]), (g(o[2]) << sh) % M
            if op[0] == 's': y = M - 1 - y
            c = {'add': 0, 'adds': 0, 'sub': 1, 'subs': 1}.get(op, C)
            v = x + y + c
            if op.endswith('s'): C = v >> 64; Z = v % M == 0; N = (v % M) >> 63
            w(o[0], v)
        elif op == 'lsr': w(o[0], g(o[1]) >> g(o[2]))
        elif op == 'lsl': w(o[0], g(o[1]) << g(o[2]))
        elif op == 'eor': w(o[0], g(o[1]) ^ g(o[2]))
        elif op == 'and': w(o[0], g(o[1]) & g(o[2]))
        elif op == 'extr': w(o[0], ((g(o[1]) << 64) | g(o[2])) >> g(o[3]))
        elif op == 'tst': Z = (g(o[0]) & g(o[1])) == 0
        elif op == 'csel': w(o[0], g(o[1]) if {'ne': not Z, 'eq': Z, 'hs': C, 'cs': C, 'lo': not C, 'cc': not C}[o[3]] else g(o[2]))
        else: raise Exception(l)

import random as _r
def vec(op, rest, V, mem, regs):
    def gv(n): return V.setdefault(n, _r.getrandbits(128))
    m = re.match(r'q(\d+),\s*\[x(\d+)(?:, #(\d+))?\]$', rest)
    if m:
        n, a = int(m[1]), regs[int(m[2])] + int(m[3] or 0)
        assert a % 16 == 0
        if op == 'ldr': V[n] = int.from_bytes(mem[a:a+16], 'little')
        else: mem[a:a+16] = gv(n).to_bytes(16, 'little')
        return
    o = [x.strip() for x in rest.split(',')]
    n = [int(re.match(r'[vx](\d+)', x)[1]) if x[0] in 'vx' else int(x[1:], 0) for x in o]
    w = {'2d': 64, '4s': 32, '2s': 32, '16b': 8}[o[0].split('.')[1]]
    L = lambda x, w: [(x >> (w*i)) % 2**w for i in range(128 // w)]
    J = lambda l, w: sum((y % 2**w) << (w*i) for i, y in enumerate(l))
    if op == 'dup': V[n[0]] = J([regs[n[1]]] * 2, 64); return
    a = gv(n[1]); b = gv(n[2]) if len(o) > 2 and o[2][0] == 'v' else None
    if op in ('umull','umull2','umlal','umlal2'):
        k = 2 if op.endswith('2') else 0
        r = [L(a, 32)[k+i] * L(b, 32)[k+i] for i in range(2)]
        if 'mlal' in op: r = [x + y for x, y in zip(r, L(gv(n[0]), 64))]; assert all(x < 2**64 for x in r), 'overflow'
        V[n[0]] = J(r, 64)
    elif op == 'add':
        r = [x + y for x, y in zip(L(a, w), L(b, w))]; assert all(x < 2**w for x in r), 'overflow'; V[n[0]] = J(r, w)
    elif op == 'sub':
        r = [x - y for x, y in zip(L(a, w), L(b, w))]; assert all(x >= 0 for x in r), 'underflow'; V[n[0]] = J(r, w)
    elif op == 'mul':
        r = [x * y for x, y in zip(L(a, w), L(b, w))]; assert all(x < 2**w for x in r), 'overflow'; V[n[0]] = J(r, w)
    elif op == 'and': V[n[0]] = a & b
    elif op == 'shl': 
        r = [x << n[2] for x in L(a, w)]; assert n[2] == 13 or all(x < 2**w for x in r), 'overflow'; V[n[0]] = J(r, w)
    elif op == 'sri': V[n[0]] = J([(y >> (w-n[2]) << (w-n[2])) | (x >> n[2]) for x, y in zip(L(a, w), L(gv(n[0]), w))], w)
    elif op == 'shlw': V[n[0]] = J([x << n[2] for x in L(a, w)], w)
    elif op == 'ushr': V[n[0]] = J([x >> n[2] for x in L(a, w)], w)
    elif op == 'trn1': x, y = L(a, w), L(b, w); V[n[0]] = J([z for i in range(0, len(x), 2) for z in (x[i], y[i])], w)
    elif op == 'trn2': x, y = L(a, w), L(b, w); V[n[0]] = J([z for i in range(0, len(x), 2) for z in (x[i+1], y[i+1])], w)
    elif op == 'uzp1': x = L(a, w) + L(b, w); V[n[0]] = J(x[0::2], w)
    elif op == 'ext': V[n[0]] = ((b << 128 | a) >> (8 * n[3])) % 2**128
    else: raise Exception(op + ' ' + rest)
