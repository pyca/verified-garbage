import random, sys, gen, emu
P = 2**255 - 19
def ld(m, o): return int.from_bytes(m[o:o+32], 'little')
for name in ('pair', 'seqpair'):
    for _ in range(50):
        m = bytearray(8192); 
        for o in (224, 256, 288, 320): m[o:o+32] = random.choice([random.getrandbits(256), 2**256-1, 0]).to_bytes(32, 'little')
        emu.run(gen.ALL[name], {i: (0 if i == 0 else random.getrandbits(64)) for i in range(31)}, m)
        assert ld(m, 448) % P == ld(m, 320) * ld(m, 224) % P and ld(m, 480) % P == ld(m, 256) * ld(m, 288) % P, name
print('ok')

for name in ('mulA', 'mulT'):
    for _ in range(200):
        m = bytearray(8192)
        for o in (224, 320): m[o:o+32] = random.choice([random.getrandbits(256), 2**256-1, 0]).to_bytes(32, 'little')
        emu.run(gen.ALL[name], {i: (0 if i == 0 else random.getrandbits(64)) for i in range(31)}, m)
        assert ld(m, 448) % P == ld(m, 320) * ld(m, 224) % P, name

for _ in range(100):
    m = bytearray(8192); m[0:4000] = random.randbytes(4000)
    for k in range(2000, 2300): m[k] = random.getrandbits(1)
    res = []
    for name in ('step', 'step_min', 'step_tree', 'st_o0', 'st_o1', 'st_o2', 'st_o3', 'st_o1n', 'src') + tuple(k for k in gen.ALL if k.startswith('sc_')):
        mm = bytearray(m); emu.run(gen.ALL[name], {i: 0 for i in range(31)}, mm)
        res.append([ld(mm, o) % P for o in (96, 128, 160, 192)])
    assert res[0] == res[1], 'min'
    for k, x in enumerate(res): assert x == res[0], k
print('steps ok')

def l5(m, o): return sum(int.from_bytes(m[o+8*k:o+8*k+8], 'little') << (51*k) for k in range(5))
def put5(m, o, top): 
    for k in range(5): m[o+8*k:o+8*k+8] = random.choice([top-1, 0, random.randrange(top)]).to_bytes(8, 'little')
def bnd(m, o): return all(int.from_bytes(m[o+8*k:o+8*k+8], 'little') < 2**51 + 2**15 for k in range(5))
for _ in range(300):
    m = bytearray(8192); put5(m, 224, 2**52 + 2**51 + 2**16); put5(m, 320, 2**52 + 2**51 + 2**16)
    emu.run(gen.ALL['m51'], {i: 0 for i in range(31)}, m); assert l5(m, 448) % P == l5(m, 224) * l5(m, 320) % P and bnd(m, 448)
    m = bytearray(8192); put5(m, 224, 2**52 + 2**51 + 2**16)
    emu.run(gen.ALL['s51'], {i: 0 for i in range(31)}, m); assert l5(m, 448) % P == l5(m, 224) ** 2 % P and bnd(m, 448)
    m = bytearray(8192)
    for n in range(5): put5(m, gen.sl(n), 2**51 + 2**15)
    for k in range(2000, 2300): m[k] = random.getrandbits(1)
    x1, x2, z2, x3, z3 = (l5(m, gen.sl(n)) for n in range(5))
    if m[99+1984] != m[99+1985]: x2, z2, x3, z3 = x3, z3, x2, z2
    emu.run(gen.ALL['st51'], {i: 0 for i in range(31)}, m)
    A, Bb, Cc, D = x2+z2, x2-z2, x3+z3, x3-z3; AA, BB, DA, CB = A*A, Bb*Bb, D*A, Cc*Bb; E = AA-BB
    for n, v in ((1, AA*BB), (2, E*(AA+121665*E)), (3, (DA+CB)**2), (4, x1*(DA-CB)**2)): assert l5(m, gen.sl(n)) % P == v % P, n; assert bnd(m, gen.sl(n))
print('51 ok')

S_ = gen.NS
for _ in range(200):
    m = bytearray(8192); reg = lambda: {i: 0 for i in range(31)}
    for n in 'ABCD': put5(m, S_[n], 2**52 + 2**51 + 2**46)
    a, b, cc, d = (l5(m, S_[n]) for n in 'ABCD')
    mm = bytearray(m); emu.run(gen.KC + gen.ALL['sq2'], reg(), mm); assert l5(mm, S_['AA']) % P == a*a % P and l5(mm, S_['BB']) % P == b*b % P
    mx = max(int.from_bytes(mm[S_['AA']+8*k:S_['AA']+8*k+8], 'little') for k in range(5)); assert mx < 2**51 + 2**20, hex(mx)
    mm = bytearray(m); emu.run(gen.KC + gen.ALL['sq2k'], reg(), mm); assert l5(mm, S_['AA']) % P == a*a % P and l5(mm, S_['BB']) % P == b*b % P
    mm = bytearray(m); emu.run(gen.KC + gen.ALL['mu2k'], reg(), mm); assert l5(mm, S_['x2']) % P == a*b % P and l5(mm, S_['z2']) % P == cc*d % P
    mm = bytearray(m); emu.run(gen.KC + gen.ALL['mu2'], reg(), mm); assert l5(mm, S_['x2']) % P == a*b % P and l5(mm, S_['z2']) % P == cc*d % P
    for name in ('sn0', 'sn1', 'sn2', 'sn3', 'sn4', 'sn5', 'sn6', 'sn6k', 'sn7'):
        m = bytearray(8192)
        for n in ('x1','x2','z2','x3','z3'): put5(m, S_[n], 2**51 + 2**20)
        for k in range(2000, 2300): m[k] = random.getrandbits(1)
        x1, x2, z2, x3, z3 = (l5(m, S_[n]) for n in ('x1','x2','z2','x3','z3'))
        if m[99+1984] != m[99+1985]: x2, z2, x3, z3 = x3, z3, x2, z2
        emu.run(gen.KC + gen.ALL[name], reg(), m)
        A, Bb, Cc, D = x2+z2, x2-z2, x3+z3, x3-z3; AA, BB, DA, CB = A*A, Bb*Bb, D*A, Cc*Bb; E = AA-BB
        for n, v in (('x2', AA*BB), ('z2', E*(AA+121665*E)), ('x3', (DA+CB)**2), ('z3', x1*(DA-CB)**2)): assert l5(m, S_[n]) % P == v % P, n
print('neon ok')
