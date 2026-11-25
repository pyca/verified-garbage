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
    for name in ('step', 'step_min', 'step_tree', 'st_o0', 'st_o1', 'st_o2', 'st_o3', 'st_o1n'):
        mm = bytearray(m); emu.run(gen.ALL[name], {i: 0 for i in range(31)}, mm)
        res.append([ld(mm, o) % P for o in (96, 128, 160, 192)])
    assert res[0] == res[1], 'min'
    for k, x in enumerate(res): assert x == res[0], k
print('steps ok')
