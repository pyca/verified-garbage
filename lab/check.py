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
