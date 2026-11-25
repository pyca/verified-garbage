"""A small emulator of the A64 instructions used here, to check the lab's bodies."""
import re
M = 2**64
def run(body, regs, mem, flags=None):
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
        m = re.match(r'(.*?),\s*\[(\w+)(?:,\s*#(-?\d+))?\]$', rest)
        if m:
            rs = [r.strip() for r in m.group(1).split(',')]; a = regs[int(m.group(2)[1:])] + int(m.group(3) or 0)
            for k, r in enumerate(rs):
                if op in ('ldr','ldp'): w(r, int.from_bytes(mem[a+8*k:a+8*k+8], 'little'))
                elif op in ('str','stp'): mem[a+8*k:a+8*k+8] = g(r).to_bytes(8, 'little')
                elif op == 'ldrb': w(r, mem[a])
                else: raise Exception(l)
            continue
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
