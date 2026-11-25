#!/usr/bin/env python3
"""Writes bench/benches/primitives/lab.rs: microbenchmarks, each a loop of a body."""
import sys, pathlib
B = {}
def rep(f, n): return [x for i in range(n) for x in f(i)]
B['clk_add100'] = ['add x2, x2, x3'] * 100
B['mul_thr100'] = rep(lambda i: [f'mul x{4+i%8}, x2, x3'], 100)
B['umulh_thr100'] = rep(lambda i: [f'umulh x{4+i%8}, x2, x3'], 100)
B['mulpair_thr50'] = rep(lambda i: [f'mul x{4+i%8}, x2, x3', f'umulh x{12+i%4}, x2, x3'], 50)
B['mul_lat100'] = ['mul x2, x2, x3'] * 100
B['umulh_lat100'] = ['umulh x2, x2, x3'] * 100
B['umull_thr100'] = rep(lambda i: [f'umull x{4+i%8}, w2, w3'], 100)
B['madd_thr100'] = rep(lambda i: [f'madd x{4+i%8}, x2, x3, x{4+i%8}'], 100)
B['umaddl_thr100'] = rep(lambda i: [f'umaddl x{4+i%8}, w2, w3, x{4+i%8}'], 100)
B['adcs_chain100'] = ['adds x4, x4, x2'] + rep(lambda i: [f'adcs x{4+i%8}, x{4+i%8}, x2'], 99)
B['adcs_indep25x4'] = rep(lambda i: [f'adds x4, x2, x3', 'adcs x5, x2, x3', 'adcs x6, x2, x3', 'adc x7, x2, x3'], 25)
B['adds_indep100'] = rep(lambda i: [f'adds x{4+i%8}, x2, x3'], 100)
B['add_thr100'] = rep(lambda i: [f'add x{4+i%8}, x2, x3'], 100)
B['addlsl_thr100'] = rep(lambda i: [f'add x{4+i%8}, x2, x3, lsl #13'], 100)
B['csel_thr100'] = rep(lambda i: [f'csel x{4+i%8}, x2, x3, ne'], 100)
B['extr_thr100'] = rep(lambda i: [f'extr x{4+i%8}, x2, x3, #7'], 100)
B['lsr_thr100'] = rep(lambda i: [f'lsr x{4+i%8}, x2, #7'], 100)
B['ldp_thr100'] = rep(lambda i: [f'ldp x{4+2*(i%4)}, x{5+2*(i%4)}, [x0, #64]'], 100)
B['stp_thr100'] = rep(lambda i: ['stp x2, x3, [x0, #64]'], 100)
B['vumull_thr100'] = rep(lambda i: [f'umull v{i%8}.2d, v16.2s, v17.2s'], 100)
B['vumlal_thr100'] = rep(lambda i: [f'umlal v{i%8}.2d, v16.2s, v17.2s'], 100)
B['vumlal_lat100'] = ['umlal v0.2d, v16.2s, v17.2s'] * 100
B['vmix100'] = rep(lambda i: [f'umlal v{i%8}.2d, v16.2s, v17.2s', f'mul x{4+i%8}, x2, x3'], 100)
B['vadd_thr100'] = rep(lambda i: [f'add v{i%8}.2d, v16.2d, v17.2d'], 100)

m = lambda i: f'mul x{4+i%4}, x2, x3'
ch = lambda i: ['adds x12, x2, x3', 'adcs x13, x2, x3', 'adcs x14, x2, x3', 'adcs x15, x2, x3']
B['mix_mul50_adds50'] = rep(lambda i: [m(i), f'adds x{12+i%4}, x2, x3'], 50)
B['mix_mul50_add50'] = rep(lambda i: [m(i), f'add x{12+i%4}, x2, x3'], 50)
B['mix_mul50_add100'] = rep(lambda i: [m(i), f'add x{12+i%4}, x2, x3', f'add x{12+i%4}, x2, x3'], 50)
B['mix_mul100_chain4x25'] = rep(lambda i: [m(0), m(1), m(2), m(3)] + ch(i), 25)
B['mix_mul50_chain4x25'] = rep(lambda i: [m(0), m(1)] + ch(i), 25)
B['mix_add100_chain4x25'] = rep(lambda i: [f'add x{4+k}, x2, x3' for k in range(4)] + ch(i), 25)
B['chain8x12'] = rep(lambda i: ['adds x12, x2, x3'] + ['adcs x13, x2, x3'] * 7, 12)
B['chain4x25_dst'] = rep(lambda i: ['adds x12, x12, x3', 'adcs x13, x13, x3', 'adcs x14, x14, x3', 'adcs x15, x15, x3'], 25)
B['adc_nochain100'] = rep(lambda i: [f'adc x{4+i%8}, x2, x3'], 100)
B['adcs_nochain_src100'] = rep(lambda i: ['cmp x2, x3', 'adcs x4, x2, x3'], 50)
B['adds_dep_mul'] = rep(lambda i: [f'mul x{4+i%4}, x2, x3', f'adds x{12+i%4}, x{4+i%4}, x3'], 50)
B['mulrows_only'] = rep(lambda i: [f'{o} x{4+k}, x2, x3' for o in ('mul','umulh') for k in range(4)], 5)
B['nop100'] = ['nop'] * 100
B['mov100'] = rep(lambda i: [f'mov w{4+i%8}, #38'], 100)
B['ldr_thr100'] = rep(lambda i: [f'ldr x{4+i%8}, [x0, #64]'], 100)
S = [l.strip() for l in open(pathlib.Path(__file__).parent / 'step.s')]
B['step'] = ['mov w10, #0', 'mov x19, #100'] + S
def idx(p, k=0):
    return [i for i, l in enumerate(S) if l.startswith(p)][k]
# the first square (load to store), and the first product
sq = [l for l in S]
stores = [i for i, l in enumerate(S) if l.startswith('stp x4, x5')]
def cut(store_off, load_prefix):
    e = next(i for i, l in enumerate(S) if l == f'stp x4, x5, [x0, #{store_off}]') + 2
    b = max(i for i in range(e) if S[i].startswith(load_prefix))
    return S[b:e]
sqr = cut(352, 'ldp x12, x13')       # slot 9 := A^2
mulx = cut(448, 'ldp x12, x13')      # slot 12 := D A
B['sqr'] = ['mov w10, #0'] + sqr
B['mul'] = ['mov w10, #0'] + mulx
B['sqr_dep'] = ['mov w10, #0'] + [l.replace('#352', '#224').replace('#368', '#240') for l in sqr]
b0 = next(i for i, l in enumerate(S) if l == 'ldp x12, x13, [x0, #224]')
B['front'] = ['mov w10, #0', 'mov x19, #100'] + S[:b0]

# Experiment 2: pairs of products, rows alternating.
def row(acc, oa, ob, i, sh):
    a, b, l = 'x3', ['x12','x13','x14','x15'], ['x2','x8','x9','x16']
    t = acc
    r = [f'ldr {a}, [x0, #{oa+8*i}]', f'ldp {b[0]}, {b[1]}, [x0, #{ob}]', f'ldp {b[2]}, {b[3]}, [x0, #{ob+16}]']
    r += [f'mul {l[k]}, {a}, {b[k]}' for k in range(4)]
    if i == 0:
        r += [f'umulh {b[k]}, {a}, {b[k]}' for k in range(4)]
        # t0=l0 stored; t1..t4
        r += [f'str {l[0]}, [x0, #{sh}]', f'adds {t[0]}, {l[1]}, {b[0]}', f'adcs {t[1]}, {l[2]}, {b[1]}', f'adcs {t[2]}, {l[3]}, {b[2]}', f'adc {t[3]}, {b[3]}, x10']
        return r
    r += [f'adds {t[0]}, {t[0]}, {l[0]}', f'adcs {t[1]}, {t[1]}, {l[1]}', f'adcs {t[2]}, {t[2]}, {l[2]}', f'adcs {t[3]}, {t[3]}, {l[3]}', f'adcs x17, x10, x10']
    r += [f'umulh {b[k]}, {a}, {b[k]}' for k in range(4)]
    r += [f'str {t[0]}, [x0, #{sh+8*i}]']
    r += [f'adds {t[1]}, {t[1]}, {b[0]}', f'adcs {t[2]}, {t[2]}, {b[1]}', f'adcs {t[3]}, {t[3]}, {b[2]}', f'adc {t[0]}, x17, {b[3]}']
    return r
def fold(h, sh, o):
    l, m = ['x2','x3','x8','x9'], ['x12','x13','x14','x15']
    r = ['mov w11, #38', f'ldp {l[0]}, {l[1]}, [x0, #{sh}]', f'ldp {l[2]}, {l[3]}, [x0, #{sh+16}]']
    r += [f'mul {m[k]}, x11, {h[k]}' for k in range(4)]
    r += [f'adds {l[0]}, {l[0]}, {m[0]}', f'adcs {l[1]}, {l[1]}, {m[1]}', f'adcs {l[2]}, {l[2]}, {m[2]}', f'adcs {l[3]}, {l[3]}, {m[3]}', 'adcs x17, x10, x10']
    r += [f'umulh {h[k]}, x11, {h[k]}' for k in range(4)]
    r += [f'adds {l[3]}, {l[3]}, {h[2]}', f'adc x17, x17, {h[3]}', f'adds x16, {l[3]}, {l[3]}', 'adc x17, x17, x17', 'mov w11, #19', f'lsr {l[3]}, x16, #1', 'mul x17, x17, x11',
          f'adds {l[0]}, {l[0]}, x17', f'adcs {l[1]}, {l[1]}, {h[0]}', f'adcs {l[2]}, {l[2]}, {h[1]}', f'adc {l[3]}, {l[3]}, x10', f'stp {l[0]}, {l[1]}, [x0, #{o}]', f'stp {l[2]}, {l[3]}, [x0, #{o+16}]']
    return r
def pair(o1, a1, b1, o2, a2, b2):
    c1, c2 = ['x4','x5','x6','x7'], ['x21','x22','x23','x24']
    r = []
    for i in range(4):
        r += row(c1, a1, b1, i, 352); r += row(c2, a2, b2, i, 384)
        if i: c1 = c1[1:] + c1[:1]; c2 = c2[1:] + c2[:1]
    return r, c1, c2
def pairfull(o1, a1, b1, o2, a2, b2):
    r, c1, c2 = pair(o1, a1, b1, o2, a2, b2)
    return r + fold(c1, 352, o1) + fold(c2, 384, o2)
B['pair'] = ['mov w10, #0'] + pairfull(448, 320, 224, 480, 256, 288)
B['pair_dep'] = ['mov w10, #0'] + pairfull(224, 224, 224, 256, 256, 256)
def seqpair(o1, a1, b1, o2, a2, b2):
    r = []
    for o, a, b in ((o1, a1, b1), (o2, a2, b2)):
        c = ['x4','x5','x6','x7']
        for i in range(4):
            r += row(c, a, b, i, 352)
            if i: c = c[1:] + c[:1]
        r += fold(c, 352, o)
    return r
B['seqpair'] = ['mov w10, #0'] + seqpair(448, 320, 224, 480, 256, 288)
B['seqpair_dep'] = ['mov w10, #0'] + seqpair(224, 224, 224, 256, 256, 256)
ALL = dict(B)

for N in (10, 20, 30, 40, 50, 60):
    for op in ('adds', 'add'):
        B[f'win_{op}{N}'] = ['umulh x2, x2, x3'] * 12 + [f'{op} x{12+k%4}, x3, x3' for k in range(N)] + ['umulh x4, x4, x3'] * 12 + [f'{op} x{12+k%4}, x3, x3' for k in range(N)]
BR = ['x12','x13','x14','x15']
def ldb(ob): return [f'ldp x12, x13, [x0, #{ob}]', f'ldp x14, x15, [x0, #{ob+16}]']
def foldR(l, h, o):
    """l + 38 h into [o], words in registers; temporaries x2 x8 x9 x11 x16 x17."""
    m = ['x2','x8','x9','x16']
    r = ['mov w11, #38'] + [f'mul {m[k]}, x11, {h[k]}' for k in range(4)] + [f'umulh {h[k]}, x11, {h[k]}' for k in range(4)]
    r += [f'adds {l[0]}, {l[0]}, {m[0]}', f'adcs {l[1]}, {l[1]}, {m[1]}', f'adcs {l[2]}, {l[2]}, {m[2]}', f'adcs {l[3]}, {l[3]}, {m[3]}', f'adc {h[3]}, {h[3]}, x10']
    r += [f'adds {l[3]}, {l[3]}, {h[2]}', f'adc {h[3]}, {h[3]}, x10', 'mov w11, #19', f'extr x17, {h[3]}, {l[3]}, #63', f'and {l[3]}, {l[3]}, #0x7fffffffffffffff', 'mul x17, x17, x11',
          f'adds {l[0]}, {l[0]}, x17', f'adcs {l[1]}, {l[1]}, {h[0]}', f'adcs {l[2]}, {l[2]}, {h[1]}', f'adc {l[3]}, {l[3]}, x10', f'stp {l[0]}, {l[1]}, [x0, #{o}]', f'stp {l[2]}, {l[3]}, [x0, #{o+16}]']
    return r
def mulA(o, a, b, fold=True):
    W = ['x4','x5','x6','x7','x21','x22','x23','x24']
    L = ['x2','x8','x9','x16']
    r = ldb(b) + [f'ldr x3, [x0, #{a}]'] + [f'mul {W[k]}, x3, {BR[k]}' for k in range(4)] + [f'umulh {L[k]}, x3, {BR[k]}' for k in range(4)]
    r += [f'adds {W[1]}, {W[1]}, {L[0]}', f'adcs {W[2]}, {W[2]}, {L[1]}', f'adcs {W[3]}, {W[3]}, {L[2]}', f'adc {W[4]}, {L[3]}, x10']
    for i in range(1, 4):
        t = W[i:i+5]
        r += [f'ldr x3, [x0, #{a+8*i}]'] + [f'mul {L[k]}, x3, {BR[k]}' for k in range(4)]
        r += [f'adds {t[0]}, {t[0]}, {L[0]}', f'adcs {t[1]}, {t[1]}, {L[1]}', f'adcs {t[2]}, {t[2]}, {L[2]}', f'adcs {t[3]}, {t[3]}, {L[3]}', f'adc {t[4]}, x10, x10']
        r += [f'umulh {L[k]}, x3, {BR[k]}' for k in range(4)]
        r += [f'adds {t[1]}, {t[1]}, {L[0]}', f'adcs {t[2]}, {t[2]}, {L[1]}', f'adcs {t[3]}, {t[3]}, {L[2]}', f'adc {t[4]}, {t[4]}, {L[3]}']
    return r + (foldR(W[:4], W[4:], o) if fold else [])
def rowP(a, w, t):
    """a * x12..x15 into w0..w4, with t0..t2 temporary."""
    return [f'ldr x3, [x0, #{a}]'] + [f'mul {w[k]}, x3, {BR[k]}' for k in range(4)] + [f'umulh {t[k]}, x3, {BR[k]}' for k in range(3)] + [f'umulh {w[4]}, x3, x15',
        f'adds {w[1]}, {w[1]}, {t[0]}', f'adcs {w[2]}, {w[2]}, {t[1]}', f'adcs {w[3]}, {w[3]}, {t[2]}', f'adc {w[4]}, {w[4]}, x10']
def mulT(o, a, b):
    T = ['x2','x8','x9']
    A, C = ['x4','x5','x6','x7','x21'], ['x16','x17','x20','x22','x23']
    r = ldb(b) + rowP(a, A, T) + rowP(a+8, C, T)
    # A + C << 64: words x4, x5, x6, x7, x21, x23
    r += ['adds x5, x5, x16', 'adcs x6, x6, x17', 'adcs x7, x7, x20', 'adcs x21, x21, x22', 'adc x23, x23, x10']
    # the second pair in x1 x11 x16 x17 x20 ; x22 x24 x2 x8 x9
    D = ['x1','x11','x16','x17','x20']
    r += ['ldr x3, [x0, #%d]' % (a+16)] + [f'mul {D[k]}, x3, {BR[k]}' for k in range(4)] + [f'umulh {k2}, x3, {BR[k]}' for k, k2 in enumerate(['x2','x8','x9'])] + ['umulh x20, x3, x15',
        'adds x11, x11, x2', 'adcs x16, x16, x8', 'adcs x17, x17, x9', 'adc x20, x20, x10']
    # S += D << 128 early: x6 x7 x21 x23 + new
    r += ['adds x6, x6, x1', 'adcs x7, x7, x11', 'adcs x21, x21, x16', 'adcs x23, x23, x17', 'adc x20, x20, x10']
    E = ['x1','x11','x16','x17','x24']
    r += ['ldr x3, [x0, #%d]' % (a+24)] + [f'mul {E[k]}, x3, {BR[k]}' for k in range(4)] + [f'umulh {k2}, x3, {BR[k]}' for k, k2 in enumerate(['x2','x8','x9'])] + ['umulh x24, x3, x15',
        'adds x11, x11, x2', 'adcs x16, x16, x8', 'adcs x17, x17, x9', 'adc x24, x24, x10',
        'adds x7, x7, x1', 'adcs x21, x21, x11', 'adcs x23, x23, x16', 'adcs x20, x20, x17', 'adc x24, x24, x10']
    return r + foldR(['x4','x5','x6','x7'], ['x21','x23','x20','x24'], o)
B['mulA'] = ['mov w10, #0'] + mulA(448, 320, 224)
B['mulA_dep'] = ['mov w10, #0'] + mulA(224, 224, 224)
B['mulT'] = ['mov w10, #0'] + mulT(448, 320, 224)
B['mulT_dep'] = ['mov w10, #0'] + mulT(224, 224, 224)

def minflags(body):
    """Flag writes that nothing reads before the next become plain operations."""
    READ = ('adcs','adc','sbcs','sbc','csel'); WRITE = ('adds','adcs','subs','sbcs','tst','cmp')
    out, live = [], False
    for l in reversed(body):
        op, _, r = l.partition(' ')
        w = op in WRITE
        if w and not live and op in ('adds','adcs','subs','sbcs'): op = op[:-1]
        elif w: live = False
        if op in READ: live = True
        out.append((op + ' ' + r).strip())
    return out[::-1]
def setters(b): return sum(l.split()[0] in ('adds','adcs','subs','sbcs','tst','cmp') for l in b)
B['step_min'] = ['mov w10, #0', 'mov x19, #100'] + minflags(S)
B['mul_min'] = ['mov w10, #0'] + minflags(mulx)
B['sqr_min'] = ['mov w10, #0'] + minflags(sqr)
B['mulA'] = minflags(B['mulA']); B['mulT'] = minflags(B['mulT'])
# the step's products as the tree
def retree(body):
    out, i = [], 0
    L = ['ldp x12, x13', 'ldp x14, x15', 'ldr x3']
    while i < len(body):
        m = [body[i+k].startswith(L[k]) for k in range(3)] if i + 3 < len(body) else [False]
        if all(m):
            b = int(body[i].split('#')[1][:-1]); a = int(body[i+2].split('#')[1][:-1])
            j = next(k for k in range(i, len(body)) if body[k].startswith('stp x4, x5')); o = int(body[j].split('#')[1][:-1])
            out += mulT(o, a, b); i = j + 2
        else: out.append(body[i]); i += 1
    return out
B['step_tree'] = ['mov w10, #0', 'mov x19, #100'] + minflags(retree(S))

W8 = ['x4','x5','x6','x7','x21','x22','x23','x24']
def sqrR(o, ext=True):
    """x12..x15 squared into [o] (o a list: registers kept in x4..x7)."""
    r = ['mul x5, x12, x13','mul x6, x12, x14','mul x7, x12, x15','umulh x2, x12, x13','umulh x8, x12, x14','umulh x9, x12, x15',
         'mul x16, x13, x14','mul x17, x13, x15','umulh x3, x13, x14','umulh x11, x13, x15','mul x20, x14, x15','umulh x23, x14, x15',
         'adds x6, x6, x2','adcs x7, x7, x8','adc x21, x9, x10',
         'adds x7, x7, x16','adcs x21, x21, x17','adc x22, x11, x10',
         'adds x21, x21, x3','adcs x22, x22, x20','adc x23, x23, x10']
    if ext: r += ['lsr x24, x23, #63','extr x23, x23, x22, #63','extr x22, x22, x21, #63','extr x21, x21, x7, #63','extr x7, x7, x6, #63','extr x6, x6, x5, #63','lsl x5, x5, #1']
    else: r += ['adds x5, x5, x5'] + [f'adcs {w}, {w}, {w}' for w in ('x6','x7','x21','x22','x23')] + ['adc x24, x10, x10']
    r += ['mul x4, x12, x12','umulh x2, x12, x12','mul x8, x13, x13','umulh x9, x13, x13','mul x16, x14, x14','umulh x17, x14, x14','mul x3, x15, x15','umulh x11, x15, x15',
          'adds x5, x5, x2','adcs x6, x6, x8','adcs x7, x7, x9','adcs x21, x21, x16','adcs x22, x22, x17','adcs x23, x23, x3','adc x24, x24, x11']
    return r + foldR(['x4','x5','x6','x7'], ['x21','x22','x23','x24'], o)
def ldw(o, rs): return [f'ldp {rs[0]}, {rs[1]}, [x0, #{o}]', f'ldp {rs[2]}, {rs[3]}, [x0, #{o+16}]']
def stw(o, rs): return [f'stp {rs[0]}, {rs[1]}, [x0, #{o}]', f'stp {rs[2]}, {rs[3]}, [x0, #{o+16}]']
R1, R2 = ['x4','x5','x6','x7'], ['x21','x22','x23','x24']
def add3(d, a, b): return [f'adds {d[0]}, {a[0]}, {b[0]}', f'adcs {d[1]}, {a[1]}, {b[1]}', 'mov w2, #38', f'adcs {d[2]}, {a[2]}, {b[2]}', f'adcs {d[3]}, {a[3]}, {b[3]}', 'csel x3, x2, x10, hs', f'adds {d[0]}, {d[0]}, x3', f'adcs {d[1]}, {d[1]}, x10', f'adc {d[2]}, {d[2]}, x10']
def sub4(d, a, b): return [f'subs {d[0]}, {a[0]}, {b[0]}', f'sbcs {d[1]}, {a[1]}, {b[1]}', 'mov w2, #38', f'sbcs {d[2]}, {a[2]}, {b[2]}', f'sbcs {d[3]}, {a[3]}, {b[3]}', 'csel x3, x10, x2, hs', f'subs {d[0]}, {d[0]}, x3', f'sbcs {d[1]}, {d[1]}, x10', f'sbcs {d[2]}, {d[2]}, x10', f'sbc {d[3]}, {d[3]}, x10']
def slot(n): return 64 + 32 * n
FR = minflags(S[:b0])
def step_order(order, ext=True):
    """order: names; E (E and AA + a24 E) is put where first needed."""
    D = ['x12','x13','x14','x15']
    def sq(o, a): return ldw(slot(a), D) + sqrR(slot(o), ext)
    ops = {
      'AA': lambda: sq(9, 5), 'BB': lambda: sq(10, 6), 'DA': lambda: mulA(slot(12), slot(8), slot(5)), 'CB': lambda: mulA(slot(13), slot(7), slot(6)),
      'E': lambda: ldw(slot(9), R1) + ldw(slot(10), R2) + sub4(D, R1, R2) + stw(slot(11), D),
      'x3': lambda: ldw(slot(12), R1) + ldw(slot(13), R2) + add3(D, R1, R2) + sqrR(slot(3), ext),
      't': lambda: ldw(slot(12), R1) + ldw(slot(13), R2) + sub4(D, R1, R2) + sqrR(slot(4), ext),
      'z3': lambda: mulA(slot(4), slot(0), slot(4)),
      'x2': lambda: mulA(slot(1), slot(9), slot(10)),
      'z2': lambda: ldw(slot(9), R1) + ldw(slot(11), D) + a24 + stw(slot(2), D) + mulA(slot(2), slot(11), slot(2)),
    }
    return sum((ops[k]() for k in order.split()), [])
ia = next(i for i, l in enumerate(S) if l.startswith('mov') and '56129' in l or l.startswith('movz x11, #') or ('0xdb41' in l))
ja = next(i for i in range(ia, len(S)) if S[i].startswith('adc x15'))
a24 = minflags(S[ia:ja+1])
ORD = {'o0': 'AA BB E DA CB x3 t z3 x2 z2', 'o1': 'DA CB AA BB t x3 z3 E x2 z2', 'o2': 'DA CB AA BB t x3 E x2 z3 z2', 'o3': 'AA BB DA CB E x2 z2 t x3 z3'}
for k, v in ORD.items(): B['st_' + k] = ['mov w10, #0', 'mov x19, #100'] + minflags(FR + step_order(v))
B['st_o1n'] = ['mov w10, #0', 'mov x19, #100'] + minflags(FR + step_order(ORD['o1'], False))
B['sqrR'] = ['mov w10, #0'] + ldw(224, ['x12','x13','x14','x15']) + minflags(sqrR(448))

# ---- radix 2^51 ----
def sl(n): return 64 + 40 * n
def ld5(o, r): return [f'ldp {r[0]}, {r[1]}, [x0, #{o}]', f'ldp {r[2]}, {r[3]}, [x0, #{o+16}]', f'ldr {r[4]}, [x0, #{o+32}]']
def st5(o, r): return [f'stp {r[0]}, {r[1]}, [x0, #{o}]', f'stp {r[2]}, {r[3]}, [x0, #{o+16}]', f'str {r[4]}, [x0, #{o+32}]']
B5 = ['x1','x2','x3','x4','x5']           # b
N5 = [None,'x6','x7','x8','x9']           # 19 b1..b4
LO = ['x10','x12','x14','x16','x20']; HI = ['x11','x13','x15','x17','x21']   # columns
AI, PL, PH = 'x22', 'x23', 'x24'
def carry51(o):
    """The columns reduced: two parallel rounds, into LO and [o]."""
    M_, C = 'x1', ['x2','x3','x4','x5','x6']
    r = ['mov x1, #0xffffffffffff', 'movk x1, #7, lsl #48'.replace('movk','movk')]
    r = ['mov x1, #0xffff', 'movk x1, #0xffff, lsl #16', 'movk x1, #0xffff, lsl #32', 'movk x1, #7, lsl #48', 'mov w7, #19']
    r += [f'extr {C[k]}, {HI[k]}, {LO[k]}, #51' for k in range(5)]
    r += [f'and {LO[k]}, {LO[k]}, x1' for k in range(5)]
    r += ['mul x6, x6, x7']
    r += [f'add {LO[k]}, {LO[k]}, {C[(k+4)%5]}' for k in range(5)]
    r += [f'lsr {C[k]}, {LO[k]}, #51' for k in range(5)]
    r += [f'and {LO[k]}, {LO[k]}, x1' for k in range(5)]
    r += ['mul x6, x6, x7']
    r += [f'add {LO[k]}, {LO[k]}, {C[(k+4)%5]}' for k in range(5)]
    return r + (st5(o, LO) if o is not None else [])
def mul51regs(a):
    """[a] times b (in B5): the columns."""
    r = ['mov w22, #19'] + [f'mul {N5[k]}, {B5[k]}, x22' for k in range(1, 5)]
    for i in range(5):
        r += [f'ldr {AI}, [x0, #{a+8*i}]']
        for j in range(5):
            c = (i + j) % 5; m = N5[j] if i + j >= 5 else B5[j]
            if i == 0: r += [f'mul {LO[c]}, {AI}, {m}', f'umulh {HI[c]}, {AI}, {m}']
            else: r += [f'mul {PL}, {AI}, {m}', f'umulh {PH}, {AI}, {m}', f'adds {LO[c]}, {LO[c]}, {PL}', f'adc {HI[c]}, {HI[c]}, {PH}']
    return r
def mul51(o, a, b): return ld5(b, B5) + mul51regs(a) + carry51(o)
def sqr51regs(o):
    """The square of B5."""
    a0, a1, a2, a3, a4 = B5
    r = ['mov w22, #19', f'add x6, {a0}, {a0}', f'add x7, {a1}, {a1}', f'mul x8, {a3}, x22', f'mul x9, {a4}, x22', 'add x24, x9, x9']
    # terms by column, first term sets
    T = [(0, a0, a0), (1, 'x6', a1), (2, 'x6', a2), (3, 'x6', a3), (4, 'x6', a4),
         (0, a1, 'x24'), (2, a1, a1), (3, 'x7', a2), (4, 'x7', a3),
         (1, a2, 'x24'), (4, a2, a2), (2, a3, 'x24'), (3, a4, 'x9'), (1, a3, 'x8'), (0, 'dbl', a2)]
    seen = set()
    for c, x, y in T:
        if x == 'dbl': r += ['add x8, x8, x8']; x = 'x8'
        if c not in seen: r += [f'mul {LO[c]}, {x}, {y}', f'umulh {HI[c]}, {x}, {y}']; seen.add(c)
        else: r += [f'mul x22, {x}, {y}', f'umulh x23, {x}, {y}', f'adds {LO[c]}, {LO[c]}, x22', f'adc {HI[c]}, {HI[c]}, x23']
    return r + carry51(o)
def sqr51(o, a): return ld5(a, B5) + sqr51regs(o)
P2 = ['x23', 'x24', 'x24', 'x24', 'x24']   # 2p's limbs: 2^52 - 38, 2^52 - 2
def p2(): return ['mov x24, #0xfffe', 'movk x24, #0xffff, lsl #16', 'movk x24, #0xffff, lsl #32', 'movk x24, #0xf, lsl #48', 'sub x23, x24, #36']
def st51():
    X2, Z2, X3, Z3 = 1, 2, 3, 4
    r = ['sub x19, x19, #1', 'add x17, x0, x19', 'ldrb w16, [x17, #1984]', 'ldrb w17, [x17, #1985]', 'eor x16, x16, x17', 'tst x16, x16'] + p2()
    # limb by limb: x2 z2 x3 z3 swapped; A = 5, B = 6, C = 7, D = 8
    for k in range(5):
        g = lambda n: f'[x0, #{sl(n)+8*k}]'
        r += [f'ldr x1, {g(X2)}', f'ldr x2, {g(Z2)}', f'ldr x3, {g(X3)}', f'ldr x4, {g(Z3)}',
              'csel x5, x3, x1, ne', 'csel x6, x4, x2, ne', 'csel x7, x1, x3, ne', 'csel x8, x2, x4, ne',
              'add x9, x5, x6', f'add x5, x5, {P2[k]}', 'sub x5, x5, x6', 'add x10, x7, x8', f'add x7, x7, {P2[k]}', 'sub x7, x7, x8',
              f'str x9, {g(5)}', f'str x5, {g(6)}', f'str x10, {g(7)}', f'str x7, {g(8)}']
    r += sqr51(sl(9), sl(5)) + sqr51(sl(10), sl(6)) + mul51(sl(8), sl(8), sl(5)) + mul51(sl(7), sl(7), sl(6))
    # E (slot 6) := AA - BB; AA + a24 E in B5 and then z2
    r += ld5(sl(9), B5) + ld5(sl(10), ['x6','x7','x8','x9','x10']) + p2()
    for k in range(5): r += [f'add {B5[k]}, {B5[k]}, {P2[k]}', f'sub {B5[k]}, {B5[k]}, {["x6","x7","x8","x9","x10"][k]}']
    r += st5(sl(6), B5) + mul51(sl(1), sl(9), sl(10))
    # x3 := (DA + CB)^2, t := (DA - CB)^2
    r += ld5(sl(8), B5) + ld5(sl(7), ['x6','x7','x8','x9','x10']) + [f'add {B5[k]}, {B5[k]}, {["x6","x7","x8","x9","x10"][k]}' for k in range(5)] + sqr51regs(sl(3))
    r += ld5(sl(8), B5) + ld5(sl(7), ['x6','x7','x8','x9','x10']) + p2()
    for k in range(5): r += [f'add {B5[k]}, {B5[k]}, {P2[k]}', f'sub {B5[k]}, {B5[k]}, {["x6","x7","x8","x9","x10"][k]}']
    r += sqr51regs(sl(4))
    # z2
    E = ['x20','x21','x22','x23','x24']; L, H, C = ['x6','x7','x8','x9','x10'], ['x11','x12','x13','x14','x15'], ['x6','x7','x8','x9','x10']
    r += ld5(sl(6), E) + ld5(sl(9), B5) + ['mov w16, #0xdb41', 'movk w16, #1, lsl #16', 'mov x17, #0xffff', 'movk x17, #0xffff, lsl #16', 'movk x17, #0xffff, lsl #32', 'movk x17, #7, lsl #48']
    r += [f'mul {L[k]}, {E[k]}, x16' for k in range(5)] + [f'umulh {H[k]}, {E[k]}, x16' for k in range(5)]
    r += [f'extr {H[k]}, {H[k]}, {L[k]}, #51' for k in range(5)] + [f'and {L[k]}, {L[k]}, x17' for k in range(5)] + ['mov w16, #19', 'mul x15, x15, x16']
    r += [f'add {B5[k]}, {B5[k]}, {L[k]}' for k in range(5)] + [f'add {B5[k]}, {B5[k]}, {H[(k+4)%5]}' for k in range(5)]
    r += mul51regs(sl(6)) + carry51(sl(2))
    # z3
    r += mul51(sl(4), sl(0), sl(4))
    return r
B['m51'] = mul51(448, 320, 224); B['m51_dep'] = mul51(224, 224, 224)
B['s51'] = sqr51(448, 224); B['s51_dep'] = sqr51(224, 224)
B['st51'] = ['mov x19, #100'] + st51()

# ---- NEON pairs, radix 2^51 ----
NS = {'x2': 16, 'z2': 64, 'x3': 112, 'z3': 160, 'A': 208, 'B': 256, 'C': 304, 'D': 352, 'AA': 400, 'BB': 448, 'x1': 560, 'E': 256, 'F': 208}
KM51, KM26, KM25, K19 = 704, 720, 736, 752      # constants: 2^51-1, 2^26-1, 2^25-1 (2d), 19 (4s)
VSP = 768                                        # vector spills
def v2(op, d, *r): return f'{op} v{d}.2d, ' + ', '.join(f'v{x}.2d' if isinstance(x, int) else x for x in r)
def vand(d, a, b): return f'and v{d}.16b, v{a}.16b, v{b}.16b'
def split(o1, o2, dst, t=(28, 29, 30), m=31):
    """The limbs of [o1], [o2] into dst[k] = [lo1, lo2, hi1, hi2]; m = mask26."""
    r = []
    a, b, c = t
    for k in (0, 2):
        r += [f'ldr q{a}, [x0, #{o1+8*k}]', f'ldr q{b}, [x0, #{o2+8*k}]', v2('trn1', c, a, b), v2('trn2', a, a, b)]
        for src, d in ((c, dst[k]), (a, dst[k+1])):
            r += [vand(b, src, m), v2('ushr', src, src, '#26'), f'uzp1 v{d}.4s, v{b}.4s, v{src}.4s']
    r += [f'ldr q{a}, [x0, #{o1+32}]', f'ldr q{b}, [x0, #{o2+32}]', v2('trn1', c, a, b), vand(b, c, m), v2('ushr', c, c, '#26'), f'uzp1 v{dst[4]}.4s, v{b}.4s, v{c}.4s']
    return r
def um(acc, d, a, b, hi):
    """d += a b (d = a b the first time)."""
    op = 'umlal' if d in acc else 'umull'; acc.add(d)
    s = '4s' if hi else '2s'
    return f"{op}{'2' if hi else ''} v{d}.2d, v{a}.{s}, v{b}.{s}"
def vreduce(E, X, o1, o2, t):
    """E[m] + 2^26 X[m], m < 5, reduced into [o1], [o2]; t: 6 temporaries."""
    a, b, c, m26, m25, m51 = t
    r = [f'ldr q{m26}, [x0, #{KM26}]', f'ldr q{m25}, [x0, #{KM25}]']
    # round 1: carries E_m -> X_m (26), X_m -> E_(m+1) (25), X_4 -> E_0 times 19
    r += [v2('ushr', c, X[4], '#25'), vand(X[4], X[4], m25)]
    r += [v2('ushr', a, E[4], '#26'), vand(E[4], E[4], m26), v2('add', X[4], X[4], a)]
    for m in (3, 2, 1, 0):
        r += [v2('ushr', b, X[m], '#25'), vand(X[m], X[m], m25), v2('add', E[m+1], E[m+1], b)]
        r += [v2('ushr', a, E[m], '#26'), vand(E[m], E[m], m26), v2('add', X[m], X[m], a)]
    r += [v2('add', E[0], E[0], c), v2('shl', a, c, '#1'), v2('shl', c, c, '#4'), v2('add', E[0], E[0], a), v2('add', E[0], E[0], c)]
    # limbs
    for m in range(5): r += [v2('shl', X[m], X[m], '#26'), v2('add', E[m], E[m], X[m])]
    r += [f'ldr q{m51}, [x0, #{KM51}]']
    for m in range(5): r += [v2('ushr', X[m], E[m], '#51'), vand(E[m], E[m], m51)]
    for m in range(1, 5): r += [v2('add', E[m], E[m], X[m-1])]
    r += [v2('add', E[0], E[0], X[4]), v2('shl', a, X[4], '#1'), v2('shl', c, X[4], '#4'), v2('add', E[0], E[0], a), v2('add', E[0], E[0], c)]
    for k in (0, 2): r += [v2('trn1', a, E[k], E[k+1]), v2('trn2', b, E[k], E[k+1]), f'str q{a}, [x0, #{o1+8*k}]', f'str q{b}, [x0, #{o2+8*k}]']
    # the fifth limbs, with the padding of the slots
    r += [v2('trn1', a, E[4], E[4]), v2('trn2', b, E[4], E[4]), f'str q{a}, [x0, #{o1+32}]', f'str q{b}, [x0, #{o2+32}]']
    return r
def mu2(o1, a1, b1, o2, a2, b2):
    Av, As, Bv, Bn = [0,1,2,3,4], [5,6,7,8,9], [10,11,12,13,14], [15,16,17,18,19]
    r = [f'ldr q31, [x0, #{KM26}]'] + split(a1, a2, Av) + split(b1, b2, Bv)
    r += [f'ext v{As[k]}.16b, v{Av[k]}.16b, v{Av[k]}.16b, #8' for k in range(5)]
    r += [f'ldr q31, [x0, #{K19}]'] + [f'mul v{Bn[k]}.4s, v{Bv[k]}.4s, v31.4s' for k in range(5)]
    E, X, H = [20,21,22,23,24], [25,26,27,28,29], [30,31]
    acc = set()
    # H_m (hi hi at m + 1) is summed first, doubled, and the lows added to it
    for m in range(5):
        for i in range(5):
            j = (m - 1 - i) % 5                 # hi hi with i + j + 1 = m (mod 5)
            r += [um(acc, E[m], Av[i], (Bn if i + j + 1 >= 5 else Bv)[j], True)]
        r += [v2('add', E[m], E[m], E[m])]
        for i in range(5):
            j = (m - i) % 5
            r += [um(acc, E[m], Av[i], (Bn if i + j >= 5 else Bv)[j], False)]
        for i in range(5):
            j = (m - i) % 5; b = (Bn if i + j >= 5 else Bv)[j]
            r += [um(acc, X[m], As[i], b, False), um(acc, X[m], As[i], b, True)]
    return r + vreduce(E, X, o1, o2, (0, 1, 2, 3, 4, 5))
def sq2(o1, a1, o2, a2):
    Av, As, Dv, N = [0,1,2,3,4], [5,6,7,8,9], [10,11,12,13,14], [15,16,17,18,19]   # a, a exchanged, 2a, 19a
    r = [f'ldr q31, [x0, #{KM26}]'] + split(a1, a2, Av)
    r += [f'ext v{As[k]}.16b, v{Av[k]}.16b, v{Av[k]}.16b, #8' for k in range(5)]
    r += [f'add v{Dv[k]}.4s, v{Av[k]}.4s, v{Av[k]}.4s' for k in range(5)]
    r += [f'ldr q31, [x0, #{K19}]'] + [f'mul v{N[k]}.4s, v{Av[k]}.4s, v31.4s' for k in range(5)]
    E, X = [20,21,22,23,24], [25,26,27,28,29]
    acc = set()
    for m in range(5):
        for i in range(5):
            j = (m - 1 - i) % 5
            if i > j: continue
            r += [um(acc, E[m], Av[i] if i == j else Dv[i], (N if i + j + 1 >= 5 else Av)[j], True)]
        r += [v2('add', E[m], E[m], E[m])]
        for i in range(5):
            j = (m - i) % 5
            if i > j: continue
            b = (N if i + j >= 5 else Av)[j]
            r += [um(acc, E[m], Av[i] if i == j else Dv[i], b, False)]
        for i in range(5):
            j = (m - i) % 5
            if i > j: continue
            b = (N if i + j >= 5 else Av)[j]
            # as_i [hi, lo] . b_j [lo, hi], doubled
            if i == j: r += [f'add v30.4s, v{As[i]}.4s, v{As[i]}.4s', um(acc, X[m], 30, b, False)]
            else: r += [f'add v30.4s, v{As[i]}.4s, v{As[i]}.4s', um(acc, X[m], 30, b, False), um(acc, X[m], 30, b, True)]
    return r + vreduce(E, X, o1, o2, (0, 1, 2, 3, 4, 5))
def weave(a, b):
    n, m, i, j, out = len(a), len(b), 0, 0, []
    while i < n and j < m:
        if i * m <= j * n: out.append(a[i]); i += 1
        else: out.append(b[j]); j += 1
    return out + a[i:] + b[j:]
def front_neon():
    r = ['sub x19, x19, #1', 'add x17, x0, x19', 'ldrb w16, [x17, #1984]', 'ldrb w17, [x17, #1985]', 'eor x16, x16, x17', 'tst x16, x16'] + p2()
    for k in range(5):
        g = lambda n: f'[x0, #{NS[n]+8*k}]'
        r += [f'ldr x1, {g("x2")}', f'ldr x2, {g("z2")}', f'ldr x3, {g("x3")}', f'ldr x4, {g("z3")}',
              'csel x5, x3, x1, ne', 'csel x6, x4, x2, ne', 'csel x7, x1, x3, ne', 'csel x8, x2, x4, ne',
              'add x9, x5, x6', f'add x5, x5, {P2[k]}', 'sub x5, x5, x6', 'add x10, x7, x8', f'add x7, x7, {P2[k]}', 'sub x7, x7, x8',
              f'str x9, {g("A")}', f'str x5, {g("B")}', f'str x10, {g("C")}', f'str x7, {g("D")}']
    return r
def vbranch():
    """AA, BB (NEON); E and AA + a24 E (NEON, limbs); x2, z2."""
    r = sq2(NS['AA'], NS['A'], NS['BB'], NS['B'])
    return r, mu2(NS['x2'], NS['AA'], NS['BB'], NS['z2'], NS['E'], NS['F'])
def mid():
    """E := AA - BB, F := AA + a24 E (scalar)."""
    O = ['x6','x7','x8','x9','x10']
    r = ld5(NS['AA'], B5) + ld5(NS['BB'], O) + p2()
    r += [x for k in range(5) for x in (f'add {O[k]}, {B5[k]}, x{23 if k == 0 else 24}'.replace(f'{B5[k]}, x', f'{B5[k]}, x') if False else f'sub {O[k]}, {B5[k]}, {O[k]}', f'add {O[k]}, {O[k]}, {P2[k]}')]
    r += [f'str {O[k]}, [x0, #{NS["E"]+8*k}]' for k in range(5)]
    H = ['x11','x12','x13','x14','x15']
    r += ['mov w16, #0xdb41', 'movk w16, #1, lsl #16', 'mov x17, #0xffff', 'movk x17, #0xffff, lsl #16', 'movk x17, #0xffff, lsl #32', 'movk x17, #7, lsl #48']
    r += [f'umulh {H[k]}, {O[k]}, x16' for k in range(5)] + [f'mul {O[k]}, {O[k]}, x16' for k in range(5)]
    r += [f'extr {H[k]}, {H[k]}, {O[k]}, #51' for k in range(5)] + [f'and {O[k]}, {O[k]}, x17' for k in range(5)] + ['mov w16, #19', 'mul x15, x15, x16']
    r += [f'add {B5[k]}, {B5[k]}, {O[k]}' for k in range(5)] + [f'add {B5[k]}, {B5[k]}, {H[(k+4)%5]}' for k in range(5)]
    return r + [f'str {B5[k]}, [x0, #{NS["F"]+8*k}]' for k in range(5)]
def sbranch():
    """DA, CB; then x3, t, z3 (scalar)."""
    DC = mul51(NS['D'], NS['D'], NS['A']) + mul51(NS['C'], NS['C'], NS['B'])
    O = ['x6','x7','x8','x9','x10']
    r = ld5(NS['D'], B5) + ld5(NS['C'], O) + [f'add {B5[k]}, {B5[k]}, {O[k]}' for k in range(5)] + sqr51regs(NS['x3'])
    r += ld5(NS['D'], B5) + ld5(NS['C'], O) + p2()
    for k in range(5): r += [f'add {B5[k]}, {B5[k]}, {P2[k]}', f'sub {B5[k]}, {B5[k]}, {O[k]}']
    r += sqr51regs(NS['z3'])
    return DC, r + mul51(NS['z3'], NS['x1'], NS['z3'])
def st_neon(wv=True):
    f = front_neon(); v1, v2_ = vbranch(); s1, s2 = sbranch()
    if wv: return f + weave(s1, v1) + mid() + weave(s2, v2_)
    return f + s1 + v1 + mid() + s2 + v2_
def ldstfix(b):
    """ldp/stp beyond their reach as two ldr/str."""
    out = []
    for l in b:
        m = __import__('re').match(r'(ld|st)p (x\d+), (x\d+), \[x0, #(\d+)\]', l)
        if m and int(m[4]) > 504 and False or (m and m[1] == 'ld' and int(m[4]) > 504): out += [f'{m[1]}r {m[2]}, [x0, #{m[4]}]', f'{m[1]}r {m[3]}, [x0, #{int(m[4])+8}]']
        else: out.append(l)
    return out
KC = ['mov x2, #0xffff','movk x2, #0xffff, lsl #16','movk x2, #0xffff, lsl #32','movk x2, #7, lsl #48','dup v0.2d, x2',f'str q0, [x0, #{KM51}]','lsr x3, x2, #25','dup v0.2d, x3',f'str q0, [x0, #{KM26}]','lsr x3, x2, #26','dup v0.2d, x3',f'str q0, [x0, #{KM25}]','mov x3, #19','lsl x4, x3, #32','add x3, x3, x4','dup v0.2d, x3',f'str q0, [x0, #{K19}]']
B['sq2'] = sq2(NS['AA'], NS['A'], NS['BB'], NS['B'])
B['mu2'] = mu2(NS['x2'], NS['A'], NS['B'], NS['z2'], NS['C'], NS['D'])
B['sn1'] = ldstfix(['mov x19, #100'] + st_neon()); B['sn0'] = ldstfix(['mov x19, #100'] + st_neon(False))

# ---- scheduled four-word steps ----
import slist as sched
def step_src(order):
    """The step (as step_order), the constants 19 and 38 in x26 and x27, the sums of DA and CB from one load."""
    D = ['x12','x13','x14','x15']
    ops = {
      'SD': lambda: ldw(slot(12), R1) + ldw(slot(13), R2) + add3(['x5n'] and ['x16','x17','x20','x24'], R1, R2)[:] ,
    }
    body = FR + step_order(order)
    out = []
    for l in minflags(body):
        if l in ('mov w11, #38', 'mov w11, #19', 'movz w11, #38, lsl #0', 'movz w11, #19, lsl #0', 'mov w2, #38', 'movz w2, #38, lsl #0'):
            out.append(l); continue
        out.append(l)
    # rename constants: uses of x11 / x2 after those movs
    res, c11, c2 = [], None, None
    for l in out:
        op, _, r = l.partition(' ')
        m = re_.match(r'(?:mov|movz) w(11|2), #(38|19)', l)
        if m:
            if m[1] == '11': c11 = 'x27' if m[2] == '38' else 'x26'
            else: c2 = 'x27'
            continue
        o = [x.strip() for x in r.split(',')]
        for c, name in ((c11, 'x11'), (c2, 'x2')):
            if c:
                st = 1 if op not in ('str', 'stp') else 0
                o = [(c if (x == name and q >= st) else x) for q, x in enumerate(o)]
        if op not in ('str','stp'):
            defs = o[:2] if op == 'ldp' else o[:1]
            if 'x11' in defs: c11 = None
            if 'x2' in defs: c2 = None
        res.append(op + ' ' + ', '.join(o))
    return res
import re as re_
SRC = step_src(ORD['o3'])
PRE = ['mov w10, #0', 'mov x19, #100', 'mov w26, #19', 'mov w27, #38']
B['src'] = PRE + SRC
REGS = [f'x{r}' for r in list(range(1, 10)) + list(range(11, 18)) + [20, 21, 22, 23, 24, 25, 28]]
for od in ('o1', 'o3'):
    for lim in (19, 21, 22):
        for W in (200, 120, 80, 50, 30, 15):
            for seed in (None, 1, 2):
                r = sched.schedule(step_src(ORD[od]), {0, 10, 19, 26, 27}, REGS, lim, 4.0, W=W, seed=seed)
                if r: B[f'sc_{od}_{lim}_{W}_{seed or 0}'] = PRE + r[0]

# ---- experiment 10 ----
def sumhalves(v, t=31): return [f'ext v{t}.16b, v{v}.16b, v{v}.16b, #8', f'add v{v}.4s, v{v}.4s, v{t}.4s']
def kar_tail(LL, HH, K, o1, o2):
    r = []
    for m in range(5): r += [v2('sub', K[m], K[m], LL[m]), v2('sub', K[m], K[m], HH[m])]
    for m in range(1, 5): r += [v2('add', LL[m], LL[m], HH[m-1]), v2('add', LL[m], LL[m], HH[m-1])]
    r += [v2('shl', 0, HH[4], '#1'), v2('shl', 1, HH[4], '#2'), v2('shl', 2, HH[4], '#5'), v2('add', LL[0], LL[0], 0), v2('add', 1, 1, 2), v2('add', LL[0], LL[0], 1)]
    return r + vreduce(LL, K, o1, o2, (0, 1, 2, 3, 4, 5))
def mu2k(o1, a1, b1, o2, a2, b2):
    A, Bv, Nn = [0,1,2,3,4], [5,6,7,8,9], [None,10,11,12,13]
    LL, HH, K = [14,15,16,17,18], [19,20,21,22,23], [24,25,26,27,28]
    r = [f'ldr q31, [x0, #{KM26}]'] + split(a1, a2, A) + split(b1, b2, Bv) + [f'ldr q31, [x0, #{K19}]'] + [f'mul v{Nn[k]}.4s, v{Bv[k]}.4s, v31.4s' for k in range(1, 5)]
    acc = set()
    for m in range(5):
        for i in range(5):
            j = (m - i) % 5; b = (Nn if i + j >= 5 else Bv)[j]
            r += [um(acc, LL[m], A[i], b, False), um(acc, HH[m], A[i], b, True)]
    for v in A + Bv + Nn[1:]: r += sumhalves(v)
    for m in range(5):
        for i in range(5):
            j = (m - i) % 5; r += [um(acc, K[m], A[i], (Nn if i + j >= 5 else Bv)[j], False)]
    return r + kar_tail(LL, HH, K, o1, o2)
def sq2k(o1, a1, o2, a2, pre=None):
    A, Dd, Nn = [0,1,2,3,4], [5,6,7,8], [None,9,10,11,12]
    LL, HH, K = [14,15,16,17,18], [19,20,21,22,23], [24,25,26,27,28]
    r = [f'ldr q31, [x0, #{KM26}]'] + (pre or split(a1, a2, A)) + [f'add v{Dd[k]}.4s, v{A[k]}.4s, v{A[k]}.4s' for k in range(4)] + [f'ldr q31, [x0, #{K19}]'] + [f'mul v{Nn[k]}.4s, v{A[k]}.4s, v31.4s' for k in range(1, 5)]
    acc = set()
    T = [[(i, (m - i) % 5) for i in range(5) if i <= (m - i) % 5] for m in range(5)]
    for m in range(5):
        for i, j in T[m]:
            a, b = (A if i == j else Dd)[i], (Nn if i + j >= 5 else A)[j]
            r += [um(acc, LL[m], a, b, False), um(acc, HH[m], a, b, True)]
    for v in A + Dd + Nn[1:]: r += sumhalves(v)
    for m in range(5):
        for i, j in T[m]: r += [um(acc, K[m], (A if i == j else Dd)[i], (Nn if i + j >= 5 else A)[j], False)]
    return r + kar_tail(LL, HH, K, o1, o2)
def front_p():
    """The front, two limbs at a time, stored by stp."""
    r = ['sub x19, x19, #1', 'add x17, x0, x19', 'ldrb w16, [x17, #1984]', 'ldrb w17, [x17, #1985]', 'eor x16, x16, x17', 'tst x16, x16'] + p2()
    for k in (0, 2, 4):
        n = 2 if k < 4 else 1
        g = lambda nm, e=0: f'[x0, #{NS[nm]+8*k+8*e}]'
        if n == 2: r += [f'ldp x1, x9, {g("x2")}', f'ldp x2, x10, {g("z2")}', f'ldp x3, x11, {g("x3")}', f'ldp x4, x12, {g("z3")}']
        else: r += [f'ldr x1, {g("x2")}', f'ldr x2, {g("z2")}', f'ldr x3, {g("x3")}', f'ldr x4, {g("z3")}']
        outs = []
        for e in range(n):
            x, z, u, v = ('x1','x2','x3','x4') if e == 0 else ('x9','x10','x11','x12')
            a, b, c, d = ('x5','x6','x7','x8') if e == 0 else ('x13','x14','x15','x16')
            r += [f'csel {a}, {u}, {x}, ne', f'csel {b}, {v}, {z}, ne', f'csel {c}, {x}, {u}, ne', f'csel {d}, {z}, {v}, ne',
                  f'add {x}, {a}, {b}', f'add {a}, {a}, {P2[k+e]}', f'sub {a}, {a}, {b}', f'add {z}, {c}, {d}', f'add {c}, {c}, {P2[k+e]}', f'sub {c}, {c}, {d}']
            outs.append((x, a, z, c))
        o2 = outs[1] if n == 2 else ('xzr',) * 4
        for q, nm in enumerate('ABCD'):
            w = 'x22' if n == 1 else o2[q]
            r += [f'stp {outs[0][q]}, {w}, {g(nm)}']
    return r
def mid_p():
    r = mid(); out = []
    for nm, regs in (('E', ['x6','x7','x8','x9','x10']), ('F', B5)):
        r = [l for l in r if not (l.startswith('str') and any(l.endswith(f'#{NS[nm]+8*k}]') for k in range(5)))] if False else r
    res = []
    for l in r:
        m = re_.match(r'str (x\d+), \[x0, #(\d+)\]', l)
        if m and int(m[2]) in (NS['E'], NS['E']+16, NS['E']+32, NS['F'], NS['F']+16, NS['F']+32): out = (m[1], int(m[2])); 
        if m:
            o = int(m[2]); base = NS['E'] if o < NS['F'] else NS['F']; k = (o - base) // 8
            if k in (0, 2): hold = m[1]; continue
            if k in (1, 3): res.append(f'stp {hold}, {m[1]}, [x0, #{o-8}]'); continue
            res.append(f'stp {m[1]}, {m[1]}, [x0, #{o}]'); continue
        res.append(l)
    return res
def sc_x3t_pre():
    """DA + CB and DA - CB, split, in v0..v4 (NEON), for the pair x3 | t."""
    A = [0,1,2,3,4]; r = [f'ldr q30, [x0, #{KP2A}]', f'ldr q29, [x0, #{KP2B}]']
    for k in (0, 2, 4):
        p = 30 if k == 0 else 29
        r += [f'ldr q20, [x0, #{NS["D"]+8*k}]', f'ldr q21, [x0, #{NS["C"]+8*k}]', v2('add', 22, 20, 21), v2('add', 20, 20, p), v2('sub', 20, 20, 21),
              v2('trn1', 23, 22, 20)] + ([v2('trn2', 24, 22, 20)] if k < 4 else [])
        for src, d in ((23, k), (24, k + 1)):
            if d > 4: continue
            r += [vand(25, src, 31), v2('ushr', src, src, '#26'), f'uzp1 v{A[d]}.4s, v25.4s, v{src}.4s']
    return r
KP2A, KP2B = 784, 800
KC += ['mov x2, #0xfffe','movk x2, #0xffff, lsl #16','movk x2, #0xffff, lsl #32','movk x2, #0xf, lsl #48','sub x3, x2, #36',f'stp x3, x2, [x0, #{KP2A}]' if False else f'str x3, [x0, #{KP2A}]',f'str x2, [x0, #{KP2A+8}]','dup v0.2d, x2',f'str q0, [x0, #{KP2B}]']
def st_n2(ka=True, pairs=True):
    f = front_p() if pairs else front_neon(); md = mid_p() if pairs else mid()
    sq, mu = (sq2k, mu2k) if ka else (sq2, mu2)
    s1, s2 = sbranch()
    return f + weave(s1, sq(NS['AA'], NS['A'], NS['BB'], NS['B'])) + md + weave(s2, mu(NS['x2'], NS['AA'], NS['BB'], NS['z2'], NS['E'], NS['F']))
def st_n3():
    s1, _ = sbranch()
    m51s = mid() + mul51(NS['x2'], NS['AA'], NS['BB']) + mul51(NS['z2'], NS['E'], NS['F'])
    return front_p() + weave(s1, sq2k(NS['AA'], NS['A'], NS['BB'], NS['B'])) + weave(m51s, sq2k(NS['x3'], None, NS['z3'], None, sc_x3t_pre())) + mul51(NS['z3'], NS['x1'], NS['z3'])
B['sq2k'] = sq2k(NS['AA'], NS['A'], NS['BB'], NS['B']); B['mu2k'] = mu2k(NS['x2'], NS['A'], NS['B'], NS['z2'], NS['C'], NS['D'])
B['sn2'] = ldstfix(['mov x19, #100'] + st_n2(False, True)); B['sn3'] = ldstfix(['mov x19, #100'] + st_n2(True, True)); B['sn4'] = ldstfix(['mov x19, #100'] + st_n3())

# ---- experiment 11: x25 = 2^51 - 1, x26 = 19, x27 = 2^52 - 2, x28 = 2^52 - 38 ----
KREG = ['mov x25, #0xffff','movk x25, #0xffff, lsl #16','movk x25, #0xffff, lsl #32','movk x25, #7, lsl #48','mov w26, #19','mov x27, #0xfffe','movk x27, #0xffff, lsl #16','movk x27, #0xffff, lsl #32','movk x27, #0xf, lsl #48','sub x28, x27, #36']
P2K = ['x28', 'x27', 'x27', 'x27', 'x27']
def carryK(o, seq):
    C = ['x2','x3','x4','x5','x6']
    if seq:
        r = []
        for k in range(4):
            r += [f'extr x2, {HI[k]}, {LO[k]}, #51', f'and {LO[k]}, {LO[k]}, x25', f'adds {LO[k+1]}, {LO[k+1]}, x2', f'adc {HI[k+1]}, {HI[k+1]}, x3']
            r[-1] = f'adc {HI[k+1]}, {HI[k+1]}, x3'
        r = ['mov w3, #0'] + r + [f'extr x2, {HI[4]}, {LO[4]}, #51', f'and {LO[4]}, {LO[4]}, x25', 'mul x2, x2, x26', f'add {LO[0]}, {LO[0]}, x2', f'lsr x2, {LO[0]}, #51', f'and {LO[0]}, {LO[0]}, x25', f'add {LO[1]}, {LO[1]}, x2']
        return r + st5(o, LO)
    r = [f'extr {C[k]}, {HI[k]}, {LO[k]}, #51' for k in range(5)] + [f'and {LO[k]}, {LO[k]}, x25' for k in range(5)] + ['mul x6, x6, x26'] + [f'add {LO[k]}, {LO[k]}, {C[(k+4)%5]}' for k in range(5)]
    r += [f'lsr {C[k]}, {LO[k]}, #51' for k in range(5)] + [f'and {LO[k]}, {LO[k]}, x25' for k in range(5)] + ['mul x6, x6, x26'] + [f'add {LO[k]}, {LO[k]}, {C[(k+4)%5]}' for k in range(5)]
    return r + st5(o, LO)
def mulK(o, a, b, seq=False):
    r = mul51regs(a)
    r = [l.replace('x22', 'x26') if l.startswith('mul x') and l.endswith('x22') and l.split()[1] in ('x6,','x7,','x8,','x9,') else l for l in r if l != 'mov w22, #19']
    return ld5(b, B5) + r + carryK(o, seq)
def midK():
    O = ['x6','x7','x8','x9','x10']; H = ['x11','x12','x13','x14','x15']
    r = ld5(NS['AA'], B5) + ld5(NS['BB'], O) + [x for k in range(5) for x in (f'sub {O[k]}, {B5[k]}, {O[k]}', f'add {O[k]}, {O[k]}, {P2K[k]}')] + st5(NS['E'], O)
    r += ['mov w16, #0xdb41', 'movk w16, #1, lsl #16'] + [f'umulh {H[k]}, {O[k]}, x16' for k in range(5)] + [f'mul {O[k]}, {O[k]}, x16' for k in range(5)]
    r += [f'extr {H[k]}, {H[k]}, {O[k]}, #51' for k in range(5)] + [f'and {O[k]}, {O[k]}, x25' for k in range(5)] + ['mul x15, x15, x26']
    return r + [f'add {B5[k]}, {B5[k]}, {O[k]}' for k in range(5)] + [f'add {B5[k]}, {B5[k]}, {H[(k+4)%5]}' for k in range(5)] + st5(NS['F'], B5)
def frontK():
    return [l for l in front_p()[:6]] + [l.replace('x23', 'x28').replace('x24', 'x27') for l in front_p()[6 + len(p2()):]]
def st_n6(sq, K, seq):
    if not K: 
        s1, _ = sbranch(); m2 = mid() + mul51(NS['x2'], NS['AA'], NS['BB']) + mul51(NS['z2'], NS['E'], NS['F']); last = mul51(NS['z3'], NS['x1'], NS['z3']); f = front_p()
    else:
        s1 = mulK(NS['D'], NS['D'], NS['A'], seq) + mulK(NS['C'], NS['C'], NS['B'], seq)
        m2 = midK() + mulK(NS['x2'], NS['AA'], NS['BB'], seq) + mulK(NS['z2'], NS['E'], NS['F'], seq); last = mulK(NS['z3'], NS['x1'], NS['z3'], seq); f = frontK()
    return f + weave(s1, sq(NS['AA'], NS['A'], NS['BB'], NS['B'])) + weave(m2, sq(NS['x3'], None, NS['z3'], None, sc_x3t_pre())) + last
def sq2(o1, a1, o2, a2, pre=None, _f=sq2):
    if pre is None: return _f(o1, a1, o2, a2)
    n = len([f'ldr q31'] + split(0, 0, [0,1,2,3,4])); r = _f(o1, 0, o2, 0)
    return r[:1] + pre + r[n:]
B['sn5'] = ldstfix(['mov x19, #100'] + st_n6(sq2, False, False))
B['sn6'] = ldstfix(['mov x19, #100'] + KREG + st_n6(sq2, True, False))
B['sn6k'] = ldstfix(['mov x19, #100'] + KREG + st_n6(sq2k, True, False))
B['sn7'] = ldstfix(['mov x19, #100'] + KREG + st_n6(sq2, True, True))

# ---- experiment 12: four-word scalar code, NEON pairs of squares ----
def split4(o1, o2, dst, m26=31, m25=30):
    """Four words each of [o1], [o2] into dst[k] = [lo1, lo2, hi1, hi2]; temporaries v20..v29."""
    r = [f'ldr q{m25}, [x0, #{KM25}]', f'ldr q20, [x0, #{o1}]', f'ldr q21, [x0, #{o2}]', f'ldr q22, [x0, #{o1+16}]', f'ldr q23, [x0, #{o2+16}]',
         v2('trn1', 24, 20, 21), v2('trn2', 25, 20, 21), v2('trn1', 26, 22, 23), v2('trn2', 27, 22, 23)]   # W0..W3
    r += [vand(20, 24, m26), v2('ushr', 21, 24, '#26'), vand(21, 21, m25), f'uzp1 v{dst[0]}.4s, v20.4s, v21.4s']
    r += [v2('shl', 20, 25, '#13'), v2('sri', 20, 24, '#51'), vand(20, 20, m26), v2('ushr', 21, 25, '#13'), vand(21, 21, m25), f'uzp1 v{dst[1]}.4s, v20.4s, v21.4s']
    r += [v2('ushr', 20, 25, '#38'), vand(21, 26, m25), f'uzp1 v{dst[2]}.4s, v20.4s, v21.4s']
    r += [v2('ushr', 20, 26, '#25'), vand(20, 20, m26), v2('shl', 21, 27, '#13'), v2('sri', 21, 26, '#51'), vand(21, 21, m25), f'uzp1 v{dst[3]}.4s, v20.4s, v21.4s']
    r += [v2('ushr', 20, 27, '#12'), vand(20, 20, m26), v2('ushr', 21, 27, '#38'), f'uzp1 v{dst[4]}.4s, v20.4s, v21.4s']
    return r
def pack(o, dst, rr=('x2','x3','x8','x9','x16','x17')):
    """The five limbs at [o] as four words in dst (and x11 a temporary)."""
    a, b, c, d, e, t = rr
    r = [f'ldp {a}, {b}, [x0, #{o}]', f'ldp {c}, {d}, [x0, #{o+16}]', f'ldr {e}, [x0, #{o+32}]']
    r += [f'lsl {t}, {b}, #51', f'adds {dst[0]}, {a}, {t}', f'lsr {b}, {b}, #13', f'lsl {t}, {c}, #38', f'adcs {dst[1]}, {b}, {t}', f'lsr {c}, {c}, #26', f'lsl {t}, {d}, #25', f'adcs {dst[2]}, {c}, {t}',
          f'lsr {d}, {d}, #39', f'lsl {t}, {e}, #12', f'adc {dst[3]}, {d}, {t}']
    return r
VO1, VO2 = 1024, 1072
def sq2_4(a1, a2, o1, o2): return sq2(o1, None, o2, None, split4(a1, a2, [0,1,2,3,4]))
def x3t_pre4(d, c):
    """DA + CB and DA - CB + 4p of the four-word [d], [c], as limb vectors (an operand < 2^28)."""
    r = split4(d, c, [0,1,2,3,4])      # [d_lo, c_lo, d_hi, c_hi]
    r += [f'ldr q28, [x0, #{KP4A}]', f'ldr q29, [x0, #{KP4B}]']
    for k in range(5):
        # s = [d + c, d - c + 4p]: [d, d] + [c, -c]
        r += [f'trn1 v20.4s, v{k}.4s, v{k}.4s', f'trn2 v21.4s, v{k}.4s, v{k}.4s', 'add v22.4s, v20.4s, v21.4s', f'add v20.4s, v20.4s, v{28 if k == 0 else 29}.4s', 'sub v20.4s, v20.4s, v21.4s', f'trn1 v{k}.4s, v22.4s, v20.4s']
    return r
KP4A, KP4B = 816, 832
def lo_hi(x): return (x & (2**26-1), x >> 26)
_p4 = [4 * (2**51 - 19)] + [4 * (2**51 - 1)] * 4
# 4p with every limb large: lo part 2 x 2^27.., as [lo, lo, hi, hi] with lo = 4 (2^26 - 1), hi = 4 (2^25 - 1), lo_0 = 4 (2^26 - 19)
def kq(lo, hi): return lo | lo << 32 | hi << 64 | hi << 96
def setq(off, v):
    r = []
    for h in range(2):
        w = v >> 64 * h & 2**64 - 1
        r += [f'mov x2, #{w & 0xffff}'] + [f'movk x2, #{w >> 16*j & 0xffff}, lsl #{16*j}' for j in (1, 2, 3)] + [f'str x2, [x0, #{off+8*h}]']
    return r
KC += setq(KP4A, kq(2*(2**26-19), 2*(2**25-1))) + setq(KP4B, kq(2*(2**26-1), 2*(2**25-1)))
def h_step(s1, rest, pair2=False):
    Dr = ['x12','x13','x14','x15']
    def sq(o, a): return ldw(slot(a), Dr) + sqrR(slot(o), True)
    ops = {'DA': lambda: mulA(slot(12), slot(8), slot(5)), 'CB': lambda: mulA(slot(13), slot(7), slot(6)),
      'P': lambda: pack(VO1, R1) + stw(slot(9), R1) + pack(VO2, R2) + stw(slot(10), R2),
      'E': lambda: sub4(Dr, R1, R2) + stw(slot(11), Dr),
      'x3': lambda: ldw(slot(12), R1) + ldw(slot(13), R2) + add3(Dr, R1, R2) + sqrR(slot(3)),
      't': lambda: ldw(slot(12), R1) + ldw(slot(13), R2) + sub4(Dr, R1, R2) + sqrR(slot(4)),
      'z3': lambda: mulA(slot(4), slot(0), slot(4)), 'x2': lambda: mulA(slot(1), slot(9), slot(10)),
      'z2': lambda: ldw(slot(9), R1) + ldw(slot(11), Dr) + a24 + stw(slot(2), Dr) + mulA(slot(2), slot(11), slot(2)),
      'P3': lambda: pack(VO1, R1) + stw(slot(3), R1) + pack(VO2, R2) + stw(slot(4), R2)}
    go = lambda t: minflags(sum((ops[k]() for k in t.split()), []))
    r = FR + weave(go(s1), sq2_4(slot(5), slot(6), VO1, VO2))
    if pair2:
        a, b = rest
        return r + weave(go(a), sq2(VO1 + 96, None, VO2 + 96, None, x3t_pre4(slot(12), slot(13)))) + [l.replace(f'#{VO1}', f'#{VO1+96}').replace(f'#{VO1+16}', f'#{VO1+112}').replace(f'#{VO1+32}', f'#{VO1+128}') for l in []] + go_p3(ops, go, b)
    return r + go(rest)
def go_p3(ops, go, b):
    return minflags(pack(VO1 + 96, R1) + stw(slot(3), R1) + pack(VO2 + 96, R2) + stw(slot(4), R2) + go(b))
H0 = ['mov w10, #0', 'mov x19, #100']
B['h1'] = H0 + h_step('DA CB', 'P E x2 z2 t x3 z3'); B['h1b'] = H0 + h_step('DA CB', 't x3 P E z3 x2 z2')
B['h2'] = H0 + h_step('DA CB t', 'P E x3 x2 z2 z3'); B['h3'] = H0 + h_step('DA CB t x3', 'P E z3 x2 z2')
B['h4'] = H0 + h_step('DA CB', ('P E x2 z2', 'z3'), True)
for k in ('h1','h1b','h2','h3','h4'): B[k] = ldstfix([l for l in B[k]])
def fixldp(b):
    out = []
    for l in b:
        m = re_.match(r'(ld|st)p (x\d+), (x\d+), \[x0, #(\d+)\]', l)
        if m and int(m[4]) > 504: out += [f'{m[1]}r {m[2]}, [x0, #{m[4]}]', f'{m[1]}r {m[3]}, [x0, #{int(m[4])+8}]']
        else: out.append(l)
    return out
for k in ('h1','h1b','h2','h3','h4'): B[k] = fixldp(B[k])

# ---- experiment 13 ----
def consts(body):
    """19 and 38 in x26 and x27 (as step_src)."""
    res, c11, c2 = [], None, None
    for l in body:
        op, _, r = l.partition(' ')
        m = re_.match(r'(?:mov|movz) w(11|2), #(38|19)', l)
        if m:
            if m[1] == '11': c11 = 'x27' if m[2] == '38' else 'x26'
            else: c2 = 'x27'
            continue
        if re_.match(r'.*[vq]\d', l): res.append(l); continue
        o = [x.strip() for x in r.split(',')]
        for c, name in ((c11, 'x11'), (c2, 'x2')):
            if c:
                st = 1 if op not in ('str', 'stp') else 0
                o = [(c if (x == name and q >= st) else x) for q, x in enumerate(o)]
        if op not in ('str','stp'):
            defs = o[:2] if op == 'ldp' else o[:1]
            if 'x11' in defs: c11 = None
            if 'x2' in defs: c2 = None
        res.append(op + ' ' + ', '.join(o))
    return res
def weave_f(a, b, num, den):
    """weave with b (the vector block) taken num / den times as fast."""
    n, m, i, j, out = len(a), len(b), 0, 0, []
    while i < n and j < m:
        if i * m * num <= j * n * den: out.append(a[i]); i += 1
        else: out.append(b[j]); j += 1
    return out + a[i:] + b[j:]
def h13(s1, rest, num=1, den=1, kar=False, c=True, mulf=None):
    Dr = ['x12','x13','x14','x15']
    ml = mulf or mulA
    ops = {'DA': lambda: ml(slot(12), slot(8), slot(5)), 'CB': lambda: ml(slot(13), slot(7), slot(6)),
      'P': lambda: pack(VO1, R1) + stw(slot(9), R1) + pack(VO2, R2) + stw(slot(10), R2), 'E': lambda: sub4(Dr, R1, R2) + stw(slot(11), Dr),
      'x3': lambda: ldw(slot(12), R1) + ldw(slot(13), R2) + add3(Dr, R1, R2) + sqrR(slot(3), False if kar == 'n' else True),
      't': lambda: ldw(slot(12), R1) + ldw(slot(13), R2) + sub4(Dr, R1, R2) + sqrR(slot(4), False if kar == 'n' else True),
      'z3': lambda: ml(slot(4), slot(0), slot(4)), 'x2': lambda: ml(slot(1), slot(9), slot(10)),
      'z2': lambda: ldw(slot(9), R1) + ldw(slot(11), Dr) + a24 + stw(slot(2), Dr) + ml(slot(2), slot(11), slot(2))}
    go = lambda t: (consts if c else (lambda x: x))(minflags(sum((ops[k]() for k in t.split()), [])))
    v = sq2k(VO1, None, VO2, None, split4(slot(5), slot(6), [0,1,2,3,4])) if kar is True else sq2_4(slot(5), slot(6), VO1, VO2)
    return fixldp((consts(FR) if c else FR) + weave_f(go(s1), v, num, den) + go(rest))
H1 = H0 + ['mov w26, #19', 'mov w27, #38']
V13 = {'a': ('DA CB t', 'P E x3 x2 z2 z3'), 'b': ('DA CB t', 'x3 P E x2 z3 z2'), 'c': ('DA CB t', 'x3 P E z3 x2 z2'), 'd': ('DA CB t', 'z3 P E x2 z2 x3'), 'e': ('DA CB t', 'P E x2 x3 z2 z3'),
       'f': ('DA CB t', 'P E z3 x2 x3 z2'), 'g': ('DA CB x3', 'P E t x2 z2 z3'), 'h': ('DA CB x3', 'P E t x2 z3 z2'), 'i': ('DA CB t', 'P E x2 z2 x3 z3'), 'j': ('DA CB t', 'P E x3 x2 z3 z2')}
for k, (u, w) in V13.items(): B['t' + k] = H1 + h13(u, w)
B['ta32'] = H1 + h13(*V13['a'], 3, 2); B['ta43'] = H1 + h13(*V13['a'], 4, 3); B['ta2'] = H1 + h13(*V13['a'], 2, 1); B['tak'] = H1 + h13(*V13['a'], kar=True); B['tan'] = H1 + h13(*V13['a'], kar='n')
B['tj43'] = H1 + h13(*V13['j'], 4, 3); B['tf43'] = H1 + h13(*V13['f'], 4, 3)

# ---- experiment 14: the emitted step's operations in other orders ----
S2 = [l.strip() for l in open(pathlib.Path(__file__).parent / 'step2.s')]
def blocks2():
    # each operation ends with its stp of the last two words of its slot
    ends = []; last = 0; out = {}
    names = ['AA', 'BB', 'DA', 'CB', 'E', 'x2', 'z2', 't', 'x3', 'z3']; slots = [9, 10, 12, 13, 11, 1, 2, 4, 3, 4]
    b = next(k for k, l in enumerate(S2) if l == f'ldp x12, x13, [x0, #{slot(5)}]')
    fr = S2[:b]; pos = b
    for n, o in zip(names, slots):
        e = next(k for k in range(pos, len(S2)) if S2[k].startswith('stp') and S2[k].endswith(f'[x0, #{slot(o)+16}]')) + 1
        out[n] = S2[pos:e]; pos = e
    assert pos == len(S2), S2[pos:]
    return fr, out
FR2, OPS2 = blocks2()
DEP = {'AA': '', 'BB': '', 'DA': '', 'CB': '', 'E': 'AA BB', 'x2': 'AA BB', 'z2': 'AA E', 't': 'DA CB', 'x3': 'DA CB', 'z3': 't x3'}
DEP = {k: v.split() for k, v in DEP.items()}; DEP['z3'] = ['t']; DEP['x3'] = ['DA', 'CB']
import random as rnd_
def rand_order(r):
    left = list(DEP); out = []
    while left:
        c = [k for k in left if all(d in out for d in DEP[k])]; k = r.choice(c); out.append(k); left.remove(k)
    # gap rule: nothing right after what it needs, if possible
    bad = sum(out[i] in DEP[out[i+1]] for i in range(9)); return bad, out
_r = rnd_.Random(7); ORDS = []
while len(ORDS) < 24:
    bad, o = rand_order(_r)
    if bad <= 1 and o[-1] not in ('E',) and o not in ORDS: ORDS.append(o)
B['r_now'] = H0 + S2
for q, o in enumerate(ORDS): B[f'r{q}'] = H0 + FR2 + sum((OPS2[k] for k in o), [])

# ---- experiment 15 ----
_e = OPS2['E'][4:]
def OP15(k): return (pack(VO1, ['x4','x5','x6','x7']) + stw(slot(9), ['x4','x5','x6','x7']) + pack(VO2, ['x21','x22','x23','x24']) + stw(slot(10), ['x21','x22','x23','x24']) + _e) if k == 'PE' else OPS2[k]
_cd = next(k for k, l in enumerate(FR2) if l == f'ldp x21, x22, [x0, #{slot(4)}]')
def s15(w, rest, early=False):
    go = lambda t: sum((OP15(k) for k in t.split()), [])
    v = sq2_4(slot(5), slot(6), VO1, VO2)
    if early: return H0 + fixldp(FR2[:_cd] + weave(FR2[_cd:] + go(w), v) + go(rest))
    return H0 + fixldp(FR2 + weave(go(w), v) + go(rest))
for k, (w, r_) in {'a': ('DA CB t', 'PE x3 x2 z2 z3'), 'b': ('DA CB t', 'PE x2 x3 z2 z3'), 'c': ('DA CB x3', 'PE t x2 z2 z3'), 'd': ('DA CB t', 'PE x2 z2 x3 z3'),
    'e': ('DA CB t x3', 'PE x2 z2 z3'), 'f': ('DA CB t', 'PE z3 x2 x3 z2'), 'g': ('DA CB t', 'x3 PE z3 x2 z2'), 'h': ('DA CB x3', 'PE x2 t z2 z3'), 'i': ('DA CB t', 'PE x3 z2 x2 z3'),'j': ('DA CB', 'PE x3 t x2 z3 z2')}.items():
    B['u' + k] = s15(w, r_)
for k in 'ace': pass
B['va'] = s15('DA CB t', 'PE x3 x2 z2 z3', True); B['vb'] = s15('DA CB t', 'PE x2 x3 z2 z3', True); B['vc'] = s15('DA CB x3', 'PE t x2 z2 z3', True); B['ve'] = s15('DA CB t x3', 'PE x2 z2 z3', True); B['vj'] = s15('DA CB', 'PE x3 t x2 z3 z2', True)
if __name__ == '__main__':
    open(pathlib.Path(__file__).parent / 'orders.txt', 'w').write('\n'.join(f'r{q} ' + ' '.join(o) for q, o in enumerate(ORDS)))
    for k in ('step','step_min','step_tree','mul','mul_min','mulA','mulT','sqr','sqr_min','sqrR','st_o0','st_o1','m51','s51','st51','sq2','mu2','sn1','src','sq2k','mu2k','sn3','sn4','sn5','sn6','sn7','h1','h3','h4') + tuple(k for k in B if k.startswith('sc_')): print(k, len(B[k]), setters(B[k]))
ALL = dict(B)
KEEP = sys.argv[1].split() if len(sys.argv) > 1 else None
if KEEP: B = {k: v for k, v in B.items() if k in KEEP}
out = ['//! Lab.', 'use criterion::{BenchmarkId, Criterion};', 'use crate::{BenchDyn, VG};', 'pub const USES: &[&str] = &["x25519"];']
asm = []
for n, body in B.items():
    asm.append(f'.p2align 6\n.globl lab_{n}\nlab_{n}:\nstp x19, x20, [sp, #-160]!\nstp x21, x22, [sp, #16]\nstp x23, x24, [sp, #32]\nstp x25, x26, [sp, #48]\nstp x27, x28, [sp, #136]\nstp d8, d9, [sp, #64]\nstp d10, d11, [sp, #80]\nstp d12, d13, [sp, #96]\nstp d14, d15, [sp, #112]\n'
      'str x1, [sp, #128]\nmov x2, #12345\nmovk x2, #54321, lsl #48\nmov x3, #777\nmovk x3, #999, lsl #32\n2:\n' + '\n'.join(body) +
      '\nldr x25, [sp, #128]\nsub x25, x25, #1\nstr x25, [sp, #128]\ncbnz x25, 2b\nldp d8, d9, [sp, #64]\nldp d10, d11, [sp, #80]\nldp d12, d13, [sp, #96]\nldp d14, d15, [sp, #112]\nldp x25, x26, [sp, #48]\nldp x27, x28, [sp, #136]\nldp x23, x24, [sp, #32]\nldp x21, x22, [sp, #16]\nldp x19, x20, [sp], #160\nret\n')
out.append('core::arch::global_asm!(r"' + '\n'.join(asm) + '");')
out.append('unsafe extern "C" {\n' + ''.join(f'fn lab_{n}(p: *mut u64, n: u64);' for n in B) + '}')
out.append('pub fn bench(c: &mut Criterion) { let mut buf = vec![0x1234_5678_9abc_def1u64; 2048]; let p = buf.as_mut_ptr();')
for n in B:
    out.append(f'let mut g = c.benchmark_group("lab_{n}"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe {{ lab_{n}(p, 100) }})); g.finish();')
out.append('}')
open(pathlib.Path(__file__).parent.parent / 'bench/benches/primitives/lab.rs', 'w').write('\n'.join(out))
