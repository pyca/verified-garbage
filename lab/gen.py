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
if __name__ == '__main__':
    for k in ('step','step_min','step_tree','mul','mul_min','mulA','mulT','sqr','sqr_min','sqrR','st_o0','st_o1','m51','s51','st51'): print(k, len(B[k]), setters(B[k]))
ALL = dict(B)
KEEP = sys.argv[1].split() if len(sys.argv) > 1 else None
if KEEP: B = {k: v for k, v in B.items() if k in KEEP}
out = ['//! Lab.', 'use criterion::{BenchmarkId, Criterion};', 'use crate::{BenchDyn, VG};', 'pub const USES: &[&str] = &["x25519"];']
asm = []
for n, body in B.items():
    asm.append(f'.p2align 6\n.globl lab_{n}\nlab_{n}:\nstp x19, x20, [sp, #-96]!\nstp x21, x22, [sp, #16]\nstp x23, x24, [sp, #32]\nstp x25, x26, [sp, #48]\nstp d8, d9, [sp, #64]\n'
      'mov x25, x1\nmov x26, x1\nmov x2, #12345\nmovk x2, #54321, lsl #48\nmov x3, #777\nmovk x3, #999, lsl #32\n2:\n' + '\n'.join(body) +
      '\nsub x25, x25, #1\ncbnz x25, 2b\nldp d8, d9, [sp, #64]\nldp x25, x26, [sp, #48]\nldp x23, x24, [sp, #32]\nldp x21, x22, [sp, #16]\nldp x19, x20, [sp], #96\nret\n')
out.append('core::arch::global_asm!(r"' + '\n'.join(asm) + '");')
out.append('unsafe extern "C" {\n' + ''.join(f'fn lab_{n}(p: *mut u64, n: u64);' for n in B) + '}')
out.append('pub fn bench(c: &mut Criterion) { let mut buf = vec![0x1234_5678_9abc_def1u64; 2048]; let p = buf.as_mut_ptr();')
for n in B:
    out.append(f'let mut g = c.benchmark_group("lab_{n}"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe {{ lab_{n}(p, 100) }})); g.finish();')
out.append('}')
open(pathlib.Path(__file__).parent.parent / 'bench/benches/primitives/lab.rs', 'w').write('\n'.join(out))
