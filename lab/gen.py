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
