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
        r += row(c1, a1, b1, i, 2048); r += row(c2, a2, b2, i, 2080)
        if i: c1 = c1[1:] + c1[:1]; c2 = c2[1:] + c2[:1]
    return r, c1, c2
def pairfull(o1, a1, b1, o2, a2, b2):
    r, c1, c2 = pair(o1, a1, b1, o2, a2, b2)
    return r + fold(c1, 2048, o1) + fold(c2, 2080, o2)
B['pair'] = ['mov w10, #0'] + pairfull(448, 320, 224, 480, 256, 288)
B['pair_dep'] = ['mov w10, #0'] + pairfull(224, 224, 224, 256, 256, 256)
def seqpair(o1, a1, b1, o2, a2, b2):
    r = []
    for o, a, b in ((o1, a1, b1), (o2, a2, b2)):
        c = ['x4','x5','x6','x7']
        for i in range(4):
            r += row(c, a, b, i, 2048)
            if i: c = c[1:] + c[:1]
        r += fold(c, 2048, o)
    return r
B['seqpair'] = ['mov w10, #0'] + seqpair(448, 320, 224, 480, 256, 288)
B['seqpair_dep'] = ['mov w10, #0'] + seqpair(224, 224, 224, 256, 256, 256)
ALL = dict(B)
KEEP = sys.argv[1].split() if len(sys.argv) > 1 else None
if KEEP: B = {k: v for k, v in B.items() if k in KEEP}
out = ['//! Lab.', 'use criterion::{BenchmarkId, Criterion};', 'use crate::{BenchDyn, VG};', 'pub const USES: &[&str] = &["x25519"];']
asm = []
for n, body in B.items():
    asm.append(f'.p2align 6\n.globl lab_{n}\nlab_{n}:\nstp x19, x20, [sp, #-96]!\nstp x21, x22, [sp, #16]\nstp x23, x24, [sp, #32]\nstp x25, x26, [sp, #48]\nstp d8, d9, [sp, #64]\n'
      'mov x25, x1\nmov x2, #12345\nmovk x2, #54321, lsl #48\nmov x3, #777\nmovk x3, #999, lsl #32\n2:\n' + '\n'.join(body) +
      '\nsub x25, x25, #1\ncbnz x25, 2b\nldp d8, d9, [sp, #64]\nldp x25, x26, [sp, #48]\nldp x23, x24, [sp, #32]\nldp x21, x22, [sp, #16]\nldp x19, x20, [sp], #96\nret\n')
out.append('core::arch::global_asm!(r"' + '\n'.join(asm) + '");')
out.append('unsafe extern "C" {\n' + ''.join(f'fn lab_{n}(p: *mut u64, n: u64);' for n in B) + '}')
out.append('pub fn bench(c: &mut Criterion) { let mut buf = vec![0x1234_5678_9abc_def1u64; 2048]; let p = buf.as_mut_ptr();')
for n in B:
    out.append(f'let mut g = c.benchmark_group("lab_{n}"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe {{ lab_{n}(p, 100) }})); g.finish();')
out.append('}')
open(pathlib.Path(__file__).parent.parent / 'bench/benches/primitives/lab.rs', 'w').write('\n'.join(out))
