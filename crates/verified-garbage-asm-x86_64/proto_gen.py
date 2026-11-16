#!/usr/bin/env python3
"""Generates the PROTOTYPE AVX2 X25519 ladder (measurement only)."""
import sys, re, subprocess
CRATE = sys.argv[1]
SQR = '--nosqr' not in sys.argv

# ---- working-space slots (32 bytes each), from 1024 ----
_slots = {}
def slot(name, k=0):
    if name in ('Q', 'S'): name = 'F'
    key = (name, k)
    if key not in _slots:
        _slots[key] = 1024 + 32 * len(_slots)
    return _slots[key]
def m(name, k=0): return f"YMMWORD PTR [rdi+{slot(name,k)}]"
for n in ['F', 'C13', 'C1X']:
    for k in range(10): slot(n, k)
for n in ['K19', 'K38', 'M26', 'M25', 'KA24', 'K4D', 'KIU', 'KIV', 'M13']: slot(n)

out = []
def e(s): out.append('\t' + s)
def y(i): return f"ymm{i}"

def carry():
    if '--parcarry' not in sys.argv: return carry_seq()
    # five chains at once, three rounds: evens -> odds, odds -> evens, evens -> odds
    def rnd(src):
        w = 26 if src[0] % 2 == 0 else 25
        mk = m('M26' if w == 26 else 'M25')
        for n, a in enumerate(src):
            t = 10 + n
            e(f"vpsrlq {y(t)}, {y(a)}, {w}")
            e(f"vpand {y(a)}, {y(a)}, {mk}")
        for n, a in enumerate(src):
            t = 10 + n; b = (a + 1) % 10
            if b == 0:
                e(f"vpaddq ymm0, ymm0, {y(t)}")
                e(f"vpsllq ymm15, {y(t)}, 1")
                e(f"vpsllq {y(t)}, {y(t)}, 4")
                e("vpaddq ymm0, ymm0, ymm15")
                e(f"vpaddq ymm0, ymm0, {y(t)}")
            else:
                e(f"vpaddq {y(b)}, {y(b)}, {y(t)}")
    rnd([0, 2, 4, 6, 8]); rnd([1, 3, 5, 7, 9]); rnd([0, 2, 4, 6, 8])
    e(f"vmovdqu ymm15, {m('M13')}")

def carry_seq():
    def cy(a, b):
        w = 26 if a % 2 == 0 else 25
        e(f"vpsrlq ymm10, {y(a)}, {w}")
        e(f"vpand {y(a)}, {y(a)}, {m('M26' if w == 26 else 'M25')}")
        if b == 0:
            e("vpsllq ymm11, ymm10, 1")
            e("vpaddq ymm0, ymm0, ymm10")
            e("vpsllq ymm10, ymm10, 4")
            e("vpaddq ymm0, ymm0, ymm11")
            e("vpaddq ymm0, ymm0, ymm10")
        else:
            e(f"vpaddq {y(b)}, {y(b)}, ymm10")
    for a, b in [(0,1),(4,5),(1,2),(5,6),(2,3),(6,7),(3,4),(7,8),(4,5),(8,9),(9,0),(0,1)]:
        cy(a, b)

def mul(pre):
    """h (ymm0-9) = [F] * [G] (with [G19]); with `pre`, added to what ymm0-9 hold."""
    started = [pre] * 10
    for i in range(10):
        e(f"vmovdqu ymm10, {m('F', i)}")
        if i % 2 == 1:
            e("vpaddq ymm11, ymm10, ymm10")
        for j in range(10):
            k = (i + j) % 10
            f = "ymm11" if (i % 2 == 1 and j % 2 == 1) else "ymm10"
            g = m('G19', j) if i + j >= 10 else m('G', j)
            if started[k]:
                e(f"vpmuludq ymm12, {f}, {g}")
                e(f"vpaddq {y(k)}, {y(k)}, ymm12")
            else:
                e(f"vpmuludq {y(k)}, {f}, {g}")
                started[k] = True

def mulx(mode):
    for i in range(10):
        e(f"vmovdqu ymm10, {m('F', i)}")
        if i % 2 == 1: e("vpaddq ymm11, ymm10, ymm10")
        for j in range(10):
            k = (i + j) % 10
            f = "ymm11" if (i % 2 == 1 and j % 2 == 1) else "ymm10"
            g = m('G19', j) if i + j >= 10 else m('G', j)
            if mode == 0:   # multiplies only
                e(f"vpmuludq ymm12, {f}, {g}")
            elif mode == 1: # multiplies only, register operands
                e(f"vpmuludq ymm12, {f}, ymm13")
            elif mode == 2: # separate load
                e(f"vmovdqu ymm13, {g}")
                e(f"vpmuludq ymm12, {f}, ymm13")
                e(f"vpaddq {y(k)}, {y(k)}, ymm12")

def v(name):
    # variant name -> memory operand
    mm = re.fullmatch(r'f(\d)(_2|_19|_38)?', name)
    k = int(mm.group(1)); suf = mm.group(2)
    return m({None: 'Q', '_2': 'Q2', '_19': 'QX', '_38': 'QX'}[suf], k)

SQ = [
 ('f0_2', [('f1',1),('f2',2),('f3',3),('f4',4),('f5',5),('f6',6),('f7',7),('f8',8),('f9',9)]),
 ('f1_2', [('f1',2),('f2',3),('f3_2',4),('f4',5),('f5_2',6),('f6',7),('f7_2',8),('f8',9),('f9_38',0)]),
 ('f2_2', [('f3',5),('f4',6),('f5',7),('f6',8),('f7',9),('f8_19',0)]),
 ('f3_2', [('f3',6),('f4',7),('f5_2',8),('f6',9),('f7_38',0),('f8_19',1),('f9_38',2)]),
 ('f4_2', [('f5',9),('f6_19',0),('f8_19',2)]),
 ('f5_2', [('f6_19',1),('f7_38',2),('f8_19',3),('f9_38',4)]),
 ('f6_2', [('f8_19',4)]),
 ('f7_2', [('f8_19',5),('f9_38',6)]),
 ('f0', [('f0',0)]), ('f2', [('f2',4),('f9_38',1)]), ('f4', [('f4',8),('f7_38',1),('f9_38',3)]),
 ('f5', [('f5_38',0)]), ('f6', [('f6_19',2),('f7_38',3),('f9_38',5)]), ('f7', [('f7_38',4)]),
 ('f8', [('f8_19',6),('f9_38',7)]), ('f9', [('f9_38',8)])]
assert sum(len(r) for _, r in SQ) == 55

def sqr():
    started = [False] * 10
    for a, row in SQ:
        e(f"vmovdqu ymm10, {v(a)}")
        for b, k in row:
            if started[k]:
                e(f"vpmuludq ymm12, ymm10, {v(b)}")
                e(f"vpaddq {y(k)}, {y(k)}, ymm12")
            else:
                e(f"vpmuludq {y(k)}, ymm10, {v(b)}")
                started[k] = True

def step():
    e("sub rbx, 1")
    e("movzx eax, BYTE PTR [rdi+rbx*1+768]")
    e("mov rdx, QWORD PTR [rdi+640]")
    e("xor rdx, rax")
    e("mov QWORD PTR [rdi+640], rax")
    e("mov ecx, 0")
    e("sub rcx, rdx")
    e("vmovq xmm15, rcx")
    e("vpbroadcastq ymm15, xmm15")
    e(f"vpand ymm15, ymm15, {m('K4D')}")
    e(f"vpxor ymm14, ymm15, {m('KIU')}")
    e(f"vpxor ymm13, ymm15, {m('KIV')}")
    e(f"vmovdqu ymm15, {m('M13')}")
    # stage 1: H = (x2+z2, z2-x2, x3+z3, z3-x3); F = perm1 H, G = perm2 H
    for k in range(10):
        e(f"vpshufd ymm10, {y(k)}, 78")
        e("vpxor ymm10, ymm10, ymm15")
        e(f"vpaddq ymm11, {y(k)}, {m('C13', k)}")
        e("vpaddq ymm10, ymm10, ymm11")
        e("vpermd ymm11, ymm14, ymm10")
        e(f"vmovdqu {m('F', k)}, ymm11")
        e("vpermd ymm12, ymm13, ymm10")
        e(f"vmovdqu {m('G', k)}, ymm12")
        if k:
            e(f"vpmuludq ymm12, ymm12, {m('K19')}")
            e(f"vmovdqu {m('G19', k)}, ymm12")
    mul(False)
    carry()
    # P = (AA, BB, DA, CB) in ymm0-9. t = (BB, AA, CB, DA); Gq = (AA+BB, E, S, Dd)
    for k in range(10):
        e(f"vpshufd ymm10, {y(k)}, 78")
        e(f"vpxor ymm11, {y(k)}, ymm15")
        e(f"vpaddq ymm11, ymm11, {m('C13', k)}")
        e("vpaddq ymm11, ymm11, ymm10")
        if SQR:
            e(f"vmovdqu {m('Q', k)}, ymm11")
            if k <= 7:
                e("vpaddq ymm12, ymm11, ymm11")
                e(f"vmovdqu {m('Q2', k)}, ymm12")
            if k >= 5:
                e(f"vpmuludq ymm12, ymm11, {m('K38' if k % 2 else 'K19')}")
                e(f"vmovdqu {m('QX', k)}, ymm12")
            # U = (AA, E, ., .)
            e(f"vpblendd ymm12, {y(k)}, ymm11, 12")
            e(f"vmovdqu {m('U', k)}, ymm12")
            # W = (BB, BB, 1, x1)
            e(f"vpblendd ymm10, ymm10, {y(k)}, 12")
            e(f"vpblendd ymm10, ymm10, {m('C1X', k)}, 240")
            e(f"vmovdqu {m('G', k)}, ymm10")
            if k:
                e(f"vpmuludq ymm10, ymm10, {m('K19')}")
                e(f"vmovdqu {m('G19', k)}, ymm10")
        else:
            raise SystemExit("nosqr not implemented")
    sqr()
    carry()
    # R = (., E^2, x3', t) in ymm0-9
    for k in range(10):
        e(f"vpblendd ymm10, {y(k)}, {m('U', k)}, 15")
        e(f"vmovdqu {m('F', k)}, ymm10")
        e(f"vpmuludq {y(k)}, {y(k)}, {m('KA24')}")
    mul(True)
    carry()

e("push rbx")
for k in range(10): e(f"vmovdqu {y(k)}, {m('S', k)}")
e("mov ebx, 255")
out.append("21:")
EXP = [a.split('=')[1] for a in sys.argv if a.startswith('--exp=')]
if EXP:
    e("sub rbx, 1")
    for c in EXP[0]:
        {'x': lambda: mulx(0), 'y': lambda: mulx(1), 'z': lambda: mulx(2), 'm': lambda: mul(False), 'M': lambda: mul(True), 'c': carry, 's': sqr}[c]()
else:
    step()
e("test rbx, rbx")
e("jne 21b")
for k in range(10): e(f"vmovdqu {m('S', k)}, {y(k)}")
e("vzeroall")
e("pop rbx")
e("ret")
loop_asm = '\n'.join(out)
n_step = sum(1 for l in out if l.startswith('\tv'))
print("vector instructions per step (approx):", n_step - 21, file=sys.stderr)
print("slots end:", 1024 + 32 * len(_slots), file=sys.stderr)
assert 1024 + 32 * len(_slots) <= 4096

if '--standalone' in sys.argv:
    open('loop.S','w').write('.intel_syntax noprefix\n.text\n.globl ladder_loop\nladder_loop:\n'+loop_asm+'\n')
    sys.exit(0)
# ---- wrappers from the generated code's text ----
src = open(f'{CRATE}/assembly/internal/vg_x25519_ifma.s').read().split('\n')
body = src[7:88] + ['\tpush rdi', '\tpush rsi', '\tpush rsi', '\tcall {ladder}', '\tpop rsi', '\tpop rsi',
                    '\tpop rdi', '\txor ebx, ebx'] + src[778:]
body = '\n'.join(body).rstrip()
ex = open(f'{CRATE}/assembly/x25519.s').read().split('\n')
i = ex.index('vg_x25519_exchange_adx:'); j = ex.index('vg_x25519_exchange:')
exb = '\n'.join(ex[i + 1:j]).rstrip().replace('{vg_x25519_adx}', '{inner}')

def off(name, k=0): return slot(name, k)
rust = f'''//! PROTOTYPE, unverified, for measurement only (bench/ branch): an AVX2 4-way
//! Montgomery ladder for X25519, radix 2^25.5. Generated by proto_gen.py.
#![allow(clippy::all, unsafe_op_in_unsafe_fn, missing_docs)]

const X1: usize = 64;
const X2: usize = 96;
const OFF: [u32; 10] = [0, 26, 51, 77, 102, 128, 153, 179, 204, 230];
const WID: [u32; 10] = [26, 25, 26, 25, 26, 25, 26, 25, 26, 25];

const fn p2(k: usize) -> u64 {{
    if k == 0 {{ (1 << 27) - 38 }} else if k % 2 == 0 {{ (1 << 27) - 2 }} else {{ (1 << 26) - 2 }}
}}

fn pack(l: [u64; 10]) -> [u64; 4] {{
    let mut w = [0u64; 5];
    for k in 0..10 {{
        let v = (l[k] as u128) << (OFF[k] % 64);
        let i = (OFF[k] / 64) as usize;
        let (s, c) = w[i].overflowing_add(v as u64);
        w[i] = s;
        let mut carry = (v >> 64) as u64 + c as u64;
        let mut j = i + 1;
        while carry != 0 && j < 5 {{
            let (s, c) = w[j].overflowing_add(carry);
            w[j] = s;
            carry = c as u64;
            j += 1;
        }}
    }}
    [w[0], w[1], w[2], w[3]]
}}

unsafe fn put(ws: *mut u8, off: usize, v: [u64; 4]) {{
    core::ptr::write_unaligned(ws.add(off) as *mut [u64; 4], v);
}}

pub unsafe extern "sysv64" fn vg_proto_ladder_avx2(ws: *mut u8) {{
    let x1w = core::ptr::read_unaligned(ws.add(X1) as *const [u64; 4]);
    let big = (x1w[0] as u128) | ((x1w[1] as u128) << 64);
    let big2 = (x1w[2] as u128) | ((x1w[3] as u128) << 64);
    let limb = |k: usize| -> u64 {{
        let o = OFF[k];
        let v: u128 = if o < 128 {{
            let lo = big >> o;
            if o == 0 {{ lo }} else {{ lo | (big2 << (128 - o)) }}
        }} else {{
            big2 >> (o - 128)
        }};
        v as u64 & ((1u64 << WID[k]) - 1)
    }};
    for k in 0..10 {{
        let one = if k == 0 {{ 1 }} else {{ 0 }};
        put(ws, {off('S')} + 32 * k, [one, 0, limb(k), one]);
        put(ws, {off('C1X')} + 32 * k, [0, 0, one, limb(k)]);
        put(ws, {off('C13')} + 32 * k, [0, p2(k) + 1, 0, p2(k) + 1]);
    }}
    put(ws, {off('K19')}, [19; 4]);
    put(ws, {off('K38')}, [38; 4]);
    put(ws, {off('M26')}, [(1 << 26) - 1; 4]);
    put(ws, {off('M25')}, [(1 << 25) - 1; 4]);
    put(ws, {off('KA24')}, [0, 121666, 0, 0]);
    put(ws, {off('K4D')}, [0x0000000400000004; 4]);
    put(ws, {off('KIU')}, [0x0000000100000000, 0x0000000300000002, 0x0000000700000006, 0x0000000500000004]);
    put(ws, {off('KIV')}, [0x0000000100000000, 0x0000000300000002, 0x0000000100000000, 0x0000000300000002]);
    put(ws, {off('M13')}, [0, !0, 0, !0]);
    ladder_loop(ws);
    let mut l = [[0u64; 10]; 4];
    for k in 0..10 {{
        let tmp = core::ptr::read_unaligned(ws.add({off('S')} + 32 * k) as *const [u64; 4]);
        for lane in 0..4 {{
            l[lane][k] = tmp[lane];
        }}
    }}
    for lane in 0..4 {{
        put(ws, X2 + 32 * lane, pack(l[lane]));
    }}
}}

#[unsafe(naked)]
unsafe extern "sysv64" fn ladder_loop(ws: *mut u8) {{
    core::arch::naked_asm!(
        r#"{loop_asm}"#,
    )
}}

#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_x25519_avx2p() {{
    core::arch::naked_asm!(
        r#"{body}"#,
        ladder = sym vg_proto_ladder_avx2,
        vg_gf25519_r64_invert = sym crate::ed25519::vg_gf25519_r64_invert::vg_gf25519_r64_invert,
    )
}}

#[unsafe(naked)]
pub(crate) unsafe extern "sysv64" fn vg_x25519_exchange_avx2p(out: *mut [u8; 32], scalar: *const [u8; 32], point: *const [u8; 32], scratch: *mut [u64; 512]) -> u32 {{
    core::arch::naked_asm!(
        r#"{exb}"#,
        inner = sym vg_x25519_avx2p,
    )
}}
'''
open(f'{CRATE}/src/proto_avx2.rs', 'w').write(rust)
