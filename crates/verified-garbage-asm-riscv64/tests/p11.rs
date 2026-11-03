//! Prototype check (bench branch only): every variant gives the baseline's result, and
//! leaves `a6` and `a7` where `tail` and `sqrTail` must.
#![cfg(target_arch = "riscv64")]
use verified_garbage_asm_riscv64::rsa_proto11 as p11;

type F = unsafe extern "C" fn(*mut u64, usize, usize);

fn setup(w: usize, seed: u64) -> Vec<u64> {
    let mut ws = vec![0u64; 32 + 8 * (w + 2) + 8];
    let mut x = seed;
    let mut r = || { x ^= x << 13; x ^= x >> 7; x ^= x << 17; x };
    let st = w + 2;
    for i in 0..w { ws[32 + i] = r(); }
    ws[32] |= 1;
    ws[32 + w - 1] |= 1 << 63;
    let m0 = ws[32];
    let mut y = m0;
    for _ in 0..6 { y = y.wrapping_mul(2u64.wrapping_sub(m0.wrapping_mul(y))); }
    ws[7] = y.wrapping_neg();
    for i in 0..w { ws[32 + 5 * st + i] = r(); ws[32 + 6 * st + i] = ws[32 + 5 * st + i]; }
    ws[32 + 5 * st + w - 1] >>= 1; ws[32 + 6 * st + w - 1] >>= 1;
    // Garbage past each array's `w` words, which the variants read and must ignore.
    for j in [0usize, 5, 6] { ws[32 + j * st + w] = r(); ws[32 + j * st + w + 1] = r(); }
    ws
}

fn out(ws: &[u64], w: usize) -> Vec<u64> { let st = w + 2; ws[32 + 5 * st..32 + 5 * st + w].to_vec() }

fn regs(ws: &[u64], w: usize) -> (u64, u64) { let st = w + 2; (ws[32 + 7 * st + 3], ws[32 + 7 * st + 4]) }

#[test]
fn variants_match_base() {
    let muls: [F; 2] = [p11::vg_p11_mul_p, p11::vg_p11_mul_po];
    let sqrs: [F; 1] = [p11::vg_p11_sqr_p];
    for w in 2usize..=64 {
        let s8 = 8 * (w as u64 + 2);
        for seed in 1..4u64 {
            for count in [1usize, 3] {
                let ws0 = setup(w, seed * 1000 + w as u64);
                let mut b = ws0.clone();
                unsafe { p11::vg_p11_mul_base(b.as_mut_ptr(), w, count) };
                let mut s = ws0.clone();
                unsafe { p11::vg_p11_sqr_base(s.as_mut_ptr(), w, count) };
                assert_ne!(out(&b, w), out(&ws0, w), "mul did nothing w={w}");
                assert_eq!(regs(&b, w), (s8, 2 * s8), "mul base regs w={w}");
                assert_eq!(regs(&s, w), (2 * s8, 2 * s8), "sqr base regs w={w}");
                if count == 1 { assert_eq!(out(&b, w), out(&s, w), "sqr vs mul w={w}"); }
                for f in muls {
                    let mut v = ws0.clone(); unsafe { f(v.as_mut_ptr(), w, count) };
                    assert_eq!(out(&v, w), out(&b, w), "mul w={w}");
                    assert_eq!(regs(&v, w), (s8, 2 * s8), "mul regs w={w}");
                }
                for f in sqrs {
                    let mut v = ws0.clone(); unsafe { f(v.as_mut_ptr(), w, count) };
                    assert_eq!(out(&v, w), out(&s, w), "sqr w={w}");
                    assert_eq!(regs(&v, w), (2 * s8, 2 * s8), "sqr regs w={w}");
                    if count == 1 { assert_eq!(out(&v, w), out(&b, w), "sqr_p vs mul w={w}"); }
                }
            }
        }
    }
}
