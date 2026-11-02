//! Prototype check (bench branch only): every variant gives the baseline's result.
#![cfg(target_arch = "riscv64")]
use verified_garbage_asm_riscv64::rsa_proto7 as p7;

type F = unsafe extern "C" fn(*mut u64, usize, usize);

fn setup(w: usize, seed: u64) -> Vec<u64> {
    let mut ws = vec![0u64; 32 + 8 * (w + 2)];
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
    ws
}

fn out(ws: &[u64], w: usize) -> Vec<u64> { let st = w + 2; ws[32 + 5 * st..32 + 5 * st + w].to_vec() }

#[test]
fn variants_match_base() {
    let muls: [F; 5] = [p7::vg_p7_mul_f, p7::vg_p7_mul_u8, p7::vg_p7_mul_fu8, p7::vg_p7_mul_c, p7::vg_p7_mul_cu8];
    let sqrs: [F; 5] = [p7::vg_p7_sqr_f, p7::vg_p7_sqr_u8, p7::vg_p7_sqr_fu8, p7::vg_p7_sqr_c, p7::vg_p7_sqr_cu8];
    for w in [2usize, 3, 4, 5, 6, 7, 8, 9, 13, 16, 17, 24, 31, 32, 33, 48, 64] {
        for seed in 1..4u64 {
            for count in [1usize, 3] {
                let ws0 = setup(w, seed * 1000 + w as u64);
                let mut b = ws0.clone();
                unsafe { p7::vg_p7_mul_base(b.as_mut_ptr(), w, count) };
                let mut s = ws0.clone();
                unsafe { p7::vg_p7_sqr_base(s.as_mut_ptr(), w, count) };
                if count == 1 { assert_eq!(out(&b, w), out(&s, w), "sqr vs mul w={w}"); }
                for f in muls { let mut v = ws0.clone(); unsafe { f(v.as_mut_ptr(), w, count) }; assert_eq!(out(&v, w), out(&b, w), "mul w={w}"); }
                for f in sqrs { let mut v = ws0.clone(); unsafe { f(v.as_mut_ptr(), w, count) }; assert_eq!(out(&v, w), out(&s, w), "sqr w={w}"); }
            }
        }
    }
}

#[test]
fn micro_runs() {
    let mut ws = setup(4, 1);
    for f in [p7::vg_p7_k_mul, p7::vg_p7_k_fused, p7::vg_p7_k_pair, p7::vg_p7_k_mulhu, p7::vg_p7_k_add] {
        unsafe { f(ws.as_mut_ptr(), 3, 10) };
    }
}
