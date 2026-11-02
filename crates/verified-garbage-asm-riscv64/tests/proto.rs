//! Prototype check (bench branch only): sqr(a) == mul(a, a) under the same modulus.
#![cfg(target_arch = "riscv64")]
use verified_garbage_asm_riscv64::rsa_proto::{vg_proto_mont_mul, vg_proto_mont_sqr};

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

#[test]
fn sqr_matches_mul() {
    for w in [8usize, 16, 17, 32, 33, 64] {
        let mut a = setup(w, 1 + w as u64);
        let mut b = a.clone();
        let st = w + 2;
        // mul: o=5 a=5 b=6 with array 6 = array 5: a square.
        unsafe { vg_proto_mont_mul(a.as_mut_ptr(), w, 1) };
        unsafe { vg_proto_mont_sqr(b.as_mut_ptr(), w, 1) };
        assert_eq!(&a[32 + 5 * st..32 + 5 * st + w], &b[32 + 5 * st..32 + 5 * st + w], "w = {w}");
    }
}
