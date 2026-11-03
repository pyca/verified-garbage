//! Prototype check (bench branch only): Proto25's one-level Karatsuba squaring gives
//! main's `sqrTail` result (even `w` from 4 to 64).
#![cfg(target_arch = "riscv64")]
use verified_garbage_asm_riscv64::rsa_proto25::*;

type F = unsafe extern "C" fn(*mut u64, usize, usize);

fn setup(w: usize, seed: u64) -> Vec<u64> {
    let mut ws = vec![0u64; 32 + 12 * (w + 2) + 8];
    let mut x = seed;
    let mut r = || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    };
    let st = w + 2;
    for i in 0..w {
        ws[32 + i] = r();
    }
    ws[32] |= 1;
    if seed % 2 == 0 {
        ws[32 + w - 1] |= 1 << 63;
    } else {
        ws[32 + w - 1] >>= 3;
        ws[32 + w - 1] |= 1;
    }
    let m0 = ws[32];
    let mut y = m0;
    for _ in 0..6 {
        y = y.wrapping_mul(2u64.wrapping_sub(m0.wrapping_mul(y)));
    }
    ws[7] = y.wrapping_neg();
    for i in 0..w {
        ws[32 + 5 * st + i] = r();
        ws[32 + 6 * st + i] = r();
    }
    // Below m: clear the top bits of both operands.
    ws[32 + 5 * st + w - 1] >>= 4;
    ws[32 + 6 * st + w - 1] >>= 4;
    if seed % 3 == 0 {
        // All ones below m's top word, to stress the carries.
        for i in 0..w - 1 {
            ws[32 + 5 * st + i] = u64::MAX;
            ws[32 + 6 * st + i] = u64::MAX;
        }
    }
    for j in [0usize, 5, 6] {
        ws[32 + j * st + w] = r();
        ws[32 + j * st + w + 1] = r();
    }
    ws
}

fn out(ws: &[u64], w: usize) -> Vec<u64> {
    let st = w + 2;
    ws[32 + 5 * st..32 + 5 * st + w].to_vec()
}

fn regs(ws: &[u64], w: usize) -> (u64, u64) {
    let st = w + 2;
    (ws[32 + 7 * st + 3], ws[32 + 7 * st + 4])
}

fn run(f: F, ws0: &[u64], w: usize, count: usize) -> Vec<u64> {
    let mut v = ws0.to_vec();
    unsafe { f(v.as_mut_ptr(), w, count) };
    v
}

#[test]
fn kara_sqr_matches_main() {
    let mut n = 0;
    for w in (4..=64).step_by(2) {
        for seed in 0..4u64 {
            let ws0 = setup(w, seed + 1000 * w as u64);
            for count in [1usize, 3] {
                let a = run(vg_p25_sqr_base, &ws0, w, count);
                let b = run(vg_p25_sqr_kara, &ws0, w, count);
                assert_eq!(out(&a, w), out(&b, w), "w={w} seed={seed} count={count}");
                n += 1;
            }
        }
    }
    eprintln!("{n} comparisons");
}
