//! Prototype check (bench branch only): Proto17's two-row multiplication and squarings give
//! the results of main's `tail` and `sqrTail` (even `w`), and leave `a6`, `a7` where they must.
#![cfg(target_arch = "riscv64")]
use verified_garbage_asm_riscv64::rsa_proto17 as p17;

type F = unsafe extern "C" fn(*mut u64, usize, usize);

fn setup(w: usize, seed: u64) -> Vec<u64> {
    let mut ws = vec![0u64; 32 + 8 * (w + 2) + 8];
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
fn p17_matches_main() {
    let mut cases = 0;
    for w in (2usize..=64).step_by(2) {
        let s8 = 8 * (w as u64 + 2);
        for seed in 1..7u64 {
            for count in [1usize, 3] {
                let ws0 = setup(w, seed * 1000 + w as u64);
                let b = run(p17::vg_p17_mul_base, &ws0, w, count);
                let t = run(p17::vg_p17_mul_two, &ws0, w, count);
                assert_ne!(out(&b, w), out(&ws0, w), "mul did nothing w={w}");
                assert_eq!(
                    out(&t, w),
                    out(&b, w),
                    "mul two w={w} seed={seed} count={count}"
                );
                assert_eq!(regs(&t, w), (s8, 2 * s8), "mul two regs w={w}");
                let sb = run(p17::vg_p17_sqr_base, &ws0, w, count);
                let st = run(p17::vg_p17_sqr_two, &ws0, w, count);
                assert_eq!(
                    out(&st, w),
                    out(&sb, w),
                    "sqr two w={w} seed={seed} count={count}"
                );
                assert_eq!(regs(&st, w), regs(&sb, w), "sqr two regs w={w}");
                let sm = run(p17::vg_p17_sqr_bymul, &ws0, w, count);
                assert_eq!(
                    out(&sm, w),
                    out(&sb, w),
                    "sqr by mul w={w} seed={seed} count={count}"
                );
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 32 * 6 * 2);
}
