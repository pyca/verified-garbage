//! Local check of Proto22 (bench branch only): ROMix with four-doubleword copy and XOR steps
//! gives main's ROMix on random blocks, for several r and N.
#![cfg(target_arch = "riscv64")]
use verified_garbage_asm_riscv64::scrypt_proto22::*;

type RoMix = unsafe extern "C" fn(*mut u8, usize, *mut u8, usize, *mut u8, *mut u64);

fn run(f: RoMix, r: usize, n: usize, seed: u64) -> Vec<u64> {
    let mut b = vec![0u64; 16 * r];
    let mut x = seed;
    for w in b.iter_mut() {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        *w = x;
    }
    let mut v = vec![0u64; 16 * r * n];
    let mut t = vec![0u64; 16 * r];
    let mut save = vec![0u64; 32];
    unsafe { f(b.as_mut_ptr().cast(), r, v.as_mut_ptr().cast(), n * r, t.as_mut_ptr().cast(), save.as_mut_ptr()) };
    b
}

#[test]
fn same_as_base() {
    for r in [1usize, 2, 3, 8] {
        for n in [2usize, 4, 16, 64, 1024] {
            for seed in [1u64, 0x1234_5678_9abc_def1, u64::MAX] {
                assert_eq!(run(vg_p22_romix_base, r, n, seed), run(vg_p22_romix_u4, r, n, seed), "r={r} n={n}");
            }
        }
    }
}
