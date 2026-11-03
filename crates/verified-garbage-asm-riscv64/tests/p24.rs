//! Local check of Proto24 (bench branch only): vg_rsa_private_crt with windows of 4, 5 and
//! 6 bits gives main's result on Wycheproof's keys (`key_cases.txt`).
#![cfg(target_arch = "riscv64")]
use verified_garbage_asm_riscv64::rsa_proto24::*;

fn hex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

type Crt = unsafe extern "C" fn(
    *mut u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *mut u64,
    usize,
) -> u32;

fn run(f: Crt, g: &[Vec<u8>], input: &[u8]) -> (u32, Vec<u8>) {
    let k = g[0].len();
    let mut out = vec![0u8; k];
    let mut s = vec![0x5a5a5a5a5a5a5a5au64; 16 * k + 32];
    let r = unsafe {
        f(
            out.as_mut_ptr(),
            k,
            g[0].as_ptr(),
            k,
            input.as_ptr(),
            k,
            g[3].as_ptr(),
            g[3].len(),
            g[4].as_ptr(),
            g[4].len(),
            g[5].as_ptr(),
            g[5].len(),
            g[6].as_ptr(),
            g[6].len(),
            g[7].as_ptr(),
            g[7].len(),
            s.as_mut_ptr(),
            s.len(),
        )
    };
    (r, out)
}

#[test]
fn windows_match_main() {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/key_cases.txt");
    let keys: Vec<Vec<Vec<u8>>> = std::fs::read_to_string(path)
        .unwrap()
        .lines()
        .map(|l| l.split(' ').map(hex).collect())
        .collect();
    let fs: [(&str, Crt); 3] = [("w4", vg_p24_w4), ("w5", vg_p24_w5), ("w6", vg_p24_w6)];
    let mut n = 0;
    for g in &keys {
        let k = g[0].len();
        for seed in 0..3u8 {
            let mut input: Vec<u8> = (0..k)
                .map(|i| (i as u8).wrapping_mul(37).wrapping_add(seed * 91))
                .collect();
            input[0] = 0;
            let want = run(vg_p24_base, g, &input);
            assert_eq!(want.0, 1);
            for (name, f) in fs {
                assert_eq!(run(f, g, &input), want, "{name} k={k} seed={seed}");
                n += 1;
            }
        }
    }
    eprintln!("{n} comparisons");
}
