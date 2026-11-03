//! Local check of Proto13 (bench branch only): the key checks with Montgomery products
//! give the same mask as main's on Wycheproof's keys (`key_cases.txt`) and on corrupted
//! ones.
#![cfg(target_arch = "riscv64")]
use verified_garbage_asm_riscv64::rsa_proto13::*;

fn hex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

fn cases() -> Vec<Vec<Vec<u8>>> {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/key_cases.txt");
    std::fs::read_to_string(path)
        .unwrap()
        .lines()
        .map(|l| l.split(' ').map(hex).collect())
        .collect()
}

type Crt = unsafe extern "C" fn(
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
type Key = unsafe extern "C" fn(
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
    *const u8,
    usize,
    *mut u64,
    usize,
) -> u32;

fn crt(f: Crt, g: &[Vec<u8>]) -> u32 {
    let mut s = vec![0x5a5a5a5a5a5a5a5au64; 16 * g[0].len() + 32];
    unsafe {
        f(
            g[0].as_ptr(),
            g[0].len(),
            g[1].as_ptr(),
            g[1].len(),
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
    }
}

fn key(f: Key, g: &[Vec<u8>]) -> u32 {
    let mut s = vec![0x5a5a5a5a5a5a5a5au64; 16 * g[0].len() + 32];
    unsafe {
        f(
            g[0].as_ptr(),
            g[0].len(),
            g[1].as_ptr(),
            g[1].len(),
            g[2].as_ptr(),
            g[2].len(),
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
    }
}

/// The key and its corruptions: each field's low bit, second bit and first byte's low bit
/// flipped; `p = 1`, `p = 0`, `qInv = p`, `qInv` all ones; `p` and `q` (with `dP`, `dQ`)
/// swapped, and swapped with `qInv` recomputed nowhere (so wrong).
fn variants(f: &[Vec<u8>]) -> Vec<(String, Vec<Vec<u8>>)> {
    let mut v = vec![("key".to_string(), f.to_vec())];
    for i in 0..8 {
        let l = f[i].len();
        for (j, m) in [(l - 1, 1u8), (l - 1, 2), (0, 1)] {
            let mut g = f.to_vec();
            g[i][j] ^= m;
            v.push((format!("field {i} byte {j} ^ {m}"), g));
        }
    }
    let pl = f[3].len();
    for (name, p) in [("p = 1", 1u8), ("p = 0", 0), ("p = 3", 3)] {
        let mut g = f.to_vec();
        g[3] = vec![0; pl];
        g[3][pl - 1] = p;
        v.push((name.to_string(), g));
    }
    let mut g = f.to_vec();
    g[7] = f[3].clone();
    v.push(("qInv = p".to_string(), g));
    let mut g = f.to_vec();
    g[7] = vec![0xff; pl];
    v.push(("qInv all ones".to_string(), g));
    let mut g = f.to_vec();
    g.swap(3, 4);
    g.swap(5, 6);
    if g[3].len() == g[7].len() {
        v.push(("p, q swapped".to_string(), g));
    }
    v
}

#[test]
fn same_masks() {
    let (mut n, mut ones) = (0, 0);
    for f in cases() {
        let k = f[0].len();
        for (name, g) in variants(&f) {
            let (a, b) = (
                crt(vg_p13_check_crt_key_base, &g),
                crt(vg_p13_check_crt_key_new, &g),
            );
            assert_eq!(a, b, "check_crt_key, k = {k}, {name}");
            let (c, d) = (
                key(vg_p13_check_key_base, &g),
                key(vg_p13_check_key_new, &g),
            );
            assert_eq!(c, d, "check_key, k = {k}, {name}");
            if name == "key" {
                assert_eq!((a, c), (1, 1), "k = {k}");
            }
            n += 1;
            ones += a + c;
        }
    }
    eprintln!("{n} variants, {ones} accepted");
}

#[test]
#[ignore]
fn timing() {
    for f in cases() {
        let t = std::time::Instant::now();
        crt(vg_p13_check_crt_key_base, &f);
        let a = t.elapsed();
        let t = std::time::Instant::now();
        crt(vg_p13_check_crt_key_new, &f);
        let b = t.elapsed();
        let t = std::time::Instant::now();
        key(vg_p13_check_key_base, &f);
        let c = t.elapsed();
        let t = std::time::Instant::now();
        key(vg_p13_check_key_new, &f);
        let d = t.elapsed();
        eprintln!("k = {}: crt {a:?} -> {b:?}, key {c:?} -> {d:?}", f[0].len());
    }
}
