//! Local check of the unproven key code (bench branch only), against the
//! private keys of Wycheproof's `rsa_oaep_*_test.json` (`key_cases.txt`:
//! `n e d p q dP dQ qInv`, padded to the contract's lengths).
#![cfg(target_arch = "riscv64")]
use verified_garbage_asm_riscv64::rsa_proto3::{vg_rsa_check_crt_key, vg_rsa_check_key, vg_rsa_crt_values};

fn hex(s: &str) -> Vec<u8> {
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}

fn cases() -> Vec<Vec<Vec<u8>>> {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/key_cases.txt");
    std::fs::read_to_string(path).unwrap().lines().map(|l| l.split(' ').map(hex).collect()).collect()
}

fn scratch(k: usize) -> Vec<u64> {
    vec![0x5a5a5a5a5a5a5a5au64; 16 * k + 32]
}

fn crt_values(f: &[Vec<u8>]) -> (u32, Vec<u8>, Vec<u8>, Vec<u8>) {
    let (n, d, p, q) = (&f[0], &f[2], &f[3], &f[4]);
    let (mut dp, mut dq, mut qi) = (vec![0xaa; p.len()], vec![0xaa; q.len()], vec![0xaa; p.len()]);
    let mut s = scratch(n.len());
    let r = unsafe {
        vg_rsa_crt_values(dp.as_mut_ptr(), dp.len(), dq.as_mut_ptr(), dq.len(), qi.as_mut_ptr(), qi.len(),
            n.as_ptr(), n.len(), p.as_ptr(), p.len(), q.as_ptr(), q.len(), d.as_ptr(), d.len(), s.as_mut_ptr(),
            s.len())
    };
    (r, dp, dq, qi)
}

fn check_key(f: &[Vec<u8>]) -> u32 {
    let mut s = scratch(f[0].len());
    unsafe {
        vg_rsa_check_key(f[0].as_ptr(), f[0].len(), f[1].as_ptr(), f[1].len(), f[2].as_ptr(), f[2].len(),
            f[3].as_ptr(), f[3].len(), f[4].as_ptr(), f[4].len(), f[5].as_ptr(), f[5].len(), f[6].as_ptr(),
            f[6].len(), f[7].as_ptr(), f[7].len(), s.as_mut_ptr(), s.len())
    }
}

fn check_crt_key(f: &[Vec<u8>]) -> u32 {
    let mut s = scratch(f[0].len());
    unsafe {
        vg_rsa_check_crt_key(f[0].as_ptr(), f[0].len(), f[1].as_ptr(), f[1].len(), f[3].as_ptr(), f[3].len(),
            f[4].as_ptr(), f[4].len(), f[5].as_ptr(), f[5].len(), f[6].as_ptr(), f[6].len(), f[7].as_ptr(),
            f[7].len(), s.as_mut_ptr(), s.len())
    }
}

/// The ways each field is perturbed: its low bit, its second bit, and the low
/// bit of its first byte.
fn perturbed(f: &[Vec<u8>], i: usize) -> Vec<Vec<Vec<u8>>> {
    let l = f[i].len();
    [(l - 1, 1u8), (l - 1, 2), (0, 1)]
        .iter()
        .map(|&(j, m)| {
            let mut g = f.to_vec();
            g[i][j] ^= m;
            g
        })
        .collect()
}

#[test]
fn crt_values_match() {
    for f in cases() {
        let k = f[0].len();
        assert_eq!(crt_values(&f), (1, f[5].clone(), f[6].clone(), f[7].clone()), "k = {k}");
    }
}

#[test]
fn crt_values_refuse() {
    for f in cases() {
        let k = f[0].len();
        // n even, n's first byte changed, p or q changed: p q ≠ n or n invalid.
        for i in [0, 3, 4] {
            for g in perturbed(&f, i) {
                let (r, dp, dq, qi) = crt_values(&g);
                assert_eq!(r, 0, "k = {k}, field {i}");
                assert!(dp.iter().chain(&dq).chain(&qi).all(|&b| b == 0), "k = {k}, field {i}");
            }
        }
    }
}

#[test]
fn check_key_accepts_and_refuses() {
    for f in cases() {
        let k = f[0].len();
        assert_eq!(check_key(&f), 1, "k = {k}");
        if k > 512 {
            continue;
        }
        for i in 0..8 {
            for g in perturbed(&f, i) {
                assert_eq!(check_key(&g), 0, "k = {k}, field {i}, {g:02x?}");
            }
        }
    }
}

#[test]
fn check_crt_key_accepts_and_refuses() {
    for f in cases() {
        let k = f[0].len();
        assert_eq!(check_crt_key(&f), 1, "k = {k}");
        if k > 512 {
            continue;
        }
        for i in [0, 1, 3, 4, 5, 6, 7] {
            for g in perturbed(&f, i) {
                assert_eq!(check_crt_key(&g), 0, "k = {k}, field {i}");
            }
        }
    }
}

#[test]
#[ignore]
fn timing() {
    for f in cases() {
        let t = std::time::Instant::now();
        crt_values(&f);
        let a = t.elapsed();
        let t = std::time::Instant::now();
        check_key(&f);
        let b = t.elapsed();
        let t = std::time::Instant::now();
        check_crt_key(&f);
        eprintln!("k = {}: crt_values {a:?}, check_key {b:?}, check_crt_key {:?}", f[0].len(), t.elapsed());
    }
}
