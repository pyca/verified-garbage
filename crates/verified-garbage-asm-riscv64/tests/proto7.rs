//! Local check of the unproven CRT variants (bench branch only): each equals the CRT.
#![cfg(target_arch = "riscv64")]
use verified_garbage_asm_riscv64::rsa_proto2::vg_rsa_private_crt;
use verified_garbage_asm_riscv64::rsa_proto7::{vg_proto_crt_base, vg_proto_crt_both, vg_proto_crt_keep, vg_proto_crt_scan};

fn hex(s: &str) -> Vec<u8> {
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}

type Crt = unsafe extern "C" fn(*mut u8, usize, *const u8, usize, *const u8, usize, *const u8, usize, *const u8,
    usize, *const u8, usize, *const u8, usize, *const u8, usize, *mut u64, usize) -> u32;

#[test]
fn variants_match_crt() {
    let path = std::env::var("CRT_CASES").unwrap();
    let fs: [(&str, Crt); 5] = [("crt", vg_rsa_private_crt), ("base", vg_proto_crt_base), ("scan", vg_proto_crt_scan),
        ("keep", vg_proto_crt_keep), ("both", vg_proto_crt_both)];
    let mut n_ok = 0;
    for line in std::fs::read_to_string(path).unwrap().lines() {
        let f: Vec<Vec<u8>> = line.split(' ').map(hex).collect();
        let (n, c, p, q, dp, dq, qi, m) = (&f[0], &f[2], &f[3], &f[4], &f[5], &f[6], &f[7], &f[8]);
        let k = n.len();
        for (name, g) in fs {
            let mut scratch = vec![0u64; 16 * k + 64];
            let mut out = vec![0u8; k];
            let r = unsafe {
                g(out.as_mut_ptr(), k, n.as_ptr(), k, c.as_ptr(), k, p.as_ptr(), p.len(), q.as_ptr(), q.len(),
                    dp.as_ptr(), dp.len(), dq.as_ptr(), dq.len(), qi.as_ptr(), qi.len(), scratch.as_mut_ptr(),
                    scratch.len())
            };
            assert_eq!((r, &out), (1, m), "{name}, k = {k}");
            // A ciphertext not below n: 0 and zeros, as the CRT.
            let big = vec![0xffu8; k];
            let r = unsafe {
                g(out.as_mut_ptr(), k, n.as_ptr(), k, big.as_ptr(), k, p.as_ptr(), p.len(), q.as_ptr(), q.len(),
                    dp.as_ptr(), dp.len(), dq.as_ptr(), dq.len(), qi.as_ptr(), qi.len(), scratch.as_mut_ptr(),
                    scratch.len())
            };
            assert_eq!((r, out.iter().all(|&b| b == 0)), (0, true), "{name} big, k = {k}");
        }
        n_ok += 1;
    }
    eprintln!("{n_ok} cases x 5 functions");
    assert!(n_ok > 0);
}
