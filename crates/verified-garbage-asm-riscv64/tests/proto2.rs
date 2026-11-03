//! Local check of the unproven private-key code (bench branch only).
#![cfg(target_arch = "riscv64")]
use verified_garbage_asm_riscv64::rsa_proto2::{vg_rsa_private_checked, vg_rsa_private_crt};

fn hex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

#[test]
fn crt_matches_pow() {
    let path = std::env::var("CRT_CASES").unwrap();
    for line in std::fs::read_to_string(path).unwrap().lines() {
        let f: Vec<Vec<u8>> = line.split(' ').map(hex).collect();
        let (n, e, c, p, q, dp, dq, qi, m) = (
            &f[0], &f[1], &f[2], &f[3], &f[4], &f[5], &f[6], &f[7], &f[8],
        );
        let k = n.len();
        let mut scratch = vec![0u64; 16 * k + 64];
        let mut out = vec![0u8; k];
        let r = unsafe {
            vg_rsa_private_crt(
                out.as_mut_ptr(),
                k,
                n.as_ptr(),
                k,
                c.as_ptr(),
                k,
                p.as_ptr(),
                p.len(),
                q.as_ptr(),
                q.len(),
                dp.as_ptr(),
                dp.len(),
                dq.as_ptr(),
                dq.len(),
                qi.as_ptr(),
                qi.len(),
                scratch.as_mut_ptr(),
                scratch.len(),
            )
        };
        assert_eq!((r, &out), (1, m), "crt, k = {k}");
        let mut out = vec![0u8; k];
        let r = unsafe {
            vg_rsa_private_checked(
                out.as_mut_ptr(),
                k,
                n.as_ptr(),
                k,
                e.as_ptr(),
                e.len(),
                c.as_ptr(),
                k,
                p.as_ptr(),
                p.len(),
                q.as_ptr(),
                q.len(),
                dp.as_ptr(),
                dp.len(),
                dq.as_ptr(),
                dq.len(),
                qi.as_ptr(),
                qi.len(),
                scratch.as_mut_ptr(),
                scratch.len(),
            )
        };
        assert_eq!((r, &out), (1, m), "checked, k = {k}");
    }
}

#[test]
fn checked_refuses_a_wrong_qinv() {
    let path = std::env::var("CRT_CASES").unwrap();
    for line in std::fs::read_to_string(path).unwrap().lines().step_by(3) {
        let f: Vec<Vec<u8>> = line.split(' ').map(hex).collect();
        let (n, e, c, p, q, dp, dq) = (&f[0], &f[1], &f[2], &f[3], &f[4], &f[5], &f[6]);
        let mut qi = f[7].clone();
        // qInv ^ 1 in its low bit: still below p (p is odd and qInv < p), but wrong.
        *qi.last_mut().unwrap() ^= 1;
        let k = n.len();
        let mut scratch = vec![0u64; 16 * k + 64];
        let mut out = vec![0xaau8; k];
        let r = unsafe {
            vg_rsa_private_checked(
                out.as_mut_ptr(),
                k,
                n.as_ptr(),
                k,
                e.as_ptr(),
                e.len(),
                c.as_ptr(),
                k,
                p.as_ptr(),
                p.len(),
                q.as_ptr(),
                q.len(),
                dp.as_ptr(),
                dp.len(),
                dq.as_ptr(),
                dq.len(),
                qi.as_ptr(),
                qi.len(),
                scratch.as_mut_ptr(),
                scratch.len(),
            )
        };
        assert_eq!((r, out.iter().all(|&b| b == 0)), (2, true), "k = {k}");
    }
}
