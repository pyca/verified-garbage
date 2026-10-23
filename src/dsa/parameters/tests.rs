use super::*;
use crate::dsa::PrivateKey;
use crate::dsa::tests::vectors::hex;

struct Vector {
    bits: usize,
    p: Vec<u8>,
    q: Vec<u8>,
    seed: Vec<u8>,
}

fn prime_vectors() -> Vec<Vector> {
    let mut section = "";
    let mut mode = "";
    let mut p = "";
    let mut q = "";
    let mut seed = "";
    let mut cases = Vec::new();
    for line in include_str!("../../../vectors/nist-cavp-dsa/PQGGen.txt").lines() {
        if line.starts_with("[A.") {
            section = line;
        } else if line.starts_with("[mod = ") {
            mode = line;
        } else if section.starts_with("[A.1.1.2 ") {
            // Indented P/counter lines are intermediate candidates, not
            // the published final answers.
            if let Some(value) = line.strip_prefix("P = ") {
                p = value;
            } else if let Some(value) = line.strip_prefix("Q = ") {
                q = value;
            } else if let Some(value) = line.strip_prefix("domain_parameter_seed = ") {
                seed = value;
            } else if line.starts_with("counter = ") {
                let bits = match mode {
                    "[mod = L=1024, N=160, SHA-1]" => 1024,
                    "[mod = L=2048, N=256, SHA-256]" => 2048,
                    "[mod = L=3072, N=256, SHA-256]" => 3072,
                    _ => continue,
                };
                if !cases.iter().any(|v: &Vector| v.bits == bits) {
                    cases.push(Vector {
                        bits,
                        p: hex(p, 0),
                        q: hex(q, 0),
                        seed: hex(seed, 0),
                    });
                }
            }
        }
    }
    assert_eq!(cases.len(), 3);
    cases
}

#[test]
fn cavp_generated_parameters() {
    for v in prime_vectors() {
        let mut tape = 0;
        let parameters = Parameters::generate_with_rng(v.bits, |buf| {
            match tape {
                0 => {
                    for seed in buf.chunks_exact_mut(v.seed.len()) {
                        seed.copy_from_slice(&v.seed);
                    }
                }
                1 => {
                    buf.fill(0);
                    for h in buf.chunks_exact_mut(v.p.len()) {
                        h[v.p.len() - 1] = 2;
                    }
                }
                // Deterministic valid witnesses for known-answer tests;
                // production obtains independent bytes from the OS.
                _ => buf.fill(2),
            }
            tape += 1;
            Ok(())
        })
        .unwrap();
        assert_eq!(tape, 3);
        assert_eq!(parameters.p(), v.p);
        assert_eq!(parameters.q(), v.q);
        assert_eq!(parameters.g().len(), v.p.len());
        let key = PrivateKey::generate(parameters.p(), parameters.q(), parameters.g()).unwrap();
        let digest = [0x53; 32];
        let signature = key.sign(&digest).unwrap();
        assert!(key.public_key().verify(&digest, &signature));
    }
}

#[test]
fn parameter_generation_errors() {
    for bits in [0, 512, 2047, 4096] {
        assert_eq!(Parameters::generate(bits).unwrap_err(), Error::Length);
    }
    for fail_at in 0..3 {
        let mut fills = 0;
        let result = Parameters::generate_with_rng(1024, |buf| {
            let fail = fills == fail_at;
            fills += 1;
            if fail {
                Err(Error::Randomness)
            } else {
                buf.fill(2);
                Ok(())
            }
        });
        assert_eq!(result.unwrap_err(), Error::Randomness);
        assert_eq!(fills, fail_at + 1);
    }
    // Repeated 0x02 seeds produce a subgroup candidate divisible by 3.
    // The verified search exhausts the seed tape and reports failure.
    assert_eq!(
        Parameters::generate_with_rng(1024, |buf| {
            buf.fill(2);
            Ok(())
        })
        .unwrap_err(),
        Error::InvalidKeyOrNonce
    );
}

#[test]
fn empty_tapes_zero_output() {
    for (p_len, q_len) in [(128, 20), (256, 32), (384, 32)] {
        let mut out = vec![0xa5; 2 * p_len + q_len];
        let mut scratch = vec![0xdeadbeef; 64 * p_len + 1024];
        let empty: &[u8] = &[];
        // SAFETY: supported widths and disjoint output/scratch allocations;
        // empty tapes satisfy the whole-chunk conditions. Selection uses
        // only features detected on this CPU.
        let status = unsafe {
            select(detected(), p_len)(
                out.as_mut_ptr(),
                out.len(),
                p_len,
                q_len,
                empty.as_ptr(),
                0,
                empty.as_ptr(),
                0,
                empty.as_ptr(),
                0,
                scratch.as_mut_ptr(),
                scratch.len(),
            )
        };
        assert_eq!(status, 0);
        assert!(out.iter().all(|&b| b == 0));
    }
}

#[test]
fn generated_parameters_with_os_randomness() {
    let parameters = Parameters::generate(1024).unwrap();
    let key = PrivateKey::generate(parameters.p(), parameters.q(), parameters.g()).unwrap();
    let digest = [0x47; 20];
    assert!(
        key.public_key()
            .verify(&digest, &key.sign(&digest).unwrap())
    );
}

#[test]
#[cfg(target_arch = "x86_64")]
fn backend_combinations() {
    use crate::hashes::{sha1::Sha1Backend as H1, sha256::Sha256Backend as H256};
    let sha1_cases: &[(H1, bool, Generate, Features)] = &[
        (
            H1::Scalar,
            false,
            vg_dsa_generate_parameters_1024,
            Features(0),
        ),
        (
            H1::Scalar,
            true,
            vg_dsa_generate_parameters_1024_mr_adx,
            VG_DSA_GENERATE_PARAMETERS_1024_MR_ADX_FEATURES,
        ),
        (
            H1::ShaNi,
            false,
            vg_dsa_generate_parameters_1024_sha1_shani,
            VG_DSA_GENERATE_PARAMETERS_1024_SHA1_SHANI_FEATURES,
        ),
        (
            H1::ShaNi,
            true,
            vg_dsa_generate_parameters_1024_sha1_shani_mr_adx,
            VG_DSA_GENERATE_PARAMETERS_1024_SHA1_SHANI_MR_ADX_FEATURES,
        ),
    ];
    for &(h1, adx, expected, required) in sha1_cases {
        for h256 in [H256::Scalar, H256::Avx2, H256::ShaNi] {
            assert!(core::ptr::fn_addr_eq(
                select_backends(h1, h256, adx, 128),
                expected
            ));
        }
        if detected().contains(required) {
            check_empty_tapes(expected, 128);
        }
    }
    let sha256_cases: &[(H256, bool, [Generate; 2], Features)] = &[
        (
            H256::Scalar,
            false,
            [
                vg_dsa_generate_parameters_2048,
                vg_dsa_generate_parameters_3072,
            ],
            Features(0),
        ),
        (
            H256::Scalar,
            true,
            [
                vg_dsa_generate_parameters_2048_mr_adx,
                vg_dsa_generate_parameters_3072_mr_adx,
            ],
            VG_DSA_GENERATE_PARAMETERS_2048_MR_ADX_FEATURES,
        ),
        (
            H256::Avx2,
            false,
            [
                vg_dsa_generate_parameters_2048_sha256_avx2,
                vg_dsa_generate_parameters_3072_sha256_avx2,
            ],
            VG_DSA_GENERATE_PARAMETERS_2048_SHA256_AVX2_FEATURES,
        ),
        (
            H256::Avx2,
            true,
            [
                vg_dsa_generate_parameters_2048_sha256_avx2_mr_adx,
                vg_dsa_generate_parameters_3072_sha256_avx2_mr_adx,
            ],
            VG_DSA_GENERATE_PARAMETERS_2048_SHA256_AVX2_MR_ADX_FEATURES,
        ),
        (
            H256::ShaNi,
            false,
            [
                vg_dsa_generate_parameters_2048_sha256_shani,
                vg_dsa_generate_parameters_3072_sha256_shani,
            ],
            VG_DSA_GENERATE_PARAMETERS_2048_SHA256_SHANI_FEATURES,
        ),
        (
            H256::ShaNi,
            true,
            [
                vg_dsa_generate_parameters_2048_sha256_shani_mr_adx,
                vg_dsa_generate_parameters_3072_sha256_shani_mr_adx,
            ],
            VG_DSA_GENERATE_PARAMETERS_2048_SHA256_SHANI_MR_ADX_FEATURES,
        ),
    ];
    for &(h256, adx, expected, required) in sha256_cases {
        for (&p_len, expected) in [256, 384].iter().zip(expected) {
            for h1 in [H1::Scalar, H1::ShaNi] {
                assert!(core::ptr::fn_addr_eq(
                    select_backends(h1, h256, adx, p_len),
                    expected
                ));
            }
            if detected().contains(required) {
                check_empty_tapes(expected, p_len);
            }
        }
    }
}

#[test]
#[cfg(target_arch = "x86")]
fn backend_combinations() {
    use crate::hashes::{sha1::Sha1Backend as H1, sha256::Sha256Backend as H256};
    // The mixed SHA pairs cannot be selected by a real CPU today because
    // the hash instructions share feature requirements. Check the complete
    // dispatch table, including those pairs, against emitted feature sets.
    let cases: &[(H1, H256, Generate, Features)] = &[
        (
            H1::Scalar,
            H256::Scalar,
            vg_dsa_generate_parameters,
            Features(0),
        ),
        (
            H1::Scalar,
            H256::ShaNi,
            vg_dsa_generate_parameters_sha256_shani,
            VG_DSA_GENERATE_PARAMETERS_SHA256_SHANI_FEATURES,
        ),
        (
            H1::ShaNi,
            H256::Scalar,
            vg_dsa_generate_parameters_sha1_shani,
            VG_DSA_GENERATE_PARAMETERS_SHA1_SHANI_FEATURES,
        ),
        (
            H1::ShaNi,
            H256::ShaNi,
            vg_dsa_generate_parameters_sha1_shani_sha256_shani,
            VG_DSA_GENERATE_PARAMETERS_SHA1_SHANI_SHA256_SHANI_FEATURES,
        ),
    ];
    for &(h1, h256, expected, required) in cases {
        let selected = select_backends(h1, h256);
        assert!(core::ptr::fn_addr_eq(selected, expected));
        if detected().contains(required) {
            check_empty_tapes(selected, 128);
        }
    }
}

/// An implementation given empty tapes zeroes `out` and returns 0.
#[cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    all(
        target_arch = "arm",
        any(
            target_os = "linux",
            target_os = "android",
            target_os = "freebsd",
            target_os = "netbsd",
            target_os = "openbsd"
        )
    )
))]
fn check_empty_tapes(selected: Generate, p_len: usize) {
    let q_len = if p_len == 128 { 20 } else { 32 };
    let mut out = vec![0xa5; 2 * p_len + q_len];
    let mut scratch = vec![0u64; 64 * p_len + 1024];
    let empty: &[u8] = &[];
    // SAFETY: the selected helper matches the supported public width; disjoint buffers,
    // whole empty tapes, and all emitted CPU requirements checked.
    assert_eq!(
        unsafe {
            selected(
                out.as_mut_ptr(),
                out.len(),
                p_len,
                q_len,
                empty.as_ptr(),
                0,
                empty.as_ptr(),
                0,
                empty.as_ptr(),
                0,
                scratch.as_mut_ptr(),
                scratch.len(),
            )
        },
        0
    );
    assert!(out.iter().all(|&byte| byte == 0));
}

#[test]
fn exhausted_tapes_after_prime_search_zero_output() {
    let v = prime_vectors().remove(0);
    assert_eq!(v.bits, 1024);
    let witnesses = vec![2; 16384 * v.p.len()];
    let rejected_h = vec![0; v.p.len()];
    // A known prime-producing seed distinguishes exhaustion during primality
    // testing from exhaustion after both primes have been found. h=0 also
    // exercises rejection of a complete generator chunk before exhaustion.
    for (rand, hs) in [
        (&[][..], &[][..]),
        (&witnesses[..], &[][..]),
        (&witnesses[..], &rejected_h[..]),
    ] {
        let mut out = vec![0xa5; 2 * v.p.len() + v.q.len()];
        let mut scratch = vec![0xdeadbeefu64; 64 * v.p.len() + 1024];
        // SAFETY: published 1024/160 widths, whole seed and h chunks, exact
        // output size, sufficient scratch, and disjoint owned buffers.
        // The selected implementation requires only detected CPU features.
        let status = unsafe {
            select(detected(), v.p.len())(
                out.as_mut_ptr(),
                out.len(),
                v.p.len(),
                v.q.len(),
                v.seed.as_ptr(),
                v.seed.len(),
                hs.as_ptr(),
                hs.len(),
                rand.as_ptr(),
                rand.len(),
                scratch.as_mut_ptr(),
                scratch.len(),
            )
        };
        assert_eq!(status, 0);
        assert!(out.iter().all(|&byte| byte == 0));
    }
}

#[test]
#[cfg(target_arch = "aarch64")]
fn backend_combinations() {
    use crate::hashes::{sha1::Sha1Backend as H1, sha256::Sha256Backend as H256};
    let cases: &[(H1, H256, Generate, Features)] = &[
        (
            H1::Scalar,
            H256::Scalar,
            vg_dsa_generate_parameters,
            Features(0),
        ),
        (
            H1::Scalar,
            H256::Sha2,
            vg_dsa_generate_parameters_sha256_sha2,
            VG_DSA_GENERATE_PARAMETERS_SHA256_SHA2_FEATURES,
        ),
        (
            H1::Sha2,
            H256::Scalar,
            vg_dsa_generate_parameters_sha1_sha2,
            VG_DSA_GENERATE_PARAMETERS_SHA1_SHA2_FEATURES,
        ),
        (
            H1::Sha2,
            H256::Sha2,
            vg_dsa_generate_parameters_sha1_sha2_sha256_sha2,
            VG_DSA_GENERATE_PARAMETERS_SHA1_SHA2_SHA256_SHA2_FEATURES,
        ),
    ];
    for &(h1, h256, expected, required) in cases {
        let selected = select_backends(h1, h256);
        assert!(core::ptr::fn_addr_eq(selected, expected));
        if detected().contains(required) {
            let mut out = [0xa5; 276];
            let mut scratch = vec![0u64; 9216];
            let empty: &[u8] = &[];
            // SAFETY: supported dimensions, disjoint output and scratch,
            // complete empty entropy tapes, and detected CPU requirements.
            let status = unsafe {
                selected(
                    out.as_mut_ptr(),
                    out.len(),
                    128,
                    20,
                    empty.as_ptr(),
                    0,
                    empty.as_ptr(),
                    0,
                    empty.as_ptr(),
                    0,
                    scratch.as_mut_ptr(),
                    scratch.len(),
                )
            };
            assert_eq!(status, 0);
            assert_eq!(out, [0; 276]);
        }
    }
}

#[test]
#[cfg(all(
    target_arch = "arm",
    any(
        target_os = "linux",
        target_os = "android",
        target_os = "freebsd",
        target_os = "netbsd",
        target_os = "openbsd"
    )
))]
fn backend_combinations() {
    let cases: &[(bool, Generate, Features)] = &[
        (false, vg_dsa_generate_parameters, Features(0)),
        (
            true,
            vg_dsa_generate_parameters_umaal,
            VG_DSA_GENERATE_PARAMETERS_UMAAL_FEATURES,
        ),
    ];
    for &(umaal, expected, required) in cases {
        let selected = select_backends(umaal);
        assert!(core::ptr::fn_addr_eq(selected, expected));
        assert!(core::ptr::fn_addr_eq(select(required, 128), expected));
        if detected().contains(required) {
            check_empty_tapes(selected, 128);
        }
    }
}
