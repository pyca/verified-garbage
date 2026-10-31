use super::*;
use crate::cpu::feature;
#[cfg(any(target_arch = "aarch64", target_arch = "powerpc64"))]
extern crate std;
use crate::hashes::{sha1::Sha1, sha224::Sha224, sha256::Sha256, sha384::Sha384, sha512::Sha512};
use alloc::{format, string::ToString};

#[path = "../../tests/cavp/dsa_vectors.rs"]
pub(super) mod vectors;
use vectors::{hex, vectors};

#[cfg(any(target_arch = "x86", target_arch = "arm", target_arch = "powerpc64"))]
#[test]
fn generation_domain_checks() {
    let cases = vectors(include_str!("../../vectors/nist-cavp-dsa/SigGen.txt"), true);
    for (p_len, q_len) in [(128, 20), (256, 20), (256, 28), (256, 32), (384, 32)] {
        let v = cases
            .iter()
            .find(|v| {
                hex(&v["P"], 0).len() == if q_len == 20 { 128 } else { p_len }
                    && hex(&v["Q"], 0).len() == q_len
            })
            .unwrap();
        let p = hex(&v["P"], p_len);
        let q = hex(&v["Q"], q_len);
        let g = hex(&v["G"], p_len);
        let valid = [&p[..], &q, &g].concat();
        let mut scratch = Secret(vec![0xa5a5a5a5a5a5a5a5; 16 * p_len]);
        let mut check = |params: &[u8]| {
            // SAFETY: every case has the supported widths and exact packed
            // length. Scratch is a separate allocation of 16*p_len words.
            unsafe {
                crate::arch::dsa::vg_dsa_check_parameters(
                    params.as_ptr(),
                    params.len(),
                    p_len,
                    q_len,
                    scratch.0.as_mut_ptr(),
                    scratch.0.len(),
                )
            }
        };
        assert_eq!(check(&valid), 1, "{p_len}/{q_len}");
        let mut bad = valid.clone();
        bad[p_len + q_len..].fill(0);
        assert_eq!(check(&bad), 0, "g = 0");
        *bad.last_mut().unwrap() = 1;
        assert_eq!(check(&bad), 0, "g = 1");
        bad[p_len + q_len..].copy_from_slice(&p);
        assert_eq!(check(&bad), 0, "g = p");
        bad.copy_from_slice(&valid);
        bad[p_len - 1] &= !1;
        assert_eq!(check(&bad), 0, "even p");
        bad.copy_from_slice(&valid);
        bad[p_len + q_len - 1] &= !1;
        assert_eq!(check(&bad), 0, "even q");
        bad.copy_from_slice(&valid);
        bad[p_len..p_len + q_len].fill(0);
        assert_eq!(check(&bad), 0, "zero q");
    }
}

#[cfg(any(target_arch = "x86", target_arch = "arm", target_arch = "powerpc64"))]
#[test]
fn generation_derive_keys() {
    let cases = vectors(include_str!("../../vectors/nist-cavp-dsa/SigGen.txt"), true);
    for (p_len, q_len) in [(128, 20), (256, 20), (256, 28), (256, 32), (384, 32)] {
        let v = cases
            .iter()
            .find(|v| {
                hex(&v["P"], 0).len() == if q_len == 20 { 128 } else { p_len }
                    && hex(&v["Q"], 0).len() == q_len
            })
            .unwrap();
        let p = hex(&v["P"], p_len);
        let q = hex(&v["Q"], q_len);
        let g = hex(&v["G"], p_len);
        let x = hex(&v["X"], q_len);
        let y = hex(&v["Y"], p_len);
        let params = [&p[..], &q, &g].concat();
        let expected = [&params[..], &y, &x].concat();
        let mut scratch = Secret(vec![0xa5a5a5a5a5a5a5a5; 16 * p_len]);
        let mut output = Secret(vec![0xa5; 3 * p_len + 2 * q_len]);
        let mut derive = |domain: &[u8], scalar: &[u8], expected: Option<&[u8]>| {
            output.0.fill(0xa5);
            // SAFETY: supported widths and exact input/output lengths; each
            // buffer has its own allocation and scratch has 16*p_len words.
            let status = unsafe {
                crate::arch::dsa::vg_dsa_derive_key(
                    output.0.as_mut_ptr(),
                    output.0.len(),
                    domain.as_ptr(),
                    domain.len(),
                    p_len,
                    scalar.as_ptr(),
                    q_len,
                    scratch.0.as_mut_ptr(),
                    scratch.0.len(),
                )
            };
            assert_eq!(status, u32::from(expected.is_some()), "{p_len}/{q_len}");
            match expected {
                Some(expected) => assert_eq!(output.0, expected),
                None => assert!(output.0.iter().all(|&b| b == 0)),
            }
        };
        derive(&params, &x, Some(&expected));
        derive(&params, &vec![0; q_len], None);
        derive(&params, &q, None);
        derive(&params, &vec![0xff; q_len], None);
        let mut bad = params.clone();
        bad[p_len - 1] &= !1;
        derive(&bad, &x, None);
        bad.copy_from_slice(&params);
        bad[p_len + q_len..].fill(0);
        derive(&bad, &x, None);
    }
}

fn digest(hash: &str, msg: &[u8]) -> Vec<u8> {
    let hashes: [(&str, Vec<u8>); 5] = [
        ("SHA-1", Sha1::digest(msg).to_vec()),
        ("SHA-224", Sha224::digest(msg).to_vec()),
        ("SHA-256", Sha256::digest(msg).to_vec()),
        ("SHA-384", Sha384::digest(msg).to_vec()),
        ("SHA-512", Sha512::digest(msg).to_vec()),
    ];
    hashes
        .into_iter()
        .find(|(name, _)| *name == hash)
        .unwrap()
        .1
}

fn sample() -> (PrivateKey, Vec<u8>, Vec<u8>) {
    let cases = vectors(include_str!("../../vectors/nist-cavp-dsa/SigGen.txt"), true);
    let v = &cases[0];
    let p = hex(&v["P"], 0);
    let q = hex(&v["Q"], 0);
    let key = PrivateKey::from_components(
        &p,
        &q,
        &hex(&v["G"], p.len()),
        &hex(&v["Y"], p.len()),
        &hex(&v["X"], q.len()),
    )
    .unwrap();
    (
        key,
        digest(&v["Hash"], &hex(&v["Msg"], 0)),
        hex(&v["K"], q.len()),
    )
}

// Interleave four batches so libtest can distribute independent vectors across cores.
fn cavp_signatures_batch(batch: usize) {
    for (i, v) in vectors(include_str!("../../vectors/nist-cavp-dsa/SigGen.txt"), true)
        .iter()
        .enumerate()
        .skip(batch)
        .step_by(4)
    {
        let p = hex(&v["P"], 0);
        let q = hex(&v["Q"], 0);
        let key = PrivateKey::from_components(
            &p,
            &q,
            &hex(&v["G"], p.len()),
            &hex(&v["Y"], p.len()),
            &hex(&v["X"], q.len()),
        )
        .unwrap();
        let digest = digest(&v["Hash"], &hex(&v["Msg"], 0));
        let mut signature = vec![0xa5; 2 * q.len()];
        let mut scratch = Secret(vec![0xa5a5a5a5a5a5a5a5; 16 * p.len()]);
        let signed = key.sign_once(
            &digest,
            &hex(&v["K"], q.len()),
            &mut signature,
            &mut scratch.0,
        );
        assert!(signed, "vector {i}");
        let expected = [hex(&v["R"], q.len()), hex(&v["S"], q.len())].concat();
        assert_eq!(signature, expected, "vector {i}");
        assert!(key.public_key().verify(&digest, &signature), "vector {i}");
        let nonce = hex(&v["K"], q.len());
        let randomized = key
            .sign_with_rng(&digest, |buf| {
                buf.copy_from_slice(&nonce);
                Ok(())
            })
            .unwrap();
        assert_eq!(randomized, expected, "random tape vector {i}");
    }
}

#[test]
fn cavp_signatures_0() {
    cavp_signatures_batch(0);
}

#[test]
fn cavp_signatures_1() {
    cavp_signatures_batch(1);
}

#[test]
fn cavp_signatures_2() {
    cavp_signatures_batch(2);
}

#[test]
fn cavp_signatures_3() {
    cavp_signatures_batch(3);
}

#[test]
fn random_tape_rejection_and_replay() {
    let (key, digest, nonce) = sample();
    let mut expected = vec![0; 2 * key.public.q_len];
    let mut scratch = Secret(vec![0u64; 16 * key.public.p_len]);
    assert!(key.sign_once(&digest, &nonce, &mut expected, &mut scratch.0));
    let mut draws = 0;
    let signature = key
        .sign_with_rng(&digest, |buf| {
            if draws == 0 {
                buf.fill(0);
            } else {
                buf.copy_from_slice(&nonce);
            }
            draws += 1;
            Ok(())
        })
        .unwrap();
    assert_eq!(draws, 2);
    assert_eq!(signature, expected);
    assert!(key.public_key().verify(&digest, &signature));
}

#[test]
fn random_signing_and_digest_lengths() {
    let (key, _, _) = sample();
    for digest in [
        vec![],
        vec![3],
        vec![7; 19],
        vec![11; 20],
        vec![13; 64],
        vec![17; 129],
    ] {
        let signature = key.sign(&digest).unwrap();
        assert!(key.public_key().verify(&digest, &signature));
        assert!(!key.public_key().verify(&[21; 32], &signature));
    }
    assert!(!key.public_key().verify(&[], &[]));
    assert!(!key.public_key().verify(&[], &[0; 40]));
    assert!(format!("{key:?}").contains("PrivateKey"));
    assert!(format!("{:?}", key.public_key().clone()).contains("PublicKey"));
}

#[test]
fn padded_domain_and_scalars() {
    let cases = vectors(include_str!("../../vectors/nist-cavp-dsa/SigGen.txt"), true);
    let v = &cases[0];
    let digest = digest(&v["Hash"], &hex(&v["Msg"], 0));
    let p = hex(&v["P"], 256);
    let q = hex(&v["Q"], 32);
    let g = hex(&v["G"], 256);
    let y = hex(&v["Y"], 256);
    let x = hex(&v["X"], 32);
    let padded = PrivateKey::from_components(&p, &q, &g, &y, &x).unwrap();
    let mut output = vec![0xa5; 64];
    let mut scratch = Secret(vec![0xa5a5a5a5a5a5a5a5; 4096]);
    assert!(padded.sign_once(&digest, &hex(&v["K"], 32), &mut output, &mut scratch.0));
    assert!(padded.public_key().verify(&digest, &output));
    let fresh = padded.sign(&digest).unwrap();
    assert!(padded.public_key().verify(&digest, &fresh));
}

#[test]
fn public_subgroup_windows() {
    let cases = vectors(include_str!("../../vectors/nist-cavp-dsa/SigGen.txt"), true);
    let v = &cases[0];
    let p = hex(&v["P"], 0);
    let q = hex(&v["Q"], 0);
    let g = hex(&v["G"], p.len());
    let y = hex(&v["Y"], p.len());
    let x = hex(&v["X"], q.len());
    let nonce = hex(&v["K"], q.len());
    let digest = digest(&v["Hash"], &hex(&v["Msg"], 0));
    let signature = [hex(&v["R"], q.len()), hex(&v["S"], q.len())].concat();
    let mut minus_one = p.clone();
    // p is odd, so subtracting one cannot borrow from the final byte.
    *minus_one.last_mut().unwrap() -= 1;
    // Each has order two, although their product is one. Both subgroup
    // checks must reject them independently for the odd subgroup order.
    for (generator, public) in [(&minus_one, &y), (&g, &minus_one), (&minus_one, &minus_one)] {
        let key = PublicKey::from_components(&p, &q, generator, public).unwrap();
        assert!(!key.verify(&digest, &signature));
    }
    // Malformed odd orders still execute the public exponentiation path.
    // Exercise zero windows, dense windows and every table digit. With
    // g = -1 and odd q, subgroup validation must always fail.
    for pattern in [0x00, 0xff, 0xf0, 0x01] {
        let mut order = vec![pattern; q.len()];
        order[0] |= 0x80;
        *order.last_mut().unwrap() |= 1;
        if pattern == 0x01 {
            order[1..9].copy_from_slice(&[0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef]);
        }
        let key = PrivateKey::from_components(&p, &order, &minus_one, &y, &x).unwrap();
        assert!(!key.public_key().verify(&digest, &signature));
        let mut output = vec![0xa5; signature.len()];
        let mut scratch = Secret(vec![0xa5a5a5a5a5a5a5a5; 16 * p.len()]);
        assert!(!key.sign_once(&digest, &nonce, &mut output, &mut scratch.0));
        assert_eq!(output, vec![0; signature.len()]);
    }
}

#[test]
fn signing_key_consistency_implies_public_subgroup() {
    let cases = vectors(include_str!("../../vectors/nist-cavp-dsa/SigGen.txt"), true);
    let v = &cases[0];
    let p = hex(&v["P"], 0);
    let q = hex(&v["Q"], 0);
    let g = hex(&v["G"], p.len());
    let y = hex(&v["Y"], p.len());
    let x = hex(&v["X"], q.len());
    let nonce = hex(&v["K"], q.len());
    let digest = digest(&v["Hash"], &hex(&v["Msg"], 0));
    let mut minus_one = p.clone();
    *minus_one.last_mut().unwrap() -= 1;
    let mut one = vec![0; q.len()];
    *one.last_mut().unwrap() = 1;
    let mut output = vec![0xa5; 2 * q.len()];
    let mut scratch = Secret(vec![0xa5a5a5a5a5a5a5a5; 16 * p.len()]);

    // A valid generator with an out-of-subgroup public value fails g^x = y.
    // With x = 1, g = y = -1 passes consistency but must fail g^q = 1.
    // With x = 1 and the original y, both subgroup checks pass but consistency fails.
    for (generator, public, private) in [
        (&g, &minus_one, &x),
        (&minus_one, &minus_one, &one),
        (&g, &y, &one),
    ] {
        let key = PrivateKey::from_components(&p, &q, generator, public, private).unwrap();
        output.fill(0xa5);
        assert!(!key.sign_once(&digest, &nonce, &mut output, &mut scratch.0));
        assert_eq!(output, vec![0; 2 * q.len()]);
    }
    // The same boundary private scalar succeeds when y = g.
    let key = PrivateKey::from_components(&p, &q, &g, &g, &one).unwrap();
    assert!(key.sign_once(&digest, &nonce, &mut output, &mut scratch.0));
    assert!(key.public_key().verify(&digest, &output));
}

#[test]
fn malformed_keys_nonces_and_bounded_retries() {
    let (mut key, digest, nonce) = sample();
    let mut output = vec![0xa5; 40];
    let mut scratch = Secret(vec![0xa5a5a5a5a5a5a5a5; 2048]);
    for invalid in [vec![0; 20], key.public.packed[128..148].to_vec()] {
        assert!(!key.sign_once(&digest, &invalid, &mut output, &mut scratch.0));
        assert_eq!(output, vec![0; 40]);
    }
    assert_eq!(
        key.sign_with_rng(&digest, |_| Err(Error::Randomness)),
        Err(Error::Randomness)
    );
    let mut draws = 0;
    assert_eq!(
        key.sign_with_rng(&digest, |b| {
            b.fill(0);
            draws += 1;
            Ok(())
        }),
        Err(Error::InvalidKeyOrNonce)
    );
    assert_eq!(draws, 128);
    key.packed.0[404..].fill(0);
    draws = 0;
    assert_eq!(
        key.sign_with_rng(&digest, |b| {
            b.copy_from_slice(&nonce);
            draws += 1;
            Ok(())
        }),
        Err(Error::InvalidKeyOrNonce)
    );
    assert_eq!(draws, 8);
    key.public.packed[128..148].fill(0);
    key.packed.0[128..148].fill(0);
    assert_eq!(
        key.sign_with_rng(&digest, |_| panic!("zero q needs no RNG")),
        Err(Error::InvalidKeyOrNonce)
    );
    // Malformed public shape takes the early failure path and zeros output.
    key.packed.0[127] &= 0xfe;
    output.fill(0xa5);
    assert!(!key.sign_once(&digest, &nonce, &mut output, &mut scratch.0));
    assert_eq!(output, vec![0; 40]);
    assert!(!key.public_key().verify(&digest, &output));
}

#[test]
fn import_lengths_errors_and_backends() {
    assert_eq!(
        PublicKey::from_components(&[], &[], &[], &[]).unwrap_err(),
        Error::Length
    );
    assert_eq!(
        PublicKey::from_components(&[0; 128], &[0; 20], &[], &[0; 128]).unwrap_err(),
        Error::Length
    );
    assert_eq!(
        PublicKey::from_components(&[0; 128], &[0; 20], &[0; 128], &[]).unwrap_err(),
        Error::Length
    );
    assert_eq!(
        PrivateKey::from_components(&[], &[], &[], &[], &[]).unwrap_err(),
        Error::Length
    );
    assert_eq!(
        PrivateKey::from_components(&[0; 128], &[0; 20], &[0; 128], &[0; 128], &[]).unwrap_err(),
        Error::Length
    );
    assert_eq!(Backend::select(Features(0)), Backend::Baseline);
    assert_eq!(Backend::select(Features(feature::BMI2)), Backend::Baseline);
    #[cfg(target_arch = "x86_64")]
    assert_eq!(
        Backend::select(Features(feature::BMI2 | feature::ADX)),
        Backend::Adx
    );
    for error in [Error::Length, Error::InvalidKeyOrNonce, Error::Randomness] {
        assert!(!error.to_string().is_empty());
        assert!(!format!("{error:?}").is_empty());
    }
}

#[path = "../../tests/dsa_legacy.rs"]
pub(super) mod legacy_vectors;

#[test]
fn legacy_2048_160_signatures() {
    let (p, q, g) = legacy_vectors::parameters();
    // With x = 1 the public key is the published generator. This is an
    // algebraic round-trip test, not a manufactured known-answer vector.
    for (p_len, q_len) in [(256, 20), (256, 28), (256, 32), (384, 32)] {
        let mut padded_p = vec![0; p_len - p.len()];
        padded_p.extend_from_slice(&p);
        let mut padded_g = vec![0; p_len - g.len()];
        padded_g.extend_from_slice(&g);
        let mut padded_q = vec![0; q_len - q.len()];
        padded_q.extend_from_slice(&q);
        let mut x = vec![0; q_len];
        x[q_len - 1] = 1;
        let key =
            PrivateKey::from_components(&padded_p, &padded_q, &padded_g, &padded_g, &x).unwrap();
        for digest in [vec![], vec![0x42; 16], vec![0x42; 20], vec![0x42; 32]] {
            let signature = key
                .sign_with_rng(&digest, |buf| {
                    assert_eq!(buf.len(), q_len);
                    buf.fill(0);
                    buf[19] = 2;
                    Ok(())
                })
                .unwrap();
            assert_eq!(signature.len(), 2 * q_len);
            assert!(key.public_key().verify(&digest, &signature));
            let mut wrong = digest.clone();
            wrong.insert(0, 1);
            assert!(!key.public_key().verify(&wrong, &signature));
            assert!(
                !key.public_key()
                    .verify(&digest, &signature[..signature.len() - 1])
            );
            let mut zero_r = signature.clone();
            zero_r[..q_len].fill(0);
            assert!(!key.public_key().verify(&digest, &zero_r));
            if digest.len() == 32 {
                let mut same_prefix = digest.clone();
                same_prefix[20..].fill(0xff);
                assert!(key.public_key().verify(&same_prefix, &signature));
            }
        }
    }
}

#[cfg(any(target_arch = "aarch64", target_arch = "powerpc64"))]
#[test]
fn immutable_public_validation_cache() {
    let (key, digest, nonce) = sample();
    let mut signature = vec![0; 2 * key.public.q_len];
    let mut scratch = Secret(vec![0u64; 16 * key.public.p_len]);
    assert!(key.sign_once(&digest, &nonce, &mut signature, &mut scratch.0));
    let public = key.public_key();
    let unchecked = public.clone();
    assert_eq!(unchecked.validated.load(Ordering::Relaxed), 0);
    assert!(!public.verify(&digest, &signature[1..]));
    assert_eq!(public.validated.load(Ordering::Relaxed), 0);
    assert!(public.verify(&digest, &signature));
    assert_eq!(public.validated.load(Ordering::Relaxed), 1);
    let validated = public.clone();
    assert_eq!(validated.validated.load(Ordering::Relaxed), 1);
    assert!(validated.verify(&digest, &signature));
    let mut bad_signature = signature.clone();
    bad_signature[..public.q_len].fill(0);
    assert!(!validated.verify(&digest, &bad_signature));
    bad_signature.copy_from_slice(&signature);
    bad_signature[public.q_len..].fill(0);
    assert!(!validated.verify(&digest, &bad_signature));
    assert!(validated.verify(&digest, &signature));

    // Compare the cached public API against the original fully checked raw API.
    for sig in [&signature, &bad_signature] {
        // SAFETY: supported widths, unchanged packed key, exact signature width
        // and separately allocated scratch with the required capacity.
        let raw = unsafe {
            vg_dsa_verify(
                public.packed.as_ptr(),
                public.packed.len(),
                public.p_len,
                public.q_len,
                sig.as_ptr(),
                sig.len(),
                digest.as_ptr(),
                digest.len(),
                scratch.0.as_mut_ptr(),
                scratch.0.len(),
            )
        };
        assert_eq!(public.verify(&digest, sig), raw == 1);
    }

    let invalid = PublicKey::from_components(&[0; 128], &[0; 20], &[0; 128], &[0; 128]).unwrap();
    assert!(!invalid.verify(&digest, &signature));
    assert_eq!(invalid.validated.load(Ordering::Relaxed), 2);
    assert!(!invalid.verify(&digest, &signature));
    let rejected = invalid.clone();
    assert_eq!(rejected.validated.load(Ordering::Relaxed), 2);
    assert!(!rejected.verify(&digest, &signature));

    // PublicKey remains Send + Sync; simultaneous first calls may each validate.
    let shared = std::sync::Arc::new(unchecked);
    let barrier = std::sync::Arc::new(std::sync::Barrier::new(4));
    let threads: Vec<_> = (0..4)
        .map(|_| {
            let key = shared.clone();
            let barrier = barrier.clone();
            let digest = digest.clone();
            let signature = signature.clone();
            std::thread::spawn(move || {
                barrier.wait();
                assert!(key.verify(&digest, &signature));
            })
        })
        .collect();
    for thread in threads {
        thread.join().unwrap();
    }
    assert_eq!(shared.validated.load(Ordering::Relaxed), 1);
}
