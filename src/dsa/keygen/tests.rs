use super::*;
use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;

use crate::dsa::tests::vectors::{hex, vectors};

fn domain(v: &BTreeMap<String, String>) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
    let p = hex(&v["P"], 0);
    let q = hex(&v["Q"], 0);
    let g = hex(&v["G"], p.len());
    (p, q, g)
}

#[test]
fn cavp_generated_keys() {
    for (i, v) in vectors(
        include_str!("../../../vectors/nist-cavp-dsa/SigGen.txt"),
        true,
    )
    .iter()
    .enumerate()
    {
        let (p, q, g) = domain(v);
        let y = hex(&v["Y"], p.len());
        let x = hex(&v["X"], q.len());
        // A published x is below q, so it is accepted as the first draw.
        let key = PrivateKey::generate_with_rng(&p, &q, &g, |buf| {
            for chunk in buf.chunks_exact_mut(q.len()) {
                chunk.copy_from_slice(&x);
            }
            Ok(())
        })
        .unwrap();
        let packed = [&p[..], &q, &g, &y, &x].concat();
        assert_eq!(key.packed.0, packed, "vector {i}");
        let public = &packed[..packed.len() - q.len()];
        assert_eq!(key.public.packed, public, "vector {i}");
    }
}

#[test]
fn generated_key_rejection_and_replay() {
    let cases = vectors(
        include_str!("../../../vectors/nist-cavp-dsa/SigGen.txt"),
        true,
    );
    let v = &cases[0];
    let (p, q, g) = domain(v);
    let x = hex(&v["X"], q.len());
    let mut draws = 0;
    let key = PrivateKey::generate_with_rng(&p, &q, &g, |buf| {
        if draws == 0 {
            buf.fill(0);
        } else {
            for chunk in buf.chunks_exact_mut(q.len()) {
                chunk.copy_from_slice(&x);
            }
        }
        draws += 1;
        Ok(())
    })
    .unwrap();
    assert_eq!(draws, 2);
    assert_eq!(&key.packed.0[3 * p.len() + q.len()..], &x[..]);
    let digest = [0x42; 32];
    let signature = key.sign(&digest).unwrap();
    assert!(key.public_key().verify(&digest, &signature));
}

#[test]
#[cfg(target_arch = "x86")]
fn generated_key_rejection_within_batch() {
    let cases = vectors(
        include_str!("../../../vectors/nist-cavp-dsa/SigGen.txt"),
        true,
    );
    let (p, q, g) = domain(&cases[0]);
    let x = hex(&cases[0]["X"], q.len());
    let y = hex(&cases[0]["Y"], p.len());
    let mut requests = 0;
    let key = PrivateKey::generate_with_rng(&p, &q, &g, |buf| {
        requests += 1;
        buf.fill(0);
        // Reject the first draw and accept the published scalar next,
        // without returning to Rust for another entropy request.
        buf[q.len()..2 * q.len()].copy_from_slice(&x);
        Ok(())
    })
    .unwrap();
    assert_eq!(requests, 1);
    assert_eq!(key.packed.0, [&p[..], &q, &g, &y, &x].concat());
}

#[test]
fn generated_keys_sign_and_verify() {
    let cases = vectors(
        include_str!("../../../vectors/nist-cavp-dsa/SigGen.txt"),
        true,
    );
    for (p_len, q_len) in [(128, 20), (256, 28), (256, 32), (384, 32)] {
        let v = cases
            .iter()
            .find(|v| hex(&v["P"], 0).len() == p_len && hex(&v["Q"], 0).len() == q_len)
            .unwrap();
        let (p, q, g) = domain(v);
        let key = PrivateKey::generate(&p, &q, &g).unwrap();
        let other = PrivateKey::generate(&p, &q, &g).unwrap();
        assert_ne!(key.packed.0, other.packed.0);
        let digest = [0x5a; 32];
        let signature = key.sign(&digest).unwrap();
        assert!(key.public_key().verify(&digest, &signature));
        assert!(!other.public_key().verify(&digest, &signature));
    }
}

#[test]
fn generation_errors() {
    let cases = vectors(
        include_str!("../../../vectors/nist-cavp-dsa/SigGen.txt"),
        true,
    );
    let (p, q, g) = domain(&cases[0]);
    for (p, q, g) in [
        (&p[..], &q[..], &g[1..]),
        (&p[1..], &q[..], &g[1..]),
        (&p, &q[1..], &g),
    ] {
        assert_eq!(
            PrivateKey::generate_with_rng(p, q, g, |_| panic!("no draw for bad widths"))
                .unwrap_err(),
            Error::Length
        );
    }
    assert_eq!(
        PrivateKey::generate_with_rng(&p, &q, &g, |_| Err(Error::Randomness)).unwrap_err(),
        Error::Randomness
    );
    let mut draws = 0;
    assert_eq!(
        PrivateKey::generate_with_rng(&p, &q, &g, |buf| {
            draws += 1;
            if draws == 1 {
                buf.fill(0);
                Ok(())
            } else {
                Err(Error::Randomness)
            }
        })
        .unwrap_err(),
        Error::Randomness
    );
    draws = 0;
    assert_eq!(
        PrivateKey::generate_with_rng(&p, &q, &g, |buf| {
            buf.fill(0);
            draws += 1;
            Ok(())
        })
        .unwrap_err(),
        Error::InvalidKeyOrNonce
    );
    assert_eq!(draws, 128 / DRAW_BATCH);
    // g = p - 1 has order two, so the domain check fails before any draw is used.
    let mut minus_one = p.clone();
    *minus_one.last_mut().unwrap() -= 1;
    draws = 0;
    assert_eq!(
        PrivateKey::generate_with_rng(&p, &q, &minus_one, |buf| {
            buf.fill(1);
            draws += 1;
            Ok(())
        })
        .unwrap_err(),
        Error::InvalidKeyOrNonce
    );
    assert_eq!(draws, 1);
}

#[test]
fn imported_private_components() {
    let cases = vectors(
        include_str!("../../../vectors/nist-cavp-dsa/SigGen.txt"),
        true,
    );
    // (256, 20) is the 1024/160 domain with its p and g zero-padded.
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
        let key = PrivateKey::from_private_components(&p, &q, &g, &x).unwrap();
        assert_eq!(key.packed.0, [&p[..], &q, &g, &y, &x].concat());
        let signature = key.sign(b"imported key").unwrap();
        assert!(key.public_key().verify(b"imported key", &signature));
        for bad_x in [vec![0; q_len], q.clone(), vec![255; q_len]] {
            assert_eq!(
                PrivateKey::from_private_components(&p, &q, &g, &bad_x).unwrap_err(),
                Error::InvalidKeyOrNonce
            );
        }
        // Invalid domains: g of 0, 1 or p, an even p or q, and a zero q.
        let mut one = vec![0; p_len];
        *one.last_mut().unwrap() = 1;
        let mut even_p = p.clone();
        *even_p.last_mut().unwrap() &= !1;
        let mut even_q = q.clone();
        *even_q.last_mut().unwrap() &= !1;
        let zero_g = vec![0; p_len];
        let zero_q = vec![0; q_len];
        for (p, q, g) in [
            (&p, &q, &zero_g),
            (&p, &q, &one),
            (&p, &q, &p),
            (&even_p, &q, &g),
            (&p, &even_q, &g),
            (&p, &zero_q, &g),
        ] {
            assert_eq!(
                PrivateKey::from_private_components(p, q, g, &x).unwrap_err(),
                Error::InvalidKeyOrNonce
            );
        }
        for (p, q, g, x) in [
            (&p[..1], &q[..], &g[..], &x[..]),
            (&p, &q[..1], &g, &x),
            (&p, &q, &g[..1], &x),
            (&p, &q, &g, &x[..1]),
        ] {
            assert_eq!(
                PrivateKey::from_private_components(p, q, g, x).unwrap_err(),
                Error::Length
            );
        }
    }
}

#[test]
fn legacy_2048_160_key_generation() {
    let (p, q, g) = crate::dsa::tests::legacy_vectors::parameters();
    let key = PrivateKey::generate_with_rng(&p, &q, &g, |buf| {
        assert_eq!(buf.len(), DRAW_BATCH * 20);
        buf.fill(0);
        buf[19] = 1;
        Ok(())
    })
    .unwrap();
    // x = 1 gives y = g, independently of the implementation's exponentiation.
    assert_eq!(&key.public.packed[2 * p.len() + q.len()..], g);
    let digest = [0x42; 32];
    let signature = key.sign(&digest).unwrap();
    assert!(key.public_key().verify(&digest, &signature));
}

#[test]
fn legacy_2048_160_private_import() {
    let (p, q, g) = crate::dsa::tests::legacy_vectors::parameters();
    let mut x = vec![0; q.len()];
    x[q.len() - 1] = 1;
    let key = PrivateKey::from_private_components(&p, &q, &g, &x).unwrap();
    assert_eq!(&key.public.packed[2 * p.len() + q.len()..], g);
    let signature = key.sign(b"legacy private import").unwrap();
    assert!(
        key.public_key()
            .verify(b"legacy private import", &signature)
    );
}
