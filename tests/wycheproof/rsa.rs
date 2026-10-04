//! The RSA private-key operation with the CRT key (RSADP, RFC 8017 §5.1.2),
//! with the private keys and ciphertexts of the RSAES decryption vectors
//! (`rsa_pkcs1_*_test.json`, `rsa_oaep_*_test.json`), whose padding is not
//! this primitive's.
//!
//! For each ciphertext of the modulus' length and below it, the result is
//! `c^d mod n` (by the public-key operation with `d` as the exponent), RSAEP
//! of it gives back the ciphertext, and for a valid PKCS #1 v1.5 vector it is
//! an encryption block of type 2 holding the message. Other ciphertexts are
//! refused.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use serde::Deserialize;
use verified_garbage::rsa::{Error, PrivateKey, PublicKey};

use crate::harness::{self, Expectation, Hex};
use crate::require_vectors;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Key {
    modulus: Hex,
    private_exponent: Hex,
    public_exponent: Hex,
    prime1: Hex,
    prime2: Hex,
    exponent1: Hex,
    exponent2: Hex,
    coefficient: Hex,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Group {
    private_key: Key,
}

#[derive(Deserialize)]
struct Case {
    msg: Hex,
    ct: Hex,
}

/// `x` without its leading zero bytes (the vectors write numbers in DER's
/// form, with a zero byte before a top bit that is set).
fn trim(x: &[u8]) -> &[u8] {
    &x[x.iter().take_while(|&&b| b == 0).count()..]
}

/// Checks every vector of `name`; `pkcs1` if its padding is PKCS #1 v1.5's.
/// Returns the numbers of ciphertexts decrypted and refused.
fn check(name: &str, pkcs1: bool) -> (usize, usize) {
    let file = harness::load::<Group, Case>(name);
    let (mut done, mut refused) = (0, 0);
    for group in &file.test_groups {
        let k = &group.params.private_key;
        let n = trim(&k.modulus.0);
        let key = PrivateKey::from_crt(
            n,
            &k.prime1.0,
            &k.prime2.0,
            &k.exponent1.0,
            &k.exponent2.0,
            &k.coefficient.0,
        )
        .unwrap_or_else(|e| panic!("{name}: {e}"));
        let by_d = PublicKey::new(n, trim(&k.private_exponent.0)).unwrap();
        let public = PublicKey::new(n, trim(&k.public_exponent.0)).unwrap();
        for test in &group.tests {
            let id = test.tc_id;
            let ct = &test.case.ct.0;
            let mut out = vec![0xa5; n.len()];
            if ct.len() != n.len() {
                assert_eq!(test.result, Expectation::Invalid, "{name} tcId {id}");
                let r = key.private_op(ct, &mut out);
                assert_eq!(r, Err(Error::InvalidLength), "{name} tcId {id}");
                refused += 1;
                continue;
            }
            if ct.as_slice() >= n {
                assert_eq!(test.result, Expectation::Invalid, "{name} tcId {id}");
                let r = key.private_op(ct, &mut out);
                assert_eq!(r, Err(Error::InputOutOfRange), "{name} tcId {id}");
                assert_eq!(out, vec![0; n.len()], "{name} tcId {id}");
                refused += 1;
                continue;
            }
            key.private_op(ct, &mut out).unwrap();
            let mut by_exp = vec![0; n.len()];
            by_d.public_op(ct, &mut by_exp).unwrap();
            assert_eq!(out, by_exp, "{name} tcId {id}");
            let mut back = vec![0; n.len()];
            public.public_op(&out, &mut back).unwrap();
            assert_eq!(&back, ct, "{name} tcId {id}");
            if pkcs1 && test.result == Expectation::Valid {
                // `00 02 PS 00 M`, with at least 8 bytes of nonzero `PS`.
                assert_eq!(&out[..2], &[0, 2], "{name} tcId {id}");
                let sep = 2 + out[2..].iter().position(|&b| b == 0).unwrap();
                assert!(sep >= 10, "{name} tcId {id}");
                assert_eq!(&out[sep + 1..], &test.case.msg.0[..], "{name} tcId {id}");
            }
            done += 1;
        }
    }
    (done, refused)
}

#[test]
fn rsa_pkcs1_test() {
    require_vectors!();
    for name in [
        "rsa_pkcs1_2048_test.json",
        "rsa_pkcs1_3072_test.json",
        "rsa_pkcs1_4096_test.json",
    ] {
        let (done, refused) = check(name, true);
        assert!(done > 0 && refused > 0, "{name}");
    }
}

#[test]
fn rsa_oaep_test() {
    require_vectors!();
    let names: Vec<String> = harness::all_files()
        .unwrap()
        .into_iter()
        .filter(|n| n.starts_with("rsa_oaep_") && n.ends_with("_test.json"))
        .collect();
    assert!(!names.is_empty());
    let mut done = 0;
    for name in &names {
        done += check(name, false).0;
    }
    assert!(done > 0);
}
