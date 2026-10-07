//! The RSA private-key operation with the CRT key, checked against the
//! public exponent (RSADP, RFC 8017 §5.1.2), with the private keys and
//! ciphertexts of the RSAES decryption vectors (`rsa_pkcs1_*_test.json`,
//! `rsa_oaep_*_test.json`), whose padding is not this primitive's.
//!
//! For each ciphertext of the modulus' length and below it, the operation
//! succeeds, RSAEP of its result gives back the ciphertext, and for a valid
//! PKCS #1 v1.5 vector it is an encryption block of type 2 holding the
//! message. Other ciphertexts are refused.

#![cfg(all(
    any(target_arch = "x86_64", target_arch = "aarch64"),
    feature = "alloc"
))]

use std::sync::Mutex;

use serde::Deserialize;
use verified_garbage::rsa::{Error, PrivateKey, PublicKey};

use super::harness::{self, Expectation, Hex, TestFile, TestGroup};
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

/// Checks every vector of `group`, of the file `name`; `pkcs1` if its padding
/// is PKCS #1 v1.5's. Returns the numbers of ciphertexts decrypted and
/// refused.
fn check_group(name: &str, group: &TestGroup<Group, Case>, pkcs1: bool) -> (usize, usize) {
    let (mut done, mut refused) = (0, 0);
    let k = &group.params.private_key;
    let n = trim(&k.modulus.0);
    let key = PrivateKey::from_crt(
        n,
        &k.public_exponent.0,
        &k.private_exponent.0,
        &k.prime1.0,
        &k.prime2.0,
        &k.exponent1.0,
        &k.exponent2.0,
        &k.coefficient.0,
    )
    .unwrap_or_else(|e| panic!("{name}: {e}"));
    let public = PublicKey::new(n, &k.public_exponent.0).unwrap();
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
    (done, refused)
}

/// Checks every vector of each of `names` with a key that
/// [`harness::rsa_key_tested`] tests, as `check_group`, and returns
/// the numbers of ciphertexts each file had decrypted and refused. The
/// groups, each with its own key, are shared among threads (`par_each`):
/// one file (`rsa_oaep_misc_test.json`) has 128 keys.
fn check_all(names: &[&str], pkcs1: bool) -> Vec<(usize, usize)> {
    let files: Vec<TestFile<Group, Case>> = names.iter().map(|n| harness::load(n)).collect();
    let groups: Vec<(usize, &TestGroup<Group, Case>)> = files
        .iter()
        .enumerate()
        .flat_map(|(i, f)| f.test_groups.iter().map(move |g| (i, g)))
        .filter(|(_, g)| harness::rsa_key_tested(&g.params.private_key.modulus.0))
        .collect();
    let results = Mutex::new(vec![(0, 0); names.len()]);
    harness::par_each(&groups, |&(i, group)| {
        let (done, refused) = check_group(names[i], group, pkcs1);
        let mut results = results.lock().unwrap();
        results[i].0 += done;
        results[i].1 += refused;
    });
    results.into_inner().unwrap()
}

#[test]
fn rsa_pkcs1_test() {
    require_vectors!();
    let names: Vec<&str> = [
        "rsa_pkcs1_2048_test.json",
        "rsa_pkcs1_3072_test.json",
        "rsa_pkcs1_4096_test.json",
    ]
    .into_iter()
    .filter(|n| harness::rsa_file_tested(n))
    .collect();
    for (name, (done, refused)) in names.iter().zip(check_all(&names, true)) {
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
        .filter(|n| harness::rsa_file_tested(n))
        .collect();
    assert!(!names.is_empty());
    let names: Vec<&str> = names.iter().map(String::as_str).collect();
    let done: usize = check_all(&names, false).iter().map(|r| r.0).sum();
    assert!(done > 0);
}
