//! RSAES-OAEP decryption and encryption with the Wycheproof vectors
//! `rsa_oaep_*_test.json`.
//!
//! A `valid` vector (and an `acceptable` one, whose ciphertext is a small
//! integer) decrypts to its message, and so does that message encrypted
//! again; an `invalid` one is refused, as of the wrong length if its
//! ciphertext is, and otherwise with the one error for every failure of
//! the ciphertext and its decoding. The pairs of hash functions the module
//! does not support (some of `rsa_oaep_misc_test.json`'s) are refused as
//! such. The files of three-prime keys are not this module's.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use serde::Deserialize;
use verified_garbage::rsa::{PrivateKey, PublicKey};
use verified_garbage::rsa_oaep::{Error, Hash, decrypt, encrypt};

use crate::harness::{self, Expectation, Hex, TestFile};
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
    sha: String,
    mgf_sha: String,
    private_key: Key,
}

#[derive(Deserialize)]
struct Case {
    msg: Hex,
    ct: Hex,
    label: Hex,
}

/// `x` without its leading zero bytes (the vectors write numbers in DER's
/// form, with a zero byte before a top bit that is set).
fn trim(x: &[u8]) -> &[u8] {
    &x[x.iter().take_while(|&&b| b == 0).count()..]
}

/// The hash functions by the vectors' names for them.
const HASHES: [(&str, Hash); 7] = [
    ("SHA-1", Hash::Sha1),
    ("SHA-224", Hash::Sha224),
    ("SHA-256", Hash::Sha256),
    ("SHA-384", Hash::Sha384),
    ("SHA-512", Hash::Sha512),
    ("SHA-512/224", Hash::Sha512_224),
    ("SHA-512/256", Hash::Sha512_256),
];

fn hash(name: &str) -> Hash {
    HASHES.iter().find(|(n, _)| *n == name).expect(name).1
}

/// Checks every vector of the file `name`; returns the numbers of
/// decrypted, refused and unsupported vectors.
fn check(name: &str) -> (usize, usize, usize) {
    let (mut valid, mut refused, mut unsupported) = (0, 0, 0);
    let file: TestFile<Group, Case> = harness::load(name);
    for group in &file.test_groups {
        let p = &group.params;
        let (h, g) = (hash(&p.sha), hash(&p.mgf_sha));
        let k = &p.private_key;
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
            let (ct, label, msg) = (&test.case.ct.0, &test.case.label.0, &test.case.msg.0);
            let r = decrypt(&key, ct, h, g, label);
            if r == Err(Error::UnsupportedHash) {
                assert_eq!(
                    encrypt(&public, msg, h, g, label),
                    Err(Error::UnsupportedHash),
                    "{name} tcId {id}"
                );
                unsupported += 1;
            } else if test.result == Expectation::Invalid {
                let e = if ct.len() == n.len() {
                    Error::Decryption
                } else {
                    Error::InvalidLength
                };
                assert_eq!(r, Err(e), "{name} tcId {id}");
                refused += 1;
            } else {
                assert_eq!(r.as_deref(), Ok(&msg[..]), "{name} tcId {id}");
                let again = encrypt(&public, msg, h, g, label).unwrap();
                assert_eq!(decrypt(&key, &again, h, g, label), r, "{name} tcId {id}");
                valid += 1;
            }
        }
    }
    (valid, refused, unsupported)
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
    let mut unsupported = 0;
    for name in &names {
        let (valid, refused, u) = check(name);
        assert!(valid > 0, "{name}");
        assert!(refused > 0 || name == "rsa_oaep_misc_test.json", "{name}");
        unsupported += u;
    }
    assert!(unsupported > 0);
}
