//! RSASSA-PSS (RFC 8017 §8.1), with the verification vectors
//! (`rsa_pss_*_test.json`, those without parameters in the key), and signing
//! with the CRT keys of the RSAES decryption vectors
//! (`rsa_pkcs1_*_test.json`).
//!
//! A group with MGF1 over the hash value's hash function is checked: a
//! `valid` signature must verify with the group's salt length and with any,
//! an `invalid` one must not verify with the group's. MGF1 over another hash
//! function is not supported, so nothing verifies with it.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use serde::Deserialize;
use verified_garbage::hashes::{
    md5::Md5, sha1::Sha1, sha224::Sha224, sha256::Sha256, sha384::Sha384, sha512::Sha512,
    sha512_224::Sha512_224, sha512_256::Sha512_256,
};
use verified_garbage::rsa::{PrivateKey, PublicKey};
use verified_garbage::rsa_pss::{Hash, SaltLength, sign, verify};

use super::harness::{self, Count, Expectation, Hex};
use crate::require_vectors;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Public {
    modulus: Hex,
    public_exponent: Hex,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct VerifyGroup {
    public_key: Public,
    sha: String,
    mgf_sha: String,
    s_len: usize,
}

#[derive(Deserialize)]
struct SigCase {
    msg: Hex,
    sig: Hex,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Crt {
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
struct CrtGroup {
    private_key: Crt,
}

#[derive(Deserialize)]
struct MsgCase {
    msg: Hex,
}

/// `x` without its leading zero bytes.
fn trim(x: &[u8]) -> &[u8] {
    &x[x.iter().take_while(|&&b| b == 0).count()..]
}

const HASHES: [(&str, Hash); 8] = [
    ("MD5", Hash::Md5),
    ("SHA-1", Hash::Sha1),
    ("SHA-224", Hash::Sha224),
    ("SHA-256", Hash::Sha256),
    ("SHA-384", Hash::Sha384),
    ("SHA-512", Hash::Sha512),
    ("SHA-512/224", Hash::Sha512_224),
    ("SHA-512/256", Hash::Sha512_256),
];

/// The hash function a group names, if it is one of RSASSA-PSS's here.
fn hash(name: &str) -> Option<Hash> {
    HASHES.iter().find(|(n, _)| *n == name).map(|(_, h)| *h)
}

/// The hash value of `msg` with `h`.
fn digest(h: Hash, msg: &[u8]) -> Vec<u8> {
    match h {
        Hash::Md5 => Md5::digest(msg).as_ref().to_vec(),
        Hash::Sha1 => Sha1::digest(msg).as_ref().to_vec(),
        Hash::Sha224 => Sha224::digest(msg).as_ref().to_vec(),
        Hash::Sha256 => Sha256::digest(msg).as_ref().to_vec(),
        Hash::Sha384 => Sha384::digest(msg).as_ref().to_vec(),
        Hash::Sha512 => Sha512::digest(msg).as_ref().to_vec(),
        Hash::Sha512_224 => Sha512_224::digest(msg).as_ref().to_vec(),
        Hash::Sha512_256 => Sha512_256::digest(msg).as_ref().to_vec(),
    }
}

#[test]
fn rsa_pss_test() {
    require_vectors!();
    let names: Vec<String> = harness::all_files()
        .unwrap()
        .into_iter()
        .filter(|n| n.starts_with("rsa_pss_") && !n.contains("_params_") && !n.contains("shake"))
        .collect();
    assert_eq!(names.len(), 13);
    for name in &names {
        let file = harness::load::<VerifyGroup, SigCase>(name);
        let (accepted, rejected) = (Count::default(), Count::default());
        let keys = |group: &harness::TestGroup<VerifyGroup, SigCase>| {
            let p = &group.params.public_key;
            PublicKey::new(trim(&p.modulus.0), &p.public_exponent.0)
                .unwrap_or_else(|e| panic!("{name}: {e}"))
        };
        file.par_tests_with(keys, |group, key, test| {
            let p = &group.params;
            let h = hash(&p.sha).expect("a supported hash function");
            let mgf = hash(&p.mgf_sha).expect("a supported hash function");
            let id = test.tc_id;
            let (d, sig) = (digest(h, &test.case.msg.0), &test.case.sig.0);
            let ok = verify(key, sig, &d, h, mgf, SaltLength::Len(p.s_len));
            let any = verify(key, sig, &d, h, mgf, SaltLength::Any);
            if mgf != h {
                assert!(!ok && !any, "{name} tcId {id}");
                return;
            }
            assert_ne!(test.result, Expectation::Acceptable, "{name} tcId {id}");
            assert_eq!(ok, test.result == Expectation::Valid, "{name} tcId {id}");
            // A signature with the expected salt length has some salt length.
            assert!(!ok || any, "{name} tcId {id}");
            if ok {
                accepted.add();
            } else {
                rejected.add();
            }
        });
        let (accepted, rejected) = (accepted.get(), rejected.get());
        if name.contains("mgf1sha1") {
            assert_eq!(accepted + rejected, 0, "{name}");
        } else {
            // The miscellaneous vectors are all valid.
            let both = rejected > 0 || name.contains("misc");
            assert!(accepted > 0 && both, "{name}");
        }
    }
}

/// Signing with each CRT key of the decryption vectors, the hash values of
/// their messages with every hash function, with salts of no bytes and of
/// the hash value's length: the signature verifies with its salt length and
/// with any, and not with another; and two signatures with random salts
/// differ. Every size of key, even where the other RSA tests leave out
/// those of 3072 and 4096 bits (`harness::rsa_bits_tested`).
#[test]
fn rsa_pss_sign_test() {
    require_vectors!();
    for bits in [2048, 3072, 4096] {
        let name = format!("rsa_pkcs1_{bits}_test.json");
        let file = harness::load::<CrtGroup, MsgCase>(&name);
        harness::par_each(&file.test_groups, |group| {
            let k = &group.params.private_key;
            let n = trim(&k.modulus.0);
            let private = PrivateKey::from_crt(
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
            for (test, (_, h)) in group.tests.iter().take(8).zip(HASHES.iter()) {
                let id = test.tc_id;
                let d = digest(*h, &test.case.msg.0);
                for s_len in [0, h.digest_len()] {
                    let sig = sign(&private, &d, *h, *h, s_len)
                        .unwrap_or_else(|e| panic!("{name} tcId {id}: {e}"));
                    assert_eq!(sig.len(), n.len(), "{name} tcId {id}");
                    assert!(verify(&public, &sig, &d, *h, *h, SaltLength::Len(s_len)));
                    assert!(verify(&public, &sig, &d, *h, *h, SaltLength::Any));
                    assert!(!verify(
                        &public,
                        &sig,
                        &d,
                        *h,
                        *h,
                        SaltLength::Len(s_len + 1)
                    ));
                }
                let a = sign(&private, &d, *h, *h, 16).unwrap();
                let b = sign(&private, &d, *h, *h, 16).unwrap();
                assert_ne!(a, b, "{name} tcId {id}");
            }
        });
    }
}
