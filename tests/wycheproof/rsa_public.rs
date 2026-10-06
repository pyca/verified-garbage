//! The RSA public-key operation (RSAVP1, RFC 8017 §5.2.2) on its own, with
//! the RSASSA-PKCS1-v1_5 verification vectors (`rsa_signature_*_test.json`)
//! but without the padding module: in each group, the encoding of a hash
//! value (`0x00 0x01`, bytes `0xff`, `0x00`, then the hash function's
//! `DigestInfo` prefix and the hash value, §9.2) is learnt from a `valid`
//! signature, whose operation must give `0x00 0x01`, `0xff` bytes, `0x00` and
//! a string that ends with the message's hash value. Then the operation on a
//! signature gives the encoding of its message's hash value exactly when the
//! signature is `valid`; a signature that is not of the modulus' length or
//! not below it is refused.

#![cfg(all(
    any(target_arch = "x86_64", target_arch = "aarch64"),
    feature = "alloc"
))]

use serde::Deserialize;
use verified_garbage::hashes::HashFunction;
use verified_garbage::hashes::{
    sha1::Sha1, sha3::Sha3_224, sha3::Sha3_256, sha3::Sha3_384, sha3::Sha3_512, sha224::Sha224,
    sha256::Sha256, sha384::Sha384, sha512::Sha512, sha512_224::Sha512_224, sha512_256::Sha512_256,
};
use verified_garbage::rsa::{Error, PublicKey};

use crate::harness::{self, Expectation, Hex};
use crate::require_vectors;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Public {
    modulus: Hex,
    public_exponent: Hex,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Group {
    public_key: Public,
    sha: String,
}

#[derive(Deserialize)]
struct Case {
    msg: Hex,
    sig: Hex,
}

/// `x` without its leading zero bytes (the vectors write numbers in DER's
/// form, with a zero byte before a top bit that is set).
fn trim(x: &[u8]) -> &[u8] {
    &x[x.iter().take_while(|&&b| b == 0).count()..]
}

/// A hash function, to its value as bytes.
type Digest = fn(&[u8]) -> Vec<u8>;

/// The hash functions by the names the vectors give them.
const HASHES: [(&str, Digest); 11] = [
    ("SHA-1", |m| Sha1::digest(m).as_ref().to_vec()),
    ("SHA-224", |m| Sha224::digest(m).as_ref().to_vec()),
    ("SHA-256", |m| Sha256::digest(m).as_ref().to_vec()),
    ("SHA-384", |m| Sha384::digest(m).as_ref().to_vec()),
    ("SHA-512", |m| Sha512::digest(m).as_ref().to_vec()),
    ("SHA-512/224", |m| Sha512_224::digest(m).as_ref().to_vec()),
    ("SHA-512/256", |m| Sha512_256::digest(m).as_ref().to_vec()),
    ("SHA3-224", |m| {
        <Sha3_224 as HashFunction>::digest(m).as_ref().to_vec()
    }),
    ("SHA3-256", |m| {
        <Sha3_256 as HashFunction>::digest(m).as_ref().to_vec()
    }),
    ("SHA3-384", |m| {
        <Sha3_384 as HashFunction>::digest(m).as_ref().to_vec()
    }),
    ("SHA3-512", |m| {
        <Sha3_512 as HashFunction>::digest(m).as_ref().to_vec()
    }),
];

/// The hash value of `msg` with the hash function the vectors call `sha`.
fn digest(sha: &str, msg: &[u8]) -> Vec<u8> {
    let (_, f) = HASHES
        .iter()
        .find(|(n, _)| *n == sha)
        .expect("a known hash function");
    f(msg)
}

/// RSAVP1 of `sig`, or `None` if the operation refuses it (leaving zeros).
fn vp1(key: &PublicKey, sig: &[u8]) -> Option<Vec<u8>> {
    let k = key.modulus_len();
    let mut out = vec![0xa5; k];
    match key.public_op(sig, &mut out) {
        Ok(()) => Some(out),
        Err(Error::InvalidLength) => {
            assert_ne!(sig.len(), k);
            None
        }
        Err(e) => {
            assert_eq!(e, Error::InputOutOfRange);
            assert_eq!(out, vec![0; k]);
            None
        }
    }
}

/// The `DigestInfo` prefix of an encoding `em` of the hash value `d`
/// (`0x00 0x01`, `0xff` bytes, `0x00`, the prefix, `d`).
fn prefix(em: &[u8], d: &[u8]) -> Vec<u8> {
    assert!(em.ends_with(d));
    assert_eq!(em[..2], [0, 1]);
    let pad = em[2..].iter().take_while(|&&b| b == 0xff).count();
    assert!(pad >= 8);
    assert_eq!(em[2 + pad], 0);
    em[3 + pad..em.len() - d.len()].to_vec()
}

/// The `k`-byte encoding of the hash value `d` with the `DigestInfo` prefix
/// `p`.
fn encoding(k: usize, p: &[u8], d: &[u8]) -> Vec<u8> {
    let mut em = vec![0, 1];
    em.resize(k - 1 - p.len() - d.len(), 0xff);
    em.push(0);
    em.extend_from_slice(p);
    em.extend_from_slice(d);
    em
}

#[test]
fn rsa_signature_test() {
    require_vectors!();
    let names: Vec<String> = harness::all_files()
        .unwrap()
        .into_iter()
        .filter(|n| n.starts_with("rsa_signature_"))
        .collect();
    assert_eq!(names.len(), 24);
    for name in &names {
        let file = harness::load::<Group, Case>(name);
        let (mut accepted, mut rejected) = (0, 0);
        for group in &file.test_groups {
            let p = &group.params.public_key;
            let key = PublicKey::new(trim(&p.modulus.0), &p.public_exponent.0).unwrap();
            let k = key.modulus_len();
            let sha = &group.params.sha;
            let cases: Vec<_> = group
                .tests
                .iter()
                .map(|t| (t, digest(sha, &t.case.msg.0), vp1(&key, &t.case.sig.0)))
                .collect();
            let (_, d, em) = cases
                .iter()
                .find(|(t, _, _)| t.result == Expectation::Valid)
                .expect("a valid signature");
            let p = prefix(em.as_ref().expect("a valid signature's operation"), d);
            for (t, d, em) in &cases {
                let ok = em.as_ref() == Some(&encoding(k, &p, d));
                match t.result {
                    Expectation::Valid => assert!(ok, "{name} tcId {}", t.tc_id),
                    Expectation::Invalid => assert!(!ok, "{name} tcId {}", t.tc_id),
                    Expectation::Acceptable => {}
                }
                if ok {
                    accepted += 1;
                } else {
                    rejected += 1;
                }
            }
        }
        assert!(accepted > 0 && rejected > 0, "{name}");
    }
}
