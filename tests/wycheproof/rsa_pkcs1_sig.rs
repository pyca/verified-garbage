//! RSASSA-PKCS1-v1_5 (RFC 8017 §8.2), with the verification vectors
//! (`rsa_signature_*_test.json`) and the signatures of the generation
//! vectors (`rsa_pkcs1_*_sig_gen_test.json`), and signing with the CRT keys
//! of the RSAES decryption vectors (`rsa_pkcs1_*_test.json`).
//!
//! A `valid` signature must verify and recover its hash value, an `invalid`
//! one must not; whatever `recover` returns, the signature verifies for it.
//! The generation vectors give no CRT key, so a signature is checked by
//! verifying it: a hash value has exactly one valid signature, the `e`-th
//! root of its encoding.

#![cfg(all(
    any(target_arch = "x86_64", target_arch = "aarch64"),
    feature = "alloc"
))]

use serde::Deserialize;
use verified_garbage::hashes::HashFunction;
use verified_garbage::hashes::{
    md5::Md5, sha1::Sha1, sha3::Sha3_224, sha3::Sha3_256, sha3::Sha3_384, sha3::Sha3_512,
    sha224::Sha224, sha256::Sha256, sha384::Sha384, sha512::Sha512, sha512_224::Sha512_224,
    sha512_256::Sha512_256,
};
use verified_garbage::rsa::{PrivateKey, PublicKey};
use verified_garbage::rsa_pkcs1_sig::{Hash, recover, sign, verify};

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
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct GenGroup {
    private_key: Public,
    sha: String,
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

/// `x` without its leading zero bytes (the vectors write numbers in DER's
/// form, with a zero byte before a top bit that is set).
fn trim(x: &[u8]) -> &[u8] {
    &x[x.iter().take_while(|&&b| b == 0).count()..]
}

const HASHES: [Hash; 12] = [
    Hash::Md5,
    Hash::Sha1,
    Hash::Sha224,
    Hash::Sha256,
    Hash::Sha384,
    Hash::Sha512,
    Hash::Sha512_224,
    Hash::Sha512_256,
    Hash::Sha3_224,
    Hash::Sha3_256,
    Hash::Sha3_384,
    Hash::Sha3_512,
];

/// The hash functions by the names the vectors give them.
const NAMES: [(&str, Hash); 11] = [
    ("SHA-1", Hash::Sha1),
    ("SHA-224", Hash::Sha224),
    ("SHA-256", Hash::Sha256),
    ("SHA-384", Hash::Sha384),
    ("SHA-512", Hash::Sha512),
    ("SHA-512/224", Hash::Sha512_224),
    ("SHA-512/256", Hash::Sha512_256),
    ("SHA3-224", Hash::Sha3_224),
    ("SHA3-256", Hash::Sha3_256),
    ("SHA3-384", Hash::Sha3_384),
    ("SHA3-512", Hash::Sha3_512),
];

/// The hash function a group's `sha` names.
fn hash(sha: &str) -> Hash {
    NAMES
        .iter()
        .find(|(n, _)| *n == sha)
        .expect("a known hash function")
        .1
}

/// The hash value of `msg` with `h`.
fn digest(h: Hash, msg: &[u8]) -> Vec<u8> {
    match h {
        Hash::Sha1 => Sha1::digest(msg).as_ref().to_vec(),
        Hash::Sha224 => Sha224::digest(msg).as_ref().to_vec(),
        Hash::Sha256 => Sha256::digest(msg).as_ref().to_vec(),
        Hash::Sha384 => Sha384::digest(msg).as_ref().to_vec(),
        Hash::Sha512 => Sha512::digest(msg).as_ref().to_vec(),
        Hash::Sha512_224 => Sha512_224::digest(msg).as_ref().to_vec(),
        Hash::Sha512_256 => Sha512_256::digest(msg).as_ref().to_vec(),
        Hash::Sha3_224 => <Sha3_224 as HashFunction>::digest(msg).as_ref().to_vec(),
        Hash::Sha3_256 => <Sha3_256 as HashFunction>::digest(msg).as_ref().to_vec(),
        Hash::Sha3_384 => <Sha3_384 as HashFunction>::digest(msg).as_ref().to_vec(),
        Hash::Sha3_512 => <Sha3_512 as HashFunction>::digest(msg).as_ref().to_vec(),
        Hash::Md5 => Md5::digest(msg).as_ref().to_vec(),
    }
}

/// Checks `sig` for the hash value `d` against the expectation `result`:
/// returns whether it verifies. `recover` returns `d` exactly when it
/// verifies, and otherwise either nothing or a value it verifies for.
fn check(
    name: &str,
    id: u64,
    key: &PublicKey,
    h: Hash,
    d: &[u8],
    sig: &[u8],
    result: Expectation,
) -> bool {
    let ok = verify(key, sig, d, h);
    match result {
        Expectation::Valid => assert!(ok, "{name} tcId {id}"),
        Expectation::Invalid => assert!(!ok, "{name} tcId {id}"),
        Expectation::Acceptable => {}
    }
    match recover(key, sig, h) {
        Ok(v) => {
            assert_eq!(v == d, ok, "{name} tcId {id}");
            assert!(verify(key, sig, &v, h), "{name} tcId {id}");
        }
        Err(_) => assert!(!ok, "{name} tcId {id}"),
    }
    ok
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
        let file = harness::load::<VerifyGroup, SigCase>(name);
        let (accepted, rejected) = (Count::default(), Count::default());
        let keys = |group: &harness::TestGroup<VerifyGroup, SigCase>| {
            let p = &group.params.public_key;
            PublicKey::new(trim(&p.modulus.0), &p.public_exponent.0).unwrap()
        };
        file.par_tests_with(keys, |group, key, test| {
            let h = hash(&group.params.sha);
            let d = digest(h, &test.case.msg.0);
            if check(name, test.tc_id, key, h, &d, &test.case.sig.0, test.result) {
                accepted.add();
            } else {
                rejected.add();
            }
        });
        assert!(accepted.get() > 0 && rejected.get() > 0, "{name}");
    }
}

/// The signatures of the generation vectors are valid (those with a weak
/// hash function or key are only `acceptable`, but still valid).
#[test]
fn rsa_pkcs1_sig_gen_test() {
    require_vectors!();
    for bits in [1024, 1536, 2048, 3072, 4096] {
        let name = format!("rsa_pkcs1_{bits}_sig_gen_test.json");
        let file = harness::load::<GenGroup, SigCase>(&name);
        let keys = |group: &harness::TestGroup<GenGroup, SigCase>| {
            let p = &group.params.private_key;
            PublicKey::new(trim(&p.modulus.0), &p.public_exponent.0).unwrap()
        };
        file.par_tests_with(keys, |group, key, test| {
            let h = hash(&group.params.sha);
            let d = digest(h, &test.case.msg.0);
            assert!(check(
                &name,
                test.tc_id,
                key,
                h,
                &d,
                &test.case.sig.0,
                Expectation::Valid
            ));
        });
    }
}

/// Signing with each CRT key of the decryption vectors, the hash values of
/// their messages with every hash function that fits the modulus: the
/// signature verifies, recovers the hash value, and is the same each time.
#[test]
fn rsa_pkcs1_sign_test() {
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
            for (test, h) in group.tests.iter().take(4).zip(HASHES.iter().cycle()) {
                let id = test.tc_id;
                let d = digest(*h, &test.case.msg.0);
                let sig =
                    sign(&private, &d, *h).unwrap_or_else(|e| panic!("{name} tcId {id}: {e}"));
                assert_eq!(sig.len(), n.len(), "{name} tcId {id}");
                assert!(check(&name, id, &public, *h, &d, &sig, Expectation::Valid));
                assert_eq!(sign(&private, &d, *h), Ok(sig), "{name} tcId {id}");
            }
            for h in HASHES {
                let d = digest(h, b"");
                let sig = sign(&private, &d, h).unwrap();
                assert!(check(&name, 0, &public, h, &d, &sig, Expectation::Valid));
                let mut other = d.clone();
                other[0] ^= 1;
                assert!(!verify(&public, &sig, &other, h), "{name}");
            }
        });
    }
}
