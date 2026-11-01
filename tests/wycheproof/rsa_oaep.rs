//! RSAES-OAEP decryption and encryption with the Wycheproof vectors
//! `rsa_oaep_*_test.json`.
//!
//! A `valid` vector (and an `acceptable` one, whose ciphertext is a small
//! integer) decrypts to its message, and so does that message encrypted
//! again; an `invalid` one is refused, as of the wrong length if its
//! ciphertext is, and otherwise with the one error for every failure of
//! the ciphertext and its decoding. The pairs of hash functions the module
//! does not support (some of `rsa_oaep_misc_test.json`'s) are refused as
//! such. The files of three-prime keys are not this module's. And every
//! pair the module supports encrypts and decrypts with a key of the vectors
//! (`rsa_oaep_every_pair`).

#![cfg(all(
    any(
        target_arch = "x86",
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64"
    ),
    feature = "alloc"
))]

use crate::json_struct;
use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::rsa::{PrivateKey, PublicKey};
use verified_garbage::rsa_oaep::{Error, Hash, decrypt, encrypt};
use verified_garbage::{rsa_pkcs1_sig, rsa_pss};

use super::harness::{self, Count, Expectation, Hex, TestFile, TestGroup};
use super::schema::{MsgCase, RsaPrivateKey as Key, RsaPrivateKeyGroup as Pkcs1Group};
use crate::bytes::trim_zeros as trim;
use crate::require_vectors;

json_struct! {
    struct Group {
        sha: String,
        #[json(rename = "mgfSha")]
        mgf_sha: String,
        #[json(rename = "privateKey")]
        private_key: Key,
    }
}

json_struct! {
    struct Case {
        msg: Hex,
        ct: Hex,
        label: Hex,
    }
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

/// The private and public keys of `k`, of the file `name`.
fn keys(name: &str, k: &Key) -> (PrivateKey, PublicKey) {
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
    (key, PublicKey::new(n, &k.public_exponent.0).unwrap())
}

/// Checks every vector of the file `name` with a key that
/// [`harness::rsa_key_tested`] tests; returns the numbers of decrypted,
/// refused and unsupported vectors.
fn check(name: &str) -> (usize, usize, usize) {
    let (valid, refused, unsupported) = (Count::default(), Count::default(), Count::default());
    let mut file: TestFile<Group, Case> = harness::load(name);
    file.test_groups
        .retain(|g| harness::rsa_key_tested(&g.params.private_key.modulus.0));
    let keys = |group: &TestGroup<Group, Case>| keys(name, &group.params.private_key);
    file.par_tests_with(keys, |group, (key, public), test| {
        let p = &group.params;
        let (h, g) = (hash(&p.sha), hash(&p.mgf_sha));
        let n = trim(&p.private_key.modulus.0);
        let id = test.tc_id;
        let (ct, label, msg) = (&test.case.ct.0, &test.case.label.0, &test.case.msg.0);
        let r = decrypt(key, ct, h, g, label);
        if r == Err(Error::UnsupportedHash) {
            let e = encrypt(public, msg, h, g, label);
            assert_eq!(e, Err(Error::UnsupportedHash), "{name} tcId {id}");
            unsupported.add();
        } else if test.result == Expectation::Invalid {
            let e = if ct.len() == n.len() {
                Error::Decryption
            } else {
                Error::InvalidLength
            };
            assert_eq!(r, Err(e), "{name} tcId {id}");
            refused.add();
        } else {
            assert_eq!(r.as_deref(), Ok(&msg[..]), "{name} tcId {id}");
            let again = encrypt(public, msg, h, g, label).unwrap();
            assert_eq!(decrypt(key, &again, h, g, label), r, "{name} tcId {id}");
            valid.add();
        }
    });
    (valid.get(), refused.get(), unsupported.get())
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
    let mut unsupported = 0;
    for name in &names {
        let (valid, refused, u) = check(name);
        assert!(valid > 0, "{name}");
        assert!(refused > 0 || name == "rsa_oaep_misc_test.json", "{name}");
        unsupported += u;
    }
    assert!(unsupported > 0);
}

/// Every pair of hash functions the module supports, with a 2048-bit key of
/// the vectors: the longest message the modulus allows decrypts from its
/// encryption, and not with another label, and ciphertexts that are not
/// the pair's encryption of anything are refused. This runs each pair with the
/// implementations a line of CI's `rust-cpu-features` chooses even where its
/// files do not: SHA-512/256's have only 3072-bit keys, which an emulated
/// CPU with AVX512_IFMA leaves out ([`harness::rsa_bits_tested`]); and it is
/// all the lines that are there only to choose an implementation run
/// (`rsa_oaep_pairs` in `ci/cpu_tests.py`).
#[test]
fn rsa_oaep_every_pair() {
    require_vectors!();
    let name = "rsa_oaep_2048_sha256_mgf1sha256_test.json";
    let file: TestFile<Group, Case> = harness::load(name);
    let (key, public) = keys(name, &file.test_groups[0].params.private_key);
    let n = trim(&file.test_groups[0].params.private_key.modulus.0);
    let k = public.modulus_len();
    assert_eq!(n.len(), k);
    // Each hash function with MGF1 over itself and over SHA-1.
    let mut pairs: Vec<(Hash, Hash)> = HASHES
        .iter()
        .flat_map(|&(_, h)| [(h, h), (h, Hash::Sha1)])
        .collect();
    pairs.dedup();
    assert_eq!(pairs.len(), 13);
    for (i, &(h, g)) in pairs.iter().enumerate() {
        let msg: Vec<u8> = (0..k - 2 * h.digest_len() - 2).map(|i| i as u8).collect();
        let ct = encrypt(&public, &msg, h, g, b"label").unwrap();
        assert_eq!(decrypt(&key, &ct, h, g, b"label"), Ok(msg), "{h:?} {g:?}");
        let other = decrypt(&key, &ct, h, g, b"other");
        assert_eq!(other, Err(Error::Decryption), "{h:?} {g:?}");
        // Ciphertexts as long as the modulus, which reach this pair's
        // decryption and fail in it: one bit flipped; the next pair's
        // encoding of a message; zero, whose encoding is all zeros; and the
        // modulus and every bit set, which are not below the modulus.
        let mut flipped = ct.clone();
        flipped[k / 2] ^= 1;
        let (h2, g2) = pairs[(i + 1) % pairs.len()];
        let next = encrypt(&public, b"message", h2, g2, b"label").unwrap();
        for (what, bad) in [
            ("one bit flipped", flipped),
            ("the next pair's", next),
            ("zero", vec![0; k]),
            ("the modulus", n.to_vec()),
            ("every bit set", vec![0xff; k]),
        ] {
            let r = decrypt(&key, &bad, h, g, b"label");
            assert_eq!(r, Err(Error::Decryption), "{h:?} {g:?}: {what}");
        }
    }
}

/// With each CRT key of the RSAES-PKCS1-v1_5 decryption vectors
/// (`rsa_pkcs1_*_test.json`), of the sizes the RSA tests run
/// (`harness::rsa_bits_tested`): PSS and PKCS #1 v1.5 verification and OAEP
/// encryption, which lease the public key's buffer, alternated on threads
/// sharing the key.
#[test]
fn rsa_shared_key_leases() {
    require_vectors!();
    for bits in [2048, 3072, 4096]
        .into_iter()
        .filter(|&b| harness::rsa_bits_tested(b))
    {
        shared_key_leases(bits, usize::MAX, 4);
    }
}

/// Concurrent callers with one vector key, for emulated backends; the full
/// stress test remains on native and SKX jobs.
#[test]
fn rsa_shared_key_leases_smoke() {
    require_vectors!();
    shared_key_leases(2048, 1, 1);
}

fn shared_key_leases(bits: usize, groups: usize, repetitions: usize) {
    let name = format!("rsa_pkcs1_{bits}_test.json");
    let file = harness::load::<Pkcs1Group, MsgCase>(&name);
    harness::par_each(
        &file.test_groups[..groups.min(file.test_groups.len())],
        |group| {
            let (private, public) = keys(&name, &group.params.private_key);
            // Signature verification and OAEP encryption lease the same key's
            // buffer, with different workspace lengths. Alternate them, including
            // rejected inputs, and share the key across concurrent callers.
            let d = Sha256::digest(&group.tests[0].case.msg.0).as_ref().to_vec();
            let sig = rsa_pkcs1_sig::sign(&private, &d, rsa_pkcs1_sig::Hash::Sha256).unwrap();
            let pss = rsa_pss::sign(
                &private,
                &d,
                rsa_pss::Hash::Sha256,
                rsa_pss::Hash::Sha256,
                0,
            )
            .unwrap();
            std::thread::scope(|scope| {
                for _ in 0..4 {
                    let (public, d, sig, pss) = (&public, &d, &sig, &pss);
                    let private = &private;
                    scope.spawn(move || {
                        for _ in 0..repetitions {
                            assert!(rsa_pkcs1_sig::verify(
                                public,
                                sig,
                                d,
                                rsa_pkcs1_sig::Hash::Sha256
                            ));
                            assert!(!rsa_pkcs1_sig::verify(
                                public,
                                &sig[..sig.len() - 1],
                                d,
                                rsa_pkcs1_sig::Hash::Sha256
                            ));
                            assert!(rsa_pss::verify(
                                public,
                                pss,
                                d,
                                rsa_pss::Hash::Sha256,
                                rsa_pss::Hash::Sha256,
                                rsa_pss::SaltLength::Len(0),
                            ));
                            assert!(!rsa_pkcs1_sig::verify(
                                public,
                                sig,
                                &d[..d.len() - 1],
                                rsa_pkcs1_sig::Hash::Sha256
                            ));
                            let ciphertext = verified_garbage::rsa_oaep::encrypt(
                                public,
                                d,
                                verified_garbage::rsa_oaep::Hash::Sha256,
                                verified_garbage::rsa_oaep::Hash::Sha256,
                                b"",
                            )
                            .unwrap();
                            assert_eq!(
                                verified_garbage::rsa_oaep::decrypt(
                                    private,
                                    &ciphertext,
                                    verified_garbage::rsa_oaep::Hash::Sha256,
                                    verified_garbage::rsa_oaep::Hash::Sha256,
                                    b"",
                                )
                                .unwrap(),
                                *d,
                            );
                            assert!(rsa_pkcs1_sig::verify(
                                public,
                                sig,
                                d,
                                rsa_pkcs1_sig::Hash::Sha256
                            ));
                        }
                    });
                }
            });
        },
    );
}
