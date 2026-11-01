//! RSAES-PKCS1-v1_5 decryption with implicit rejection
//! (draft-irtf-cfrg-rsa-guidance-10 §7.2), and encryption, with the
//! Wycheproof vectors `rsa_pkcs1_*_test.json`.
//!
//! Wycheproof labels a ciphertext whose padding is not valid
//! (`InvalidPkcs1Padding`) `invalid`, for an implementation that reports the
//! error. With implicit rejection such a ciphertext is never refused: it
//! decrypts to a message derived from the key and the ciphertext, the same
//! every time, of at most `k - 11` bytes, which is what is checked of those
//! vectors (the draft's own vectors check the messages themselves). The
//! other `invalid` vectors have a ciphertext of the wrong length or not
//! below the modulus, which is refused. A `valid` vector decrypts to its
//! message, and so does that message encrypted again.

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

use verified_garbage::rsa::{PrivateKey, PublicKey};
use verified_garbage::rsa_pkcs1_enc::{Error, decrypt, encrypt};

use super::harness::{self, Count, Expectation, TestFile, TestGroup};
use super::schema::{EncryptCase as Case, RsaPrivateKeyGroup as Group};
use crate::bytes::trim_zeros as trim;
use crate::require_vectors;

/// Checks every vector of the file `name`; returns the numbers of valid
/// vectors, of invalid paddings and of refused ciphertexts.
fn check(name: &str) -> (usize, usize, usize) {
    let (valid, padding, refused) = (Count::default(), Count::default(), Count::default());
    let file: TestFile<Group, Case> = harness::load(name);
    let keys = |group: &TestGroup<Group, Case>| {
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
        (key, PublicKey::new(n, &k.public_exponent.0).unwrap())
    };
    file.par_tests_with(keys, |group, (key, public), test| {
        let n = trim(&group.params.private_key.modulus.0);
        let id = test.tc_id;
        let ct = &test.case.ct.0;
        let r = decrypt(key, ct);
        if test.result == Expectation::Valid {
            assert_eq!(r.as_deref(), Ok(&test.case.msg.0[..]), "{name} tcId {id}");
            let again = encrypt(public, &test.case.msg.0).unwrap();
            assert_eq!(decrypt(key, &again), r, "{name} tcId {id}");
            valid.add();
        } else if test.flags.iter().any(|f| f == "InvalidPkcs1Padding") {
            let m = r.unwrap_or_else(|e| panic!("{name} tcId {id}: {e}"));
            assert!(m.len() <= n.len() - 11, "{name} tcId {id}");
            assert_eq!(decrypt(key, ct), Ok(m), "{name} tcId {id}");
            padding.add();
        } else {
            let e = if ct.len() == n.len() {
                Error::InputOutOfRange
            } else {
                Error::InvalidLength
            };
            assert_eq!(r, Err(e), "{name} tcId {id}");
            refused.add();
        }
    });
    (valid.get(), padding.get(), refused.get())
}

#[test]
fn rsa_pkcs1_test() {
    require_vectors!();
    for name in [
        "rsa_pkcs1_2048_test.json",
        "rsa_pkcs1_3072_test.json",
        "rsa_pkcs1_4096_test.json",
    ]
    .into_iter()
    .filter(|n| harness::rsa_file_tested(n))
    {
        let (valid, padding, refused) = check(name);
        assert!(valid > 0 && padding > 0 && refused > 0, "{name}");
    }
}
