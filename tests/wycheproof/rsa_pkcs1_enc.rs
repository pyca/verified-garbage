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
//!
//! Every message returned, either kind, must leave no copy of itself in its
//! allocation outside the returned bytes (#6301): once the message is wiped,
//! the whole `k`-byte buffer the library decrypted into is zero
//! (`no_residue`).

#![cfg(all(
    any(
        target_arch = "x86",
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64",
        target_arch = "riscv64"
    ),
    feature = "alloc"
))]

use verified_garbage::rsa::pkcs1_enc::Error;
use verified_garbage::rsa::{BigUint, PrivateKey, PublicKey};

use super::harness::{self, Count, Expectation, TestFile, TestGroup};
use super::schema::{EncryptCase, RsaPrivateKeyGroup};
use crate::bytes::trim_zeros;
use crate::require_vectors;

/// Wipes `m`, a message `decrypt_pkcs1v15` returned for a `k`-byte modulus,
/// and checks that the `k` bytes of its allocation are then all zero: no copy
/// of the message is left past its end.
fn no_residue(mut m: Vec<u8>, k: usize, what: &str) {
    assert!(m.capacity() >= k, "{what}");
    m.fill(0);
    let p = m.as_ptr();
    // SAFETY: the library allocates the message's vector with `k` initialized
    // bytes (`vec![0u8; k]`) and only shortens it, so its allocation holds at
    // least `k` initialized bytes from `p`, which `m` keeps alive and nothing
    // writes while they are read.
    let all = unsafe { core::slice::from_raw_parts(p, k) };
    assert!(
        all.iter().all(|&b| b == 0),
        "{what}: message bytes left in the allocation"
    );
}

/// Checks every vector of the file `name`; returns the numbers of valid
/// vectors, of invalid paddings and of refused ciphertexts.
fn check(name: &str) -> (usize, usize, usize) {
    let (valid, padding, refused) = (Count::default(), Count::default(), Count::default());
    let file: TestFile<RsaPrivateKeyGroup, EncryptCase> = harness::load(name);
    let keys = |group: &TestGroup<RsaPrivateKeyGroup, EncryptCase>| {
        let k = &group.params.private_key;
        let n = trim_zeros(&k.modulus.0);
        let key = PrivateKey::from_crt(
            BigUint::from_be_bytes(n),
            BigUint::from_be_bytes(&k.public_exponent.0),
            BigUint::from_be_bytes(&k.private_exponent.0),
            BigUint::from_be_bytes(&k.prime1.0),
            BigUint::from_be_bytes(&k.prime2.0),
            BigUint::from_be_bytes(&k.exponent1.0),
            BigUint::from_be_bytes(&k.exponent2.0),
            BigUint::from_be_bytes(&k.coefficient.0),
        );
        let key = key.unwrap_or_else(|e| panic!("{name}: {e}"));
        (
            key,
            PublicKey::new(
                BigUint::from_be_bytes(n),
                BigUint::from_be_bytes(&k.public_exponent.0),
            )
            .unwrap(),
        )
    };
    file.par_tests_with(keys, |group, (key, public), test| {
        let n = trim_zeros(&group.params.private_key.modulus.0);
        let id = test.tc_id;
        let ct = &test.case.ct.0;
        let r = key.decrypt_pkcs1v15(ct);
        if test.result == Expectation::Valid {
            assert_eq!(r.as_deref(), Ok(&test.case.msg.0[..]), "{name} tcId {id}");
            let again = public.encrypt_pkcs1v15(&test.case.msg.0).unwrap();
            assert_eq!(key.decrypt_pkcs1v15(&again), r, "{name} tcId {id}");
            no_residue(r.unwrap(), n.len(), &format!("{name} tcId {id}"));
            valid.add();
        } else if test.flags.iter().any(|f| f == "InvalidPkcs1Padding") {
            let m = r.unwrap_or_else(|e| panic!("{name} tcId {id}: {e}"));
            assert!(m.len() <= n.len() - 11, "{name} tcId {id}");
            assert_eq!(
                key.decrypt_pkcs1v15(ct).as_ref(),
                Ok(&m),
                "{name} tcId {id}"
            );
            no_residue(m, n.len(), &format!("{name} tcId {id}"));
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
