//! ECDSA over secp256k1 with SHA-256 (`EcdsaP1363Verify` vectors of
//! `ecdsa_secp256k1_sha256_p1363_test.json`, signatures as `r ‖ s`), and, on
//! x86 and x86-64, where it signs with every hash function with a table, with SHA-512
//! (`ecdsa_secp256k1_sha512_p1363_test.json`).
//!
//! A valid vector must verify, an invalid one must be refused (or, if its
//! signature is not 64 bytes, cannot be passed).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::ecdsa::{Error, Secp256k1, SignatureHash, VerifyingKey};
use verified_garbage::hashes::sha256::Sha256;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use verified_garbage::hashes::sha512::Sha512;

use super::harness::{self, Count, Expectation};
use super::schema::{EcdsaGroup, SigCase};
use crate::require_vectors;

#[test]
fn ecdsa_secp256k1_sha256_p1363_test() {
    require_vectors!();
    check::<Sha256>("ecdsa_secp256k1_sha256_p1363_test.json", "SHA-256");
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
#[test]
fn ecdsa_secp256k1_sha512_p1363_test() {
    require_vectors!();
    check::<Sha512>("ecdsa_secp256k1_sha512_p1363_test.json", "SHA-512");
}

/// The vectors of `file`, with the hash function `H`, named `sha` there.
fn check<H: SignatureHash<Secp256k1>>(file: &str, sha: &str) {
    let file = harness::load::<EcdsaGroup, SigCase>(file);
    let (verified, refused) = (Count::default(), Count::default());
    file.par_tests(|group, test| {
        assert_eq!(group.params.public_key.curve, "secp256k1");
        assert_eq!(group.params.sha, sha);
        let q: [u8; 65] = group.params.public_key.uncompressed.0[..]
            .try_into()
            .unwrap();
        let key = VerifyingKey::<Secp256k1>::from_bytes(&q);
        let Ok(sig) = <[u8; 64]>::try_from(&test.case.sig.0[..]) else {
            assert_eq!(test.result, Expectation::Invalid, "tcId {}", test.tc_id);
            return;
        };
        let result = key.verify::<H>(&test.case.msg.0, &sig);
        match test.result {
            Expectation::Valid => {
                assert_eq!(result, Ok(()), "tcId {}", test.tc_id);
                verified.add();
            }
            Expectation::Invalid | Expectation::Acceptable => {
                assert_eq!(result, Err(Error::InvalidSignature), "tcId {}", test.tc_id);
                refused.add();
            }
        }
    });
    assert!(verified.get() > 0 && refused.get() > 0);
}
