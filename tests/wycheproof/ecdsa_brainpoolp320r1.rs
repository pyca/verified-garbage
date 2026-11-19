//! ECDSA over brainpoolP320r1 with SHA-384 (`EcdsaP1363Verify` vectors of
//! `ecdsa_brainpoolP320r1_sha384_p1363_test.json`, signatures as `r ‖ s`).
//!
//! A valid vector must verify, an invalid one must be refused (or, if its
//! signature is not 80 bytes, cannot be passed).
//!
//! No published vectors sign over brainpoolP320r1 (RFC 6979 and RFC 7027
//! have none), so signing is checked against verification: the private keys
//! of `ecdh_brainpoolP320r1_test.json`'s valid vectors sign, and what they
//! sign verifies with the public keys they derive.

#![cfg(any(target_arch = "x86_64", target_arch = "powerpc64"))]

use verified_garbage::ec::{BrainpoolP320r1, PrivateKey, PublicKey};
use verified_garbage::error::{InvalidKey, InvalidSignature};
use verified_garbage::hashes::sha384::Sha384;

use super::harness::{self, Count, Expectation};
use super::schema::{CurveEncodingGroup, EcdhCase, EcdsaGroup, SigCase};
use crate::require_vectors;

#[test]
fn ecdsa_brainpoolp320r1_sha384_p1363_test() {
    require_vectors!();
    let file = harness::load::<EcdsaGroup, SigCase>("ecdsa_brainpoolP320r1_sha384_p1363_test.json");
    let (verified, refused) = (Count::default(), Count::default());
    file.par_tests(|group, test| {
        assert_eq!(group.params.public_key.curve, "brainpoolP320r1");
        assert_eq!(group.params.sha, "SHA-384");
        let q: [u8; 81] = group.params.public_key.uncompressed.0[..]
            .try_into()
            .unwrap();
        let key = PublicKey::<BrainpoolP320r1>::from_bytes(&q);
        let Ok(sig) = <[u8; 80]>::try_from(&test.case.sig.0[..]) else {
            assert_eq!(test.result, Expectation::Invalid, "tcId {}", test.tc_id);
            return;
        };
        let result = key.verify::<Sha384>(&test.case.msg.0, &sig);
        match test.result {
            Expectation::Valid => {
                assert_eq!(result, Ok(()), "tcId {}", test.tc_id);
                verified.add();
            }
            Expectation::Invalid | Expectation::Acceptable => {
                assert_eq!(result, Err(InvalidSignature), "tcId {}", test.tc_id);
                refused.add();
            }
        }
    });
    assert!(verified.get() > 0 && refused.get() > 0);
}

/// A private key of up to 41 bytes (Wycheproof writes them as signed
/// integers), as 40.
fn private_key(bytes: &[u8]) -> [u8; 40] {
    let bytes = bytes.strip_prefix(&[0]).unwrap_or(bytes);
    let mut d = [0; 40];
    d[40 - bytes.len()..].copy_from_slice(bytes);
    d
}

#[test]
fn ecdsa_brainpoolp320r1_sign_with_ecdh_keys() {
    require_vectors!();
    let file = harness::load::<CurveEncodingGroup, EcdhCase>("ecdh_brainpoolP320r1_test.json");
    let signed = Count::default();
    let message = b"brainpoolP320r1 API message";
    file.par_tests(|group, test| {
        assert_eq!(group.params.curve, "brainpoolP320r1");
        if test.result != Expectation::Valid || test.tc_id % 32 != 1 {
            return;
        }
        let key = PrivateKey::<BrainpoolP320r1>::from_bytes(&private_key(&test.case.private.0));
        let verifier = key.public_key().unwrap();
        let sig = key.clone().sign::<Sha384>(message).unwrap();
        assert_eq!(
            key.sign_prehashed::<Sha384>(&Sha384::digest(message)),
            Ok(sig),
            "tcId {}",
            test.tc_id
        );
        assert_eq!(verifier.verify::<Sha384>(message, &sig), Ok(()));
        assert_eq!(
            verifier.verify::<Sha384>(b"changed", &sig),
            Err(InvalidSignature)
        );
        signed.add();
    });
    assert!(signed.get() > 0);
    // 0 and 2³²⁰ − 1 (above n) are not in [1, n − 1].
    for d in [[0; 40], [0xff; 40]] {
        let bad = PrivateKey::<BrainpoolP320r1>::from_bytes(&d);
        assert_eq!(bad.public_key(), Err(InvalidKey));
        assert_eq!(bad.sign::<Sha384>(message), Err(InvalidKey));
    }
}
