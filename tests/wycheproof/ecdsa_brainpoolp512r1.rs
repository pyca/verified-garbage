//! ECDSA over brainpoolP512r1 with SHA-512 (`EcdsaP1363Verify` vectors of
//! `ecdsa_brainpoolP512r1_sha512_p1363_test.json`, signatures as `r ‖ s`).
//!
//! A valid vector must verify, an invalid one must be refused (or, if its
//! signature is not 128 bytes, cannot be passed).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use verified_garbage::ecdsa::{BrainpoolP512r1, Error, VerifyingKey};
use verified_garbage::hashes::sha512::Sha512;

use super::harness::{self, Count, Expectation};
use super::schema::{EcdsaGroup as Group, SigCase as Case};
use crate::require_vectors;

#[test]
fn ecdsa_brainpoolp512r1_sha512_p1363_test() {
    require_vectors!();
    let file = harness::load::<Group, Case>("ecdsa_brainpoolP512r1_sha512_p1363_test.json");
    let (verified, refused) = (Count::default(), Count::default());
    file.par_tests(|group, test| {
        assert_eq!(group.params.public_key.curve, "brainpoolP512r1");
        assert_eq!(group.params.sha, "SHA-512");
        let q: [u8; 129] = group.params.public_key.uncompressed.0[..]
            .try_into()
            .unwrap();
        let key = VerifyingKey::<BrainpoolP512r1>::from_bytes(&q);
        let Ok(sig) = <[u8; 128]>::try_from(&test.case.sig.0[..]) else {
            assert_eq!(test.result, Expectation::Invalid, "tcId {}", test.tc_id);
            return;
        };
        let result = key.verify::<Sha512>(&test.case.msg.0, &sig);
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
