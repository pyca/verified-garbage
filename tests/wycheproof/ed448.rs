//! All Ed448 verification cases in Wycheproof's ed448_test.json.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use verified_garbage::ed448::{Error, VerifyingKey};

use super::harness::{self, Count, Expectation};
use super::schema::{EdGroup, SigCase};
use crate::require_vectors;

#[test]
fn ed448_test() {
    require_vectors!();
    let file = harness::load::<EdGroup, SigCase>("ed448_test.json");
    let checked = Count::default();
    file.par_tests(|group, test| {
        assert_eq!(group.params.public_key.curve, "edwards448");
        let public: [u8; 57] = group.params.public_key.pk.0.clone().try_into().unwrap();
        let key = VerifyingKey::from_bytes(&public);
        assert_ne!(test.result, Expectation::Acceptable, "tcId {}", test.tc_id);
        let expected = if test.result == Expectation::Valid {
            Ok(())
        } else {
            Err(Error::InvalidSignature)
        };
        let actual = key.verify(&test.case.msg.0, &test.case.sig.0);
        assert_eq!(actual, expected, "tcId {}", test.tc_id);
        checked.add();
    });
    assert!(checked.get() > 0);
}
