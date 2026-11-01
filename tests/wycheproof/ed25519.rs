//! All pure Ed25519 verification cases in Wycheproof's ed25519_test.json.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use verified_garbage::ed25519::{Error, VerifyingKey};

use super::harness::{self, Count, Expectation};
use super::schema::{EdGroup as Group, SigCase as Case};
use crate::require_vectors;

#[test]
fn ed25519_test() {
    require_vectors!();
    let file = harness::load::<Group, Case>("ed25519_test.json");
    let checked = Count::default();
    file.par_tests(|group, test| {
        assert_eq!(group.params.public_key.curve, "edwards25519");
        let public: [u8; 32] = group.params.public_key.pk.0.clone().try_into().unwrap();
        let key = VerifyingKey::from_bytes(&public);
        let expected = match test.result {
            Expectation::Valid => Ok(()),
            // Signatures under small-order and mixed-order public keys, which
            // Wycheproof allows either way: `VerifyingKey::verify` rejects no
            // key for its order (RFC 8032 §5.1.7 requires no such check), so
            // it accepts them.
            Expectation::Acceptable => {
                let order = |f: &String| f == "SmallOrderPublicKey" || f == "MixedOrderPublicKey";
                assert!(test.flags.iter().all(order), "tcId {}", test.tc_id);
                Ok(())
            }
            Expectation::Invalid => Err(Error::InvalidSignature),
        };
        let actual = key.verify(&test.case.msg.0, &test.case.sig.0);
        assert_eq!(actual, expected, "tcId {}", test.tc_id);
        checked.add();
    });
    assert!(checked.get() > 0);
}
