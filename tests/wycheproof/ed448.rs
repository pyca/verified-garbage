//! All Ed448 verification cases in Wycheproof's ed448_test.json.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use serde::Deserialize;
use verified_garbage::ed448::{Error, VerifyingKey};

use crate::harness::{self, Count, Expectation, Hex};
use crate::require_vectors;

#[derive(Deserialize)]
struct PublicKey {
    curve: String,
    pk: Hex,
}

#[derive(Deserialize)]
struct Group {
    #[serde(rename = "publicKey")]
    public_key: PublicKey,
}

#[derive(Deserialize)]
struct Case {
    msg: Hex,
    sig: Hex,
}

#[test]
fn ed448_test() {
    require_vectors!();
    let file = harness::load::<Group, Case>("ed448_test.json");
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
