//! ECDSA over P-384 with SHA-384 (`EcdsaP1363Verify` vectors of
//! `ecdsa_secp384r1_sha384_p1363_test.json`, signatures as `r ‖ s`).
//!
//! A valid vector must verify, an invalid one must be refused (or, if its
//! signature is not 96 bytes, cannot be passed).

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use serde::Deserialize;
use verified_garbage::ecdsa::{Error, P384, VerifyingKey};
use verified_garbage::hashes::sha384::Sha384;

use crate::harness::{self, Expectation, Hex};
use crate::require_vectors;

#[derive(Deserialize)]
struct Key {
    curve: String,
    uncompressed: Hex,
}

#[derive(Deserialize)]
struct Group {
    #[serde(rename = "publicKey")]
    public_key: Key,
    sha: String,
}

#[derive(Deserialize)]
struct Case {
    msg: Hex,
    sig: Hex,
}

#[test]
fn ecdsa_secp384r1_sha384_p1363_test() {
    require_vectors!();
    let file = harness::load::<Group, Case>("ecdsa_secp384r1_sha384_p1363_test.json");
    let (mut verified, mut refused) = (0, 0);
    for (group, test) in file.tests() {
        assert_eq!(group.params.public_key.curve, "secp384r1");
        assert_eq!(group.params.sha, "SHA-384");
        let q: [u8; 97] = group.params.public_key.uncompressed.0[..]
            .try_into()
            .unwrap();
        let key = VerifyingKey::<P384>::from_bytes(&q);
        let Ok(sig) = <[u8; 96]>::try_from(&test.case.sig.0[..]) else {
            assert_eq!(test.result, Expectation::Invalid, "tcId {}", test.tc_id);
            continue;
        };
        let result = key.verify::<Sha384>(&test.case.msg.0, &sig);
        match test.result {
            Expectation::Valid => {
                assert_eq!(result, Ok(()), "tcId {}", test.tc_id);
                verified += 1;
            }
            Expectation::Invalid | Expectation::Acceptable => {
                assert_eq!(result, Err(Error::InvalidSignature), "tcId {}", test.tc_id);
                refused += 1;
            }
        }
    }
    assert!(verified > 0 && refused > 0);
}
