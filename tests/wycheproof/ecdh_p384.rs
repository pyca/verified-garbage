//! ECDH over P-384 (`EcdhEcpointTest` vectors of
//! `ecdh_secp384r1_ecpoint_test.json`, public keys as SEC 1 octet strings).
//!
//! [`PrivateKey::diffie_hellman`] takes an uncompressed public key: a valid
//! vector must give its shared secret, an invalid one must be refused (or,
//! if not 97 bytes, cannot be passed), and the acceptable ones are
//! compressed keys, which cannot be passed either.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

use serde::Deserialize;
use verified_garbage::ecdh::{Error, P384, PrivateKey};

use super::harness::{self, Count, Expectation, Hex};
use crate::require_vectors;

#[derive(Deserialize)]
struct Group {
    curve: String,
}

#[derive(Deserialize)]
struct Case {
    public: Hex,
    private: Hex,
    shared: Hex,
}

/// A private key of up to 49 bytes (Wycheproof writes them as signed
/// integers), as 48.
fn private_key(bytes: &[u8]) -> [u8; 48] {
    let bytes = bytes.strip_prefix(&[0]).unwrap_or(bytes);
    let mut d = [0; 48];
    d[48 - bytes.len()..].copy_from_slice(bytes);
    d
}

#[test]
fn ecdh_secp384r1_ecpoint_test() {
    require_vectors!();
    let file = harness::load::<Group, Case>("ecdh_secp384r1_ecpoint_test.json");
    let (checked, refused) = (Count::default(), Count::default());
    file.par_tests(|group, test| {
        assert_eq!(group.params.curve, "secp384r1");
        let key = PrivateKey::<P384>::from_bytes(&private_key(&test.case.private.0));
        let Ok(public) = <[u8; 97]>::try_from(&test.case.public.0[..]) else {
            assert_ne!(test.result, Expectation::Valid, "tcId {}", test.tc_id);
            return;
        };
        let result = key.diffie_hellman(&public);
        match test.result {
            Expectation::Valid => {
                let shared = result.map(|z| z.to_vec());
                let expected = Ok(test.case.shared.0.clone());
                assert_eq!(shared, expected, "tcId {}", test.tc_id);
                checked.add();
            }
            Expectation::Invalid | Expectation::Acceptable => {
                assert_eq!(result, Err(Error::InvalidKey), "tcId {}", test.tc_id);
                refused.add();
            }
        }
    });
    assert!(checked.get() > 0 && refused.get() > 0);
}
