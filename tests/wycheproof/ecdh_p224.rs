//! ECDH over P-224 (`EcdhEcpointTest` vectors of
//! `ecdh_secp224r1_ecpoint_test.json`, public keys as SEC 1 octet strings).
//!
//! [`PrivateKey::diffie_hellman`] takes an uncompressed public key: a valid
//! vector must give its shared secret, an invalid one must be refused (or,
//! if not 57 bytes, cannot be passed), and the acceptable ones are
//! compressed keys, which cannot be passed either.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use verified_garbage::ecdh::{Error, P224, PrivateKey};

use super::harness::{self, Count, Expectation};
use super::schema::{CurveGroup, EcdhCase};
use crate::require_vectors;

/// A private key of up to 29 bytes (Wycheproof writes them as signed
/// integers), as 28.
fn private_key(bytes: &[u8]) -> [u8; 28] {
    let bytes = bytes.strip_prefix(&[0]).unwrap_or(bytes);
    let mut d = [0; 28];
    d[28 - bytes.len()..].copy_from_slice(bytes);
    d
}

#[test]
fn ecdh_secp224r1_ecpoint_test() {
    require_vectors!();
    let file = harness::load::<CurveGroup, EcdhCase>("ecdh_secp224r1_ecpoint_test.json");
    let (checked, refused) = (Count::default(), Count::default());
    file.par_tests(|group, test| {
        assert_eq!(group.params.curve, "secp224r1");
        let key = PrivateKey::<P224>::from_bytes(&private_key(&test.case.private.0));
        let Ok(public) = <[u8; 57]>::try_from(&test.case.public.0[..]) else {
            assert_ne!(test.result, Expectation::Valid, "tcId {}", test.tc_id);
            return;
        };
        let result = key.diffie_hellman(&public);
        #[cfg(target_arch = "x86_64")]
        {
            // A scalar of one makes ECDH an independent reference for the
            // standalone point check, regardless of this case's scalar.
            let mut one = [0; 28];
            let last = one.len() - 1;
            one[last] = 1;
            let reference = PrivateKey::<P224>::from_bytes(&one);
            let valid = P224::validate_public_key(&public);
            let expected = reference.diffie_hellman(&public).is_ok();
            assert_eq!(valid, expected, "point check, tcId {}", test.tc_id);
        }
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
