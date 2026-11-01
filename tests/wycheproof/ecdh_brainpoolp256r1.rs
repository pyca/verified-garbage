//! ECDH over brainpoolP256r1 (`EcdhTest` vectors of
//! `ecdh_brainpoolP256r1_test.json`, public keys as DER `SubjectPublicKeyInfo`).
//!
//! [`PrivateKey::diffie_hellman`] takes an uncompressed public key, so a
//! vector's key is passed only if it is the DER encoding of an uncompressed
//! point with brainpoolP256r1's named curve parameters: a valid vector must
//! give its shared secret, and an invalid or acceptable one must be refused
//! (the one acceptable vector so encoded changes the point's last byte, which
//! takes it off the curve). A key in any other encoding (an explicit or wrong
//! curve, a compressed point, malformed DER) cannot be passed, and its vector
//! must not be valid.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use verified_garbage::ecdh::{BrainpoolP256r1, Error, PrivateKey};

use super::harness::{self, Count, Expectation};
use super::schema::{CurveEncodingGroup as Group, EcdhCase as Case};
use crate::require_vectors;

/// The DER encoding of a `SubjectPublicKeyInfo` up to its point (RFC 5480
/// §2): `id-ecPublicKey` with the named curve brainpoolP256r1
/// (1.3.36.3.3.2.8.1.1.7, RFC 5639 §4.1), then the 66-byte bit string
/// holding the 65-byte point.
const SPKI_PREFIX: [u8; 26] = [
    0x30, 0x5a, 0x30, 0x14, 0x06, 0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01, 0x06, 0x09, 0x2b,
    0x24, 0x03, 0x03, 0x02, 0x08, 0x01, 0x01, 0x07, 0x03, 0x42,
];

/// The uncompressed point of a named-curve `SubjectPublicKeyInfo`, if `der`
/// is one.
fn point(der: &[u8]) -> Option<[u8; 65]> {
    let rest = der.strip_prefix(&SPKI_PREFIX)?.strip_prefix(&[0])?;
    let point = <[u8; 65]>::try_from(rest).ok()?;
    (point[0] == 4).then_some(point)
}

/// A private key of up to 33 bytes (Wycheproof writes them as signed
/// integers), as 32.
fn private_key(bytes: &[u8]) -> [u8; 32] {
    let bytes = bytes.strip_prefix(&[0]).unwrap_or(bytes);
    let mut d = [0; 32];
    d[32 - bytes.len()..].copy_from_slice(bytes);
    d
}

#[test]
fn ecdh_brainpoolp256r1_test() {
    require_vectors!();
    let file = harness::load::<Group, Case>("ecdh_brainpoolP256r1_test.json");
    let (checked, refused) = (Count::default(), Count::default());
    file.par_tests(|group, test| {
        assert_eq!(group.params.curve, "brainpoolP256r1");
        assert_eq!(group.params.encoding, "asn");
        let key = PrivateKey::<BrainpoolP256r1>::from_bytes(&private_key(&test.case.private.0));
        let Some(public) = point(&test.case.public.0) else {
            assert_ne!(test.result, Expectation::Valid, "tcId {}", test.tc_id);
            return;
        };
        #[cfg(target_arch = "x86_64")]
        {
            let mut one = [0; 32];
            let last = one.len() - 1;
            one[last] = 1;
            let reference = PrivateKey::<BrainpoolP256r1>::from_bytes(&one);
            let valid = BrainpoolP256r1::validate_public_key(&public);
            let expected = reference.diffie_hellman(&public).is_ok();
            assert_eq!(valid, expected, "point check, tcId {}", test.tc_id);
        }
        let result = key.diffie_hellman(&public).map(|z| z.to_vec());
        let shared = Ok(test.case.shared.0.clone());
        match test.result {
            Expectation::Valid => {
                assert_eq!(result, shared, "tcId {}", test.tc_id);
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
