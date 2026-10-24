//! RFC 7027 §A.3's brainpoolP512r1 keys, signing and verifying with ECDSA.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use verified_garbage::ecdsa::{BrainpoolP512r1, Error, SigningKey, VerifyingKey};
use verified_garbage::hashes::sha512::Sha512;

use super::value;

const CURVE: &str = "brainpoolP512r1";

fn public(x: &str, y: &str) -> [u8; 129] {
    let (x, y) = (value::<64>(CURVE, x), value::<64>(CURVE, y));
    core::array::from_fn(|i| match i {
        0 => 4,
        1..=64 => x[i - 1],
        _ => y[i - 65],
    })
}

/// Signatures by RFC 7027's keys (RFC 6979 has no brainpool vectors; the
/// verifier is checked against Wycheproof's), and keys out of range.
#[test]
fn ecdsa_and_invalid_keys() {
    let da = value::<64>(CURVE, "dA =");
    let qa = public("x_qA =", "y_qA =");
    let key = SigningKey::<BrainpoolP512r1>::from_bytes(&da);
    assert_eq!(key.public_key(), Ok(qa));
    let verifier = VerifyingKey::<BrainpoolP512r1>::from_bytes(&qa);
    let message = b"brainpoolP512r1 API message";
    let sig = key.clone().sign::<Sha512>(message).unwrap();
    assert_eq!(
        key.sign_prehashed::<Sha512>(&Sha512::digest(message)),
        Ok(sig)
    );
    assert_eq!(verifier.verify::<Sha512>(message, &sig), Ok(()));
    assert_eq!(
        verifier.verify::<Sha512>(b"changed", &sig),
        Err(Error::InvalidSignature)
    );
    let mut invalid = qa;
    invalid[0] = 0;
    assert_eq!(
        VerifyingKey::<BrainpoolP512r1>::from_bytes(&invalid).verify::<Sha512>(message, &sig),
        Err(Error::InvalidSignature)
    );
    // 0 and 2⁵¹² − 1 (above n) are not in [1, n − 1].
    for d in [[0; 64], [0xff; 64]] {
        let bad = SigningKey::<BrainpoolP512r1>::from_bytes(&d);
        assert_eq!(bad.public_key(), Err(Error::InvalidKey));
        assert_eq!(bad.sign::<Sha512>(message), Err(Error::InvalidKey));
    }
}
