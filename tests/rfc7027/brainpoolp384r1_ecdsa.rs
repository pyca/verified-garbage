//! RFC 7027 §A.2's brainpoolP384r1 keys, signing and verifying with ECDSA.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::ec::{BrainpoolP384r1, PrivateKey, PublicKey};
use verified_garbage::error::{InvalidKey, InvalidSignature};
use verified_garbage::hashes::sha384::Sha384;

use super::value;

const CURVE: &str = "brainpoolP384r1";

fn public(x: &str, y: &str) -> [u8; 97] {
    let (x, y) = (value::<48>(CURVE, x), value::<48>(CURVE, y));
    core::array::from_fn(|i| match i {
        0 => 4,
        1..=48 => x[i - 1],
        _ => y[i - 49],
    })
}

/// Signatures by RFC 7027's keys (RFC 6979 has no brainpool vectors; the
/// verifier is checked against Wycheproof's), and keys out of range.
#[test]
fn ecdsa_and_invalid_keys() {
    let da = value::<48>(CURVE, "dA =");
    let qa = public("x_qA =", "y_qA =");
    let key = PrivateKey::<BrainpoolP384r1>::from_bytes(&da);
    assert_eq!(key.public_key(), Ok(PublicKey::from_bytes(&qa)));
    let verifier = PublicKey::<BrainpoolP384r1>::from_bytes(&qa);
    let message = b"brainpoolP384r1 API message";
    let sig = key.clone().sign::<Sha384>(message).unwrap();
    assert_eq!(
        key.sign_prehashed::<Sha384>(&Sha384::digest(message)),
        Ok(sig)
    );
    assert_eq!(verifier.verify::<Sha384>(message, &sig), Ok(()));
    assert_eq!(
        verifier.verify::<Sha384>(b"changed", &sig),
        Err(InvalidSignature)
    );
    let mut invalid = qa;
    invalid[0] = 0;
    assert_eq!(
        PublicKey::<BrainpoolP384r1>::from_bytes(&invalid).verify::<Sha384>(message, &sig),
        Err(InvalidSignature)
    );
    // 0 and 2³⁸⁴ − 1 (above n) are not in [1, n − 1].
    for d in [[0; 48], [0xff; 48]] {
        let bad = PrivateKey::<BrainpoolP384r1>::from_bytes(&d);
        assert_eq!(bad.public_key(), Err(InvalidKey));
        assert_eq!(bad.sign::<Sha384>(message), Err(InvalidKey));
    }
}
