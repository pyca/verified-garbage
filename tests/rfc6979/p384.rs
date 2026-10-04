//! RFC 6979 §A.2.6: P-384, with SHA-384.

#![cfg(target_arch = "x86_64")]

use verified_garbage::ecdsa::{Error, P384, SigningKey, VerifyingKey};
use verified_garbage::hashes::sha384::Sha384;

use super::{Signatures, add};

/// `q`, `x`, `U = 04 ‖ Ux ‖ Uy`, and the SHA-384 signatures.
fn p384() -> ([u8; 48], [u8; 48], [u8; 97], Signatures<96>) {
    super::section("\nA.2.6.  ECDSA, 384 Bits (Prime Field)\n", &["SHA-384"])
}

/// The signature of `message`, of the message and of its hash.
fn sign(key: &SigningKey<P384>, message: &[u8]) -> [Result<[u8; 96], Error>; 2] {
    [
        key.sign::<Sha384>(message),
        key.sign_prehashed::<Sha384>(&Sha384::digest(message)),
    ]
}

/// Whether `rs` verifies for `message`, of the message and of its hash.
fn verify(key: &VerifyingKey<P384>, message: &[u8], rs: &[u8; 96]) -> [Result<(), Error>; 2] {
    [
        key.verify::<Sha384>(message, rs),
        key.verify_prehashed::<Sha384>(&Sha384::digest(message), rs),
    ]
}

/// The signatures, whichever implementation of SHA-384 this CPU runs (the
/// test's name selects it for each CPU configuration CI tests).
#[test]
fn p384_sha384() {
    let (_, x, _, signatures) = p384();
    let key = SigningKey::<P384>::from_bytes(&x);
    for (hash, message, rs) in &signatures {
        assert_eq!(
            sign(&key.clone(), message.as_bytes()),
            [Ok(*rs); 2],
            "{hash} {message}"
        );
    }
    assert_eq!(format!("{key:?}"), "SigningKey { .. }");
}

/// The signatures verify with the public key, and not of another message,
/// with another key, or changed.
#[test]
fn p384_verify() {
    let (_, x, u, signatures) = p384();
    let key = VerifyingKey::<P384>::from_bytes(&u);
    assert_eq!(key.to_bytes(), u);
    let other = SigningKey::<P384>::from_bytes(&add(&x, 1))
        .public_key()
        .unwrap();
    let other = VerifyingKey::<P384>::from_bytes(&other);
    let bad = Err(Error::InvalidSignature);
    for (hash, message, rs) in &signatures {
        assert_eq!(
            verify(&key.clone(), message.as_bytes(), rs),
            [Ok(()); 2],
            "{hash} {message}"
        );
        assert_eq!(verify(&key, b"other", rs), [bad; 2]);
        assert_eq!(verify(&other, message.as_bytes(), rs), [bad; 2]);
        let mut changed = *rs;
        changed[95] ^= 1;
        assert_eq!(verify(&key, message.as_bytes(), &changed), [bad; 2]);
    }
    assert_ne!(key, other);
}

#[test]
fn p384_public_key() {
    let (_, x, u, _) = p384();
    assert_eq!(SigningKey::<P384>::from_bytes(&x).public_key(), Ok(u));
}

/// A key outside `[1, n − 1]` is refused; those at its ends sign, and have
/// public keys.
#[test]
fn p384_keys() {
    let (q, _, _, _) = p384();
    for bad in [[0; 48], q, add(&q, 1), [0xff; 48]] {
        let key = SigningKey::<P384>::from_bytes(&bad);
        assert_eq!(sign(&key, b"sample"), [Err(Error::InvalidKey); 2]);
        assert_eq!(key.public_key(), Err(Error::InvalidKey));
    }
    for good in [add(&[0; 48], 1), add(&q, -1)] {
        let key = SigningKey::<P384>::from_bytes(&good);
        assert!(sign(&key, b"sample").iter().all(Result::is_ok));
        assert!(key.public_key().is_ok());
    }
}
