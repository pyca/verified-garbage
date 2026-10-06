//! RFC 6979 §A.2.7: P-521, with SHA-512.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64"
))]

use verified_garbage::ecdsa::{Error, P521, SigningKey, VerifyingKey};
use verified_garbage::hashes::sha512::Sha512;

use super::{Signatures, add};

/// `q`, `x`, `U = 04 ‖ Ux ‖ Uy`, and the SHA-512 signatures.
fn p521() -> ([u8; 66], [u8; 66], [u8; 133], Signatures<132>) {
    super::section("\nA.2.7.  ECDSA, 521 Bits (Prime Field)\n", &["SHA-512"])
}

/// The signature of `message`, of the message and of its hash.
fn sign(key: &SigningKey<P521>, message: &[u8]) -> [Result<[u8; 132], Error>; 2] {
    [
        key.sign::<Sha512>(message),
        key.sign_prehashed::<Sha512>(&Sha512::digest(message)),
    ]
}

/// Whether `rs` verifies for `message`, of the message and of its hash.
fn verify(key: &VerifyingKey<P521>, message: &[u8], rs: &[u8; 132]) -> [Result<(), Error>; 2] {
    [
        key.verify::<Sha512>(message, rs),
        key.verify_prehashed::<Sha512>(&Sha512::digest(message), rs),
    ]
}

/// The signatures, whichever implementation of SHA-512 this CPU runs (the
/// test's name selects it for each CPU configuration CI tests).
#[test]
fn p521_sha512() {
    let (_, x, _, signatures) = p521();
    let key = SigningKey::<P521>::from_bytes(&x);
    for (hash, message, rs) in &signatures {
        let signed = sign(&key.clone(), message.as_bytes());
        assert_eq!(signed, [Ok(*rs); 2], "{hash} {message}");
    }
    assert_eq!(format!("{key:?}"), "SigningKey { .. }");
}

/// The signatures verify with the public key, and not of another message,
/// with another key, or changed.
#[test]
fn p521_verify() {
    let (_, x, u, signatures) = p521();
    let key = VerifyingKey::<P521>::from_bytes(&u);
    assert_eq!(key.to_bytes(), u);
    let other = SigningKey::<P521>::from_bytes(&add(&x, 1))
        .public_key()
        .unwrap();
    let other = VerifyingKey::<P521>::from_bytes(&other);
    let bad = Err(Error::InvalidSignature);
    for (hash, message, rs) in &signatures {
        let verified = verify(&key.clone(), message.as_bytes(), rs);
        assert_eq!(verified, [Ok(()); 2], "{hash} {message}");
        assert_eq!(verify(&key, b"other", rs), [bad; 2]);
        assert_eq!(verify(&other, message.as_bytes(), rs), [bad; 2]);
        let mut changed = *rs;
        changed[131] ^= 1;
        assert_eq!(verify(&key, message.as_bytes(), &changed), [bad; 2]);
    }
    assert_ne!(key, other);
}

#[test]
fn p521_public_key() {
    let (_, x, u, _) = p521();
    assert_eq!(SigningKey::<P521>::from_bytes(&x).public_key(), Ok(u));
}

/// A key outside `[1, n − 1]` is refused; those at its ends sign, and have
/// public keys.
#[test]
fn p521_keys() {
    let (q, _, _, _) = p521();
    for bad in [[0; 66], q, add(&q, 1), [0xff; 66]] {
        let key = SigningKey::<P521>::from_bytes(&bad);
        assert_eq!(sign(&key, b"sample"), [Err(Error::InvalidKey); 2]);
        assert_eq!(key.public_key(), Err(Error::InvalidKey));
    }
    for good in [add(&[0; 66], 1), add(&q, -1)] {
        let key = SigningKey::<P521>::from_bytes(&good);
        assert!(sign(&key, b"sample").iter().all(Result::is_ok));
        assert!(key.public_key().is_ok());
    }
}
