//! RFC 6979 §A.2.3: P-192, with SHA-256.

#![cfg(target_arch = "x86_64")]

use verified_garbage::ecdsa::{Error, P192, SigningKey, VerifyingKey};
use verified_garbage::hashes::sha256::Sha256;

use super::{Signatures, add};

/// `q`, `x`, `U = 04 ‖ Ux ‖ Uy`, and the SHA-256 signatures.
fn p192() -> ([u8; 24], [u8; 24], [u8; 49], Signatures<48>) {
    super::section("\nA.2.3.  ECDSA, 192 Bits (Prime Field)\n", &["SHA-256"])
}

/// The signature of `message`, of the message and of its hash.
fn sign(key: &SigningKey<P192>, message: &[u8]) -> [Result<[u8; 48], Error>; 2] {
    [
        key.sign::<Sha256>(message),
        key.sign_prehashed::<Sha256>(&Sha256::digest(message)),
    ]
}

/// Whether `rs` verifies for `message`, of the message and of its hash.
fn verify(key: &VerifyingKey<P192>, message: &[u8], rs: &[u8; 48]) -> [Result<(), Error>; 2] {
    [
        key.verify::<Sha256>(message, rs),
        key.verify_prehashed::<Sha256>(&Sha256::digest(message), rs),
    ]
}

/// The signatures, whichever implementation of SHA-256 this CPU runs (the
/// test's name selects it for each CPU configuration CI tests).
#[test]
fn p192_sha256() {
    let (_, x, _, signatures) = p192();
    let key = SigningKey::<P192>::from_bytes(&x);
    for (hash, message, rs) in &signatures {
        let signed = sign(&key.clone(), message.as_bytes());
        assert_eq!(signed, [Ok(*rs); 2], "{hash} {message}");
    }
    assert_eq!(format!("{key:?}"), "SigningKey { .. }");
}

/// The signatures verify with the public key, and not of another message,
/// with another key, or changed.
#[test]
fn p192_verify() {
    let (_, x, u, signatures) = p192();
    let key = VerifyingKey::<P192>::from_bytes(&u);
    assert_eq!(key.to_bytes(), u);
    let other = SigningKey::<P192>::from_bytes(&add(&x, 1))
        .public_key()
        .unwrap();
    let other = VerifyingKey::<P192>::from_bytes(&other);
    let bad = Err(Error::InvalidSignature);
    for (hash, message, rs) in &signatures {
        let verified = verify(&key.clone(), message.as_bytes(), rs);
        assert_eq!(verified, [Ok(()); 2], "{hash} {message}");
        assert_eq!(verify(&key, b"other", rs), [bad; 2]);
        assert_eq!(verify(&other, message.as_bytes(), rs), [bad; 2]);
        let mut changed = *rs;
        changed[47] ^= 1;
        assert_eq!(verify(&key, message.as_bytes(), &changed), [bad; 2]);
    }
    assert_ne!(key, other);
}

#[test]
fn p192_public_key() {
    let (_, x, u, _) = p192();
    assert_eq!(SigningKey::<P192>::from_bytes(&x).public_key(), Ok(u));
}

/// A key outside `[1, n − 1]` is refused; those at its ends sign, and have
/// public keys.
#[test]
fn p192_keys() {
    let (q, _, _, _) = p192();
    for bad in [[0; 24], q, add(&q, 1), [0xff; 24]] {
        let key = SigningKey::<P192>::from_bytes(&bad);
        assert_eq!(sign(&key, b"sample"), [Err(Error::InvalidKey); 2]);
        assert_eq!(key.public_key(), Err(Error::InvalidKey));
    }
    for good in [add(&[0; 24], 1), add(&q, -1)] {
        let key = SigningKey::<P192>::from_bytes(&good);
        assert!(sign(&key, b"sample").iter().all(Result::is_ok));
        assert!(key.public_key().is_ok());
    }
}
