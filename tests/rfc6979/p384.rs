//! RFC 6979 §A.2.6: P-384, with SHA-384, and on x86-64 the
//! section's other hash functions.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

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
        let signed = sign(&key.clone(), message.as_bytes());
        assert_eq!(signed, [Ok(*rs); 2], "{hash} {message}");
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
        let verified = verify(&key.clone(), message.as_bytes(), rs);
        assert_eq!(verified, [Ok(()); 2], "{hash} {message}");
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

/// On x86-64, the signatures with SHA-1 (`super::other_hash`).
#[cfg(target_arch = "x86_64")]
#[test]
fn p384_sha1() {
    super::other_hash::<P384, verified_garbage::hashes::sha1::Sha1, 48, 97, 96>(
        "\nA.2.6.  ECDSA, 384 Bits (Prime Field)\n",
        "SHA-1",
    );
}

/// On x86-64, the signatures with SHA-224 (`super::other_hash`).
#[cfg(target_arch = "x86_64")]
#[test]
fn p384_sha224() {
    super::other_hash::<P384, verified_garbage::hashes::sha224::Sha224, 48, 97, 96>(
        "\nA.2.6.  ECDSA, 384 Bits (Prime Field)\n",
        "SHA-224",
    );
}

/// On x86-64, the signatures with SHA-256 (`super::other_hash`).
#[cfg(target_arch = "x86_64")]
#[test]
fn p384_sha256() {
    super::other_hash::<P384, verified_garbage::hashes::sha256::Sha256, 48, 97, 96>(
        "\nA.2.6.  ECDSA, 384 Bits (Prime Field)\n",
        "SHA-256",
    );
}

/// On x86-64, the signatures with SHA-512 (`super::other_hash`).
#[cfg(target_arch = "x86_64")]
#[test]
fn p384_sha512() {
    super::other_hash::<P384, verified_garbage::hashes::sha512::Sha512, 48, 97, 96>(
        "\nA.2.6.  ECDSA, 384 Bits (Prime Field)\n",
        "SHA-512",
    );
}
