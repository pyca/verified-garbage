//! RFC 6979 §A.2.5: P-256, with SHA-256 and SHA-384.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

use verified_garbage::ecdsa::{Error, P256, SigningKey, VerifyingKey};
use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::hashes::sha384::Sha384;

use super::{Signatures, add};

/// `q`, `x`, `U = 04 ‖ Ux ‖ Uy`, and the SHA-256 and SHA-384 signatures.
fn p256() -> ([u8; 32], [u8; 32], [u8; 65], Signatures<64>) {
    super::section(
        "\nA.2.5.  ECDSA, 256 Bits (Prime Field)\n",
        &["SHA-256", "SHA-384"],
    )
}

/// The signature of `message` with `hash`, of the message and of its hash.
fn sign(key: &SigningKey<P256>, hash: &str, message: &[u8]) -> [Result<[u8; 64], Error>; 2] {
    if hash == "SHA-256" {
        [
            key.sign::<Sha256>(message),
            key.sign_prehashed::<Sha256>(&Sha256::digest(message)),
        ]
    } else {
        [
            key.sign::<Sha384>(message),
            key.sign_prehashed::<Sha384>(&Sha384::digest(message)),
        ]
    }
}

/// Whether `rs` verifies for `message` with `hash`, of the message and of
/// its hash.
fn verify(
    key: &VerifyingKey<P256>,
    hash: &str,
    message: &[u8],
    rs: &[u8; 64],
) -> [Result<(), Error>; 2] {
    if hash == "SHA-256" {
        [
            key.verify::<Sha256>(message, rs),
            key.verify_prehashed::<Sha256>(&Sha256::digest(message), rs),
        ]
    } else {
        [
            key.verify::<Sha384>(message, rs),
            key.verify_prehashed::<Sha384>(&Sha384::digest(message), rs),
        ]
    }
}

/// The signatures with `hash`, whichever implementation of it this CPU runs
/// (the tests' names select them for each CPU configuration CI tests).
fn p256_sign(hash: &str) {
    let (_, x, _, signatures) = p256();
    let key = SigningKey::<P256>::from_bytes(&x);
    let mut signed = 0;
    for (h, message, rs) in signatures.iter().filter(|(h, _, _)| *h == hash) {
        let results = sign(&key.clone(), h, message.as_bytes());
        assert_eq!(results, [Ok(*rs); 2], "{h} {message}");
        signed += 1;
    }
    assert_eq!(signed, 2);
    assert_eq!(format!("{key:?}"), "SigningKey { .. }");
}

#[test]
fn p256_sha256() {
    p256_sign("SHA-256");
}

#[test]
fn p256_sha384() {
    p256_sign("SHA-384");
}

/// The signatures verify with the public key, and not of another message,
/// with another hash function or with another key.
#[test]
fn p256_verify() {
    let (_, x, u, signatures) = p256();
    let key = VerifyingKey::<P256>::from_bytes(&u);
    assert_eq!(key.to_bytes(), u);
    let other = SigningKey::<P256>::from_bytes(&add(&x, 1))
        .public_key()
        .unwrap();
    let other = VerifyingKey::<P256>::from_bytes(&other);
    for (hash, message, rs) in &signatures {
        let verified = verify(&key.clone(), hash, message.as_bytes(), rs);
        assert_eq!(verified, [Ok(()); 2], "{hash} {message}");
        let bad = Err(Error::InvalidSignature);
        assert_eq!(verify(&key, hash, b"other", rs), [bad; 2]);
        assert_eq!(verify(&other, hash, message.as_bytes(), rs), [bad; 2]);
        let other_hash = if *hash == "SHA-256" {
            "SHA-384"
        } else {
            "SHA-256"
        };
        assert_eq!(verify(&key, other_hash, message.as_bytes(), rs), [bad; 2]);
    }
    assert_ne!(key, other);
    assert!(format!("{key:?}").starts_with("VerifyingKey"));
    assert_eq!(
        Error::InvalidSignature.to_string(),
        "invalid ECDSA signature"
    );
}

#[test]
fn p256_public_key() {
    let (_, x, u, _) = p256();
    assert_eq!(SigningKey::<P256>::from_bytes(&x).public_key(), Ok(u));
}

/// A key outside `[1, n − 1]` is refused; those at its ends sign, and have
/// public keys.
#[test]
fn p256_keys() {
    let (q, _, _, _) = p256();
    for bad in [[0; 32], q, add(&q, 1), [0xff; 32]] {
        let key = SigningKey::<P256>::from_bytes(&bad);
        for hash in ["SHA-256", "SHA-384"] {
            assert_eq!(sign(&key, hash, b"sample"), [Err(Error::InvalidKey); 2]);
        }
        assert_eq!(key.public_key(), Err(Error::InvalidKey));
    }
    for good in [add(&[0; 32], 1), add(&q, -1)] {
        let key = SigningKey::<P256>::from_bytes(&good);
        for hash in ["SHA-256", "SHA-384"] {
            assert!(sign(&key, hash, b"sample").iter().all(Result::is_ok));
        }
        assert!(key.public_key().is_ok());
    }
    assert_eq!(Error::InvalidKey.to_string(), "invalid ECDSA private key");
}
