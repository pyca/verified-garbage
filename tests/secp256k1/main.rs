//! Published deterministic ECDSA vectors and public API boundary checks.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::json_struct;
use verified_garbage::ec::{Error, PrivateKey, PublicKey, Secp256k1};
use verified_garbage::hashes::sha256::Sha256;

json_struct! {
    struct Case {
        d: String,
        m: String,
        signature: String,
    }
}

json_struct! {
    struct Vectors {
        valid: Vec<Case>,
    }
}

fn vectors() -> Vec<Case> {
    let json = crate::vectors::text("vectors/secp256k1-ecdsa/ecdsa.json");
    crate::json::parse::<Vectors>("ecdsa.json", &json).valid
}

fn hex<const N: usize>(s: &str) -> [u8; N] {
    assert_eq!(s.len(), 2 * N);
    core::array::from_fn(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
}

// Interleave four batches so libtest can distribute independent vectors across cores.
fn deterministic_sha256_batch(batch: usize) {
    let cases = vectors();
    let mut order = hex::<32>(&cases[1].d);
    order[31] += 1; // The published second key is n - 1.
    for case in cases.iter().skip(batch).step_by(4) {
        let key = PrivateKey::<Secp256k1>::from_bytes(&hex(&case.d));
        let digest = hex(&case.m);
        let signature = hex::<64>(&case.signature);
        let actual = key.sign_prehashed::<Sha256>(&digest).unwrap();
        // Noble publishes low-s signatures; this API returns RFC 6979's
        // original s. The two encodings have the same r and s or n-s.
        let mut alternate = signature;
        let mut borrow = 0i16;
        for i in (0..32).rev() {
            let difference = i16::from(order[i]) - i16::from(signature[32 + i]) - borrow;
            alternate[32 + i] = difference as u8;
            borrow = i16::from(difference < 0);
        }
        assert!(actual == signature || actual == alternate);
        let verifier = key.public_key().unwrap();
        assert_eq!(
            verifier.verify_prehashed::<Sha256>(&digest, &actual),
            Ok(())
        );
    }
}

#[test]
fn deterministic_sha256_0() {
    deterministic_sha256_batch(0);
}

#[test]
fn deterministic_sha256_1() {
    deterministic_sha256_batch(1);
}

#[test]
fn deterministic_sha256_2() {
    deterministic_sha256_batch(2);
}

#[test]
fn deterministic_sha256_3() {
    deterministic_sha256_batch(3);
}

#[test]
fn messages_and_keys() {
    let cases = vectors();
    let d = hex(&cases[0].d);
    let key = PrivateKey::<Secp256k1>::from_bytes(&d);
    let verifier = key.public_key().unwrap();
    let public = *verifier.as_bytes();
    let message = b"secp256k1 API message";
    let sig = key.clone().sign::<Sha256>(message).unwrap();
    assert_eq!(
        key.sign_prehashed::<Sha256>(&Sha256::digest(message)),
        Ok(sig)
    );
    assert_eq!(verifier.clone().verify::<Sha256>(message, &sig), Ok(()));
    assert_eq!(
        verifier.verify::<Sha256>(b"changed", &sig),
        Err(Error::InvalidSignature)
    );
    let private = PrivateKey::<Secp256k1>::from_bytes(&d);
    assert_eq!(private.public_key(), Ok(PublicKey::from_bytes(&public)));
    let peer = PrivateKey::<Secp256k1>::from_bytes(&hex(&cases[1].d));
    let peer_public = peer.public_key().unwrap();
    assert_eq!(private.exchange(&peer_public), peer.exchange(&verifier));
    assert_eq!(PublicKey::from_bytes(&public), verifier);
    assert_eq!(format!("{key:?}"), "PrivateKey { .. }");

    // The second published vector's key is n-1; the next integer is invalid.
    let mut n = hex::<32>(&cases[1].d);
    let mut carry = 1u16;
    for byte in n.iter_mut().rev() {
        let sum = u16::from(*byte) + carry;
        *byte = sum as u8;
        carry = sum >> 8;
    }
    for d in [[0; 32], n, [0xff; 32]] {
        let bad = PrivateKey::<Secp256k1>::from_bytes(&d);
        assert_eq!(bad.public_key(), Err(Error::InvalidKey));
        assert_eq!(bad.sign::<Sha256>(message), Err(Error::InvalidKey));
        let bad = PrivateKey::<Secp256k1>::from_bytes(&d);
        assert_eq!(
            bad.public_key(),
            Err(verified_garbage::ec::Error::InvalidKey)
        );
        assert_eq!(
            bad.exchange(&verifier),
            Err(verified_garbage::ec::Error::InvalidKey)
        );
    }
    let mut invalid = public;
    invalid[0] = 0;
    assert_eq!(
        private.exchange(&PublicKey::from_bytes(&invalid)),
        Err(verified_garbage::ec::Error::InvalidKey)
    );
    assert_eq!(
        PublicKey::<Secp256k1>::from_bytes(&invalid).verify::<Sha256>(message, &sig),
        Err(Error::InvalidSignature)
    );
}
