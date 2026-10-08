//! Published deterministic ECDSA vectors and public API boundary checks.

#![cfg(target_arch = "x86_64")]

use serde::Deserialize;
use verified_garbage::ecdh::PrivateKey;
use verified_garbage::ecdsa::{Error, Secp256k1, SigningKey, VerifyingKey};
use verified_garbage::hashes::sha256::Sha256;

#[derive(Deserialize)]
struct Case {
    d: String,
    m: String,
    signature: String,
}

#[derive(Deserialize)]
struct Vectors {
    valid: Vec<Case>,
}

fn vectors() -> Vec<Case> {
    serde_json::from_str::<Vectors>(include_str!("../../vectors/secp256k1-ecdsa/ecdsa.json"))
        .unwrap()
        .valid
}

fn hex<const N: usize>(s: &str) -> [u8; N] {
    assert_eq!(s.len(), 2 * N);
    core::array::from_fn(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
}

#[test]
fn deterministic_sha256() {
    let cases = vectors();
    let mut order = hex::<32>(&cases[1].d);
    order[31] += 1; // The published second key is n - 1.
    for case in cases {
        let key = SigningKey::<Secp256k1>::from_bytes(&hex(&case.d));
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
        let public = key.public_key().unwrap();
        let verifier = VerifyingKey::<Secp256k1>::from_bytes(&public);
        assert_eq!(
            verifier.verify_prehashed::<Sha256>(&digest, &actual),
            Ok(())
        );
    }
}

#[test]
fn messages_and_keys() {
    let cases = vectors();
    let d = hex(&cases[0].d);
    let key = SigningKey::<Secp256k1>::from_bytes(&d);
    let public = key.public_key().unwrap();
    let verifier = VerifyingKey::<Secp256k1>::from_bytes(&public);
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
    assert_eq!(private.public_key(), Ok(public));
    let peer = PrivateKey::<Secp256k1>::from_bytes(&hex(&cases[1].d));
    let peer_public = peer.public_key().unwrap();
    assert_eq!(
        private.diffie_hellman(&peer_public),
        peer.diffie_hellman(&public)
    );
    assert_eq!(verifier.to_bytes(), public);
    assert_eq!(format!("{key:?}"), "SigningKey { .. }");

    // The second published vector's key is n-1; the next integer is invalid.
    let mut n = hex::<32>(&cases[1].d);
    let mut carry = 1u16;
    for byte in n.iter_mut().rev() {
        let sum = u16::from(*byte) + carry;
        *byte = sum as u8;
        carry = sum >> 8;
    }
    for d in [[0; 32], n, [0xff; 32]] {
        let bad = SigningKey::<Secp256k1>::from_bytes(&d);
        assert_eq!(bad.public_key(), Err(Error::InvalidKey));
        assert_eq!(bad.sign::<Sha256>(message), Err(Error::InvalidKey));
        let bad = PrivateKey::<Secp256k1>::from_bytes(&d);
        assert_eq!(
            bad.public_key(),
            Err(verified_garbage::ecdh::Error::InvalidKey)
        );
        assert_eq!(
            bad.diffie_hellman(&public),
            Err(verified_garbage::ecdh::Error::InvalidKey)
        );
    }
    let mut invalid = public;
    invalid[0] = 0;
    assert_eq!(
        private.diffie_hellman(&invalid),
        Err(verified_garbage::ecdh::Error::InvalidKey)
    );
    assert_eq!(
        VerifyingKey::<Secp256k1>::from_bytes(&invalid).verify::<Sha256>(message, &sig),
        Err(Error::InvalidSignature)
    );
}
