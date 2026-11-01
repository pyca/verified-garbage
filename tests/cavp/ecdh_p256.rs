//! The P-256 vectors of the SP 800-56A ECC CDH primitive test
//! (vectors/nist-cavp/ecc-cdh/): for each, the private key `dIUT` has the
//! public key `QIUT`, and its shared secret with `QCAVS` is `ZIUT`; and keys
//! that are not valid are refused.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::ecdh::{Error, P256, PrivateKey};

use super::unhex;

/// Each vector: `QCAVS` (uncompressed), `dIUT`, `QIUT` (uncompressed) and
/// `ZIUT`.
type Vector = ([u8; 65], [u8; 32], [u8; 65], [u8; 32]);

fn vectors() -> Vec<Vector> {
    let mut vectors = Vec::new();
    for [peer, d, public, shared] in super::ecdh_vectors("P-256", 32) {
        vectors.push((
            peer.try_into().unwrap(),
            d.try_into().unwrap(),
            public.try_into().unwrap(),
            shared.try_into().unwrap(),
        ));
    }
    vectors
}

#[test]
fn ecdh_p256() {
    for (peer, d, public, shared) in vectors() {
        let key = PrivateKey::<P256>::from_bytes(&d);
        assert_eq!(key.public_key(), Ok(public));
        assert_eq!(key.diffie_hellman(&peer), Ok(shared));
        assert!(key.clone().diffie_hellman(&public).is_ok());
    }
}

/// The peer's key must be uncompressed, have coordinates below `p` and be
/// on the curve; the private key must be in `[1, n − 1]`.
#[test]
fn ecdh_p256_invalid() {
    let (peer, d, _, _) = vectors()[0];
    let key = PrivateKey::<P256>::from_bytes(&d);
    let mut bad = Vec::new();
    for lead in [0, 2, 3, 5, 0xff] {
        let mut p = peer;
        p[0] = lead;
        bad.push(p);
    }
    let mut off_curve = peer;
    off_curve[64] ^= 1;
    bad.push(off_curve);
    // x = p (the field's prime, which is not below p).
    let mut big_x = peer;
    big_x[1..33].copy_from_slice(&unhex(
        "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
    ));
    bad.push(big_x);
    let mut big_y = peer;
    big_y[33..].fill(0xff);
    bad.push(big_y);
    bad.push([0; 65]);
    for p in &bad {
        assert_eq!(key.diffie_hellman(p), Err(Error::InvalidKey));
    }
    let n = unhex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551");
    for d in [[0; 32], n.try_into().unwrap(), [0xff; 32]] {
        let key = PrivateKey::<P256>::from_bytes(&d);
        assert_eq!(key.public_key(), Err(Error::InvalidKey));
        assert_eq!(key.diffie_hellman(&peer), Err(Error::InvalidKey));
    }
    assert_eq!(format!("{key:?}"), "PrivateKey { .. }");
    assert_eq!(Error::InvalidKey.to_string(), "invalid ECDH key");
}
