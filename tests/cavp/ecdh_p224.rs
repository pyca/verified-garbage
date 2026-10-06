//! The P-224 vectors of the SP 800-56A ECC CDH primitive test
//! (vectors/nist-cavp/ecc-cdh/): for each, the private key `dIUT` has the
//! public key `QIUT`, and its shared secret with `QCAVS` is `ZIUT`; and keys
//! that are not valid are refused.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64"
))]

use verified_garbage::ecdh::{Error, P224, PrivateKey};

use super::unhex;

/// Each vector: `QCAVS` (uncompressed), `dIUT`, `QIUT` (uncompressed) and
/// `ZIUT`.
type Vector = ([u8; 57], [u8; 28], [u8; 57], [u8; 28]);

fn point(x: &str, y: &str) -> [u8; 57] {
    let mut p = [4; 57];
    p[1..29].copy_from_slice(&unhex(x));
    p[29..].copy_from_slice(&unhex(y));
    p
}

fn vectors() -> Vec<Vector> {
    let text = include_str!("../../vectors/nist-cavp/ecc-cdh/KAS_ECC_CDH_PrimitiveTest.txt");
    let text = text.split_once("[P-224]").unwrap().1;
    let text = text.split_once("\n[").unwrap().0;
    let fields = super::fields(text);
    assert_eq!(fields.len(), 25 * 7);
    fields
        .chunks(7)
        .map(|v| {
            let names: Vec<&str> = v.iter().map(|(k, _)| *k).collect();
            assert_eq!(
                names,
                [
                    "COUNT", "QCAVSx", "QCAVSy", "dIUT", "QIUTx", "QIUTy", "ZIUT"
                ]
            );
            (
                point(v[1].1, v[2].1),
                unhex(v[3].1).try_into().unwrap(),
                point(v[4].1, v[5].1),
                unhex(v[6].1).try_into().unwrap(),
            )
        })
        .collect()
}

#[test]
fn ecdh_p224() {
    for (peer, d, public, shared) in vectors() {
        let key = PrivateKey::<P224>::from_bytes(&d);
        assert_eq!(key.public_key(), Ok(public));
        assert_eq!(key.diffie_hellman(&peer), Ok(shared));
        assert!(key.clone().diffie_hellman(&public).is_ok());
    }
}

/// The peer's key must be uncompressed, have coordinates below `p` and be
/// on the curve; the private key must be in `[1, n − 1]`.
#[test]
fn ecdh_p224_invalid() {
    let (peer, d, _, _) = vectors()[0];
    let key = PrivateKey::<P224>::from_bytes(&d);
    let mut bad = Vec::new();
    for lead in [0, 2, 3, 5, 0xff] {
        let mut p = peer;
        p[0] = lead;
        bad.push(p);
    }
    let mut off_curve = peer;
    off_curve[56] ^= 1;
    bad.push(off_curve);
    // x = p (the field's prime, which is not below p).
    let mut big_x = peer;
    big_x[1..29].copy_from_slice(&unhex(
        "ffffffffffffffffffffffffffffffff000000000000000000000001",
    ));
    bad.push(big_x);
    let mut big_y = peer;
    big_y[29..].fill(0xff);
    bad.push(big_y);
    bad.push([0; 57]);
    for p in &bad {
        assert_eq!(key.diffie_hellman(p), Err(Error::InvalidKey));
    }
    let n = unhex("ffffffffffffffffffffffffffff16a2e0b8f03e13dd29455c5c2a3d");
    for d in [[0; 28], n.try_into().unwrap(), [0xff; 28]] {
        let key = PrivateKey::<P224>::from_bytes(&d);
        assert_eq!(key.public_key(), Err(Error::InvalidKey));
        assert_eq!(key.diffie_hellman(&peer), Err(Error::InvalidKey));
    }
    assert_eq!(format!("{key:?}"), "PrivateKey { .. }");
    assert_eq!(Error::InvalidKey.to_string(), "invalid ECDH key");
}
