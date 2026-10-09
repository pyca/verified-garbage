//! The P-192 vectors of the SP 800-56A ECC CDH primitive test
//! (vectors/nist-cavp/ecc-cdh/): for each, the private key `dIUT` has the
//! public key `QIUT`, and its shared secret with `QCAVS` is `ZIUT`; and keys
//! that are not valid are refused.

#![cfg(target_arch = "x86_64")]

use verified_garbage::ecdh::{Error, P192, PrivateKey};

use super::unhex;

/// Each vector: `QCAVS` (uncompressed), `dIUT`, `QIUT` (uncompressed) and
/// `ZIUT`.
type Vector = ([u8; 49], [u8; 24], [u8; 49], [u8; 24]);

fn point(x: &str, y: &str) -> [u8; 49] {
    let mut p = [4; 49];
    p[1..25].copy_from_slice(&unhex(x));
    p[25..].copy_from_slice(&unhex(y));
    p
}

fn vectors() -> Vec<Vector> {
    let text = include_str!("../../vectors/nist-cavp/ecc-cdh/KAS_ECC_CDH_PrimitiveTest.txt");
    let text = text.split_once("[P-192]").unwrap().1;
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
fn ecdh_p192() {
    for (peer, d, public, shared) in vectors() {
        let key = PrivateKey::<P192>::from_bytes(&d);
        assert_eq!(key.public_key(), Ok(public));
        assert_eq!(key.diffie_hellman(&peer), Ok(shared));
        assert!(key.clone().diffie_hellman(&public).is_ok());
    }
}

/// The peer's key must be uncompressed, have coordinates below `p` and be
/// on the curve; the private key must be in `[1, n − 1]`.
#[test]
fn ecdh_p192_invalid() {
    let (peer, d, _, _) = vectors()[0];
    let key = PrivateKey::<P192>::from_bytes(&d);
    let mut bad = Vec::new();
    for lead in [0, 2, 3, 5, 0xff] {
        let mut p = peer;
        p[0] = lead;
        bad.push(p);
    }
    let mut off_curve = peer;
    off_curve[48] ^= 1;
    bad.push(off_curve);
    // An all-ones coordinate is above the field prime.
    let mut big_x = peer;
    big_x[1..25].fill(0xff);
    bad.push(big_x);
    let mut big_y = peer;
    big_y[25..].fill(0xff);
    bad.push(big_y);
    bad.push([0; 49]);
    for p in &bad {
        assert_eq!(key.diffie_hellman(p), Err(Error::InvalidKey));
    }
    for d in [[0; 24], [0xff; 24]] {
        let key = PrivateKey::<P192>::from_bytes(&d);
        assert_eq!(key.public_key(), Err(Error::InvalidKey));
        assert_eq!(key.diffie_hellman(&peer), Err(Error::InvalidKey));
    }
    assert_eq!(format!("{key:?}"), "PrivateKey { .. }");
    assert_eq!(Error::InvalidKey.to_string(), "invalid ECDH key");
}
