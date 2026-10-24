//! RFC 7027 §A.3: brainpoolP512r1.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use verified_garbage::ecdh::{BrainpoolP512r1, Error, PrivateKey};

use super::value;

const CURVE: &str = "brainpoolP512r1";

fn public(x: &str, y: &str) -> [u8; 129] {
    let (x, y) = (value::<64>(CURVE, x), value::<64>(CURVE, y));
    core::array::from_fn(|i| match i {
        0 => 4,
        1..=64 => x[i - 1],
        _ => y[i - 65],
    })
}

#[test]
fn ecdh() {
    let (da, db) = (value::<64>(CURVE, "dA ="), value::<64>(CURVE, "dB ="));
    let qa = public("x_qA =", "y_qA =");
    let qb = public("x_qB =", "y_qB =");
    let z = value::<64>(CURVE, "x_Z =");
    let (a, b) = (
        PrivateKey::<BrainpoolP512r1>::from_bytes(&da),
        PrivateKey::<BrainpoolP512r1>::from_bytes(&db),
    );
    assert_eq!(a.public_key(), Ok(qa));
    assert_eq!(b.public_key(), Ok(qb));
    assert_eq!(a.diffie_hellman(&qb), Ok(z));
    assert_eq!(b.diffie_hellman(&qa), Ok(z));
}

/// An invalid peer key, and private keys out of range.
#[test]
fn invalid_keys() {
    let da = value::<64>(CURVE, "dA =");
    let qa = public("x_qA =", "y_qA =");
    let mut invalid = qa;
    invalid[0] = 0;
    assert_eq!(
        PrivateKey::<BrainpoolP512r1>::from_bytes(&da).diffie_hellman(&invalid),
        Err(Error::InvalidKey)
    );
    // 0 and 2⁵¹² − 1 (above n) are not in [1, n − 1].
    for d in [[0; 64], [0xff; 64]] {
        let bad = PrivateKey::<BrainpoolP512r1>::from_bytes(&d);
        assert_eq!(bad.public_key(), Err(Error::InvalidKey));
        assert_eq!(bad.diffie_hellman(&qa), Err(Error::InvalidKey));
    }
}
