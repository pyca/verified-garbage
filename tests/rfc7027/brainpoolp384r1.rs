//! RFC 7027 §A.2: brainpoolP384r1.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::ec::{BrainpoolP384r1, PrivateKey, PublicKey};
use verified_garbage::error::InvalidKey;

use super::value;

const CURVE: &str = "brainpoolP384r1";

fn public(x: &str, y: &str) -> [u8; 97] {
    let (x, y) = (value::<48>(CURVE, x), value::<48>(CURVE, y));
    core::array::from_fn(|i| match i {
        0 => 4,
        1..=48 => x[i - 1],
        _ => y[i - 49],
    })
}

#[test]
fn ecdh() {
    let (da, db) = (value::<48>(CURVE, "dA ="), value::<48>(CURVE, "dB ="));
    let qa = public("x_qA =", "y_qA =");
    let qb = public("x_qB =", "y_qB =");
    let z = value::<48>(CURVE, "x_Z =");
    let (a, b) = (
        PrivateKey::<BrainpoolP384r1>::from_bytes(&da),
        PrivateKey::<BrainpoolP384r1>::from_bytes(&db),
    );
    assert_eq!(a.public_key(), Ok(PublicKey::from_bytes(&qa)));
    assert_eq!(b.public_key(), Ok(PublicKey::from_bytes(&qb)));
    assert_eq!(a.exchange(&PublicKey::from_bytes(&qb)), Ok(z));
    assert_eq!(b.exchange(&PublicKey::from_bytes(&qa)), Ok(z));
}

/// An invalid peer key, and private keys out of range.
#[test]
fn invalid_keys() {
    let da = value::<48>(CURVE, "dA =");
    let qa = public("x_qA =", "y_qA =");
    let mut invalid = qa;
    invalid[0] = 0;
    assert_eq!(
        PrivateKey::<BrainpoolP384r1>::from_bytes(&da).exchange(&PublicKey::from_bytes(&invalid)),
        Err(InvalidKey)
    );
    // 0 and 2³⁸⁴ − 1 (above n) are not in [1, n − 1].
    for d in [[0; 48], [0xff; 48]] {
        let bad = PrivateKey::<BrainpoolP384r1>::from_bytes(&d);
        assert_eq!(bad.public_key(), Err(InvalidKey));
        assert_eq!(bad.exchange(&PublicKey::from_bytes(&qa)), Err(InvalidKey));
    }
}
