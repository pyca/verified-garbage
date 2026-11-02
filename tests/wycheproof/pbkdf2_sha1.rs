//! PBKDF2-HMAC-SHA-1 (`PbkdfTest` vectors), and `pbkdf2_hmac_verify` on
//! the keys it derives.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::hashes::sha1::Sha1;
use verified_garbage::pbkdf2::pbkdf2_hmac;

use super::pbkdf2::check_with;
use crate::require_vectors;

#[test]
fn pbkdf2_hmac_sha1_vectors() {
    require_vectors!();
    check_with("pbkdf2_hmacsha1_test.json", pbkdf2_hmac::<Sha1>);
}

/// `pbkdf2_hmac_verify` accepts the key derived at the length it checks
/// (40 bytes, and 16: PBKDF2's keys of different lengths share prefixes, so
/// each length checks its own), and rejects any other: with a bit flipped in
/// its first, a middle or its last byte, with a byte appended that is not the
/// next one derived, and from another password.
#[test]
fn pbkdf2_hmac_sha1_verify() {
    use core::num::NonZeroU32;

    use verified_garbage::pbkdf2::{KeyMismatch, pbkdf2_hmac_verify};

    let c = NonZeroU32::new(3).unwrap();
    let mut dk = [0u8; 41];
    pbkdf2_hmac::<Sha1>(b"password", b"salt", c, &mut dk);
    let key: [u8; 40] = dk[..40].try_into().unwrap();
    let verify =
        |expected: &[u8; 40]| pbkdf2_hmac_verify::<Sha1, 40>(b"password", b"salt", c, expected);
    assert_eq!(verify(&key), Ok(()));
    for i in [0, 20, 39] {
        let mut bad = key;
        bad[i] ^= 1;
        assert_eq!(verify(&bad), Err(KeyMismatch));
    }
    let short: [u8; 16] = dk[..16].try_into().unwrap();
    assert_eq!(
        pbkdf2_hmac_verify::<Sha1, 16>(b"password", b"salt", c, &short),
        Ok(())
    );
    assert_eq!(
        pbkdf2_hmac_verify::<Sha1, 41>(b"password", b"salt", c, &dk),
        Ok(())
    );
    dk[40] ^= 1;
    assert_eq!(
        pbkdf2_hmac_verify::<Sha1, 41>(b"password", b"salt", c, &dk),
        Err(KeyMismatch)
    );
    assert_eq!(
        pbkdf2_hmac_verify::<Sha1, 40>(b"passwore", b"salt", c, &key),
        Err(KeyMismatch)
    );
    assert_eq!(KeyMismatch.to_string(), "PBKDF2 derived key does not match");
    let _: &dyn std::error::Error = &KeyMismatch;
    assert_eq!(format!("{KeyMismatch:?}"), "KeyMismatch");
}
