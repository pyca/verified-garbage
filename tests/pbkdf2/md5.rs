//! PBKDF2-HMAC-MD5 against its definition.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use verified_garbage::hashes::md5::Md5;
use verified_garbage::pbkdf2::pbkdf2_hmac;

#[test]
fn pbkdf2_hmac_md5() {
    super::check::<Md5>(pbkdf2_hmac::<Md5>);
}
