//! PBKDF2-HMAC-MD5 (RFC 8018 §5.2): one call of the verified
//! `vg_pbkdf2_hmac_md5` (contract `VG.Spec.Hmac.Instance.pbkdf2Contract` of
//! `VG.Spec.Hmac.md5I`), which derives the whole key.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::pbkdf2_md5::vg_pbkdf2_hmac_md5;
use crate::hashes::md5::{Md5, Md5Backend};

super::whole_pbkdf2!(
    Md5 (Md5Backend) {
        Scalar => vg_pbkdf2_hmac_md5,
    },
    output: 16,
);
