//! RC2 (RFC 2268) in CBC mode, incrementally and without padding.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

mod cbc;

pub use cbc::{Error, Rc2CbcDecryptor, Rc2CbcEncryptor};
