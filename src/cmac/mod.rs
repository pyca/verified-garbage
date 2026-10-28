//! CMAC (NIST SP 800-38B, RFC 4493): a MAC built from a block cipher.
//!
//! Each block cipher with a verified CMAC implementation has a module of its
//! own here: `aes`, and `triple_des` (TDEA).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

pub mod aes;
pub mod triple_des;

/// The key does not have a length the block cipher accepts.
pub use crate::error::InvalidKeyLength;
pub use crate::hmac::InvalidMac;
