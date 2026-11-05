//! Blowfish (Schneier, FSE 1994) in ECB, CBC, CFB64 and OFB mode (SP 800-38A),
//! without padding.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

mod cbc;
mod cfb;
mod ecb;
mod ofb;

pub use cbc::{BlowfishCbcDecryptor, BlowfishCbcEncryptor};
pub use cfb::{BlowfishCfb64Decryptor, BlowfishCfb64Encryptor};
pub use ecb::{BlowfishEcbDecryptor, BlowfishEcbEncryptor};
pub use ofb::BlowfishOfb;
