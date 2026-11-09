//! Camellia (RFC 3713) with 128-, 192- and 256-bit keys, in ECB, CBC, CFB128,
//! OFB and CTR mode (SP 800-38A), in place and without padding.

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
mod ctr;
mod ecb;
mod ofb;

pub use cbc::{CamelliaCbcDecryptor, CamelliaCbcEncryptor};
pub use cfb::{CamelliaCfb128Decryptor, CamelliaCfb128Encryptor};
pub use ctr::CamelliaCtr;
pub use ecb::CamelliaEcb;
pub use ofb::CamelliaOfb;
