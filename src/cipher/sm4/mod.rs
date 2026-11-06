//! SM4 (GB/T 32907-2016, transcribed in draft-ribose-cfrg-sm4-10) in ECB, CBC,
//! CFB128, OFB and CTR mode (SP 800-38A), in place and without padding.

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

pub use cbc::{Sm4CbcDecryptor, Sm4CbcEncryptor};
pub use cfb::{Sm4Cfb128Decryptor, Sm4Cfb128Encryptor};
pub use ctr::Sm4Ctr;
pub use ecb::Sm4Ecb;
pub use ofb::Sm4Ofb;
