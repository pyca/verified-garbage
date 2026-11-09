//! AES (FIPS 197) with 128-, 192- and 256-bit keys, in place and without
//! padding: in ECB, CBC, CFB8, CFB128, OFB and CTR mode (SP 800-38A), and as
//! XTS-AES (IEEE Std 1619-2007, SP 800-38E).

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
mod cfb8;
mod ctr;
mod ecb;
mod ofb;
mod xts;

pub use cbc::{AesCbcDecryptor, AesCbcEncryptor};
pub use cfb::{AesCfb128Decryptor, AesCfb128Encryptor};
pub use cfb8::{AesCfb8Decryptor, AesCfb8Encryptor};
pub use ctr::AesCtr;
pub use ecb::AesEcb;
pub use ofb::AesOfb;
pub use xts::{AesXts, XTS_MAX_BLOCKS, XtsError};
