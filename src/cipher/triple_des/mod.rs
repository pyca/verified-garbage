//! Triple DES (FIPS 46-3) in ECB, CBC, CFB8, CFB64 and OFB mode (SP 800-38A),
//! in place and without padding.

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
mod ecb;
mod ofb;

pub use cbc::{TripleDesCbcDecryptor, TripleDesCbcEncryptor};
pub use cfb::{TripleDesCfb64Decryptor, TripleDesCfb64Encryptor};
pub use cfb8::{TripleDesCfb8Decryptor, TripleDesCfb8Encryptor};
pub use ecb::TripleDesEcb;
pub use ofb::TripleDesOfb;
