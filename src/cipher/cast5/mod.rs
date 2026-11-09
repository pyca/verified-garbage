//! CAST5 (CAST-128, RFC 2144) with 5- to 16-byte keys, in ECB, CBC, CFB64 and
//! OFB mode (SP 800-38A), in place and without padding.

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

pub use cbc::{Cast5CbcDecryptor, Cast5CbcEncryptor};
pub use cfb::{Cast5Cfb64Decryptor, Cast5Cfb64Encryptor};
pub use ecb::Cast5Ecb;
pub use ofb::Cast5Ofb;
