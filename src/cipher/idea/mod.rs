//! IDEA (Lai, 1992) in ECB, CBC, CFB64 and OFB mode (SP 800-38A), in place and
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

pub use cbc::{IdeaCbcDecryptor, IdeaCbcEncryptor};
pub use cfb::{IdeaCfb64Decryptor, IdeaCfb64Encryptor};
pub use ecb::IdeaEcb;
pub use ofb::IdeaOfb;
