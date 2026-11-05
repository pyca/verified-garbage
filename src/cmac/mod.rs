//! CMAC (NIST SP 800-38B, RFC 4493) with AES (`aes`) and with TDEA
//! (`triple_des`).

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
