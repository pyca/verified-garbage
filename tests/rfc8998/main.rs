//! SM4-GCM: the example of RFC 8998 Appendix A.1, read from the
//! byte-for-byte vendored RFC (`vectors/rfc8998/`, see
//! `vectors/sources/rfc8998.toml`), whole, in pieces and with truncated or
//! changed tags. Wycheproof's SM4-GCM vectors, with nonces of other
//! lengths, are in `tests/wycheproof/sm4_gcm.rs`.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "arm",
    target_arch = "aarch64",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

mod sm4_gcm;
