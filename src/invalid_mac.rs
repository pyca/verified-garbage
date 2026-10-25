//! The error of every MAC check: HMAC's, CMAC's, Poly1305's and keyed
//! BLAKE2's, which their modules re-export.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

/// The MAC did not match: the message or the key is not what was
/// authenticated. HMAC, CMAC, Poly1305 and keyed BLAKE2 return it (each
/// module re-exports it; not every one is built on every architecture).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidMac;

impl core::fmt::Display for InvalidMac {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("MAC does not match")
    }
}

impl core::error::Error for InvalidMac {}

#[cfg(test)]
mod tests {
    use super::InvalidMac;

    /// The error's message (which `crate::error`'s test checks too, on the
    /// architectures it is built for).
    #[test]
    fn invalid_mac_display() {
        extern crate std;
        use std::string::ToString;
        assert_eq!(InvalidMac.to_string(), "MAC does not match");
    }
}
