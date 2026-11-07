//! X448 (RFC 7748 §5), Diffie-Hellman on Curve448.
//!
//! [`exchange`](PrivateKey::exchange) rejects the all-zero shared secret that a
//! public key of small order gives (§6.2), and returns the shared secret raw,
//! not passed through a KDF.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use crate::arch::dispatch::x448::{vg_x448_base_auto, vg_x448_exchange_auto};
use crate::error::XdhError;
use crate::zeroize::zeroize;

/// `X448(scalar, u)` (RFC 7748 §5), by `vg_x448_exchange`, which also checks
/// it: `None` if it is all zero (§6.2).
fn exchange(dit: crate::dit::Dit<'_>, scalar: &[u8; 56], u: &[u8; 56]) -> Option<[u8; 56]> {
    let mut out = [0u8; 56];
    let mut scratch = [0u64; 1024];
    // SAFETY: `out` and `scratch` are valid for reads and writes of 56 and
    // 8192 bytes, and `scalar` and `u` for reads of 56 bytes; the writable
    // buffers are disjoint from each other and from the inputs.
    // No buffer overlaps the callee's stack or wraps around the address space.
    // The dispatcher calls only an implementation the CPU has the features of.
    let nonzero = unsafe { vg_x448_exchange_auto(dit, &mut out, scalar, u, &mut scratch) };
    zeroize(&mut scratch);
    // The contract: 0 if and only if `out` is all zero, so there is no
    // secret in it to destroy.
    (nonzero != 0).then_some(out)
}

/// `X448(scalar, 5)`, by `vg_x448_base`.
fn base(dit: crate::dit::Dit<'_>, scalar: &[u8; 56]) -> [u8; 56] {
    let mut out = [0u8; 56];
    let mut scratch = [0u64; 1024];
    // SAFETY: `out` and `scratch` are valid for reads and writes of 56 and
    // 8192 bytes, and `scalar` for reads of 56 bytes; the writable buffers are
    // disjoint from each other and from the input. No buffer overlaps the
    // callee's stack or wraps around the address space. The dispatcher calls
    // only an implementation the CPU has the features of.
    unsafe { vg_x448_base_auto(dit, &mut out, scalar, &mut scratch) };
    zeroize(&mut scratch);
    out
}

/// An X448 private key: 56 bytes, which X448 decodes into a scalar.
#[derive(Clone)]
pub struct PrivateKey {
    bytes: [u8; 56],
}

impl core::fmt::Debug for PrivateKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("PrivateKey").finish_non_exhaustive()
    }
}

impl Drop for PrivateKey {
    fn drop(&mut self) {
        zeroize(&mut self.bytes);
    }
}

impl PrivateKey {
    /// The size of a private key, in bytes.
    pub const SIZE: usize = 56;

    /// A new private key: 56 random bytes from the operating system.
    pub fn generate() -> Result<Self, XdhError> {
        let mut bytes = [0u8; 56];
        getrandom::fill(&mut bytes).map_err(|_| XdhError::Randomness)?;
        Ok(PrivateKey { bytes })
    }

    /// The private key `bytes`.
    pub fn from_bytes(bytes: &[u8; 56]) -> Self {
        PrivateKey { bytes: *bytes }
    }

    /// The bytes of the key.
    pub fn as_bytes(&self) -> &[u8; 56] {
        &self.bytes
    }

    /// The public key, `X448(k, 5)` (RFC 7748 §6.2).
    pub fn public_key(&self) -> PublicKey {
        crate::dit::enter!(dit);
        PublicKey {
            bytes: base(dit, &self.bytes),
        }
    }

    /// The shared secret with the peer whose public key is `peer`,
    /// `X448(k, peer)` (RFC 7748 §6.2); [`XdhError::ZeroSharedSecret`] if it
    /// is all zero, which the verified code checks without revealing
    /// anything else about it.
    pub fn exchange(&self, peer: &PublicKey) -> Result<[u8; 56], XdhError> {
        crate::dit::enter!(dit);
        exchange(dit, &self.bytes, &peer.bytes).ok_or(XdhError::ZeroSharedSecret)
    }
}

/// An X448 public key: the u-coordinate of a point, 56 bytes (RFC 7748
/// §5).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublicKey {
    bytes: [u8; 56],
}

impl PublicKey {
    /// The size of a public key, in bytes.
    pub const SIZE: usize = 56;

    /// The public key `bytes`. Any 56 bytes are one: X448 reduces them
    /// modulo the field prime (RFC 7748 §5), and [`PrivateKey::exchange`]
    /// rejects the keys of small order.
    pub fn from_bytes(bytes: &[u8; 56]) -> Self {
        PublicKey { bytes: *bytes }
    }

    /// The bytes of the key.
    pub fn as_bytes(&self) -> &[u8; 56] {
        &self.bytes
    }
}

#[cfg(test)]
mod tests {
    use super::{PrivateKey, PublicKey};
    use crate::error::XdhError;

    /// The u-coordinate of the base point, 5 (RFC 7748 §4.2), encoded.
    const BASE_POINT: [u8; 56] = {
        let mut b = [0; 56];
        b[0] = 5;
        b
    };

    /// A generated key agrees with itself: both sides compute the same
    /// secret.
    #[test]
    fn agreement() {
        let a = PrivateKey::generate().unwrap();
        let b = PrivateKey::generate().unwrap();
        assert_ne!(a.as_bytes(), b.as_bytes());
        let ka = a.public_key();
        let kb = b.public_key();
        assert_eq!(a.exchange(&kb).unwrap(), b.exchange(&ka).unwrap());
        assert_eq!(PrivateKey::from_bytes(a.as_bytes()).public_key(), ka);
        assert_eq!(a.clone().public_key(), ka);
        assert_eq!(PublicKey::from_bytes(ka.as_bytes()), ka);
    }

    /// The public key is the shared secret with the base point, `X448(k, 5)`,
    /// for many scalars: random ones, and ones
    /// with every nibble the same.
    #[test]
    fn public_key_is_x448_of_base_point() {
        let check = |k: &[u8; 56]| {
            assert_eq!(
                *PrivateKey::from_bytes(k).public_key().as_bytes(),
                PrivateKey::from_bytes(k)
                    .exchange(&PublicKey::from_bytes(&BASE_POINT))
                    .unwrap()
            );
        };
        for n in 0..=15u8 {
            check(&[n * 0x11; 56]);
        }
        for _ in 0..64 {
            check(PrivateKey::generate().unwrap().as_bytes());
        }
    }

    /// The point 0 has small order: the shared secret is zero.
    #[test]
    fn zero_shared_secret() {
        let a = PrivateKey::from_bytes(&[0x42; 56]);
        let zero = PublicKey::from_bytes(&[0; 56]);
        assert_eq!(a.exchange(&zero).unwrap_err(), XdhError::ZeroSharedSecret);
    }
}
