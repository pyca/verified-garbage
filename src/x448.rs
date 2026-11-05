//! X448 (RFC 7748), Diffie-Hellman on Curve448.
//!
//! The whole function is the verified `vg_x448` (contract
//! `VG.Spec.X448.x448Contract`): `X448(k, u)` of RFC 7748 §5, the
//! scalar decoded (clamped) and all 448 bits of the u-coordinate reduced
//! modulo the field prime, in constant time; and
//! [`public_key`](PrivateKey::public_key) is the verified `vg_x448_base`
//! (contract `VG.Spec.X448.x448BaseContract`), `X448(k, 5)`. On x86-64 CPUs
//! with the features their `_FEATURES` constants name, `Backend::select`
//! chooses their variants `vg_x448_adx` and `vg_x448_base_adx`, with the
//! same contracts. This module gives them working space, and destroys what
//! they leave there.
//!
//! [`exchange`](PrivateKey::exchange) is `vg_x448` of the private key and
//! the peer's [`PublicKey`], and rejects the all-zero shared secret that a
//! public key of small order gives (RFC 7748 §6.2), in constant time.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use crate::arch::x448::vg_x448;
use crate::arch::x448::vg_x448_base;
#[cfg(target_arch = "x86_64")]
use crate::arch::x448::{
    VG_X448_ADX_FEATURES, VG_X448_BASE_ADX_FEATURES, vg_x448_adx, vg_x448_base_adx,
};
use crate::cpu::detected;
use crate::zeroize::zeroize;
use verified_garbage_cpu::Features;

/// The implementations of `vg_x448` and `vg_x448_base`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Backend {
    /// The baseline implementation.
    Baseline,
    /// `_adx`.
    #[cfg(target_arch = "x86_64")]
    Adx,
}

impl Backend {
    /// The best implementation a CPU with the features `f` can run.
    #[cfg(target_arch = "x86_64")]
    fn select(f: Features) -> Backend {
        if f.contains(const { Features::all(&[VG_X448_ADX_FEATURES, VG_X448_BASE_ADX_FEATURES]) }) {
            Backend::Adx
        } else {
            Backend::Baseline
        }
    }

    /// The best implementation a CPU with the features `f` can run: there
    /// is only one here.
    #[cfg(not(target_arch = "x86_64"))]
    fn select(_: Features) -> Backend {
        Backend::Baseline
    }
}

/// Why an operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The shared secret is all zero: the peer's public key is a point of
    /// small order (RFC 7748 §6.2).
    ZeroSharedSecret,
    /// The operating system's random number generator failed.
    Randomness,
}

crate::error::impl_error! {
    Error {
        ZeroSharedSecret => "X448 shared secret is all zero",
        Randomness => "X448 random number generator failed",
    }
}

/// `X448(scalar, u)` (RFC 7748 §5), which may be all zero.
fn x448(scalar: &[u8; 56], u: &[u8; 56]) -> [u8; 56] {
    let mut out = [0u8; 56];
    let mut scratch = [0u64; 1024];
    let f = match Backend::select(detected()) {
        Backend::Baseline => vg_x448,
        // `select` chose it because the CPU has the features it needs.
        #[cfg(target_arch = "x86_64")]
        Backend::Adx => vg_x448_adx,
    };
    // SAFETY: `out` and `scratch` are valid for reads and writes of 56 and
    // 8192 bytes, and `scalar` and `u` for reads of 56 bytes; the writable
    // buffers are disjoint from each other and from the inputs.
    // No buffer overlaps the callee's stack or wraps around the address space.
    // The CPU has the features of the function `select` chose.
    unsafe { f(&mut out, scalar, u, &mut scratch) };
    zeroize(&mut scratch);
    out
}

/// `X448(scalar, 5)`, by `vg_x448_base`.
fn base(scalar: &[u8; 56]) -> [u8; 56] {
    let mut out = [0u8; 56];
    let mut scratch = [0u64; 1024];
    let f = match Backend::select(detected()) {
        Backend::Baseline => vg_x448_base,
        // `select` chose it because the CPU has the features it needs.
        #[cfg(target_arch = "x86_64")]
        Backend::Adx => vg_x448_base_adx,
    };
    // SAFETY: `out` and `scratch` are valid for reads and writes of 56 and
    // 8192 bytes, and `scalar` for reads of 56 bytes; the writable buffers are
    // disjoint from each other and from the input. No buffer overlaps the
    // callee's stack or wraps around the address space.
    // The CPU has the features of the function `select` chose.
    unsafe { f(&mut out, scalar, &mut scratch) };
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
    pub fn generate() -> Result<Self, Error> {
        let mut bytes = [0u8; 56];
        getrandom::fill(&mut bytes).map_err(|_| Error::Randomness)?;
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
        PublicKey {
            bytes: base(&self.bytes),
        }
    }

    /// The shared secret with the peer whose public key is `peer`,
    /// `X448(k, peer)` (RFC 7748 §6.2); [`Error::ZeroSharedSecret`] if it
    /// is all zero, which is checked without revealing anything else about
    /// it.
    pub fn exchange(&self, peer: &PublicKey) -> Result<SharedSecret, Error> {
        let mut bytes = x448(&self.bytes, &peer.bytes);
        if crate::ct::eq(&bytes, &[0; 56]) {
            zeroize(&mut bytes);
            return Err(Error::ZeroSharedSecret);
        }
        Ok(SharedSecret { bytes })
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

/// The shared secret of an X448 exchange, never all zero. It is wiped when
/// dropped.
pub struct SharedSecret {
    bytes: [u8; 56],
}

impl core::fmt::Debug for SharedSecret {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SharedSecret").finish_non_exhaustive()
    }
}

impl Drop for SharedSecret {
    fn drop(&mut self) {
        zeroize(&mut self.bytes);
    }
}

impl SharedSecret {
    /// The size of a shared secret, in bytes.
    pub const SIZE: usize = 56;

    /// The bytes of the secret.
    pub fn as_bytes(&self) -> &[u8; 56] {
        &self.bytes
    }
}

#[cfg(test)]
mod tests {
    use super::{Backend, Error, Features, PrivateKey, PublicKey, x448};
    #[cfg(target_arch = "x86_64")]
    use super::{VG_X448_ADX_FEATURES, VG_X448_BASE_ADX_FEATURES};

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
        assert_eq!(
            a.exchange(&kb).unwrap().as_bytes(),
            b.exchange(&ka).unwrap().as_bytes()
        );
        assert_eq!(PrivateKey::from_bytes(a.as_bytes()).public_key(), ka);
        assert_eq!(a.clone().public_key(), ka);
        assert_eq!(PublicKey::from_bytes(ka.as_bytes()), ka);
    }

    /// The public key is `X448(k, 5)` for many scalars: random ones, and ones
    /// with every nibble the same.
    #[test]
    fn public_key_is_x448_of_base_point() {
        let check = |k: &[u8; 56]| {
            assert_eq!(
                *PrivateKey::from_bytes(k).public_key().as_bytes(),
                x448(k, &BASE_POINT)
            );
        };
        for n in 0..=15u8 {
            check(&[n * 0x11; 56]);
        }
        for _ in 0..64 {
            check(PrivateKey::generate().unwrap().as_bytes());
        }
    }

    /// The choice of implementation follows the features (CI tests each
    /// end to end, `VG_CPU_FEATURES=none` the baseline).
    #[test]
    fn backends() {
        assert_eq!(Backend::select(Features(0)), Backend::Baseline);
        #[cfg(target_arch = "x86_64")]
        {
            let adx = Features::all(&[VG_X448_ADX_FEATURES, VG_X448_BASE_ADX_FEATURES]);
            assert_eq!(Backend::select(adx), Backend::Adx);
            assert_eq!(
                Backend::select(Features(verified_garbage_cpu::feature::BMI2)),
                Backend::Baseline
            );
        }
    }

    /// The point 0 has small order: the shared secret is zero.
    #[test]
    fn zero_shared_secret() {
        let a = PrivateKey::from_bytes(&[0x42; 56]);
        let zero = PublicKey::from_bytes(&[0; 56]);
        assert_eq!(a.exchange(&zero).unwrap_err(), Error::ZeroSharedSecret);
        assert_eq!(x448(a.as_bytes(), &[0; 56]), [0; 56]);
    }
}
