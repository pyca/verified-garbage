//! X25519 (RFC 7748 §5), Diffie-Hellman on Curve25519.
//!
//! [`exchange`](PrivateKey::exchange) rejects the all-zero shared secret that a
//! public key of small order gives (§6.1), and returns the shared secret raw,
//! not passed through a KDF.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
))]

#[cfg(target_arch = "aarch64")]
use crate::arch::x25519::VG_X25519_BASE_SCRATCH_WRITTEN;
use crate::arch::x25519::vg_x25519;
use crate::arch::x25519::vg_x25519_base;
#[cfg(target_arch = "x86_64")]
use crate::arch::x25519::{
    VG_X25519_ADX_FEATURES, VG_X25519_BASE_ADX_FEATURES, VG_X25519_BASE_IFMA_FEATURES,
    VG_X25519_IFMA_FEATURES, vg_x25519_adx, vg_x25519_base_adx, vg_x25519_base_ifma,
    vg_x25519_ifma,
};
#[cfg(target_arch = "arm")]
use crate::arch::x25519::{VG_X25519_UMAAL_FEATURES, vg_x25519_umaal};
use crate::cpu::detected;
use crate::error::XdhError;
use crate::zeroize::{zeroize, zeroize_raw};
use core::mem::{MaybeUninit, size_of};
use verified_garbage_cpu::Features;

/// The implementations of `vg_x25519`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Backend {
    /// The baseline implementation.
    Baseline,
    /// `_adx`.
    #[cfg(target_arch = "x86_64")]
    Adx,
    /// `_ifma`.
    #[cfg(target_arch = "x86_64")]
    Ifma,
    /// `_umaal`, of `vg_x25519` alone.
    #[cfg(target_arch = "arm")]
    Umaal,
}

impl Backend {
    /// The best implementation a CPU with the features `f` can run.
    #[cfg(target_arch = "x86_64")]
    fn select(f: Features) -> Backend {
        if f.contains(
            const { Features::all(&[VG_X25519_IFMA_FEATURES, VG_X25519_BASE_IFMA_FEATURES]) },
        ) {
            Backend::Ifma
        } else if f.contains(
            const { Features::all(&[VG_X25519_ADX_FEATURES, VG_X25519_BASE_ADX_FEATURES]) },
        ) {
            Backend::Adx
        } else {
            Backend::Baseline
        }
    }

    /// The best implementation a CPU with the features `f` can run.
    #[cfg(target_arch = "arm")]
    fn select(f: Features) -> Backend {
        if f.contains(VG_X25519_UMAAL_FEATURES) {
            Backend::Umaal
        } else {
            Backend::Baseline
        }
    }

    /// The best implementation a CPU with the features `f` can run: there
    /// is only one here.
    #[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
    fn select(_: Features) -> Backend {
        Backend::Baseline
    }
}

/// `X25519(scalar, u)` (RFC 7748 §5), which may be all zero.
fn x25519(scalar: &[u8; 32], u: &[u8; 32]) -> [u8; 32] {
    let mut out = [0u8; 32];
    // Uninitialized: the function's contract holds whatever the scratch
    // holds, so filling it with zeros first would only cost time.
    let mut scratch = MaybeUninit::<[u64; 512]>::uninit();
    let f = match Backend::select(detected()) {
        Backend::Baseline => vg_x25519,
        // `select` chose it because the CPU has the features it needs.
        #[cfg(target_arch = "x86_64")]
        Backend::Adx => vg_x25519_adx,
        #[cfg(target_arch = "x86_64")]
        Backend::Ifma => vg_x25519_ifma,
        #[cfg(target_arch = "arm")]
        Backend::Umaal => vg_x25519_umaal,
    };
    // SAFETY: `out` and `scratch` are valid for reads and writes of 32 and
    // 4096 bytes, and `scalar` and `u` for reads of 32 bytes; they are
    // distinct Rust objects, so they do not overlap each other or the stack,
    // or wrap around the end of the address space; and the CPU has the
    // features of the function `select` chose.
    unsafe { f(&mut out, scalar, u, scratch.as_mut_ptr()) };
    // SAFETY: `scratch` is writable for its whole length.
    unsafe { zeroize_raw(scratch.as_mut_ptr().cast(), size_of::<[u64; 512]>()) };
    out
}

/// `X25519(scalar, 9)`, by `vg_x25519_base`.
fn base(scalar: &[u8; 32]) -> [u8; 32] {
    let mut out = [0u8; 32];
    // Uninitialized, as in `x25519`.
    let mut scratch = MaybeUninit::<[u64; 1024]>::uninit();
    #[cfg(target_arch = "x86_64")]
    let f = match Backend::select(detected()) {
        Backend::Baseline => vg_x25519_base,
        Backend::Adx => vg_x25519_base_adx,
        Backend::Ifma => vg_x25519_base_ifma,
    };
    #[cfg(not(target_arch = "x86_64"))]
    let f = vg_x25519_base;
    // SAFETY: `out` and `scratch` are valid for reads and writes of 32 and
    // 8192 bytes, and `scalar` for reads of 32 bytes; the writable buffers are
    // disjoint from each other and from the input. No buffer overlaps the
    // callee's stack or wraps around the address space. The selected backend
    // has the required CPU features.
    unsafe { f(&mut out, scalar, scratch.as_mut_ptr()) };
    // The bytes of `scratch` the function may have written: on AArch64 its
    // first `VG_X25519_BASE_SCRATCH_WRITTEN` (`Artifact.written`), elsewhere
    // all of it.
    #[cfg(target_arch = "aarch64")]
    let written = VG_X25519_BASE_SCRATCH_WRITTEN;
    #[cfg(not(target_arch = "aarch64"))]
    let written = size_of::<[u64; 1024]>();
    // SAFETY: `scratch` is writable for its whole length, which `written`
    // does not exceed.
    unsafe { zeroize_raw(scratch.as_mut_ptr().cast(), written) };
    out
}

/// An X25519 private key: 32 bytes, which X25519 decodes into a scalar.
#[derive(Clone)]
pub struct PrivateKey {
    bytes: [u8; 32],
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
    pub const SIZE: usize = 32;

    /// A new private key: 32 random bytes from the operating system.
    pub fn generate() -> Result<Self, XdhError> {
        let mut bytes = [0u8; 32];
        getrandom::fill(&mut bytes).map_err(|_| XdhError::Randomness)?;
        Ok(PrivateKey { bytes })
    }

    /// The private key `bytes`.
    pub fn from_bytes(bytes: &[u8; 32]) -> Self {
        PrivateKey { bytes: *bytes }
    }

    /// The bytes of the key.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.bytes
    }

    /// The public key, `X25519(k, 9)` (RFC 7748 §6.1).
    pub fn public_key(&self) -> PublicKey {
        PublicKey {
            bytes: base(&self.bytes),
        }
    }

    /// The shared secret with the peer whose public key is `peer`,
    /// `X25519(k, peer)` (RFC 7748 §6.1); [`XdhError::ZeroSharedSecret`] if it
    /// is all zero, which is checked without revealing anything else about
    /// it.
    pub fn exchange(&self, peer: &PublicKey) -> Result<SharedSecret, XdhError> {
        let mut bytes = x25519(&self.bytes, &peer.bytes);
        if crate::ct::eq(&bytes, &[0; 32]) {
            zeroize(&mut bytes);
            return Err(XdhError::ZeroSharedSecret);
        }
        Ok(SharedSecret { bytes })
    }
}

/// An X25519 public key: the u-coordinate of a point, 32 bytes (RFC 7748
/// §5).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublicKey {
    bytes: [u8; 32],
}

impl PublicKey {
    /// The size of a public key, in bytes.
    pub const SIZE: usize = 32;

    /// The public key `bytes`. Any 32 bytes are one: X25519 ignores the top
    /// bit (RFC 7748 §5), and [`PrivateKey::exchange`] rejects the keys of
    /// small order.
    pub fn from_bytes(bytes: &[u8; 32]) -> Self {
        PublicKey { bytes: *bytes }
    }

    /// The bytes of the key.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.bytes
    }
}

/// The shared secret of an X25519 exchange, never all zero. It is wiped
/// when dropped.
pub struct SharedSecret {
    bytes: [u8; 32],
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
    pub const SIZE: usize = 32;

    /// The bytes of the secret.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.bytes
    }
}

#[cfg(test)]
mod tests {
    #[cfg(target_arch = "arm")]
    use super::VG_X25519_UMAAL_FEATURES;
    use super::{Backend, Features, PrivateKey, PublicKey, x25519};
    #[cfg(target_arch = "x86_64")]
    use super::{
        VG_X25519_ADX_FEATURES, VG_X25519_BASE_ADX_FEATURES, VG_X25519_BASE_IFMA_FEATURES,
        VG_X25519_IFMA_FEATURES,
    };
    use crate::error::XdhError;

    /// The u-coordinate of the base point, 9 (RFC 7748 §4.1), encoded.
    const BASE_POINT: [u8; 32] = {
        let mut b = [0; 32];
        b[0] = 9;
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

    /// The public key is `X25519(k, 9)` for many scalars: random ones, ones
    /// with every nibble the same, and each individual bit (including the
    /// bits that clamping overrides).
    #[test]
    fn public_key_is_x25519_of_base_point() {
        let check = |k: &[u8; 32]| {
            assert_eq!(
                *PrivateKey::from_bytes(k).public_key().as_bytes(),
                x25519(k, &BASE_POINT)
            );
        };
        for n in 0..=15u8 {
            check(&[n * 0x11; 32]);
        }
        for bit in 0..256 {
            let mut k = [0; 32];
            k[bit / 8] = 1 << (bit % 8);
            check(&k);
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
            let adx = Features(VG_X25519_ADX_FEATURES.0 | VG_X25519_BASE_ADX_FEATURES.0);
            assert_eq!(Backend::select(adx), Backend::Adx);
            // `vg_x25519_adx`'s features alone, without the AVX2 of
            // `vg_x25519_base_adx`'s.
            assert_eq!(Backend::select(VG_X25519_ADX_FEATURES), Backend::Baseline);
            assert_eq!(
                Backend::select(Features(verified_garbage_cpu::feature::BMI2)),
                Backend::Baseline
            );
            let ifma = Features(VG_X25519_IFMA_FEATURES.0 | VG_X25519_BASE_IFMA_FEATURES.0);
            assert_eq!(Backend::select(ifma), Backend::Ifma);
            assert_eq!(
                Backend::select(Features(
                    adx.0 | Features(verified_garbage_cpu::feature::AVX512IFMA).0
                )),
                Backend::Adx
            );
            // Without AVX512F, which both `_ifma` functions need.
            assert_eq!(
                Backend::select(Features(
                    ifma.0 & !Features(verified_garbage_cpu::feature::AVX512F).0
                )),
                Backend::Adx
            );
        }
        #[cfg(target_arch = "arm")]
        assert_eq!(Backend::select(VG_X25519_UMAAL_FEATURES), Backend::Umaal);
    }

    /// The point 0 has small order: the shared secret is zero.
    #[test]
    fn zero_shared_secret() {
        let a = PrivateKey::from_bytes(&[0x42; 32]);
        let zero = PublicKey::from_bytes(&[0; 32]);
        assert_eq!(a.exchange(&zero).unwrap_err(), XdhError::ZeroSharedSecret);
        assert_eq!(x25519(a.as_bytes(), &[0; 32]), [0; 32]);
    }
}
