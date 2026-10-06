//! ECDSA over P-256: deterministic signatures with HMAC-SHA-256 or
//! HMAC-SHA-384 (`vg_ecdsa_p256_<hash>_sign`, which calls
//! `vg_ecdsa_p256_sign`), public keys (`vg_ec_p256_public_key`), and
//! verification (`vg_ecdsa_p256_verify`), each with BMI2 and ADX where the
//! CPU has them (`_adx`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

use super::{Error, P256, SignatureHash, SigningKey, sealed};
use crate::arch::ecdsa_p256::vg_ecdsa_p256_verify;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_p256::vg_ecdsa_p256_verify_adx;
use crate::arch::ecdsa_p256_sha256::vg_ecdsa_p256_sha256_sign;
#[cfg(target_arch = "aarch64")]
use crate::arch::ecdsa_p256_sha256::vg_ecdsa_p256_sha256_sign_sha2;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::ecdsa_p256_sha256::vg_ecdsa_p256_sha256_sign_shani;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_p256_sha256::{
    vg_ecdsa_p256_sha256_sign_adx, vg_ecdsa_p256_sha256_sign_avx2,
    vg_ecdsa_p256_sha256_sign_avx2_adx, vg_ecdsa_p256_sha256_sign_shani_adx,
};
use crate::arch::ecdsa_p256_sha384::vg_ecdsa_p256_sha384_sign;
#[cfg(target_arch = "aarch64")]
use crate::arch::ecdsa_p256_sha384::vg_ecdsa_p256_sha384_sign_sha3;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_p256_sha384::{
    vg_ecdsa_p256_sha384_sign_adx, vg_ecdsa_p256_sha384_sign_avx2,
    vg_ecdsa_p256_sha384_sign_avx2_adx, vg_ecdsa_p256_sha384_sign_shani,
    vg_ecdsa_p256_sha384_sign_shani_adx,
};
use crate::cpu::detected;
use crate::ec::p256::{Mul, public_key};
use crate::hashes::sha256::{Sha256, Sha256Backend};
use crate::hashes::sha384::{Sha384, Sha384Backend};
use crate::zeroize::zeroize;

impl SigningKey<P256> {
    /// The public key `Q = dG`, in the uncompressed form of SEC 1 §2.3.3:
    /// `04 ‖ x ‖ y`, each coordinate 32 bytes, most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn public_key(&self) -> Result<[u8; 65], Error> {
        public_key(&self.d).ok_or(Error::InvalidKey)
    }
}

/// A verified `vg_ecdsa_p256_<hash>_sign`, for a hash of `N` bytes.
#[cfg(target_arch = "x86_64")]
type SignFn<const N: usize> = unsafe extern "sysv64" fn(
    *mut [u8; 64],
    *const [u8; 32],
    *const [u8; N],
    *mut [u64; 1024],
) -> u32;
/// A verified `vg_ecdsa_p256_<hash>_sign`, for a hash of `N` bytes.
#[cfg(any(target_arch = "x86", target_arch = "aarch64", target_arch = "arm"))]
type SignFn<const N: usize> =
    unsafe extern "C" fn(*mut [u8; 64], *const [u8; 32], *const [u8; N], *mut [u64; 1024]) -> u32;

/// The signature `r ‖ s` of `digest` with the key `d`, by `sign`.
///
/// # Safety
///
/// `sign` needs no CPU feature that this CPU lacks.
unsafe fn sign_with<const N: usize>(
    sign: SignFn<N>,
    d: &[u8; 32],
    digest: &[u8; N],
) -> Result<[u8; 64], Error> {
    let mut out = [0; 64];
    let mut scratch = [0u64; 1024];
    // SAFETY: `out` is valid for reads and writes of 64 bytes, `d` for reads
    // of 32, `digest` for reads of `N` and `scratch` for reads and writes of
    // 8192; `out` and `scratch` are distinct objects from each other and the
    // others, so none overlaps another or the call's stack frame, and, as
    // Rust objects, none wraps around the address space. The caller
    // guarantees the CPU features `sign` needs.
    let ok = unsafe { sign(&mut out, d, digest, &mut scratch) };
    zeroize(&mut scratch);
    if ok == 1 {
        Ok(out)
    } else {
        Err(Error::InvalidKey)
    }
}

/// Whether `signature` verifies with `q` for the hash whose leftmost 32
/// bytes are `e`.
fn verify_with(q: &[u8; 65], e: &[u8; 32], signature: &[u8; 64]) -> Result<(), Error> {
    let mut scratch = [0u64; 1024];
    let ok = match Mul::select(detected()) {
        // SAFETY: `q` is valid for reads of 65 bytes, `e` of 32, `signature`
        // of 64 and `scratch` for reads and writes of 8192; `scratch` is a
        // distinct object from the others, so it overlaps neither them nor
        // the call's stack frame, and, as Rust objects, none wraps around
        // the address space.
        Mul::Baseline => unsafe { vg_ecdsa_p256_verify(q, e, signature, &mut scratch) },
        // SAFETY: as for `Mul::Baseline`, and the CPU has BMI2 and ADX
        // (`Mul::select`).
        #[cfg(target_arch = "x86_64")]
        Mul::Adx => unsafe { vg_ecdsa_p256_verify_adx(q, e, signature, &mut scratch) },
    };
    if ok == 1 {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}

impl sealed::Functions<P256> for Sha256 {
    fn sign(d: &[u8; 32], digest: &[u8; 32]) -> Result<[u8; 64], Error> {
        let f = detected();
        let sign = match (Sha256Backend::select(f), Mul::select(f)) {
            (Sha256Backend::Scalar, Mul::Baseline) => vg_ecdsa_p256_sha256_sign,
            #[cfg(target_arch = "aarch64")]
            (Sha256Backend::Sha2, Mul::Baseline) => vg_ecdsa_p256_sha256_sign_sha2,
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            (Sha256Backend::ShaNi, Mul::Baseline) => vg_ecdsa_p256_sha256_sign_shani,
            #[cfg(target_arch = "x86_64")]
            (Sha256Backend::Avx2, Mul::Baseline) => vg_ecdsa_p256_sha256_sign_avx2,
            #[cfg(target_arch = "x86_64")]
            (Sha256Backend::Scalar, Mul::Adx) => vg_ecdsa_p256_sha256_sign_adx,
            #[cfg(target_arch = "x86_64")]
            (Sha256Backend::ShaNi, Mul::Adx) => vg_ecdsa_p256_sha256_sign_shani_adx,
            #[cfg(target_arch = "x86_64")]
            (Sha256Backend::Avx2, Mul::Adx) => vg_ecdsa_p256_sha256_sign_avx2_adx,
        };
        // SAFETY: `sign` needs no CPU feature that the implementation of
        // SHA-256 and the multiplications selected for this CPU do not.
        unsafe { sign_with(sign, d, digest) }
    }

    fn verify(q: &[u8; 65], digest: &[u8; 32], signature: &[u8; 64]) -> Result<(), Error> {
        verify_with(q, digest, signature)
    }
}

impl SignatureHash<P256> for Sha256 {}

impl sealed::Functions<P256> for Sha384 {
    fn sign(d: &[u8; 32], digest: &[u8; 48]) -> Result<[u8; 64], Error> {
        let f = detected();
        let sign = match (Sha384Backend::select(f), Mul::select(f)) {
            (Sha384Backend::Scalar, Mul::Baseline) => vg_ecdsa_p256_sha384_sign,
            #[cfg(target_arch = "aarch64")]
            (Sha384Backend::Sha3, Mul::Baseline) => vg_ecdsa_p256_sha384_sign_sha3,
            #[cfg(target_arch = "x86_64")]
            (Sha384Backend::ShaNi, Mul::Baseline) => vg_ecdsa_p256_sha384_sign_shani,
            #[cfg(target_arch = "x86_64")]
            (Sha384Backend::Avx2, Mul::Baseline) => vg_ecdsa_p256_sha384_sign_avx2,
            #[cfg(target_arch = "x86_64")]
            (Sha384Backend::Scalar, Mul::Adx) => vg_ecdsa_p256_sha384_sign_adx,
            #[cfg(target_arch = "x86_64")]
            (Sha384Backend::ShaNi, Mul::Adx) => vg_ecdsa_p256_sha384_sign_shani_adx,
            #[cfg(target_arch = "x86_64")]
            (Sha384Backend::Avx2, Mul::Adx) => vg_ecdsa_p256_sha384_sign_avx2_adx,
        };
        // SAFETY: `sign` needs no CPU feature that the implementation of
        // SHA-384 and the multiplications selected for this CPU do not.
        unsafe { sign_with(sign, d, digest) }
    }

    /// `e` is the leftmost 256 bits of the hash (FIPS 186-5 §6.4.2), its
    /// first 32 bytes.
    fn verify(q: &[u8; 65], digest: &[u8; 48], signature: &[u8; 64]) -> Result<(), Error> {
        let (e, _) = digest.split_first_chunk::<32>().unwrap();
        verify_with(q, e, signature)
    }
}

impl SignatureHash<P256> for Sha384 {}

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    use super::*;
    use crate::arch::ecdsa_p256_sha256::{
        VG_ECDSA_P256_SHA256_SIGN_ADX_FEATURES, VG_ECDSA_P256_SHA256_SIGN_AVX2_ADX_FEATURES,
        VG_ECDSA_P256_SHA256_SIGN_AVX2_FEATURES, VG_ECDSA_P256_SHA256_SIGN_SHANI_ADX_FEATURES,
        VG_ECDSA_P256_SHA256_SIGN_SHANI_FEATURES,
    };
    use crate::arch::ecdsa_p256_sha384::{
        VG_ECDSA_P256_SHA384_SIGN_ADX_FEATURES, VG_ECDSA_P256_SHA384_SIGN_AVX2_ADX_FEATURES,
        VG_ECDSA_P256_SHA384_SIGN_AVX2_FEATURES, VG_ECDSA_P256_SHA384_SIGN_SHANI_ADX_FEATURES,
        VG_ECDSA_P256_SHA384_SIGN_SHANI_FEATURES,
    };
    use crate::cpu::{Features, NAMES};

    /// The CPU features of the signature with SHA-256's backend `s` and the
    /// multiplications `m`.
    fn sha256_required(s: Sha256Backend, m: Mul) -> Features {
        match (s, m) {
            (Sha256Backend::Scalar, Mul::Baseline) => Features(0),
            (Sha256Backend::ShaNi, Mul::Baseline) => VG_ECDSA_P256_SHA256_SIGN_SHANI_FEATURES,
            (Sha256Backend::Avx2, Mul::Baseline) => VG_ECDSA_P256_SHA256_SIGN_AVX2_FEATURES,
            (Sha256Backend::Scalar, Mul::Adx) => VG_ECDSA_P256_SHA256_SIGN_ADX_FEATURES,
            (Sha256Backend::ShaNi, Mul::Adx) => VG_ECDSA_P256_SHA256_SIGN_SHANI_ADX_FEATURES,
            (Sha256Backend::Avx2, Mul::Adx) => VG_ECDSA_P256_SHA256_SIGN_AVX2_ADX_FEATURES,
        }
    }

    /// The CPU features of the signature with SHA-384's backend `s` and the
    /// multiplications `m`.
    fn sha384_required(s: Sha384Backend, m: Mul) -> Features {
        match (s, m) {
            (Sha384Backend::Scalar, Mul::Baseline) => Features(0),
            (Sha384Backend::ShaNi, Mul::Baseline) => VG_ECDSA_P256_SHA384_SIGN_SHANI_FEATURES,
            (Sha384Backend::Avx2, Mul::Baseline) => VG_ECDSA_P256_SHA384_SIGN_AVX2_FEATURES,
            (Sha384Backend::Scalar, Mul::Adx) => VG_ECDSA_P256_SHA384_SIGN_ADX_FEATURES,
            (Sha384Backend::ShaNi, Mul::Adx) => VG_ECDSA_P256_SHA384_SIGN_SHANI_ADX_FEATURES,
            (Sha384Backend::Avx2, Mul::Adx) => VG_ECDSA_P256_SHA384_SIGN_AVX2_ADX_FEATURES,
        }
    }

    /// Each signature needs no CPU feature that the hash's backend and the
    /// multiplications are not selected for: on every set of features that
    /// selects them.
    #[test]
    fn whole_algorithm_features() {
        for bits in 0..1u32 << NAMES.len() {
            let f = Features(bits);
            let m = Mul::select(f);
            assert!(
                f.contains(sha256_required(Sha256Backend::select(f), m)),
                "{bits:#b}"
            );
            assert!(
                f.contains(sha384_required(Sha384Backend::select(f), m)),
                "{bits:#b}"
            );
        }
    }
}
