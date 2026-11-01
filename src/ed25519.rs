//! Ed25519 (RFC 8032), deterministic signatures from 32-byte seeds.
//!
//! Key derivation, signing, and verification each call one verified
//! function, including SHA-512 (but for key derivation on x86-64 and
//! AArch64, below), on every supported architecture. On x86-64 and AArch64,
//! their variants, with the same contracts, are one for each pair of the
//! implementations of SHA-512 (`Sha512Backend`) and of the field (`Field`)
//! this CPU runs; on x86-64, `Field::select` chooses the `_ifma` variants,
//! then the `_adx` ones, on CPUs with the features their `_FEATURES`
//! constants name. On x86-64 and AArch64, [`SigningKey`] keeps the seed's
//! SHA-512 digest, computed once in [`SigningKey::from_seed`] with the
//! verified SHA-512, and key derivation (`vg_ed25519_public_key_expanded`)
//! and signing (`vg_ed25519_sign_expanded`) read it rather than hashing the
//! seed again.
//! Secret scratch values are cleared after use.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use crate::arch::ed25519::vg_ed25519_verify;
#[cfg(target_arch = "x86_64")]
use crate::arch::ed25519::{
    VG_ED25519_PUBLIC_KEY_EXPANDED_ADX_FEATURES, VG_ED25519_PUBLIC_KEY_EXPANDED_IFMA_FEATURES,
    VG_ED25519_SIGN_EXPANDED_ADX_FEATURES, VG_ED25519_SIGN_EXPANDED_IFMA_FEATURES,
    VG_ED25519_VERIFY_ADX_FEATURES, VG_ED25519_VERIFY_IFMA_FEATURES,
    vg_ed25519_public_key_expanded_adx, vg_ed25519_public_key_expanded_ifma,
    vg_ed25519_sign_expanded_adx, vg_ed25519_sign_expanded_avx2, vg_ed25519_sign_expanded_avx2_adx,
    vg_ed25519_sign_expanded_avx2_ifma, vg_ed25519_sign_expanded_ifma,
    vg_ed25519_sign_expanded_shani, vg_ed25519_sign_expanded_shani_adx,
    vg_ed25519_sign_expanded_shani_ifma, vg_ed25519_verify_adx, vg_ed25519_verify_avx2,
    vg_ed25519_verify_avx2_adx, vg_ed25519_verify_avx2_ifma, vg_ed25519_verify_ifma,
    vg_ed25519_verify_shani, vg_ed25519_verify_shani_adx, vg_ed25519_verify_shani_ifma,
};
#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
use crate::arch::ed25519::{vg_ed25519_public_key, vg_ed25519_sign_cached};
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
use crate::arch::ed25519::{vg_ed25519_public_key_expanded, vg_ed25519_sign_expanded};
#[cfg(target_arch = "aarch64")]
use crate::arch::ed25519::{vg_ed25519_sign_expanded_sha3, vg_ed25519_verify_sha3};
use crate::cpu::detected;
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
use crate::hashes::sha512::Sha512;
use crate::hashes::sha512::Sha512Backend;
use crate::zeroize::{zeroize, zeroize_raw};
use core::mem::{MaybeUninit, size_of};
use verified_garbage_cpu::Features;

/// The field multiplications of the complete operations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Field {
    /// The baseline implementation.
    Baseline,
    /// `_adx`.
    #[cfg(target_arch = "x86_64")]
    Adx,
    /// `_ifma`.
    #[cfg(target_arch = "x86_64")]
    Ifma,
}

impl Field {
    /// The fastest field multiplications a CPU with the features `f` can run.
    #[cfg(target_arch = "x86_64")]
    fn select(f: Features) -> Field {
        let adx = f.contains(
            const {
                Features::all(&[
                    VG_ED25519_PUBLIC_KEY_EXPANDED_ADX_FEATURES,
                    VG_ED25519_SIGN_EXPANDED_ADX_FEATURES,
                    VG_ED25519_VERIFY_ADX_FEATURES,
                ])
            },
        );
        let ifma = f.contains(
            const {
                Features::all(&[
                    VG_ED25519_PUBLIC_KEY_EXPANDED_IFMA_FEATURES,
                    VG_ED25519_SIGN_EXPANDED_IFMA_FEATURES,
                    VG_ED25519_VERIFY_IFMA_FEATURES,
                ])
            },
        );
        if adx && ifma {
            Field::Ifma
        } else if adx {
            Field::Adx
        } else {
            Field::Baseline
        }
    }

    /// The field multiplications a CPU with the features `f` can run: there
    /// is only one here.
    #[cfg(not(target_arch = "x86_64"))]
    fn select(_: Features) -> Field {
        Field::Baseline
    }
}

/// Why signature verification failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The signature has the wrong length, a noncanonical encoding, or an invalid equation.
    InvalidSignature,
}

crate::error::impl_error! {
    Error {
        InvalidSignature => "invalid Ed25519 signature",
    }
}

/// An encoded Ed25519 public key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifyingKey {
    bytes: [u8; 32],
}

impl VerifyingKey {
    /// Import an encoded public key. Its encoding is checked during verification.
    pub fn from_bytes(bytes: &[u8; 32]) -> Self {
        Self { bytes: *bytes }
    }

    /// The encoded public key.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.bytes
    }

    /// Verify a pure Ed25519 signature (RFC 8032 §5.1.7).
    ///
    /// Public keys and signatures must use canonical encodings, and the
    /// signature scalar must be less than the subgroup order. This checks
    /// the uncofactored equation. The SHA-512 challenge is reduced modulo the
    /// subgroup order, following RFC 8032 §6. No additional subgroup or
    /// small-order rejection policy is imposed.
    /// Verification timing may depend on the public key, message, and signature.
    pub fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        let signature: &[u8; 64] = signature.try_into().map_err(|_| Error::InvalidSignature)?;
        let valid = verify_message(&self.bytes, message, signature);
        if valid == 1 {
            Ok(())
        } else {
            Err(Error::InvalidSignature)
        }
    }
}

/// An Ed25519 signing key, storing its seed and derived public key.
///
/// The seed is cleared when the key is dropped. Debug output omits it.
#[derive(Clone)]
pub struct SigningKey {
    seed: [u8; 32],
    /// The seed's SHA-512 digest (RFC 8032 §5.1.6, step 1), which signing
    /// on x86-64 and AArch64 reads rather than hashing the seed again.
    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    expanded: [u8; 64],
    public: VerifyingKey,
}

impl core::fmt::Debug for SigningKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SigningKey").finish_non_exhaustive()
    }
}

impl Drop for SigningKey {
    fn drop(&mut self) {
        zeroize(&mut self.seed);
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
        zeroize(&mut self.expanded);
    }
}

impl SigningKey {
    /// Derive a signing key and its public key from an RFC 8032 seed.
    pub fn from_seed(seed: &[u8; 32]) -> Self {
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
        {
            let expanded = Sha512::digest(seed);
            let public = VerifyingKey {
                bytes: public_key_expanded(&expanded),
            };
            Self {
                seed: *seed,
                expanded,
                public,
            }
        }
        #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
        Self {
            seed: *seed,
            public: VerifyingKey {
                bytes: public_key(seed),
            },
        }
    }

    /// The original 32-byte seed.
    pub fn seed(&self) -> &[u8; 32] {
        &self.seed
    }

    /// The public key derived from this key's seed.
    pub fn verifying_key(&self) -> &VerifyingKey {
        &self.public
    }

    /// Sign `message` deterministically using pure Ed25519 (RFC 8032 §5.1.6).
    pub fn sign(&self, message: &[u8]) -> [u8; 64] {
        sign_message(self, message)
    }
}

/// The public key of `seed` (RFC 8032 §5.1.5), with the verified
/// `vg_ed25519_public_key` including SHA-512.
#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
fn public_key(seed: &[u8; 32]) -> [u8; 32] {
    let f = detected();
    let derive = match (Sha512Backend::select(f), Field::select(f)) {
        (Sha512Backend::Scalar, Field::Baseline) => vg_ed25519_public_key,
    };
    let mut public = [0u8; 32];
    // Uninitialized: each function's contract holds whatever the scratch
    // holds, so filling it with zeros first would only cost time.
    let mut scratch = MaybeUninit::<[u64; 1024]>::uninit();
    // SAFETY: the output, seed, and scratch are distinct objects valid for
    // 32, 32, and 8192 bytes, respectively, so they overlap neither each
    // other nor the call's stack, and none wraps the address space. The
    // seed is the caller's. The CPU has the features of both backends
    // chosen (SHA-512's and the field's).
    unsafe { derive(&mut public, seed, scratch.as_mut_ptr()) };
    // SAFETY: `scratch` is writable for its whole length.
    unsafe { zeroize_raw(scratch.as_mut_ptr().cast(), size_of::<[u64; 1024]>()) };
    public
}

/// The public key (RFC 8032 §5.1.5) of the seed whose SHA-512 digest is
/// `expanded`, with the verified `vg_ed25519_public_key_expanded`.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
fn public_key_expanded(expanded: &[u8; 64]) -> [u8; 32] {
    let derive = match Field::select(detected()) {
        Field::Baseline => vg_ed25519_public_key_expanded,
        #[cfg(target_arch = "x86_64")]
        Field::Adx => vg_ed25519_public_key_expanded_adx,
        #[cfg(target_arch = "x86_64")]
        Field::Ifma => vg_ed25519_public_key_expanded_ifma,
    };
    let mut public = [0u8; 32];
    // Uninitialized: the contract holds whatever the scratch holds, so
    // filling it with zeros first would only cost time.
    let mut scratch = MaybeUninit::<[u64; 1024]>::uninit();
    // SAFETY: the output, digest, and scratch are distinct objects valid for
    // 32, 64, and 8192 bytes, respectively, so they overlap neither each
    // other nor the call's stack, and none wraps the address space. The
    // digest is the SHA-512 digest of the caller's seed (`from_seed`). The
    // CPU has the features of the field's backend chosen.
    unsafe { derive(&mut public, expanded, scratch.as_mut_ptr()) };
    // SAFETY: `scratch` is writable for its whole length.
    unsafe { zeroize_raw(scratch.as_mut_ptr().cast(), size_of::<[u64; 1024]>()) };
    public
}

fn verify_message(pk: &[u8; 32], message: &[u8], signature: &[u8; 64]) -> u32 {
    let f = detected();
    let verify = match (Sha512Backend::select(f), Field::select(f)) {
        (Sha512Backend::Scalar, Field::Baseline) => vg_ed25519_verify,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Scalar, Field::Adx) => vg_ed25519_verify_adx,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Scalar, Field::Ifma) => vg_ed25519_verify_ifma,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::ShaNi, Field::Baseline) => vg_ed25519_verify_shani,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::ShaNi, Field::Adx) => vg_ed25519_verify_shani_adx,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::ShaNi, Field::Ifma) => vg_ed25519_verify_shani_ifma,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Avx2, Field::Baseline) => vg_ed25519_verify_avx2,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Avx2, Field::Adx) => vg_ed25519_verify_avx2_adx,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Avx2, Field::Ifma) => vg_ed25519_verify_avx2_ifma,
        #[cfg(target_arch = "aarch64")]
        (Sha512Backend::Sha3, Field::Baseline) => vg_ed25519_verify_sha3,
    };
    // Uninitialized: each function's contract holds whatever the scratch
    // holds, so filling it with zeros first would only cost time.
    let mut scratch = MaybeUninit::<[u64; 1024]>::uninit();
    // SAFETY: input references are valid for their declared lengths and scratch
    // is a distinct writable object. No object overlaps the call stack. The
    // CPU has the features of both backends chosen (SHA-512's and the
    // field's).
    let valid = unsafe {
        verify(
            pk,
            message.as_ptr(),
            message.len(),
            signature,
            scratch.as_mut_ptr(),
        )
    };
    // SAFETY: `scratch` is writable for its whole length.
    unsafe { zeroize_raw(scratch.as_mut_ptr().cast(), size_of::<[u64; 1024]>()) };
    valid
}

fn sign_message(key: &SigningKey, message: &[u8]) -> [u8; 64] {
    let f = detected();
    let sign = match (Sha512Backend::select(f), Field::select(f)) {
        #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
        (Sha512Backend::Scalar, Field::Baseline) => vg_ed25519_sign_cached,
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
        (Sha512Backend::Scalar, Field::Baseline) => vg_ed25519_sign_expanded,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Scalar, Field::Adx) => vg_ed25519_sign_expanded_adx,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Scalar, Field::Ifma) => vg_ed25519_sign_expanded_ifma,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::ShaNi, Field::Baseline) => vg_ed25519_sign_expanded_shani,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::ShaNi, Field::Adx) => vg_ed25519_sign_expanded_shani_adx,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::ShaNi, Field::Ifma) => vg_ed25519_sign_expanded_shani_ifma,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Avx2, Field::Baseline) => vg_ed25519_sign_expanded_avx2,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Avx2, Field::Adx) => vg_ed25519_sign_expanded_avx2_adx,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Avx2, Field::Ifma) => vg_ed25519_sign_expanded_avx2_ifma,
        #[cfg(target_arch = "aarch64")]
        (Sha512Backend::Sha3, Field::Baseline) => vg_ed25519_sign_expanded_sha3,
    };
    let mut signature = [0u8; 64];
    // Uninitialized: each function's contract holds whatever the scratch
    // holds, so filling it with zeros first would only cost time.
    let mut scratch = MaybeUninit::<[u64; 1024]>::uninit();
    // x86-64 and AArch64 sign from the seed's SHA-512 digest, the others
    // from the seed.
    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    let secret = &key.expanded;
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    let secret = &key.seed;
    // SAFETY: the input references are valid for their declared lengths.
    // Signature and scratch are distinct writable objects, disjoint from the
    // inputs and the call's stack. None wraps the address space. The public
    // key is the seed's, and on x86-64 and AArch64 `expanded` is the seed's SHA-512
    // digest (`from_seed` computes both, with `Sha512::digest` and the
    // verified `vg_ed25519_public_key_expanded`). The CPU has the features
    // of both backends chosen (SHA-512's and the field's).
    unsafe {
        sign(
            &mut signature,
            secret,
            &key.public.bytes,
            message.as_ptr(),
            message.len(),
            scratch.as_mut_ptr(),
        )
    };
    // SAFETY: `scratch` is writable for its whole length.
    unsafe { zeroize_raw(scratch.as_mut_ptr().cast(), size_of::<[u64; 1024]>()) };
    signature
}

#[cfg(all(test, target_arch = "aarch64"))]
mod tests {
    use super::Sha512Backend;
    use crate::arch::ed25519::{
        VG_ED25519_SIGN_EXPANDED_SHA3_FEATURES, VG_ED25519_VERIFY_SHA3_FEATURES,
    };
    use crate::cpu::NAMES;
    use verified_garbage_cpu::Features;

    /// Every feature set selecting SHA-512's optimized backend also supports
    /// each complete Ed25519 operation that uses that backend.
    #[test]
    fn whole_algorithm_features() {
        for bits in 0..1u32 << NAMES.len() {
            let features = Features(bits);
            match Sha512Backend::select(features) {
                Sha512Backend::Scalar => {}
                Sha512Backend::Sha3 => {
                    assert!(features.contains(Features::all(&[
                        VG_ED25519_SIGN_EXPANDED_SHA3_FEATURES,
                        VG_ED25519_VERIFY_SHA3_FEATURES,
                    ])));
                }
            }
        }
    }
}

#[cfg(all(test, target_arch = "x86_64"))]
mod x86_64_tests {
    use super::*;
    use crate::arch::ed25519::{
        VG_ED25519_SIGN_EXPANDED_AVX2_ADX_FEATURES, VG_ED25519_SIGN_EXPANDED_AVX2_FEATURES,
        VG_ED25519_SIGN_EXPANDED_AVX2_IFMA_FEATURES, VG_ED25519_SIGN_EXPANDED_SHANI_ADX_FEATURES,
        VG_ED25519_SIGN_EXPANDED_SHANI_FEATURES, VG_ED25519_SIGN_EXPANDED_SHANI_IFMA_FEATURES,
        VG_ED25519_VERIFY_AVX2_ADX_FEATURES, VG_ED25519_VERIFY_AVX2_FEATURES,
        VG_ED25519_VERIFY_AVX2_IFMA_FEATURES, VG_ED25519_VERIFY_SHANI_ADX_FEATURES,
        VG_ED25519_VERIFY_SHANI_FEATURES, VG_ED25519_VERIFY_SHANI_IFMA_FEATURES,
    };
    use crate::cpu::NAMES;
    use verified_garbage_cpu::feature;

    /// The CPU features of the three operations with SHA-512's backend `s`
    /// and the field multiplications `f`.
    fn required(s: Sha512Backend, f: Field) -> [Features; 3] {
        match (s, f) {
            (Sha512Backend::Scalar, Field::Baseline) => [Features(0); 3],
            (Sha512Backend::Scalar, Field::Adx) => [
                VG_ED25519_PUBLIC_KEY_EXPANDED_ADX_FEATURES,
                VG_ED25519_SIGN_EXPANDED_ADX_FEATURES,
                VG_ED25519_VERIFY_ADX_FEATURES,
            ],
            (Sha512Backend::ShaNi, Field::Baseline) => [
                Features(0),
                VG_ED25519_SIGN_EXPANDED_SHANI_FEATURES,
                VG_ED25519_VERIFY_SHANI_FEATURES,
            ],
            (Sha512Backend::ShaNi, Field::Adx) => [
                VG_ED25519_PUBLIC_KEY_EXPANDED_ADX_FEATURES,
                VG_ED25519_SIGN_EXPANDED_SHANI_ADX_FEATURES,
                VG_ED25519_VERIFY_SHANI_ADX_FEATURES,
            ],
            (Sha512Backend::Avx2, Field::Baseline) => [
                Features(0),
                VG_ED25519_SIGN_EXPANDED_AVX2_FEATURES,
                VG_ED25519_VERIFY_AVX2_FEATURES,
            ],
            (Sha512Backend::Avx2, Field::Adx) => [
                VG_ED25519_PUBLIC_KEY_EXPANDED_ADX_FEATURES,
                VG_ED25519_SIGN_EXPANDED_AVX2_ADX_FEATURES,
                VG_ED25519_VERIFY_AVX2_ADX_FEATURES,
            ],
            (Sha512Backend::Scalar, Field::Ifma) => [
                VG_ED25519_PUBLIC_KEY_EXPANDED_IFMA_FEATURES,
                VG_ED25519_SIGN_EXPANDED_IFMA_FEATURES,
                VG_ED25519_VERIFY_IFMA_FEATURES,
            ],
            (Sha512Backend::ShaNi, Field::Ifma) => [
                VG_ED25519_PUBLIC_KEY_EXPANDED_IFMA_FEATURES,
                VG_ED25519_SIGN_EXPANDED_SHANI_IFMA_FEATURES,
                VG_ED25519_VERIFY_SHANI_IFMA_FEATURES,
            ],
            (Sha512Backend::Avx2, Field::Ifma) => [
                VG_ED25519_PUBLIC_KEY_EXPANDED_IFMA_FEATURES,
                VG_ED25519_SIGN_EXPANDED_AVX2_IFMA_FEATURES,
                VG_ED25519_VERIFY_AVX2_IFMA_FEATURES,
            ],
        }
    }

    /// Each complete Ed25519 operation needs no CPU feature that SHA-512's
    /// backend and the field's are not selected for: on every set of
    /// features that selects them.
    #[test]
    fn whole_algorithm_features() {
        for bits in 0..1u32 << NAMES.len() {
            let f = Features(bits);
            let r = required(Sha512Backend::select(f), Field::select(f));
            assert!(f.contains(Features::all(&r)), "{bits:#b}");
        }
    }

    /// The implementations chosen with exactly the features of each one,
    /// with only one of BMI2 and ADX, which `_adx` needs both of, with both
    /// but without the AVX2 `_adx` needs too, with all of `_ifma`'s but
    /// AVX512VL, and with verification's `_ifma` features alone, without the
    /// AVX512F of key derivation's and signing's.
    #[test]
    fn select() {
        let cases: [(Features, Sha512Backend, Field); 14] = [
            (Features(0), Sha512Backend::Scalar, Field::Baseline),
            (
                Features(feature::BMI2),
                Sha512Backend::Scalar,
                Field::Baseline,
            ),
            (
                Features(feature::ADX),
                Sha512Backend::Scalar,
                Field::Baseline,
            ),
            (
                Features(feature::BMI2 | feature::ADX),
                Sha512Backend::Scalar,
                Field::Baseline,
            ),
            (
                Features(feature::AVX | feature::AVX2 | feature::BMI2 | feature::ADX),
                Sha512Backend::Scalar,
                Field::Adx,
            ),
            (
                VG_ED25519_SIGN_EXPANDED_AVX2_FEATURES,
                Sha512Backend::Avx2,
                Field::Baseline,
            ),
            (
                VG_ED25519_SIGN_EXPANDED_AVX2_ADX_FEATURES,
                Sha512Backend::Avx2,
                Field::Adx,
            ),
            (
                VG_ED25519_SIGN_EXPANDED_SHANI_FEATURES,
                Sha512Backend::ShaNi,
                Field::Baseline,
            ),
            (
                VG_ED25519_SIGN_EXPANDED_SHANI_ADX_FEATURES,
                Sha512Backend::ShaNi,
                Field::Adx,
            ),
            (
                VG_ED25519_SIGN_EXPANDED_IFMA_FEATURES,
                Sha512Backend::Scalar,
                Field::Ifma,
            ),
            (
                Features(
                    feature::AVX
                        | feature::AVX2
                        | feature::BMI2
                        | feature::ADX
                        | feature::AVX512F
                        | feature::AVX512IFMA,
                ),
                Sha512Backend::Scalar,
                Field::Adx,
            ),
            (
                VG_ED25519_VERIFY_IFMA_FEATURES,
                Sha512Backend::Scalar,
                Field::Adx,
            ),
            (
                VG_ED25519_SIGN_EXPANDED_AVX2_IFMA_FEATURES,
                Sha512Backend::Avx2,
                Field::Ifma,
            ),
            (
                VG_ED25519_SIGN_EXPANDED_SHANI_IFMA_FEATURES,
                Sha512Backend::ShaNi,
                Field::Ifma,
            ),
        ];
        for (features, s, f) in cases {
            let chosen = (Sha512Backend::select(features), Field::select(features));
            assert_eq!(chosen, (s, f), "{features:?}");
        }
    }
}
