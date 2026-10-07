//! ECDSA over P-521: deterministic signatures with HMAC-SHA-512
//! (`vg_ecdsa_p521_sha512_sign`, which calls `vg_ecdsa_p521_sign`), public
//! keys (`vg_ec_p521_public_key`), and verification (`vg_ecdsa_p521_verify`),
//! each with BMI2 and ADX (and the comb's selection by AVX2) where the CPU
//! has them (`_adx`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64"
))]

use super::{Error, P521, SignatureHash, SigningKey, sealed};
use crate::arch::ecdsa_p521::vg_ecdsa_p521_verify;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_p521::vg_ecdsa_p521_verify_adx;
use crate::arch::ecdsa_p521_sha512::vg_ecdsa_p521_sha512_sign;
#[cfg(target_arch = "aarch64")]
use crate::arch::ecdsa_p521_sha512::vg_ecdsa_p521_sha512_sign_sha3;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_p521_sha512::{
    vg_ecdsa_p521_sha512_sign_adx, vg_ecdsa_p521_sha512_sign_avx2,
    vg_ecdsa_p521_sha512_sign_avx2_adx, vg_ecdsa_p521_sha512_sign_shani,
    vg_ecdsa_p521_sha512_sign_shani_adx,
};
use crate::cpu::detected;
use crate::ec::p521::{Mul, public_key};
use crate::hashes::sha512::{Sha512, Sha512Backend};
use crate::zeroize::zeroize;

impl SigningKey<P521> {
    /// The public key `Q = dG`, in the uncompressed form of SEC 1 §2.3.3:
    /// `04 ‖ x ‖ y`, each coordinate 66 bytes, most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn public_key(&self) -> Result<[u8; 133], Error> {
        public_key(&self.d).ok_or(Error::InvalidKey)
    }
}

/// The 66 bytes `vg_ecdsa_p521_verify` takes for a hash shorter than them:
/// the hash's integer shifted left by 7 bits, so that its leftmost 521 bits
/// are the hash's integer (FIPS 186-5 §6.4.1).
fn widen(digest: &[u8; 64]) -> [u8; 66] {
    let mut out = [0; 66];
    for (i, b) in digest.iter().enumerate() {
        out[i + 1] |= b >> 1;
        out[i + 2] |= b << 7;
    }
    out
}

impl sealed::Functions<P521> for Sha512 {
    fn sign(d: &[u8; 66], digest: &[u8; 64]) -> Result<[u8; 132], Error> {
        let f = detected();
        let sign = match (Sha512Backend::select(f), Mul::select(f)) {
            (Sha512Backend::Scalar, Mul::Baseline) => vg_ecdsa_p521_sha512_sign,
            #[cfg(target_arch = "aarch64")]
            (Sha512Backend::Sha3, Mul::Baseline) => vg_ecdsa_p521_sha512_sign_sha3,
            #[cfg(target_arch = "x86_64")]
            (Sha512Backend::ShaNi, Mul::Baseline) => vg_ecdsa_p521_sha512_sign_shani,
            #[cfg(target_arch = "x86_64")]
            (Sha512Backend::Avx2, Mul::Baseline) => vg_ecdsa_p521_sha512_sign_avx2,
            #[cfg(target_arch = "x86_64")]
            (Sha512Backend::Scalar, Mul::Adx) => vg_ecdsa_p521_sha512_sign_adx,
            #[cfg(target_arch = "x86_64")]
            (Sha512Backend::ShaNi, Mul::Adx) => vg_ecdsa_p521_sha512_sign_shani_adx,
            #[cfg(target_arch = "x86_64")]
            (Sha512Backend::Avx2, Mul::Adx) => vg_ecdsa_p521_sha512_sign_avx2_adx,
        };
        let mut out = [0; 132];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 132 bytes, `d` for
        // reads of 66, `digest` of 64 and `scratch` for reads and writes of
        // 8192; `out` and `scratch` are distinct objects from each other and
        // the others, so none overlaps another or the call's stack frame,
        // and, as Rust objects, none wraps around the address space. `sign`
        // needs no CPU feature that the implementation of SHA-512 and the
        // multiplications selected for this CPU do not.
        let ok = unsafe { sign(&mut out, d, digest, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }

    fn verify(q: &[u8; 133], digest: &[u8; 64], signature: &[u8; 132]) -> Result<(), Error> {
        let digest = widen(digest);
        let mut scratch = [0u64; 1024];
        let ok = match Mul::select(detected()) {
            // SAFETY: `q` is valid for reads of 133 bytes, `digest` of 66,
            // `signature` of 132 and `scratch` for reads and writes of 8192;
            // `scratch` is a distinct object from the others, so it overlaps
            // neither them nor the call's stack frame, and, as Rust objects,
            // none wraps around the address space.
            Mul::Baseline => unsafe { vg_ecdsa_p521_verify(q, &digest, signature, &mut scratch) },
            // SAFETY: as for `Mul::Baseline`, and the CPU has BMI2 and ADX
            // (`Mul::select`).
            #[cfg(target_arch = "x86_64")]
            Mul::Adx => unsafe { vg_ecdsa_p521_verify_adx(q, &digest, signature, &mut scratch) },
        };
        if ok == 1 {
            Ok(())
        } else {
            Err(Error::InvalidSignature)
        }
    }
}

impl SignatureHash<P521> for Sha512 {}

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    use super::*;
    use crate::arch::ecdsa_p521_sha512::{
        VG_ECDSA_P521_SHA512_SIGN_ADX_FEATURES, VG_ECDSA_P521_SHA512_SIGN_AVX2_ADX_FEATURES,
        VG_ECDSA_P521_SHA512_SIGN_AVX2_FEATURES, VG_ECDSA_P521_SHA512_SIGN_SHANI_ADX_FEATURES,
        VG_ECDSA_P521_SHA512_SIGN_SHANI_FEATURES,
    };
    use crate::cpu::{Features, NAMES};

    /// The CPU features of the signature with SHA-512's backend `s` and the
    /// multiplications `m`.
    fn required(s: Sha512Backend, m: Mul) -> Features {
        match (s, m) {
            (Sha512Backend::Scalar, Mul::Baseline) => Features(0),
            (Sha512Backend::ShaNi, Mul::Baseline) => VG_ECDSA_P521_SHA512_SIGN_SHANI_FEATURES,
            (Sha512Backend::Avx2, Mul::Baseline) => VG_ECDSA_P521_SHA512_SIGN_AVX2_FEATURES,
            (Sha512Backend::Scalar, Mul::Adx) => VG_ECDSA_P521_SHA512_SIGN_ADX_FEATURES,
            (Sha512Backend::ShaNi, Mul::Adx) => VG_ECDSA_P521_SHA512_SIGN_SHANI_ADX_FEATURES,
            (Sha512Backend::Avx2, Mul::Adx) => VG_ECDSA_P521_SHA512_SIGN_AVX2_ADX_FEATURES,
        }
    }

    /// Each signature needs no CPU feature that the hash's backend and the
    /// multiplications are not selected for: on every set of features that
    /// selects them.
    #[test]
    fn whole_algorithm_features() {
        for bits in 0..1u32 << NAMES.len() {
            let f = Features(bits);
            let r = required(Sha512Backend::select(f), Mul::select(f));
            assert!(f.contains(r), "{bits:#b}");
        }
    }
}
