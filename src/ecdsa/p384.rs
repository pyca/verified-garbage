//! ECDSA over P-384: deterministic signatures with HMAC-SHA-384
//! (`vg_ecdsa_p384_sha384_sign`, which calls `vg_ecdsa_p384_sign`), public
//! keys (`vg_ec_p384_public_key`), and verification (`vg_ecdsa_p384_verify`),
//! each with BMI2 and ADX where the CPU has them (`_adx`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

use super::{Error, P384, SignatureHash, SigningKey, sealed};
use crate::arch::ecdsa_p384::vg_ecdsa_p384_verify;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_p384::vg_ecdsa_p384_verify_adx;
use crate::arch::ecdsa_p384_sha384::vg_ecdsa_p384_sha384_sign;
#[cfg(target_arch = "aarch64")]
use crate::arch::ecdsa_p384_sha384::vg_ecdsa_p384_sha384_sign_sha3;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_p384_sha384::{
    vg_ecdsa_p384_sha384_sign_adx, vg_ecdsa_p384_sha384_sign_avx2,
    vg_ecdsa_p384_sha384_sign_avx2_adx, vg_ecdsa_p384_sha384_sign_shani,
    vg_ecdsa_p384_sha384_sign_shani_adx,
};
use crate::cpu::detected;
use crate::ec::p384::{Mul, public_key};
use crate::hashes::sha384::{Sha384, Sha384Backend};
use crate::zeroize::zeroize;

impl SigningKey<P384> {
    /// The public key `Q = dG`, in the uncompressed form of SEC 1 §2.3.3:
    /// `04 ‖ x ‖ y`, each coordinate 48 bytes, most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn public_key(&self) -> Result<[u8; 97], Error> {
        public_key(&self.d).ok_or(Error::InvalidKey)
    }
}

impl sealed::Functions<P384> for Sha384 {
    fn sign(d: &[u8; 48], digest: &[u8; 48]) -> Result<[u8; 96], Error> {
        let f = detected();
        let sign = match (Sha384Backend::select(f), Mul::select(f)) {
            (Sha384Backend::Scalar, Mul::Baseline) => vg_ecdsa_p384_sha384_sign,
            #[cfg(target_arch = "aarch64")]
            (Sha384Backend::Sha3, Mul::Baseline) => vg_ecdsa_p384_sha384_sign_sha3,
            #[cfg(target_arch = "x86_64")]
            (Sha384Backend::ShaNi, Mul::Baseline) => vg_ecdsa_p384_sha384_sign_shani,
            #[cfg(target_arch = "x86_64")]
            (Sha384Backend::Avx2, Mul::Baseline) => vg_ecdsa_p384_sha384_sign_avx2,
            #[cfg(target_arch = "x86_64")]
            (Sha384Backend::Scalar, Mul::Adx) => vg_ecdsa_p384_sha384_sign_adx,
            #[cfg(target_arch = "x86_64")]
            (Sha384Backend::ShaNi, Mul::Adx) => vg_ecdsa_p384_sha384_sign_shani_adx,
            #[cfg(target_arch = "x86_64")]
            (Sha384Backend::Avx2, Mul::Adx) => vg_ecdsa_p384_sha384_sign_avx2_adx,
        };
        let mut out = [0; 96];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 96 bytes, `d` and
        // `digest` for reads of 48 and `scratch` for reads and writes of
        // 8192; `out` and `scratch` are distinct objects from each other and
        // the others, so none overlaps another or the call's stack frame,
        // and, as Rust objects, none wraps around the address space. `sign`
        // needs no CPU feature that the implementation of SHA-384 and the
        // multiplications selected for this CPU do not.
        let ok = unsafe { sign(&mut out, d, digest, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }

    fn verify(q: &[u8; 97], digest: &[u8; 48], signature: &[u8; 96]) -> Result<(), Error> {
        let mut scratch = [0u64; 1024];
        let ok = match Mul::select(detected()) {
            // SAFETY: `q` is valid for reads of 97 bytes, `digest` of 48,
            // `signature` of 96 and `scratch` for reads and writes of 8192;
            // `scratch` is a distinct object from the others, so it overlaps
            // neither them nor the call's stack frame, and, as Rust objects,
            // none wraps around the address space.
            Mul::Baseline => unsafe { vg_ecdsa_p384_verify(q, digest, signature, &mut scratch) },
            // SAFETY: as for `Mul::Baseline`, and the CPU has BMI2 and ADX
            // (`Mul::select`).
            #[cfg(target_arch = "x86_64")]
            Mul::Adx => unsafe { vg_ecdsa_p384_verify_adx(q, digest, signature, &mut scratch) },
        };
        if ok == 1 {
            Ok(())
        } else {
            Err(Error::InvalidSignature)
        }
    }
}

impl SignatureHash<P384> for Sha384 {}

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    use super::*;
    use crate::arch::ecdsa_p384_sha384::{
        VG_ECDSA_P384_SHA384_SIGN_ADX_FEATURES, VG_ECDSA_P384_SHA384_SIGN_AVX2_ADX_FEATURES,
        VG_ECDSA_P384_SHA384_SIGN_AVX2_FEATURES, VG_ECDSA_P384_SHA384_SIGN_SHANI_ADX_FEATURES,
        VG_ECDSA_P384_SHA384_SIGN_SHANI_FEATURES,
    };
    use crate::cpu::{Features, NAMES};

    /// The CPU features of the signature with SHA-384's backend `s` and the
    /// multiplications `m`.
    fn required(s: Sha384Backend, m: Mul) -> Features {
        match (s, m) {
            (Sha384Backend::Scalar, Mul::Baseline) => Features(0),
            (Sha384Backend::ShaNi, Mul::Baseline) => VG_ECDSA_P384_SHA384_SIGN_SHANI_FEATURES,
            (Sha384Backend::Avx2, Mul::Baseline) => VG_ECDSA_P384_SHA384_SIGN_AVX2_FEATURES,
            (Sha384Backend::Scalar, Mul::Adx) => VG_ECDSA_P384_SHA384_SIGN_ADX_FEATURES,
            (Sha384Backend::ShaNi, Mul::Adx) => VG_ECDSA_P384_SHA384_SIGN_SHANI_ADX_FEATURES,
            (Sha384Backend::Avx2, Mul::Adx) => VG_ECDSA_P384_SHA384_SIGN_AVX2_ADX_FEATURES,
        }
    }

    /// Each signature needs no CPU feature that the hash's backend and the
    /// multiplications are not selected for: on every set of features that
    /// selects them.
    #[test]
    fn whole_algorithm_features() {
        for bits in 0..1u32 << NAMES.len() {
            let f = Features(bits);
            let r = required(Sha384Backend::select(f), Mul::select(f));
            assert!(f.contains(r), "{bits:#b}");
        }
    }
}
