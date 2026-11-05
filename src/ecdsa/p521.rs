//! ECDSA over P-521: deterministic signatures with HMAC-SHA-512
//! (`vg_ecdsa_p521_sha512_sign`), public
//! keys (`vg_ec_p521_public_key`), and verification (`vg_ecdsa_p521_verify`),
//! and their `_adx` variants on x86-64 CPUs with the features their
//! `_FEATURES` constants name.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

#[cfg(any(target_arch = "x86_64", target_arch = "arm"))]
use super::table::{HmacHash, SignFn, sign_with};
use super::{Error, P521, SignatureHash, SigningKey, sealed};
#[cfg(any(target_arch = "x86_64", target_arch = "arm"))]
use crate::arch::ecdsa_p521::vg_ecdsa_p521_sign;
use crate::arch::ecdsa_p521::vg_ecdsa_p521_verify;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_p521::{vg_ecdsa_p521_sign_adx, vg_ecdsa_p521_verify_adx};
#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
use crate::arch::ecdsa_p521_sha512::vg_ecdsa_p521_sha512_sign;
#[cfg(target_arch = "aarch64")]
use crate::arch::ecdsa_p521_sha512::vg_ecdsa_p521_sha512_sign_sha3;
use crate::cpu::detected;
use crate::ec::p521::{Mul, public_key};
#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
use crate::hashes::sha512::{Sha512, Sha512Backend};
#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
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
fn widen(digest: &[u8]) -> [u8; 66] {
    let mut out = [0; 66];
    let o = 65 - digest.len();
    for (i, b) in digest.iter().enumerate() {
        out[o + i] |= b >> 1;
        out[o + i + 1] |= b << 7;
    }
    out
}

/// Whether `signature` verifies with `q` for the 66 bytes `e` of the hash
/// (its leftmost bits, as many as the order has, FIPS 186-5 §6.4.2).
fn verify_with(q: &[u8; 133], e: &[u8; 66], signature: &[u8; 132]) -> Result<(), Error> {
    let mut scratch = [0u64; 1024];
    let ok = match Mul::select(detected()) {
        // SAFETY: `q` is valid for reads of 133 bytes, `e` of 66,
        // `signature` of 132 and `scratch` for reads and writes of 8192;
        // `scratch` is a distinct object from the others, so it overlaps
        // neither them nor the call's stack frame, and, as Rust objects,
        // none wraps around the address space.
        Mul::Baseline => unsafe { vg_ecdsa_p521_verify(q, e, signature, &mut scratch) },
        // SAFETY: as for `Mul::Baseline`, and the CPU has BMI2 and ADX
        // (`Mul::select`).
        #[cfg(target_arch = "x86_64")]
        Mul::Adx => unsafe { vg_ecdsa_p521_verify_adx(q, e, signature, &mut scratch) },
    };
    if ok == 1 {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}

#[cfg(any(target_arch = "x86_64", target_arch = "arm"))]
impl<H: HmacHash> sealed::Functions<P521> for H {
    fn sign(d: &[u8; 66], digest: &H::Output) -> Result<[u8; 132], Error> {
        let f = detected();
        let sign: SignFn<66, 132> = match Mul::select(f) {
            Mul::Baseline => vg_ecdsa_p521_sign,
            #[cfg(target_arch = "x86_64")]
            Mul::Adx => vg_ecdsa_p521_sign_adx,
        };
        // SAFETY: `sign` needs no CPU feature that the multiplications
        // selected for this CPU do not.
        unsafe { sign_with::<H, 66, 132>(sign, f, d, digest) }
    }

    /// `e` is the hash's integer, which is shorter than the order's 521 bits
    /// (FIPS 186-5 §6.4.2), widened.
    fn verify(q: &[u8; 133], digest: &H::Output, signature: &[u8; 132]) -> Result<(), Error> {
        verify_with(q, &widen(digest.as_ref()), signature)
    }
}

#[cfg(any(target_arch = "x86_64", target_arch = "arm"))]
impl<H: HmacHash> SignatureHash<P521> for H {}

#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
impl sealed::Functions<P521> for Sha512 {
    fn sign(d: &[u8; 66], digest: &[u8; 64]) -> Result<[u8; 132], Error> {
        let f = detected();
        let sign = match (Sha512Backend::select(f), Mul::select(f)) {
            (Sha512Backend::Scalar, Mul::Baseline) => vg_ecdsa_p521_sha512_sign,
            #[cfg(target_arch = "aarch64")]
            (Sha512Backend::Sha3, Mul::Baseline) => vg_ecdsa_p521_sha512_sign_sha3,
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
        verify_with(q, &widen(digest), signature)
    }
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
impl SignatureHash<P521> for Sha512 {}

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    use super::Mul;
    use crate::arch::ecdsa_p521::VG_ECDSA_P521_SIGN_ADX_FEATURES;
    use crate::cpu::NAMES;
    use verified_garbage_cpu::Features;

    /// The CPU features of the signature with the multiplications `m`.
    fn required(m: Mul) -> Features {
        match m {
            Mul::Baseline => Features(0),
            Mul::Adx => VG_ECDSA_P521_SIGN_ADX_FEATURES,
        }
    }

    /// The signature needs no CPU feature that the multiplications are not
    /// selected for: on every set of features that selects them.
    #[test]
    fn whole_algorithm_features() {
        for bits in 0..1u32 << NAMES.len() {
            let f = Features(bits);
            assert!(f.contains(required(Mul::select(f))), "{bits:#b}");
        }
    }
}
