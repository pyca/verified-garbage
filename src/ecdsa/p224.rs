//! ECDSA over P-224: deterministic signatures with HMAC-SHA-224
//! (`vg_ecdsa_p224_sha224_sign`), public
//! keys (`vg_ec_p224_public_key`), and verification (`vg_ecdsa_p224_verify`),
//! and their `_umaal` variants on ARMv7 CPUs with the features their
//! `_FEATURES` constants name.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

#[cfg(any(target_arch = "x86_64", target_arch = "arm"))]
use super::table::{HmacHash, SignFn, leftmost, sign_with};
use super::{Error, P224, SignatureHash, SigningKey, sealed};
#[cfg(any(target_arch = "x86_64", target_arch = "arm"))]
use crate::arch::ecdsa_p224::vg_ecdsa_p224_sign;
use crate::arch::ecdsa_p224::vg_ecdsa_p224_verify;
#[cfg(target_arch = "arm")]
use crate::arch::ecdsa_p224::{vg_ecdsa_p224_sign_umaal, vg_ecdsa_p224_verify_umaal};
#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
use crate::arch::ecdsa_p224_sha224::vg_ecdsa_p224_sha224_sign;
#[cfg(target_arch = "aarch64")]
use crate::arch::ecdsa_p224_sha224::vg_ecdsa_p224_sha224_sign_sha2;
#[cfg(target_arch = "x86")]
use crate::arch::ecdsa_p224_sha224::vg_ecdsa_p224_sha224_sign_shani;
use crate::cpu::detected;
use crate::ec::p224::{Mul, public_key};
#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
use crate::hashes::sha224::{Sha224, Sha224Backend};
#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
use crate::zeroize::zeroize;

impl SigningKey<P224> {
    /// The public key `Q = dG`, in the uncompressed form of SEC 1 §2.3.3:
    /// `04 ‖ x ‖ y`, each coordinate 28 bytes, most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn public_key(&self) -> Result<[u8; 57], Error> {
        public_key(&self.d).ok_or(Error::InvalidKey)
    }
}

/// Whether `signature` verifies with `q` for the hash whose leftmost 28
/// bytes are `e`.
fn verify_with(q: &[u8; 57], e: &[u8; 28], signature: &[u8; 56]) -> Result<(), Error> {
    let mut scratch = [0u64; 1024];
    let ok = match Mul::select(detected()) {
        // SAFETY: `q` is valid for reads of 57 bytes, `e` of 28,
        // `signature` of 56 and `scratch` for reads and writes of 8192;
        // `scratch` is a distinct object from the others, so it overlaps
        // neither them nor the call's stack frame, and, as Rust objects,
        // none wraps around the address space.
        Mul::Baseline => unsafe { vg_ecdsa_p224_verify(q, e, signature, &mut scratch) },
        // SAFETY: as for `Mul::Baseline`, and the CPU has `umaal`
        // (`Mul::select`).
        #[cfg(target_arch = "arm")]
        Mul::Umaal => unsafe { vg_ecdsa_p224_verify_umaal(q, e, signature, &mut scratch) },
    };
    if ok == 1 {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}

#[cfg(any(target_arch = "x86_64", target_arch = "arm"))]
impl<H: HmacHash> sealed::Functions<P224> for H {
    fn sign(d: &[u8; 28], digest: &H::Output) -> Result<[u8; 56], Error> {
        let f = detected();
        let sign: SignFn<28, 56> = match Mul::select(f) {
            Mul::Baseline => vg_ecdsa_p224_sign,
            #[cfg(target_arch = "arm")]
            Mul::Umaal => vg_ecdsa_p224_sign_umaal,
        };
        // SAFETY: `sign` needs no CPU feature that the multiplications
        // selected for this CPU do not.
        unsafe { sign_with::<H, 28, 56>(sign, f, d, digest) }
    }

    /// `e` is the leftmost 224 bits of the hash (FIPS 186-5 §6.4.2): its
    /// first 28 bytes, or the hash after zeros if it is shorter.
    fn verify(q: &[u8; 57], digest: &H::Output, signature: &[u8; 56]) -> Result<(), Error> {
        verify_with(q, &leftmost::<28>(digest.as_ref()), signature)
    }
}

#[cfg(any(target_arch = "x86_64", target_arch = "arm"))]
impl<H: HmacHash> SignatureHash<P224> for H {}

#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
impl sealed::Functions<P224> for Sha224 {
    fn sign(d: &[u8; 28], digest: &[u8; 28]) -> Result<[u8; 56], Error> {
        let f = detected();
        let sign = match (Sha224Backend::select(f), Mul::select(f)) {
            (Sha224Backend::Scalar, Mul::Baseline) => vg_ecdsa_p224_sha224_sign,
            #[cfg(target_arch = "aarch64")]
            (Sha224Backend::Sha2, Mul::Baseline) => vg_ecdsa_p224_sha224_sign_sha2,
            #[cfg(target_arch = "x86")]
            (Sha224Backend::ShaNi, Mul::Baseline) => vg_ecdsa_p224_sha224_sign_shani,
        };
        let mut out = [0; 56];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 56 bytes, `d` and
        // `digest` for reads of 28 and `scratch` for reads and writes of
        // 8192; `out` and `scratch` are distinct objects from each other and
        // the others, so none overlaps another or the call's stack frame,
        // and, as Rust objects, none wraps around the address space. `sign`
        // needs no CPU feature that the implementation of SHA-224 and the
        // multiplications selected for this CPU do not.
        let ok = unsafe { sign(&mut out, d, digest, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }

    fn verify(q: &[u8; 57], digest: &[u8; 28], signature: &[u8; 56]) -> Result<(), Error> {
        verify_with(q, digest, signature)
    }
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
impl SignatureHash<P224> for Sha224 {}

#[cfg(all(test, target_arch = "arm"))]
mod umaal_tests {
    use super::Mul;
    use crate::arch::ecdsa_p224::VG_ECDSA_P224_SIGN_UMAAL_FEATURES;
    use crate::cpu::NAMES;
    use verified_garbage_cpu::Features;

    /// The CPU features of the signature with the multiplications `m`.
    fn required(m: Mul) -> Features {
        match m {
            Mul::Baseline => Features(0),
            Mul::Umaal => VG_ECDSA_P224_SIGN_UMAAL_FEATURES,
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
