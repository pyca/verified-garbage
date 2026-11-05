//! ECDSA over P-384: deterministic signatures with HMAC over any hash function
//! that has a table (`HmacHash`), taken as that table (`vg_ecdsa_p384_sign`),
//! and verification (`vg_ecdsa_p384_verify`), and their variants on CPUs with
//! the features their `_FEATURES` constants name: `_adx` on x86-64, `_umaal` on
//! ARMv7.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use super::table::{HmacHash, SignFn, leftmost, sign_with};
use super::{Error, SignatureHash, sealed};
use crate::arch::ecdsa_p384::vg_ecdsa_p384_sign;
use crate::arch::ecdsa_p384::vg_ecdsa_p384_verify;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_p384::{vg_ecdsa_p384_sign_adx, vg_ecdsa_p384_verify_adx};
#[cfg(target_arch = "arm")]
use crate::arch::ecdsa_p384::{vg_ecdsa_p384_sign_umaal, vg_ecdsa_p384_verify_umaal};
use crate::cpu::detected;
use crate::ec::P384;
use crate::ec::p384::Mul;

/// Whether `signature` verifies with `q` for the 48 bytes `e` of the hash
/// (its leftmost bits, as many as the order has, FIPS 186-5 §6.4.2).
fn verify_with(q: &[u8; 97], e: &[u8; 48], signature: &[u8; 96]) -> Result<(), Error> {
    let mut scratch = [0u64; 1024];
    let ok = match Mul::select(detected()) {
        // SAFETY: `q` is valid for reads of 97 bytes, `e` of 48,
        // `signature` of 96 and `scratch` for reads and writes of 8192;
        // `scratch` is a distinct object from the others, so it overlaps
        // neither them nor the call's stack frame, and, as Rust objects,
        // none wraps around the address space.
        Mul::Baseline => unsafe { vg_ecdsa_p384_verify(q, e, signature, &mut scratch) },
        // SAFETY: as for `Mul::Baseline`, and the CPU has BMI2 and ADX
        // (`Mul::select`).
        #[cfg(target_arch = "x86_64")]
        Mul::Adx => unsafe { vg_ecdsa_p384_verify_adx(q, e, signature, &mut scratch) },
        // SAFETY: as for `Mul::Baseline`, and the CPU has `umaal`
        // (`Mul::select`).
        #[cfg(target_arch = "arm")]
        Mul::Umaal => unsafe { vg_ecdsa_p384_verify_umaal(q, e, signature, &mut scratch) },
    };
    if ok == 1 {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}

impl<H: HmacHash> sealed::Functions<P384> for H {
    fn sign(d: &[u8; 48], digest: &H::Output) -> Result<[u8; 96], Error> {
        let f = detected();
        let sign: SignFn<48, 96> = match Mul::select(f) {
            Mul::Baseline => vg_ecdsa_p384_sign,
            #[cfg(target_arch = "x86_64")]
            Mul::Adx => vg_ecdsa_p384_sign_adx,
            #[cfg(target_arch = "arm")]
            Mul::Umaal => vg_ecdsa_p384_sign_umaal,
        };
        // SAFETY: `sign` needs no CPU feature that the multiplications
        // selected for this CPU do not.
        unsafe { sign_with::<H, 48, 96>(sign, f, d, digest) }
    }

    /// `e` is the leftmost 384 bits of the hash (FIPS 186-5 §6.4.2): its
    /// first 48 bytes, or the hash after zeros if it is shorter.
    fn verify(q: &[u8; 97], digest: &H::Output, signature: &[u8; 96]) -> Result<(), Error> {
        verify_with(q, &leftmost::<48>(digest.as_ref()), signature)
    }
}

impl<H: HmacHash> SignatureHash<P384> for H {}

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    use super::Mul;
    use crate::arch::ecdsa_p384::VG_ECDSA_P384_SIGN_ADX_FEATURES;
    use crate::cpu::NAMES;
    use verified_garbage_cpu::Features;

    /// The CPU features of the signature with the multiplications `m`.
    fn required(m: Mul) -> Features {
        match m {
            Mul::Baseline => Features(0),
            Mul::Adx => VG_ECDSA_P384_SIGN_ADX_FEATURES,
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

#[cfg(all(test, target_arch = "arm"))]
mod umaal_tests {
    use super::Mul;
    use crate::arch::ecdsa_p384::VG_ECDSA_P384_SIGN_UMAAL_FEATURES;
    use crate::cpu::NAMES;
    use verified_garbage_cpu::Features;

    /// The CPU features of the signature with the multiplications `m`.
    fn required(m: Mul) -> Features {
        match m {
            Mul::Baseline => Features(0),
            Mul::Umaal => VG_ECDSA_P384_SIGN_UMAAL_FEATURES,
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
