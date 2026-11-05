//! ECDSA over P-256: deterministic signatures, on x86-64 and ARMv7 with HMAC over any
//! hash function that has a table (`HmacHash`), taken as that table
//! (`vg_ecdsa_p256_sign`), and elsewhere with HMAC-SHA-256 or HMAC-SHA-384
//! (`vg_ecdsa_p256_<hash>_sign`), public keys (`vg_ec_p256_public_key`), and
//! verification (`vg_ecdsa_p256_verify`), and their variants on CPUs with
//! the features their `_FEATURES` constants name: `_adx` on x86-64, `_umaal`
//! on ARMv7.

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
use super::{Error, P256, SignatureHash, SigningKey, sealed};
#[cfg(any(target_arch = "x86_64", target_arch = "arm"))]
use crate::arch::ecdsa_p256::vg_ecdsa_p256_sign;
use crate::arch::ecdsa_p256::vg_ecdsa_p256_verify;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_p256::{vg_ecdsa_p256_sign_adx, vg_ecdsa_p256_verify_adx};
#[cfg(target_arch = "arm")]
use crate::arch::ecdsa_p256::{vg_ecdsa_p256_sign_umaal, vg_ecdsa_p256_verify_umaal};
#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
use crate::arch::ecdsa_p256_sha256::vg_ecdsa_p256_sha256_sign;
#[cfg(target_arch = "aarch64")]
use crate::arch::ecdsa_p256_sha256::vg_ecdsa_p256_sha256_sign_sha2;
#[cfg(target_arch = "x86")]
use crate::arch::ecdsa_p256_sha256::vg_ecdsa_p256_sha256_sign_shani;
#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
use crate::arch::ecdsa_p256_sha384::vg_ecdsa_p256_sha384_sign;
#[cfg(target_arch = "aarch64")]
use crate::arch::ecdsa_p256_sha384::vg_ecdsa_p256_sha384_sign_sha3;
use crate::cpu::detected;
use crate::ec::p256::{Mul, public_key};
#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
use crate::hashes::sha256::{Sha256, Sha256Backend};
#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
use crate::hashes::sha384::{Sha384, Sha384Backend};
#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
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
#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
type SignFn<const N: usize> =
    unsafe extern "C" fn(*mut [u8; 64], *const [u8; 32], *const [u8; N], *mut [u64; 1024]) -> u32;

/// The signature `r ‖ s` of `digest` with the key `d`, by `sign`.
///
/// # Safety
///
/// `sign` needs no CPU feature that this CPU lacks.
#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
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
    // Aligned to a cache line on x86-64, where that makes verification
    // faster.
    #[cfg_attr(target_arch = "x86_64", repr(align(64)))]
    struct Scratch([u64; 1024]);
    let mut scratch = Scratch([0u64; 1024]);
    let ok = match Mul::select(detected()) {
        // SAFETY: `q` is valid for reads of 65 bytes, `e` of 32, `signature`
        // of 64 and `scratch` for reads and writes of 8192; `scratch` is a
        // distinct object from the others, so it overlaps neither them nor
        // the call's stack frame, and, as Rust objects, none wraps around
        // the address space.
        Mul::Baseline => unsafe { vg_ecdsa_p256_verify(q, e, signature, &mut scratch.0) },
        // SAFETY: as for `Mul::Baseline`, and the CPU has BMI2 and ADX
        // (`Mul::select`).
        #[cfg(target_arch = "x86_64")]
        Mul::Adx => unsafe { vg_ecdsa_p256_verify_adx(q, e, signature, &mut scratch.0) },
        // SAFETY: as for `Mul::Baseline`, and the CPU has `umaal`
        // (`Mul::select`).
        #[cfg(target_arch = "arm")]
        Mul::Umaal => unsafe { vg_ecdsa_p256_verify_umaal(q, e, signature, &mut scratch.0) },
    };
    if ok == 1 {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
impl sealed::Functions<P256> for Sha256 {
    fn sign(d: &[u8; 32], digest: &[u8; 32]) -> Result<[u8; 64], Error> {
        let f = detected();
        let sign = match (Sha256Backend::select(f), Mul::select(f)) {
            (Sha256Backend::Scalar, Mul::Baseline) => vg_ecdsa_p256_sha256_sign,
            #[cfg(target_arch = "aarch64")]
            (Sha256Backend::Sha2, Mul::Baseline) => vg_ecdsa_p256_sha256_sign_sha2,
            #[cfg(target_arch = "x86")]
            (Sha256Backend::ShaNi, Mul::Baseline) => vg_ecdsa_p256_sha256_sign_shani,
        };
        // SAFETY: `sign` needs no CPU feature that the implementation of
        // SHA-256 and the multiplications selected for this CPU do not.
        unsafe { sign_with(sign, d, digest) }
    }

    fn verify(q: &[u8; 65], digest: &[u8; 32], signature: &[u8; 64]) -> Result<(), Error> {
        verify_with(q, digest, signature)
    }
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
impl SignatureHash<P256> for Sha256 {}

#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
impl sealed::Functions<P256> for Sha384 {
    fn sign(d: &[u8; 32], digest: &[u8; 48]) -> Result<[u8; 64], Error> {
        let f = detected();
        let sign = match (Sha384Backend::select(f), Mul::select(f)) {
            (Sha384Backend::Scalar, Mul::Baseline) => vg_ecdsa_p256_sha384_sign,
            #[cfg(target_arch = "aarch64")]
            (Sha384Backend::Sha3, Mul::Baseline) => vg_ecdsa_p256_sha384_sign_sha3,
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

#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
impl SignatureHash<P256> for Sha384 {}

#[cfg(any(target_arch = "x86_64", target_arch = "arm"))]
impl<H: HmacHash> sealed::Functions<P256> for H {
    fn sign(d: &[u8; 32], digest: &H::Output) -> Result<[u8; 64], Error> {
        let f = detected();
        let sign: SignFn<32, 64> = match Mul::select(f) {
            Mul::Baseline => vg_ecdsa_p256_sign,
            #[cfg(target_arch = "x86_64")]
            Mul::Adx => vg_ecdsa_p256_sign_adx,
            #[cfg(target_arch = "arm")]
            Mul::Umaal => vg_ecdsa_p256_sign_umaal,
        };
        // SAFETY: `sign` needs no CPU feature that the multiplications
        // selected for this CPU do not.
        unsafe { sign_with::<H, 32, 64>(sign, f, d, digest) }
    }

    /// `e` is the leftmost 256 bits of the hash (FIPS 186-5 §6.4.2): its
    /// first 32 bytes, or the hash after zeros if it is shorter.
    fn verify(q: &[u8; 65], digest: &H::Output, signature: &[u8; 64]) -> Result<(), Error> {
        verify_with(q, &leftmost::<32>(digest.as_ref()), signature)
    }
}

#[cfg(any(target_arch = "x86_64", target_arch = "arm"))]
impl<H: HmacHash> SignatureHash<P256> for H {}

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    use super::Mul;
    use crate::arch::ecdsa_p256::VG_ECDSA_P256_SIGN_ADX_FEATURES;
    use crate::cpu::NAMES;
    use verified_garbage_cpu::Features;

    /// The CPU features of the signature with the multiplications `m`.
    fn required(m: Mul) -> Features {
        match m {
            Mul::Baseline => Features(0),
            Mul::Adx => VG_ECDSA_P256_SIGN_ADX_FEATURES,
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
    use crate::arch::ecdsa_p256::VG_ECDSA_P256_SIGN_UMAAL_FEATURES;
    use crate::cpu::NAMES;
    use verified_garbage_cpu::Features;

    /// The CPU features of the signature with the multiplications `m`.
    fn required(m: Mul) -> Features {
        match m {
            Mul::Baseline => Features(0),
            Mul::Umaal => VG_ECDSA_P256_SIGN_UMAAL_FEATURES,
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
