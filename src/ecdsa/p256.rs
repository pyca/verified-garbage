//! ECDSA over P-256.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

#[cfg(not(target_arch = "riscv64"))]
use super::table::leftmost;
use super::table::{HmacHash, SignFn, sign_with};
use super::{Error, SignatureHash, sealed};
use crate::arch::ecdsa_p256::vg_ecdsa_p256_sign;
use crate::arch::ecdsa_p256::vg_ecdsa_p256_verify;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_p256::{vg_ecdsa_p256_sign_adx, vg_ecdsa_p256_verify_adx};
#[cfg(target_arch = "arm")]
use crate::arch::ecdsa_p256::{vg_ecdsa_p256_sign_umaal, vg_ecdsa_p256_verify_umaal};
use crate::cpu::detected;
use crate::ec::P256;
use crate::ec::p256::Mul;

/// Whether `signature` verifies with `q` for the hash `digest`.
fn verify_with(q: &[u8; 65], digest: &[u8], signature: &[u8; 64]) -> Result<(), Error> {
    // Aligned to a cache line on x86-64, where that makes verification
    // faster.
    #[cfg_attr(target_arch = "x86_64", repr(align(64)))]
    struct Scratch([u64; 1024]);
    let mut scratch = Scratch([0u64; 1024]);
    // Elsewhere the function takes the hash's 32 bytes `e` (FIPS 186-5
    // §6.4.2); on RISC-V, the hash itself.
    #[cfg(not(target_arch = "riscv64"))]
    let e = &leftmost::<32>(digest);
    let ok = match Mul::select(detected()) {
        // SAFETY: `q` is valid for reads of 65 bytes, `digest` of `digest.len()`,
        // `signature` of 64 and `scratch` for reads and writes of 8192; `scratch`
        // is a distinct object from the others, so it overlaps neither them nor the
        // call's stack frame, and, as Rust objects, none wraps around the address
        // space.
        #[cfg(target_arch = "riscv64")]
        Mul::Baseline => unsafe {
            vg_ecdsa_p256_verify(q, digest.as_ptr(), digest.len(), signature, &mut scratch.0)
        },
        // SAFETY: `q` is valid for reads of 65 bytes, `e` of 32, `signature`
        // of 64 and `scratch` for reads and writes of 8192; `scratch` is a
        // distinct object from the others, so it overlaps neither them nor
        // the call's stack frame, and, as Rust objects, none wraps around
        // the address space.
        #[cfg(not(target_arch = "riscv64"))]
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
        verify_with(q, digest.as_ref(), signature)
    }
}

impl<H: HmacHash> SignatureHash<P256> for H {}
