//! ECDSA over P-521.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use super::table::{HmacHash, SignFn, sign_with};
use super::{Error, SignatureHash, sealed};
use crate::arch::ecdsa_p521::vg_ecdsa_p521_sign;
use crate::arch::ecdsa_p521::vg_ecdsa_p521_verify;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_p521::{vg_ecdsa_p521_sign_adx, vg_ecdsa_p521_verify_adx};
use crate::cpu::detected;
use crate::ec::P521;
use crate::ec::p521::Mul;

/// Whether `signature` verifies with `q` for the hash `digest`.
fn verify_with(q: &[u8; 133], digest: &[u8], signature: &[u8; 132]) -> Result<(), Error> {
    let mut scratch = [0u64; 1024];
    let ok = match Mul::select(detected()) {
        // SAFETY: `q` is valid for reads of 133 bytes, `digest` of `digest.len()`,
        // `signature` of 132 and `scratch` for reads and writes of 8192; `scratch`
        // is a distinct object from the others, so it overlaps neither them nor the
        // call's stack frame, and, as Rust objects, none wraps around the address
        // space.
        Mul::Baseline => unsafe {
            vg_ecdsa_p521_verify(q, digest.as_ptr(), digest.len(), signature, &mut scratch)
        },
        // SAFETY: as for `Mul::Baseline`, and the CPU has BMI2 and ADX
        // (`Mul::select`).
        #[cfg(target_arch = "x86_64")]
        Mul::Adx => unsafe {
            vg_ecdsa_p521_verify_adx(q, digest.as_ptr(), digest.len(), signature, &mut scratch)
        },
    };
    if ok == 1 {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}

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

    /// The verified function takes the hash itself, of any length, and
    /// uses as many of its leftmost bits as the order has (FIPS 186-5 §6.4.2).
    fn verify(q: &[u8; 133], digest: &H::Output, signature: &[u8; 132]) -> Result<(), Error> {
        verify_with(q, digest.as_ref(), signature)
    }
}

impl<H: HmacHash> SignatureHash<P521> for H {}
