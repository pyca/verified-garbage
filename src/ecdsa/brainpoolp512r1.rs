//! ECDSA over brainpoolP512r1.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use super::table::{HmacHash, SignFn, sign_with};
use super::{Error, SignatureHash, sealed};
use crate::arch::ecdsa_brainpoolp512r1::vg_ecdsa_brainpoolp512r1_sign;
use crate::arch::ecdsa_brainpoolp512r1::vg_ecdsa_brainpoolp512r1_verify;
#[cfg(target_arch = "arm")]
use crate::arch::ecdsa_brainpoolp512r1::{
    vg_ecdsa_brainpoolp512r1_sign_umaal, vg_ecdsa_brainpoolp512r1_verify_umaal,
};
use crate::cpu::detected;
use crate::ec::BrainpoolP512r1;
use crate::ec::brainpoolp512r1::Mul;

/// Whether `signature` verifies with `q` for the hash `digest`.
fn verify_with(q: &[u8; 129], digest: &[u8], signature: &[u8; 128]) -> Result<(), Error> {
    let mut scratch = [0u64; 1024];
    let ok = match Mul::select(detected()) {
        // SAFETY: `q` is valid for reads of 129 bytes, `digest` of `digest.len()`,
        // `signature` of 128 and `scratch` for reads and writes of 8192; `scratch`
        // is a distinct object from the others, so it overlaps neither them nor the
        // call's stack frame, and, as Rust objects, none wraps around the address
        // space.
        Mul::Baseline => unsafe {
            vg_ecdsa_brainpoolp512r1_verify(
                q,
                digest.as_ptr(),
                digest.len(),
                signature,
                &mut scratch,
            )
        },
        // SAFETY: as for `Mul::Baseline`, and the CPU has `umaal`
        // (`Mul::select`).
        #[cfg(target_arch = "arm")]
        Mul::Umaal => unsafe {
            vg_ecdsa_brainpoolp512r1_verify_umaal(
                q,
                digest.as_ptr(),
                digest.len(),
                signature,
                &mut scratch,
            )
        },
    };
    if ok == 1 {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}

impl<H: HmacHash> sealed::Functions<BrainpoolP512r1> for H {
    fn sign(d: &[u8; 64], digest: &H::Output) -> Result<[u8; 128], Error> {
        let f = detected();
        let sign: SignFn<64, 128> = match Mul::select(f) {
            Mul::Baseline => vg_ecdsa_brainpoolp512r1_sign,
            #[cfg(target_arch = "arm")]
            Mul::Umaal => vg_ecdsa_brainpoolp512r1_sign_umaal,
        };
        // SAFETY: `sign` needs no CPU feature that the multiplications
        // selected for this CPU do not.
        unsafe { sign_with::<H, 64, 128>(sign, f, d, digest) }
    }

    /// The verified function takes the hash itself, of any length, and
    /// uses as many of its leftmost bits as the order has (FIPS 186-5 §6.4.2).
    fn verify(q: &[u8; 129], digest: &H::Output, signature: &[u8; 128]) -> Result<(), Error> {
        verify_with(q, digest.as_ref(), signature)
    }
}

impl<H: HmacHash> SignatureHash<BrainpoolP512r1> for H {}
