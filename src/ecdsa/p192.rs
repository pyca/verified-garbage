//! ECDSA over P-192.

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
use super::table::{HmacHash, sign_with};
use super::{Error, SignatureHash, sealed};
use crate::arch::ecdsa_p192::vg_ecdsa_p192_sign;
use crate::arch::ecdsa_p192::vg_ecdsa_p192_verify;
use crate::ec::P192;

/// Whether `signature` verifies with `q` for the hash `digest`.
fn verify_with(q: &[u8; 49], digest: &[u8], signature: &[u8; 48]) -> Result<(), Error> {
    let mut scratch = [0u64; 1024];
    // Elsewhere the function takes the hash's 24 bytes `e` (FIPS 186-5
    // §6.4.2); on RISC-V, the hash itself.
    #[cfg(not(target_arch = "riscv64"))]
    let e = &leftmost::<24>(digest);
    // SAFETY: `q` is valid for reads of 49 bytes, `digest` of `digest.len()`,
    // `signature` of 48 and `scratch` for reads and writes of 8192; `scratch`
    // is a distinct object from the others, so it overlaps neither them nor the
    // call's stack frame, and, as Rust objects, none wraps around the address
    // space.
    #[cfg(target_arch = "riscv64")]
    let ok =
        unsafe { vg_ecdsa_p192_verify(q, digest.as_ptr(), digest.len(), signature, &mut scratch) };
    // SAFETY: `q` is valid for reads of 49 bytes, `e` of 24, `signature` of
    // 48 and `scratch` for reads and writes of 8192; `scratch` is a distinct
    // object from the others, so it overlaps neither them nor the call's
    // stack frame, and, as Rust objects, none wraps around the address
    // space.
    #[cfg(not(target_arch = "riscv64"))]
    let ok = unsafe { vg_ecdsa_p192_verify(q, e, signature, &mut scratch) };
    if ok == 1 {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}

impl<H: HmacHash> sealed::Functions<P192> for H {
    fn sign(d: &[u8; 24], digest: &H::Output) -> Result<[u8; 48], Error> {
        // SAFETY: `vg_ecdsa_p192_sign` needs no CPU feature.
        unsafe { sign_with::<H, 24, 48>(vg_ecdsa_p192_sign, crate::cpu::detected(), d, digest) }
    }

    /// `e` is the leftmost 192 bits of the hash (FIPS 186-5 §6.4.2): its
    /// first 24 bytes.
    fn verify(q: &[u8; 49], digest: &H::Output, signature: &[u8; 48]) -> Result<(), Error> {
        verify_with(q, digest.as_ref(), signature)
    }
}

impl<H: HmacHash> SignatureHash<P192> for H {}
