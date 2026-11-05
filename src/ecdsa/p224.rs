//! ECDSA over P-224: deterministic signatures with HMAC over any hash
//! function that has a table (`HmacHash`), taken as that table
//! (`vg_ecdsa_p224_sign`), public keys (`vg_ec_p224_public_key`), and
//! verification (`vg_ecdsa_p224_verify`), and their variants on CPUs with the
//! features their `_FEATURES` constants name: `_umaal` on ARMv7.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use super::table::{HmacHash, SignFn, leftmost, sign_with};
use super::{Error, P224, SignatureHash, SigningKey, sealed};
use crate::arch::ecdsa_p224::vg_ecdsa_p224_sign;
use crate::arch::ecdsa_p224::vg_ecdsa_p224_verify;
#[cfg(target_arch = "arm")]
use crate::arch::ecdsa_p224::{vg_ecdsa_p224_sign_umaal, vg_ecdsa_p224_verify_umaal};
use crate::cpu::detected;
use crate::ec::p224::{Mul, public_key};

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

impl<H: HmacHash> SignatureHash<P224> for H {}
