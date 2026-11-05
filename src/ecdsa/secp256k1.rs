//! ECDSA over secp256k1: deterministic signatures with HMAC over any hash
//! function that has a table (`HmacHash`), taken as that table
//! (`vg_ecdsa_secp256k1_sign`), public keys (`vg_ec_secp256k1_public_key`), and
//! verification (`vg_ecdsa_secp256k1_verify`), and their variants on CPUs with the
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
use super::{Error, Secp256k1, SignatureHash, SigningKey, sealed};
use crate::arch::ecdsa_secp256k1::vg_ecdsa_secp256k1_sign;
use crate::arch::ecdsa_secp256k1::vg_ecdsa_secp256k1_verify;
#[cfg(target_arch = "arm")]
use crate::arch::ecdsa_secp256k1::{
    vg_ecdsa_secp256k1_sign_umaal, vg_ecdsa_secp256k1_verify_umaal,
};
use crate::cpu::detected;
use crate::ec::secp256k1::{Mul, public_key};

impl SigningKey<Secp256k1> {
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

/// Whether `signature` verifies with `q` for the hash whose leftmost 32
/// bytes are `e`.
fn verify_with(q: &[u8; 65], e: &[u8; 32], signature: &[u8; 64]) -> Result<(), Error> {
    let mut scratch = [0u64; 1024];
    let ok = match Mul::select(detected()) {
        // SAFETY: `q` is valid for reads of 65 bytes, `e` of 32,
        // `signature` of 64 and `scratch` for reads and writes of 8192;
        // `scratch` is a distinct object from the others, so it overlaps
        // neither them nor the call's stack frame, and, as Rust objects,
        // none wraps around the address space.
        Mul::Baseline => unsafe { vg_ecdsa_secp256k1_verify(q, e, signature, &mut scratch) },
        // SAFETY: as for `Mul::Baseline`, and the CPU has `umaal`
        // (`Mul::select`).
        #[cfg(target_arch = "arm")]
        Mul::Umaal => unsafe { vg_ecdsa_secp256k1_verify_umaal(q, e, signature, &mut scratch) },
    };
    if ok == 1 {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}

impl<H: HmacHash> sealed::Functions<Secp256k1> for H {
    fn sign(d: &[u8; 32], digest: &H::Output) -> Result<[u8; 64], Error> {
        let f = detected();
        let sign: SignFn<32, 64> = match Mul::select(f) {
            Mul::Baseline => vg_ecdsa_secp256k1_sign,
            #[cfg(target_arch = "arm")]
            Mul::Umaal => vg_ecdsa_secp256k1_sign_umaal,
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

impl<H: HmacHash> SignatureHash<Secp256k1> for H {}
