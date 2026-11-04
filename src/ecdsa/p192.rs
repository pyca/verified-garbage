//! ECDSA over p192: deterministic signatures with HMAC-SHA-256
//! (`vg_ecdsa_p192_sha256_sign`), or, on x86-64 and ARMv7, with HMAC over
//! any hash function with a table, taken as that table (`vg_ecdsa_p192_sign`,
//! [`super::x86_64`], [`super::arm`]), public keys (`vg_ec_p192_public_key`), and
//! verification (`vg_ecdsa_p192_verify`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

#[cfg(target_arch = "arm")]
use super::arm::{SignFn as TableSignFn, TableHash, leftmost, sign_with as sign_table};
#[cfg(target_arch = "x86_64")]
use super::x86_64::{SignFn as TableSignFn, TableHash, leftmost, sign_with as sign_table};
use super::{Error, P192, SignatureHash, SigningKey, sealed};
use crate::arch::ec_p192::vg_ec_p192_public_key;
#[cfg(any(target_arch = "x86_64", target_arch = "arm"))]
use crate::arch::ecdsa_p192::vg_ecdsa_p192_sign;
use crate::arch::ecdsa_p192::vg_ecdsa_p192_verify;
#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
use crate::arch::ecdsa_p192_sha256::vg_ecdsa_p192_sha256_sign;
#[cfg(target_arch = "aarch64")]
use crate::arch::ecdsa_p192_sha256::vg_ecdsa_p192_sha256_sign_sha2;
#[cfg(target_arch = "x86")]
use crate::arch::ecdsa_p192_sha256::vg_ecdsa_p192_sha256_sign_shani;
#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
use crate::hashes::sha256::{Sha256, Sha256Backend};
use crate::zeroize::zeroize;

impl SigningKey<P192> {
    /// The public key `Q = dG`, in the uncompressed form of SEC 1 §2.3.3:
    /// `04 ‖ x ‖ y`, each coordinate 24 bytes, most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn public_key(&self) -> Result<[u8; 49], Error> {
        let mut out = [0; 49];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 49 bytes, `self.d`
        // for reads of 24 and `scratch` for reads and writes of 8192; `out`
        // and `scratch` are distinct objects from each other and `self.d`,
        // so none overlaps another or the call's stack frame, and, as Rust
        // objects, none wraps around the address space.
        let ok = unsafe { vg_ec_p192_public_key(&mut out, &self.d, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }
}

/// Whether `signature` verifies with `q` for the hash whose leftmost bits,
/// as many as the order has, are `e`.
fn verify_e(q: &[u8; 49], e: &[u8; 24], signature: &[u8; 48]) -> Result<(), Error> {
    let mut scratch = [0u64; 1024];
    // SAFETY: `q` is valid for reads of 49 bytes, the e prefix of 24,
    // `signature` of 48 and `scratch` for reads and writes of 8192;
    // `scratch` is a distinct object from the others, so it overlaps
    // neither them nor the call's stack frame, and, as Rust objects,
    // none wraps around the address space.
    let ok = unsafe { vg_ecdsa_p192_verify(q, e, signature, &mut scratch) };
    if ok == 1 {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
impl sealed::Functions<P192> for Sha256 {
    fn sign(d: &[u8; 24], digest: &[u8; 32]) -> Result<[u8; 48], Error> {
        let sign = match Sha256Backend::select(crate::cpu::detected()) {
            Sha256Backend::Scalar => vg_ecdsa_p192_sha256_sign,
            #[cfg(target_arch = "aarch64")]
            Sha256Backend::Sha2 => vg_ecdsa_p192_sha256_sign_sha2,
            #[cfg(target_arch = "x86")]
            Sha256Backend::ShaNi => vg_ecdsa_p192_sha256_sign_shani,
        };
        let mut out = [0; 48];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 48 bytes, `d` for
        // reads of 24, `digest` of 32 and `scratch` for reads and writes of
        // 8192; `out` and `scratch` are distinct objects from each other and
        // the others, so none overlaps another or the call's stack frame,
        // and, as Rust objects, none wraps around the address space. `sign`
        // needs no CPU feature that the implementation of SHA-256 selected
        // for this CPU does not.
        let ok = unsafe { sign(&mut out, d, digest, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }

    fn verify(q: &[u8; 49], digest: &[u8; 32], signature: &[u8; 48]) -> Result<(), Error> {
        verify_e(q, digest[..24].try_into().unwrap(), signature)
    }
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
impl SignatureHash<P192> for Sha256 {}

#[cfg(any(target_arch = "x86_64", target_arch = "arm"))]
impl<H: TableHash> sealed::Functions<P192> for H {
    fn sign(d: &[u8; 24], digest: &H::Output) -> Result<[u8; 48], Error> {
        let f = crate::cpu::detected();
        let sign: TableSignFn<24, 48> = vg_ecdsa_p192_sign;
        // SAFETY: `sign` needs no CPU feature.
        unsafe { sign_table::<H, 24, 48>(sign, f, d, digest) }
    }

    /// `e` is the leftmost 192 bits of the hash (FIPS 186-5 §6.4.2): its
    /// first 24 bytes, or the hash after zeros if it is shorter.
    fn verify(q: &[u8; 49], digest: &H::Output, signature: &[u8; 48]) -> Result<(), Error> {
        verify_e(q, &leftmost::<24>(digest.as_ref()), signature)
    }
}

#[cfg(any(target_arch = "x86_64", target_arch = "arm"))]
impl<H: TableHash> SignatureHash<P192> for H {}
