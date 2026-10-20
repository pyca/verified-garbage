//! ECDSA over brainpoolP512r1: deterministic signatures with HMAC-SHA-512
//! (`vg_ecdsa_brainpoolp512r1_sha512_sign`, which calls `vg_ecdsa_brainpoolp512r1_sign`), public
//! keys (`vg_ec_brainpoolp512r1_public_key`), and verification (`vg_ecdsa_brainpoolp512r1_verify`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

use super::{BrainpoolP512r1, Error, SignatureHash, SigningKey, sealed};
use crate::arch::ec_brainpoolp512r1::vg_ec_brainpoolp512r1_public_key;
use crate::arch::ecdsa_brainpoolp512r1::vg_ecdsa_brainpoolp512r1_verify;
use crate::arch::ecdsa_brainpoolp512r1_sha512::vg_ecdsa_brainpoolp512r1_sha512_sign;
#[cfg(target_arch = "aarch64")]
use crate::arch::ecdsa_brainpoolp512r1_sha512::vg_ecdsa_brainpoolp512r1_sha512_sign_sha3;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_brainpoolp512r1_sha512::{
    vg_ecdsa_brainpoolp512r1_sha512_sign_avx2, vg_ecdsa_brainpoolp512r1_sha512_sign_shani,
};
use crate::hashes::sha512::{Sha512, Sha512Backend};
use crate::zeroize::zeroize;

impl SigningKey<BrainpoolP512r1> {
    /// The public key `Q = dG`, in the uncompressed form of SEC 1 §2.3.3:
    /// `04 ‖ x ‖ y`, each coordinate 64 bytes, most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn public_key(&self) -> Result<[u8; 129], Error> {
        let mut out = [0; 129];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 129 bytes, `self.d`
        // for reads of 64 and `scratch` for reads and writes of 8192; `out`
        // and `scratch` are distinct objects from each other and `self.d`,
        // so none overlaps another or the call's stack frame, and, as Rust
        // objects, none wraps around the address space.
        let ok = unsafe { vg_ec_brainpoolp512r1_public_key(&mut out, &self.d, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }
}

impl sealed::Functions<BrainpoolP512r1> for Sha512 {
    fn sign(d: &[u8; 64], digest: &[u8; 64]) -> Result<[u8; 128], Error> {
        let sign = match Sha512Backend::select(crate::cpu::detected()) {
            Sha512Backend::Scalar => vg_ecdsa_brainpoolp512r1_sha512_sign,
            #[cfg(target_arch = "aarch64")]
            Sha512Backend::Sha3 => vg_ecdsa_brainpoolp512r1_sha512_sign_sha3,
            #[cfg(target_arch = "x86_64")]
            Sha512Backend::ShaNi => vg_ecdsa_brainpoolp512r1_sha512_sign_shani,
            #[cfg(target_arch = "x86_64")]
            Sha512Backend::Avx2 => vg_ecdsa_brainpoolp512r1_sha512_sign_avx2,
        };
        let mut out = [0; 128];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 128 bytes, `d` and
        // `digest` for reads of 64 and `scratch` for reads and writes of
        // 8192; `out` and `scratch` are distinct objects from each other and
        // the others, so none overlaps another or the call's stack frame,
        // and, as Rust objects, none wraps around the address space. `sign`
        // needs no CPU feature that the implementation of SHA-512 selected
        // for this CPU does not.
        let ok = unsafe { sign(&mut out, d, digest, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }

    fn verify(q: &[u8; 129], digest: &[u8; 64], signature: &[u8; 128]) -> Result<(), Error> {
        let mut scratch = [0u64; 1024];
        // SAFETY: `q` is valid for reads of 129 bytes, `digest` of 64,
        // `signature` of 128 and `scratch` for reads and writes of 8192;
        // `scratch` is a distinct object from the others, so it overlaps
        // neither them nor the call's stack frame, and, as Rust objects,
        // none wraps around the address space.
        let ok = unsafe { vg_ecdsa_brainpoolp512r1_verify(q, digest, signature, &mut scratch) };
        if ok == 1 {
            Ok(())
        } else {
            Err(Error::InvalidSignature)
        }
    }
}

impl SignatureHash<BrainpoolP512r1> for Sha512 {}
