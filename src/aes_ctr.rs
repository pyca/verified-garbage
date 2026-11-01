//! AES-CTR (SP 800-38A §6.5) with 128-, 192- and 256-bit keys, in place,
//! with the standard incrementing function of Appendix B.1 on the whole
//! counter block (a 128-bit big-endian number, wrapping modulo `2¹²⁸`, as
//! OpenSSL's and aws-lc's AES-CTR).
//!
//! The block cipher work is verified assembly: `vg_aes_expand_key`
//! (contract `VG.Spec.Aes.expandKeyContract`) writes the key schedule, and
//! `vg_aes_ctr` (`VG.Spec.Ctr.aesContract`) XORs whole blocks with the
//! output blocks `Oⱼ = CIPH_K(Tⱼ)` from the counter block at `ctr`, which it
//! replaces with the counter block to continue from, in constant time:
//! its timing may depend on the last four bytes of the counter block (the
//! 32-bit counter, public in OpenSSL, BoringSSL and aws-lc, which split the
//! blocks where it wraps), but not on the rest of it, the key or the data.
//! This module holds the key schedule and handles a partial last block (§6.5,
//! `Cₙ* = Pₙ* ⊕ MSB_u(Oₙ)`): CTR of the last bytes padded to a block XORs
//! them with the first bytes of the next output block.
//!
//! The caller chooses the initial counter block, and must never use a
//! counter block twice with the same key (Appendix B.2).
//!
//! The variants of `vg_aes_ctr`, with the same contract, are chosen with
//! `crate::aes::Backend`, on CPUs with the features their `_FEATURES`
//! constants name (and the key expansion's): on x86-64, `vg_aes_ctr_vaes`,
//! then `vg_aes_ctr_aesni` (both with `vg_aes_expand_key_aesni`); on x86,
//! `vg_aes_ctr_aesni`; on AArch64, `vg_aes_ctr_aes`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::aes::Backend;
use crate::arch::aes::vg_aes_expand_key;
#[cfg(target_arch = "aarch64")]
use crate::arch::aes::vg_aes_expand_key_aes;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::aes::vg_aes_expand_key_aesni;
use crate::arch::aes_ctr::vg_aes_ctr;
#[cfg(target_arch = "aarch64")]
use crate::arch::aes_ctr::{VG_AES_CTR_AES_FEATURES, vg_aes_ctr_aes};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::aes_ctr::{VG_AES_CTR_AESNI_FEATURES, vg_aes_ctr_aesni};
#[cfg(target_arch = "x86_64")]
use crate::arch::aes_ctr::{VG_AES_CTR_VAES_FEATURES, vg_aes_ctr_vaes};
use crate::cpu::detected;
use crate::zeroize::zeroize;
use verified_garbage_cpu::Features;

/// The variant of a function for `backend`: the baseline one, or its
/// `_aesni`, `_vaes` or `_aes` one.
macro_rules! instance {
    ($backend:expr, $scalar:ident, $aesni:ident, $vaes:ident, $aes:ident) => {
        match $backend {
            Backend::Scalar => $scalar,
            #[cfg(target_arch = "x86_64")]
            Backend::AesNi => $aesni,
            #[cfg(target_arch = "x86_64")]
            Backend::Vaes => $vaes,
            #[cfg(target_arch = "x86")]
            Backend::AesNi => $aesni,
            #[cfg(target_arch = "aarch64")]
            Backend::Aes => $aes,
        }
    };
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its CTR function.
#[cfg(target_arch = "x86_64")]
fn select(f: Features) -> Backend {
    Backend::select_for(f, VG_AES_CTR_VAES_FEATURES, VG_AES_CTR_AESNI_FEATURES)
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its CTR function.
#[cfg(target_arch = "x86")]
fn select(f: Features) -> Backend {
    Backend::select_for(f, VG_AES_CTR_AESNI_FEATURES)
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its CTR function.
#[cfg(target_arch = "aarch64")]
fn select(f: Features) -> Backend {
    Backend::select_for(f, VG_AES_CTR_AES_FEATURES)
}

/// The only implementation of AES on ARMv7, PPC64LE and RISC-V.
#[cfg(any(
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
fn select(f: Features) -> Backend {
    Backend::select(f)
}

/// The key is not 16, 24 or 32 bytes long.
pub use crate::error::InvalidKeyLength;

/// An expanded AES key for CTR, whose encryption and decryption are the same
/// operation.
pub struct AesCtr {
    /// The key schedule `vg_aes_expand_key` writes.
    schedule: [u8; 240],
    /// The number of rounds of AES: 10, 12 or 14.
    rounds: usize,
    /// The implementation of AES the function called uses.
    backend: Backend,
}

impl AesCtr {
    /// Expands a 16-, 24- or 32-byte key.
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(InvalidKeyLength);
        }
        let backend = select(detected());
        let expand = instance!(
            backend,
            vg_aes_expand_key,
            vg_aes_expand_key_aesni,
            vg_aes_expand_key_aesni,
            vg_aes_expand_key_aes
        );
        let mut schedule = [0; 240];
        // SAFETY: the key is 16, 24 or 32 bytes long; the key and the
        // schedule are separate valid buffers of the sizes of the signature,
        // and `select` chose `expand` for the CPU's features. The function
        // zeroes its working space on its own stack before returning.
        unsafe { expand(key.as_ptr(), key.len(), &mut schedule) };
        Ok(Self {
            schedule,
            rounds: key.len() / 4 + 6,
            backend,
        })
    }

    /// Encrypts or decrypts (the same operation) `buffer` in place, from the
    /// counter block `ctr`, which it replaces with the counter block after
    /// the last one used: `ctr` plus the number of blocks (counting a partial
    /// last one), modulo `2¹²⁸` (unchanged for empty input). A message may
    /// be processed in pieces of whole blocks, each continuing from the `ctr`
    /// the last left; a piece whose length is not a multiple of 16 bytes
    /// must end the message.
    pub fn apply_keystream(&self, ctr: &mut [u8; 16], buffer: &mut [u8]) {
        let whole = buffer.len() / 16 * 16;
        let (blocks, rest) = buffer.split_at_mut(whole);
        self.crypt(ctr, blocks);
        if !rest.is_empty() {
            // The last bytes, padded to a block: CTR XORs them with the first
            // bytes of the next output block.
            let mut last = [0; 16];
            last[..rest.len()].copy_from_slice(rest);
            self.crypt(ctr, &mut last);
            rest.copy_from_slice(&last[..rest.len()]);
            zeroize(&mut last);
        }
    }

    /// CTR of whole blocks.
    fn crypt(&self, ctr: &mut [u8; 16], blocks: &mut [u8]) {
        let f = instance!(
            self.backend,
            vg_aes_ctr,
            vg_aes_ctr_aesni,
            vg_aes_ctr_vaes,
            vg_aes_ctr_aes
        );
        let mut scratch = [0; 272];
        // SAFETY: `rounds` is 10, 12 or 14 and the schedule holds its key
        // schedule; `blocks` holds `len / 16` whole blocks (its length is a
        // multiple of 16), and it, the block at `ctr`, the schedule and the
        // scratch space are separate valid objects of the sizes of the
        // signature. `select` chose `f` for the CPU's features.
        unsafe {
            f(
                &self.schedule,
                self.rounds,
                ctr,
                blocks.as_mut_ptr().cast(),
                blocks.len() / 16,
                &mut scratch,
            );
        }
        // The scratch space may hold the key schedule, the data and our
        // caller's registers.
        zeroize(&mut scratch);
    }
}

impl Drop for AesCtr {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}

#[cfg(test)]
mod tests {
    use super::{AesCtr, select};
    use crate::cpu::detected;

    /// A new key uses the implementation chosen for the CPU's features.
    #[test]
    fn select_detected() {
        for len in [16, 24, 32] {
            assert_eq!(
                AesCtr::new(&[0; 32][..len]).unwrap().backend,
                select(detected())
            );
        }
    }

    /// Each implementation is chosen for the features of its function.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64"))]
    #[test]
    fn select_features() {
        use crate::aes::Backend;
        use verified_garbage_cpu::{Features, feature};
        assert_eq!(select(Features(0)), Backend::Scalar);
        #[cfg(target_arch = "x86_64")]
        {
            assert_eq!(
                select(Features(feature::AES | feature::SSSE3)),
                Backend::AesNi
            );
            let vaes = Features(
                feature::AES | feature::AVX | feature::AVX2 | feature::SSSE3 | feature::VAES,
            );
            assert_eq!(select(vaes), Backend::Vaes);
        }
        #[cfg(target_arch = "x86")]
        assert_eq!(select(Features(feature::AES)), Backend::AesNi);
        #[cfg(target_arch = "aarch64")]
        assert_eq!(select(Features(feature::AES)), Backend::Aes);
    }
}
