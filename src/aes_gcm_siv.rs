//! AES-GCM-SIV (RFC 8452) with 128- and 256-bit keys: nonce-misuse-resistant
//! authenticated encryption.
//!
//! The whole AEAD is verified assembly: `vg_aes_gcm_siv_seal` and
//! `vg_aes_gcm_siv_open` (contracts `VG.Spec.GcmSiv.sealContract` and
//! `openContract`) are encryption and decryption (§4, §5) in one call each,
//! the per-nonce key derivation included, from the AES key schedule of the
//! key-generating key that `vg_aes_expand_key` writes. `open` checks the tag
//! in constant time and overwrites the data with zeros when it is wrong.
//! This module checks the lengths of §6, which the assembly does not, and
//! holds the key schedule.
//!
//! The functions are emitted once for each combination of the
//! implementations of AES (`vg_aes_ctr32`, `vg_aes_expand_key`) and of GHASH
//! (`vg_ghash`, with which POLYVAL is computed) that AES-GCM has, and are
//! chosen as AES-GCM's are (`crate::aes_gcm`'s backends). x86-64, x86,
//! AArch64 and 32-bit ARM (the baseline ISA's implementations alone) have
//! implementations so far.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

use crate::aes_gcm::{Backend, instance, select};
use crate::arch::aes::vg_aes_expand_key;
#[cfg(target_arch = "aarch64")]
use crate::arch::aes::vg_aes_expand_key_aes;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::aes::vg_aes_expand_key_aesni;
use crate::arch::aes_gcm_siv::{vg_aes_gcm_siv_open, vg_aes_gcm_siv_seal};
#[cfg(target_arch = "aarch64")]
use crate::arch::aes_gcm_siv::{vg_aes_gcm_siv_open_aes, vg_aes_gcm_siv_seal_aes};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::aes_gcm_siv::{
    vg_aes_gcm_siv_open_aesni, vg_aes_gcm_siv_open_aesni_pclmul, vg_aes_gcm_siv_open_pclmul,
    vg_aes_gcm_siv_seal_aesni, vg_aes_gcm_siv_seal_aesni_pclmul, vg_aes_gcm_siv_seal_pclmul,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::aes_gcm_siv::{
    vg_aes_gcm_siv_open_aesni_pclmul_avx, vg_aes_gcm_siv_open_aesni_vpclmul,
    vg_aes_gcm_siv_open_vaes, vg_aes_gcm_siv_open_vaes_pclmul, vg_aes_gcm_siv_open_vaes_vpclmul,
    vg_aes_gcm_siv_open_vaes_vpclmul_avx512, vg_aes_gcm_siv_open_vpclmul,
    vg_aes_gcm_siv_seal_aesni_pclmul_avx, vg_aes_gcm_siv_seal_aesni_vpclmul,
    vg_aes_gcm_siv_seal_vaes, vg_aes_gcm_siv_seal_vaes_pclmul, vg_aes_gcm_siv_seal_vaes_vpclmul,
    vg_aes_gcm_siv_seal_vaes_vpclmul_avx512, vg_aes_gcm_siv_seal_vpclmul,
};
use crate::cpu::detected;
use crate::zeroize::zeroize;
use core::mem::MaybeUninit;

/// The longest plaintext and additional data, in bytes (§6: `P_MAX` and
/// `A_MAX`, `2^36`).
const MAX_LEN: u64 = 1 << 36;

/// Why an AES-GCM-SIV operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The key is not 16 or 32 bytes long.
    InvalidKeyLength,
    /// The plaintext or ciphertext is longer than `2^36` bytes (§6).
    InvalidTextLength,
    /// The additional data is longer than `2^36` bytes (§6).
    InvalidAadLength,
    /// The tag does not match: the ciphertext, the additional data or the
    /// nonce is not what was authenticated under this key.
    TagMismatch,
}

/// An AES-GCM-SIV key: the AES key schedule of the key-generating key.
#[derive(Clone)]
pub struct AesGcmSiv {
    /// The key schedule `vg_aes_expand_key` writes.
    schedule: [u8; 240],
    /// The number of rounds of AES: 10 or 14.
    rounds: usize,
    /// The implementations of AES and GHASH the functions called call.
    backend: Backend,
}

impl Drop for AesGcmSiv {
    /// Wipes the key schedule.
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}

/// Checks the lengths of §6: of the additional data and of the text.
fn check(aad_len: u64, len: u64) -> Result<(), Error> {
    if len > MAX_LEN {
        return Err(Error::InvalidTextLength);
    }
    if aad_len > MAX_LEN {
        return Err(Error::InvalidAadLength);
    }
    Ok(())
}

impl AesGcmSiv {
    /// Prepares the key-generating key `key`, which must be 16 or 32 bytes
    /// long (AEAD_AES_128_GCM_SIV, AEAD_AES_256_GCM_SIV).
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        if !matches!(key.len(), 16 | 32) {
            return Err(Error::InvalidKeyLength);
        }
        let mut k = AesGcmSiv {
            schedule: [0; 240],
            rounds: key.len() / 4 + 6,
            backend: select(detected()),
        };
        // The instances with AES-NI or VAES call `vg_aes_expand_key_aesni`,
        // those with the AArch64 AES instructions `vg_aes_expand_key_aes`.
        let expand = instance!(k.backend, vg_aes_expand_key,
            x86_64: [vg_aes_expand_key_aesni, vg_aes_expand_key, vg_aes_expand_key_aesni],
            vaes: [vg_aes_expand_key_aesni, vg_aes_expand_key, vg_aes_expand_key_aesni,
                vg_aes_expand_key_aesni, vg_aes_expand_key_aesni, vg_aes_expand_key_aesni],
            avx: [vg_aes_expand_key_aesni],
            aarch64: [vg_aes_expand_key_aes]);
        let mut scratch = MaybeUninit::<[u64; 64]>::uninit();
        // SAFETY: `key` is valid for reads of `key.len()` bytes, which is 16
        // or 32; `k.schedule` and `scratch` are valid for reads and writes of
        // 240 and 512 bytes. They are distinct objects, so no two overlap,
        // nor do they overlap the return address on the stack or the stack
        // below it, and none wraps around the end of the address space. The
        // CPU has the features of the implementation selected. `scratch` is
        // uninitialized: it is only working space.
        unsafe {
            expand(
                key.as_ptr(),
                key.len(),
                &mut k.schedule,
                scratch.as_mut_ptr(),
            )
        };
        Ok(k)
    }

    /// Encryption (§4): encrypts `data` in place under the 12-byte `nonce`,
    /// and returns the 16-byte tag, which authenticates the plaintext and
    /// `aad`. The RFC's ciphertext is `data` followed by the tag. Reusing a
    /// nonce with the same key reveals only whether two messages (with
    /// their additional data) are equal.
    pub fn encrypt_in_place(
        &self,
        nonce: &[u8; 12],
        aad: &[u8],
        data: &mut [u8],
    ) -> Result<[u8; 16], Error> {
        check(aad.len() as u64, data.len() as u64)?;
        let seal = instance!(self.backend, vg_aes_gcm_siv_seal,
            x86_64: [vg_aes_gcm_siv_seal_aesni, vg_aes_gcm_siv_seal_pclmul, vg_aes_gcm_siv_seal_aesni_pclmul],
            vaes: [vg_aes_gcm_siv_seal_vaes, vg_aes_gcm_siv_seal_vpclmul, vg_aes_gcm_siv_seal_vaes_pclmul,
                vg_aes_gcm_siv_seal_aesni_vpclmul, vg_aes_gcm_siv_seal_vaes_vpclmul,
                vg_aes_gcm_siv_seal_vaes_vpclmul_avx512],
            avx: [vg_aes_gcm_siv_seal_aesni_pclmul_avx],
            aarch64: [vg_aes_gcm_siv_seal_aes]);
        let mut tag = [0u8; 16];
        // SAFETY: `self.schedule` is the key schedule `vg_aes_expand_key`
        // wrote for `self.rounds` (10 or 14) rounds, valid for reads of 240
        // bytes. `nonce` (12 bytes) and `aad` are valid for reads of their
        // lengths, `data` for reads and writes of `data.len()` bytes, and
        // `tag` for reads and writes of 16. `data` and `tag` are unique
        // borrows, so they overlap neither each other nor the other buffers;
        // no buffer overlaps the arguments on the stack, the return address
        // or the stack below it, and none wraps around the end of the address
        // space. The CPU has the features of the implementation selected
        // (see `features_cover_instances`).
        unsafe {
            seal(
                &self.schedule,
                self.rounds,
                nonce,
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
                &mut tag,
            )
        };
        Ok(tag)
    }

    /// Decryption (§5): if `tag` authenticates the ciphertext in `data`,
    /// `aad` and `nonce`, decrypts `data` in place. Otherwise returns an
    /// error and overwrites `data` with zeros.
    pub fn decrypt_in_place(
        &self,
        nonce: &[u8; 12],
        aad: &[u8],
        data: &mut [u8],
        tag: &[u8; 16],
    ) -> Result<(), Error> {
        check(aad.len() as u64, data.len() as u64)?;
        let open = instance!(self.backend, vg_aes_gcm_siv_open,
            x86_64: [vg_aes_gcm_siv_open_aesni, vg_aes_gcm_siv_open_pclmul, vg_aes_gcm_siv_open_aesni_pclmul],
            vaes: [vg_aes_gcm_siv_open_vaes, vg_aes_gcm_siv_open_vpclmul, vg_aes_gcm_siv_open_vaes_pclmul,
                vg_aes_gcm_siv_open_aesni_vpclmul, vg_aes_gcm_siv_open_vaes_vpclmul,
                vg_aes_gcm_siv_open_vaes_vpclmul_avx512],
            avx: [vg_aes_gcm_siv_open_aesni_pclmul_avx],
            aarch64: [vg_aes_gcm_siv_open_aes]);
        // SAFETY: as in `encrypt_in_place`, with the received tag `tag`
        // valid for reads of 16 bytes, which `data`, a unique borrow, does not
        // overlap.
        let ok = unsafe {
            open(
                &self.schedule,
                self.rounds,
                nonce,
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
                tag,
            )
        };
        // `open`'s contract leaves the plaintext in `data` if it returns 1,
        // and zeros otherwise.
        if ok == 1 {
            Ok(())
        } else {
            Err(Error::TagMismatch)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{AesGcmSiv, Error, MAX_LEN, check};
    use crate::aes_gcm::{Backend, instance};
    #[cfg(target_arch = "aarch64")]
    use crate::arch::aes_gcm_siv::{
        VG_AES_GCM_SIV_OPEN_AES_FEATURES, VG_AES_GCM_SIV_SEAL_AES_FEATURES,
    };
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    use crate::arch::aes_gcm_siv::{
        VG_AES_GCM_SIV_OPEN_AESNI_FEATURES, VG_AES_GCM_SIV_OPEN_AESNI_PCLMUL_FEATURES,
        VG_AES_GCM_SIV_OPEN_PCLMUL_FEATURES, VG_AES_GCM_SIV_SEAL_AESNI_FEATURES,
        VG_AES_GCM_SIV_SEAL_AESNI_PCLMUL_FEATURES, VG_AES_GCM_SIV_SEAL_PCLMUL_FEATURES,
    };
    #[cfg(target_arch = "x86_64")]
    use crate::arch::aes_gcm_siv::{
        VG_AES_GCM_SIV_OPEN_AESNI_PCLMUL_AVX_FEATURES, VG_AES_GCM_SIV_OPEN_AESNI_VPCLMUL_FEATURES,
        VG_AES_GCM_SIV_OPEN_VAES_FEATURES, VG_AES_GCM_SIV_OPEN_VAES_PCLMUL_FEATURES,
        VG_AES_GCM_SIV_OPEN_VAES_VPCLMUL_AVX512_FEATURES,
        VG_AES_GCM_SIV_OPEN_VAES_VPCLMUL_FEATURES, VG_AES_GCM_SIV_OPEN_VPCLMUL_FEATURES,
        VG_AES_GCM_SIV_SEAL_AESNI_PCLMUL_AVX_FEATURES, VG_AES_GCM_SIV_SEAL_AESNI_VPCLMUL_FEATURES,
        VG_AES_GCM_SIV_SEAL_VAES_FEATURES, VG_AES_GCM_SIV_SEAL_VAES_PCLMUL_FEATURES,
        VG_AES_GCM_SIV_SEAL_VAES_VPCLMUL_AVX512_FEATURES,
        VG_AES_GCM_SIV_SEAL_VAES_VPCLMUL_FEATURES, VG_AES_GCM_SIV_SEAL_VPCLMUL_FEATURES,
    };
    use crate::cpu::Features;

    /// The features of every instance of a backend are within those it is
    /// selected by (AES-GCM's `seal`'s).
    #[test]
    fn features_cover_instances() {
        const NONE: Features = Features(0);
        for &(b, need) in Backend::ALL {
            let seal = instance!(b, NONE,
                x86_64: [VG_AES_GCM_SIV_SEAL_AESNI_FEATURES, VG_AES_GCM_SIV_SEAL_PCLMUL_FEATURES, VG_AES_GCM_SIV_SEAL_AESNI_PCLMUL_FEATURES],
                vaes: [VG_AES_GCM_SIV_SEAL_VAES_FEATURES, VG_AES_GCM_SIV_SEAL_VPCLMUL_FEATURES, VG_AES_GCM_SIV_SEAL_VAES_PCLMUL_FEATURES,
                    VG_AES_GCM_SIV_SEAL_AESNI_VPCLMUL_FEATURES, VG_AES_GCM_SIV_SEAL_VAES_VPCLMUL_FEATURES,
                    VG_AES_GCM_SIV_SEAL_VAES_VPCLMUL_AVX512_FEATURES],
                avx: [VG_AES_GCM_SIV_SEAL_AESNI_PCLMUL_AVX_FEATURES],
                aarch64: [VG_AES_GCM_SIV_SEAL_AES_FEATURES]);
            let open = instance!(b, NONE,
                x86_64: [VG_AES_GCM_SIV_OPEN_AESNI_FEATURES, VG_AES_GCM_SIV_OPEN_PCLMUL_FEATURES, VG_AES_GCM_SIV_OPEN_AESNI_PCLMUL_FEATURES],
                vaes: [VG_AES_GCM_SIV_OPEN_VAES_FEATURES, VG_AES_GCM_SIV_OPEN_VPCLMUL_FEATURES, VG_AES_GCM_SIV_OPEN_VAES_PCLMUL_FEATURES,
                    VG_AES_GCM_SIV_OPEN_AESNI_VPCLMUL_FEATURES, VG_AES_GCM_SIV_OPEN_VAES_VPCLMUL_FEATURES,
                    VG_AES_GCM_SIV_OPEN_VAES_VPCLMUL_AVX512_FEATURES],
                avx: [VG_AES_GCM_SIV_OPEN_AESNI_PCLMUL_AVX_FEATURES],
                aarch64: [VG_AES_GCM_SIV_OPEN_AES_FEATURES]);
            assert!(need.contains(seal) && need.contains(open), "{b:?}");
        }
    }

    /// The lengths of §6, which no test can allocate.
    #[test]
    fn lengths() {
        assert_eq!(check(MAX_LEN, MAX_LEN), Ok(()));
        assert_eq!(check(0, MAX_LEN + 1), Err(Error::InvalidTextLength));
        assert_eq!(check(MAX_LEN + 1, 0), Err(Error::InvalidAadLength));
    }

    #[test]
    fn errors() {
        let key = [0u8; 40];
        for n in [0, 15, 17, 24, 31, 33, 40] {
            assert_eq!(
                AesGcmSiv::new(&key[..n]).err(),
                Some(Error::InvalidKeyLength)
            );
        }
    }
}
