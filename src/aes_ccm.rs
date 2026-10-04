//! AES-CCM (NIST SP 800-38C, with the formatting and counter generation of
//! its Appendix A, as RFC 3610) with 128-, 192- and 256-bit AES keys.
//!
//! The whole AEAD is verified assembly: `vg_aes_ccm_seal` and
//! `vg_aes_ccm_open` (contracts `VG.Spec.Ccm.sealContract` and
//! `openContract`) are generation-encryption and decryption-verification
//! (§6.1, §6.2) in one call each, from the AES key schedule that
//! `vg_aes_expand_key` writes. `open` checks the MAC in constant time and
//! overwrites the data with zeros when it is wrong. This module checks the
//! lengths of Appendix A.1, which the assembly does not, and holds the key
//! schedule.
//!
//! # Tags
//!
//! The length of the tag (the encrypted MAC) is a parameter of CCM: it is
//! part of the first block the MAC is computed over. It is a type parameter
//! here, `T` in [`AesCcm::encrypt_in_place`] and
//! [`AesCcm::decrypt_in_place`], so that it is fixed in the caller's code
//! and never comes from a message (see `crate::aes_gcm`): one of the lengths
//! Appendix A.1 allows, 4, 6, 8, 10, 12, 14 or 16 bytes, checked at compile
//! time.
//!
//! The functions are emitted once for each implementation of AES they call
//! (`vg_aes_ctr32`, directly for counter mode and through
//! `vg_cmac_aes_update` for the CBC-MAC), which have the same contracts: on
//! x86-64, CPUs with AES-NI and SSSE3 run the `_aesni` instances, and CPUs
//! with VAES and AVX2 too the `_vaes` ones (`crate::aes::Backend`). On
//! ARMv7 there is only the constant-time scalar implementation.

#![cfg(any(target_arch = "x86_64", target_arch = "arm"))]

use crate::aes::Backend;
use crate::arch::aes::vg_aes_expand_key;
#[cfg(target_arch = "x86_64")]
use crate::arch::aes::vg_aes_expand_key_aesni;
use crate::arch::aes_ccm::{vg_aes_ccm_open, vg_aes_ccm_seal};
#[cfg(target_arch = "x86_64")]
use crate::arch::aes_ccm::{
    VG_AES_CCM_OPEN_AESNI_FEATURES, VG_AES_CCM_OPEN_VAES_FEATURES, VG_AES_CCM_SEAL_AESNI_FEATURES,
    VG_AES_CCM_SEAL_VAES_FEATURES, vg_aes_ccm_open_aesni, vg_aes_ccm_open_vaes,
    vg_aes_ccm_seal_aesni, vg_aes_ccm_seal_vaes,
};
use crate::cpu::{Features, detected};
use crate::zeroize::zeroize;
use core::mem::MaybeUninit;

/// The working space of `vg_aes_ccm_seal` and `vg_aes_ccm_open`, in 64-bit
/// words: the tag in its first bytes.
const WORK: usize = 320;

/// The instance of a function for `backend`.
macro_rules! instance {
    ($backend:expr, $scalar:ident, $aesni:ident, $vaes:ident) => {
        match $backend {
            Backend::Scalar => $scalar,
            #[cfg(target_arch = "x86_64")]
            Backend::AesNi => $aesni,
            #[cfg(target_arch = "x86_64")]
            Backend::Vaes => $vaes,
        }
    };
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// the AES-CCM functions for it.
#[cfg(target_arch = "x86_64")]
fn select(f: Features) -> Backend {
    const VAES: Features =
        Features::all(&[VG_AES_CCM_SEAL_VAES_FEATURES, VG_AES_CCM_OPEN_VAES_FEATURES]);
    const AESNI: Features = Features::all(&[
        VG_AES_CCM_SEAL_AESNI_FEATURES,
        VG_AES_CCM_OPEN_AESNI_FEATURES,
    ]);
    Backend::select_for(f, VAES, AESNI)
}

/// The only implementation of AES here, with the AES-CCM functions for it.
#[cfg(target_arch = "arm")]
fn select(f: Features) -> Backend {
    Backend::select(f)
}

/// Fails to compile unless `T` is a tag length Appendix A.1 allows: 4, 6,
/// 8, 10, 12, 14 or 16 bytes.
macro_rules! assert_tag_length {
    ($t:expr) => {
        const {
            assert!(
                matches!($t, 4 | 6 | 8 | 10 | 12 | 14 | 16),
                "an AES-CCM tag is 4, 6, 8, 10, 12, 14 or 16 bytes long"
            )
        }
    };
}

/// Why an AES-CCM operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The key is not 16, 24 or 32 bytes long.
    InvalidKeyLength,
    /// The nonce is not 7 to 13 bytes long (Appendix A.1).
    InvalidNonceLength,
    /// The payload is too long for the nonce: at least `2^(8 (15 − n))`
    /// bytes for a nonce of `n` bytes (Appendix A.1).
    InvalidTextLength,
    /// The tag does not match: the ciphertext, the associated data or the
    /// nonce is not what was authenticated under this key.
    TagMismatch,
}

/// An AES-CCM key: its AES key schedule.
#[derive(Clone)]
pub struct AesCcm {
    /// The key schedule `vg_aes_expand_key` writes.
    schedule: [u8; 240],
    /// The number of rounds of AES.
    rounds: usize,
    /// The implementation of AES the functions called call.
    backend: Backend,
}

impl Drop for AesCcm {
    /// Wipes the key schedule.
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}

/// Checks the nonce's length and the payload's (Appendix A.1): a nonce of
/// `n` bytes, from 7 to 13, leaves `q = 15 − n` bytes for the payload's
/// length, which must be less than `2^(8q)`.
fn check(nonce: &[u8], len: usize) -> Result<(), Error> {
    if !(7..=13).contains(&nonce.len()) {
        return Err(Error::InvalidNonceLength);
    }
    let q = 15 - nonce.len();
    // `len < 2^(8q)`; for `q = 8` every `usize` is.
    if q < 8 && (len as u64) >> (8 * q) != 0 {
        return Err(Error::InvalidTextLength);
    }
    Ok(())
}

impl AesCcm {
    /// Prepares `key`, which must be 16, 24 or 32 bytes long.
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(Error::InvalidKeyLength);
        }
        let mut k = AesCcm {
            schedule: [0; 240],
            rounds: key.len() / 4 + 6,
            backend: select(detected()),
        };
        // `_vaes` calls `vg_aes_expand_key_aesni`'s schedule.
        let expand = instance!(
            k.backend,
            vg_aes_expand_key,
            vg_aes_expand_key_aesni,
            vg_aes_expand_key_aesni
        );
        let mut scratch = MaybeUninit::<[u64; 64]>::uninit();
        // SAFETY: `key` is valid for reads of `key.len()` bytes, which is 16,
        // 24 or 32; `k.schedule` and `scratch` are valid for reads and writes
        // of 240 and 512 bytes. They are distinct objects, so no two overlap,
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

    /// Generation-encryption (§6.1) with a tag of `T` bytes: encrypts `data`
    /// in place under `nonce` (7 to 13 bytes), and returns the tag, which
    /// authenticates the plaintext, `aad` and `nonce`. The ciphertext of
    /// §6.1 is `data` followed by the tag. A nonce must never be used twice
    /// with the same key.
    ///
    /// `T` must be 4, 6, 8, 10, 12, 14 or 16 (Appendix A.1); any other length
    /// is an error when the call is compiled.
    pub fn encrypt_in_place<const T: usize>(
        &self,
        nonce: &[u8],
        aad: &[u8],
        data: &mut [u8],
    ) -> Result<[u8; T], Error> {
        assert_tag_length!(T);
        check(nonce, data.len())?;
        let seal = instance!(
            self.backend,
            vg_aes_ccm_seal,
            vg_aes_ccm_seal_aesni,
            vg_aes_ccm_seal_vaes
        );
        let mut work = MaybeUninit::<[u64; WORK]>::uninit();
        // SAFETY: `self.schedule` is the key schedule `vg_aes_expand_key`
        // wrote for `self.rounds` (10, 12 or 14) rounds, valid for reads of
        // 240 bytes. `nonce` (7 to 13 bytes) and `aad` are valid for reads
        // of their lengths, `data` for reads and writes of `data.len()`
        // bytes, which `check` has checked is less than `2^(8 (15 −
        // nonce.len()))`, and `work` for reads and writes of 2560. `T` is a
        // length Appendix A.1 allows (`assert_tag_length`). `data` and
        // `work` are unique borrows, so they overlap neither each other nor
        // the other buffers; no buffer overlaps the arguments on the stack,
        // the return address or the stack below it, and none wraps around
        // the end of the address space. The CPU has the features of the
        // implementation selected. `work` is uninitialized: it is only
        // working space but for the tag written to its first `T` bytes.
        unsafe {
            seal(
                &self.schedule,
                self.rounds,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
                work.as_mut_ptr(),
                T,
            )
        };
        // SAFETY: `seal` wrote the tag to the first `T` (at most 16) bytes
        // of `work`, and so the first 16 bytes.
        let b = unsafe { first_block(&work) };
        let mut tag = [0u8; T];
        tag.copy_from_slice(&b[..T]);
        Ok(tag)
    }

    /// Decryption-verification (§6.2) with a tag of `T` bytes: if `tag`
    /// authenticates the ciphertext in `data`, `aad` and `nonce`, decrypts
    /// `data` in place. Otherwise returns an error and overwrites `data`
    /// with zeros.
    ///
    /// `T` must be 4, 6, 8, 10, 12, 14 or 16 (Appendix A.1); any other length
    /// is an error when the call is compiled.
    pub fn decrypt_in_place<const T: usize>(
        &self,
        nonce: &[u8],
        aad: &[u8],
        data: &mut [u8],
        tag: &[u8; T],
    ) -> Result<(), Error> {
        assert_tag_length!(T);
        check(nonce, data.len())?;
        let open = instance!(
            self.backend,
            vg_aes_ccm_open,
            vg_aes_ccm_open_aesni,
            vg_aes_ccm_open_vaes
        );
        let mut work = MaybeUninit::<[u64; WORK]>::uninit();
        let mut t = [0u8; 16];
        t[..T].copy_from_slice(tag);
        let w = work.as_mut_ptr().cast::<u64>();
        // SAFETY: `work` is valid for writes of 320 words.
        unsafe {
            w.write(u64::from_le_bytes(t[..8].try_into().unwrap()));
            w.add(1)
                .write(u64::from_le_bytes(t[8..].try_into().unwrap()));
        }
        // SAFETY: as in `encrypt_in_place`, with the received tag in the
        // first `T` bytes of `work`.
        let ok = unsafe {
            open(
                &self.schedule,
                self.rounds,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
                work.as_mut_ptr(),
                T,
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

/// The first 16 bytes of `work`, where `seal` writes the tag.
///
/// # Safety
///
/// They must have been written.
unsafe fn first_block(work: &MaybeUninit<[u64; WORK]>) -> [u8; 16] {
    let w = work.as_ptr().cast::<u64>();
    let mut b = [0u8; 16];
    // SAFETY: the first two words are initialized (the caller's guarantee).
    unsafe {
        b[..8].copy_from_slice(&w.read().to_le_bytes());
        b[8..].copy_from_slice(&w.add(1).read().to_le_bytes());
    }
    b
}

#[cfg(test)]
mod tests {
    use super::{AesCcm, Error};

    #[test]
    fn key_lengths() {
        let key = [0u8; 40];
        for n in [0, 15, 17, 23, 25, 31, 33, 40] {
            assert_eq!(AesCcm::new(&key[..n]).err(), Some(Error::InvalidKeyLength));
        }
    }

    #[test]
    fn text_lengths() {
        let k = AesCcm::new(&[0; 16]).unwrap();
        // A 13-byte nonce leaves 2 bytes for the length: at most 65535.
        let mut data = [1u8; 1 << 16];
        assert_eq!(
            k.encrypt_in_place::<16>(&[0; 13], &[], &mut data),
            Err(Error::InvalidTextLength)
        );
        assert_eq!(
            k.decrypt_in_place(&[0; 13], &[], &mut data, &[0; 16]),
            Err(Error::InvalidTextLength)
        );
        assert!(data.iter().all(|&b| b == 1));
        let data = &mut data[..(1 << 16) - 1];
        let tag = k.encrypt_in_place::<16>(&[0; 13], &[], data).unwrap();
        k.decrypt_in_place(&[0; 13], &[], data, &tag).unwrap();
        assert!(data.iter().all(|&b| b == 1));
    }
}
