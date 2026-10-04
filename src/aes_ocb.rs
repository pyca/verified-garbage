//! AES-OCB (OCB3, RFC 7253) with 128-, 192- and 256-bit AES keys.
//!
//! The whole AEAD is verified assembly: `vg_aes_ocb_init` (contract
//! `VG.Spec.Ocb.initContract`) writes the key context (the key schedule and
//! `L_*`), and `vg_aes_ocb_seal` and `vg_aes_ocb_open` (`sealContract`,
//! `openContract`) are `OCB-ENCRYPT` and `OCB-DECRYPT` (§4.2, §4.3) in one
//! call each, HASH of the associated data included, in constant time. `open`
//! checks the tag in constant time and overwrites the data with zeros when it
//! is wrong. This module checks the nonce's length, which the assembly does
//! not, and holds the key context.
//!
//! # Tags
//!
//! The length of the tag is a parameter of OCB: it is part of the nonce's
//! first block (§4.2). It is a type parameter here, `T` in
//! [`AesOcb::encrypt_in_place`] and [`AesOcb::decrypt_in_place`], so that it
//! is fixed in the caller's code and never comes from a message (see
//! `crate::aes_gcm`): 1 to 16 bytes, checked at compile time. §3.1 defines
//! the AEADs with tags of 16, 12 and 8 bytes.
//!
//! The functions are emitted once for each implementation of AES they call
//! (`vg_aes_expand_key`, `vg_aes_encrypt_blocks` and
//! `vg_aes_decrypt_blocks`), which have the same contracts: on x86-64, CPUs
//! with AES-NI and SSSE3 run the `_aesni` instances (`crate::aes::Backend`;
//! there is no VAES implementation of whole blocks yet, so its CPUs run them
//! too); on AArch64, CPUs with the AES instructions run the `_aes` ones.
//! x86-64 and AArch64 have implementations so far.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use crate::aes::Backend;
use crate::arch::aes_ocb::{vg_aes_ocb_init, vg_aes_ocb_open, vg_aes_ocb_seal};
#[cfg(target_arch = "aarch64")]
use crate::arch::aes_ocb::{
    VG_AES_OCB_INIT_AES_FEATURES, VG_AES_OCB_OPEN_AES_FEATURES, VG_AES_OCB_SEAL_AES_FEATURES,
    vg_aes_ocb_init_aes, vg_aes_ocb_open_aes, vg_aes_ocb_seal_aes,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::aes_ocb::{
    VG_AES_OCB_INIT_AESNI_FEATURES, VG_AES_OCB_OPEN_AESNI_FEATURES, VG_AES_OCB_SEAL_AESNI_FEATURES,
    vg_aes_ocb_init_aesni, vg_aes_ocb_open_aesni, vg_aes_ocb_seal_aesni,
};
use crate::cpu::{Features, detected};
use crate::zeroize::zeroize;
use core::mem::MaybeUninit;

/// The working space of the functions, in 64-bit words: for `seal` and
/// `open`, the tag in its first bytes.
const WORK: usize = 320;

/// The instance of a function for `backend`: the scalar one, x86-64's for
/// AES-NI, or AArch64's for the AES instructions.
macro_rules! instance {
    ($backend:expr, $scalar:ident, $aesni:ident, $aes:ident) => {
        match $backend {
            Backend::Scalar => $scalar,
            // No VAES implementation of whole blocks yet.
            #[cfg(target_arch = "x86_64")]
            Backend::AesNi | Backend::Vaes => $aesni,
            #[cfg(target_arch = "aarch64")]
            Backend::Aes => $aes,
        }
    };
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// the AES-OCB functions for it.
#[cfg(target_arch = "x86_64")]
fn select(f: Features) -> Backend {
    const AESNI: Features = Features::all(&[
        VG_AES_OCB_INIT_AESNI_FEATURES,
        VG_AES_OCB_SEAL_AESNI_FEATURES,
        VG_AES_OCB_OPEN_AESNI_FEATURES,
    ]);
    Backend::select_for(f, AESNI, AESNI)
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// the AES-OCB functions for it.
#[cfg(target_arch = "aarch64")]
fn select(f: Features) -> Backend {
    const AES: Features = Features::all(&[
        VG_AES_OCB_INIT_AES_FEATURES,
        VG_AES_OCB_SEAL_AES_FEATURES,
        VG_AES_OCB_OPEN_AES_FEATURES,
    ]);
    Backend::select_for(f, AES)
}

/// Fails to compile unless `T` is a tag length OCB allows: 1 to 16 bytes.
macro_rules! assert_tag_length {
    ($t:expr) => {
        const { assert!(matches!($t, 1..=16), "an AES-OCB tag is 1 to 16 bytes long") }
    };
}

/// Why an AES-OCB operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The key is not 16, 24 or 32 bytes long.
    InvalidKeyLength,
    /// The nonce is not 1 to 15 bytes long (§4.2: at most 120 bits).
    InvalidNonceLength,
    /// The tag does not match: the ciphertext, the associated data or the
    /// nonce is not what was authenticated under this key.
    TagMismatch,
}

/// An AES-OCB key: its key context.
#[derive(Clone)]
pub struct AesOcb {
    /// The key context `vg_aes_ocb_init` writes: the key schedule, and `L_*`
    /// in bytes 240–255.
    ctx: [u64; 32],
    /// The number of rounds of AES.
    rounds: usize,
    /// The implementation of AES the functions called call.
    backend: Backend,
}

impl Drop for AesOcb {
    /// Wipes the key context.
    fn drop(&mut self) {
        zeroize(&mut self.ctx);
    }
}

/// Checks the nonce's length: 1 to 15 bytes.
fn check(nonce: &[u8]) -> Result<(), Error> {
    if (1..=15).contains(&nonce.len()) {
        Ok(())
    } else {
        Err(Error::InvalidNonceLength)
    }
}

impl AesOcb {
    /// Prepares `key`, which must be 16, 24 or 32 bytes long.
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(Error::InvalidKeyLength);
        }
        let mut k = AesOcb {
            ctx: [0; 32],
            rounds: key.len() / 4 + 6,
            backend: select(detected()),
        };
        let init = instance!(k.backend, vg_aes_ocb_init, vg_aes_ocb_init_aesni, vg_aes_ocb_init_aes);
        let mut scratch = MaybeUninit::<[u64; WORK]>::uninit();
        // SAFETY: `key` is valid for reads of `key.len()` bytes, which is 16,
        // 24 or 32; `k.ctx` and `scratch` are valid for reads and writes of
        // 256 and 2560 bytes. They are distinct objects, so no two overlap,
        // nor do they overlap the return address on the stack or the stack
        // below it, and none wraps around the end of the address space. The
        // CPU has the features of the implementation selected. `scratch` is
        // uninitialized: it is only working space.
        unsafe { init(key.as_ptr(), key.len(), &mut k.ctx, scratch.as_mut_ptr()) };
        Ok(k)
    }

    /// `OCB-ENCRYPT` (§4.2) with a tag of `T` bytes: encrypts `data` in
    /// place under `nonce` (1 to 15 bytes), and returns the tag, which
    /// authenticates the plaintext, `aad` and `nonce`. The ciphertext of
    /// §4.2 is `data` followed by the tag. A nonce must never be used twice
    /// with the same key.
    ///
    /// `T` must be 1 to 16; any other length is an error when the call is
    /// compiled.
    pub fn encrypt_in_place<const T: usize>(
        &self,
        nonce: &[u8],
        aad: &[u8],
        data: &mut [u8],
    ) -> Result<[u8; T], Error> {
        assert_tag_length!(T);
        check(nonce)?;
        let seal = instance!(self.backend, vg_aes_ocb_seal, vg_aes_ocb_seal_aesni, vg_aes_ocb_seal_aes);
        let mut work = MaybeUninit::<[u64; WORK]>::uninit();
        // SAFETY: `self.ctx` is the key context `vg_aes_ocb_init` wrote for
        // `self.rounds` (10, 12 or 14) rounds, valid for reads of 256 bytes.
        // `nonce` (1 to 15 bytes, `check`) and `aad` are valid for reads of
        // their lengths, `data` for reads and writes of `data.len()` bytes,
        // and `work` for reads and writes of 2560. `T` is 1 to 16
        // (`assert_tag_length`). `data` and `work` are unique borrows, so
        // they overlap neither each other nor the other buffers; no buffer
        // overlaps the arguments on the stack, the return address or the
        // stack below it, and none wraps around the end of the address
        // space. The CPU has the features of the implementation selected.
        // `work` is uninitialized: it is only working space but for the tag
        // written to its first `T` bytes.
        unsafe {
            seal(
                &self.ctx,
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

    /// `OCB-DECRYPT` (§4.3) with a tag of `T` bytes: if `tag` authenticates
    /// the ciphertext in `data`, `aad` and `nonce`, decrypts `data` in place.
    /// Otherwise returns an error and overwrites `data` with zeros.
    ///
    /// `T` must be 1 to 16; any other length is an error when the call is
    /// compiled.
    pub fn decrypt_in_place<const T: usize>(
        &self,
        nonce: &[u8],
        aad: &[u8],
        data: &mut [u8],
        tag: &[u8; T],
    ) -> Result<(), Error> {
        assert_tag_length!(T);
        check(nonce)?;
        let open = instance!(self.backend, vg_aes_ocb_open, vg_aes_ocb_open_aesni, vg_aes_ocb_open_aes);
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
                &self.ctx,
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
    use super::{AesOcb, Error};

    #[test]
    fn key_lengths() {
        let key = [0u8; 40];
        for n in [0, 15, 17, 23, 25, 31, 33, 40] {
            assert_eq!(AesOcb::new(&key[..n]).err(), Some(Error::InvalidKeyLength));
        }
    }

    #[test]
    fn nonce_lengths() {
        let k = AesOcb::new(&[0; 16]).unwrap();
        let mut data = [1u8; 20];
        for n in [0, 16, 17] {
            let nonce = [0u8; 17];
            assert_eq!(
                k.encrypt_in_place::<16>(&nonce[..n], &[], &mut data),
                Err(Error::InvalidNonceLength)
            );
            assert_eq!(
                k.decrypt_in_place(&nonce[..n], &[], &mut data, &[0; 16]),
                Err(Error::InvalidNonceLength)
            );
        }
        assert!(data.iter().all(|&b| b == 1));
        for n in [1, 15] {
            let nonce = [7u8; 15];
            let tag = k
                .encrypt_in_place::<1>(&nonce[..n], &[2], &mut data)
                .unwrap();
            k.decrypt_in_place(&nonce[..n], &[2], &mut data, &tag)
                .unwrap();
            assert!(data.iter().all(|&b| b == 1));
        }
    }
}
