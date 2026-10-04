//! AES-SIV (RFC 5297) with 256-, 384- and 512-bit keys (AES-128, AES-192
//! and AES-256 for each half): deterministic authenticated encryption, and
//! nonce-based when the caller passes a nonce as the last associated-data
//! component (RFC 5297 §3).
//!
//! The whole AEAD is verified assembly: `vg_aes_siv_init` (contract
//! `VG.Spec.Siv.initContract`) writes the key context (the key schedule of
//! `K1` and its CMAC subkeys, and the key schedule of `K2`), and
//! `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt` (`encryptContract`,
//! `decryptContract`) are `SIV-ENCRYPT` and `SIV-DECRYPT` in one call each,
//! S2V over the associated-data components included, in constant time.
//! `decrypt` overwrites the data with zeros when the synthetic IV is wrong.
//! This module checks the number of components (RFC 5297 §2.6 allows at most
//! 126 besides the plaintext), which the assembly does not count, lists them
//! for the assembly as `[address, length]` pairs, and holds the key context.
//!
//! The functions are emitted once for each implementation of AES they call
//! (`vg_aes_expand_key` and `vg_aes_ctr32`, through the CMAC functions made
//! with them, and directly for CTR), which have the same contracts: on
//! x86-64, CPUs with AES-NI and SSSE3 run the `_aesni` instances, and CPUs
//! with VAES and AVX2 too the `_vaes` ones (`crate::aes::Backend`). On
//! AArch64, CPUs with the AES extension run `vg_aes_siv_init_aes`, and
//! `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt` follow the implementations
//! of `vg_cmac_aes_update` too, as AES-CMAC does (`crate::cmac::aes`): when
//! the associated-data components and the data total more than 32 bytes,
//! the `_aes_cbc` instances, whose CMAC chains whole blocks with the round
//! keys and the chaining value kept in vector registers, and otherwise the
//! `_aes` ones (`chains_long`). On ARMv7 there is one implementation of
//! AES, and so one instance of each function.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use crate::aes::Backend;
#[cfg(target_arch = "aarch64")]
use crate::arch::aes_siv::{
    VG_AES_SIV_DECRYPT_AES_CBC_FEATURES, VG_AES_SIV_DECRYPT_AES_FEATURES,
    VG_AES_SIV_ENCRYPT_AES_CBC_FEATURES, VG_AES_SIV_ENCRYPT_AES_FEATURES,
    VG_AES_SIV_INIT_AES_FEATURES, vg_aes_siv_decrypt_aes, vg_aes_siv_decrypt_aes_cbc,
    vg_aes_siv_encrypt_aes, vg_aes_siv_encrypt_aes_cbc, vg_aes_siv_init_aes,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::aes_siv::{
    VG_AES_SIV_DECRYPT_AESNI_FEATURES, VG_AES_SIV_DECRYPT_VAES_FEATURES,
    VG_AES_SIV_ENCRYPT_AESNI_FEATURES, VG_AES_SIV_ENCRYPT_VAES_FEATURES,
    VG_AES_SIV_INIT_AESNI_FEATURES, VG_AES_SIV_INIT_VAES_FEATURES, vg_aes_siv_decrypt_aesni,
    vg_aes_siv_decrypt_vaes, vg_aes_siv_encrypt_aesni, vg_aes_siv_encrypt_vaes,
    vg_aes_siv_init_aesni, vg_aes_siv_init_vaes,
};
use crate::arch::aes_siv::{vg_aes_siv_decrypt, vg_aes_siv_encrypt, vg_aes_siv_init};
use crate::cpu::{Features, detected};
use crate::zeroize::zeroize;
use core::mem::MaybeUninit;

/// A 16-byte block.
type Block = [u8; 16];

/// The working space of `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt`, in
/// 64-bit words: the synthetic IV in its first 16 bytes.
const WORK: usize = 322;

/// The instance of a function for `backend`; for `encrypt` and `decrypt` on
/// AArch64 with the AES extension, `$aes_cbc` rather than `$aes` if `$long`
/// (`chains_long`).
macro_rules! instance {
    ($backend:expr, $long:expr, $scalar:ident,
     x86_64: [$aesni:ident, $vaes:ident],
     aarch64: [$aes:ident, $aes_cbc:ident]) => {
        match $backend {
            Backend::Scalar => $scalar,
            #[cfg(target_arch = "x86_64")]
            Backend::AesNi => $aesni,
            #[cfg(target_arch = "x86_64")]
            Backend::Vaes => $vaes,
            #[cfg(target_arch = "aarch64")]
            Backend::Aes => {
                if $long {
                    $aes_cbc
                } else {
                    $aes
                }
            }
        }
    };
}

/// Whether `encrypt` and `decrypt` should run the `_aes_cbc` instances (on
/// AArch64 with the AES extension), whose CMAC chains whole blocks with the
/// round keys and the chaining value kept in vector registers, rather than
/// the `_aes` ones: when the associated-data components `ads` and the `len`
/// bytes of data total more than 32 bytes, as AES-CMAC's updates
/// (`crate::cmac::aes`).
#[cfg(target_arch = "aarch64")]
fn chains_long(ads: &[&[u8]], len: usize) -> bool {
    ads.iter()
        .fold(len, |total, ad| total.saturating_add(ad.len()))
        > 32
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// the AES-SIV functions for it.
#[cfg(target_arch = "aarch64")]
fn select(f: Features) -> Backend {
    const AES: Features = Features::all(&[
        VG_AES_SIV_INIT_AES_FEATURES,
        VG_AES_SIV_ENCRYPT_AES_FEATURES,
        VG_AES_SIV_ENCRYPT_AES_CBC_FEATURES,
        VG_AES_SIV_DECRYPT_AES_FEATURES,
        VG_AES_SIV_DECRYPT_AES_CBC_FEATURES,
    ]);
    Backend::select_for(f, AES)
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// the AES-SIV functions for it.
#[cfg(target_arch = "x86_64")]
fn select(f: Features) -> Backend {
    const VAES: Features = Features::all(&[
        VG_AES_SIV_INIT_VAES_FEATURES,
        VG_AES_SIV_ENCRYPT_VAES_FEATURES,
        VG_AES_SIV_DECRYPT_VAES_FEATURES,
    ]);
    const AESNI: Features = Features::all(&[
        VG_AES_SIV_INIT_AESNI_FEATURES,
        VG_AES_SIV_ENCRYPT_AESNI_FEATURES,
        VG_AES_SIV_DECRYPT_AESNI_FEATURES,
    ]);
    Backend::select_for(f, VAES, AESNI)
}

/// The only implementation of AES on ARMv7, with the AES-SIV functions for
/// it.
#[cfg(target_arch = "arm")]
fn select(f: Features) -> Backend {
    Backend::select(f)
}

/// Why an AES-SIV operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The key is not 32, 48 or 64 bytes long.
    InvalidKeyLength,
    /// More than [`AesSiv::MAX_COMPONENTS`] associated-data components.
    TooManyComponents,
    /// The synthetic IV does not match: the ciphertext or the associated
    /// data is not what was authenticated under this key.
    TagMismatch,
}

/// An AES-SIV key: its key context. [`encrypt_in_place`](Self::encrypt_in_place)
/// is `SIV-ENCRYPT` and [`decrypt_in_place`](Self::decrypt_in_place)
/// `SIV-DECRYPT` (RFC 5297 §2.6, §2.7), with the synthetic IV `V` apart from
/// the data: the RFC's output is `V` followed by the ciphertext.
#[derive(Clone)]
pub struct AesSiv {
    /// The key context `vg_aes_siv_init` writes (`VG.Spec.Siv.KeyRepr`).
    ctx: [u64; 64],
    /// The number of rounds of AES for each half of the key.
    rounds: usize,
    /// The implementation of AES the functions called call.
    backend: Backend,
}

impl Drop for AesSiv {
    /// Wipes the key context.
    fn drop(&mut self) {
        zeroize(&mut self.ctx);
    }
}

impl AesSiv {
    /// The size of the synthetic IV, in bytes.
    pub const TAG_SIZE: usize = 16;

    /// The most associated-data components a message may have (RFC 5297
    /// §2.6: S2V takes at most 127 strings, the last the plaintext).
    pub const MAX_COMPONENTS: usize = 126;

    /// Prepares `key`, which must be 32, 48 or 64 bytes long: `K1`, for
    /// S2V, then `K2`, for CTR, each 16, 24 or 32 bytes.
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        if !matches!(key.len(), 32 | 48 | 64) {
            return Err(Error::InvalidKeyLength);
        }
        let mut k = AesSiv {
            ctx: [0; 64],
            rounds: key.len() / 8 + 6,
            backend: select(detected()),
        };
        let init = instance!(
            k.backend,
            false,
            vg_aes_siv_init,
            x86_64: [vg_aes_siv_init_aesni, vg_aes_siv_init_vaes],
            aarch64: [vg_aes_siv_init_aes, vg_aes_siv_init_aes]
        );
        // SAFETY: `key` is valid for reads of `key.len()` bytes, which is 32,
        // 48 or 64, and `k.ctx` for reads and writes of 512 bytes. They are
        // distinct objects, so they do not overlap each other, the return
        // addresses on the stack (on x86-64) or the stack below them that
        // the function uses, and neither wraps around the end of the address
        // space. The CPU has the features of the implementation selected.
        unsafe { init(key.as_ptr(), key.len(), &mut k.ctx) };
        Ok(k)
    }

    /// Writes the descriptors of the associated-data components `ads` to the
    /// start of `descs`, as `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt`
    /// take them: each its address and its length. Only those `ads.len()`
    /// entries are written (the rest stay uninitialized, and the functions
    /// read only those), so a short list costs no more than its length.
    fn descriptors(
        ads: &[&[u8]],
        descs: &mut [MaybeUninit<[usize; 2]>; Self::MAX_COMPONENTS],
    ) -> Result<*const [usize; 2], Error> {
        if ads.len() > Self::MAX_COMPONENTS {
            return Err(Error::TooManyComponents);
        }
        for (d, s) in descs.iter_mut().zip(ads) {
            d.write([s.as_ptr() as usize, s.len()]);
        }
        Ok(descs.as_ptr().cast())
    }

    /// `SIV-ENCRYPT` (RFC 5297 §2.6): encrypts `data` in place, and returns
    /// the synthetic IV `V`, which authenticates the plaintext and the
    /// associated-data components `ads` (at most
    /// [`MAX_COMPONENTS`](Self::MAX_COMPONENTS) of them, in order). The same
    /// key, components and plaintext always give the same output: a
    /// protocol that must hide repeated messages passes a nonce as the last
    /// component.
    pub fn encrypt_in_place(&self, ads: &[&[u8]], data: &mut [u8]) -> Result<Block, Error> {
        let mut storage = [const { MaybeUninit::uninit() }; Self::MAX_COMPONENTS];
        let descs = Self::descriptors(ads, &mut storage)?;
        let mut work = MaybeUninit::<[u64; WORK]>::uninit();
        let encrypt = instance!(
            self.backend,
            chains_long(ads, data.len()),
            vg_aes_siv_encrypt,
            x86_64: [vg_aes_siv_encrypt_aesni, vg_aes_siv_encrypt_vaes],
            aarch64: [vg_aes_siv_encrypt_aes, vg_aes_siv_encrypt_aes_cbc]
        );
        // SAFETY: `self.ctx` is the key context `vg_aes_siv_init` wrote for
        // `self.rounds` (10, 12 or 14) rounds (every implementation writes
        // the same one), valid for reads of 512 bytes. `descs` points to
        // `storage`, whose first `ads.len()` entries (`16 * ads.len()`
        // bytes, all the function reads) `descriptors` initialized to list
        // the components of `ads`, each valid for reads of its length in
        // bytes. `data` is valid for
        // reads and writes of `data.len()` bytes and `work` for reads and
        // writes of 2576. `data` and `work` are unique borrows, so they
        // overlap neither each other nor `self.ctx`, `storage` or a component;
        // no buffer overlaps the arguments on the stack or the return address
        // (on x86-64) or the stack below it that the function uses, and none
        // wraps around the end of the address space. The CPU has the
        // features of the implementation selected.
        // `work` is uninitialized: it is only working space but for the
        // synthetic IV written to its first 16 bytes, and the contract's
        // result does not depend on what it holds.
        unsafe {
            encrypt(
                &self.ctx,
                self.rounds,
                descs,
                ads.len(),
                data.as_mut_ptr(),
                data.len(),
                work.as_mut_ptr(),
            )
        };
        // SAFETY: `encrypt` wrote the synthetic IV to the first 16 bytes of
        // `work`.
        Ok(unsafe { first_block(&work) })
    }

    /// `SIV-DECRYPT` (RFC 5297 §2.7): decrypts `data` in place with the
    /// synthetic IV `tag`, and checks that `tag` authenticates the plaintext
    /// and the associated-data components `ads`. If it does not, returns an
    /// error and overwrites `data` with zeros.
    pub fn decrypt_in_place(
        &self,
        ads: &[&[u8]],
        data: &mut [u8],
        tag: &[u8; 16],
    ) -> Result<(), Error> {
        let mut storage = [const { MaybeUninit::uninit() }; Self::MAX_COMPONENTS];
        let descs = Self::descriptors(ads, &mut storage)?;
        let mut work = MaybeUninit::<[u64; WORK]>::uninit();
        let decrypt = instance!(
            self.backend,
            chains_long(ads, data.len()),
            vg_aes_siv_decrypt,
            x86_64: [vg_aes_siv_decrypt_aesni, vg_aes_siv_decrypt_vaes],
            aarch64: [vg_aes_siv_decrypt_aes, vg_aes_siv_decrypt_aes_cbc]
        );
        let w = work.as_mut_ptr().cast::<u64>();
        // SAFETY: `work` is valid for writes of 322 words.
        unsafe {
            w.write(u64::from_le_bytes(tag[..8].try_into().unwrap()));
            w.add(1)
                .write(u64::from_le_bytes(tag[8..].try_into().unwrap()));
        }
        // SAFETY: as in `encrypt_in_place`, with the received synthetic IV
        // in the first 16 bytes of `work`.
        let ok = unsafe {
            decrypt(
                &self.ctx,
                self.rounds,
                descs,
                ads.len(),
                data.as_mut_ptr(),
                data.len(),
                work.as_mut_ptr(),
            )
        };
        // `decrypt`'s contract leaves the plaintext in `data` if it returns
        // 1, and zeros otherwise.
        if ok == 1 {
            Ok(())
        } else {
            Err(Error::TagMismatch)
        }
    }
}

/// The first 16 bytes of `work`, where `encrypt` writes the synthetic IV.
///
/// # Safety
///
/// They must have been written.
unsafe fn first_block(work: &MaybeUninit<[u64; WORK]>) -> Block {
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
    use super::{AesSiv, Error};

    /// The `_aes_cbc` instances run when the components and the data total
    /// more than 32 bytes, and the `_aes` ones otherwise.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn chains_long() {
        use super::chains_long;
        assert!(!chains_long(&[], 0));
        assert!(!chains_long(&[], 32));
        assert!(chains_long(&[], 33));
        assert!(!chains_long(&[&[0; 16], &[0; 8]], 8));
        assert!(chains_long(&[&[0; 16], &[0; 8]], 9));
        assert!(chains_long(&[&[0; 33]], 0));
    }

    #[test]
    fn key_lengths() {
        let key = [0u8; 80];
        for n in [0, 16, 24, 31, 33, 47, 63, 65, 80] {
            assert_eq!(AesSiv::new(&key[..n]).err(), Some(Error::InvalidKeyLength));
        }
    }

    #[test]
    fn too_many_components() {
        let k = AesSiv::new(&[0; 32]).unwrap();
        let ads = [&[][..]; AesSiv::MAX_COMPONENTS + 1];
        let mut data = [1u8; 5];
        assert_eq!(
            k.encrypt_in_place(&ads, &mut data),
            Err(Error::TooManyComponents)
        );
        assert_eq!(
            k.decrypt_in_place(&ads, &mut data, &[0; 16]),
            Err(Error::TooManyComponents)
        );
        // Nothing was touched.
        assert_eq!(data, [1; 5]);
        // The most components allowed round-trip.
        let ads = &ads[..AesSiv::MAX_COMPONENTS];
        let tag = k.encrypt_in_place(ads, &mut data).unwrap();
        k.decrypt_in_place(ads, &mut data, &tag).unwrap();
        assert_eq!(data, [1; 5]);
    }
}
