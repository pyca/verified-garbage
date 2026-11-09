//! AES-GCM (NIST SP 800-38D) with 128-, 192- and 256-bit keys, for whole
//! messages and incrementally.
//!
//! A nonce must never be used twice with the same key. **An
//! [`AesGcmDecryptor`]'s `update` returns plaintext that has not been
//! authenticated**: act on none of it before its `finalize` succeeds, or, when
//! the message fits in memory, use [`AesGcm::decrypt_in_place`], which checks
//! the tag before it decrypts.
//!
//! # Tags
//!
//! Encryption returns the full 16-byte tag; a protocol that sends a shorter one
//! sends its first bytes. Decryption takes a `&[u8; 16]` or, for a truncated
//! tag, a `&[u8; N]` with `N` from 4 to 16 fixed at compile time
//! ([`AesGcm::decrypt_in_place_truncated`],
//! [`AesGcmDecryptor::finalize_truncated`]), never a slice, whose length often
//! comes from the message: splitting the last 16 bytes off a 4-byte message
//! would check a 4-byte tag, forged with probability 2⁻³² rather than 2⁻¹²⁸. SP
//! 800-38D §5.2.1.2 allows only 4, 8 and 12 to 16 bytes (5–7 and 9–11 are
//! extensions), and 4 and 8 only within its Appendix C's limits on message
//! lengths and decryptions per key, which the caller enforces.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::gcm::{
    vg_aes_gcm_init_auto, vg_aes_gcm_stream_aad_auto, vg_aes_gcm_stream_finish_auto,
    vg_aes_gcm_stream_init_auto, vg_aes_gcm_stream_verify_auto,
};
// On AArch64 and x86-64, a key computes the powers of its hash subkey when
// it is created, which the functions below read; elsewhere the functions
// read the key context alone.
use crate::align::CacheAligned;
#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
use crate::arch::dispatch::gcm::vg_aes_gcm_open_to_auto;
#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
use crate::arch::dispatch::gcm::{
    vg_aes_gcm_open_auto, vg_aes_gcm_seal_auto, vg_aes_gcm_seal_gather_auto,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::dispatch::gcm::{
    vg_aes_gcm_open_prepared_auto, vg_aes_gcm_open_to_prepared_auto, vg_aes_gcm_prepare_auto,
    vg_aes_gcm_seal_gather_prepared_auto, vg_aes_gcm_seal_prepared_auto,
    vg_aes_gcm_stream_decrypt_prepared_auto, vg_aes_gcm_stream_encrypt_prepared_auto,
    vg_aes_gcm_wipe_prepared_auto,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::dispatch::gcm::{
    vg_aes_gcm_open_to_with_powers_auto, vg_aes_gcm_open_with_powers_auto,
    vg_aes_gcm_seal_with_powers_auto, vg_aes_gcm_store_powers_auto,
};
#[cfg(not(target_arch = "x86_64"))]
use crate::arch::dispatch::gcm::{vg_aes_gcm_stream_decrypt_auto, vg_aes_gcm_stream_encrypt_auto};
use crate::error::InvalidKeyLength;
#[cfg(not(target_arch = "x86_64"))]
use crate::zeroize::zeroize;
use core::mem::MaybeUninit;

/// A 16-byte block.
type Block = [u8; 16];

/// What a key keeps of its key context: on x86-64, the 1032-byte prepared key
/// context of `vg_aes_gcm_prepare` (`VG.Spec.Gcm.PreparedRepr`), whose first
/// 256 bytes are the key context of `vg_aes_gcm_init` (`AesGcm::key`),
/// followed by the powers of its hash subkey and a word saying whether they
/// are there; elsewhere, the key context of `vg_aes_gcm_init` alone.
#[cfg(target_arch = "x86_64")]
type KeyCtx = [u64; 129];
#[cfg(not(target_arch = "x86_64"))]
type KeyCtx = [u64; 32];

/// On AArch64, the powers of the hash subkey that the `_with_powers`
/// functions read next to the key context (`VG.Spec.Gcm.Powers8Repr`).
#[cfg(target_arch = "aarch64")]
type Powers = [u64; 16];

/// The largest plaintext (and ciphertext), in bytes: `2^39 − 256` bits
/// (SP 800-38D §5.2.1.1).
const MAX_TEXT: u64 = (1 << 36) - 32;

/// The largest additional data, in bytes: `2^64 − 1` bits, rounded down to
/// whole bytes (SP 800-38D §5.2.1.1).
const MAX_AAD: u64 = (1 << 61) - 1;

/// Why an AES-GCM operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The nonce is empty.
    InvalidNonceLength,
    /// The plaintext or ciphertext is longer than `2^36 − 32` bytes.
    InvalidTextLength,
    /// The additional data is longer than `2^61 − 1` bytes.
    InvalidAadLength,
    /// The tag does not match: the ciphertext, the additional data or the
    /// nonce is not what was authenticated under this key.
    TagMismatch,
    /// [`AesGcmEncryptor::update_aad`] or [`AesGcmDecryptor::update_aad`]
    /// was called after `update`: GCM authenticates all of the additional
    /// data before the text.
    AadAfterText,
    /// The output of [`AesGcm::encrypt`] is not as long as the plaintext.
    InvalidOutputLength,
    /// More than [`AesGcm::MAX_PIECES`] pieces of plaintext for
    /// [`AesGcm::encrypt`].
    TooManyPieces,
}

crate::error::impl_error! {
    Error {
        InvalidNonceLength => "AES-GCM nonce is empty",
        InvalidTextLength => "AES-GCM text is too long",
        InvalidAadLength => "AES-GCM additional data is too long",
        TagMismatch => "AES-GCM tag does not match",
        AadAfterText => "AES-GCM additional data after the text",
        InvalidOutputLength => "AES-GCM output is not as long as the plaintext",
        TooManyPieces => "too many pieces of AES-GCM plaintext",
    }
}

/// `len + n`, if it is at most `max`.
fn add_len(len: u64, n: usize, max: u64) -> Result<u64, ()> {
    match len.checked_add(n as u64) {
        Some(total) if total <= max => Ok(total),
        _ => Err(()),
    }
}

/// Checks that a nonce is not empty (§5.2.1.1; it is shorter than `2^61`
/// bytes, as no buffer is that long).
fn check_nonce(nonce: &[u8]) -> Result<(), Error> {
    if nonce.is_empty() {
        return Err(Error::InvalidNonceLength);
    }
    Ok(())
}

/// Fails to compile unless `N` is between 4 and 16 bytes, inclusive.
macro_rules! assert_tag_length {
    ($n:expr) => {
        const {
            assert!(
                matches!($n, 4..=16),
                "an AES-GCM tag is between 4 and 16 bytes long"
            )
        }
    };
}

/// An AES-GCM key: its key context (the AES key schedule and the hash
/// subkey `H`, with the powers of `H` on x86-64 and AArch64). Its
/// [`encrypt_in_place`](Self::encrypt_in_place) and
/// [`decrypt_in_place`](Self::decrypt_in_place) (or
/// [`decrypt_in_place_truncated`](Self::decrypt_in_place_truncated)) are the
/// one-shot AEAD; [`encryptor`](Self::encryptor) and
/// [`decryptor`](Self::decryptor) start incremental ones.
#[derive(Clone)]
// The key context, with the powers on x86-64, is the first field, aligned
// to a cache line, so that the implementations' reads of it (the prepared
// functions' of the powers) do not cross cache lines, as some would at 8
// bytes' alignment. After a pointer, on x86 its offset in a 4-byte-aligned
// value also left the compiler unable to clear it with aligned 16-byte
// stores in `new`, and it called `memset` instead (4–5% slower `new` on
// Zen 3).
#[repr(C)]
pub struct AesGcm {
    /// The key context `vg_aes_gcm_init` writes (`VG.Spec.Gcm.KeyRepr`),
    /// with the powers `vg_aes_gcm_prepare` writes after it on x86-64
    /// (`KeyCtx`), all of which `new` writes.
    ctx: CacheAligned<MaybeUninit<KeyCtx>>,
    rounds: usize,
    /// On AArch64, the powers of the hash subkey that `new` stores
    /// (`VG.Spec.Gcm.Powers8Repr`).
    #[cfg(target_arch = "aarch64")]
    powers: CacheAligned<Powers>,
}

impl Drop for AesGcm {
    /// Wipes the key context, with the powers.
    fn drop(&mut self) {
        // SAFETY: `self.ctx` is a prepared key context (`new`), valid for
        // reads and writes of 1032 bytes, and overlaps nothing on the stack;
        // `vg_aes_gcm_wipe_prepared` zeroes all of it that `new` wrote but the
        // flag word (`VG.Spec.Gcm.wipePreparedContract`).
        #[cfg(target_arch = "x86_64")]
        unsafe {
            vg_aes_gcm_wipe_prepared_auto(
                crate::dit::public(crate::dit::Why::Wipe),
                self.ctx.0.as_mut_ptr(),
            )
        };
        #[cfg(not(target_arch = "x86_64"))]
        zeroize(core::slice::from_mut(&mut self.ctx));
        #[cfg(target_arch = "aarch64")]
        zeroize(&mut self.powers.0);
    }
}

impl AesGcm {
    /// The size of a full tag, in bytes.
    pub const TAG_SIZE: usize = 16;

    /// Prepares `key`, which must be 16, 24 or 32 bytes long (AES-128,
    /// AES-192 or AES-256).
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        crate::dit::enter!(dit);
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(InvalidKeyLength);
        }
        let mut k = AesGcm {
            ctx: CacheAligned(MaybeUninit::uninit()),
            rounds: key.len() / 4 + 6,
            #[cfg(target_arch = "aarch64")]
            powers: CacheAligned([0; size_of::<Powers>() / 8]),
        };
        // Only the key context of `vg_aes_gcm_init` is cleared first (`init`
        // reads it); on x86-64 `prepare` writes the rest.
        // SAFETY: `k.ctx` is valid for writes of at least 256 bytes.
        unsafe { k.ctx.0.as_mut_ptr().cast::<[u64; 32]>().write([0; 32]) };
        // SAFETY: `key` is valid for reads of `key.len()` bytes, which is 16,
        // 24 or 32; `k.ctx` is valid for reads and writes of 256 bytes. They
        // are distinct objects, so they do not overlap each other or anything
        // on the stack, or wrap around the end of the address space.
        unsafe { vg_aes_gcm_init_auto(dit, key.as_ptr(), key.len(), k.ctx.0.as_mut_ptr().cast()) };
        // SAFETY: `k.ctx` is valid for reads and writes of 1032 bytes, and
        // overlaps nothing on the stack; its first 256 bytes are the key
        // context of `vg_aes_gcm_init` (`VG.Spec.Gcm.KeyRepr`), which
        // `vg_aes_gcm_prepare` keeps, making the rest a prepared key context
        // (`PreparedRepr`), which the `_prepared` functions require.
        #[cfg(target_arch = "x86_64")]
        unsafe {
            vg_aes_gcm_prepare_auto(dit, k.ctx.0.as_mut_ptr())
        };
        // SAFETY: the key context, valid for reads of 256 bytes (written
        // above), and `k.powers`, for writes of 128, are distinct fields, so
        // they do not overlap each other or anything on the stack, or wrap
        // around the end of the address space. `vg_aes_gcm_store_powers`
        // writes the powers of the context's hash subkey (`Powers8Repr`),
        // which the `_with_powers` functions require.
        #[cfg(target_arch = "aarch64")]
        unsafe {
            vg_aes_gcm_store_powers_auto(dit, k.ctx.0.as_ptr().cast(), &mut k.powers.0)
        };
        Ok(k)
    }

    /// The key context of `vg_aes_gcm_init`, which the functions that read
    /// no powers read.
    #[inline(always)]
    fn key(&self) -> &[u64; 32] {
        // SAFETY: `new` writes the first 256 bytes of `self.ctx`.
        unsafe { &*self.ctx.0.as_ptr().cast::<[u64; 32]>() }
    }

    /// GCM-AE (§7.1): encrypts `data` in place under `nonce`, and returns
    /// the 16-byte tag authenticating the ciphertext and `aad`. A caller that
    /// wants a shorter tag truncates it (keeping its first bytes), and
    /// decrypts with [`decrypt_in_place_truncated`](Self::decrypt_in_place_truncated).
    ///
    /// The nonce may have any nonzero length; 12 bytes is the recommended
    /// (and fastest) one. A nonce must never be used twice with the same key.
    pub fn encrypt_in_place(
        &self,
        nonce: &[u8],
        aad: &[u8],
        data: &mut [u8],
    ) -> Result<Block, Error> {
        crate::dit::enter!(dit);
        // Check the lengths before encrypting anything.
        check_nonce(nonce)?;
        add_len(0, data.len(), MAX_TEXT).map_err(|()| Error::InvalidTextLength)?;
        add_len(0, aad.len(), MAX_AAD).map_err(|()| Error::InvalidAadLength)?;
        Ok(self.seal(dit, nonce, aad, data))
    }

    /// `vg_aes_gcm_seal` (on x86-64, `vg_aes_gcm_seal_prepared`; on
    /// AArch64, `vg_aes_gcm_seal_with_powers`) of `data` in place, whose
    /// lengths the caller checked.
    #[inline(always)]
    fn seal(&self, dit: crate::dit::Dit<'_>, nonce: &[u8], aad: &[u8], data: &mut [u8]) -> Block {
        let mut tag: Block = [0; 16];
        // SAFETY: `self.ctx` is the key context `vg_aes_gcm_init` wrote for
        // `self.rounds` (10, 12 or 14) rounds, valid for reads of 256 bytes,
        // followed on x86-64 by the powers `vg_aes_gcm_prepare` wrote for the
        // same key (`AesGcm::new`), valid for reads of 1032 bytes in all,
        // and on AArch64 next to the powers `vg_aes_gcm_store_powers` wrote
        // (`self.powers`, 128 bytes); `nonce` and `aad` are valid for reads
        // and `data` for reads and writes of their lengths, and `tag` (a
        // local) for reads and writes of 16 bytes. They are distinct objects
        // (`data` a unique borrow), so the writable ones overlap nothing
        // else, nor anything on the stack, and none wraps around the end of
        // the address space.
        unsafe {
            #[cfg(target_arch = "x86_64")]
            vg_aes_gcm_seal_prepared_auto(
                dit,
                self.ctx.0.as_ptr(),
                self.rounds,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
                &mut tag,
            );
            #[cfg(target_arch = "aarch64")]
            vg_aes_gcm_seal_with_powers_auto(
                dit,
                self.key(),
                self.rounds,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
                &mut tag,
                &self.powers.0,
            );
            #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
            vg_aes_gcm_seal_auto(
                dit,
                self.key(),
                self.rounds,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
                &mut tag,
            );
        }
        tag
    }

    /// GCM-AD (§7.2): if the 16-byte `tag` authenticates the ciphertext in
    /// `data` and `aad` under `nonce`, decrypts `data` in place. Otherwise
    /// returns an error and leaves `data` unchanged.
    ///
    /// A protocol that truncates the tag uses
    /// [`decrypt_in_place_truncated`](Self::decrypt_in_place_truncated).
    pub fn decrypt_in_place(
        &self,
        nonce: &[u8],
        aad: &[u8],
        data: &mut [u8],
        tag: &[u8; 16],
    ) -> Result<(), Error> {
        self.decrypt_in_place_truncated(nonce, aad, data, tag)
    }

    /// GCM-AD (§7.2) with a tag truncated to `N` bytes: if `tag` is the
    /// first `N` bytes of the tag of the ciphertext in `data` and `aad` under
    /// `nonce`, decrypts `data` in place. Otherwise returns an error and
    /// leaves `data` unchanged.
    ///
    /// `N` must be between 4 and 16, inclusive; any
    /// other length is an error when the call is compiled. It is a type
    /// parameter, fixed in the caller's code, so that it cannot come from the message: see
    /// the [module documentation](self#tags). SP 800-38D Appendix C
    /// restricts 4- and 8-byte tags to applications that bound the length of
    /// the messages and the number of decryptions under one key.
    pub fn decrypt_in_place_truncated<const N: usize>(
        &self,
        nonce: &[u8],
        aad: &[u8],
        data: &mut [u8],
        tag: &[u8; N],
    ) -> Result<(), Error> {
        crate::dit::enter!(dit);
        assert_tag_length!(N);
        check_nonce(nonce)?;
        add_len(0, data.len(), MAX_TEXT).map_err(|()| Error::InvalidTextLength)?;
        add_len(0, aad.len(), MAX_AAD).map_err(|()| Error::InvalidAadLength)?;
        self.open(dit, data, tag, nonce, aad)
    }

    /// GCM-AD (§7.2) with `tag`, of a length between 4 and 16 (which the
    /// callers check at compile time; `vg_aes_gcm_open` rejects any other),
    /// whose other lengths the caller checked. Its arguments come in the
    /// order that puts on its stack (`nonce.len()`, `aad`) only what `open`
    /// takes in registers on x86-64, so each is loaded into a register by
    /// itself: passed as `open` takes them, the three on its stack were what
    /// `open` takes on its own, and the compiler copied two of them with one
    /// 16-byte load, which was not forwarded from the caller's two 8-byte
    /// stores (5–11% slower opens of up to 255 bytes on Zen 3, 4 and 5); and
    /// an inline call made every open about 5 ns slower on Emerald Rapids.
    #[cfg_attr(target_arch = "x86_64", inline(never))]
    fn open(
        &self,
        dit: crate::dit::Dit<'_>,
        data: &mut [u8],
        tag: &[u8],
        nonce: &[u8],
        aad: &[u8],
    ) -> Result<(), Error> {
        // SAFETY: as in `seal`, with the received tag `tag` valid for reads
        // of its length.
        let ok = unsafe {
            #[cfg(target_arch = "x86_64")]
            let ok = vg_aes_gcm_open_prepared_auto(
                dit,
                self.ctx.0.as_ptr(),
                self.rounds,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
                tag.as_ptr(),
                tag.len(),
            );
            #[cfg(target_arch = "aarch64")]
            let ok = vg_aes_gcm_open_with_powers_auto(
                dit,
                self.key(),
                self.rounds,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
                tag.as_ptr(),
                tag.len(),
                &self.powers.0,
            );
            #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
            let ok = vg_aes_gcm_open_auto(
                dit,
                self.key(),
                self.rounds,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
                tag.as_ptr(),
                tag.len(),
            );
            ok
        };
        // `open`'s contract leaves `data` as it was unless it returns 1.
        if ok == 1 {
            Ok(())
        } else {
            Err(Error::TagMismatch)
        }
    }

    /// GCM-AD (§7.2), out of place: if the 16-byte `tag` authenticates
    /// `ciphertext` and `aad` under `nonce`, writes the plaintext to `out`,
    /// which must be exactly as long as `ciphertext`. Otherwise returns an
    /// error, having written zeros to `out` if the tag was wrong (and left it
    /// as it was if a length was).
    ///
    /// A protocol that truncates the tag uses
    /// [`decrypt_truncated`](Self::decrypt_truncated).
    pub fn decrypt(
        &self,
        nonce: &[u8],
        aad: &[u8],
        ciphertext: &[u8],
        tag: &[u8; 16],
        out: &mut [u8],
    ) -> Result<(), Error> {
        self.decrypt_truncated(nonce, aad, ciphertext, tag, out)
    }

    /// [`decrypt`](Self::decrypt) with a tag truncated to `N` bytes, as
    /// [`decrypt_in_place_truncated`](Self::decrypt_in_place_truncated)
    /// takes it.
    pub fn decrypt_truncated<const N: usize>(
        &self,
        nonce: &[u8],
        aad: &[u8],
        ciphertext: &[u8],
        tag: &[u8; N],
        out: &mut [u8],
    ) -> Result<(), Error> {
        crate::dit::enter!(dit);
        assert_tag_length!(N);
        if out.len() != ciphertext.len() {
            return Err(Error::InvalidOutputLength);
        }
        check_nonce(nonce)?;
        add_len(0, out.len(), MAX_TEXT).map_err(|()| Error::InvalidTextLength)?;
        add_len(0, aad.len(), MAX_AAD).map_err(|()| Error::InvalidAadLength)?;
        // SAFETY: as in `seal`, with `ciphertext` and the received tag `tag`
        // valid for reads, and `out` for reads and writes, of their lengths,
        // `out` as long as `ciphertext`. `out` is a unique borrow, so it
        // overlaps neither `ciphertext` nor any other argument.
        let ok = unsafe {
            #[cfg(target_arch = "x86_64")]
            let ok = vg_aes_gcm_open_to_prepared_auto(
                dit,
                self.ctx.0.as_ptr(),
                self.rounds,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                ciphertext.as_ptr(),
                ciphertext.len(),
                out.as_mut_ptr(),
                out.len(),
                tag.as_ptr(),
                tag.len(),
            );
            #[cfg(target_arch = "aarch64")]
            let ok = vg_aes_gcm_open_to_with_powers_auto(
                dit,
                self.key(),
                self.rounds,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                ciphertext.as_ptr(),
                ciphertext.len(),
                out.as_mut_ptr(),
                out.len(),
                tag.as_ptr(),
                tag.len(),
                &self.powers.0,
            );
            #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
            let ok = vg_aes_gcm_open_to_auto(
                dit,
                self.key(),
                self.rounds,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                ciphertext.as_ptr(),
                ciphertext.len(),
                out.as_mut_ptr(),
                out.len(),
                tag.as_ptr(),
                tag.len(),
            );
            ok
        };
        // `open_to`'s contract writes zeros to `out` unless it returns 1.
        if ok == 1 {
            Ok(())
        } else {
            Err(Error::TagMismatch)
        }
    }

    /// The most pieces [`encrypt`](Self::encrypt) takes a plaintext in.
    pub const MAX_PIECES: usize = 64;

    /// GCM-AE (§7.1), out of place: encrypts the plaintext made of the
    /// pieces `plaintext`, in order, under `nonce` into `out`, which must be
    /// exactly as long as they are in all, and returns the 16-byte tag
    /// authenticating the ciphertext and `aad`. A plaintext in one buffer is
    /// one piece (`&[buf]`); there may be at most
    /// [`MAX_PIECES`](Self::MAX_PIECES). The nonce is as for
    /// [`encrypt_in_place`](Self::encrypt_in_place).
    pub fn encrypt(
        &self,
        nonce: &[u8],
        aad: &[u8],
        plaintext: &[&[u8]],
        out: &mut [u8],
    ) -> Result<Block, Error> {
        crate::dit::enter!(dit);
        if plaintext.len() > Self::MAX_PIECES {
            return Err(Error::TooManyPieces);
        }
        check_nonce(nonce)?;
        let mut len = 0;
        for p in plaintext {
            len = add_len(len, p.len(), MAX_TEXT).map_err(|()| Error::InvalidTextLength)?;
        }
        if len != out.len() as u64 {
            return Err(Error::InvalidOutputLength);
        }
        add_len(0, aad.len(), MAX_AAD).map_err(|()| Error::InvalidAadLength)?;
        Ok(self.seal_pieces(dit, nonce, aad, plaintext, out))
    }

    /// `encrypt` on AArch64, where no `_with_powers` function gathers the
    /// pieces: copies the pieces `plaintext` to `out`, one after the other
    /// (as `vg_aes_gcm_seal_gather` does), and seals them there. Which bytes
    /// it copies where depends only on the pieces' lengths (whose sum
    /// `encrypt` checked is `out.len()`).
    #[cfg(target_arch = "aarch64")]
    #[inline(never)]
    fn seal_pieces(
        &self,
        dit: crate::dit::Dit<'_>,
        nonce: &[u8],
        aad: &[u8],
        plaintext: &[&[u8]],
        out: &mut [u8],
    ) -> Block {
        let mut rest = &mut *out;
        for piece in plaintext {
            let (dst, tail) = rest.split_at_mut(piece.len());
            dst.copy_from_slice(piece);
            rest = tail;
        }
        self.seal(dit, nonce, aad, out)
    }

    /// `encrypt` elsewhere, by `vg_aes_gcm_seal_gather` (on x86-64,
    /// `vg_aes_gcm_seal_gather_prepared`).
    #[cfg(not(target_arch = "aarch64"))]
    #[inline(always)]
    fn seal_pieces(
        &self,
        dit: crate::dit::Dit<'_>,
        nonce: &[u8],
        aad: &[u8],
        plaintext: &[&[u8]],
        out: &mut [u8],
    ) -> Block {
        // The descriptors of the pieces, as `vg_aes_gcm_seal_gather` takes
        // them: each its address and its length. Only the first
        // `plaintext.len()` are written, and the function reads only those.
        let mut descs = [const { MaybeUninit::<[usize; 2]>::uninit() }; Self::MAX_PIECES];
        for (d, p) in descs.iter_mut().zip(plaintext) {
            d.write([p.as_ptr() as usize, p.len()]);
        }
        let src: *const [usize; 2] = descs.as_ptr().cast();
        let mut tag: Block = [0; 16];
        // SAFETY: as in `seal`, with `out` valid for reads and writes of
        // `out.len()` bytes; `src` points to `plaintext.len()` initialized
        // descriptors (in `descs`, a local), each the address and the length
        // of a piece valid for reads, which are `out.len()` bytes in all.
        // The pieces and the descriptors are read only, and overlap neither
        // `out` (a unique borrow) nor `tag`, nor anything on the stack the
        // function uses.
        unsafe {
            #[cfg(target_arch = "x86_64")]
            vg_aes_gcm_seal_gather_prepared_auto(
                dit,
                self.ctx.0.as_ptr(),
                self.rounds,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                src,
                plaintext.len(),
                out.as_mut_ptr(),
                out.len(),
                &mut tag,
            );
            #[cfg(not(target_arch = "x86_64"))]
            vg_aes_gcm_seal_gather_auto(
                dit,
                self.key(),
                self.rounds,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                src,
                plaintext.len(),
                out.as_mut_ptr(),
                out.len(),
                &mut tag,
            );
        }
        tag
    }

    /// Starts encrypting a message under this key and `nonce` (of any
    /// nonzero length; 12 bytes is the recommended one). A nonce must never
    /// be used twice with the same key.
    pub fn encryptor(&self, nonce: &[u8]) -> Result<AesGcmEncryptor<'_>, Error> {
        crate::dit::enter!(dit);
        Ok(AesGcmEncryptor {
            stream: Stream::new(dit, self, nonce)?,
        })
    }

    /// Starts decrypting a message under this key and `nonce`. Its
    /// [`update`](AesGcmDecryptor::update) returns plaintext that has not
    /// been authenticated until its [`finalize`](AesGcmDecryptor::finalize)
    /// succeeds.
    pub fn decryptor(&self, nonce: &[u8]) -> Result<AesGcmDecryptor<'_>, Error> {
        crate::dit::enter!(dit);
        Ok(AesGcmDecryptor {
            stream: Stream::new(dit, self, nonce)?,
        })
    }
}

/// The state of an incremental encryption or decryption (`DECRYPT`), which
/// [`AesGcmEncryptor`] and [`AesGcmDecryptor`] wrap: the key, the streaming
/// state, and the lengths absorbed so far.
#[derive(Clone)]
struct Stream<'a, const DECRYPT: bool> {
    key: &'a AesGcm,
    /// The streaming state `vg_aes_gcm_stream_init` writes and the other
    /// functions update (`VG.Spec.Gcm.StreamRepr`).
    state: CacheAligned<[u64; 10]>,
    aad_len: u64,
    text_len: u64,
    /// Whether [`update`](Self::update) has been called.
    in_text: bool,
}

impl<const DECRYPT: bool> Drop for Stream<'_, DECRYPT> {
    /// Wipes the streaming state (the key wipes itself).
    fn drop(&mut self) {
        crate::zeroize::zeroize(&mut self.state.0);
    }
}

impl<'a, const DECRYPT: bool> Stream<'a, DECRYPT> {
    /// Starts a message under `key` and `nonce`.
    fn new(dit: crate::dit::Dit<'_>, key: &'a AesGcm, nonce: &[u8]) -> Result<Self, Error> {
        check_nonce(nonce)?;
        let mut s = Stream {
            key,
            state: CacheAligned([0; 10]),
            aad_len: 0,
            text_len: 0,
            in_text: false,
        };
        // SAFETY: `key.key()` is a key context (as in `AesGcm::seal`), valid
        // for reads of 256 bytes, `nonce` for reads of `nonce.len()`, and
        // `s.state` for reads and writes of 80. They are distinct objects, so
        // the writable one overlaps nothing else, nor anything on the stack,
        // and none wraps around.
        unsafe {
            vg_aes_gcm_stream_init_auto(dit, key.key(), nonce.as_ptr(), nonce.len(), &mut s.state.0)
        };
        Ok(s)
    }

    /// Absorbs more additional data, which must all come before the text.
    fn update_aad(&mut self, dit: crate::dit::Dit<'_>, aad: &[u8]) -> Result<(), Error> {
        if self.in_text {
            return Err(Error::AadAfterText);
        }
        let aad_len =
            add_len(self.aad_len, aad.len(), MAX_AAD).map_err(|()| Error::InvalidAadLength)?;
        // SAFETY: as in `new`; `self.state` represents a message with
        // `self.aad_len` bytes of additional data and no text yet.
        unsafe {
            vg_aes_gcm_stream_aad_auto(
                dit,
                self.key.key(),
                &mut self.state.0,
                self.aad_len,
                aad.as_ptr(),
                aad.len(),
            )
        };
        self.aad_len = aad_len;
        Ok(())
    }

    /// Encrypts (or, if `DECRYPT`, decrypts) the next `data.len()` bytes of
    /// the text in place.
    fn update(&mut self, dit: crate::dit::Dit<'_>, data: &mut [u8]) -> Result<(), Error> {
        let text_len =
            add_len(self.text_len, data.len(), MAX_TEXT).map_err(|()| Error::InvalidTextLength)?;
        self.in_text = true;
        #[cfg(target_arch = "x86_64")]
        let (ctx, encrypt, decrypt) = (
            self.key.ctx.0.as_ptr(),
            vg_aes_gcm_stream_encrypt_prepared_auto,
            vg_aes_gcm_stream_decrypt_prepared_auto,
        );
        #[cfg(not(target_arch = "x86_64"))]
        let (ctx, encrypt, decrypt) = (
            self.key.key(),
            vg_aes_gcm_stream_encrypt_auto,
            vg_aes_gcm_stream_decrypt_auto,
        );
        // SAFETY: as in `new`, with the key context as in `AesGcm::seal` and
        // `data` valid for reads and writes of `data.len()` bytes (a unique
        // borrow, so it overlaps nothing else); `self.state` represents a
        // message with `self.aad_len` bytes of additional data and
        // `self.text_len` of text.
        unsafe {
            (if DECRYPT { decrypt } else { encrypt })(
                dit,
                ctx,
                self.key.rounds,
                &mut self.state.0,
                self.aad_len,
                self.text_len,
                data.as_mut_ptr(),
                data.len(),
            )
        };
        self.text_len = text_len;
        Ok(())
    }
}

impl Stream<'_, false> {
    /// Finishes the message and returns its 16-byte tag.
    fn finish(mut self, dit: crate::dit::Dit<'_>) -> Block {
        let mut tag: Block = [0; 16];
        // SAFETY: as in `update`, with `tag` (a local) valid for reads and
        // writes of 16 bytes. `update_aad` and `update` checked the lengths
        // (§5.2.1.1).
        unsafe {
            vg_aes_gcm_stream_finish_auto(
                dit,
                self.key.key(),
                self.key.rounds,
                &mut self.state.0,
                self.aad_len,
                self.text_len,
                &mut tag,
            )
        };
        tag
    }
}

impl Stream<'_, true> {
    /// Finishes the message and checks the received prefix in constant time.
    /// Callers check at compile time that its length is between 4 and 16.
    fn verify(mut self, dit: crate::dit::Dit<'_>, tag: &[u8]) -> Result<(), Error> {
        // SAFETY: as in `finish`, with the received tag `tag` valid for
        // reads of its length.
        let ok = unsafe {
            vg_aes_gcm_stream_verify_auto(
                dit,
                self.key.key(),
                self.key.rounds,
                &mut self.state.0,
                self.aad_len,
                self.text_len,
                tag.as_ptr(),
                tag.len(),
            )
        };
        if ok == 1 {
            Ok(())
        } else {
            Err(Error::TagMismatch)
        }
    }
}

/// An incremental AES-GCM encryption, from [`AesGcm::encryptor`]: the
/// additional data with [`update_aad`](Self::update_aad), then the plaintext
/// with [`update`](Self::update), in pieces of any length, and the tag from
/// [`finalize`](Self::finalize).
///
/// It borrows its [`AesGcm`], so a key encrypts many messages without
/// expanding it again.
#[derive(Clone)]
pub struct AesGcmEncryptor<'a> {
    stream: Stream<'a, false>,
}

impl AesGcmEncryptor<'_> {
    /// Absorbs more additional data. All of it must come before the
    /// plaintext.
    pub fn update_aad(&mut self, aad: &[u8]) -> Result<(), Error> {
        crate::dit::enter!(dit);
        self.stream.update_aad(dit, aad)
    }

    /// Encrypts the next `data.len()` bytes of the plaintext in place.
    pub fn update(&mut self, data: &mut [u8]) -> Result<(), Error> {
        crate::dit::enter!(dit);
        self.stream.update(dit, data)
    }

    /// Finishes the message and returns its full 16-byte tag. A protocol
    /// that sends a shorter tag sends its first bytes. GCM leaves no
    /// buffered text to return.
    pub fn finalize(self) -> Block {
        crate::dit::enter!(dit);
        self.stream.finish(dit)
    }
}

/// An incremental AES-GCM decryption, from [`AesGcm::decryptor`]: the
/// additional data with [`update_aad`](Self::update_aad), then the
/// ciphertext with [`update`](Self::update), in pieces of any length, and
/// the tag checked by [`finalize`](Self::finalize) (16 bytes) or
/// [`finalize_truncated`](Self::finalize_truncated) (a length fixed at
/// compile time: see the [module documentation](self#tags)).
///
/// **[`update`](Self::update) returns plaintext that has not been
/// authenticated yet.** Nothing may act on it before
/// [`finalize`](Self::finalize) (or
/// [`finalize_truncated`](Self::finalize_truncated)) has succeeded. When the
/// whole message fits in memory, [`AesGcm::decrypt_in_place`] checks the tag
/// before it decrypts.
#[derive(Clone)]
pub struct AesGcmDecryptor<'a> {
    stream: Stream<'a, true>,
}

impl AesGcmDecryptor<'_> {
    /// Absorbs more additional data. All of it must come before the
    /// ciphertext.
    pub fn update_aad(&mut self, aad: &[u8]) -> Result<(), Error> {
        crate::dit::enter!(dit);
        self.stream.update_aad(dit, aad)
    }

    /// Decrypts the next `data.len()` bytes of the ciphertext in place. The
    /// result is not authenticated until [`finalize`](Self::finalize) (or
    /// [`finalize_truncated`](Self::finalize_truncated)) succeeds.
    pub fn update(&mut self, data: &mut [u8]) -> Result<(), Error> {
        crate::dit::enter!(dit);
        self.stream.update(dit, data)
    }

    /// Finishes the message and checks that `tag` is its 16-byte tag. If
    /// they differ, this fails, and nothing may act on the plaintext
    /// [`update`](Self::update) returned.
    ///
    /// A protocol that truncates the tag uses
    /// [`finalize_truncated`](Self::finalize_truncated).
    pub fn finalize(self, tag: &[u8; 16]) -> Result<(), Error> {
        self.finalize_truncated(tag)
    }

    /// Finishes the message and checks that `tag` is the first `N` bytes of
    /// its tag. If they differ, this fails, and nothing may act on the
    /// plaintext [`update`](Self::update) returned.
    ///
    /// `N` must be between 4 and 16, inclusive; any
    /// other length is an error when the call is compiled. It is a type
    /// parameter, fixed in the caller's code, so that it cannot come from the
    /// message: see the [module documentation](self#tags). SP 800-38D
    /// Appendix C restricts 4- and 8-byte tags to applications that bound the
    /// length of the messages and the number of decryptions under one key.
    pub fn finalize_truncated<const N: usize>(self, tag: &[u8; N]) -> Result<(), Error> {
        crate::dit::enter!(dit);
        assert_tag_length!(N);
        self.stream.verify(dit, tag)
    }
}

#[cfg(test)]
mod tests {
    use super::{AesGcm, Error, InvalidKeyLength, MAX_AAD, MAX_TEXT, add_len};

    /// Encryption and decryption are inverse, for every key size, 12-byte
    /// and other nonces, and texts and additional data of whole and partial
    /// blocks; a modified tag is rejected.
    #[test]
    fn round_trip() {
        let key: [u8; 32] = core::array::from_fn(|i| i as u8);
        let msg: [u8; 67] = core::array::from_fn(|i| (i as u8).wrapping_mul(7));
        for key_len in [16, 24, 32] {
            let k = AesGcm::new(&key[..key_len]).unwrap();
            for nonce_len in [1, 12, 16, 17] {
                let nonce = &[0x5a; 17][..nonce_len];
                for len in [0, 1, 16, 31, 64, 67] {
                    let (msg, aad) = (&msg[..len], &msg[..len / 2]);
                    let mut buf = [0u8; 67];
                    let buf = &mut buf[..len];
                    buf.copy_from_slice(msg);
                    let tag = k.encrypt_in_place(nonce, aad, buf).unwrap();
                    assert!(len == 0 || buf != msg);
                    let mut bad = tag;
                    bad[15] ^= 1;
                    assert_eq!(
                        k.decrypt_in_place(nonce, aad, buf, &bad),
                        Err(Error::TagMismatch)
                    );
                    k.decrypt_in_place(nonce, aad, buf, &tag).unwrap();
                    assert_eq!(buf, msg);
                }
            }
        }
    }

    /// One-shot encryption and decryption of long messages agree with the
    /// streaming functions, and a wrong tag leaves the ciphertext as it was.
    #[test]
    fn long_one_shot() {
        let msg: [u8; 4111] = core::array::from_fn(|i| (i * 31 + 7) as u8);
        let aad = [3u8; 21];
        let nonce = [5u8; 12];
        for key_len in [16, 24, 32] {
            let k = AesGcm::new(&[0x42; 32][..key_len]).unwrap();
            for len in [255, 256, 257, 511, 512, 529, 1024, 4096, 4111] {
                let mut ct = msg;
                let ct = &mut ct[..len];
                let tag = k.encrypt_in_place(&nonce, &aad, ct).unwrap();
                let mut e = k.encryptor(&nonce).unwrap();
                e.update_aad(&aad).unwrap();
                let mut s = msg;
                e.update(&mut s[..len]).unwrap();
                assert_eq!(&s[..len], &ct[..]);
                assert_eq!(e.finalize(), tag);

                let mut bad = tag;
                bad[0] ^= 0x80;
                let mut buf = msg;
                let buf = &mut buf[..len];
                buf.copy_from_slice(ct);
                assert_eq!(
                    k.decrypt_in_place(&nonce, &aad, buf, &bad),
                    Err(Error::TagMismatch)
                );
                assert_eq!(&buf[..], &ct[..]);
                k.decrypt_in_place(&nonce, &aad, buf, &tag).unwrap();
                assert_eq!(buf, &msg[..len]);
            }
        }
    }

    /// One-shot, streaming, out-of-place and gathering encryption agree for
    /// long texts with every number of bytes after their whole blocks, every
    /// number of whole blocks from 16 to 41 (alone or with part of a block
    /// after them), and the lengths around the prepared functions' loops,
    /// after additional data of none, part of and whole blocks; decryption,
    /// in place, out of place and streaming, undoes it, and a wrong tag
    /// leaves the ciphertext as it was (in place) or zeroes the output (out
    /// of place).
    #[test]
    fn paths_agree() {
        let msg: [u8; 3100] = core::array::from_fn(|i| (i * 13 + 1) as u8);
        let nonce = [2u8; 12];
        let aad = [9u8; 17];
        let lens = (1024..=1040)
            .chain((256..=656).step_by(16).flat_map(|l| [l, l + 5]))
            .chain([
                0, 1, 15, 16, 17, 100, 255, 300, 511, 512, 513, 767, 768, 769,
            ])
            .chain([
                1300, 1535, 1536, 2048, 2303, 2304, 2305, 3071, 3072, 3073, 3100,
            ]);
        for key_len in [16, 24, 32] {
            let k = AesGcm::new(&[0x5a; 32][..key_len]).unwrap();
            for len in lens.clone() {
                for al in [0, 5, 16, 17] {
                    let aad = &aad[..al];
                    let mut ct = msg;
                    let tag = k.encrypt_in_place(&nonce, aad, &mut ct[..len]).unwrap();
                    let ct = &ct[..len];
                    // Streaming, in three updates, and decrypting back.
                    let mut e = k.encryptor(&nonce).unwrap();
                    e.update_aad(aad).unwrap();
                    let mut s = msg;
                    let (x, rest) = s[..len].split_at_mut(len / 3);
                    let (y, z) = rest.split_at_mut(rest.len() / 2);
                    for part in [x, y, z] {
                        e.update(part).unwrap();
                    }
                    assert_eq!((&s[..len], e.finalize()), (ct, tag));
                    let mut d = k.decryptor(&nonce).unwrap();
                    d.update_aad(aad).unwrap();
                    d.update(&mut s[..len]).unwrap();
                    d.finalize(&tag).unwrap();
                    assert_eq!(&s[..len], &msg[..len]);
                    // In place, with a wrong tag and the right one.
                    let mut buf = msg;
                    let buf = &mut buf[..len];
                    buf.copy_from_slice(ct);
                    let mut bad = tag;
                    bad[0] ^= 1;
                    assert_eq!(
                        k.decrypt_in_place(&nonce, aad, buf, &bad),
                        Err(Error::TagMismatch)
                    );
                    assert_eq!(&buf[..], ct);
                    k.decrypt_in_place(&nonce, aad, buf, &tag).unwrap();
                    assert_eq!(&buf[..], &msg[..len]);
                    // Out of place, and a wrong tag zeroes the output.
                    let mut out = [0x55u8; 3100];
                    k.decrypt(&nonce, aad, ct, &tag, &mut out[..len]).unwrap();
                    assert_eq!(&out[..len], &msg[..len]);
                    let r = k.decrypt(&nonce, aad, ct, &bad, &mut out[..len]);
                    assert_eq!(r, Err(Error::TagMismatch));
                    assert!(out[..len].iter().all(|&x| x == 0));
                    // Gathering pieces: one; a last of 1 byte (a TLS 1.3
                    // record's content type), of none (a TLS 1.2 record's),
                    // of 16 and of 17; three; empty pieces around and
                    // between them; pieces after one ending inside a block,
                    // shorter than the bytes that end it, ending it exactly,
                    // and longer; and as many pieces as `encrypt` takes.
                    let m = &msg[..len];
                    let (a, b) = m.split_at(len.saturating_sub(17));
                    let (b, c) = b.split_at(b.len().min(1));
                    let t = len.saturating_sub(16);
                    let mut many: [&[u8]; AesGcm::MAX_PIECES] = [&[]; AesGcm::MAX_PIECES];
                    let chunks = m.chunks(len.div_ceil(AesGcm::MAX_PIECES).max(1));
                    for (piece, chunk) in many.iter_mut().zip(chunks) {
                        *piece = chunk;
                    }
                    let ways: [&[&[u8]]; 9] = [
                        &[m],
                        &[&m[..len.saturating_sub(1)], &m[len.saturating_sub(1)..]],
                        &[m, &[]],
                        &[&m[..t], &m[t..]],
                        &[a, b, c],
                        &[&[], a, &[], &[], b, c, &[]],
                        &[
                            &m[..len.min(5)],
                            &m[len.min(5)..len.min(7)],
                            &m[len.min(7)..],
                        ],
                        &[
                            &m[..len.min(1)],
                            &m[len.min(1)..len.min(32)],
                            &m[len.min(32)..],
                        ],
                        &many,
                    ];
                    for pieces in ways {
                        let mut out = [0u8; 3100];
                        let r = k.encrypt(&nonce, aad, pieces, &mut out[..len]);
                        assert_eq!((&out[..len], r), (ct, Ok(tag)));
                    }
                }
            }
        }
    }

    /// A clone of a key is the same key, which outlives the original.
    #[test]
    fn key_clone() {
        let nonce = [7u8; 12];
        let k = AesGcm::new(&[0x3c; 24]).unwrap();
        let mut a = [1u8; 700];
        let tag = k.encrypt_in_place(&nonce, b"ad", &mut a).unwrap();
        let c = k.clone();
        drop(k);
        let mut b = [1u8; 700];
        assert_eq!(c.encrypt_in_place(&nonce, b"ad", &mut b), Ok(tag));
        assert_eq!(a, b);
    }

    /// Streaming a long message in three updates, split on and off block
    /// boundaries, agrees with the one-shot functions, in both directions.
    #[test]
    fn long_stream() {
        let msg: [u8; 1100] = core::array::from_fn(|i| (i * 7 + 3) as u8);
        let aad = [6u8; 13];
        let nonce = [8u8; 12];
        let k = AesGcm::new(&[0x24; 16]).unwrap();
        let mut ct = msg;
        let tag = k.encrypt_in_place(&nonce, &aad, &mut ct).unwrap();
        let splits = [
            (0, 1100),
            (1, 300),
            (15, 16),
            (16, 529),
            (17, 1099),
            (255, 256),
            (300, 1100),
            (513, 514),
        ];
        for (a, b) in splits {
            let mut e = k.encryptor(&nonce).unwrap();
            e.update_aad(&aad).unwrap();
            let mut buf = msg;
            let (x, rest) = buf.split_at_mut(a);
            let (y, z) = rest.split_at_mut(b - a);
            e.update(x).unwrap();
            e.update(y).unwrap();
            e.update(z).unwrap();
            assert_eq!(buf, ct);
            assert_eq!(e.finalize(), tag);

            let mut d = k.decryptor(&nonce).unwrap();
            d.update_aad(&aad).unwrap();
            let (x, rest) = buf.split_at_mut(a);
            let (y, z) = rest.split_at_mut(b - a);
            d.update(x).unwrap();
            d.update(y).unwrap();
            d.update(z).unwrap();
            assert_eq!(buf, msg);
            assert_eq!(d.finalize(&tag), Ok(()));
        }
    }

    /// Streaming, with the additional data or the text split at every
    /// point (around block boundaries), agrees with the one-shot functions,
    /// in both directions, with one key for every message.
    #[test]
    fn stream() {
        let key = [7u8; 16];
        let nonce = [9u8; 12];
        let aad: [u8; 40] = core::array::from_fn(|i| i as u8);
        let msg: [u8; 50] = core::array::from_fn(|i| (i as u8).wrapping_mul(13));
        let k = AesGcm::new(&key).unwrap();
        let mut ct = msg;
        let tag = k.encrypt_in_place(&nonce, &aad, &mut ct).unwrap();
        // Every split of one, with the other split in the middle.
        let splits = (0..=aad.len())
            .map(|a| (a, msg.len() / 2))
            .chain((0..=msg.len()).map(|m| (aad.len() / 2, m)));
        for (a, m) in splits {
            let mut e = k.encryptor(&nonce).unwrap();
            e.update_aad(&aad[..a]).unwrap();
            e.update_aad(&aad[a..]).unwrap();
            let mut buf = msg;
            let (x, y) = buf.split_at_mut(m);
            e.update(x).unwrap();
            e.update(y).unwrap();
            assert_eq!(buf, ct);
            assert_eq!(e.finalize(), tag);

            let mut d = k.decryptor(&nonce).unwrap();
            d.update_aad(&aad[..a]).unwrap();
            d.update_aad(&aad[a..]).unwrap();
            let (x, y) = buf.split_at_mut(m);
            d.update(x).unwrap();
            d.update(y).unwrap();
            assert_eq!(buf, msg);
            assert_eq!(d.finalize(&tag), Ok(()));
        }
        // A byte at a time.
        let mut e = k.encryptor(&nonce).unwrap();
        for b in aad.chunks(1) {
            e.update_aad(b).unwrap();
        }
        let mut buf = msg;
        for b in buf.chunks_mut(1) {
            e.update(b).unwrap();
        }
        assert_eq!(buf, ct);
        assert_eq!(e.finalize(), tag);
        // Without text, or without either.
        let mut t = [0u8; 0];
        let tag = k.encrypt_in_place(&nonce, &aad[..5], &mut t).unwrap();
        let mut e = k.encryptor(&nonce).unwrap();
        e.update_aad(&aad[..5]).unwrap();
        assert_eq!(e.finalize(), tag);
        let tag = k.encrypt_in_place(&nonce, &[], &mut t).unwrap();
        let e = k.encryptor(&nonce).unwrap();
        assert_eq!(e.finalize(), tag);
        let d = k.decryptor(&nonce).unwrap();
        assert_eq!(d.finalize(&tag), Ok(()));
    }

    /// A clone continues the message independently of the original.
    #[test]
    fn stream_clone() {
        let k = AesGcm::new(&[1; 24]).unwrap();
        let nonce = [2u8; 12];
        let msg = [3u8; 20];
        let mut ct = msg;
        let tag = k.encrypt_in_place(&nonce, &[4; 8], &mut ct).unwrap();

        let mut e = k.encryptor(&nonce).unwrap();
        e.update_aad(&[4; 8]).unwrap();
        let mut other = e.clone();
        other.update(&mut [0; 1]).unwrap();
        let mut buf = msg;
        e.update(&mut buf).unwrap();
        assert_eq!((buf, e.finalize()), (ct, tag));
        assert_ne!(other.finalize(), tag);

        let mut d = k.decryptor(&nonce).unwrap();
        d.update_aad(&[4; 8]).unwrap();
        let mut other = d.clone();
        other.update(&mut [0; 1]).unwrap();
        let mut buf = ct;
        d.update(&mut buf).unwrap();
        assert_eq!(buf, msg);
        assert_eq!(d.finalize(&tag), Ok(()));
        assert_eq!(other.finalize(&tag), Err(Error::TagMismatch));
    }

    /// A tag truncated to `N` bytes: its first `N` bytes are accepted, one
    /// at a time and streaming, and any other `N` bytes (a bit flipped in
    /// each byte) are rejected, leaving the ciphertext unchanged.
    fn truncated<const N: usize>() {
        let key = [3u8; 16];
        let nonce = [4u8; 12];
        let aad = [5u8; 20];
        let msg: [u8; 37] = core::array::from_fn(|i| i as u8);
        let k = AesGcm::new(&key).unwrap();
        let mut ct = msg;
        let full = k.encrypt_in_place(&nonce, &aad, &mut ct).unwrap();
        let tag: [u8; N] = full[..N].try_into().unwrap();
        let mut buf = ct;
        k.decrypt_in_place_truncated(&nonce, &aad, &mut buf, &tag)
            .unwrap();
        assert_eq!(buf, msg);
        let stream = |tag: &[u8; N]| {
            let mut d = k.decryptor(&nonce).unwrap();
            d.update_aad(&aad).unwrap();
            let mut buf = ct;
            d.update(&mut buf).unwrap();
            assert_eq!(buf, msg);
            d.finalize_truncated(tag)
        };
        assert_eq!(stream(&tag), Ok(()));
        for i in 0..N {
            let mut bad = tag;
            bad[i] ^= 0x80;
            let mut buf = ct;
            assert_eq!(
                k.decrypt_in_place_truncated(&nonce, &aad, &mut buf, &bad),
                Err(Error::TagMismatch)
            );
            assert_eq!(buf, ct);
            assert_eq!(stream(&bad), Err(Error::TagMismatch));
        }
    }

    /// Empty messages, partial blocks, and prepared-context boundaries.
    fn truncated_boundaries<const N: usize>() {
        let key = [3u8; 32];
        let nonce = [4u8; 13];
        let aad = [5u8; 20];
        let msg: [u8; 2057] = core::array::from_fn(|i| i as u8);
        for key_len in [16, 24, 32] {
            let k = AesGcm::new(&key[..key_len]).unwrap();
            for nonce_len in [12, 13] {
                let nonce = &nonce[..nonce_len];
                for len in [
                    0, 1, 15, 16, 17, 127, 128, 255, 256, 257, 511, 512, 513, 1023, 1024, 1025,
                    2057,
                ] {
                    let aad = &aad[..if len % 2 == 0 { 0 } else { aad.len() }];
                    let mut ct = msg;
                    let full = k.encrypt_in_place(nonce, aad, &mut ct[..len]).unwrap();
                    let tag: [u8; N] = full[..N].try_into().unwrap();
                    let mut buf = ct;
                    k.decrypt_in_place_truncated(nonce, aad, &mut buf[..len], &tag)
                        .unwrap();
                    assert_eq!(&buf[..len], &msg[..len]);
                    let mut d = k.decryptor(nonce).unwrap();
                    d.update_aad(aad).unwrap();
                    buf = ct;
                    for chunk in buf[..len].chunks_mut(17) {
                        d.update(chunk).unwrap();
                    }
                    d.finalize_truncated(&tag).unwrap();
                    assert_eq!(&buf[..len], &msg[..len]);
                    let mut bad = tag;
                    bad[N - 1] ^= 1;
                    buf = ct;
                    assert_eq!(
                        k.decrypt_in_place_truncated(nonce, aad, &mut buf[..len], &bad),
                        Err(Error::TagMismatch)
                    );
                    assert_eq!(buf, ct);
                }
            }
            let mut empty = [];
            assert_eq!(
                k.decrypt_in_place_truncated(&[], &aad, &mut empty, &[0; N]),
                Err(Error::InvalidNonceLength)
            );
        }
    }

    /// Every supported tag length, including the extensions to §5.2.1.2.
    #[test]
    fn truncated_tags() {
        truncated::<4>();
        truncated::<5>();
        truncated::<6>();
        truncated::<7>();
        truncated::<8>();
        truncated::<9>();
        truncated::<10>();
        truncated::<11>();
        truncated::<12>();
        truncated::<13>();
        truncated::<14>();
        truncated::<15>();
        truncated::<16>();
        truncated_boundaries::<5>();
        truncated_boundaries::<6>();
        truncated_boundaries::<7>();
        truncated_boundaries::<9>();
        truncated_boundaries::<10>();
        truncated_boundaries::<11>();
    }

    /// Out-of-place encryption of a plaintext in pieces matches in-place
    /// encryption, after additional data of whole blocks, of a partial block
    /// and of none, for pieces split on and off block boundaries (empty ones
    /// included), the most pieces, and an empty text; an output of the wrong
    /// length and too many pieces are refused.
    #[test]
    fn out_of_place() {
        let k = AesGcm::new(&[3; 16]).unwrap();
        let nonce = [5u8; 12];
        let msg: [u8; 300] = core::array::from_fn(|i| (i as u8).wrapping_mul(29));
        for aad_len in [0, 5, 16, 20] {
            let aad = &msg[..aad_len];
            for len in [0, 1, 16, 17, 300] {
                let mut want = msg;
                let want_tag = k.encrypt_in_place(&nonce, aad, &mut want[..len]).unwrap();
                let m = &msg[..len];
                let (h, q) = (len / 2, (len / 2 + 16).min(len));
                let one: [&[u8]; 1] = [m];
                let two: [&[u8]; 2] = [&m[..h], &m[h..]];
                let five: [&[u8]; 5] = [&[], &m[..h], &m[h..h], &m[h..q], &m[q..]];
                for pieces in [&one[..], &two, &five] {
                    let mut out = [0u8; 300];
                    let tag = k.encrypt(&nonce, aad, pieces, &mut out[..len]);
                    assert_eq!((&out[..len], tag), (&want[..len], Ok(want_tag)));
                }
            }
        }
        let n = AesGcm::MAX_PIECES;
        let mut want = msg;
        let want_tag = k.encrypt_in_place(&nonce, &[], &mut want[..n]).unwrap();
        let bytes: [&[u8]; AesGcm::MAX_PIECES] = core::array::from_fn(|i| &msg[i..i + 1]);
        let mut out = [0u8; AesGcm::MAX_PIECES];
        let tag = k.encrypt(&nonce, &[], &bytes, &mut out);
        assert_eq!((&out[..], tag), (&want[..n], Ok(want_tag)));
        let empty = [&msg[..0]; AesGcm::MAX_PIECES + 1];
        let tag = k.encrypt(&nonce, &[], &empty, &mut []);
        assert_eq!(tag, Err(Error::TooManyPieces));
        assert_eq!(
            k.encrypt(&nonce, &[], &[], &mut []),
            k.encrypt(&nonce, &[], &[&[]], &mut [])
        );
        let mut out = [0u8; 4];
        let tag = k.encrypt(&nonce, &[], &[&msg[..1], &msg[1..3]], &mut out);
        assert_eq!(tag, Err(Error::InvalidOutputLength));
        let t = [0u8; 16];
        assert_eq!(
            k.decrypt(&nonce, &[], &msg[..3], &t, &mut out),
            Err(Error::InvalidOutputLength)
        );
        assert_eq!(
            k.decrypt(&[], &[], &msg[..4], &t, &mut out),
            Err(Error::InvalidNonceLength)
        );
        assert_eq!(out, [0; 4]);
        assert_eq!(
            k.encrypt(&[], &[], &[&msg[..4]], &mut out),
            Err(Error::InvalidNonceLength)
        );
    }

    #[test]
    fn errors() {
        assert_eq!(AesGcm::new(&[0; 15]).err(), Some(InvalidKeyLength));
        let k = AesGcm::new(&[0; 32]).unwrap();
        let mut buf = [0u8; 3];
        assert_eq!(
            k.encrypt_in_place(&[], &[], &mut buf),
            Err(Error::InvalidNonceLength)
        );
        assert_eq!(
            k.decrypt_in_place(&[], &[], &mut buf, &[0; 16]),
            Err(Error::InvalidNonceLength)
        );
        assert_eq!(
            k.decrypt_in_place(&[0; 12], &[], &mut buf, &[0; 16]),
            Err(Error::TagMismatch)
        );
        assert_eq!(buf, [0; 3]);

        assert_eq!(k.encryptor(&[]).err(), Some(Error::InvalidNonceLength));
        assert_eq!(k.decryptor(&[]).err(), Some(Error::InvalidNonceLength));
        let mut e = k.encryptor(&[0; 12]).unwrap();
        e.update(&mut buf).unwrap();
        assert_eq!(e.update_aad(&[1]), Err(Error::AadAfterText));
        let mut d = k.decryptor(&[0; 12]).unwrap();
        d.update(&mut buf).unwrap();
        assert_eq!(d.update_aad(&[1]), Err(Error::AadAfterText));
        assert_eq!(d.finalize(&[0; 16]), Err(Error::TagMismatch));

        // The length limits (§5.2.1.1), which no test can reach with real
        // buffers.
        assert_eq!(add_len(MAX_TEXT - 1, 1, MAX_TEXT), Ok(MAX_TEXT));
        assert_eq!(add_len(MAX_TEXT, 1, MAX_TEXT), Err(()));
        assert_eq!(add_len(MAX_AAD, 0, MAX_AAD), Ok(MAX_AAD));
        assert_eq!(add_len(u64::MAX, 1, MAX_AAD), Err(()));
        let mut e = k.encryptor(&[0; 12]).unwrap();
        e.stream.text_len = MAX_TEXT;
        assert_eq!(e.update(&mut buf), Err(Error::InvalidTextLength));
        e.stream.aad_len = MAX_AAD;
        e.stream.in_text = false;
        assert_eq!(e.update_aad(&[1]), Err(Error::InvalidAadLength));
        let mut d = k.decryptor(&[0; 12]).unwrap();
        d.stream.text_len = MAX_TEXT;
        assert_eq!(d.update(&mut buf), Err(Error::InvalidTextLength));
        d.stream.aad_len = MAX_AAD;
        assert_eq!(d.update_aad(&[1]), Err(Error::InvalidAadLength));
    }
}
