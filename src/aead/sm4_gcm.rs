//! SM4-GCM: GCM (NIST SP 800-38D) with SM4 (GB/T 32907-2016, transcribed in
//! draft-ribose-cfrg-sm4-10), the `AEAD_SM4_GCM` of RFC 8998 §3.5.1, with
//! 16-byte keys, for whole messages and incrementally.
//!
//! A nonce must never be used twice with the same key. **An
//! [`Sm4GcmDecryptor`]'s `update` returns plaintext that has not been
//! authenticated**: act on none of it before its `finalize` succeeds, or, when
//! the message fits in memory, use [`Sm4Gcm::decrypt_in_place`], which checks
//! the tag before it decrypts.
//!
//! # Tags
//!
//! Encryption returns the full 16-byte tag (RFC 8998's length); a protocol that
//! sends a shorter one sends its first bytes. Decryption takes a `&[u8; 16]`
//! ([`Sm4Gcm::decrypt_in_place`], [`Sm4GcmDecryptor::finalize`]) or, for a
//! truncated tag, a `&[u8; N]` with `N` from 4 to 16 fixed at compile time
//! ([`Sm4Gcm::decrypt_in_place_truncated`],
//! [`Sm4GcmDecryptor::finalize_truncated`]), as AES-GCM's does: see
//! [`crate::aead::aes_gcm`] for why the length is never a slice's, and for which
//! lengths SP 800-38D allows.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "arm",
    target_arch = "aarch64",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::align::CacheAligned;
use crate::arch::dispatch::sm4_gcm::{
    vg_sm4_gcm_init_auto, vg_sm4_gcm_open_auto, vg_sm4_gcm_seal_auto, vg_sm4_gcm_stream_aad_auto,
    vg_sm4_gcm_stream_decrypt_auto, vg_sm4_gcm_stream_encrypt_auto, vg_sm4_gcm_stream_finish_auto,
    vg_sm4_gcm_stream_init_auto, vg_sm4_gcm_stream_verify_auto,
};
use crate::zeroize::zeroize;

/// A 16-byte block: a tag.
pub type Block = [u8; 16];

/// The longest plaintext, in bytes: `2^39 − 256` bits (§5.2.1.1).
const MAX_TEXT: u64 = (1 << 36) - 32;
/// The longest additional data, in bytes: `2^64 − 1` bits, rounded down
/// to whole bytes (§5.2.1.1).
const MAX_AAD: u64 = (1 << 61) - 1;

/// Why an SM4-GCM operation failed.
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
    /// [`Sm4GcmEncryptor::update_aad`] or [`Sm4GcmDecryptor::update_aad`]
    /// was called after `update`: GCM authenticates all of the additional
    /// data before the text.
    AadAfterText,
}

crate::error::impl_error! {
    Error {
        InvalidNonceLength => "SM4-GCM nonce is empty",
        InvalidTextLength => "SM4-GCM text is too long",
        InvalidAadLength => "SM4-GCM additional data is too long",
        TagMismatch => "SM4-GCM tag does not match",
        AadAfterText => "SM4-GCM additional data after the text",
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
                "an SM4-GCM tag is between 4 and 16 bytes long"
            )
        }
    };
}

/// An SM4-GCM key: its key context (SM4's key schedule and the hash subkey
/// `H`). Its [`encrypt_in_place`](Self::encrypt_in_place) and
/// [`decrypt_in_place`](Self::decrypt_in_place) (or
/// [`decrypt_in_place_truncated`](Self::decrypt_in_place_truncated)) are the
/// one-shot AEAD; [`encryptor`](Self::encryptor) and
/// [`decryptor`](Self::decryptor) start incremental ones.
#[derive(Clone)]
pub struct Sm4Gcm {
    /// The key context `vg_sm4_gcm_init` writes (`VG.Spec.Sm4.Gcm.KeyRepr`).
    ctx: CacheAligned<[u64; 32]>,
}

impl Drop for Sm4Gcm {
    /// Wipes the key context.
    fn drop(&mut self) {
        zeroize(&mut self.ctx.0);
    }
}

impl Sm4Gcm {
    /// The size of a full tag, in bytes.
    pub const TAG_SIZE: usize = 16;

    /// Prepares a 16-byte SM4 key.
    pub fn new(key: &[u8; 16]) -> Self {
        crate::dit::enter!(dit);
        let mut k = Sm4Gcm {
            ctx: CacheAligned([0; 32]),
        };
        // SAFETY: `key` is valid for reads of 16 bytes and `k.ctx` for reads
        // and writes of 256. They are distinct objects, so they do not
        // overlap each other or anything on the stack, or wrap around the end
        // of the address space. The dispatcher calls only an implementation
        // the CPU has the features of.
        unsafe { vg_sm4_gcm_init_auto(dit, key, &mut k.ctx.0) };
        k
    }

    /// GCM-AE (§7.1): encrypts `data` in place under `nonce`, and returns
    /// the 16-byte tag authenticating the ciphertext and `aad`. A caller that
    /// wants a shorter tag truncates it (keeping its first bytes), and
    /// decrypts with [`decrypt_in_place_truncated`](Self::decrypt_in_place_truncated).
    ///
    /// The nonce may have any nonzero length; 12 bytes is RFC 8998's (and
    /// the fastest) one. A nonce must never be used twice with the same key.
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
        let mut tag: Block = [0; 16];
        // SAFETY: `self.ctx` is the key context `vg_sm4_gcm_init` wrote,
        // valid for reads of 256 bytes; `nonce` and `aad` are valid for reads
        // and `data` for reads and writes of their lengths, and `tag` (a
        // local) for reads and writes of 16 bytes. They are distinct objects
        // (`data` a unique borrow), so the writable ones overlap nothing
        // else, nor anything on the stack, and none wraps around the end of
        // the address space. The dispatcher calls only an implementation the
        // CPU has the features of.
        unsafe {
            vg_sm4_gcm_seal_auto(
                dit,
                &self.ctx.0,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
                &mut tag,
            )
        };
        Ok(tag)
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
    /// `N` must be between 4 and 16, inclusive; any other length is an
    /// error when the call is compiled (see the
    /// [module documentation](self#tags)).
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
        // SAFETY: as in `encrypt_in_place`, with the received tag `tag` valid
        // for reads of its `N` bytes, between 4 and 16 (`vg_sm4_gcm_open`
        // rejects any other length).
        let ok = unsafe {
            vg_sm4_gcm_open_auto(
                dit,
                &self.ctx.0,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
                tag.as_ptr(),
                N,
            )
        };
        if ok == 1 {
            Ok(())
        } else {
            Err(Error::TagMismatch)
        }
    }

    /// Starts an incremental encryption under `nonce`.
    pub fn encryptor(&self, nonce: &[u8]) -> Result<Sm4GcmEncryptor<'_>, Error> {
        crate::dit::enter!(dit);
        Ok(Sm4GcmEncryptor {
            stream: Stream::new(dit, self, nonce)?,
        })
    }

    /// Starts an incremental decryption under `nonce`.
    pub fn decryptor(&self, nonce: &[u8]) -> Result<Sm4GcmDecryptor<'_>, Error> {
        crate::dit::enter!(dit);
        Ok(Sm4GcmDecryptor {
            stream: Stream::new(dit, self, nonce)?,
        })
    }
}

/// The state of an incremental encryption or decryption (`DECRYPT`), which
/// [`Sm4GcmEncryptor`] and [`Sm4GcmDecryptor`] wrap: the key, the streaming
/// state, and the lengths absorbed so far.
#[derive(Clone)]
struct Stream<'a, const DECRYPT: bool> {
    key: &'a Sm4Gcm,
    /// The streaming state `vg_sm4_gcm_stream_init` writes and the other
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
        zeroize(&mut self.state.0);
    }
}

impl<'a, const DECRYPT: bool> Stream<'a, DECRYPT> {
    /// Starts a message under `key` and `nonce`.
    fn new(dit: crate::dit::Dit<'_>, key: &'a Sm4Gcm, nonce: &[u8]) -> Result<Self, Error> {
        check_nonce(nonce)?;
        let mut s = Stream {
            key,
            state: CacheAligned([0; 10]),
            aad_len: 0,
            text_len: 0,
            in_text: false,
        };
        // SAFETY: `key.ctx` is a key context (as in
        // `Sm4Gcm::encrypt_in_place`), valid for reads of 256 bytes, `nonce`
        // for reads of `nonce.len()`, and `s.state` for reads and writes of
        // 80. They are distinct objects, so the writable one overlaps nothing
        // else, nor anything on the stack, and none wraps around. The
        // dispatcher calls only an implementation the CPU has the features
        // of.
        unsafe {
            vg_sm4_gcm_stream_init_auto(
                dit,
                &key.ctx.0,
                nonce.as_ptr(),
                nonce.len(),
                &mut s.state.0,
            )
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
            vg_sm4_gcm_stream_aad_auto(
                dit,
                &self.key.ctx.0,
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
        let f = if DECRYPT {
            vg_sm4_gcm_stream_decrypt_auto
        } else {
            vg_sm4_gcm_stream_encrypt_auto
        };
        // SAFETY: as in `new`, with `data` valid for reads and writes of
        // `data.len()` bytes (a unique borrow, so it overlaps nothing else);
        // `self.state` represents a message with `self.aad_len` bytes of
        // additional data and `self.text_len` of text.
        unsafe {
            f(
                dit,
                &self.key.ctx.0,
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
            vg_sm4_gcm_stream_finish_auto(
                dit,
                &self.key.ctx.0,
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
            vg_sm4_gcm_stream_verify_auto(
                dit,
                &self.key.ctx.0,
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

/// An incremental SM4-GCM encryption, from [`Sm4Gcm::encryptor`]: the
/// additional data with [`update_aad`](Self::update_aad), then the plaintext
/// with [`update`](Self::update), in pieces of any length, and the tag from
/// [`finalize`](Self::finalize).
#[derive(Clone)]
pub struct Sm4GcmEncryptor<'a> {
    stream: Stream<'a, false>,
}

impl Sm4GcmEncryptor<'_> {
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
    /// that sends a shorter tag sends its first bytes.
    pub fn finalize(self) -> Block {
        crate::dit::enter!(dit);
        self.stream.finish(dit)
    }
}

/// An incremental SM4-GCM decryption, from [`Sm4Gcm::decryptor`]: the
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
/// whole message fits in memory, [`Sm4Gcm::decrypt_in_place`] checks the tag
/// before it decrypts.
#[derive(Clone)]
pub struct Sm4GcmDecryptor<'a> {
    stream: Stream<'a, true>,
}

impl Sm4GcmDecryptor<'_> {
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
    pub fn finalize(self, tag: &[u8; 16]) -> Result<(), Error> {
        self.finalize_truncated(tag)
    }

    /// Finishes the message and checks that `tag` is the first `N` bytes of
    /// its tag. If they differ, this fails, and nothing may act on the
    /// plaintext [`update`](Self::update) returned.
    ///
    /// `N` must be between 4 and 16, inclusive; any other length is an
    /// error when the call is compiled (see the
    /// [module documentation](self#tags)).
    pub fn finalize_truncated<const N: usize>(self, tag: &[u8; N]) -> Result<(), Error> {
        crate::dit::enter!(dit);
        assert_tag_length!(N);
        self.stream.verify(dit, tag)
    }
}

#[cfg(test)]
mod tests {
    extern crate std;

    use super::{Error, MAX_AAD, MAX_TEXT, Sm4Gcm, Stream, add_len};

    /// The text of a message is checked against its limits before
    /// anything is encrypted, and so is its additional data.
    #[test]
    fn lengths() {
        assert_eq!(add_len(MAX_TEXT - 1, 1, MAX_TEXT), Ok(MAX_TEXT));
        assert_eq!(add_len(MAX_TEXT, 1, MAX_TEXT), Err(()));
        assert_eq!(add_len(u64::MAX, 1, u64::MAX), Err(()));
        let key = Sm4Gcm::new(&[1; 16]);
        let dit = crate::dit::public(crate::dit::Why::Test);
        let mut s = Stream::<false>::new(dit, &key, &[0; 12]).unwrap();
        s.text_len = MAX_TEXT;
        let mut data = [9; 3];
        assert_eq!(s.update(dit, &mut data), Err(Error::InvalidTextLength));
        assert_eq!(data, [9; 3]);
        let mut s = Stream::<true>::new(dit, &key, &[0; 12]).unwrap();
        s.aad_len = MAX_AAD;
        assert_eq!(s.update_aad(dit, &[0]), Err(Error::InvalidAadLength));
        assert_eq!(s.update_aad(dit, &[]), Ok(()));
    }

    #[test]
    fn errors() {
        for (e, msg) in [
            (Error::InvalidNonceLength, "SM4-GCM nonce is empty"),
            (Error::InvalidTextLength, "SM4-GCM text is too long"),
            (
                Error::InvalidAadLength,
                "SM4-GCM additional data is too long",
            ),
            (Error::TagMismatch, "SM4-GCM tag does not match"),
            (
                Error::AadAfterText,
                "SM4-GCM additional data after the text",
            ),
        ] {
            assert_eq!(std::format!("{e}"), msg);
        }
    }
}
