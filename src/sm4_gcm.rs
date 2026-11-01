//! SM4-GCM: GCM (NIST SP 800-38D) with SM4 (GB/T 32907-2016, transcribed in
//! the Internet-Draft draft-ribose-cfrg-sm4-10) as its block cipher, the
//! `AEAD_SM4_GCM` of RFC 8998 §3.5.1, with 16-byte keys.
//!
//! Key setup, in-place AEAD and the streaming operations are verified
//! assembly, with the contracts of `VG.Spec.Sm4.Gcm`: `vg_sm4_gcm_init`
//! (`initContract`) writes the key context (SM4's key schedule and the hash
//! subkey `H`, in AES-GCM's layout), `vg_sm4_gcm_seal` and `vg_sm4_gcm_open`
//! (`sealContract`, `openContract`) are GCM-AE and GCM-AD (§7), and
//! `vg_sm4_gcm_stream_init`, `_aad`, `_encrypt`, `_decrypt`, `_finish` and
//! `_verify` keep a streaming state (`VG.Spec.Gcm.StreamRepr`). `open` and
//! `verify` check the tag, in constant time, and `open` decrypts only if it
//! matches. This module checks the lengths of §5.2.1.1, which the assembly
//! does not, and holds the key context and the state.
//!
//! An [`Sm4Gcm`] is a key: it encrypts and decrypts whole messages at once,
//! and starts incremental ones with [`Sm4Gcm::encryptor`] and
//! [`Sm4Gcm::decryptor`], which borrow it. **An [`Sm4GcmDecryptor`]'s
//! `update` returns plaintext that has not been authenticated yet**: nothing
//! may act on it before its `finalize` has succeeded. When the whole message
//! fits in memory, [`Sm4Gcm::decrypt_in_place`] checks the tag before it
//! decrypts.
//!
//! The functions but `init` have variants, with the same contracts, one for
//! each of GHASH's (`vg_ghash`'s), chosen on CPUs with the features of `seal`'s
//! `_FEATURES` constants (which are every other function's): on x86-64, the
//! `_vpclmul` ones, then the `_pclmul` ones; on x86, the `_pclmul` ones; on
//! AArch64, the `_aes` ones. Which one a key calls depends only on the CPU.
//!
//! # Tags
//!
//! Encryption returns the full 16-byte tag (RFC 8998's length); a protocol
//! that sends a shorter one sends its first bytes. Decryption takes a
//! `&[u8; 16]` ([`Sm4Gcm::decrypt_in_place`], [`Sm4GcmDecryptor::finalize`]),
//! or, for a protocol that truncates the tag, a `&[u8; N]` whose length `N`
//! is a type parameter ([`Sm4Gcm::decrypt_in_place_truncated`],
//! [`Sm4GcmDecryptor::finalize_truncated`]): 4 through 16 bytes, checked at
//! compile time, as AES-GCM's (see [`crate::aes_gcm`]'s documentation for
//! why the length is never taken from a slice).

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "arm",
    target_arch = "aarch64",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

#[cfg(target_arch = "aarch64")]
use crate::arch::sm4_gcm::{
    VG_SM4_GCM_SEAL_AES_FEATURES, vg_sm4_gcm_open_aes, vg_sm4_gcm_seal_aes,
    vg_sm4_gcm_stream_aad_aes, vg_sm4_gcm_stream_decrypt_aes, vg_sm4_gcm_stream_encrypt_aes,
    vg_sm4_gcm_stream_finish_aes, vg_sm4_gcm_stream_init_aes, vg_sm4_gcm_stream_verify_aes,
};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::sm4_gcm::{
    VG_SM4_GCM_SEAL_PCLMUL_FEATURES, vg_sm4_gcm_open_pclmul, vg_sm4_gcm_seal_pclmul,
    vg_sm4_gcm_stream_aad_pclmul, vg_sm4_gcm_stream_decrypt_pclmul,
    vg_sm4_gcm_stream_encrypt_pclmul, vg_sm4_gcm_stream_finish_pclmul,
    vg_sm4_gcm_stream_init_pclmul, vg_sm4_gcm_stream_verify_pclmul,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::sm4_gcm::{
    VG_SM4_GCM_SEAL_VPCLMUL_FEATURES, vg_sm4_gcm_open_vpclmul, vg_sm4_gcm_seal_vpclmul,
    vg_sm4_gcm_stream_aad_vpclmul, vg_sm4_gcm_stream_decrypt_vpclmul,
    vg_sm4_gcm_stream_encrypt_vpclmul, vg_sm4_gcm_stream_finish_vpclmul,
    vg_sm4_gcm_stream_init_vpclmul, vg_sm4_gcm_stream_verify_vpclmul,
};
use crate::arch::sm4_gcm::{
    vg_sm4_gcm_init, vg_sm4_gcm_open, vg_sm4_gcm_seal, vg_sm4_gcm_stream_aad,
    vg_sm4_gcm_stream_decrypt, vg_sm4_gcm_stream_encrypt, vg_sm4_gcm_stream_finish,
    vg_sm4_gcm_stream_init, vg_sm4_gcm_stream_verify,
};
use crate::cpu::detected;
use crate::zeroize::zeroize;
use verified_garbage_cpu::Features;

/// A 16-byte block: a tag.
pub type Block = [u8; 16];

/// The longest plaintext, in bytes: `2^39 − 256` bits (§5.2.1.1).
const MAX_TEXT: u64 = (1 << 36) - 32;
/// The longest additional data, in bytes: `2^64 − 1` bits, rounded down
/// to whole bytes (§5.2.1.1).
const MAX_AAD: u64 = (1 << 61) - 1;

/// The implementations of SM4-GCM, one for each of GHASH's (`vg_ghash`'s):
/// each is the instance with its suffix of every `vg_sm4_gcm_*` function but
/// `init`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Ghash {
    /// The baseline ISA.
    Scalar,
    /// PCLMULQDQ: the `_pclmul` instances (x86 and x86-64).
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    Pclmul,
    /// VPCLMULQDQ: the `_vpclmul` instances (x86-64 only).
    #[cfg(target_arch = "x86_64")]
    Vpclmul,
    /// PMULL (FEAT_PMULL, which Rust and `src/cpu.rs` call `aes`): the
    /// `_aes` instances (AArch64 only).
    #[cfg(target_arch = "aarch64")]
    Aes,
}

/// The instance of a function for `ghash`: the baseline one, then the
/// `_pclmul` one (x86 and x86-64), the `_vpclmul` one (x86-64) and the
/// `_aes` one (AArch64).
macro_rules! instance {
    ($ghash:expr, $scalar:ident,
     x86: [$pclmul:ident],
     x86_64: [$vpclmul:ident],
     aarch64: [$aes:ident]) => {
        match $ghash {
            Ghash::Scalar => $scalar,
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            Ghash::Pclmul => $pclmul,
            #[cfg(target_arch = "x86_64")]
            Ghash::Vpclmul => $vpclmul,
            #[cfg(target_arch = "aarch64")]
            Ghash::Aes => $aes,
        }
    };
}

impl Ghash {
    /// The best implementation a CPU with the features `f` can run: the
    /// features of its instances are `seal`'s, which are every other
    /// function's.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    fn select(f: Features) -> Ghash {
        #[cfg(target_arch = "x86_64")]
        if f.contains(VG_SM4_GCM_SEAL_VPCLMUL_FEATURES) {
            return Ghash::Vpclmul;
        }
        if f.contains(VG_SM4_GCM_SEAL_PCLMUL_FEATURES) {
            Ghash::Pclmul
        } else {
            Ghash::Scalar
        }
    }

    /// The best implementation an AArch64 CPU with the features `f` can run.
    #[cfg(target_arch = "aarch64")]
    fn select(f: Features) -> Ghash {
        if f.contains(VG_SM4_GCM_SEAL_AES_FEATURES) {
            Ghash::Aes
        } else {
            Ghash::Scalar
        }
    }

    /// The only implementation on ARMv7, PPC64LE and RISC-V, whatever the CPU.
    #[cfg(any(
        target_arch = "arm",
        all(target_arch = "powerpc64", target_endian = "little"),
        target_arch = "riscv64"
    ))]
    fn select(_: Features) -> Ghash {
        Ghash::Scalar
    }
}

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
    ctx: [u64; 32],
    /// The implementation of GHASH the functions called call.
    ghash: Ghash,
}

impl Drop for Sm4Gcm {
    /// Wipes the key context.
    fn drop(&mut self) {
        zeroize(&mut self.ctx);
    }
}

impl Sm4Gcm {
    /// The size of a full tag, in bytes.
    pub const TAG_SIZE: usize = 16;

    /// Prepares a 16-byte SM4 key.
    pub fn new(key: &[u8; 16]) -> Self {
        let mut k = Sm4Gcm {
            ctx: [0; 32],
            ghash: Ghash::select(detected()),
        };
        // SAFETY: `key` is valid for reads of 16 bytes and `k.ctx` for reads
        // and writes of 256. They are distinct objects, so they do not
        // overlap each other or anything on the stack, or wrap around the end
        // of the address space. The function needs no CPU feature.
        unsafe { vg_sm4_gcm_init(key, &mut k.ctx) };
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
        // Check the lengths before encrypting anything.
        check_nonce(nonce)?;
        add_len(0, data.len(), MAX_TEXT).map_err(|()| Error::InvalidTextLength)?;
        add_len(0, aad.len(), MAX_AAD).map_err(|()| Error::InvalidAadLength)?;
        let seal = instance!(self.ghash, vg_sm4_gcm_seal,
            x86: [vg_sm4_gcm_seal_pclmul],
            x86_64: [vg_sm4_gcm_seal_vpclmul],
            aarch64: [vg_sm4_gcm_seal_aes]);
        let mut tag: Block = [0; 16];
        // SAFETY: `self.ctx` is the key context `vg_sm4_gcm_init` wrote,
        // valid for reads of 256 bytes; `nonce` and `aad` are valid for reads
        // and `data` for reads and writes of their lengths, and `tag` (a
        // local) for reads and writes of 16 bytes. They are distinct objects
        // (`data` a unique borrow), so the writable ones overlap nothing
        // else, nor anything on the stack, and none wraps around the end of
        // the address space. The CPU has the features of the implementation
        // selected.
        unsafe {
            seal(
                &self.ctx,
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
        assert_tag_length!(N);
        check_nonce(nonce)?;
        add_len(0, data.len(), MAX_TEXT).map_err(|()| Error::InvalidTextLength)?;
        add_len(0, aad.len(), MAX_AAD).map_err(|()| Error::InvalidAadLength)?;
        let open = instance!(self.ghash, vg_sm4_gcm_open,
            x86: [vg_sm4_gcm_open_pclmul],
            x86_64: [vg_sm4_gcm_open_vpclmul],
            aarch64: [vg_sm4_gcm_open_aes]);
        // SAFETY: as in `encrypt_in_place`, with the received tag `tag` valid
        // for reads of its `N` bytes, between 4 and 16 (`vg_sm4_gcm_open`
        // rejects any other length).
        let ok = unsafe {
            open(
                &self.ctx,
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
        Ok(Sm4GcmEncryptor {
            stream: Stream::new(self, nonce)?,
        })
    }

    /// Starts an incremental decryption under `nonce`.
    pub fn decryptor(&self, nonce: &[u8]) -> Result<Sm4GcmDecryptor<'_>, Error> {
        Ok(Sm4GcmDecryptor {
            stream: Stream::new(self, nonce)?,
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
    state: [u64; 10],
    aad_len: u64,
    text_len: u64,
    /// Whether [`update`](Self::update) has been called.
    in_text: bool,
}

impl<const DECRYPT: bool> Drop for Stream<'_, DECRYPT> {
    /// Wipes the streaming state (the key wipes itself).
    fn drop(&mut self) {
        zeroize(&mut self.state);
    }
}

impl<'a, const DECRYPT: bool> Stream<'a, DECRYPT> {
    /// Starts a message under `key` and `nonce`.
    fn new(key: &'a Sm4Gcm, nonce: &[u8]) -> Result<Self, Error> {
        check_nonce(nonce)?;
        let mut s = Stream {
            key,
            state: [0; 10],
            aad_len: 0,
            text_len: 0,
            in_text: false,
        };
        let init = instance!(key.ghash, vg_sm4_gcm_stream_init,
            x86: [vg_sm4_gcm_stream_init_pclmul],
            x86_64: [vg_sm4_gcm_stream_init_vpclmul],
            aarch64: [vg_sm4_gcm_stream_init_aes]);
        // SAFETY: `key.ctx` is a key context (as in
        // `Sm4Gcm::encrypt_in_place`), valid for reads of 256 bytes, `nonce`
        // for reads of `nonce.len()`, and `s.state` for reads and writes of
        // 80. They are distinct objects, so the writable one overlaps nothing
        // else, nor anything on the stack, and none wraps around. The CPU has
        // the features of the implementation selected.
        unsafe { init(&key.ctx, nonce.as_ptr(), nonce.len(), &mut s.state) };
        Ok(s)
    }

    /// Absorbs more additional data, which must all come before the text.
    fn update_aad(&mut self, aad: &[u8]) -> Result<(), Error> {
        if self.in_text {
            return Err(Error::AadAfterText);
        }
        let aad_len =
            add_len(self.aad_len, aad.len(), MAX_AAD).map_err(|()| Error::InvalidAadLength)?;
        let f = instance!(self.key.ghash, vg_sm4_gcm_stream_aad,
            x86: [vg_sm4_gcm_stream_aad_pclmul],
            x86_64: [vg_sm4_gcm_stream_aad_vpclmul],
            aarch64: [vg_sm4_gcm_stream_aad_aes]);
        // SAFETY: as in `new`; `self.state` represents a message with
        // `self.aad_len` bytes of additional data and no text yet.
        unsafe {
            f(
                &self.key.ctx,
                &mut self.state,
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
    fn update(&mut self, data: &mut [u8]) -> Result<(), Error> {
        let text_len =
            add_len(self.text_len, data.len(), MAX_TEXT).map_err(|()| Error::InvalidTextLength)?;
        self.in_text = true;
        let f = if DECRYPT {
            instance!(self.key.ghash, vg_sm4_gcm_stream_decrypt,
                x86: [vg_sm4_gcm_stream_decrypt_pclmul],
                x86_64: [vg_sm4_gcm_stream_decrypt_vpclmul],
                aarch64: [vg_sm4_gcm_stream_decrypt_aes])
        } else {
            instance!(self.key.ghash, vg_sm4_gcm_stream_encrypt,
                x86: [vg_sm4_gcm_stream_encrypt_pclmul],
                x86_64: [vg_sm4_gcm_stream_encrypt_vpclmul],
                aarch64: [vg_sm4_gcm_stream_encrypt_aes])
        };
        // SAFETY: as in `new`, with `data` valid for reads and writes of
        // `data.len()` bytes (a unique borrow, so it overlaps nothing else);
        // `self.state` represents a message with `self.aad_len` bytes of
        // additional data and `self.text_len` of text.
        unsafe {
            f(
                &self.key.ctx,
                &mut self.state,
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
    fn finish(mut self) -> Block {
        let f = instance!(self.key.ghash, vg_sm4_gcm_stream_finish,
            x86: [vg_sm4_gcm_stream_finish_pclmul],
            x86_64: [vg_sm4_gcm_stream_finish_vpclmul],
            aarch64: [vg_sm4_gcm_stream_finish_aes]);
        let mut tag: Block = [0; 16];
        // SAFETY: as in `update`, with `tag` (a local) valid for reads and
        // writes of 16 bytes. `update_aad` and `update` checked the lengths
        // (§5.2.1.1).
        unsafe {
            f(
                &self.key.ctx,
                &mut self.state,
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
    fn verify(mut self, tag: &[u8]) -> Result<(), Error> {
        let f = instance!(self.key.ghash, vg_sm4_gcm_stream_verify,
            x86: [vg_sm4_gcm_stream_verify_pclmul],
            x86_64: [vg_sm4_gcm_stream_verify_vpclmul],
            aarch64: [vg_sm4_gcm_stream_verify_aes]);
        // SAFETY: as in `finish`, with the received tag `tag` valid for
        // reads of its length.
        let ok = unsafe {
            f(
                &self.key.ctx,
                &mut self.state,
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
        self.stream.update_aad(aad)
    }

    /// Encrypts the next `data.len()` bytes of the plaintext in place.
    pub fn update(&mut self, data: &mut [u8]) -> Result<(), Error> {
        self.stream.update(data)
    }

    /// Finishes the message and returns its full 16-byte tag. A protocol
    /// that sends a shorter tag sends its first bytes.
    pub fn finalize(self) -> Block {
        self.stream.finish()
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
        self.stream.update_aad(aad)
    }

    /// Decrypts the next `data.len()` bytes of the ciphertext in place. The
    /// result is not authenticated until [`finalize`](Self::finalize) (or
    /// [`finalize_truncated`](Self::finalize_truncated)) succeeds.
    pub fn update(&mut self, data: &mut [u8]) -> Result<(), Error> {
        self.stream.update(data)
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
        assert_tag_length!(N);
        self.stream.verify(tag)
    }
}

#[cfg(test)]
mod tests {
    extern crate std;

    use super::{Error, Ghash, MAX_AAD, MAX_TEXT, Sm4Gcm, Stream, add_len};
    use crate::cpu::detected;
    use verified_garbage_cpu::Features;

    /// The implementation of GHASH chosen for each set of features.
    #[test]
    fn ghash_backend() {
        let f = |bits: u32| Ghash::select(Features(bits));
        assert_eq!(f(0), Ghash::Scalar);
        assert_eq!(Sm4Gcm::new(&[0; 16]).ghash, Ghash::select(detected()));
    }

    /// The instances x86's and x86-64's CPUs choose among.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    #[test]
    fn ghash_backend_x86() {
        let f = |bits: u32| Ghash::select(Features(bits));
        assert_eq!(f(verified_garbage_cpu::feature::PCLMULQDQ), Ghash::Scalar);
        assert_eq!(
            f(verified_garbage_cpu::feature::PCLMULQDQ | verified_garbage_cpu::feature::SSSE3),
            Ghash::Pclmul
        );
        let all = verified_garbage_cpu::feature::AVX
            | verified_garbage_cpu::feature::AVX2
            | verified_garbage_cpu::feature::PCLMULQDQ
            | verified_garbage_cpu::feature::SSSE3
            | verified_garbage_cpu::feature::VPCLMULQDQ;
        #[cfg(target_arch = "x86_64")]
        assert_eq!(f(all), Ghash::Vpclmul);
        // 32-bit x86 has no `_vpclmul` instances.
        #[cfg(target_arch = "x86")]
        assert_eq!(f(all), Ghash::Pclmul);
        assert_eq!(f(all & !verified_garbage_cpu::feature::AVX), Ghash::Pclmul);
    }

    /// The instance AArch64's CPUs with PMULL choose.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn ghash_backend_aarch64() {
        assert_eq!(
            Ghash::select(Features(verified_garbage_cpu::feature::AES)),
            Ghash::Aes
        );
    }

    /// The text of a message is checked against its limits before
    /// anything is encrypted, and so is its additional data.
    #[test]
    fn lengths() {
        assert_eq!(add_len(MAX_TEXT - 1, 1, MAX_TEXT), Ok(MAX_TEXT));
        assert_eq!(add_len(MAX_TEXT, 1, MAX_TEXT), Err(()));
        assert_eq!(add_len(u64::MAX, 1, u64::MAX), Err(()));
        let key = Sm4Gcm::new(&[1; 16]);
        let mut s = Stream::<false>::new(&key, &[0; 12]).unwrap();
        s.text_len = MAX_TEXT;
        let mut data = [9; 3];
        assert_eq!(s.update(&mut data), Err(Error::InvalidTextLength));
        assert_eq!(data, [9; 3]);
        let mut s = Stream::<true>::new(&key, &[0; 12]).unwrap();
        s.aad_len = MAX_AAD;
        assert_eq!(s.update_aad(&[0]), Err(Error::InvalidAadLength));
        assert_eq!(s.update_aad(&[]), Ok(()));
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
