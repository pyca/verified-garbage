//! SM4-GCM: GCM (NIST SP 800-38D) with SM4 (GB/T 32907-2016, transcribed in
//! the Internet-Draft draft-ribose-cfrg-sm4-10) as its block cipher, the
//! `AEAD_SM4_GCM` of RFC 8998 §3.5.1, with 16-byte keys.
//!
//! The block-cipher work is verified assembly: `vg_sm4_expand_key`
//! (contract `VG.Spec.Sm4.expandKeyContract`) writes the key schedule, and
//! `vg_sm4_ctr32` (`VG.Spec.Sm4.ctr32Contract`) is counter mode with GCM's
//! `inc₃₂` over whole blocks, bitsliced SM4 with no table lookups: it
//! computes the hash subkey `H = CIPH_K(0¹²⁸)` (§7.1 step 1, the zero block
//! from the zero counter block), encrypts and decrypts the text from
//! `inc₃₂(J₀)` (step 3), and masks the tag, `GCTR_K(J₀, S)` (step 6). GHASH
//! (§6.4) is `vg_ghash` (`VG.Spec.Gcm.ghashContract`), or on CPUs with
//! PCLMULQDQ and SSSE3 `vg_ghash_pclmul`, and on x86-64 CPUs with VPCLMULQDQ
//! and AVX2 too `vg_ghash_vpclmul` (`Ghash`). This module composes them: it
//! forms `J₀` (§7.1 step 2), feeds GHASH the additional data, the ciphertext,
//! their zero padding and their lengths (step 5), keeps the partial blocks
//! of a message given in pieces, and checks the lengths of §5.2.1.1. Every
//! branch it takes depends only on lengths; the tags are compared in
//! constant time (`crate::ct::eq`).
//!
//! An [`Sm4Gcm`] is a key: it encrypts and decrypts whole messages at once,
//! and starts incremental ones with [`Sm4Gcm::encryptor`] and
//! [`Sm4Gcm::decryptor`], which borrow it. **An [`Sm4GcmDecryptor`]'s
//! `update` returns plaintext that has not been authenticated yet**: nothing
//! may act on it before its `finalize` has succeeded. When the whole message
//! fits in memory, [`Sm4Gcm::decrypt_in_place`] checks the tag before it
//! decrypts.
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

#![cfg(target_arch = "x86_64")]

use crate::arch::gcm::vg_ghash;
#[cfg(target_arch = "x86_64")]
use crate::arch::gcm::{
    VG_GHASH_PCLMUL_FEATURES, VG_GHASH_VPCLMUL_FEATURES, vg_ghash_pclmul, vg_ghash_vpclmul,
};
use crate::arch::sm4::vg_sm4_expand_key;
use crate::arch::sm4_gcm::vg_sm4_ctr32;
use crate::cpu::{Features, detected};
use crate::zeroize::zeroize;

/// A 16-byte block: a tag, or a block of GHASH or of counter mode.
pub type Block = [u8; 16];

/// The longest plaintext, in bytes: `2^39 − 256` bits (§5.2.1.1).
const MAX_TEXT: u64 = (1 << 36) - 32;
/// The longest additional data, in bytes: `2^64 − 1` bits, rounded down
/// to whole bytes (§5.2.1.1).
const MAX_AAD: u64 = (1 << 61) - 1;

/// The most blocks of text counter mode transforms before GHASH hashes
/// them: 4 KiB, which stays in the L1 cache between the two passes.
const CHUNK: usize = 4096;

/// The implementations of GHASH (`vg_ghash` and its variants, all with the
/// contract `VG.Spec.Gcm.ghashContract`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Ghash {
    /// Constant-time scalar code, for the target's baseline ISA.
    Scalar,
    /// PCLMULQDQ, one block at a time (and SSSE3's byte reversal).
    #[cfg(target_arch = "x86_64")]
    Pclmul,
    /// VPCLMULQDQ, eight blocks at a time in 256-bit registers.
    #[cfg(target_arch = "x86_64")]
    Vpclmul,
}

impl Ghash {
    /// The best implementation a CPU with the features `f` can run.
    pub(crate) fn select(f: Features) -> Ghash {
        #[cfg(target_arch = "x86_64")]
        if f.contains(VG_GHASH_VPCLMUL_FEATURES) {
            return Ghash::Vpclmul;
        }
        #[cfg(target_arch = "x86_64")]
        if f.contains(VG_GHASH_PCLMUL_FEATURES) {
            return Ghash::Pclmul;
        }
        let _ = f;
        Ghash::Scalar
    }

    /// Continues GHASH with the hash subkey `h` from `y` over the whole
    /// blocks of `data` (whose length is a multiple of 16).
    fn run(self, h: &Block, y: &mut Block, data: &[u8]) {
        debug_assert_eq!(data.len() % 16, 0);
        let (p, n) = (data.as_ptr().cast(), data.len() / 16);
        let mut scratch = [0u64; 32];
        // SAFETY: `h` and `y` are 16-byte blocks, `data` holds `n` whole
        // blocks, and `scratch` (a local) is 256 bytes: distinct objects
        // valid for the reads and writes of the signature, none of them on
        // the callee's stack or wrapping around. The CPU has the features of
        // the implementation `select` chose.
        unsafe {
            match self {
                Ghash::Scalar => vg_ghash(h, y, p, n, &mut scratch),
                #[cfg(target_arch = "x86_64")]
                Ghash::Pclmul => vg_ghash_pclmul(h, y, p, n, &mut scratch),
                #[cfg(target_arch = "x86_64")]
                Ghash::Vpclmul => vg_ghash_vpclmul(h, y, p, n, &mut scratch),
            }
        }
        // The scalar code leaves products of `h` and the data there.
        zeroize(&mut scratch);
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

/// `inc₃₂` (§6.2): the last 32 bits of `x`, as a big-endian integer, plus
/// one, modulo `2³²`.
fn inc32(x: &Block) -> Block {
    let mut y = *x;
    let c = u32::from_be_bytes([x[12], x[13], x[14], x[15]]).wrapping_add(1);
    y[12..].copy_from_slice(&c.to_be_bytes());
    y
}

/// An SM4-GCM key: its SM4 key schedule and its hash subkey `H`. Its
/// [`encrypt_in_place`](Self::encrypt_in_place) and
/// [`decrypt_in_place`](Self::decrypt_in_place) (or
/// [`decrypt_in_place_truncated`](Self::decrypt_in_place_truncated)) are the
/// one-shot AEAD; [`encryptor`](Self::encryptor) and
/// [`decryptor`](Self::decryptor) start incremental ones.
#[derive(Clone)]
pub struct Sm4Gcm {
    /// The key schedule `vg_sm4_expand_key` writes.
    schedule: [u8; 128],
    /// The hash subkey `H = CIPH_K(0¹²⁸)`.
    h: Block,
    /// The implementation of GHASH.
    ghash: Ghash,
}

impl Drop for Sm4Gcm {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
        zeroize(&mut self.h);
    }
}

impl Sm4Gcm {
    /// The size of a full tag, in bytes.
    pub const TAG_SIZE: usize = 16;

    /// Prepares a 16-byte SM4 key.
    pub fn new(key: &[u8; 16]) -> Self {
        Self::with_ghash(key, Ghash::select(detected()))
    }

    /// `new`, with the implementation of GHASH `ghash`.
    fn with_ghash(key: &[u8; 16], ghash: Ghash) -> Self {
        let mut k = Sm4Gcm {
            schedule: [0; 128],
            h: [0; 16],
            ghash,
        };
        // SAFETY: `key` and `k.schedule` are separate valid buffers of the
        // required sizes. The function zeroes its working space on its own
        // stack before returning.
        unsafe { vg_sm4_expand_key(key, &mut k.schedule) };
        // §7.1 step 1: `H` is the encryption of the zero block, the first
        // block of counter mode on a zero block from the zero counter block.
        let mut h = [0; 16];
        k.ctr32(&mut [0; 16], &mut h);
        k.h = h;
        k
    }

    /// Counter mode with `inc₃₂` on the whole blocks of `blocks` (whose
    /// length is a multiple of 16), in place, from the counter block
    /// `counter`, which it leaves at the next one.
    fn ctr32(&self, counter: &mut Block, blocks: &mut [u8]) {
        debug_assert_eq!(blocks.len() % 16, 0);
        // SAFETY: `blocks` holds `len / 16` whole blocks, and it, `counter`
        // and the schedule are separate valid objects of the sizes of the
        // signature, none of them on the callee's stack. The function zeroes
        // its working space on its own stack before returning.
        unsafe {
            vg_sm4_ctr32(
                &self.schedule,
                counter,
                blocks.as_mut_ptr().cast(),
                blocks.len() / 16,
            )
        };
    }

    /// Counter mode with `inc₃₂` on `data` of any length, from `counter`:
    /// a partial last block is XORed with the first bytes of the next
    /// keystream block.
    fn crypt(&self, counter: &mut Block, data: &mut [u8]) {
        let whole = data.len() / 16 * 16;
        let (blocks, rest) = data.split_at_mut(whole);
        self.ctr32(counter, blocks);
        if !rest.is_empty() {
            let mut ks = [0; 16];
            self.ctr32(counter, &mut ks);
            for (x, k) in rest.iter_mut().zip(&ks) {
                *x ^= k;
            }
            zeroize(&mut ks);
        }
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
        add_len(0, data.len(), MAX_TEXT).map_err(|()| Error::InvalidTextLength)?;
        let mut s = Stream::<false>::new(self, nonce)?;
        s.update_aad(aad)?;
        s.update(data)?;
        Ok(s.finish())
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
    /// error when the call is compiled. It is a type parameter, fixed in the
    /// caller's code, so that it cannot come from the message. SP 800-38D
    /// Appendix C restricts 4- and 8-byte tags to applications that bound the
    /// length of the messages and the number of decryptions under one key.
    pub fn decrypt_in_place_truncated<const N: usize>(
        &self,
        nonce: &[u8],
        aad: &[u8],
        data: &mut [u8],
        tag: &[u8; N],
    ) -> Result<(), Error> {
        assert_tag_length!(N);
        add_len(0, data.len(), MAX_TEXT).map_err(|()| Error::InvalidTextLength)?;
        let mut s = Stream::<true>::new(self, nonce)?;
        s.update_aad(aad)?;
        // Hash the ciphertext, and decrypt it only once the tag is right.
        s.start_text();
        s.absorb(data, 0);
        s.text_len = data.len() as u64;
        let mut counter = s.counter;
        s.verify(tag)?;
        self.crypt(&mut counter, data);
        zeroize(&mut counter);
        Ok(())
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
/// [`Sm4GcmEncryptor`] and [`Sm4GcmDecryptor`] wrap: what GCM-AE or GCM-AD
/// keeps of a message given in pieces, as `VG.Spec.Gcm.StreamRepr` describes
/// it, and the lengths absorbed so far.
#[derive(Clone)]
struct Stream<'a, const DECRYPT: bool> {
    key: &'a Sm4Gcm,
    /// The pre-counter block `J₀` (§7.1 step 2).
    j0: Block,
    /// GHASH of the whole blocks of `A ‖ 0ᵛ ‖ C` so far.
    y: Block,
    /// The bytes of the string GHASH absorbs that do not fill a block yet:
    /// the last `aad_len mod 16` bytes of the additional data before the
    /// text, and the last `text_len mod 16` of the ciphertext after it.
    buf: Block,
    /// The next counter block.
    counter: Block,
    /// If the text ends in a partial block, its keystream block, whose
    /// bytes after the first `text_len mod 16` the next piece uses.
    ks: Block,
    aad_len: u64,
    text_len: u64,
    /// Whether the text has begun (and the additional data was padded).
    in_text: bool,
}

impl<const DECRYPT: bool> Drop for Stream<'_, DECRYPT> {
    /// Wipes the state (the key wipes itself).
    fn drop(&mut self) {
        zeroize(&mut self.j0);
        zeroize(&mut self.y);
        zeroize(&mut self.buf);
        zeroize(&mut self.counter);
        zeroize(&mut self.ks);
    }
}

impl<'a, const DECRYPT: bool> Stream<'a, DECRYPT> {
    /// Starts a message under `key` and `nonce`.
    fn new(key: &'a Sm4Gcm, nonce: &[u8]) -> Result<Self, Error> {
        // A nonce is shorter than `2^61` bytes (§5.2.1.1), as no buffer is
        // that long, but it must not be empty.
        if nonce.is_empty() {
            return Err(Error::InvalidNonceLength);
        }
        let mut s = Stream {
            key,
            j0: [0; 16],
            y: [0; 16],
            buf: [0; 16],
            counter: [0; 16],
            ks: [0; 16],
            aad_len: 0,
            text_len: 0,
            in_text: false,
        };
        // §7.1 step 2: `IV ‖ 0³¹ ‖ 1` for a 96-bit IV, and otherwise
        // `GHASH_H(IV ‖ 0^(s+64) ‖ [len(IV)]₆₄)`.
        if nonce.len() == 12 {
            s.j0[..12].copy_from_slice(nonce);
            s.j0[15] = 1;
        } else {
            s.absorb(nonce, 0);
            s.pad(nonce.len() % 16);
            let mut lens = [0; 16];
            lens[8..].copy_from_slice(&(nonce.len() as u64).wrapping_mul(8).to_be_bytes());
            key.ghash.run(&key.h, &mut s.y, &lens);
            s.j0 = s.y;
            s.y = [0; 16];
        }
        // §7.1 step 3: the text's counter blocks start at `inc₃₂(J₀)`.
        s.counter = inc32(&s.j0);
        Ok(s)
    }

    /// Continues GHASH over `data`, with `filled` bytes (below 16) of the
    /// string already in `buf`: whole blocks into `y`, the rest to `buf`.
    fn absorb(&mut self, mut data: &[u8], filled: usize) {
        let k = self.key;
        if filled != 0 {
            let take = data.len().min(16 - filled);
            self.buf[filled..filled + take].copy_from_slice(&data[..take]);
            data = &data[take..];
            if filled + take < 16 {
                return;
            }
            k.ghash.run(&k.h, &mut self.y, &self.buf);
        }
        let whole = data.len() / 16 * 16;
        k.ghash.run(&k.h, &mut self.y, &data[..whole]);
        self.buf[..data.len() - whole].copy_from_slice(&data[whole..]);
    }

    /// Pads the `filled` bytes in `buf` with zeros to a block, and absorbs
    /// it (nothing if there are none).
    fn pad(&mut self, filled: usize) {
        if filled != 0 {
            self.buf[filled..].fill(0);
            let k = self.key;
            k.ghash.run(&k.h, &mut self.y, &self.buf);
        }
    }

    /// Absorbs more additional data, which must all come before the text.
    fn update_aad(&mut self, aad: &[u8]) -> Result<(), Error> {
        if self.in_text {
            return Err(Error::AadAfterText);
        }
        let aad_len =
            add_len(self.aad_len, aad.len(), MAX_AAD).map_err(|()| Error::InvalidAadLength)?;
        self.absorb(aad, (self.aad_len % 16) as usize);
        self.aad_len = aad_len;
        Ok(())
    }

    /// Pads the additional data (`0ᵛ`) before the first of the text.
    fn start_text(&mut self) {
        if !self.in_text {
            self.pad((self.aad_len % 16) as usize);
            self.in_text = true;
        }
    }

    /// Encrypts (or, if `DECRYPT`, decrypts) the next `data.len()` bytes of
    /// the text in place, and absorbs the ciphertext.
    fn update(&mut self, data: &mut [u8]) -> Result<(), Error> {
        let text_len =
            add_len(self.text_len, data.len(), MAX_TEXT).map_err(|()| Error::InvalidTextLength)?;
        self.start_text();
        let key = self.key;
        let mut pos = (self.text_len % 16) as usize;
        let mut rest = data;
        // The rest of a partial block, with its keystream block.
        if pos != 0 {
            let take = rest.len().min(16 - pos);
            let (head, tail) = rest.split_at_mut(take);
            self.text(head, pos, |s, head| {
                for (x, k) in head.iter_mut().zip(&s.ks[pos..]) {
                    *x ^= k;
                }
            });
            pos = (pos + take) % 16;
            rest = tail;
        }
        // Whole blocks, a chunk at a time.
        if pos == 0 {
            let whole = rest.len() / 16 * 16;
            let (blocks, tail) = rest.split_at_mut(whole);
            for chunk in blocks.chunks_mut(CHUNK) {
                self.text(chunk, 0, |s, chunk| key.ctr32(&mut s.counter, chunk));
            }
            // A partial last block, with the next keystream block.
            if !tail.is_empty() {
                self.ks = [0; 16];
                key.ctr32(&mut self.counter, &mut self.ks);
                self.text(tail, 0, |s, tail| {
                    for (x, k) in tail.iter_mut().zip(&s.ks) {
                        *x ^= k;
                    }
                });
            }
        }
        self.text_len = text_len;
        Ok(())
    }

    /// Transforms the text `data` (by `f`), which starts at byte `filled`
    /// of a block, and absorbs the ciphertext: after the transformation when
    /// encrypting, before when decrypting.
    fn text(&mut self, data: &mut [u8], filled: usize, f: impl FnOnce(&mut Self, &mut [u8])) {
        if DECRYPT {
            self.absorb(data, filled);
            f(self, data);
        } else {
            f(self, data);
            self.absorb(data, filled);
        }
    }

    /// Finishes the message and returns its 16-byte tag (§7.1 steps 5–6):
    /// GHASH over the padding and the lengths, masked with `CIPH_K(J₀)`.
    fn finish(&mut self) -> Block {
        self.start_text();
        self.pad((self.text_len % 16) as usize);
        let mut lens = [0; 16];
        lens[..8].copy_from_slice(&self.aad_len.wrapping_mul(8).to_be_bytes());
        lens[8..].copy_from_slice(&self.text_len.wrapping_mul(8).to_be_bytes());
        let k = self.key;
        k.ghash.run(&k.h, &mut self.y, &lens);
        let mut tag = self.y;
        let mut j0 = self.j0;
        k.ctr32(&mut j0, &mut tag);
        zeroize(&mut j0);
        tag
    }

    /// Finishes the message and checks the received prefix `tag` of its
    /// tag in constant time. Callers check at compile time that its length is
    /// between 4 and 16.
    fn verify(&mut self, tag: &[u8]) -> Result<(), Error> {
        let mut full = self.finish();
        let ok = crate::ct::eq(&full[..tag.len()], tag);
        zeroize(&mut full);
        if ok { Ok(()) } else { Err(Error::TagMismatch) }
    }
}

/// An incremental SM4-GCM encryption, from [`Sm4Gcm::encryptor`]: the
/// additional data with [`update_aad`](Self::update_aad), then the plaintext
/// with [`update`](Self::update), in pieces of any length, and the tag from
/// [`finalize`](Self::finalize).
///
/// It borrows its [`Sm4Gcm`], so a key encrypts many messages without
/// expanding it again.
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
    /// that sends a shorter tag sends its first bytes. GCM leaves no
    /// buffered text to return.
    pub fn finalize(mut self) -> Block {
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
    pub fn finalize_truncated<const N: usize>(mut self, tag: &[u8; N]) -> Result<(), Error> {
        assert_tag_length!(N);
        self.stream.verify(tag)
    }
}

#[cfg(test)]
mod tests {
    extern crate std;

    use super::{Error, Ghash, MAX_AAD, MAX_TEXT, Sm4Gcm, Stream, add_len, inc32};
    use crate::cpu::{Features, detected};
    use crate::sm4_ecb::Sm4Ecb;
    use std::vec::Vec;

    /// The implementation of GHASH chosen for each set of features.
    #[test]
    fn ghash_backend() {
        let f = |names: &[&str]| Ghash::select(Features::of(names));
        assert_eq!(f(&[]), Ghash::Scalar);
        #[cfg(target_arch = "x86_64")]
        {
            assert_eq!(f(&["pclmulqdq"]), Ghash::Scalar);
            assert_eq!(f(&["pclmulqdq", "ssse3"]), Ghash::Pclmul);
            let all = ["avx", "avx2", "pclmulqdq", "ssse3", "vpclmulqdq"];
            assert_eq!(f(&all), Ghash::Vpclmul);
            assert_eq!(f(&all[1..]), Ghash::Pclmul);
        }
        assert_eq!(Sm4Gcm::new(&[0; 16]).ghash, Ghash::select(detected()));
    }

    /// `vg_sm4_ctr32` steps only the last 32 bits of the counter block,
    /// across their wrap to zero, as `inc32`, against SM4-ECB on the counter
    /// blocks.
    #[test]
    fn ctr32_wraps() {
        let k = [7; 16];
        let key = Sm4Gcm::new(&k);
        let ecb = Sm4Ecb::new(&k);
        let mut start = [0xff; 16];
        start[12..].copy_from_slice(&0xffff_fff0u32.to_be_bytes());
        let n = 40;
        let mut counters = Vec::new();
        let mut c = start;
        for _ in 0..n {
            counters.extend_from_slice(&c);
            c = inc32(&c);
        }
        ecb.encrypt(&mut counters).unwrap();
        let data: Vec<u8> = (0..16 * n).map(|i| i as u8).collect();
        let mut out = data.clone();
        let mut ctr = start;
        key.ctr32(&mut ctr, &mut out);
        assert_eq!(ctr, c);
        assert_eq!(ctr[..12], start[..12]);
        let expected: Vec<u8> = data.iter().zip(&counters).map(|(x, k)| x ^ k).collect();
        assert_eq!(out, expected);
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
