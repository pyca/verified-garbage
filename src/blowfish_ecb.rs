//! Blowfish-ECB (Schneier, FSE 1994), without padding:
//! [`BlowfishEcbEncryptor`] and [`BlowfishEcbDecryptor`].
//!
//! Key expansion and the encryption and decryption of whole blocks are the
//! verified primitives (`VG.Spec.Blowfish.expandKeyContract`,
//! `VG.Spec.Blowfish.ecbEncryptContract` and
//! `VG.Spec.Blowfish.ecbDecryptContract`). This wrapper checks the key's
//! length before key expansion and keeps the bytes of a partial block until
//! the next update completes it; updates write the whole blocks they
//! complete to the caller's buffer, so nothing is allocated; finalization
//! rejects a trailing partial block. On AArch64, ECB runs sixteen blocks at
//! a time in AdvSIMD registers; on x86-64, one at a time with SSE2.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use crate::arch::blowfish::{
    vg_blowfish_ecb_decrypt, vg_blowfish_ecb_encrypt, vg_blowfish_expand_key,
};
use crate::zeroize::zeroize;

/// Why a Blowfish-ECB operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key length is outside 4..=56 bytes (32 to 448 bits).
    InvalidKeyLength,
    /// The total input length is not a multiple of eight bytes.
    IncompleteBlock,
    /// The output buffer of an update is shorter than the bytes it would
    /// write ([`BlowfishEcbEncryptor::output_len`],
    /// [`BlowfishEcbDecryptor::output_len`]).
    OutputTooSmall,
}

/// A streaming Blowfish-ECB encryption (or, if `DECRYPT`, decryption),
/// which [`BlowfishEcbEncryptor`] and [`BlowfishEcbDecryptor`] wrap.
struct Ecb<const DECRYPT: bool> {
    /// The expanded key.
    schedule: [u8; 4168],
    /// The bytes of a partial block, the first `pending_len` of them.
    pending: [u8; 8],
    pending_len: usize,
}

impl<const DECRYPT: bool> Ecb<DECRYPT> {
    /// Expands a key of 4..=56 bytes.
    fn new(key: &[u8]) -> Result<Self, Error> {
        if !(4..=56).contains(&key.len()) {
            return Err(Error::InvalidKeyLength);
        }
        let mut ecb = Self {
            schedule: [0; 4168],
            pending: [0; 8],
            pending_len: 0,
        };
        // SAFETY: the key has a length in 4..=56; the key and the schedule
        // are separate valid objects of the lengths passed.
        unsafe {
            vg_blowfish_expand_key(key.as_ptr(), key.len(), &mut ecb.schedule);
        }
        Ok(ecb)
    }

    /// The number of bytes an update with `input_len` bytes of input
    /// writes, saturating at `usize::MAX`.
    fn output_len(&self, input_len: usize) -> usize {
        self.pending_len
            .checked_add(input_len)
            .map_or(usize::MAX, |total| total / 8 * 8)
    }

    /// Processes the whole blocks of the pending bytes and `input` into the
    /// first bytes of `output`, keeps the rest pending, and returns how many
    /// bytes it wrote; changes nothing if `output` is too short.
    fn update(&mut self, input: &[u8], output: &mut [u8]) -> Result<usize, Error> {
        // No slice is `usize::MAX` bytes long, so an overflowing length
        // (`output_len` saturates) is too long for any `output`.
        let written = self.output_len(input.len());
        let output = output.get_mut(..written).ok_or(Error::OutputTooSmall)?;
        if written == 0 {
            // `pending_len + input.len() < 8`.
            self.pending[self.pending_len..self.pending_len + input.len()].copy_from_slice(input);
            self.pending_len += input.len();
            return Ok(0);
        }
        // `written` is at least 8, more than `pending_len`.
        let (head, rest) = output.split_at_mut(self.pending_len);
        head.copy_from_slice(&self.pending[..self.pending_len]);
        let (used, left) = input.split_at(rest.len());
        rest.copy_from_slice(used);
        let crypt = if DECRYPT {
            vg_blowfish_ecb_decrypt
        } else {
            vg_blowfish_ecb_encrypt
        };
        // SAFETY: `output` holds `written / 8` complete eight-byte blocks;
        // the schedule, written by key expansion, and `output` are separate
        // valid objects of the lengths passed. The function zeroes its
        // working space on its own stack before returning.
        unsafe {
            crypt(&self.schedule, output.as_mut_ptr().cast(), written / 8);
        }
        self.pending[..left.len()].copy_from_slice(left);
        self.pending_len = left.len();
        Ok(written)
    }

    /// Fails if a partial block remains.
    fn finalize(self) -> Result<(), Error> {
        if self.pending_len == 0 {
            Ok(())
        } else {
            Err(Error::IncompleteBlock)
        }
    }
}

impl<const DECRYPT: bool> Drop for Ecb<DECRYPT> {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
        zeroize(&mut self.pending);
    }
}

/// A streaming Blowfish-ECB encryptor, without padding.
pub struct BlowfishEcbEncryptor {
    ecb: Ecb<false>,
}

impl BlowfishEcbEncryptor {
    /// Expands a key of 4..=56 bytes (32 to 448 bits). Weak keys are
    /// accepted.
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        Ok(Self {
            ecb: Ecb::new(key)?,
        })
    }

    /// The number of bytes the next [`update`](Self::update) with
    /// `input_len` bytes of input writes: the whole blocks of the pending
    /// bytes and the input, at most `input_len + 7` (saturating at
    /// `usize::MAX`, for lengths no slice has).
    pub fn output_len(&self, input_len: usize) -> usize {
        self.ecb.output_len(input_len)
    }

    /// Encrypts the whole blocks of the pending bytes and `input` into the
    /// first bytes of `output`, keeps the rest (at most seven bytes) pending
    /// for the next update, and returns how many bytes it wrote:
    /// [`output_len`](Self::output_len)`(input.len())`.
    ///
    /// `output` may be longer than that, and `input.len() + 7` bytes always
    /// suffice. If it is shorter, fails with [`Error::OutputTooSmall`],
    /// writing nothing and leaving the encryptor unchanged.
    pub fn update(&mut self, input: &[u8], output: &mut [u8]) -> Result<usize, Error> {
        self.ecb.update(input, output)
    }

    /// Consumes the encryptor. Fails with [`Error::IncompleteBlock`] if a
    /// partial block is pending; padding is neither added nor removed.
    pub fn finalize(self) -> Result<(), Error> {
        self.ecb.finalize()
    }
}

/// A streaming Blowfish-ECB decryptor, without padding.
pub struct BlowfishEcbDecryptor {
    ecb: Ecb<true>,
}

impl BlowfishEcbDecryptor {
    /// Expands a key of 4..=56 bytes (32 to 448 bits). Weak keys are
    /// accepted.
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        Ok(Self {
            ecb: Ecb::new(key)?,
        })
    }

    /// The number of bytes the next [`update`](Self::update) with
    /// `input_len` bytes of input writes: the whole blocks of the pending
    /// bytes and the input, at most `input_len + 7` (saturating at
    /// `usize::MAX`, for lengths no slice has).
    pub fn output_len(&self, input_len: usize) -> usize {
        self.ecb.output_len(input_len)
    }

    /// Decrypts the whole blocks of the pending bytes and `input` into the
    /// first bytes of `output`, keeps the rest (at most seven bytes) pending
    /// for the next update, and returns how many bytes it wrote:
    /// [`output_len`](Self::output_len)`(input.len())`.
    ///
    /// `output` may be longer than that, and `input.len() + 7` bytes always
    /// suffice. If it is shorter, fails with [`Error::OutputTooSmall`],
    /// writing nothing and leaving the decryptor unchanged.
    pub fn update(&mut self, input: &[u8], output: &mut [u8]) -> Result<usize, Error> {
        self.ecb.update(input, output)
    }

    /// Consumes the decryptor. Fails with [`Error::IncompleteBlock`] if a
    /// partial block is pending; padding is neither added nor removed.
    pub fn finalize(self) -> Result<(), Error> {
        self.ecb.finalize()
    }
}
