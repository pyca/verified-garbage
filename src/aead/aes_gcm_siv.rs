//! AES-GCM-SIV (RFC 8452) with 128- and 256-bit keys: nonce-misuse-resistant
//! authenticated encryption.
//!
//! Repeating a nonce under one key reveals only whether two messages with the
//! same associated data are equal.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::aes::vg_aes_expand_key_auto;
use crate::arch::dispatch::aes_gcm_siv::{vg_aes_gcm_siv_open_auto, vg_aes_gcm_siv_seal_auto};
use crate::error::InvalidKeyLength;
use crate::zeroize::zeroize;

/// The longest plaintext and additional data, in bytes (§6: `P_MAX` and
/// `A_MAX`, `2^36`).
const MAX_LEN: u64 = 1 << 36;

/// Why an AES-GCM-SIV operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The plaintext or ciphertext is longer than `2^36` bytes (§6).
    InvalidTextLength,
    /// The additional data is longer than `2^36` bytes (§6).
    InvalidAadLength,
    /// The tag does not match: the ciphertext, the additional data or the
    /// nonce is not what was authenticated under this key.
    TagMismatch,
}

crate::error::impl_error! {
    Error {
        InvalidTextLength => "AES-GCM-SIV text is too long",
        InvalidAadLength => "AES-GCM-SIV additional data is too long",
        TagMismatch => "AES-GCM-SIV tag does not match",
    }
}

/// An AES-GCM-SIV key: the AES key schedule of the key-generating key.
#[derive(Clone)]
pub struct AesGcmSiv {
    /// The key schedule `vg_aes_expand_key` writes.
    schedule: [u8; 240],
    /// The number of rounds of AES: 10 or 14.
    rounds: usize,
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
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 16 | 32) {
            return Err(InvalidKeyLength);
        }
        // The schedule is written in the value returned, not copied into it
        // after: a copy reads the schedule's 16-byte stores with wider loads,
        // which cannot take them from the store buffer and wait for them.
        let mut k = Ok(AesGcmSiv {
            schedule: [0; 240],
            rounds: key.len() / 4 + 6,
        });
        if let Ok(k) = &mut k {
            // SAFETY: `key` is valid for reads of `key.len()` bytes, which is
            // 16 or 32, and `k.schedule` for reads and writes of 240 bytes.
            // They are distinct objects, so they do not overlap, nor do they
            // overlap the return address on the stack or the stack below it,
            // and neither wraps around the end of the address space. The
            // dispatcher calls only an implementation the CPU has the features
            // of.
            unsafe { vg_aes_expand_key_auto(key.as_ptr(), key.len(), &mut k.schedule) };
        }
        k
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
        let mut tag = [0u8; 16];
        // SAFETY: `self.schedule` is the key schedule `vg_aes_expand_key`
        // wrote for `self.rounds` (10 or 14) rounds, valid for reads of 240
        // bytes. `nonce` (12 bytes) and `aad` are valid for reads of their
        // lengths, `data` for reads and writes of `data.len()` bytes, and
        // `tag` for reads and writes of 16. `data` and `tag` are unique
        // borrows, so they overlap neither each other nor the other buffers;
        // no buffer overlaps the arguments on the stack, the return address
        // or the stack below it, and none wraps around the end of the address
        // space. The dispatcher calls only an implementation the CPU has
        // the features of.
        unsafe {
            vg_aes_gcm_siv_seal_auto(
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
        // SAFETY: as in `encrypt_in_place`, with the received tag `tag`
        // valid for reads of 16 bytes, which `data`, a unique borrow, does not
        // overlap.
        let ok = unsafe {
            vg_aes_gcm_siv_open_auto(
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
        // `vg_aes_gcm_siv_open`'s contract leaves the plaintext in `data` if it returns 1,
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
    use super::{AesGcmSiv, Error, InvalidKeyLength, MAX_LEN, check};

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
            assert_eq!(AesGcmSiv::new(&key[..n]).err(), Some(InvalidKeyLength));
        }
    }
}
