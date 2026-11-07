//! Triple DES-CBC (SP 800-38A §6.2, with Triple DES as in FIPS 46-3), in place
//! and without padding.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use super::ecb::Backend;
use crate::arch::triple_des::vg_triple_des_expand_key;
use crate::arch::triple_des_cbc::{
    vg_triple_des_cbc_decrypt_chained, vg_triple_des_cbc_encrypt_chained,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::triple_des_cbc::{
    vg_triple_des_cbc_decrypt_chained_avx2, vg_triple_des_cbc_decrypt_chained_avx512,
};
use crate::cpu::detected;
use crate::error::{IncompleteBlock, InvalidKeyLength};
use crate::zeroize::zeroize;

/// An expanded Triple DES key, which serves both directions.
struct Key {
    /// The key schedule `vg_triple_des_expand_key` writes.
    schedule: [u8; 384],
}

/// A Triple DES-CBC encryption of one message, without padding.
///
/// Each call takes whole 8-byte blocks and continues the message from the
/// last ciphertext block of the call before, so that a message may be
/// encrypted in pieces.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct TripleDesCbcEncryptor {
    key: Key,
    /// The chaining value: the IV, then the last ciphertext block.
    iv: [u8; 8],
}

impl TripleDesCbcEncryptor {
    /// Expands a 16- or 24-byte key (a 24-byte key encodes K1, K2 and K3; a
    /// 16-byte key, K1 and K2, with K3 repeating K1; each byte's parity bit is
    /// ignored), to encrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 8]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
        })
    }

    /// Encrypts whole 8-byte blocks in place, continuing the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 8.
    pub fn encrypt(&mut self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        self.key.encrypt(&mut self.iv, buffer)
    }
}

/// A Triple DES-CBC decryption of one message, without padding.
///
/// Each call takes whole 8-byte blocks and continues the message from the
/// last ciphertext block of the call before, so that a message may be
/// decrypted in pieces.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct TripleDesCbcDecryptor {
    key: Key,
    /// The chaining value: the IV, then the last ciphertext block.
    iv: [u8; 8],
    /// The implementation of ECB decryption the CPU runs best, whose
    /// variant of CBC decryption runs.
    backend: Backend,
}

impl TripleDesCbcDecryptor {
    /// Expands a 16- or 24-byte key (a 24-byte key encodes K1, K2 and K3; a
    /// 16-byte key, K1 and K2, with K3 repeating K1; each byte's parity bit is
    /// ignored), to decrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 8]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
            backend: Backend::select(detected()),
        })
    }

    /// Decrypts whole 8-byte blocks in place, continuing the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 8.
    pub fn decrypt(&mut self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        self.key.decrypt(self.backend, &mut self.iv, buffer)
    }
}

impl Key {
    /// Expands a 16- or 24-byte key.
    fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 16 | 24) {
            return Err(InvalidKeyLength);
        }
        let mut schedule = [0; 384];
        // SAFETY: the key has a validated length; key and schedule are separate
        // valid buffers of the required sizes.
        unsafe {
            vg_triple_des_expand_key(key.as_ptr(), key.len(), &mut schedule);
        }
        Ok(Self { schedule })
    }

    /// Encrypts whole eight-byte blocks in place, chained from `iv`, and
    /// replaces `iv` with the last ciphertext block (leaving it unchanged
    /// for empty input).
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of eight.
    fn encrypt(&self, iv: &mut [u8; 8], buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(8) {
            return Err(IncompleteBlock);
        }
        // SAFETY: the buffer holds `len / 8` whole blocks, and it, the chaining
        // value (which the function reads and replaces) and the schedule are
        // separate valid objects of the sizes of the signature, none of them on
        // the callee's stack.
        unsafe {
            vg_triple_des_cbc_encrypt_chained(
                &self.schedule,
                iv,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 8,
            );
        }
        Ok(())
    }

    /// Decrypts whole eight-byte blocks in place, chained from `iv`, and
    /// replaces `iv` with the last ciphertext block (leaving it unchanged
    /// for empty input).
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of eight.
    fn decrypt(
        &self,
        backend: Backend,
        iv: &mut [u8; 8],
        buffer: &mut [u8],
    ) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(8) {
            return Err(IncompleteBlock);
        }
        let f = match backend {
            Backend::Scalar => vg_triple_des_cbc_decrypt_chained,
            #[cfg(target_arch = "x86_64")]
            Backend::Avx2 => vg_triple_des_cbc_decrypt_chained_avx2,
            #[cfg(target_arch = "x86_64")]
            Backend::Avx512 => vg_triple_des_cbc_decrypt_chained_avx512,
        };
        // SAFETY: as in `encrypt`; `Backend::select` chose `f` for the CPU's
        // features, which its ECB function needs too.
        unsafe {
            f(
                &self.schedule,
                iv,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 8,
            );
        }
        Ok(())
    }
}

impl Drop for Key {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
