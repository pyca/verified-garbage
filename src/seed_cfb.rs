//! SEED-CFB128 (SP 800-38A §6.3 with 128-bit segments, with SEED as in RFC
//! 4269), in place.
//!
//! The IV must be unpredictable (SP 800-38A Appendix C).

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::seed::vg_seed_expand_key;
use crate::arch::seed_cfb::{vg_seed_cfb128_decrypt, vg_seed_cfb128_encrypt};
use crate::zeroize::zeroize;

/// Why an SEED-CFB128 operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key does not contain 16 bytes.
    InvalidKeyLength,
    /// The input of a call that does not end the message is not a whole
    /// number of blocks.
    IncompleteBlock,
}

crate::error::impl_error! {
    Error {
        InvalidKeyLength => "invalid SEED key length",
        IncompleteBlock => "SEED-CFB128 input is not a whole number of blocks",
    }
}

/// An expanded SEED key.
struct Key {
    /// The key schedule `vg_seed_expand_key` writes.
    schedule: [u8; 128],
}

/// A SEED-CFB128 encryption of one message.
///
/// Each call but the last takes whole 16-byte blocks and continues the
/// message from the last ciphertext block of the call before; the last,
/// [`encrypt_final`](Self::encrypt_final), takes the rest of the message, of
/// any length.
pub struct SeedCfb128Encryptor {
    key: Key,
    /// The block to continue from: the IV, then the last ciphertext block.
    iv: [u8; 16],
}

impl SeedCfb128Encryptor {
    /// Expands a 16-byte key, to encrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 16]) -> Result<Self, Error> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
        })
    }

    /// Encrypts whole 16-byte blocks in place, continuing the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 16: only [`encrypt_final`](Self::encrypt_final) takes
    /// a partial last segment.
    pub fn encrypt(&mut self, buffer: &mut [u8]) -> Result<(), Error> {
        if !buffer.len().is_multiple_of(16) {
            return Err(Error::IncompleteBlock);
        }
        self.key.encrypt(&mut self.iv, buffer);
        Ok(())
    }

    /// Encrypts the rest of the message in place, of any length: its whole
    /// blocks, then a partial last segment if there is one (§6.3,
    /// `Cₙ* = Pₙ* ⊕ MSB_u(CIPH_K(Cₙ₋₁))`).
    pub fn encrypt_final(mut self, buffer: &mut [u8]) {
        self.key.encrypt(&mut self.iv, buffer);
    }
}

impl Drop for SeedCfb128Encryptor {
    /// Wipes the block to continue from, which after a partial last segment
    /// is keystream.
    fn drop(&mut self) {
        zeroize(&mut self.iv);
    }
}

/// A SEED-CFB128 decryption of one message.
///
/// Each call but the last takes whole 16-byte blocks and continues the
/// message from the last ciphertext block of the call before; the last,
/// [`decrypt_final`](Self::decrypt_final), takes the rest of the message, of
/// any length.
pub struct SeedCfb128Decryptor {
    key: Key,
    /// The block to continue from: the IV, then the last ciphertext block.
    iv: [u8; 16],
}

impl SeedCfb128Decryptor {
    /// Expands a 16-byte key, to decrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 16]) -> Result<Self, Error> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
        })
    }

    /// Decrypts whole 16-byte blocks in place, continuing the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 16: only [`decrypt_final`](Self::decrypt_final) takes
    /// a partial last segment.
    pub fn decrypt(&mut self, buffer: &mut [u8]) -> Result<(), Error> {
        if !buffer.len().is_multiple_of(16) {
            return Err(Error::IncompleteBlock);
        }
        self.key.decrypt(&mut self.iv, buffer);
        Ok(())
    }

    /// Decrypts the rest of the message in place, of any length: its whole
    /// blocks, then a partial last segment if there is one (§6.3,
    /// `Cₙ* = Pₙ* ⊕ MSB_u(CIPH_K(Cₙ₋₁))`).
    pub fn decrypt_final(mut self, buffer: &mut [u8]) {
        self.key.decrypt(&mut self.iv, buffer);
    }
}

impl Drop for SeedCfb128Decryptor {
    /// Wipes the block to continue from, which after a partial last segment
    /// is keystream.
    fn drop(&mut self) {
        zeroize(&mut self.iv);
    }
}

/// The signature of `vg_seed_cfb128_encrypt` and `vg_seed_cfb128_decrypt`.
#[cfg(target_arch = "x86_64")]
type Cfb = unsafe extern "sysv64" fn(*const [u8; 128], *mut [u8; 16], *mut [u8; 16], usize);
/// The signature of `vg_seed_cfb128_encrypt` and `vg_seed_cfb128_decrypt`.
#[cfg(any(
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
type Cfb = unsafe extern "C" fn(*const [u8; 128], *mut [u8; 16], *mut [u8; 16], usize);

impl Key {
    /// Expands a 16-byte key.
    fn new(key: &[u8]) -> Result<Self, Error> {
        let key: &[u8; 16] = key.try_into().map_err(|_| Error::InvalidKeyLength)?;
        let mut schedule = [0; 128];
        // SAFETY: key and schedule are separate valid buffers of the required
        // sizes.
        unsafe { vg_seed_expand_key(key, &mut schedule) };
        Ok(Self { schedule })
    }

    /// Encrypts `buffer` in place, from the block `iv`, which it replaces
    /// with the last ciphertext block (unchanged for empty input; after a
    /// partial last segment, the cipher of the last whole one). A message
    /// may be encrypted in pieces of whole blocks, each continuing from the
    /// `iv` the last left; a piece whose length is not a multiple of 16
    /// bytes must end the message.
    fn encrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        self.crypt(iv, buffer, vg_seed_cfb128_encrypt);
    }

    /// Decrypts `buffer` in place, from the block `iv`, which it replaces
    /// with the last ciphertext block (unchanged for empty input; after a
    /// partial last segment, the cipher of the last whole one). A message
    /// may be decrypted in pieces of whole blocks, each continuing from the
    /// `iv` the last left; a piece whose length is not a multiple of 16
    /// bytes must end the message.
    fn decrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        self.crypt(iv, buffer, vg_seed_cfb128_decrypt);
    }

    fn crypt(&self, iv: &mut [u8; 16], buffer: &mut [u8], f: Cfb) {
        let whole = buffer.len() / 16 * 16;
        let (blocks, rest) = buffer.split_at_mut(whole);
        self.blocks(iv, blocks, f);
        if !rest.is_empty() {
            // `CIPH_K` of the block to continue from, as CFB encryption of a
            // zero block, XORed into the last bytes.
            let mut last = [0; 16];
            self.blocks(iv, &mut last, vg_seed_cfb128_encrypt);
            for (b, o) in rest.iter_mut().zip(last) {
                *b ^= o;
            }
            zeroize(&mut last);
        }
    }

    /// `f` on whole blocks.
    fn blocks(&self, iv: &mut [u8; 16], blocks: &mut [u8], f: Cfb) {
        // SAFETY: `blocks` holds `len / 16` whole blocks (its length is a
        // multiple of 16), and it, the block at `iv` and the schedule are
        // separate valid objects of the sizes of the signature, none of them on
        // the callee's stack.
        unsafe {
            f(
                &self.schedule,
                iv,
                blocks.as_mut_ptr().cast(),
                blocks.len() / 16,
            )
        };
    }
}

impl Drop for Key {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
