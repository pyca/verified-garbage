//! CAST5-CFB64 (SP 800-38A §6.3 with 64-bit segments, with CAST5 as in RFC
//! 2144), in place.
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

use crate::arch::cast5_cfb::{vg_cast5_cfb64_decrypt, vg_cast5_cfb64_encrypt};
use crate::cast5_ecb::Cast5Ecb;
use crate::error::{IncompleteBlock, InvalidKeyLength};
use crate::zeroize::zeroize;

/// An expanded CAST5 key.
struct Key {
    key: Cast5Ecb,
}

/// A CAST5-CFB64 encryption of one message.
///
/// Each call but the last takes whole 8-byte blocks and continues the
/// message from the last ciphertext block of the call before; the last,
/// [`encrypt_final`](Self::encrypt_final), takes the rest of the message, of
/// any length.
pub struct Cast5Cfb64Encryptor {
    key: Key,
    /// The block to continue from: the IV, then the last ciphertext block.
    iv: [u8; 8],
}

impl Cast5Cfb64Encryptor {
    /// Expands a key of 5 to 16 bytes, to encrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 8]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
        })
    }

    /// Encrypts whole 8-byte blocks in place, continuing the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 8: only [`encrypt_final`](Self::encrypt_final) takes
    /// a partial last segment.
    pub fn encrypt(&mut self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(8) {
            return Err(IncompleteBlock);
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

impl Drop for Cast5Cfb64Encryptor {
    /// Wipes the block to continue from, which after a partial last segment
    /// is keystream.
    fn drop(&mut self) {
        zeroize(&mut self.iv);
    }
}

/// A CAST5-CFB64 decryption of one message.
///
/// Each call but the last takes whole 8-byte blocks and continues the
/// message from the last ciphertext block of the call before; the last,
/// [`decrypt_final`](Self::decrypt_final), takes the rest of the message, of
/// any length.
pub struct Cast5Cfb64Decryptor {
    key: Key,
    /// The block to continue from: the IV, then the last ciphertext block.
    iv: [u8; 8],
}

impl Cast5Cfb64Decryptor {
    /// Expands a key of 5 to 16 bytes, to decrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 8]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
        })
    }

    /// Decrypts whole 8-byte blocks in place, continuing the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 8: only [`decrypt_final`](Self::decrypt_final) takes
    /// a partial last segment.
    pub fn decrypt(&mut self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(8) {
            return Err(IncompleteBlock);
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

impl Drop for Cast5Cfb64Decryptor {
    /// Wipes the block to continue from, which after a partial last segment
    /// is keystream.
    fn drop(&mut self) {
        zeroize(&mut self.iv);
    }
}

/// The signature of `vg_cast5_cfb64_encrypt` and `vg_cast5_cfb64_decrypt`.
#[cfg(target_arch = "x86_64")]
type Cfb = unsafe extern "sysv64" fn(*const [u8; 128], usize, *mut [u8; 8], *mut [u8; 8], usize);
/// The signature of `vg_cast5_cfb64_encrypt` and `vg_cast5_cfb64_decrypt`.
#[cfg(any(
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
type Cfb = unsafe extern "C" fn(*const [u8; 128], usize, *mut [u8; 8], *mut [u8; 8], usize);

impl Key {
    /// Expands a key of 5 to 16 bytes.
    fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Cast5Ecb::new(key).map_err(|_| InvalidKeyLength)?,
        })
    }

    /// Encrypts `buffer` in place, from the block `iv`, which it replaces
    /// with the last ciphertext block (unchanged for empty input; after a
    /// partial last segment, the cipher of the last whole one). A message
    /// may be encrypted in pieces of whole blocks, each continuing from the
    /// `iv` the last left; a piece whose length is not a multiple of 8 bytes
    /// must end the message.
    fn encrypt(&self, iv: &mut [u8; 8], buffer: &mut [u8]) {
        self.crypt(iv, buffer, vg_cast5_cfb64_encrypt);
    }

    /// Decrypts `buffer` in place, from the block `iv`, which it replaces
    /// with the last ciphertext block (unchanged for empty input; after a
    /// partial last segment, the cipher of the last whole one). A message
    /// may be decrypted in pieces of whole blocks, each continuing from the
    /// `iv` the last left; a piece whose length is not a multiple of 8 bytes
    /// must end the message.
    fn decrypt(&self, iv: &mut [u8; 8], buffer: &mut [u8]) {
        self.crypt(iv, buffer, vg_cast5_cfb64_decrypt);
    }

    fn crypt(&self, iv: &mut [u8; 8], buffer: &mut [u8], f: Cfb) {
        let whole = buffer.len() / 8 * 8;
        let (blocks, rest) = buffer.split_at_mut(whole);
        self.blocks(iv, blocks, f);
        if !rest.is_empty() {
            // `CIPH_K` of the block to continue from, as CFB encryption of a
            // zero block, XORed into the last bytes.
            let mut last = [0; 8];
            self.blocks(iv, &mut last, vg_cast5_cfb64_encrypt);
            for (b, o) in rest.iter_mut().zip(last) {
                *b ^= o;
            }
            zeroize(&mut last);
        }
    }

    /// `f` on whole blocks.
    fn blocks(&self, iv: &mut [u8; 8], blocks: &mut [u8], f: Cfb) {
        // SAFETY: `rounds` is 12 or 16, as `Cast5Ecb::new` chose for the key
        // the schedule was expanded from; `blocks` holds `len / 8` whole
        // blocks, and it, the block at `iv` and the schedule are separate valid
        // objects of the sizes of the signature, none of them on the callee's
        // stack.
        unsafe {
            f(
                self.key.schedule(),
                self.key.rounds(),
                iv,
                blocks.as_mut_ptr().cast(),
                blocks.len() / 8,
            )
        };
    }
}
