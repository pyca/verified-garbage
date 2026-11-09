//! RC2-CBC (RFC 2268), in place and without padding.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "arm",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use crate::align::CacheAligned;
use crate::arch::dispatch::rc2::vg_rc2_cbc_init_auto;
use crate::arch::dispatch::rc2_cbc::{
    vg_rc2_cbc_decrypt_chained_auto, vg_rc2_cbc_encrypt_chained_auto,
};
use crate::error::IncompleteBlock;
use crate::zeroize::zeroize;

/// The key length is outside 1..=128 bytes.
pub use crate::error::InvalidKeyLength;

/// Why an RC2-CBC encryptor or decryptor was not created.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key length is outside 1..=128 bytes.
    InvalidKeyLength,
    /// The effective key size is outside 1..=1024 bits.
    InvalidEffectiveBits,
}

crate::error::impl_error! {
    Error {
        InvalidKeyLength => "invalid RC2 key length",
        InvalidEffectiveBits => "invalid RC2 effective key size",
    }
}

/// An RC2-CBC encryption (or, if `DECRYPT`, decryption), which
/// [`Rc2CbcEncryptor`] and [`Rc2CbcDecryptor`] wrap.
struct Cbc<const DECRYPT: bool> {
    /// The verified primitives' context: key schedule, chaining value and
    /// unused space for pending bytes (always empty at this API).
    ctx: CacheAligned<[u8; 144]>,
}

impl<const DECRYPT: bool> Cbc<DECRYPT> {
    /// Initializes CBC with an effective key size of `effective_bits`.
    fn new(key: &[u8], iv: &[u8; 8], effective_bits: usize) -> Result<Self, Error> {
        let mut ctx = Self {
            ctx: CacheAligned([0; 144]),
        };
        crate::dit::enter!(dit);
        // SAFETY: the key, IV and context are valid, separate objects of the
        // lengths passed; the primitive checks the lengths.
        let code = unsafe {
            vg_rc2_cbc_init_auto(
                dit,
                key.as_ptr(),
                key.len(),
                effective_bits,
                iv.as_ptr(),
                iv.len(),
                &mut ctx.ctx.0,
            )
        };
        match code {
            0 => Ok(ctx),
            1 => Err(Error::InvalidKeyLength),
            2 => Err(Error::InvalidEffectiveBits),
            // The fixed-size IV rules out the primitive's only other status.
            // NO-COVERAGE-START
            _ => unreachable!("RC2-CBC IV is exactly eight bytes"),
            // NO-COVERAGE-END
        }
    }

    /// Processes whole blocks in place, preserving the chaining value.
    fn crypt(&mut self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(8) {
            return Err(IncompleteBlock);
        }
        let crypt = if DECRYPT {
            vg_rc2_cbc_decrypt_chained_auto
        } else {
            vg_rc2_cbc_encrypt_chained_auto
        };
        let ctx = self.ctx.0.as_mut_ptr();
        crate::dit::enter!(dit);
        // SAFETY: initialization wrote the schedule in bytes 0..128 and the
        // IV in bytes 128..136 of the context. These regions and the buffer
        // are disjoint and valid for the signature's sizes. The buffer holds
        // exactly `len / 8` whole blocks; the primitive updates the IV to
        // continue the message, leaving it unchanged for empty input.
        unsafe {
            crypt(
                dit,
                ctx.cast(),
                ctx.add(128).cast(),
                buffer.as_mut_ptr().cast(),
                buffer.len() / 8,
            );
        }
        Ok(())
    }
}

impl<const DECRYPT: bool> Drop for Cbc<DECRYPT> {
    fn drop(&mut self) {
        zeroize(&mut self.ctx.0);
    }
}

/// An RC2-CBC encryption of one message, without padding.
///
/// Each call takes whole 8-byte blocks and continues from the last ciphertext
/// block of the previous call, so a message may be encrypted in pieces.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct Rc2CbcEncryptor {
    cbc: Cbc<false>,
}

impl Rc2CbcEncryptor {
    /// Initializes CBC, using the supplied key's bit length as the effective
    /// key size. Returns [`InvalidKeyLength`] unless the key contains
    /// 1..=128 bytes.
    pub fn new(key: &[u8], iv: &[u8; 8]) -> Result<Self, InvalidKeyLength> {
        Self::new_with_effective_bits(key, iv, key.len().saturating_mul(8))
            .map_err(|_| InvalidKeyLength)
    }

    /// Initializes CBC with an explicit effective key size of 1..=1024 bits,
    /// independently of the supplied key's length of 1..=128 bytes.
    /// Returns [`Error::InvalidKeyLength`] for an invalid key length or
    /// [`Error::InvalidEffectiveBits`] for an invalid effective key size.
    pub fn new_with_effective_bits(
        key: &[u8],
        iv: &[u8; 8],
        effective_bits: usize,
    ) -> Result<Self, Error> {
        Ok(Self {
            cbc: Cbc::new(key, iv, effective_bits)?,
        })
    }

    /// Encrypts whole 8-byte blocks in place, continuing the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 8.
    pub fn encrypt(&mut self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        self.cbc.crypt(buffer)
    }
}

/// An RC2-CBC decryption of one message, without padding.
///
/// Each call takes whole 8-byte blocks and continues from the last ciphertext
/// block of the previous call, so a message may be decrypted in pieces.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct Rc2CbcDecryptor {
    cbc: Cbc<true>,
}

impl Rc2CbcDecryptor {
    /// Initializes CBC, using the supplied key's bit length as the effective
    /// key size. Returns [`InvalidKeyLength`] unless the key contains
    /// 1..=128 bytes.
    pub fn new(key: &[u8], iv: &[u8; 8]) -> Result<Self, InvalidKeyLength> {
        Self::new_with_effective_bits(key, iv, key.len().saturating_mul(8))
            .map_err(|_| InvalidKeyLength)
    }

    /// Initializes CBC with an explicit effective key size of 1..=1024 bits,
    /// independently of the supplied key's length of 1..=128 bytes.
    /// Returns [`Error::InvalidKeyLength`] for an invalid key length or
    /// [`Error::InvalidEffectiveBits`] for an invalid effective key size.
    pub fn new_with_effective_bits(
        key: &[u8],
        iv: &[u8; 8],
        effective_bits: usize,
    ) -> Result<Self, Error> {
        Ok(Self {
            cbc: Cbc::new(key, iv, effective_bits)?,
        })
    }

    /// Decrypts whole 8-byte blocks in place, continuing the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 8.
    pub fn decrypt(&mut self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        self.cbc.crypt(buffer)
    }
}
