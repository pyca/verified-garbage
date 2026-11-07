//! XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) with 256-, 384- and 512-bit
//! keys (AES-128, AES-192 and AES-256), with ciphertext stealing for a data
//! unit that is not of whole blocks: from one buffer to another
//! ([`AesXts::encrypt`], [`AesXts::decrypt`]) or in place
//! ([`AesXts::encrypt_in_place`], [`AesXts::decrypt_in_place`]).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::aes::vg_aes_expand_key_auto;
use crate::arch::dispatch::aes_xts::{vg_aes_xts_decrypt_unit_auto, vg_aes_xts_encrypt_unit_auto};
#[cfg(target_arch = "x86_64")]
use crate::arch::dispatch::aes_xts::{
    vg_aes_xts_decrypt_unit_to_auto, vg_aes_xts_encrypt_unit_to_auto,
};
use crate::zeroize::zeroize;

/// The most blocks a data unit may have (IEEE Std 1619-2007 §5.1, NIST SP
/// 800-38E).
pub const XTS_MAX_BLOCKS: usize = 1 << 20;

/// Why an XTS-AES operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum XtsError {
    /// The key is not 32, 48 or 64 bytes long.
    InvalidKeyLength,
    /// The two halves of the key, `Key1` and `Key2`, are equal, which
    /// SP 800-38E's implementation guidance (FIPS 140-3 IG C.I) forbids.
    EqualKeyHalves,
    /// The data unit is shorter than one block (16 bytes).
    DataUnitTooShort,
    /// The data unit is longer than [`XTS_MAX_BLOCKS`] blocks.
    DataUnitTooLong,
    /// The output of [`AesXts::encrypt`] or [`AesXts::decrypt`] is not
    /// as long as the data unit.
    InvalidOutputLength,
}

crate::error::impl_error! {
    XtsError {
        InvalidKeyLength => "invalid AES-XTS key length",
        EqualKeyHalves => "AES-XTS key halves are equal",
        DataUnitTooShort => "AES-XTS data unit is shorter than a block",
        DataUnitTooLong => "AES-XTS data unit is too long",
        InvalidOutputLength => "AES-XTS output is not as long as the data unit",
    }
}

/// An XTS-AES key, `Key1 ‖ Key2`, expanded for encryption and decryption.
///
/// Each operation takes a whole data unit, of 16 bytes or more, and its
/// 16-byte tweak value `i` (for a storage device, usually the data unit's
/// number, little-endian); a data unit that is not of whole blocks is
/// processed with ciphertext stealing.
pub struct AesXts {
    /// The key schedule of `Key1`, which enciphers the data.
    data_schedule: [u8; 240],
    /// The key schedule of `Key2`, which enciphers the tweak value.
    tweak_schedule: [u8; 240],
    /// The number of rounds of AES: 10, 12 or 14.
    rounds: usize,
}

/// Checks a data unit's length, as the verified functions require it.
fn check_len(len: usize) -> Result<(), XtsError> {
    if len < 16 {
        return Err(XtsError::DataUnitTooShort);
    }
    if len > 16 * XTS_MAX_BLOCKS {
        return Err(XtsError::DataUnitTooLong);
    }
    Ok(())
}

impl AesXts {
    /// Expands a 32-, 48- or 64-byte key, `Key1 ‖ Key2`, for use in either
    /// direction.
    pub fn new(key: &[u8]) -> Result<Self, XtsError> {
        crate::dit::enter!(dit);
        if !matches!(key.len(), 32 | 48 | 64) {
            return Err(XtsError::InvalidKeyLength);
        }
        let (key1, key2) = key.split_at(key.len() / 2);
        // Without branching on the key's bytes, only on whether they are all
        // equal.
        if crate::ct::eq(dit, key1, key2) {
            return Err(XtsError::EqualKeyHalves);
        }
        let mut data_schedule = [0; 240];
        let mut tweak_schedule = [0; 240];
        // SAFETY: each half of the key is 16, 24 or 32 bytes long; it and its
        // schedule are separate valid buffers of the sizes of the signature.
        // The dispatcher calls only an implementation the CPU has the
        // features of.
        unsafe {
            vg_aes_expand_key_auto(dit, key1.as_ptr(), key1.len(), &mut data_schedule);
            vg_aes_expand_key_auto(dit, key2.as_ptr(), key2.len(), &mut tweak_schedule);
        }
        Ok(Self {
            data_schedule,
            tweak_schedule,
            rounds: key1.len() / 4 + 6,
        })
    }

    /// Encrypts the data unit `buffer` in place with the tweak value `i`
    /// (§5.3.2). Returns an error without changing the buffer if it is
    /// shorter than 16 bytes or longer than [`XTS_MAX_BLOCKS`] blocks.
    pub fn encrypt_in_place(&self, i: &[u8; 16], buffer: &mut [u8]) -> Result<(), XtsError> {
        crate::dit::enter!(dit);
        self.unit(dit, true, i, buffer)
    }

    /// Decrypts the data unit `buffer` in place with the tweak value `i`
    /// (§5.4.2). Returns an error without changing the buffer if it is
    /// shorter than 16 bytes or longer than [`XTS_MAX_BLOCKS`] blocks.
    pub fn decrypt_in_place(&self, i: &[u8; 16], buffer: &mut [u8]) -> Result<(), XtsError> {
        crate::dit::enter!(dit);
        self.unit(dit, false, i, buffer)
    }

    /// Encrypts (`enc`) or decrypts the data unit `buffer` in place with the
    /// tweak value `i`, after checking its length.
    fn unit(
        &self,
        dit: crate::dit::Dit<'_>,
        enc: bool,
        i: &[u8; 16],
        buffer: &mut [u8],
    ) -> Result<(), XtsError> {
        check_len(buffer.len())?;
        let mut scratch = [0; 304];
        // SAFETY: `rounds` is 10, 12 or 14 and the schedules hold its key
        // schedules; `buffer` holds `len` bytes, at least 16 and at most
        // `XTS_MAX_BLOCKS` blocks; it, the tweak value, the schedules and the
        // scratch space are separate valid objects of the sizes of the
        // signature. The dispatcher calls only an implementation the CPU has
        // the features of.
        unsafe {
            if enc {
                vg_aes_xts_encrypt_unit_auto(
                    dit,
                    &self.data_schedule,
                    &self.tweak_schedule,
                    self.rounds,
                    i,
                    buffer.as_mut_ptr(),
                    buffer.len(),
                    &mut scratch,
                );
            } else {
                vg_aes_xts_decrypt_unit_auto(
                    dit,
                    &self.data_schedule,
                    &self.tweak_schedule,
                    self.rounds,
                    i,
                    buffer.as_mut_ptr(),
                    buffer.len(),
                    &mut scratch,
                );
            }
        }
        // The scratch space may hold the key schedule, the tweaks, the data
        // and our caller's registers.
        zeroize(&mut scratch);
        Ok(())
    }

    /// Encrypts the data unit `src` with the tweak value `i` (§5.3.2) into
    /// `dst`, which must be as long. Returns an error without changing `dst`
    /// if it is not, or if `src` is shorter than 16 bytes or longer than
    /// [`XTS_MAX_BLOCKS`] blocks.
    pub fn encrypt(&self, i: &[u8; 16], src: &[u8], dst: &mut [u8]) -> Result<(), XtsError> {
        crate::dit::enter!(dit);
        self.unit_to(dit, true, i, src, dst)
    }

    /// Decrypts the data unit `src` with the tweak value `i` (§5.4.2) into
    /// `dst`, which must be as long. Returns an error without changing `dst`
    /// if it is not, or if `src` is shorter than 16 bytes or longer than
    /// [`XTS_MAX_BLOCKS`] blocks.
    pub fn decrypt(&self, i: &[u8; 16], src: &[u8], dst: &mut [u8]) -> Result<(), XtsError> {
        crate::dit::enter!(dit);
        self.unit_to(dit, false, i, src, dst)
    }

    /// Encrypts (`enc`) or decrypts the data unit `src` into `dst`, after
    /// checking their lengths, with the out-of-place function.
    #[cfg(target_arch = "x86_64")]
    fn unit_to(
        &self,
        dit: crate::dit::Dit<'_>,
        enc: bool,
        i: &[u8; 16],
        src: &[u8],
        dst: &mut [u8],
    ) -> Result<(), XtsError> {
        if src.len() != dst.len() {
            return Err(XtsError::InvalidOutputLength);
        }
        check_len(src.len())?;
        let mut scratch = [0; 304];
        // SAFETY: `rounds` is 10, 12 or 14 and the schedules hold its key
        // schedules; `src` and `dst` hold `len` bytes each, at least 16 and at
        // most `XTS_MAX_BLOCKS` blocks; they (`dst` being a `&mut`), the tweak
        // value, the schedules and the scratch space are separate valid objects
        // of the sizes of the signature. The dispatcher calls only an
        // implementation the CPU has the features of.
        unsafe {
            if enc {
                vg_aes_xts_encrypt_unit_to_auto(
                    dit,
                    &self.data_schedule,
                    &self.tweak_schedule,
                    self.rounds,
                    i,
                    src.as_ptr(),
                    src.len(),
                    dst.as_mut_ptr(),
                    dst.len(),
                    &mut scratch,
                );
            } else {
                vg_aes_xts_decrypt_unit_to_auto(
                    dit,
                    &self.data_schedule,
                    &self.tweak_schedule,
                    self.rounds,
                    i,
                    src.as_ptr(),
                    src.len(),
                    dst.as_mut_ptr(),
                    dst.len(),
                    &mut scratch,
                );
            }
        }
        // The scratch space may hold the key schedule, the tweaks, the data
        // and our caller's registers.
        zeroize(&mut scratch);
        Ok(())
    }

    /// Encrypts (`enc`) or decrypts the data unit `src` into `dst`, after
    /// checking their lengths: a copy, transformed in place.
    #[cfg(not(target_arch = "x86_64"))]
    fn unit_to(
        &self,
        dit: crate::dit::Dit<'_>,
        enc: bool,
        i: &[u8; 16],
        src: &[u8],
        dst: &mut [u8],
    ) -> Result<(), XtsError> {
        if src.len() != dst.len() {
            return Err(XtsError::InvalidOutputLength);
        }
        check_len(src.len())?;
        dst.copy_from_slice(src);
        if enc {
            self.unit(dit, true, i, dst)
        } else {
            self.unit(dit, false, i, dst)
        }
    }
}

impl Drop for AesXts {
    fn drop(&mut self) {
        zeroize(&mut self.data_schedule);
        zeroize(&mut self.tweak_schedule);
    }
}
