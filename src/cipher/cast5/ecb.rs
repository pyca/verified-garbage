//! CAST5-ECB (CAST-128, RFC 2144) with 5- to 16-byte keys (§2.5), in place and
//! without padding.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::align::CacheAligned;
use crate::arch::cast5::{vg_cast5_ecb_decrypt, vg_cast5_ecb_encrypt, vg_cast5_expand_key};
use crate::error::{IncompleteBlock, InvalidKeyLength};
use crate::zeroize::zeroize;

/// An expanded CAST5 key for ECB encryption and decryption.
///
/// ECB encrypts equal blocks to equal blocks, so it reveals patterns in the
/// data.
pub struct Cast5Ecb {
    schedule: CacheAligned<[u8; 128]>,
    rounds: usize,
}

impl Cast5Ecb {
    /// Expands a key of 5 to 16 bytes for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !(5..=16).contains(&key.len()) {
            return Err(InvalidKeyLength);
        }
        let mut schedule = CacheAligned([0; 128]);
        let mut scratch = CacheAligned([0; 32]);
        // SAFETY: the key has a validated length; the key, schedule and
        // scratch space are separate valid objects of the sizes of the
        // signature.
        unsafe {
            vg_cast5_expand_key(key.as_ptr(), key.len(), &mut schedule.0, &mut scratch.0);
        }
        // The scratch space holds the intermediate values of key expansion.
        zeroize(&mut scratch.0);
        Ok(Self {
            schedule,
            rounds: if key.len() <= 10 { 12 } else { 16 },
        })
    }

    /// Encrypts complete eight-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn encrypt(&self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        self.crypt(buffer, vg_cast5_ecb_encrypt)
    }

    /// Decrypts complete eight-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn decrypt(&self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        self.crypt(buffer, vg_cast5_ecb_decrypt)
    }

    /// The subkeys, for the other modes of CAST5.
    pub(crate) fn schedule(&self) -> &[u8; 128] {
        &self.schedule.0
    }

    /// The number of rounds, 12 or 16, for the modes built on CAST5.
    pub(crate) fn rounds(&self) -> usize {
        self.rounds
    }

    fn crypt(&self, buffer: &mut [u8], f: Ecb) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(8) {
            return Err(IncompleteBlock);
        }
        let mut scratch = CacheAligned([0; 32]);
        // SAFETY: `rounds` is 12 or 16, as `new` chose for the key the
        // schedule was expanded from; the buffer holds `len / 8` whole
        // blocks, and it, the schedule and the scratch space are separate
        // valid objects of the sizes of the signature.
        unsafe {
            f(
                &self.schedule.0,
                self.rounds,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 8,
                &mut scratch.0,
            );
        }
        // The scratch space may hold the subkeys, the data and our caller's
        // registers.
        zeroize(&mut scratch.0);
        Ok(())
    }
}

/// The signature of `vg_cast5_ecb_encrypt` and `vg_cast5_ecb_decrypt`.
#[cfg(target_arch = "x86_64")]
type Ecb = unsafe extern "sysv64" fn(*const [u8; 128], usize, *mut [u8; 8], usize, *mut [u64; 32]);
/// The signature of `vg_cast5_ecb_encrypt` and `vg_cast5_ecb_decrypt`.
#[cfg(any(
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
type Ecb = unsafe extern "C" fn(*const [u8; 128], usize, *mut [u8; 8], usize, *mut [u64; 32]);

impl Drop for Cast5Ecb {
    fn drop(&mut self) {
        zeroize(&mut self.schedule.0);
    }
}
