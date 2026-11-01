//! SM4 ECB (GB/T 32907-2016, as transcribed in draft-ribose-cfrg-sm4-10;
//! SP 800-38A §6.1), in place and without padding.
//!
//! ECB is the block cipher applied to each block on its own, so the whole
//! mode is verified assembly: `vg_sm4_expand_key` (contract
//! `VG.Spec.Sm4.expandKeyContract`) writes the key schedule, and
//! `vg_sm4_ecb_encrypt` and `vg_sm4_ecb_decrypt` (`ecbEncryptContract`,
//! `ecbDecryptContract`) replace each block with its encryption or
//! decryption, in constant time. Each operation accepts complete 16-byte
//! blocks, including empty input.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::sm4::{vg_sm4_ecb_decrypt, vg_sm4_ecb_encrypt, vg_sm4_expand_key};
use crate::zeroize::zeroize;

/// Why a SM4 ECB operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The input length is not a multiple of 16 bytes.
    IncompleteBlock,
}

crate::error::impl_error! {
    Error {
        IncompleteBlock => "SM4-ECB input is not a whole number of blocks",
    }
}

/// An expanded SM4 key for ECB encryption and decryption.
///
/// No padding is added or removed.
// Aligned to 8 bytes, which makes the functions faster on RISC-V.
#[repr(C, align(8))]
pub struct Sm4Ecb {
    schedule: [u8; 128],
}

impl Sm4Ecb {
    /// Expands a 16-byte key for use in either direction.
    pub fn new(key: &[u8; 16]) -> Self {
        let mut schedule = [0; 128];
        // SAFETY: key and schedule are separate valid buffers of the
        // required sizes. The function zeroes its working space on its own
        // stack before returning.
        unsafe {
            vg_sm4_expand_key(key, &mut schedule);
        }
        Self { schedule }
    }

    /// Encrypts complete 16-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn encrypt(&self, buffer: &mut [u8]) -> Result<(), Error> {
        self.crypt(buffer, true)
    }

    /// Decrypts complete 16-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn decrypt(&self, buffer: &mut [u8]) -> Result<(), Error> {
        self.crypt(buffer, false)
    }

    fn crypt(&self, buffer: &mut [u8], encrypt: bool) -> Result<(), Error> {
        if !buffer.len().is_multiple_of(16) {
            return Err(Error::IncompleteBlock);
        }
        let f = if encrypt {
            vg_sm4_ecb_encrypt
        } else {
            vg_sm4_ecb_decrypt
        };
        // SAFETY: buffer contains complete 16-byte blocks, including zero
        // blocks. The buffer and schedule are separate valid objects and do
        // not overlap the callee's stack. The function zeroes its working
        // space on its own stack before returning.
        unsafe {
            f(
                &self.schedule,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 16,
            );
        }
        Ok(())
    }
}

impl Drop for Sm4Ecb {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Eight-byte aligned storage for a schedule at an offset.
    #[repr(align(8))]
    struct Aligned([u8; 136]);

    /// The functions take the schedule at any address: from copies at every
    /// offset modulo 8 they compute what they compute from the context's.
    #[test]
    fn unaligned_schedule() {
        let ctx = Sm4Ecb::new(&[0x5a; 16]);
        let input: [u8; 64] = core::array::from_fn(|i| (i * 13) as u8);
        for encrypt in [true, false] {
            let mut expected = input;
            ctx.crypt(&mut expected, encrypt).unwrap();
            for offset in 0..8 {
                let mut storage = Aligned([0; 136]);
                storage.0[offset..offset + 128].copy_from_slice(&ctx.schedule);
                let mut output = input;
                // SAFETY: the schedule's copy and the output are separate
                // valid objects, and the output holds four whole blocks.
                unsafe {
                    let schedule = storage.0.as_ptr().add(offset).cast();
                    if encrypt {
                        vg_sm4_ecb_encrypt(schedule, output.as_mut_ptr().cast(), 4);
                    } else {
                        vg_sm4_ecb_decrypt(schedule, output.as_mut_ptr().cast(), 4);
                    }
                }
                assert_eq!(output, expected);
            }
        }
    }
}
