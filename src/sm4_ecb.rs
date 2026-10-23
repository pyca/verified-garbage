//! SM4 ECB (GB/T 32907-2016, as transcribed in draft-ribose-cfrg-sm4-10;
//! SP 800-38A §6.1), in place and without padding.
//!
//! Key expansion and ECB encryption/decryption use verified primitives.
//! Each operation accepts complete 16-byte blocks, including empty input.
//! ECB runs sixteen blocks at a time, computing each round bitsliced in
//! general-purpose registers, with no table lookups.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little")
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

#[cfg(all(
    test,
    any(
        target_arch = "arm",
        all(target_arch = "powerpc64", target_endian = "little")
    )
))]
mod prepared_tests {
    use super::*;
    use crate::arch::sm4::{vg_sm4_crypt_prepared, vg_sm4_prepare_keys};

    /// The words of the working space the functions use.
    #[cfg(target_arch = "arm")]
    const WORDS: usize = 182;
    #[cfg(target_arch = "powerpc64")]
    const WORDS: usize = 402;

    /// The first word of the batch of sixteen blocks in the working space.
    #[cfg(target_arch = "arm")]
    const BATCH: usize = 32;
    #[cfg(target_arch = "powerpc64")]
    const BATCH: usize = 96;

    #[test]
    fn prepared_batches_match_ecb_and_keep_extra_workspace() {
        let ctx = Sm4Ecb::new(&[0x63; 16]);
        for decrypt in [false, true] {
            let mut workspace = [0x7171_7171_7171_7171u64; WORDS + 18];
            // SAFETY: the schedule and working space are separate valid
            // objects, the space exceeds `WORDS` words, and the direction is 0 or 1.
            unsafe {
                vg_sm4_prepare_keys(
                    &ctx.schedule,
                    usize::from(decrypt),
                    workspace.as_mut_ptr(),
                    workspace.len(),
                );
            }
            assert!(
                workspace[WORDS..]
                    .iter()
                    .all(|&w| w == 0x7171_7171_7171_7171)
            );
            for batch in 0..2 {
                let input: [u8; 128] = core::array::from_fn(|i| (i * 19 + batch * 7) as u8);
                let mut expected = input;
                if decrypt {
                    ctx.decrypt(&mut expected).unwrap();
                } else {
                    ctx.encrypt(&mut expected).unwrap();
                }
                for (word, bytes) in workspace[BATCH..BATCH + 16]
                    .iter_mut()
                    .zip(input.as_chunks::<8>().0)
                {
                    *word = u64::from_le_bytes(*bytes);
                }
                // SAFETY: the space holds the table left by the preparation;
                // writing the batch at words `BATCH..BATCH + 16` preserves that table.
                unsafe {
                    vg_sm4_crypt_prepared(workspace.as_mut_ptr(), workspace.len());
                }
                for (word, bytes) in workspace[BATCH..BATCH + 16]
                    .iter()
                    .zip(expected.as_chunks::<8>().0)
                {
                    assert_eq!(word.to_le_bytes(), *bytes);
                }
                assert!(
                    workspace[WORDS..]
                        .iter()
                        .all(|&w| w == 0x7171_7171_7171_7171)
                );
            }
            zeroize(&mut workspace);
        }
    }
}
