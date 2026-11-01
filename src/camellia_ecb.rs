//! Camellia ECB (RFC 3713), in place and without padding.
//!
//! ECB is the block cipher applied to each block on its own, so the whole
//! mode is verified assembly: `vg_camellia_expand_key` (contract
//! `VG.Spec.Camellia.expandKeyContract`) writes the subkeys, and
//! `vg_camellia_ecb_encrypt` and `vg_camellia_ecb_decrypt`
//! (`ecbEncryptContract`, `ecbDecryptContract`) replace each block with its
//! encryption or decryption, in constant time. Each operation accepts
//! complete 16-byte blocks, including empty input.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::camellia::{
    vg_camellia_ecb_decrypt, vg_camellia_ecb_encrypt, vg_camellia_expand_key,
};
use crate::zeroize::zeroize;

/// Why a Camellia ECB operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key does not contain 16, 24 or 32 bytes.
    InvalidKeyLength,
    /// The input length is not a multiple of 16 bytes.
    IncompleteBlock,
}

crate::error::impl_error! {
    Error {
        InvalidKeyLength => "invalid Camellia key length",
        IncompleteBlock => "Camellia-ECB input is not a whole number of blocks",
    }
}

/// An expanded Camellia key for ECB encryption and decryption.
///
/// Keys of 16 bytes use 18 rounds; keys of 24 or 32 bytes, 24. No padding
/// is added or removed.
pub struct CamelliaEcb {
    schedule: [u8; 272],
    rounds: usize,
}

impl CamelliaEcb {
    /// Expands a 16-, 24- or 32-byte key for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        let rounds = match key.len() {
            16 => 18,
            24 | 32 => 24,
            _ => return Err(Error::InvalidKeyLength),
        };
        let mut schedule = [0; 272];
        // SAFETY: the key has a validated length; key and schedule are separate
        // valid buffers of the required sizes.
        unsafe {
            vg_camellia_expand_key(key.as_ptr(), key.len(), &mut schedule);
        }
        Ok(Self { schedule, rounds })
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
            vg_camellia_ecb_encrypt
        } else {
            vg_camellia_ecb_decrypt
        };
        // SAFETY: `rounds` is 18 for a key of 16 bytes and 24 otherwise, as
        // `new` expanded the schedule for. The buffer contains complete 16-byte
        // blocks, including zero blocks. The buffer and schedule are separate
        // valid objects and do not overlap the callee's stack.
        unsafe {
            f(
                &self.schedule,
                self.rounds,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 16,
            );
        }
        Ok(())
    }
}

impl Drop for CamelliaEcb {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}

#[cfg(all(test, target_arch = "powerpc64", target_endian = "little"))]
mod prepared_tests {
    use super::*;
    use crate::arch::camellia::{vg_camellia_crypt_prepared, vg_camellia_prepare_keys};

    /// The words of the working space the functions use.
    const WORDS: usize = 414;

    /// The first word of the batch of eight blocks in the working space.
    const BATCH: usize = 386;

    #[test]
    fn prepared_batches_match_ecb_and_keep_extra_workspace() {
        for key_len in [16, 32] {
            let ctx = CamelliaEcb::new(&[0x63; 32][..key_len]).unwrap();
            for decrypt in [false, true] {
                let mut workspace = [0x7171_7171_7171_7171u64; WORDS + 18];
                // SAFETY: the schedule and working space are separate valid
                // objects, the space exceeds `WORDS` words, the direction is 0
                // or 1, and `rounds` is the one `new` expanded the schedule for.
                unsafe {
                    vg_camellia_prepare_keys(
                        &ctx.schedule,
                        ctx.rounds,
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
                    // SAFETY: the space holds the table left by the
                    // preparation for these rounds; writing the batch at words
                    // `BATCH..BATCH + 16` preserves that table.
                    unsafe {
                        vg_camellia_crypt_prepared(
                            ctx.rounds,
                            workspace.as_mut_ptr(),
                            workspace.len(),
                        );
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
}
