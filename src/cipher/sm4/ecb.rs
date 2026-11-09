//! SM4-ECB (GB/T 32907-2016, as transcribed in draft-ribose-cfrg-sm4-10; SP
//! 800-38A §6.1), in place and without padding.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::align::CacheAligned;
use crate::arch::dispatch::sm4::{
    vg_sm4_ecb_decrypt_auto, vg_sm4_ecb_encrypt_auto, vg_sm4_expand_key_auto,
};
use crate::error::IncompleteBlock;
use crate::zeroize::zeroize;

/// An expanded SM4 key for ECB encryption and decryption.
///
/// No padding is added or removed. ECB encrypts equal blocks to equal blocks,
/// so it reveals patterns in the data.
// Aligned to a cache line, by its schedule (at least 8 bytes make the
// functions faster on RISC-V).
pub struct Sm4Ecb {
    schedule: CacheAligned<[u8; 128]>,
}

impl Sm4Ecb {
    /// Expands a 16-byte key for use in either direction.
    pub fn new(key: &[u8; 16]) -> Self {
        let mut schedule = CacheAligned([0; 128]);
        crate::dit::enter!(dit);
        // SAFETY: key and schedule are separate valid buffers of the required
        // sizes.
        unsafe {
            vg_sm4_expand_key_auto(dit, key, &mut schedule.0);
        }
        Self { schedule }
    }

    /// Encrypts complete 16-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn encrypt(&self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        self.crypt(buffer, true)
    }

    /// Decrypts complete 16-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn decrypt(&self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        self.crypt(buffer, false)
    }

    fn crypt(&self, buffer: &mut [u8], encrypt: bool) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(16) {
            return Err(IncompleteBlock);
        }
        let f = if encrypt {
            vg_sm4_ecb_encrypt_auto
        } else {
            vg_sm4_ecb_decrypt_auto
        };
        crate::dit::enter!(dit);
        // SAFETY: buffer contains complete 16-byte blocks, including zero
        // blocks. The buffer and schedule are separate valid objects and do not
        // overlap the callee's stack.
        unsafe {
            f(
                dit,
                &self.schedule.0,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 16,
            );
        }
        Ok(())
    }
}

impl Drop for Sm4Ecb {
    fn drop(&mut self) {
        zeroize(&mut self.schedule.0);
    }
}

#[cfg(test)]
mod tests {
    use super::{Sm4Ecb, vg_sm4_ecb_decrypt_auto, vg_sm4_ecb_encrypt_auto};

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
                storage.0[offset..offset + 128].copy_from_slice(&ctx.schedule.0);
                let mut output = input;
                let dit = crate::dit::public(crate::dit::Why::Test);
                // SAFETY: the schedule's copy and the output are separate
                // valid objects, and the output holds four whole blocks.
                unsafe {
                    let schedule = storage.0.as_ptr().add(offset).cast();
                    if encrypt {
                        vg_sm4_ecb_encrypt_auto(dit, schedule, output.as_mut_ptr().cast(), 4);
                    } else {
                        vg_sm4_ecb_decrypt_auto(dit, schedule, output.as_mut_ptr().cast(), 4);
                    }
                }
                assert_eq!(output, expected);
            }
        }
    }
}
