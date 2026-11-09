//! AES-CMAC (NIST SP 800-38B, RFC 4493) with 128-, 192- and 256-bit keys and
//! the full 16-byte MAC.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::align::CacheAligned;
use crate::arch::dispatch::cmac_aes::{
    vg_cmac_aes_absorb_auto, vg_cmac_aes_finish_auto, vg_cmac_aes_init_auto,
};
use crate::error::{InvalidKeyLength, InvalidMac};
use crate::zeroize::zeroize;

/// The streaming state, in 64-bit words.
const STATE: usize = 38;

/// An incremental AES-CMAC computation.
///
/// A computation that has absorbed nothing yet can be cloned to MAC several
/// messages with the same key without expanding it again.
///
/// Messages are limited to 2⁶⁴ − 1 bytes.
#[derive(Clone)]
pub struct AesCmac {
    /// The streaming state (`VG.Spec.Cmac.Repr`): the key schedule, the
    /// subkeys, the chaining value and the bytes held back.
    state: CacheAligned<[u64; STATE]>,
    /// The number of rounds of AES for the key.
    rounds: usize,
    /// The length of the message the state represents, in bytes.
    count: u64,
}

impl Drop for AesCmac {
    /// Wipes the streaming state, which holds the key schedule.
    fn drop(&mut self) {
        zeroize(&mut self.state.0);
    }
}

impl AesCmac {
    /// The size of the MAC, in bytes.
    pub const MAC_SIZE: usize = 16;

    /// Starts an AES-CMAC computation with `key`, which must be 16, 24 or 32
    /// bytes long (AES-128, AES-192 or AES-256).
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        crate::dit::enter!(dit);
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(InvalidKeyLength);
        }
        let mut c = AesCmac {
            state: CacheAligned([0; STATE]),
            rounds: key.len() / 4 + 6,
            count: 0,
        };
        // SAFETY: `c.state` is valid for reads and writes of 304 bytes,
        // and `key` for reads of `key.len()` bytes, which is 16, 24 or 32.
        // `c.state` is a local and `key` a borrow, so neither overlaps the
        // other, the return address (on x86-64 and x86), the arguments on the
        // stack (on 32-bit ARM and x86) or the stack below them that the
        // function uses, and neither wraps around the end of the address
        // space. The dispatcher calls only an implementation the CPU has the
        // features of.
        unsafe { vg_cmac_aes_init_auto(dit, &mut c.state.0, key.as_ptr(), key.len()) };
        Ok(c)
    }

    /// Absorbs `data`.
    ///
    /// # Panics
    ///
    /// If the message reaches 2⁶⁴ bytes.
    pub fn update(&mut self, data: &[u8]) {
        crate::dit::enter!(dit);
        let count = self
            .count
            .checked_add(data.len() as u64)
            .expect("message too long");
        // SAFETY: `self.state` is valid for reads and writes of 304 bytes
        // and `data` for reads of `data.len()` bytes. `self.state` is a
        // mutable borrow and `data` a borrow, so neither overlaps the other,
        // the return address (on x86-64 and x86), the arguments on the stack
        // (on 32-bit ARM and x86) or the stack below them that the function
        // uses, and neither wraps around the end of the address space. `self.rounds` is 10, 12 or
        // 14, that of the key `new` was given. The state represents a
        // message of `self.count` bytes, which with `data` is shorter than
        // 2⁶⁴ bytes, as the contract's postcondition requires. The
        // dispatcher calls only an implementation the CPU has the features
        // of.
        unsafe {
            vg_cmac_aes_absorb_auto(
                dit,
                &mut self.state.0,
                self.rounds,
                self.count,
                data.as_ptr(),
                data.len(),
            )
        };
        self.count = count;
    }

    /// Returns the MAC of everything absorbed.
    pub fn finalize(self) -> [u8; 16] {
        crate::dit::enter!(dit);
        self.finalize_with(dit)
    }

    /// [`finalize`](Self::finalize), with the token of the operation it is
    /// part of (see `crate::dit`).
    fn finalize_with(mut self, dit: crate::dit::Dit<'_>) -> [u8; 16] {
        let mut mac = [0; 16];
        // SAFETY: `self.state` is valid for reads and writes of 304 bytes
        // and `mac` for writes of 16. `self.state` is owned and `mac` a
        // local, so neither overlaps the other, the return address (on x86-64
        // and x86), the arguments on the stack (on 32-bit ARM and x86) or the
        // stack below them that the function uses, and neither wraps around
        // the end of the address space. `self.rounds`
        // is 10, 12 or 14, that of the key `new` was given, and the state
        // represents a message of `self.count` bytes, as the contract's
        // postcondition requires. The dispatcher calls only an implementation
        // the CPU has the features of.
        unsafe {
            vg_cmac_aes_finish_auto(dit, &mut self.state.0, self.rounds, self.count, &mut mac)
        };
        mac
    }

    /// Checks that `mac` is the MAC of everything absorbed, in constant
    /// time: the time taken does not depend on where, or whether, `mac`
    /// differs from it (its length is public). `mac` must be the whole MAC,
    /// of [`MAC_SIZE`](Self::MAC_SIZE) bytes; a truncated one is rejected.
    pub fn verify(self, mac: &[u8]) -> Result<(), InvalidMac> {
        crate::dit::enter!(dit);
        if crate::ct::eq(dit, &self.finalize_with(dit), mac) {
            Ok(())
        } else {
            Err(InvalidMac)
        }
    }

    /// The MAC of `data` with `key`, which must be 16, 24 or 32 bytes long.
    pub fn mac(key: &[u8], data: &[u8]) -> Result<[u8; 16], InvalidKeyLength> {
        let mut c = Self::new(key)?;
        c.update(data);
        Ok(c.finalize())
    }
}

#[cfg(test)]
mod tests {
    use super::AesCmac;
    use crate::error::InvalidKeyLength;

    /// Keys of other lengths are rejected.
    #[test]
    fn key_lengths() {
        for len in [0, 15, 17, 23, 25, 31, 33, 64] {
            assert_eq!(AesCmac::new(&[0; 64][..len]).err(), Some(InvalidKeyLength));
            assert_eq!(
                AesCmac::mac(&[0; 64][..len], b"").err(),
                Some(InvalidKeyLength)
            );
        }
    }

    /// Absorbing a message in two pieces, split anywhere, gives the MAC of
    /// the whole, also from a clone of a computation that absorbed nothing.
    #[test]
    fn splits() {
        let key = [0x2b; 16];
        let msg: [u8; 50] = core::array::from_fn(|i| i as u8);
        let fresh = AesCmac::new(&key).unwrap();
        for len in 0..=msg.len() {
            let mac = AesCmac::mac(&key, &msg[..len]).unwrap();
            for split in 0..=len {
                let mut c = fresh.clone();
                c.update(&msg[..split]);
                c.update(&msg[split..len]);
                assert_eq!(c.finalize(), mac, "{split} of {len}");
            }
        }
    }

    /// Absorbing a message a byte at a time gives the MAC of the whole.
    #[test]
    fn bytes() {
        let key = [0x2b; 32];
        let msg: [u8; 70] = core::array::from_fn(|i| (3 * i) as u8);
        let mut c = AesCmac::new(&key).unwrap();
        for b in msg {
            c.update(&[b]);
        }
        assert_eq!(c.finalize(), AesCmac::mac(&key, &msg).unwrap());
    }

    /// A message of 2⁶⁴ bytes or more is refused.
    #[test]
    #[should_panic(expected = "message too long")]
    fn too_long() {
        let mut c = AesCmac::new(&[0; 16]).unwrap();
        c.count = u64::MAX;
        c.update(b"x");
    }
}
