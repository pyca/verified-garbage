//! TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) with two- and three-key TDEA
//! (16- and 24-byte keys) and the full 8-byte MAC.
//!
//! The computation is the verified assembly for the target architecture,
//! on a streaming state this module holds without looking into it:
//! `vg_cmac_triple_des_stream_init` (contract
//! `VG.Spec.Cmac.tdesStreamInitContract`) expands the key into the state,
//! `vg_cmac_triple_des_absorb` (`VG.Spec.Cmac.tdesAbsorbContract`) absorbs
//! data, holding back the message's last bytes, and
//! `vg_cmac_triple_des_finish` (`VG.Spec.Cmac.tdesFinishContract`) writes the
//! MAC. This module keeps the length of the message so far, which the state
//! does not store, and compares MACs.
//!
//! TDEA's 64-bit block makes it a poor choice for new protocols (see NIST
//! SP 800-131A): this is for interoperating with existing ones.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use super::{InvalidKeyLength, InvalidMac};
use crate::arch::cmac_triple_des::{
    vg_cmac_triple_des_absorb, vg_cmac_triple_des_finish, vg_cmac_triple_des_stream_init,
};
use crate::zeroize::zeroize;

/// The streaming state, in 64-bit words.
const STATE: usize = 52;

/// An incremental TDEA-CMAC computation.
///
/// A computation that has absorbed nothing yet can be cloned to MAC several
/// messages with the same key without expanding it again.
///
/// Messages are limited to 2⁶⁴ − 1 bytes.
#[derive(Clone)]
pub struct TripleDesCmac {
    /// The streaming state (`VG.Spec.Cmac.tdesRepr`): the key schedule, the
    /// subkeys, the chaining value and the bytes held back.
    state: [u64; STATE],
    /// The length of the message the state represents, in bytes.
    count: u64,
}

impl Drop for TripleDesCmac {
    /// Wipes the streaming state, which holds the key schedule.
    fn drop(&mut self) {
        zeroize(&mut self.state);
    }
}

impl TripleDesCmac {
    /// The size of the MAC, in bytes.
    pub const MAC_SIZE: usize = 8;

    /// Starts a TDEA-CMAC computation with `key`, which must be 16 bytes
    /// (two-key TDEA: `K1 ‖ K2`, with `K3 = K1`) or 24 bytes (three-key
    /// TDEA: `K1 ‖ K2 ‖ K3`) long. The DES keys' parity bits are ignored.
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 16 | 24) {
            return Err(InvalidKeyLength);
        }
        let mut c = TripleDesCmac {
            state: [0; STATE],
            count: 0,
        };
        // SAFETY: `c.state` is valid for reads and writes of 416 bytes, and
        // `key` for reads of `key.len()` bytes, which is 16 or 24. `c.state`
        // is a local and `key` a borrow, so neither overlaps the other, the
        // return address (on x86-64 and x86), the arguments on the stack (on
        // 32-bit ARM and x86) or the stack below them that the function uses,
        // and neither wraps around the end of the address space.
        unsafe { vg_cmac_triple_des_stream_init(&mut c.state, key.as_ptr(), key.len()) };
        Ok(c)
    }

    /// Absorbs `data`.
    ///
    /// # Panics
    ///
    /// If the message reaches 2⁶⁴ bytes.
    pub fn update(&mut self, data: &[u8]) {
        let count = self
            .count
            .checked_add(data.len() as u64)
            .expect("message too long");
        // SAFETY: `self.state` is valid for reads and writes of 416 bytes
        // and `data` for reads of `data.len()` bytes. `self.state` is a
        // mutable borrow and `data` a borrow, so neither overlaps the other,
        // the return address (on x86-64 and x86), the arguments on the stack
        // (on 32-bit ARM and x86) or the stack below them that the function
        // uses, and neither wraps around the end of the address space. The
        // state represents a message of `self.count` bytes, which with
        // `data` is shorter than 2⁶⁴ bytes, as the contract's postcondition
        // requires.
        unsafe {
            vg_cmac_triple_des_absorb(&mut self.state, self.count, data.as_ptr(), data.len())
        };
        self.count = count;
    }

    /// Returns the MAC of everything absorbed.
    pub fn finalize(mut self) -> [u8; 8] {
        let mut mac = [0; 8];
        // SAFETY: `self.state` is valid for reads and writes of 416 bytes
        // and `mac` for writes of 8. `self.state` is owned and `mac` a
        // local, so neither overlaps the other, the return address (on x86-64
        // and x86), the arguments on the stack (on 32-bit ARM and x86) or the
        // stack below them that the function uses, and neither wraps around
        // the end of the address space. The state represents a message of
        // `self.count` bytes, as the contract's postcondition requires.
        unsafe { vg_cmac_triple_des_finish(&mut self.state, self.count, &mut mac) };
        mac
    }

    /// Checks that `mac` is the MAC of everything absorbed, in constant
    /// time: the time taken does not depend on where, or whether, `mac`
    /// differs from it (its length is public). `mac` must be the whole MAC,
    /// of [`MAC_SIZE`](Self::MAC_SIZE) bytes; a truncated one is rejected.
    pub fn verify(self, mac: &[u8]) -> Result<(), InvalidMac> {
        if crate::ct::eq(&self.finalize(), mac) {
            Ok(())
        } else {
            Err(InvalidMac)
        }
    }

    /// The MAC of `data` with `key`, which must be 16 or 24 bytes long.
    pub fn mac(key: &[u8], data: &[u8]) -> Result<[u8; 8], InvalidKeyLength> {
        let mut c = Self::new(key)?;
        c.update(data);
        Ok(c.finalize())
    }
}

#[cfg(test)]
mod tests {
    use super::TripleDesCmac;
    use crate::cmac::{InvalidKeyLength, InvalidMac};

    /// Keys of other lengths are rejected.
    #[test]
    fn key_lengths() {
        for len in [0, 8, 15, 17, 23, 25, 32] {
            assert_eq!(
                TripleDesCmac::new(&[0; 32][..len]).err(),
                Some(InvalidKeyLength)
            );
            assert_eq!(
                TripleDesCmac::mac(&[0; 32][..len], b"").err(),
                Some(InvalidKeyLength)
            );
        }
    }

    /// Absorbing a message in two pieces, split anywhere, gives the MAC of
    /// the whole, also from a clone of a computation that absorbed nothing.
    #[test]
    fn splits() {
        let key: [u8; 24] = core::array::from_fn(|i| 0x2b ^ i as u8);
        let msg: [u8; 30] = core::array::from_fn(|i| i as u8);
        let fresh = TripleDesCmac::new(&key).unwrap();
        for len in 0..=msg.len() {
            let mac = TripleDesCmac::mac(&key, &msg[..len]).unwrap();
            for split in 0..=len {
                let mut c = fresh.clone();
                c.update(&msg[..split]);
                c.update(&msg[split..len]);
                assert_eq!(c.finalize(), mac, "{split} of {len}");
            }
        }
    }

    /// A message of 2⁶⁴ bytes or more is refused.
    #[test]
    #[should_panic(expected = "message too long")]
    fn too_long() {
        let mut c = TripleDesCmac::new(&[0; 16]).unwrap();
        c.count = u64::MAX;
        c.update(b"x");
    }

    /// A two-key TDEA key is the three-key one with `K3 = K1`.
    #[test]
    fn two_keys() {
        let key: [u8; 16] = core::array::from_fn(|i| 0x51 ^ (7 * i) as u8);
        let three = [&key[..], &key[..8]].concat();
        for len in [0, 7, 8, 9, 24] {
            let msg = [0xa5; 24];
            assert_eq!(
                TripleDesCmac::mac(&key, &msg[..len]),
                TripleDesCmac::mac(&three, &msg[..len])
            );
        }
    }

    /// `verify` accepts the MAC, and nothing else: not a MAC with a bit
    /// flipped, nor a truncated one.
    #[test]
    fn verify() {
        let key = [0x3c; 16];
        let mac = TripleDesCmac::mac(&key, b"message").unwrap();
        let check = |m: &[u8]| {
            let mut c = TripleDesCmac::new(&key).unwrap();
            c.update(b"message");
            c.verify(m)
        };
        assert_eq!(check(&mac), Ok(()));
        for i in 0..8 {
            let mut bad = mac;
            bad[i] ^= 1;
            assert_eq!(check(&bad), Err(InvalidMac));
        }
        assert_eq!(check(&mac[..7]), Err(InvalidMac));
    }
}
