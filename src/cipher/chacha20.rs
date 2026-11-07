//! ChaCha20 (RFC 8439 §2.4), with the 16-byte nonce of OpenSSL and
//! pyca/cryptography: the 4-byte little-endian initial block counter, then RFC
//! 8439's 12-byte nonce.
//!
//! A nonce must never be used twice with the same key. As in RFC 8439, the
//! block counter is 32 bits, so a keystream that starts at block counter `c` is
//! 2³² − `c` blocks long: applying more of it panics, leaving the data
//! unchanged, rather than wrapping the counter or carrying it into the nonce as
//! OpenSSL does.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::chacha20::{vg_chacha20_init, vg_chacha20_set_nonce};
use crate::arch::dispatch::chacha20::vg_chacha20_apply_auto;
use crate::zeroize::zeroize_raw;
use core::mem::MaybeUninit;

/// A ChaCha20 keystream, applied incrementally.
///
/// `new` only stores the key and the nonce: `vg_chacha20_init` runs on the
/// first `apply_keystream`, on the state in place. Were `new` to run it, on
/// a local it then returns, the 776-byte state would be copied to the
/// caller's object: `init` is given the local's address, so the compiler
/// cannot build it in the caller's.
#[repr(C)]
pub struct ChaCha20 {
    /// The streaming state of `vg_chacha20_init` and `vg_chacha20_apply`
    /// (`VG.Spec.ChaCha20.restAt`): the key, the position in the keystream
    /// and the partly used block, then the working space of `apply`. Only
    /// the verified functions read or write it, and they read only bytes
    /// they have written, so it need not be initialized.
    state: MaybeUninit<[u64; 96]>,
    /// The key and the nonce of `new` (and `reset_nonce`), which `init`
    /// reads while `pending`.
    key: [u8; 32],
    nonce: [u8; 16],
    /// Whether `init` has yet to run: `state` holds nothing.
    pending: bool,
}

impl Drop for ChaCha20 {
    /// Wipes the whole object: the state, which holds the key and keystream
    /// (all of it, as the contract lets the functions write any of it), and
    /// the key.
    fn drop(&mut self) {
        // SAFETY: `self` is valid for writes of its size; it is a distinct
        // object, so it does not overlap the callee's stack frame or wrap
        // around the end of the address space. It is not used after the
        // drop, so its fields need not stay valid.
        unsafe { zeroize_raw((self as *mut Self).cast::<u8>(), size_of::<Self>()) };
    }
}

impl ChaCha20 {
    /// The size of a key, in bytes.
    pub const KEY_SIZE: usize = 32;
    /// The size of a nonce (initial block counter and RFC 8439 nonce), in bytes.
    pub const NONCE_SIZE: usize = 16;

    /// Starts the keystream for `key` and `nonce` (the initial block counter,
    /// little-endian, followed by the 12-byte RFC 8439 nonce).
    pub fn new(key: &[u8; 32], nonce: &[u8; 16]) -> Self {
        ChaCha20 {
            state: MaybeUninit::uninit(),
            key: *key,
            nonce: *nonce,
            pending: true,
        }
    }

    /// Runs `vg_chacha20_init` on the key and nonce stored.
    fn start(&mut self) {
        // SAFETY: `state` is valid for writes of 768 bytes (`init` reads none
        // of them), `key` for reads of 32 bytes and `nonce` for reads of 16
        // bytes; they are distinct fields, so they do not overlap each other
        // or the return address, and do not wrap around the end of the
        // address space.
        unsafe { vg_chacha20_init(self.state.as_mut_ptr(), &self.key, &self.nonce) };
        self.pending = false;
    }

    /// Restarts the keystream, with the same key, for `nonce`.
    pub fn reset_nonce(&mut self, nonce: &[u8; 16]) {
        if self.pending {
            self.nonce = *nonce;
            return;
        }
        // SAFETY: as in `start`, for `state` and `nonce` (`set_nonce` reads
        // no byte of `state` either).
        unsafe { vg_chacha20_set_nonce(self.state.as_mut_ptr(), nonce) };
    }

    /// XORs the next `data.len()` bytes of the keystream into `data`
    /// (encrypting or decrypting it).
    ///
    /// # Panics
    ///
    /// If the keystream is not that long: if the block counter would pass
    /// `0xffffffff`, i.e. if more than 64 × (2³² − `c`) bytes in all would
    /// have been applied since the nonce (with initial block counter `c`) was
    /// set. `data` is then left unchanged.
    pub fn apply_keystream(&mut self, data: &mut [u8]) {
        if self.pending {
            self.start();
        }
        // SAFETY: `state` is valid for reads and writes of 768 bytes (the
        // bytes `apply` reads before writing them are those `init` and
        // `set_nonce` wrote) and `data` for reads and writes of `data.len()`
        // bytes; they are
        // distinct objects, so they do not overlap each other, the stack
        // frame of the call (the return address) or the stack below it, and
        // do not wrap around the end of the address space. The dispatcher
        // calls only an implementation the CPU has the features of.
        let ok = unsafe {
            vg_chacha20_apply_auto(self.state.as_mut_ptr(), data.as_mut_ptr(), data.len())
        };
        // `apply` checks the block counter itself, and leaves the data and the
        // state unchanged when it would overflow.
        assert!(ok == 1, "ChaCha20 block counter would overflow");
    }
}

#[cfg(test)]
mod tests {
    use super::ChaCha20;

    fn unhex<const N: usize>(s: &str) -> [u8; N] {
        let mut out = [0u8; N];
        for (i, o) in out.iter_mut().enumerate() {
            *o = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap();
        }
        out
    }

    /// A fixed key, `00:01:…:1f`.
    fn key() -> [u8; 32] {
        core::array::from_fn(|i| i as u8)
    }

    /// A 16-byte nonce from an RFC 8439 block counter and nonce.
    fn nonce(counter: u32, nonce: &[u8; 12]) -> [u8; 16] {
        let mut n = [0u8; 16];
        n[..4].copy_from_slice(&counter.to_le_bytes());
        n[4..].copy_from_slice(nonce);
        n
    }

    /// The first `N` bytes of keystream.
    fn keystream<const N: usize>(key: &[u8; 32], nonce: &[u8; 16]) -> [u8; N] {
        let mut out = [0u8; N];
        ChaCha20::new(key, nonce).apply_keystream(&mut out);
        out
    }

    /// Applying the keystream in two pieces, or a byte at a time, is the
    /// same as applying it at once, for every split around block boundaries.
    #[test]
    fn incremental() {
        let n = nonce(7, &[3; 12]);
        let expected = keystream::<200>(&key(), &n);
        for split in 0..=200 {
            let mut data = [0u8; 200];
            let mut c = ChaCha20::new(&key(), &n);
            c.apply_keystream(&mut data[..split]);
            c.apply_keystream(&mut data[split..]);
            assert_eq!(data, expected);
        }
        let mut data = [0u8; 200];
        let mut c = ChaCha20::new(&key(), &n);
        for byte in data.chunks_mut(1) {
            c.apply_keystream(byte);
        }
        assert_eq!(data, expected);
    }

    /// `reset_nonce` restarts the keystream.
    #[test]
    fn reset_nonce() {
        let (n1, n2) = (nonce(0, &[1; 12]), nonce(5, &[2; 12]));
        let mut c = ChaCha20::new(&key(), &n1);
        let mut data = [0u8; 100];
        c.apply_keystream(&mut data);
        c.reset_nonce(&n2);
        let mut data = [0u8; 100];
        c.apply_keystream(&mut data);
        assert_eq!(data, keystream::<100>(&key(), &n2));
    }

    /// `reset_nonce` before any keystream is applied replaces the nonce of
    /// `new`.
    #[test]
    fn reset_nonce_first() {
        let (n1, n2) = (nonce(0, &[1; 12]), nonce(5, &[2; 12]));
        let mut c = ChaCha20::new(&key(), &n1);
        c.reset_nonce(&n2);
        let mut data = [0u8; 100];
        c.apply_keystream(&mut data);
        assert_eq!(data, keystream::<100>(&key(), &n2));
    }

    /// The keystream from block counter 0xffffffff is one block long,
    /// however it is applied, and `reset_nonce` starts a new one.
    #[test]
    fn last_block() {
        let n = nonce(0xffff_ffff, &unhex("0900000011223344aabbccdd"));
        let ks = keystream::<64>(&key(), &n);
        let mut c = ChaCha20::new(&key(), &n);
        let mut data = [0u8; 64];
        c.apply_keystream(&mut data[..10]);
        c.apply_keystream(&mut data[10..]);
        c.apply_keystream(&mut []);
        assert_eq!(data, ks);
        c.reset_nonce(&n);
        let mut data = [0u8; 64];
        c.apply_keystream(&mut data);
        assert_eq!(data, ks);
    }

    /// Applies `first` bytes of the keystream from block counter `counter`
    /// and then `then` more, which the tests below make too many.
    fn overflow(counter: u32, first: usize, then: usize) {
        let mut c = ChaCha20::new(&key(), &nonce(counter, &[4; 12]));
        let mut data = [0u8; 192];
        c.apply_keystream(&mut data[..first]);
        c.apply_keystream(&mut data[..then]);
    }

    /// Applying keystream past block counter 0xffffffff panics: in whole
    /// blocks, byte by byte, and after part of the last block.
    #[test]
    #[should_panic(expected = "ChaCha20 block counter would overflow")]
    fn overflow_whole_blocks() {
        overflow(0xffff_fffe, 0, 64 * 3);
    }

    #[test]
    #[should_panic(expected = "ChaCha20 block counter would overflow")]
    fn overflow_after_blocks() {
        overflow(0xffff_fffe, 64, 64 * 2);
    }

    #[test]
    #[should_panic(expected = "ChaCha20 block counter would overflow")]
    fn overflow_one_byte() {
        overflow(0xffff_ffff, 64, 1);
    }

    #[test]
    #[should_panic(expected = "ChaCha20 block counter would overflow")]
    fn overflow_partial_block() {
        overflow(0xffff_ffff, 10, 55);
    }

    /// Applying more keystream than is left leaves the data unchanged, and
    /// what is left of the keystream can still be applied.
    #[test]
    fn overflow_unchanged() {
        extern crate std;
        let n = nonce(0xffff_ffff, &[7; 12]);
        let ks = keystream::<64>(&key(), &n);
        let mut c = ChaCha20::new(&key(), &n);
        let mut data = [0u8; 64];
        c.apply_keystream(&mut data[..10]);
        let mut more = [0x5au8; 55];
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            c.apply_keystream(&mut more)
        }));
        assert!(r.is_err());
        assert_eq!(more, [0x5a; 55]);
        c.apply_keystream(&mut data[10..]);
        assert_eq!(data, ks);
    }

    /// Applying 35 blocks of keystream in two pieces, split every 61 bytes,
    /// is the same as applying them at once, also up to the last block
    /// counter.
    #[test]
    fn incremental_bulk() {
        const LEN: usize = 16 * 64 * 2 + 64 * 3;
        for counter in [0, 0u32.wrapping_sub((LEN / 64) as u32)] {
            let n = nonce(counter, &[5; 12]);
            let expected = keystream::<LEN>(&key(), &n);
            for split in (0..=LEN).step_by(61) {
                let mut data = [0u8; LEN];
                let mut c = ChaCha20::new(&key(), &n);
                c.apply_keystream(&mut data[..split]);
                c.apply_keystream(&mut data[split..]);
                assert_eq!(data, expected);
            }
        }
    }

    /// On unaligned slices the keystream is XORed into the data as at
    /// offset 0 into zeros, leaving the bytes around them unchanged, for
    /// lengths within a byte of multiples of a block, from three blocks to
    /// sixteen, and up to the last block counter.
    #[test]
    fn bulk_boundaries() {
        for len in [
            191, 192, 193, 255, 256, 257, 319, 320, 321, 383, 384, 385, 447, 448, 449, 511, 512,
            513, 575, 576, 577, 767, 768, 769, 1023, 1024,
        ] {
            for offset in [0, 1, 7, 15] {
                for counter in [7, u32::MAX - (len as u32).div_ceil(64) + 1] {
                    let n = nonce(counter, &[6; 12]);
                    let msg: [u8; 1040] = core::array::from_fn(|i| (i * 29) as u8);
                    let mut ks = [0u8; 1024];
                    ChaCha20::new(&key(), &n).apply_keystream(&mut ks[..len]);
                    let mut expected = msg;
                    for (e, k) in expected[offset..offset + len].iter_mut().zip(ks) {
                        *e ^= k;
                    }
                    let mut actual = msg;
                    ChaCha20::new(&key(), &n).apply_keystream(&mut actual[offset..offset + len]);
                    assert_eq!(actual, expected);
                    // Starting with a partial block gives the same keystream,
                    // up to the same final counter.
                    let mut fragmented = msg;
                    let mut c = ChaCha20::new(&key(), &n);
                    c.apply_keystream(&mut fragmented[offset..offset + 1]);
                    c.apply_keystream(&mut fragmented[offset + 1..offset + len]);
                    assert_eq!(fragmented, expected);
                }
            }
        }
    }
}
