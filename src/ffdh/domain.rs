//! The FFDH operations: the domain, public-key and key-pair checks, key
//! generation and the exchange.

use super::arithmetic::scalar;
#[cfg(test)]
use crate::arch::dispatch::ffdh::vg_ffdh_generate_key_cached_auto;
use crate::arch::dispatch::ffdh::vg_ffdh_key_generation_init_auto;
use crate::arch::dispatch::ffdh::{
    vg_ffdh_check_domain_auto, vg_ffdh_check_private_auto, vg_ffdh_check_public_auto,
    vg_ffdh_derive_public_auto, vg_ffdh_exchange_auto, vg_ffdh_generate_key_search_cached_auto,
};
use crate::rsa::Scratch;

/// The working space every function needs, `16 p_len + 32` words.
fn scratch(p_len: usize) -> Scratch {
    Scratch::new(16 * p_len + 32)
}

/// A checked domain: p, g and, if present, q, each `p_len` bytes.
#[derive(Clone, Debug)]
pub(super) struct Domain {
    bytes: alloc::vec::Vec<u8>,
    p_len: usize,
    precomputed: super::precomputed::Precomputed,
}

impl Domain {
    /// Lays out p (without leading zeros, 64 to 1024 bytes), g and q,
    /// each padded to p's width, and checks them (`vg_ffdh_check_domain`).
    /// `None` for an invalid domain.
    pub(super) fn new(
        dit: crate::dit::Dit<'_>,
        p: &[u8],
        g: &[u8],
        q: Option<&[u8]>,
    ) -> Option<Self> {
        let p_len = p.len();
        if !(64..=1024).contains(&p_len) || g.len() > p_len || q.is_some_and(|q| q.len() > p_len) {
            return None;
        }
        let mut bytes = alloc::vec![0; p_len * if q.is_some() { 3 } else { 2 }];
        bytes[..p_len].copy_from_slice(p);
        bytes[2 * p_len - g.len()..2 * p_len].copy_from_slice(g);
        if let Some(q) = q {
            bytes[3 * p_len - q.len()..].copy_from_slice(q);
        }
        let mut ws = scratch(p_len);
        // SAFETY: `bytes` is `2 p_len` or `3 p_len` bytes for a `p_len` in
        // 64..=1024, and `ws` is `16 p_len + 32` words; they are distinct
        // Rust objects. The dispatcher calls only an implementation the CPU
        // has the features of.
        let ok = unsafe {
            vg_ffdh_check_domain_auto(
                dit,
                bytes.as_ptr(),
                bytes.len(),
                p_len,
                ws.as_mut_ptr(),
                ws.len(),
            )
        };
        if ok != 1 {
            return None;
        }
        let precomputed = super::precomputed::Precomputed::new(dit, &bytes, p_len, &mut ws);
        Some(Self {
            bytes,
            p_len,
            precomputed,
        })
    }

    pub(super) fn exponent_len(&self) -> usize {
        self.precomputed.exponent_len()
    }

    /// Whether `y` (without leading zeros) is a valid public value
    /// (`vg_ffdh_check_public`).
    pub(super) fn check_public(&self, dit: crate::dit::Dit<'_>, y: &[u8]) -> bool {
        if y.len() > self.p_len {
            return false;
        }
        let y = scalar(y, self.p_len);
        let mut ws = scratch(self.p_len);
        // SAFETY: `self.bytes` is a domain laid out by `new`, `y` is `p_len`
        // bytes and `ws` `16 p_len + 32` words; all are distinct objects.
        // The dispatcher calls only an implementation the CPU has the
        // features of.
        unsafe {
            vg_ffdh_check_public_auto(
                dit,
                self.bytes.as_ptr(),
                self.bytes.len(),
                self.p_len,
                y.as_ptr(),
                y.len(),
                ws.as_mut_ptr(),
                ws.len(),
            ) == 1
        }
    }

    /// Whether `x` (1 to `p_len` bytes) and `y` (without leading zeros) are
    /// a valid key pair (`vg_ffdh_check_private`).
    pub(super) fn check_private(&self, dit: crate::dit::Dit<'_>, y: &[u8], x: &[u8]) -> bool {
        if y.len() > self.p_len || x.is_empty() || x.len() > self.p_len {
            return false;
        }
        let y = scalar(y, self.p_len);
        let mut ws = scratch(self.p_len);
        // SAFETY: as in `check_public`, and `x` is 1 to `p_len` bytes.
        unsafe {
            vg_ffdh_check_private_auto(
                dit,
                self.bytes.as_ptr(),
                self.bytes.len(),
                self.p_len,
                y.as_ptr(),
                y.len(),
                x.as_ptr(),
                x.len(),
                ws.as_mut_ptr(),
                ws.len(),
            ) == 1
        }
    }

    /// The public value `g^x mod p` of the scalar `x` (1 to `p_len` bytes)
    /// into `y` (`p_len` bytes): 1, or 2 for a scalar out of range and 3 for
    /// a degenerate public value, with zeros (`vg_ffdh_derive_public`).
    pub(super) fn derive_public(&self, dit: crate::dit::Dit<'_>, x: &[u8], y: &mut [u8]) -> u32 {
        assert!(!x.is_empty() && x.len() <= self.p_len && y.len() == self.p_len);
        let mut ws = scratch(self.p_len);
        // SAFETY: `y` is `p_len` bytes, `x` 1 to `p_len`, the domain, `ws`
        // and the dispatcher as in `check_public`; all are distinct objects.
        unsafe {
            vg_ffdh_derive_public_auto(
                dit,
                y.as_mut_ptr(),
                y.len(),
                self.bytes.as_ptr(),
                self.bytes.len(),
                self.p_len,
                x.as_ptr(),
                x.len(),
                ws.as_mut_ptr(),
                ws.len(),
            )
        }
    }

    /// The key-generation controller's 16 words for this domain: the
    /// rejection budgets, `p_len` and the first request, then private
    /// working space (`vg_ffdh_key_generation_init`).
    pub(super) fn key_state(&self, dit: crate::dit::Dit<'_>) -> [u64; 16] {
        let mut state = [0; 16];
        // SAFETY: `state` is 16 writable words, a Rust object of its own.
        let ok = unsafe { vg_ffdh_key_generation_init_auto(dit, &mut state, self.p_len) };
        // A checked domain's `p_len` is in 64..=1024, which init accepts.
        assert_eq!(ok, 1);
        state
    }

    /// Run the key search on `tape` into `x` and `y` (`p_len` bytes each):
    /// the status (1 for a key pair, 3 for a budget exhausted, 0 for more
    /// entropy), the bytes of the tape consumed and the next request.
    /// It calls `vg_ffdh_generate_key_search_cached`, given the public
    /// context `new` computed.
    pub(super) fn key_search(
        &self,
        dit: crate::dit::Dit<'_>,
        state: &mut [u64; 16],
        tape: &[u8],
        x: &mut [u8],
        y: &mut [u8],
    ) -> (u32, usize, usize) {
        assert!(x.len() == self.p_len && y.len() == self.p_len);
        let mut ws = scratch(self.p_len);
        let mut used = [0u64; 1];
        // SAFETY: `state` came from `key_state` for this domain and has only
        // been passed to this function since, which keeps its words as the
        // contract's precondition needs; the domain was checked by
        // `vg_ffdh_check_domain`; `x` and `y` are `p_len` bytes and `ws`
        // `16 p_len + 32` words. All are distinct Rust objects. The
        // dispatcher calls only an implementation the CPU has the features
        // of. The public context is the immutable canonical allocation written
        // once for this checked domain and its exact ctx_len.
        let status = unsafe {
            vg_ffdh_generate_key_search_cached_auto(
                dit,
                x.as_mut_ptr(),
                x.len(),
                y.as_mut_ptr(),
                y.len(),
                &mut used,
                self.bytes.as_ptr(),
                self.bytes.len(),
                self.p_len,
                tape.as_ptr(),
                tape.len(),
                ws.as_mut_ptr(),
                ws.len(),
                state,
                self.precomputed.words().as_ptr(),
                self.precomputed.words().len(),
            )
        };
        (status, used[0] as usize, state[3] as usize)
    }

    /// One attempt at a key pair from `p_len` random bytes `rand`: 1 and the
    /// scalar and public value in `x` and `y` (`p_len` bytes each), 2 for a
    /// scalar out of range, 3 for a degenerate public value (the cached
    /// entry point of `vg_ffdh_generate_key`).
    #[cfg(test)]
    pub(super) fn generate_key(
        &self,
        dit: crate::dit::Dit<'_>,
        rand: &[u8],
        x: &mut [u8],
        y: &mut [u8],
    ) -> u32 {
        assert!(rand.len() == self.p_len && x.len() == self.p_len && y.len() == self.p_len);
        let mut ws = scratch(self.p_len);
        // SAFETY: `x`, `y` and `rand` are `p_len` bytes each, the domain,
        // `ws` and the dispatcher as in `check_public`; all are distinct
        // objects.
        unsafe {
            vg_ffdh_generate_key_cached_auto(
                dit,
                x.as_mut_ptr(),
                x.len(),
                y.as_mut_ptr(),
                y.len(),
                self.bytes.as_ptr(),
                self.bytes.len(),
                self.p_len,
                rand.as_ptr(),
                rand.len(),
                ws.as_mut_ptr(),
                ws.len(),
                self.precomputed.words().as_ptr(),
                self.precomputed.words().len(),
            )
        }
    }

    /// The shared value of the scalar `x` (1 to `p_len` bytes) and the
    /// checked peer value `y` (without leading zeros) into `out` (`p_len`
    /// bytes), or `false` and zeros for a degenerate one
    /// (`vg_ffdh_exchange`).
    pub(super) fn exchange(
        &self,
        dit: crate::dit::Dit<'_>,
        x: &[u8],
        y: &[u8],
        out: &mut [u8],
    ) -> bool {
        assert!(
            !x.is_empty()
                && x.len() <= self.p_len
                && y.len() <= self.p_len
                && out.len() == self.p_len
        );
        let y = scalar(y, self.p_len);
        let mut ws = scratch(self.p_len);
        // SAFETY: `out` and `y` are `p_len` bytes, `x` 1 to `p_len`, the
        // domain, `ws` and the dispatcher as in `check_public`; all are
        // distinct objects.
        unsafe {
            vg_ffdh_exchange_auto(
                dit,
                out.as_mut_ptr(),
                out.len(),
                self.bytes.as_ptr(),
                self.bytes.len(),
                self.p_len,
                x.as_ptr(),
                x.len(),
                y.as_ptr(),
                y.len(),
                ws.as_mut_ptr(),
                ws.len(),
            ) == 1
        }
    }
}

#[cfg(test)]
mod cache_tests {
    use super::Domain;

    #[test]
    fn clones_share_immutable_context_and_keep_it_alive() {
        let dit = crate::dit::public(crate::dit::Why::Test);
        // Structurally valid legacy-size domain; imported domains do not
        // claim a primality certificate. x=3 yields y=8 here.
        let mut p = alloc::vec![0; 64];
        p[0] = 0x80;
        p[63] = 1;
        let domain = Domain::new(dit, &p, &[2], None).unwrap();
        let cloned = domain.clone();
        assert!(domain.precomputed.shares_allocation(&cloned.precomputed));
        assert_eq!(domain.precomputed.words().len(), 3 + 34 * 8);
        assert_eq!(domain.exponent_len(), 64);
        let expected = domain.precomputed.words().to_vec();
        drop(domain);
        let mut draw = alloc::vec![0; 64];
        draw[63] = 3;
        for _ in 0..2 {
            let (mut x, mut y) = (alloc::vec![0; 64], alloc::vec![0; 64]);
            assert_eq!(cloned.generate_key(dit, &draw, &mut x, &mut y), 1);
            assert_eq!(x, draw);
            assert_eq!(super::super::arithmetic::canonical(&y), &[8]);
            assert_eq!(cloned.precomputed.words(), expected);
        }
    }
}
