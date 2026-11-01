//! The FFDH operations, entirely in verified code: the domain, public-key
//! and key-pair checks, key generation and the exchange (`VG.Spec.Ffdh`'s
//! contracts). Key generation's whole rejection search is verified
//! (`vg_ffdh_generate_key_search`, or its cached entry point on ARMv7/AArch64).
//! Rust lays out the domain, pads the values to the modulus' width,
//! allocates the working space and selects the implementation for the CPU.

use super::arithmetic::{Backend, scalar};
#[cfg(not(any(target_arch = "arm", target_arch = "aarch64")))]
use crate::arch::ffdh::vg_ffdh_generate_key_search;
use crate::arch::ffdh::{
    vg_ffdh_check_domain, vg_ffdh_check_private, vg_ffdh_check_public, vg_ffdh_exchange,
    vg_ffdh_key_generation_init,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::ffdh::{
    vg_ffdh_check_domain_adx, vg_ffdh_check_private_adx, vg_ffdh_check_public_adx,
    vg_ffdh_derive_public_adx, vg_ffdh_exchange_adx, vg_ffdh_generate_key_search_adx,
};
use crate::cpu::detected;
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
    #[cfg(any(target_arch = "arm", target_arch = "aarch64"))]
    precomputed: super::precomputed::Precomputed,
}

impl Domain {
    /// Lays out p (without leading zeros, 64 to 1024 bytes), g and q,
    /// each padded to p's width, and checks them (`vg_ffdh_check_domain`).
    /// `None` for an invalid domain.
    pub(super) fn new(p: &[u8], g: &[u8], q: Option<&[u8]>) -> Option<Self> {
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
        let f = match Backend::ffdh(detected()) {
            Backend::Baseline => vg_ffdh_check_domain,
            #[cfg(target_arch = "x86_64")]
            Backend::Adx => vg_ffdh_check_domain_adx,
            #[cfg(target_arch = "arm")]
            Backend::Umaal => crate::arch::ffdh::vg_ffdh_check_domain_umaal,
        };
        // SAFETY: `bytes` is `2 p_len` or `3 p_len` bytes for a `p_len` in
        // 64..=1024, and `ws` is `16 p_len + 32` words; they are distinct
        // Rust objects. The CPU variant is selected only when the CPU has
        // its generated feature set.
        let ok = unsafe {
            f(
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
        #[cfg(any(target_arch = "arm", target_arch = "aarch64"))]
        let precomputed = super::precomputed::Precomputed::new(&bytes, p_len, &mut ws);
        Some(Self {
            bytes,
            p_len,
            #[cfg(any(target_arch = "arm", target_arch = "aarch64"))]
            precomputed,
        })
    }

    #[cfg(any(target_arch = "arm", target_arch = "aarch64"))]
    pub(super) fn exponent_len(&self) -> usize {
        self.precomputed.exponent_len()
    }

    /// Whether `y` (without leading zeros) is a valid public value
    /// (`vg_ffdh_check_public`).
    pub(super) fn check_public(&self, y: &[u8]) -> bool {
        if y.len() > self.p_len {
            return false;
        }
        let y = scalar(y, self.p_len);
        let mut ws = scratch(self.p_len);
        let f = match Backend::ffdh(detected()) {
            Backend::Baseline => vg_ffdh_check_public,
            #[cfg(target_arch = "x86_64")]
            Backend::Adx => vg_ffdh_check_public_adx,
            #[cfg(target_arch = "arm")]
            Backend::Umaal => crate::arch::ffdh::vg_ffdh_check_public_umaal,
        };
        // SAFETY: `self.bytes` is a domain laid out by `new`, `y` is `p_len`
        // bytes and `ws` `16 p_len + 32` words; all are distinct objects.
        // The CPU variant is selected only when the CPU has its generated
        // feature set.
        unsafe {
            f(
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
    pub(super) fn check_private(&self, y: &[u8], x: &[u8]) -> bool {
        if y.len() > self.p_len || x.is_empty() || x.len() > self.p_len {
            return false;
        }
        let y = scalar(y, self.p_len);
        let mut ws = scratch(self.p_len);
        let f = match Backend::ffdh(detected()) {
            Backend::Baseline => vg_ffdh_check_private,
            #[cfg(target_arch = "x86_64")]
            Backend::Adx => vg_ffdh_check_private_adx,
            #[cfg(target_arch = "arm")]
            Backend::Umaal => crate::arch::ffdh::vg_ffdh_check_private_umaal,
        };
        // SAFETY: as in `check_public`, and `x` is 1 to `p_len` bytes.
        unsafe {
            f(
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
    pub(super) fn derive_public(&self, x: &[u8], y: &mut [u8]) -> u32 {
        assert!(!x.is_empty() && x.len() <= self.p_len && y.len() == self.p_len);
        let mut ws = scratch(self.p_len);
        let f = match Backend::ffdh(detected()) {
            Backend::Baseline => crate::arch::ffdh::vg_ffdh_derive_public,
            #[cfg(target_arch = "arm")]
            Backend::Umaal => crate::arch::ffdh::vg_ffdh_derive_public_umaal,
            #[cfg(target_arch = "x86_64")]
            Backend::Adx => vg_ffdh_derive_public_adx,
        };
        // SAFETY: `y` is `p_len` bytes, `x` 1 to `p_len`, the domain, `ws`
        // and the variant as in `check_public`; all are distinct objects.
        unsafe {
            f(
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
    pub(super) fn key_state(&self) -> [u64; 16] {
        let mut state = [0; 16];
        // SAFETY: `state` is 16 writable words, a Rust object of its own.
        let ok = unsafe { vg_ffdh_key_generation_init(&mut state, self.p_len) };
        // A checked domain's `p_len` is in 64..=1024, which init accepts.
        assert_eq!(ok, 1);
        state
    }

    /// Run the key search on `tape` into `x` and `y` (`p_len` bytes each):
    /// the status (1 for a key pair, 3 for a budget exhausted, 0 for more
    /// entropy), the bytes of the tape consumed and the next request.
    /// ARMv7 and AArch64 call `vg_ffdh_generate_key_search_cached`, given the
    /// public context `new` computed; other architectures
    /// `vg_ffdh_generate_key_search`.
    pub(super) fn key_search(
        &self,
        state: &mut [u64; 16],
        tape: &[u8],
        x: &mut [u8],
        y: &mut [u8],
    ) -> (u32, usize, usize) {
        assert!(x.len() == self.p_len && y.len() == self.p_len);
        let mut ws = scratch(self.p_len);
        #[cfg(any(target_arch = "arm", target_arch = "aarch64"))]
        let f = match Backend::ffdh(detected()) {
            Backend::Baseline => crate::arch::ffdh::vg_ffdh_generate_key_search_cached,
            #[cfg(target_arch = "arm")]
            Backend::Umaal => crate::arch::ffdh::vg_ffdh_generate_key_search_cached_umaal,
        };
        #[cfg(not(any(target_arch = "arm", target_arch = "aarch64")))]
        let f = match Backend::ffdh(detected()) {
            Backend::Baseline => vg_ffdh_generate_key_search,
            #[cfg(target_arch = "x86_64")]
            Backend::Adx => vg_ffdh_generate_key_search_adx,
        };
        let mut used = [0u64; 1];
        // SAFETY: `state` came from `key_state` for this domain and has only
        // been passed to this function since, which keeps its words as the
        // contract's precondition needs; the domain was checked by
        // `vg_ffdh_check_domain`; `x` and `y` are `p_len` bytes and `ws`
        // `16 p_len + 32` words. All are distinct Rust objects. The CPU
        // variant is selected only when the CPU has its generated feature
        // set. The public context is the immutable canonical allocation written
        // once for this checked domain and its exact ctx_len.
        let status = unsafe {
            f(
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
                #[cfg(any(target_arch = "arm", target_arch = "aarch64"))]
                self.precomputed.words().as_ptr(),
                #[cfg(any(target_arch = "arm", target_arch = "aarch64"))]
                self.precomputed.words().len(),
            )
        };
        (status, used[0] as usize, state[3] as usize)
    }

    /// One attempt at a key pair from `p_len` random bytes `rand`: 1 and the
    /// scalar and public value in `x` and `y` (`p_len` bytes each), 2 for a
    /// scalar out of range, 3 for a degenerate public value (the cached
    /// entry point of `vg_ffdh_generate_key`).
    #[cfg(all(test, any(target_arch = "arm", target_arch = "aarch64")))]
    pub(super) fn generate_key(&self, rand: &[u8], x: &mut [u8], y: &mut [u8]) -> u32 {
        assert!(rand.len() == self.p_len && x.len() == self.p_len && y.len() == self.p_len);
        let mut ws = scratch(self.p_len);
        let f = match Backend::ffdh(detected()) {
            Backend::Baseline => crate::arch::ffdh::vg_ffdh_generate_key_cached,
            #[cfg(target_arch = "arm")]
            Backend::Umaal => crate::arch::ffdh::vg_ffdh_generate_key_cached_umaal,
        };
        // SAFETY: `x`, `y` and `rand` are `p_len` bytes each, the domain,
        // `ws` and the variant as in `check_public`; all are distinct
        // objects.
        unsafe {
            f(
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
    pub(super) fn exchange(&self, x: &[u8], y: &[u8], out: &mut [u8]) -> bool {
        assert!(
            !x.is_empty()
                && x.len() <= self.p_len
                && y.len() <= self.p_len
                && out.len() == self.p_len
        );
        let y = scalar(y, self.p_len);
        let mut ws = scratch(self.p_len);
        let f = match Backend::ffdh(detected()) {
            Backend::Baseline => vg_ffdh_exchange,
            #[cfg(target_arch = "x86_64")]
            Backend::Adx => vg_ffdh_exchange_adx,
            #[cfg(target_arch = "arm")]
            Backend::Umaal => crate::arch::ffdh::vg_ffdh_exchange_umaal,
        };
        // SAFETY: `out` and `y` are `p_len` bytes, `x` 1 to `p_len`, the
        // domain, `ws` and the variant as in `check_public`; all are
        // distinct objects.
        unsafe {
            f(
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

#[cfg(all(test, any(target_arch = "arm", target_arch = "aarch64")))]
mod cache_tests {
    use super::*;

    #[test]
    fn clones_share_immutable_context_and_keep_it_alive() {
        // Structurally valid legacy-size domain; imported domains do not
        // claim a primality certificate. x=3 yields y=8 here.
        let mut p = alloc::vec![0; 64];
        p[0] = 0x80;
        p[63] = 1;
        let domain = Domain::new(&p, &[2], None).unwrap();
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
            assert_eq!(cloned.generate_key(&draw, &mut x, &mut y), 1);
            assert_eq!(x, draw);
            assert_eq!(super::super::arithmetic::canonical(&y), &[8]);
            assert_eq!(cloned.precomputed.words(), expected);
        }
    }

    #[cfg(target_arch = "arm")]
    #[test]
    fn canonical_context_crosses_arithmetic_backends() {
        // Feature-forced baseline CI runs take the first path; UMAAL runs
        // also exercise both directions with the actual generated functions.
        if Backend::ffdh(detected()) != Backend::Umaal {
            return;
        }
        let mut p = alloc::vec![0; 64];
        p[0] = 0x80;
        p[63] = 1;
        // Exercise an uncapped domain and a published vetted group without
        // deriving or repeating their sampling policy in Rust.
        let vetted = super::super::vetted_tests::modp_groups().remove(0);
        for p in [p, vetted] {
            let domain = Domain::new(&p, &[2], None).unwrap();
            let mut ws = scratch(domain.p_len);
            let baseline = super::super::precomputed::Precomputed::new_with_backend(
                &domain.bytes,
                domain.p_len,
                &mut ws,
                Backend::Baseline,
            );
            let umaal = super::super::precomputed::Precomputed::new_with_backend(
                &domain.bytes,
                domain.p_len,
                &mut ws,
                Backend::Umaal,
            );
            // Every word of the context is the same.
            assert_eq!(baseline.words(), umaal.words());
            let mut draw = alloc::vec![0; domain.p_len];
            draw[domain.p_len - 1] = 3;
            let (mut expected_x, mut expected_y) =
                (alloc::vec![0; domain.p_len], alloc::vec![0; domain.p_len]);
            let expected = domain.generate_key(&draw, &mut expected_x, &mut expected_y);
            for (context, backend) in [(&baseline, Backend::Umaal), (&umaal, Backend::Baseline)] {
                let f = match backend {
                    Backend::Baseline => crate::arch::ffdh::vg_ffdh_generate_key_cached,
                    Backend::Umaal => crate::arch::ffdh::vg_ffdh_generate_key_cached_umaal,
                };
                let (mut x, mut y) = (alloc::vec![0; domain.p_len], alloc::vec![0; domain.p_len]);
                // SAFETY: domain was checked, context was initialized for these
                // exact parameters by the opposite arithmetic backend, all byte
                // outputs/draw have p_len entries, ws has the required capacity,
                // allocations are disjoint, and the CPU supports both backends.
                let status = unsafe {
                    f(
                        x.as_mut_ptr(),
                        x.len(),
                        y.as_mut_ptr(),
                        y.len(),
                        domain.bytes.as_ptr(),
                        domain.bytes.len(),
                        domain.p_len,
                        draw.as_ptr(),
                        draw.len(),
                        ws.as_mut_ptr(),
                        ws.len(),
                        context.words().as_ptr(),
                        context.words().len(),
                    )
                };
                assert_eq!(status, expected);
                assert_eq!(x, expected_x);
                assert_eq!(y, expected_y);
                assert_eq!(context.words(), domain.precomputed.words());
            }
        }
    }
}
