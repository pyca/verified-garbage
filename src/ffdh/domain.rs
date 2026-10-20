//! The FFDH operations, entirely in verified code: the domain, public-key
//! and key-pair checks, key generation and the exchange (`VG.Spec.Ffdh`'s
//! contracts). Key generation's whole rejection search is verified
//! (`vg_ffdh_generate_key_search`, or its vetted-group entry point on ARM).
//! Rust lays out the domain, pads the values to the modulus' width,
//! allocates the working space and selects the implementation for the CPU.

use super::arithmetic::{Backend, scalar};
use crate::arch::ffdh::{
    vg_ffdh_check_domain, vg_ffdh_check_private, vg_ffdh_check_public, vg_ffdh_exchange,
    vg_ffdh_generate_key_search, vg_ffdh_key_generation_init,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::ffdh::{
    vg_ffdh_check_domain_adx, vg_ffdh_check_private_adx, vg_ffdh_check_public_adx,
    vg_ffdh_exchange_adx, vg_ffdh_generate_key_search_adx,
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
        (ok == 1).then_some(Self { bytes, p_len })
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
    /// entropy), the bytes of the tape consumed and the next request
    /// ARM uses `vg_ffdh_generate_key_search_vetted` for generator 2;
    /// other generators and architectures use the full-width search.
    pub(super) fn key_search(
        &self,
        state: &mut [u64; 16],
        tape: &[u8],
        x: &mut [u8],
        y: &mut [u8],
    ) -> (u32, usize, usize) {
        assert!(x.len() == self.p_len && y.len() == self.p_len);
        let mut ws = scratch(self.p_len);
        #[cfg(target_arch = "arm")]
        let f = {
            // The public generator occupies one padded domain component.
            // Exact prime and subgroup recognition remains in verified code.
            let generator = &self.bytes[self.p_len..2 * self.p_len];
            let vetted = generator[..self.p_len - 1].iter().all(|&byte| byte == 0)
                && generator[self.p_len - 1] == 2;
            match (Backend::ffdh(detected()), vetted) {
                (Backend::Baseline, false) => vg_ffdh_generate_key_search,
                (Backend::Baseline, true) => crate::arch::ffdh::vg_ffdh_generate_key_search_vetted,
                (Backend::Umaal, false) => crate::arch::ffdh::vg_ffdh_generate_key_search_umaal,
                (Backend::Umaal, true) => {
                    crate::arch::ffdh::vg_ffdh_generate_key_search_vetted_umaal
                }
            }
        };
        #[cfg(not(target_arch = "arm"))]
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
        // set.
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
            )
        };
        (status, used[0] as usize, state[3] as usize)
    }

    /// One attempt at a key pair from `p_len` random bytes `rand`: 1 and the
    /// scalar and public value in `x` and `y` (`p_len` bytes each), 2 for a
    /// scalar out of range, 3 for a degenerate public value
    /// (`vg_ffdh_generate_key`).
    #[cfg(test)]
    pub(super) fn generate_key(&self, rand: &[u8], x: &mut [u8], y: &mut [u8]) -> u32 {
        assert!(rand.len() == self.p_len && x.len() == self.p_len && y.len() == self.p_len);
        let mut ws = scratch(self.p_len);
        let f = match Backend::ffdh(detected()) {
            Backend::Baseline => crate::arch::ffdh::vg_ffdh_generate_key,
            #[cfg(target_arch = "x86_64")]
            Backend::Adx => crate::arch::ffdh::vg_ffdh_generate_key_adx,
            #[cfg(target_arch = "arm")]
            Backend::Umaal => crate::arch::ffdh::vg_ffdh_generate_key_umaal,
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
