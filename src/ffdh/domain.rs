//! The FFDH operations, entirely in verified code: the domain, public-key
//! and key-pair checks, one attempt at key generation and the exchange
//! (`VG.Spec.Ffdh`'s contracts). Rust lays out the domain, pads the values
//! to the modulus' width, allocates the working space, selects the
//! implementation for the CPU and retries key generation with fresh random
//! bytes.

use super::arithmetic::{Backend, scalar};
use crate::arch::ffdh::{
    vg_ffdh_check_domain, vg_ffdh_check_private, vg_ffdh_check_public, vg_ffdh_exchange,
    vg_ffdh_generate_key,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::ffdh::{
    vg_ffdh_check_domain_adx, vg_ffdh_check_private_adx, vg_ffdh_check_public_adx,
    vg_ffdh_exchange_adx, vg_ffdh_generate_key_adx,
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
        };
        // SAFETY: `bytes` is `2 p_len` or `3 p_len` bytes for a `p_len` in
        // 64..=1024, and `ws` is `16 p_len + 32` words; they are distinct
        // Rust objects. The ADX variant is selected only when the CPU has
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
        };
        // SAFETY: `self.bytes` is a domain laid out by `new`, `y` is `p_len`
        // bytes and `ws` `16 p_len + 32` words; all are distinct objects.
        // The ADX variant is selected only when the CPU has its generated
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

    /// One attempt at a key pair from `p_len` random bytes `rand`: 1 and the
    /// scalar and public value in `x` and `y` (`p_len` bytes each), 2 for a
    /// scalar out of range, 3 for a degenerate public value
    /// (`vg_ffdh_generate_key`).
    pub(super) fn generate_key(&self, rand: &[u8], x: &mut [u8], y: &mut [u8]) -> u32 {
        assert!(rand.len() == self.p_len && x.len() == self.p_len && y.len() == self.p_len);
        let mut ws = scratch(self.p_len);
        let f = match Backend::ffdh(detected()) {
            Backend::Baseline => vg_ffdh_generate_key,
            #[cfg(target_arch = "x86_64")]
            Backend::Adx => vg_ffdh_generate_key_adx,
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
