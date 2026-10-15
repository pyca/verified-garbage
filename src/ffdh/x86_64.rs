//! Verified FFDH key operations on x86-64. Rust pads the inputs,
//! allocates scratch space, and selects the shared arithmetic backend.

#![cfg(target_arch = "x86_64")]

use super::arithmetic::{Backend, scalar};
use crate::arch::ffdh::{
    vg_ffdh_check_domain, vg_ffdh_check_domain_adx, vg_ffdh_check_private,
    vg_ffdh_check_private_adx, vg_ffdh_check_public, vg_ffdh_check_public_adx, vg_ffdh_exchange,
    vg_ffdh_exchange_adx, vg_ffdh_generate_key, vg_ffdh_generate_key_adx,
    vg_ffdh_generate_parameters, vg_ffdh_generate_parameters_adx,
    vg_ffdh_parameter_generation_init,
};
use crate::cpu::detected;
use crate::rsa::Scratch;

/// Check canonical domain components using the verified domain validator.
pub(super) fn check_domain(p: &[u8], g: &[u8], q: Option<&[u8]>) -> bool {
    let len = p.len();
    if !(64..=1024).contains(&len) || g.len() > len || q.is_some_and(|q| q.len() > len) {
        return false;
    }
    let domain = pack_domain(p, g, q);
    let mut ws = Scratch::new(16 * len + 32);
    let f = match Backend::select(detected()) {
        Backend::Baseline => vg_ffdh_check_domain,
        Backend::Adx => vg_ffdh_check_domain_adx,
    };
    // SAFETY: len is 64..=1024, domain is exactly 2 or 3 such widths,
    // and scratch is 16*len+32 words. The allocations are disjoint.
    unsafe {
        f(
            domain.as_ptr(),
            domain.len(),
            len,
            ws.as_mut_ptr(),
            ws.len(),
        ) == 1
    }
}

/// Check a canonical public value in an already checked domain.
pub(super) fn check_public(p: &[u8], g: &[u8], q: Option<&[u8]>, y: &[u8]) -> bool {
    let len = p.len();
    if y.len() > len {
        return false;
    }
    let domain = pack_domain(p, g, q);
    let y = scalar(y, len);
    let mut ws = Scratch::new(16 * len + 32);
    let f = match Backend::select(detected()) {
        Backend::Baseline => vg_ffdh_check_public,
        Backend::Adx => vg_ffdh_check_public_adx,
    };
    // SAFETY: the checked domain has p in 64..=1024 bytes and g and q no
    // longer than p. The packed domain is 2 or 3 such widths, y is one
    // width, and scratch is 16*len+32 words. The allocations are disjoint.
    unsafe {
        f(
            domain.as_ptr(),
            domain.len(),
            len,
            y.as_ptr(),
            y.len(),
            ws.as_mut_ptr(),
            ws.len(),
        ) == 1
    }
}

/// Lay out domain components at the modulus width for the verified ABI.
fn pack_domain(p: &[u8], g: &[u8], q: Option<&[u8]>) -> alloc::vec::Vec<u8> {
    let len = p.len();
    let mut bytes = alloc::vec![0; len * if q.is_some() { 3 } else { 2 }];
    bytes[..len].copy_from_slice(p);
    bytes[2 * len - g.len()..2 * len].copy_from_slice(g);
    if let Some(q) = q {
        bytes[3 * len - q.len()..].copy_from_slice(q);
    }
    bytes
}

/// Exchange with a checked public value and a private scalar of public length.
pub(super) fn exchange(
    p: &[u8],
    g: &[u8],
    q: Option<&[u8]>,
    x: &[u8],
    y: &[u8],
    out: &mut [u8],
) -> bool {
    let len = p.len();
    assert!(!x.is_empty() && x.len() <= len && y.len() <= len && out.len() == len);
    let domain = pack_domain(p, g, q);
    let y = scalar(y, len);
    let mut ws = Scratch::new(16 * len + 32);
    let f = match Backend::select(detected()) {
        Backend::Baseline => vg_ffdh_exchange,
        Backend::Adx => vg_ffdh_exchange_adx,
    };
    // SAFETY: the domain and peer are already checked. The domain has 2 or
    // 3 modulus widths, peer and output one width each, scalar 1..=len
    // bytes, and scratch 16*len+32 words. The output and scratch are
    // disjoint from all inputs and each other.
    unsafe {
        f(
            out.as_mut_ptr(),
            out.len(),
            domain.as_ptr(),
            domain.len(),
            len,
            x.as_ptr(),
            x.len(),
            y.as_ptr(),
            y.len(),
            ws.as_mut_ptr(),
            ws.len(),
        ) == 1
    }
}

/// Check scalar bounds and consistency with the imported public value.
pub(super) fn check_private(p: &[u8], g: &[u8], q: Option<&[u8]>, y: &[u8], x: &[u8]) -> bool {
    let len = p.len();
    if y.len() > len || x.is_empty() || x.len() > len {
        return false;
    }
    let domain = pack_domain(p, g, q);
    let y = scalar(y, len);
    let mut ws = Scratch::new(16 * len + 32);
    let f = match Backend::select(detected()) {
        Backend::Baseline => vg_ffdh_check_private,
        Backend::Adx => vg_ffdh_check_private_adx,
    };
    // SAFETY: domain was checked at import; its packed length is 2 or 3
    // modulus widths, y is one width, and x has 1..=len bytes. Scratch has
    // 16*len+32 words and is disjoint from all inputs.
    unsafe {
        f(
            domain.as_ptr(),
            domain.len(),
            len,
            y.as_ptr(),
            y.len(),
            x.as_ptr(),
            x.len(),
            ws.as_mut_ptr(),
            ws.len(),
        ) == 1
    }
}

/// One verified private-key attempt from a modulus-width random string.
pub(super) fn generate_key(
    p: &[u8],
    g: &[u8],
    q: Option<&[u8]>,
    rand: &[u8],
    x: &mut [u8],
    y: &mut [u8],
) -> u32 {
    let len = p.len();
    assert!(rand.len() == len && x.len() == len && y.len() == len);
    let domain = pack_domain(p, g, q);
    let mut ws = Scratch::new(16 * len + 32);
    let f = match Backend::select(detected()) {
        Backend::Baseline => vg_ffdh_generate_key,
        Backend::Adx => vg_ffdh_generate_key_adx,
    };
    // SAFETY: the checked domain has 2 or 3 modulus widths. Both outputs
    // and randomness have one width, and scratch has 16*len+32 words.
    // The output and scratch allocations are disjoint from all inputs.
    unsafe {
        f(
            x.as_mut_ptr(),
            x.len(),
            y.as_mut_ptr(),
            y.len(),
            domain.as_ptr(),
            domain.len(),
            len,
            rand.as_ptr(),
            rand.len(),
            ws.as_mut_ptr(),
            ws.len(),
        )
    }
}

/// Persistent native policy and private saved-register workspace.
/// `Scratch` wipes all sixteen words when the controller is dropped.
pub(super) struct GenerationState(Scratch);

impl GenerationState {
    pub(super) fn parameters(bits: usize, generator: u32) -> Result<Self, super::Error> {
        let mut state = Self(Scratch::new(16));
        // SAFETY: the independent allocation has sixteen initialized,
        // writable u64s and lies outside the native callable's stack.
        let status = unsafe {
            vg_ffdh_parameter_generation_init(state.0.as_mut_ptr().cast(), bits, generator)
        };
        if status == 1 {
            Ok(state)
        } else {
            Err(super::Error::InvalidParameters)
        }
    }

    pub(super) fn width(&self) -> usize {
        self.0[1] as usize
    }

    pub(super) fn requested(&self) -> usize {
        self.0[3] as usize
    }

    #[cfg(test)]
    pub(super) fn limit_attempts(&mut self, limit: usize) {
        self.0[0] = self.0[0].min(limit as u64);
    }
}

/// Run the complete parameter search until success, exhaustion or an
/// entropy request. All candidate and witness retry decisions are native.
pub(super) fn generate_parameters(
    bits: usize,
    generator: u32,
    rand: &[u8],
    p: &mut [u8],
    scratch: &mut Scratch,
    state: &mut GenerationState,
) -> (u32, usize, usize) {
    let mut used = [0u64; 1];
    let f = match Backend::select(detected()) {
        Backend::Baseline => vg_ffdh_generate_parameters,
        Backend::Adx => vg_ffdh_generate_parameters_adx,
    };
    // SAFETY: native initialization validates bits and generator and sets
    // the width and entropy cap. The caller allocates that output width
    // and 16*len+32 scratch words, and preserves the native controller's
    // policy between refills. Output, used, tape, scratch and state are
    // separate allocations, disjoint from the callee's stack. The host
    // services the exact native requests, so the tape stays within its cap.
    // Backend selection checks the generated BMI2+ADX feature set.
    let status = unsafe {
        f(
            p.as_mut_ptr(),
            p.len(),
            &mut used,
            bits,
            generator,
            rand.as_ptr(),
            rand.len(),
            scratch.as_mut_ptr(),
            scratch.len(),
            state.0.as_mut_ptr().cast(),
        )
    };
    (status, used[0] as usize, state.requested())
}
