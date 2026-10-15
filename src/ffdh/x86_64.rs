//! Verified public-key validation on x86-64. Rust pads the inputs and
//! allocates the working space; the range and subgroup checks run in the
//! code proven against `VG.Spec.Ffdh.checkPublicContract`.

#![cfg(target_arch = "x86_64")]

use super::arithmetic::{Backend, scalar};
use crate::arch::ffdh::{
    vg_ffdh_check_public, vg_ffdh_check_public_adx, vg_ffdh_exchange, vg_ffdh_exchange_adx,
};
use crate::cpu::detected;
use crate::rsa::Scratch;

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

/// Lay out the checked domain at the modulus width for the verified ABI.
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
