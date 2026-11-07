//! FFDH's public arithmetic.
use alloc::{vec, vec::Vec};

/// The public value `a` without its leading zero bytes: its time depends on
/// how many there are, so it is never given a secret (a private key is kept
/// at its encoding's width instead, `PrivateKey::assemble`).
pub(super) fn canonical(a: &[u8]) -> &[u8] {
    &a[a.iter().position(|&b| b != 0).unwrap_or(a.len())..]
}
pub(super) fn bits(a: &[u8]) -> usize {
    let a = canonical(a);
    a.first()
        .map_or(0, |b| 8 * a.len() - b.leading_zeros() as usize)
}
/// The public value `a` in `len` bytes, by `canonical`.
pub(super) fn scalar(a: &[u8], len: usize) -> Vec<u8> {
    let a = canonical(a);
    let mut out = vec![0; len];
    out[len - a.len()..].copy_from_slice(a);
    out
}
