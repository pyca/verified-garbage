//! Byte strings the tests make: patterns, XORs and hex decoding, each
//! compiled once.
//!
//! Every test file had its own, mostly as iterator chains over a closure
//! (`(0..n).map(|i| …).collect()`), which the test binary compiles again at
//! every call site, the closure being a type of its own: these were 7% of
//! the work of compiling it.

/// The `len` bytes `mul · i + add` (mod 256), for `i` from 0.
pub fn pattern(len: usize, mul: usize, add: usize) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(len);
    for i in 0..len {
        bytes.push((mul * i + add) as u8);
    }
    bytes
}

/// [`pattern`], of `N` bytes, as an array.
pub fn pattern_array<const N: usize>(mul: usize, add: usize) -> [u8; N] {
    pattern(N, mul, add).try_into().unwrap()
}

/// `a ⊕ b`, as long as the shorter of the two.
pub fn xor(a: &[u8], b: &[u8]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(a.len().min(b.len()));
    for (x, y) in a.iter().zip(b) {
        bytes.push(x ^ y);
    }
    bytes
}

/// The bytes written in hex in `s`, two digits each.
pub fn unhex(s: &str) -> Vec<u8> {
    assert!(s.len().is_multiple_of(2), "odd length: {s}");
    let mut bytes = Vec::with_capacity(s.len() / 2);
    for i in (0..s.len()).step_by(2) {
        bytes.push(u8::from_str_radix(&s[i..i + 2], 16).unwrap());
    }
    bytes
}

/// [`unhex`] of `text` without its whitespace.
pub fn unhex_spaced(text: &str) -> Vec<u8> {
    let hex: String = text.chars().filter(|c| !c.is_whitespace()).collect();
    unhex(&hex)
}

/// Whether every byte of `bytes` is `value` (guard bytes a call must not
/// have written).
pub fn all_equal(bytes: &[u8], value: u8) -> bool {
    bytes.iter().all(|&b| b == value)
}

/// `x` without its leading zero bytes: a number in DER's form, which has a
/// zero byte before a top bit that is set. For the RSA and DSA tests.
#[cfg(all(
    any(
        target_arch = "x86_64",
        target_arch = "x86",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64"
    ),
    feature = "alloc"
))]
pub fn trim_zeros(x: &[u8]) -> &[u8] {
    &x[x.iter().take_while(|&&b| b == 0).count()..]
}
