//! ECDH known-answer tests from the vendored RFC 7027, Appendix A: for each
//! brainpool curve, the private keys `dA` and `dB` of two parties, their
//! public keys, and the x-coordinate of their shared secret.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]

mod brainpoolp256r1;
mod brainpoolp256r1_ecdsa;
mod brainpoolp384r1;
mod brainpoolp384r1_ecdsa;
mod brainpoolp512r1;
mod brainpoolp512r1_ecdsa;

const TEXT: &str = include_str!("../../vectors/rfc7027/rfc7027.txt");

/// The hex value labelled `label` (as `dA =`) in the test vectors of the
/// curve `curve`, on the label's line and the lines after it that are only
/// hex digits, in `N` bytes.
fn value<const N: usize>(curve: &str, label: &str) -> [u8; N] {
    let lines: Vec<&str> = TEXT.lines().map(str::trim).collect();
    let mut i = lines
        .iter()
        .position(|l| *l == format!("Curve {curve}"))
        .unwrap();
    while !lines[i].starts_with(label) {
        i += 1;
    }
    let mut hex = lines[i][label.len()..].trim().to_string();
    i += 1;
    while !lines[i].is_empty() && lines[i].bytes().all(|b| b.is_ascii_hexdigit()) {
        hex.push_str(lines[i]);
        i += 1;
    }
    assert_eq!(hex.len(), 2 * N, "{curve} {label}");
    core::array::from_fn(|j| u8::from_str_radix(&hex[2 * j..2 * j + 2], 16).unwrap())
}
