//! SM3's published vectors (SM3 is GB/T 32905-2016, and is not in NIST's
//! CAVP or Wycheproof), vendored unmodified under `vectors/` (see
//! `vectors/sources/`) and compiled into the test binary, so these tests
//! always run:
//!
//! * `draft_sca_cfrg_sm3`: the hash values of the Internet-Draft
//!   draft-sca-cfrg-sm3-02 (a draft, not an RFC): Appendix A's two examples
//!   from GB/T 32905-2016, and Appendix B's eighteen from GB/T 32918 (SM2);
//! * `cryptography`: pyca/cryptography's `oscca.txt`, which adds the empty
//!   and a one-byte message.
//!
//! Each vector is checked in one call and split into pieces at every
//! position.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

mod cryptography;
mod draft_sca_cfrg_sm3;

use verified_garbage::hashes::HashFunction;
use verified_garbage::hashes::sm3::Sm3;

fn unhex(s: &str) -> Vec<u8> {
    assert_eq!(s.len() % 2, 0);
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

/// Checks the hash value of `msg`, in one call and absorbed in two pieces
/// split at every position.
fn check(msg: &[u8], md: &[u8]) {
    assert_eq!(Sm3::digest(msg)[..], md[..]);
    assert_eq!(<Sm3 as HashFunction>::digest(msg)[..], md[..]);
    for i in 0..=msg.len() {
        let mut h = Sm3::new();
        h.update(&msg[..i]);
        h.update(&msg[i..]);
        assert_eq!(h.finalize()[..], md[..]);
    }
}
