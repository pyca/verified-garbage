//! The HKDF-SHA-256 and HKDF-SHA-1 test cases of RFC 5869 (Appendix A),
//! which give the pseudorandom key `PRK` too: HKDF-Extract's (`extract`)
//! and HKDF-Expand's from it (`from_prk`).
//!
//! The RFC is vendored under `vectors/rfc5869/` (see `vectors/sources/`
//! for where it comes from) and read at run time (`tests/vectors.rs`), so these
//! tests always run.

#![cfg(any(
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "riscv64",
    target_arch = "x86_64"
))]

use verified_garbage::hashes::sha1::Sha1;
use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::kdf::hkdf::{Hkdf, HkdfHash};
use verified_garbage_test_vectors::unhex;

/// A test case: its fields (`Hash`, `IKM`, `salt`, …), each the text after
/// its `=`, its continuation lines appended.
struct Case(Vec<(String, String)>);

impl Case {
    fn get(&self, name: &str) -> &str {
        &self.0.iter().find(|(f, _)| f == name).unwrap().1
    }

    /// The bytes of a field: its hex (`0x…`, up to the length in
    /// parentheses), none for `(0 octets)`, and `None` for `not provided`.
    fn bytes(&self, name: &str) -> Option<Vec<u8>> {
        let v = self.get(name);
        if v.starts_with("not provided") {
            return None;
        }
        let hex = v.split('(').next().unwrap();
        let hex: String = hex.split_whitespace().collect();
        Some(unhex(hex.strip_prefix("0x").unwrap_or(&hex)))
    }
}

/// The test cases of Appendix A: from each `A.N.  Test Case N` heading to
/// the next. A field is a line indented by three spaces `Name = value`; a
/// line indented further continues its value.
fn cases() -> Vec<Case> {
    let mut out: Vec<Case> = Vec::new();
    for l in crate::vectors::text("vectors/rfc5869/rfc5869.txt").lines() {
        if l.starts_with("A.") && l.contains("Test Case") {
            let n = l.rsplit(' ').next().unwrap();
            assert_eq!(n, (out.len() + 1).to_string());
            out.push(Case(Vec::new()));
            continue;
        }
        let Some(case) = out.last_mut() else { continue };
        if !l.starts_with(' ') {
            continue;
        }
        let indent = l.len() - l.trim_start().len();
        if indent == 3 {
            if let Some((name, value)) = l.trim().split_once('=') {
                case.0
                    .push((name.trim().to_string(), value.trim().to_string()));
            }
        } else {
            // Any other line (the vectors indent them further) continues the
            // last field's value.
            let (_, v) = case.0.last_mut().expect("a continuation follows a field");
            v.push(' ');
            v.push_str(l.trim());
        }
    }
    out
}

/// One case with HKDF over `H`: `PRK` and the output keying material from
/// HKDF-Extract, and the output keying material from `PRK`.
fn check<H: HkdfHash>(c: &Case) {
    let ikm = c.bytes("IKM").unwrap();
    let salt = c.bytes("salt");
    let info = c.bytes("info").unwrap();
    let len: usize = c.get("L").parse().unwrap();
    let prk = c.bytes("PRK").unwrap();
    let okm = c.bytes("OKM").unwrap();
    assert_eq!(okm.len(), len);
    let (p, hkdf) = Hkdf::<H>::extract(salt.as_deref(), &ikm);
    assert_eq!(p.as_ref(), prk);
    let mut out = vec![0; len];
    hkdf.expand(&info, &mut out).unwrap();
    assert_eq!(out, okm);
    let mut out = vec![0; len];
    Hkdf::<H>::from_prk(&prk)
        .unwrap()
        .expand(&info, &mut out)
        .unwrap();
    assert_eq!(out, okm);
}

#[test]
fn rfc5869() {
    let cases = cases();
    assert_eq!(cases.len(), 7);
    for c in &cases {
        if c.get("Hash") == "SHA-256" {
            check::<Sha256>(c);
        } else {
            assert_eq!(c.get("Hash"), "SHA-1");
            check::<Sha1>(c);
        }
    }
}
