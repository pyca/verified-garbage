//! The HMAC-SHA-224, HMAC-SHA-256, HMAC-SHA-384 and HMAC-SHA-512 test cases
//! of RFC 4231 (Section 4), whose test cases 6 and 7 have a key of 131
//! bytes, longer than a block of each of the hash functions, which Wycheproof's
//! vectors never are for SHA-384 and SHA-512.
//!
//! The RFC is vendored under `vectors/rfc4231/` (see `vectors/sources/`
//! for where it comes from) and compiled into the test binary, so these tests
//! always run. Test case 5's truncated MAC is compared with the start of the
//! computed one.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::hashes::sha224::Sha224;
use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::hashes::sha384::Sha384;
use verified_garbage::hashes::sha512::Sha512;
use verified_garbage::hmac::{Hmac, HmacHash};

const RFC: &str = include_str!("../../vectors/rfc4231/rfc4231.txt");

fn unhex(s: &str) -> Vec<u8> {
    assert_eq!(s.len() % 2, 0, "{s}");
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

/// A test case: its fields (`Key`, `Data`, `HMAC-SHA-224`, …), each the hex
/// it lists, and the length the RFC states for the key, if it does.
struct Case {
    fields: Vec<(String, String)>,
    key_len: Option<usize>,
}

impl Case {
    fn get(&self, name: &str) -> Vec<u8> {
        let (_, v) = self.fields.iter().find(|(f, _)| f == name).unwrap();
        unhex(v)
    }
}

/// The test cases of Section 4: from each `4.N.  Test Case K` heading to the
/// next heading. A field starts on a line indented by three spaces with its
/// name (`Key =`, `HMAC-SHA-256 =`, …); a line indented further continues
/// its value. The value is the first word of each line; what follows it is
/// a comment (the length, or the text the bytes spell). The prose, the page
/// footers and headers are skipped.
fn cases() -> Vec<Case> {
    let mut out: Vec<Case> = Vec::new();
    let mut in_case = false;
    for l in RFC.lines() {
        if !l.starts_with(' ') {
            if l.starts_with("4.") && l.contains("Test Case") {
                let n = l.rsplit(' ').next().unwrap();
                assert_eq!(n, (out.len() + 1).to_string());
                out.push(Case {
                    fields: Vec::new(),
                    key_len: None,
                });
                in_case = true;
            } else if l.starts_with("5.") {
                in_case = false;
            }
            continue;
        }
        if !in_case {
            continue;
        }
        let case = out.last_mut().unwrap();
        let indent = l.len() - l.trim_start().len();
        let words: Vec<&str> = l.split_whitespace().collect();
        if indent == 3 {
            let name = words[0];
            if name != "Key" && name != "Data" && !name.starts_with("HMAC-SHA-") {
                continue;
            }
            let rest = if words.get(1) == Some(&"=") {
                &words[2..]
            } else {
                &words[1..]
            };
            case.fields.push((name.to_string(), rest[0].to_string()));
            if name == "Key" {
                case.key_len = key_len(&rest[1..]);
            }
        } else {
            assert!(indent > 3, "{l}");
            let (name, v) = case.fields.last_mut().unwrap();
            v.push_str(words[0]);
            if name == "Key" {
                case.key_len = key_len(&words[1..]).or(case.key_len);
            }
        }
    }
    assert_eq!(out.len(), 7);
    out
}

/// The length in a comment `(<n> bytes)`.
fn key_len(comment: &[&str]) -> Option<usize> {
    match comment {
        [n, "bytes)"] => Some(n.strip_prefix('(').unwrap().parse().unwrap()),
        _ => None,
    }
}

/// Checks the cases for `H`, at once and one byte at a time, and that test
/// cases 6 and 7 have a key longer than a block.
fn check<H: HmacHash>(name: &str) {
    let cases = cases();
    for (i, c) in cases.iter().enumerate() {
        let (key, data, mac) = (c.get("Key"), c.get("Data"), c.get(name));
        if let Some(n) = c.key_len {
            assert_eq!(key.len(), n);
        }
        let full = Hmac::<H>::mac(&key, &data);
        assert_eq!(full.as_ref().len(), H::OUTPUT_SIZE);
        if i == 4 {
            assert_eq!(mac.len(), 16);
            assert_eq!(&full.as_ref()[..16], &mac[..]);
        } else {
            assert_eq!(full.as_ref(), &mac[..]);
        }
        let mut h = Hmac::<H>::new(&key);
        for byte in &data {
            h.update(core::slice::from_ref(byte));
        }
        assert_eq!(h.finalize().as_ref(), full.as_ref());
    }
    for c in &cases[5..] {
        assert!(c.get("Key").len() > H::BLOCK_SIZE);
    }
}

#[test]
fn hmac_sha224() {
    check::<Sha224>("HMAC-SHA-224");
}

#[test]
fn hmac_sha256() {
    check::<Sha256>("HMAC-SHA-256");
}

#[test]
fn hmac_sha384() {
    check::<Sha384>("HMAC-SHA-384");
}

#[test]
fn hmac_sha512() {
    check::<Sha512>("HMAC-SHA-512");
}
