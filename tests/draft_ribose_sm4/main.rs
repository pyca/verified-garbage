//! SM4's example vectors: Appendix A of the Internet-Draft
//! draft-ribose-cfrg-sm4-10 (a draft, not an RFC; SM4 is GB/T 32907-2016,
//! and is not in NIST's CAVP), vendored unmodified under
//! `vectors/draft-ribose-cfrg-sm4/` (see
//! `vectors/sources/draft-ribose-cfrg-sm4.toml`) and read at run time
//! (`tests/vectors.rs`), so these tests always run.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

mod sm4_cbc;
mod sm4_cfb;
mod sm4_ctr;
mod sm4_ecb;
mod sm4_ofb;

use crate::bytes::unhex;

/// The text of the appendix between the headings starting `from` and `to`.
fn section(from: &str, to: &str) -> String {
    let draft = crate::vectors::text("vectors/draft-ribose-cfrg-sm4/draft-ribose-cfrg-sm4-10.txt");
    let appendix = draft
        .split("Appendix A.  Appendix A: Example Calculations")
        .last()
        .unwrap();
    let start = appendix.find(from).unwrap();
    let end = start + appendix[start..].find(to).unwrap();
    appendix[start..end].to_owned()
}

/// The bytes after the label `label` (e.g. `"Plaintext:"`), from the lines
/// of two-digit hex numbers that follow it, skipping the page breaks, up to
/// the next label.
fn field(text: &str, label: &str) -> Vec<u8> {
    let mut lines = text.lines().map(str::trim);
    lines
        .by_ref()
        .find(|line| line.eq_ignore_ascii_case(label))
        .unwrap();
    let mut out = Vec::new();
    for line in lines {
        if line.ends_with(':') {
            break;
        }
        if !line.is_empty() && line.split(' ').all(|byte| byte.len() == 2) {
            out.extend(unhex(&line.replace(' ', "")));
        }
    }
    assert!(!out.is_empty());
    out
}
