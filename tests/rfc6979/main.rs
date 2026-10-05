//! Deterministic ECDSA known-answer tests from the vendored RFC 6979:
//! §A.2.5 (P-256), §A.2.6 (P-384) and §A.2.7 (P-521), each the private
//! key, its public key, and its signatures of "sample" and "test" with the
//! hash functions the curve signs with here.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

mod p256;
mod p384;
mod p521;

const TEXT: &str = include_str!("../../vectors/rfc6979/rfc6979.txt");

fn unhex(s: &str) -> Vec<u8> {
    assert_eq!(s.len() % 2, 0, "{s}");
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

/// The hex value of the first line from `lines[*i..]` that begins with
/// `label`, continued on the lines after it that are only hex digits, in
/// `N` bytes (P-521's values have an odd number of digits); `*i` moves past
/// it.
fn value<const N: usize>(lines: &[&str], i: &mut usize, label: &str) -> [u8; N] {
    while !lines[*i].starts_with(label) {
        *i += 1;
    }
    let mut hex = lines[*i][label.len()..].to_string();
    *i += 1;
    while !lines[*i].is_empty() && lines[*i].bytes().all(|b| b.is_ascii_hexdigit()) {
        hex.push_str(lines[*i]);
        *i += 1;
    }
    unhex(&format!("{hex:0>width$}", width = 2 * N))
        .try_into()
        .unwrap()
}

/// Each hash function, message and the `r ‖ s` of its signature.
type Signatures<const S: usize> = Vec<(&'static str, String, [u8; S])>;

/// From the section `title`: `q`, `x`, `U = 04 ‖ Ux ‖ Uy`, and the
/// signatures with the hash functions `hashes`.
fn section<const Q: usize, const U: usize, const S: usize>(
    title: &str,
    hashes: &[&'static str],
) -> ([u8; Q], [u8; Q], [u8; U], Signatures<S>) {
    let text = TEXT.split_once(title).unwrap().1;
    let text = text.split_once("\nA.").unwrap().0;
    let lines: Vec<&str> = text.lines().map(str::trim).collect();
    let mut i = 0;
    let q = value(&lines, &mut i, "q = ");
    let x = value(&lines, &mut i, "x = ");
    let mut u = [4; U];
    u[1..=Q].copy_from_slice(&value::<Q>(&lines, &mut i, "Ux = "));
    u[Q + 1..].copy_from_slice(&value::<Q>(&lines, &mut i, "Uy = "));
    let mut signatures = Vec::new();
    while i < lines.len() {
        let line = lines[i];
        i += 1;
        let Some((hash, message)) = hashes.iter().find_map(|hash| {
            line.strip_prefix(&format!("With {hash}, message = \""))
                .map(|m| (*hash, m))
        }) else {
            continue;
        };
        let message = message.strip_suffix("\":").unwrap();
        let mut rs = [0; S];
        rs[..Q].copy_from_slice(&value::<Q>(&lines, &mut i, "r = "));
        rs[Q..].copy_from_slice(&value::<Q>(&lines, &mut i, "s = "));
        signatures.push((hash, message.to_string(), rs));
    }
    assert_eq!(signatures.len(), 2 * hashes.len());
    (q, x, u, signatures)
}

/// The integer `x + delta` (mod 2^(8N)) of the `N` bytes `x`.
fn add<const N: usize>(x: &[u8; N], delta: i16) -> [u8; N] {
    let mut out = *x;
    let mut carry = delta;
    for b in out.iter_mut().rev() {
        let v = i16::from(*b) + carry;
        *b = v.rem_euclid(256) as u8;
        carry = v.div_euclid(256);
    }
    out
}
