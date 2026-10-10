//! SM4-CTR: the CTR examples of draft-ribose-cfrg-sm4-10 (A.2.5), unmodified
//! under vectors/, whole, in pieces and truncated; and CTR from ECB
//! (`Sm4Ecb`, tested on the draft's ECB examples) on every length up to
//! a few groups of sixteen blocks and across the carries of the counter.

#![cfg(target_arch = "x86_64")]

use verified_garbage::sm4_ctr::Sm4Ctr;
use verified_garbage::sm4_ecb::Sm4Ecb;

use super::unhex;

const DRAFT: &str =
    include_str!("../../vectors/draft-ribose-cfrg-sm4/draft-ribose-cfrg-sm4-10.txt");

/// The text of the appendix between the headings starting `from` and `to`.
fn section(from: &str, to: &str) -> &'static str {
    let appendix = DRAFT
        .split("Appendix A.  Appendix A: Example Calculations")
        .last()
        .unwrap();
    let start = appendix.find(from).unwrap();
    let end = start + appendix[start..].find(to).unwrap();
    &appendix[start..end]
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

/// `ctr` plus `k`, modulo `2¹²⁸`.
fn add(ctr: [u8; 16], k: usize) -> [u8; 16] {
    u128::from_be_bytes(ctr).wrapping_add(k as u128).to_be_bytes()
}

/// CTR from ECB: `data` XORed with the encryptions of `ctr`, `ctr + 1`, ….
fn reference(key: &[u8; 16], ctr: [u8; 16], data: &[u8]) -> Vec<u8> {
    let blocks = data.len().div_ceil(16);
    let mut keystream: Vec<u8> = (0..blocks).flat_map(|i| add(ctr, i)).collect();
    Sm4Ecb::new(key).encrypt(&mut keystream).unwrap();
    data.iter().zip(&keystream).map(|(x, y)| x ^ y).collect()
}

/// `apply_keystream` on `data` from `ctr`, whole and split at every block
/// boundary, gives `expected` and leaves `ctr` plus the number of blocks.
fn check(ctx: &Sm4Ctr, ctr: [u8; 16], data: &[u8], expected: &[u8]) {
    let after = add(ctr, data.len().div_ceil(16));
    let mut c = ctr;
    let mut output = data.to_vec();
    ctx.apply_keystream(&mut c, &mut output);
    assert_eq!(output, expected);
    assert_eq!(c, after);
    for offset in (0..=data.len()).step_by(16) {
        let mut c = ctr;
        let mut output = data.to_vec();
        ctx.apply_keystream(&mut c, &mut []);
        assert_eq!(c, ctr);
        ctx.apply_keystream(&mut c, &mut output[..offset]);
        assert_eq!(c, add(ctr, offset / 16));
        ctx.apply_keystream(&mut c, &mut output[offset..]);
        assert_eq!(output, expected);
        assert_eq!(c, after);
    }
}

#[test]
fn draft_examples() {
    for (from, to) in [
        ("A.2.5.1.  Example 1", "A.2.5.2.  Example 2"),
        ("A.2.5.2.  Example 2", "Appendix B.  Sample Implementation"),
    ] {
        let text = section(from, to);
        let key: [u8; 16] = field(text, "Encryption key:").try_into().unwrap();
        let iv: [u8; 16] = field(text, "IV:").try_into().unwrap();
        let plaintext = field(text, "Plaintext:");
        let ciphertext = field(text, "Ciphertext:");
        let ctx = Sm4Ctr::new(&key);
        check(&ctx, iv, &plaintext, &ciphertext);
        check(&ctx, iv, &ciphertext, &plaintext);
        // Every prefix, the last block partial.
        for len in 0..=plaintext.len() {
            let mut c = iv;
            let mut output = plaintext[..len].to_vec();
            ctx.apply_keystream(&mut c, &mut output);
            assert_eq!(output, ciphertext[..len]);
            assert_eq!(c, add(iv, len.div_ceil(16)));
        }
    }
}

/// Every length up to three groups of sixteen blocks and a bit, from
/// counter blocks whose last 64 bits, or all 128, wrap around within them.
#[test]
fn from_ecb() {
    let key: [u8; 16] = core::array::from_fn(|i| (17 * i + 3) as u8);
    let ctx = Sm4Ctr::new(&key);
    let data: Vec<u8> = (0..16 * 50 + 7).map(|i| (i * 31 + 7) as u8).collect();
    let low = u128::from(u64::MAX - 20);
    for ctr in [
        [0; 16],
        core::array::from_fn(|i| (i * 11) as u8),
        low.to_be_bytes(),
        ((5 << 64) | low).to_be_bytes(),
        (u128::MAX - 20).to_be_bytes(),
    ] {
        for len in (0..=data.len()).step_by(5) {
            let input = &data[..len];
            let expected = reference(&key, ctr, input);
            let mut c = ctr;
            let mut output = input.to_vec();
            ctx.apply_keystream(&mut c, &mut output);
            assert_eq!(output, expected);
            assert_eq!(c, add(ctr, len.div_ceil(16)));
        }
        check(&ctx, ctr, &data, &reference(&key, ctr, &data));
    }
}
