//! Published SM4 vectors: Appendix A of draft-ribose-cfrg-sm4-10, unmodified
//! under vectors/ (its round keys and intermediate values are checked in
//! `lean/VerifiedGarbageTest/Sm4.lean`). Its single blocks and its repeated
//! encryptions (A.1) and its ECB examples (A.2.1) test ECB directly; its
//! CBC, OFB, CFB and CTR examples (A.2.2–A.2.5) are computed here from ECB.

#![cfg(target_arch = "x86_64")]

use verified_garbage::sm4_ecb::{Error, Sm4Ecb};

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

struct Example {
    key: [u8; 16],
    plaintext: Vec<u8>,
    ciphertext: Vec<u8>,
}

fn example(text: &str) -> Example {
    Example {
        key: field(text, "Encryption key:").try_into().unwrap(),
        plaintext: field(text, "Plaintext:"),
        ciphertext: field(text, "Ciphertext:"),
    }
}

fn encrypt_block(ctx: &Sm4Ecb, block: &[u8]) -> Vec<u8> {
    let mut out = block.to_vec();
    ctx.encrypt(&mut out).unwrap();
    out
}

fn xor(a: &[u8], b: &[u8]) -> Vec<u8> {
    a.iter().zip(b).map(|(x, y)| x ^ y).collect()
}

/// ECB in both directions, whole and split at every block boundary.
fn check_ecb(key: &[u8; 16], plaintext: &[u8], ciphertext: &[u8]) {
    assert_eq!(plaintext.len(), ciphertext.len());
    let ctx = Sm4Ecb::new(key);
    for (operation, input, expected) in [
        (
            Sm4Ecb::encrypt as fn(&Sm4Ecb, &mut [u8]) -> Result<(), Error>,
            plaintext,
            ciphertext,
        ),
        (
            Sm4Ecb::decrypt as fn(&Sm4Ecb, &mut [u8]) -> Result<(), Error>,
            ciphertext,
            plaintext,
        ),
    ] {
        let mut output = input.to_vec();
        operation(&ctx, &mut output).unwrap();
        assert_eq!(output, expected);
        for offset in (0..=input.len()).step_by(16) {
            let mut output = input.to_vec();
            operation(&ctx, &mut []).unwrap();
            operation(&ctx, &mut output[..offset]).unwrap();
            operation(&ctx, &mut output[offset..]).unwrap();
            assert_eq!(output, expected);
        }
    }
}

#[test]
fn single_blocks() {
    for (from, to) in [
        ("A.1.1.  Example 1 (", "A.1.2.  Example 2 ("),
        ("A.1.4.  Example 4", "A.1.5.  Example 5"),
    ] {
        let e = example(section(from, to));
        check_ecb(&e.key, &e.plaintext, &e.ciphertext);
    }
    // Examples 2 and 5 decrypt examples 1 and 4: their "plaintext" is the
    // ciphertext and their "ciphertext" the plaintext.
    for (from, to) in [
        ("A.1.2.  Example 2 (", "A.1.3.  Example 3 ("),
        ("A.1.5.  Example 5", "A.1.6.  Example 6"),
    ] {
        let text = section(from, to);
        let key: [u8; 16] = field(text, "Encryption key:").try_into().unwrap();
        check_ecb(
            &key,
            &field(text, "Plaintext:"),
            &field(text, "Ciphertext:"),
        );
    }
}

/// A.1.3 and A.1.6: a block encrypted 1,000,000 times, sixteen copies at a
/// time, and the whole buffer decrypted back.
#[test]
fn repeated() {
    for (from, to) in [
        ("A.1.3.  Example 3 (", "A.1.4.  Example 4"),
        ("A.1.6.  Example 6", "A.2.  Examples For Various Modes"),
    ] {
        let e = example(section(from, to));
        let ctx = Sm4Ecb::new(&e.key);
        let mut buffer = e.plaintext.repeat(16);
        for _ in 0..1_000_000 {
            ctx.encrypt(&mut buffer).unwrap();
        }
        assert_eq!(buffer, e.ciphertext.repeat(16));
        for _ in 0..1_000_000 {
            ctx.decrypt(&mut buffer).unwrap();
        }
        assert_eq!(buffer, e.plaintext.repeat(16));
    }
}

#[test]
fn ecb() {
    for (from, to) in [
        ("A.2.1.1.  Example 1", "A.2.1.2.  Example 2"),
        ("A.2.1.2.  Example 2", "A.2.2.  SM4-CBC Examples"),
    ] {
        let e = example(section(from, to));
        check_ecb(&e.key, &e.plaintext, &e.ciphertext);
        // The same blocks many times over: more than one group of sixteen,
        // and a partial group.
        check_ecb(&e.key, &e.plaintext.repeat(21), &e.ciphertext.repeat(21));
    }
}

#[test]
fn cbc() {
    for (from, to) in [
        ("A.2.2.1.  Example 1", "A.2.2.2.  Example 2"),
        ("A.2.2.2.  Example 2", "A.2.3.  SM4-OFB Examples"),
    ] {
        let text = section(from, to);
        let e = example(text);
        let ctx = Sm4Ecb::new(&e.key);
        let mut chain = field(text, "IV:");
        let mut ciphertext: Vec<u8> = Vec::new();
        for block in e.plaintext.chunks(16) {
            chain = encrypt_block(&ctx, &xor(block, &chain));
            ciphertext.extend(&chain);
        }
        assert_eq!(ciphertext, e.ciphertext);
        // Decryption of all the blocks at once.
        let mut decrypted = e.ciphertext.clone();
        ctx.decrypt(&mut decrypted).unwrap();
        let previous = [
            field(text, "IV:"),
            e.ciphertext[..e.ciphertext.len() - 16].to_vec(),
        ]
        .concat();
        assert_eq!(xor(&decrypted, &previous), e.plaintext);
    }
}

#[test]
fn ofb() {
    for (from, to) in [
        ("A.2.3.1.  Example 1", "A.2.3.2.  Example 2"),
        ("A.2.3.2.  Example 2", "A.2.4.  SM4-CFB Examples"),
    ] {
        let text = section(from, to);
        let e = example(text);
        let ctx = Sm4Ecb::new(&e.key);
        let mut state = field(text, "IV:");
        let mut keystream: Vec<u8> = Vec::new();
        for _ in e.plaintext.chunks(16) {
            state = encrypt_block(&ctx, &state);
            keystream.extend(&state);
        }
        assert_eq!(xor(&e.plaintext, &keystream), e.ciphertext);
    }
}

#[test]
fn cfb() {
    for (from, to) in [
        ("A.2.4.1.  Example 1", "A.2.4.2.  Example 2"),
        ("A.2.4.2.  Example 2", "A.2.5.  SM4-CTR Examples"),
    ] {
        let text = section(from, to);
        let e = example(text);
        let ctx = Sm4Ecb::new(&e.key);
        let mut chain = field(text, "IV:");
        let mut ciphertext: Vec<u8> = Vec::new();
        for block in e.plaintext.chunks(16) {
            chain = xor(block, &encrypt_block(&ctx, &chain));
            ciphertext.extend(&chain);
        }
        assert_eq!(ciphertext, e.ciphertext);
    }
}

#[test]
fn ctr() {
    for (from, to) in [
        ("A.2.5.1.  Example 1", "A.2.5.2.  Example 2"),
        ("A.2.5.2.  Example 2", "Appendix B.  Sample Implementation"),
    ] {
        let text = section(from, to);
        let e = example(text);
        let ctx = Sm4Ecb::new(&e.key);
        let iv = u128::from_be_bytes(field(text, "IV:").try_into().unwrap());
        // All the counter blocks at once.
        let mut keystream: Vec<u8> = (0..e.plaintext.len() as u128 / 16)
            .flat_map(|i| iv.wrapping_add(i).to_be_bytes())
            .collect();
        ctx.encrypt(&mut keystream).unwrap();
        assert_eq!(xor(&e.plaintext, &keystream), e.ciphertext);
    }
}

#[test]
fn incomplete_block() {
    let ctx = Sm4Ecb::new(&[0; 16]);
    for len in [1, 15, 17, 31] {
        let mut buffer = vec![0x5a; len];
        assert_eq!(ctx.encrypt(&mut buffer), Err(Error::IncompleteBlock));
        assert_eq!(ctx.decrypt(&mut buffer), Err(Error::IncompleteBlock));
        assert_eq!(buffer, vec![0x5a; len]);
    }
}
