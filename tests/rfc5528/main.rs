//! The Camellia-CTR test vectors of RFC 5528 §4.1, read from the
//! byte-for-byte vendored RFC, and the increment of the counter block across
//! its words and past `2¹²⁸`, against Camellia-ECB on the counter blocks.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use verified_garbage::camellia_ctr::{CamelliaCtr, InvalidKeyLength};
use verified_garbage::camellia_ecb::CamelliaEcb;

const TEXT: &str = include_str!("../../vectors/rfc5528/rfc5528.txt");

fn unhex(text: &str) -> Vec<u8> {
    let hex: String = text.chars().filter(|c| !c.is_whitespace()).collect();
    assert_eq!(hex.len() % 2, 0);
    (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).unwrap())
        .collect()
}

/// The counter block `n` blocks after `ctr`, modulo `2¹²⁸`.
fn add(ctr: &[u8; 16], n: usize) -> [u8; 16] {
    u128::from_be_bytes(*ctr)
        .wrapping_add(n as u128)
        .to_be_bytes()
}

/// The fields of one test vector: `label: hex`, with continuation lines `: hex`,
/// labels in lower case with single spaces (the RFC writes `Key Stream    (1)`).
/// Lines whose value is not hex (the
/// title, `Plaintext String`) are not fields.
fn fields(vector: &str) -> Vec<(String, Vec<u8>)> {
    let mut out: Vec<(String, String)> = Vec::new();
    for line in vector.lines() {
        let Some((label, value)) = line.split_once(':') else {
            continue;
        };
        let label = label
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
            .to_lowercase();
        if label.is_empty() {
            out.last_mut().unwrap().1.push_str(value);
        } else if value
            .chars()
            .all(|c| c.is_ascii_hexdigit() || c.is_whitespace())
        {
            out.push((label, value.to_string()));
        }
    }
    out.into_iter().map(|(k, v)| (k, unhex(&v))).collect()
}

fn get<'a>(fields: &'a [(String, Vec<u8>)], label: &str) -> &'a [u8] {
    &fields.iter().find(|(k, _)| k == label).unwrap().1
}

/// Checks a message in one call, split at every block boundary, one call per
/// block, and cut short at each length, with the counter block left after
/// each.
fn check(ctx: &CamelliaCtr, ctr: &[u8; 16], input: &[u8], expected: &[u8]) {
    let blocks = input.len().div_ceil(16);
    let mut output = input.to_vec();
    let mut chain = *ctr;
    ctx.apply_keystream(&mut chain, &mut output);
    assert_eq!(output, expected);
    assert_eq!(chain, add(ctr, blocks));
    for offset in (0..=input.len()).step_by(16) {
        let mut output = input.to_vec();
        let mut chain = *ctr;
        ctx.apply_keystream(&mut chain, &mut []);
        assert_eq!(chain, *ctr);
        ctx.apply_keystream(&mut chain, &mut output[..offset]);
        assert_eq!(chain, add(ctr, offset / 16));
        ctx.apply_keystream(&mut chain, &mut output[offset..]);
        assert_eq!(output, expected);
        assert_eq!(chain, add(ctr, blocks));
    }
    let mut output = input.to_vec();
    let mut chain = *ctr;
    for block in output.chunks_mut(16) {
        ctx.apply_keystream(&mut chain, block);
    }
    assert_eq!(output, expected);
    assert_eq!(chain, add(ctr, blocks));
    for len in 0..input.len() {
        let mut output = input[..len].to_vec();
        let mut chain = *ctr;
        ctx.apply_keystream(&mut chain, &mut output);
        assert_eq!(output, expected[..len]);
        assert_eq!(chain, add(ctr, len.div_ceil(16)));
    }
}

#[test]
fn rfc5528_test_vectors() {
    // The section itself, not its line in the table of contents.
    let section = TEXT.rsplit_once("4.1.  Camellia-CTR").unwrap().1;
    let section = section.split_once("4.2.  Camellia-CCM").unwrap().0;
    let mut key_lens = Vec::new();
    for vector in section.split("TV #").skip(1) {
        let fields = fields(vector);
        let key = get(&fields, "camellia key");
        let ctr: [u8; 16] = get(&fields, "counter block (1)").try_into().unwrap();
        let plaintext = get(&fields, "plaintext");
        let ciphertext = get(&fields, "ciphertext");
        key_lens.push(key.len());
        let ctx = CamelliaCtr::new(key).unwrap();
        check(&ctx, &ctr, plaintext, ciphertext);
        check(&ctx, &ctr, ciphertext, plaintext);
        // The key stream is CTR of zeros, block by block from its counter block.
        let blocks = plaintext.len().div_ceil(16);
        let mut stream = vec![0; 16 * blocks];
        let mut chain = ctr;
        ctx.apply_keystream(&mut chain, &mut stream);
        for (j, block) in stream.chunks(16).enumerate() {
            assert_eq!(
                get(&fields, &format!("counter block ({})", j + 1)),
                add(&ctr, j)
            );
            assert_eq!(get(&fields, &format!("key stream ({})", j + 1)), block);
        }
    }
    assert_eq!(key_lens, [16, 16, 16, 24, 24, 24, 32, 32, 32]);
}

/// The counter block's increment carries across its 32- and 64-bit words and
/// wraps from `1¹²⁸` to `0¹²⁸`: the output blocks are Camellia (by
/// Camellia-ECB) of the counter blocks counted with `u128`. The messages are
/// longer than a group of eight blocks, so that a group follows another.
#[test]
fn counter_carries_and_wraps() {
    let starts: [u128; 6] = [
        u128::MAX - 2,
        u128::MAX,
        (1 << 32) - 2,
        (1 << 64) - 3,
        (1 << 96) - 1,
        0x0123_4567_89ab_cdef_ffff_ffff_ffff_fffe,
    ];
    for key_len in [16, 24, 32] {
        let key: Vec<_> = (0..key_len).map(|i| (29 * i + 7) as u8).collect();
        let ctx = CamelliaCtr::new(&key).unwrap();
        let ecb = CamelliaEcb::new(&key).unwrap();
        for start in starts {
            let ctr = start.to_be_bytes();
            let message: Vec<_> = (0..16 * 17 + 7).map(|i| (11 * i + 5) as u8).collect();
            let blocks = message.len().div_ceil(16);
            let mut stream: Vec<u8> = (0..blocks)
                .flat_map(|j| start.wrapping_add(j as u128).to_be_bytes())
                .collect();
            ecb.encrypt(&mut stream).unwrap();
            let expected: Vec<_> = message.iter().zip(&stream).map(|(m, s)| m ^ s).collect();
            check(&ctx, &ctr, &message, &expected);
        }
    }
}

#[test]
fn limits_and_lengths() {
    for len in 0..=40 {
        let key: Vec<_> = (0..len).map(|i| (17 * i + 3) as u8).collect();
        if !matches!(len, 16 | 24 | 32) {
            assert!(matches!(CamelliaCtr::new(&key), Err(InvalidKeyLength)));
            continue;
        }
        let ctx = CamelliaCtr::new(&key).unwrap();
        let mut ctr = [0x3c; 16];
        ctx.apply_keystream(&mut ctr, &mut []);
        assert_eq!(ctr, [0x3c; 16]);
    }
}
