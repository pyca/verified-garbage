//! SM4-OFB: the OFB examples (A.2.3) of the Internet-Draft
//! draft-ribose-cfrg-sm4-10, unmodified under vectors/, whole and in pieces;
//! and OFB from ECB (`Sm4Ecb`, tested on the draft's ECB examples) on every
//! length up to a few blocks, partial last blocks included.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::sm4_ecb::Sm4Ecb;
use verified_garbage::sm4_ofb::Sm4Ofb;

use super::{field, section};

/// OFB from ECB: the output and the last output block used.
fn reference(key: &[u8; 16], iv: [u8; 16], data: &[u8]) -> (Vec<u8>, [u8; 16]) {
    let ecb = Sm4Ecb::new(key);
    let mut o = iv;
    let mut out = Vec::new();
    for block in data.chunks(16) {
        ecb.encrypt(&mut o).unwrap();
        out.extend(crate::bytes::xor(block, &o));
    }
    (out, o)
}

#[test]
fn draft_examples() {
    for (from, to) in [
        ("A.2.3.1.  Example 1", "A.2.3.2.  Example 2"),
        ("A.2.3.2.  Example 2", "A.2.4.  SM4-CFB Examples"),
    ] {
        let text = &section(from, to);
        let key: [u8; 16] = field(text, "Encryption Key:").try_into().unwrap();
        let iv: [u8; 16] = field(text, "IV:").try_into().unwrap();
        let plaintext = field(text, "Plaintext:");
        let ciphertext = field(text, "Ciphertext:");
        let n = plaintext.len();
        let after: [u8; 16] =
            core::array::from_fn(|i| plaintext[n - 16 + i] ^ ciphertext[n - 16 + i]);
        let ctx = Sm4Ofb::new(&key);
        for (input, output) in [(&plaintext, &ciphertext), (&ciphertext, &plaintext)] {
            for offset in (0..=n).step_by(16) {
                let mut chain = iv;
                let mut buffer = input.clone();
                ctx.apply_keystream(&mut chain, &mut buffer[..offset]);
                ctx.apply_keystream(&mut chain, &mut buffer[offset..]);
                assert_eq!(&buffer, output);
                assert_eq!(chain, after);
            }
        }
    }
}

/// Every length up to 20 blocks.
#[test]
fn from_ecb() {
    let key: [u8; 16] = crate::bytes::pattern_array(17, 3);
    let iv: [u8; 16] = crate::bytes::pattern_array(11, 5);
    let ctx = Sm4Ofb::new(&key);
    let data: Vec<u8> = crate::bytes::pattern(16 * 20, 31, 7);
    for len in 0..=data.len() {
        let (output, after) = reference(&key, iv, &data[..len]);
        let mut chain = iv;
        let mut buffer = data[..len].to_vec();
        ctx.apply_keystream(&mut chain, &mut buffer);
        assert_eq!(buffer, output);
        assert_eq!(chain, after);
    }
}

/// Unaligned buffers, partial segments and guards, at lengths around
/// multiples of eight and sixteen blocks.
#[test]
fn unaligned_buffers() {
    let key = crate::bytes::pattern_array(17, 3);
    let iv = crate::bytes::pattern_array(11, 5);
    let ctx = Sm4Ofb::new(&key);
    for blocks in [0, 1, 2, 3, 4, 7, 8, 9, 15, 16, 17, 31, 32, 33, 64, 65, 1024] {
        for tail in [0, 7] {
            let len = 16 * blocks + tail;
            let input: Vec<u8> = crate::bytes::pattern(len, 31, 7);
            let (output, after) = reference(&key, iv, &input);
            for offset in 0..16 {
                let mut buffer = vec![0xa5; len + 32];
                buffer[offset..offset + len].copy_from_slice(&input);
                let mut chain = [0xa5; 48];
                chain[offset..offset + 16].copy_from_slice(&iv);
                let iv = (&mut chain[offset..offset + 16]).try_into().unwrap();
                let data = &mut buffer[offset..offset + len];
                ctx.apply_keystream(iv, data);
                assert_eq!(&buffer[offset..offset + len], output);
                assert_eq!(&chain[offset..offset + 16], after);
                assert!(crate::bytes::all_equal(&buffer[..offset], 0xa5));
                assert!(crate::bytes::all_equal(&buffer[offset + len..], 0xa5));
                assert!(crate::bytes::all_equal(&chain[..offset], 0xa5));
                assert!(crate::bytes::all_equal(&chain[offset + 16..], 0xa5));
            }
        }
    }
}
