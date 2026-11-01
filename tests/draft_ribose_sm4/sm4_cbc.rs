//! SM4-CBC: the CBC examples (A.2.2) of the Internet-Draft
//! draft-ribose-cfrg-sm4-10, unmodified under vectors/, whole and in
//! pieces; and CBC from ECB (`Sm4Ecb`, tested on the draft's ECB examples)
//! on every length up to 50 blocks.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::sm4_cbc::{Error, Sm4Cbc};
use verified_garbage::sm4_ecb::Sm4Ecb;

use super::{field, section};

/// CBC encryption from ECB, one block at a time.
fn reference(key: &[u8; 16], iv: [u8; 16], data: &[u8]) -> Vec<u8> {
    let ecb = Sm4Ecb::new(key);
    let mut chain = iv;
    let mut out = Vec::new();
    for block in data.chunks(16) {
        let mut b: Vec<u8> = crate::bytes::xor(block, &chain);
        ecb.encrypt(&mut b).unwrap();
        chain.copy_from_slice(&b);
        out.extend_from_slice(&b);
    }
    out
}

/// `plaintext` encrypts to `ciphertext` and decrypts back, whole and split
/// at every block boundary, leaving the last ciphertext block as the
/// chaining value.
fn check(ctx: &Sm4Cbc, iv: [u8; 16], plaintext: &[u8], ciphertext: &[u8]) {
    let after: [u8; 16] = match ciphertext.len() {
        0 => iv,
        len => ciphertext[len - 16..].try_into().unwrap(),
    };
    for offset in (0..=plaintext.len()).step_by(16) {
        let mut chain = iv;
        let mut buffer = plaintext.to_vec();
        ctx.encrypt(&mut chain, &mut buffer[..offset]).unwrap();
        ctx.encrypt(&mut chain, &mut buffer[offset..]).unwrap();
        assert_eq!(buffer, ciphertext);
        assert_eq!(chain, after);
        let mut chain = iv;
        ctx.decrypt(&mut chain, &mut buffer[..offset]).unwrap();
        ctx.decrypt(&mut chain, &mut buffer[offset..]).unwrap();
        assert_eq!(buffer, plaintext);
        assert_eq!(chain, after);
    }
}

#[test]
fn draft_examples() {
    for (from, to) in [
        ("A.2.2.1.  Example 1", "A.2.2.2.  Example 2"),
        ("A.2.2.2.  Example 2", "A.2.3.  SM4-OFB Examples"),
    ] {
        let text = &section(from, to);
        let key: [u8; 16] = field(text, "Encryption Key:").try_into().unwrap();
        let iv: [u8; 16] = field(text, "IV:").try_into().unwrap();
        let plaintext = field(text, "Plaintext:");
        let ciphertext = field(text, "Ciphertext:");
        check(&Sm4Cbc::new(&key), iv, &plaintext, &ciphertext);
    }
}

/// Every number of blocks up to 50.
#[test]
fn from_ecb() {
    let key: [u8; 16] = crate::bytes::pattern_array(17, 3);
    let iv: [u8; 16] = crate::bytes::pattern_array(11, 5);
    let ctx = Sm4Cbc::new(&key);
    let data: Vec<u8> = crate::bytes::pattern(16 * 50, 31, 7);
    for blocks in 0..=50 {
        let input = &data[..16 * blocks];
        check(&ctx, iv, input, &reference(&key, iv, input));
    }
}

#[test]
fn incomplete_blocks() {
    let ctx = Sm4Cbc::new(&[0; 16]);
    for len in [1, 15, 17, 31] {
        let mut chain = [7; 16];
        let mut buffer = vec![0x5a; len];
        assert_eq!(
            ctx.encrypt(&mut chain, &mut buffer),
            Err(Error::IncompleteBlock)
        );
        assert_eq!(
            ctx.decrypt(&mut chain, &mut buffer),
            Err(Error::IncompleteBlock)
        );
        assert_eq!(buffer, vec![0x5a; len]);
        assert_eq!(chain, [7; 16]);
    }
}

/// Slices at every byte offset, with an unaligned chaining value, leave the
/// bytes around them unchanged, including empty slices and lengths around
/// multiples of sixteen blocks.
#[test]
fn unaligned_guarded() {
    for key in [[0; 16], [0xff; 16], crate::bytes::pattern_array(1, 0)] {
        let ctx = Sm4Cbc::new(&key);
        let iv = crate::bytes::pattern_array(19, 3);
        for blocks in [0, 1, 2, 3, 15, 16, 17, 31, 32, 33, 64, 65] {
            let input: Vec<u8> = crate::bytes::pattern(16 * blocks, 29, 11);
            let expected = reference(&key, iv, &input);
            let after = expected.last_chunk::<16>().copied().unwrap_or(iv);
            for offset in 0..16 {
                let mut buffer = vec![0xa5; offset + input.len() + 16];
                buffer[offset..offset + input.len()].copy_from_slice(&input);
                let mut chain = [0xa5; 48];
                let start = (offset + 3) % 16;
                chain[start..start + 16].copy_from_slice(&iv);
                ctx.encrypt(
                    (&mut chain[start..start + 16]).try_into().unwrap(),
                    &mut buffer[offset..offset + input.len()],
                )
                .unwrap();
                assert_eq!(&buffer[offset..offset + input.len()], &expected);
                assert_eq!(&chain[start..start + 16], &after);
                chain[start..start + 16].copy_from_slice(&iv);
                ctx.decrypt(
                    (&mut chain[start..start + 16]).try_into().unwrap(),
                    &mut buffer[offset..offset + input.len()],
                )
                .unwrap();
                assert_eq!(&buffer[offset..offset + input.len()], &input);
                assert_eq!(&chain[start..start + 16], &after);
                assert!(crate::bytes::all_equal(&buffer[..offset], 0xa5));
                assert!(crate::bytes::all_equal(
                    &buffer[offset + input.len()..],
                    0xa5
                ));
                assert!(crate::bytes::all_equal(&chain[..start], 0xa5));
                assert!(crate::bytes::all_equal(&chain[start + 16..], 0xa5));
            }
        }
    }
}
