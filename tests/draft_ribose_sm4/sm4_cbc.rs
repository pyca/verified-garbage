//! SM4-CBC: the CBC examples (A.2.2) of the Internet-Draft
//! draft-ribose-cfrg-sm4-10, unmodified under vectors/, whole and in
//! pieces; and CBC from ECB (`Sm4Ecb`, tested on the draft's ECB examples)
//! on every length up to a few groups of sixteen blocks.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use verified_garbage::sm4_cbc::{Error, Sm4Cbc};
use verified_garbage::sm4_ecb::Sm4Ecb;

use super::{field, section};

/// CBC encryption from ECB, one block at a time.
fn reference(key: &[u8; 16], iv: [u8; 16], data: &[u8]) -> Vec<u8> {
    let ecb = Sm4Ecb::new(key);
    let mut chain = iv;
    let mut out = Vec::new();
    for block in data.chunks(16) {
        let mut b: Vec<u8> = block.iter().zip(&chain).map(|(x, y)| x ^ y).collect();
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
        let text = section(from, to);
        let key: [u8; 16] = field(text, "Encryption Key:").try_into().unwrap();
        let iv: [u8; 16] = field(text, "IV:").try_into().unwrap();
        let plaintext = field(text, "Plaintext:");
        let ciphertext = field(text, "Ciphertext:");
        check(&Sm4Cbc::new(&key), iv, &plaintext, &ciphertext);
    }
}

/// Every number of blocks up to three groups of sixteen and a bit.
#[test]
fn from_ecb() {
    let key: [u8; 16] = core::array::from_fn(|i| (17 * i + 3) as u8);
    let iv: [u8; 16] = core::array::from_fn(|i| (i * 11 + 5) as u8);
    let ctx = Sm4Cbc::new(&key);
    let data: Vec<u8> = (0..16 * 50).map(|i| (i * 31 + 7) as u8).collect();
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
