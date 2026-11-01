//! SM4-CFB128: the CFB examples (A.2.4) of the Internet-Draft
//! draft-ribose-cfrg-sm4-10, unmodified under vectors/, whole and in pieces;
//! and CFB128 from ECB (`Sm4Ecb`, tested on the draft's ECB examples) on
//! every length up to a few blocks, partial last segments included.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::sm4_cfb::Sm4Cfb128;
use verified_garbage::sm4_ecb::Sm4Ecb;

use super::{field, section};

/// CFB128 from ECB: the output and the block to continue from (the last
/// ciphertext block, or after a partial segment `CIPH_K` of the last whole
/// one's).
fn reference(key: &[u8; 16], iv: [u8; 16], data: &[u8], encrypt: bool) -> (Vec<u8>, [u8; 16]) {
    let ecb = Sm4Ecb::new(key);
    let mut chain = iv;
    let mut out = Vec::new();
    for block in data.chunks(16) {
        let mut o = chain;
        ecb.encrypt(&mut o).unwrap();
        let y: Vec<u8> = crate::bytes::xor(block, &o);
        let c = if encrypt { &y[..] } else { block };
        chain = if block.len() == 16 {
            c.try_into().unwrap()
        } else {
            o
        };
        out.extend(y);
    }
    (out, chain)
}

#[test]
fn draft_examples() {
    for (from, to) in [
        ("A.2.4.1.  Example 1", "A.2.4.2.  Example 2"),
        ("A.2.4.2.  Example 2", "A.2.5.  SM4-CTR Examples"),
    ] {
        let text = &section(from, to);
        let key: [u8; 16] = field(text, "Encryption Key:").try_into().unwrap();
        let iv: [u8; 16] = field(text, "IV:").try_into().unwrap();
        let plaintext = field(text, "Plaintext:");
        let ciphertext = field(text, "Ciphertext:");
        let after: [u8; 16] = ciphertext[ciphertext.len() - 16..].try_into().unwrap();
        let ctx = Sm4Cfb128::new(&key);
        for offset in (0..=plaintext.len()).step_by(16) {
            let mut chain = iv;
            let mut buffer = plaintext.clone();
            ctx.encrypt(&mut chain, &mut buffer[..offset]);
            ctx.encrypt(&mut chain, &mut buffer[offset..]);
            assert_eq!(buffer, ciphertext);
            assert_eq!(chain, after);
            let mut chain = iv;
            ctx.decrypt(&mut chain, &mut buffer[..offset]);
            ctx.decrypt(&mut chain, &mut buffer[offset..]);
            assert_eq!(buffer, plaintext);
            assert_eq!(chain, after);
        }
    }
}

/// Every length up to 20 blocks, in each direction.
#[test]
fn from_ecb() {
    let key: [u8; 16] = crate::bytes::pattern_array(17, 3);
    let iv: [u8; 16] = crate::bytes::pattern_array(11, 5);
    let ctx = Sm4Cfb128::new(&key);
    let data: Vec<u8> = crate::bytes::pattern(16 * 20, 31, 7);
    for len in 0..=data.len() {
        for encrypt in [true, false] {
            let (output, after) = reference(&key, iv, &data[..len], encrypt);
            let mut chain = iv;
            let mut buffer = data[..len].to_vec();
            if encrypt {
                ctx.encrypt(&mut chain, &mut buffer);
            } else {
                ctx.decrypt(&mut chain, &mut buffer);
            }
            assert_eq!(buffer, output);
            assert_eq!(chain, after);
        }
    }
}

/// Unaligned buffers, partial segments and guards across batch boundaries.
#[test]
fn feedback_buffers_unaligned() {
    let key = crate::bytes::pattern_array(17, 3);
    let iv = crate::bytes::pattern_array(11, 5);
    let ctx = Sm4Cfb128::new(&key);
    for blocks in [0, 1, 2, 3, 4, 7, 8, 9, 15, 16, 17, 31, 32, 33, 64, 65, 1024] {
        for tail in [0, 7] {
            let len = 16 * blocks + tail;
            let input: Vec<u8> = crate::bytes::pattern(len, 31, 7);
            for encrypt in [true, false] {
                let (output, after) = reference(&key, iv, &input, encrypt);
                for offset in 0..16 {
                    let mut buffer = vec![0xa5; len + 32];
                    buffer[offset..offset + len].copy_from_slice(&input);
                    let mut chain = [0xa5; 48];
                    chain[offset..offset + 16].copy_from_slice(&iv);
                    let iv = (&mut chain[offset..offset + 16]).try_into().unwrap();
                    let data = &mut buffer[offset..offset + len];
                    if encrypt {
                        ctx.encrypt(iv, data);
                    } else {
                        ctx.decrypt(iv, data);
                    }
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
}
