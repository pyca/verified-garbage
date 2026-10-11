//! SM4-CFB128: the CFB examples (A.2.4) of the Internet-Draft
//! draft-ribose-cfrg-sm4-10, unmodified under vectors/, whole and in pieces;
//! and CFB128 from ECB (`Sm4Ecb`, tested on the draft's ECB examples) on
//! every length up to a few blocks, partial last segments included.

#![cfg(target_arch = "x86_64")]

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
        let y: Vec<u8> = block.iter().zip(&o).map(|(x, y)| x ^ y).collect();
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
        let text = section(from, to);
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
    let key: [u8; 16] = core::array::from_fn(|i| (17 * i + 3) as u8);
    let iv: [u8; 16] = core::array::from_fn(|i| (i * 11 + 5) as u8);
    let ctx = Sm4Cfb128::new(&key);
    let data: Vec<u8> = (0..16 * 20).map(|i| (i * 31 + 7) as u8).collect();
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
