//! Camellia-CFB128: OpenSSL's test vectors as pyca/cryptography vendors
//! them, unmodified under vectors/; and CFB128 from ECB (`CamelliaEcb`,
//! tested on RFC 3713's and NTT's vectors) on every length up to a few
//! blocks, partial last segments included, for each key length.

#![cfg(target_arch = "x86_64")]

use verified_garbage::camellia_cfb::{CamelliaCfb128, InvalidKeyLength};
use verified_garbage::camellia_ecb::CamelliaEcb;

use super::unhex;

/// CFB128 from ECB: the output and the block to continue from (the last
/// ciphertext block, or after a partial segment `CIPH_K` of the last whole
/// one's).
fn reference(key: &[u8], iv: [u8; 16], data: &[u8], encrypt: bool) -> (Vec<u8>, [u8; 16]) {
    let ecb = CamelliaEcb::new(key).unwrap();
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
fn openssl_vectors() {
    let text = include_str!("../../vectors/cryptography-camellia-cfb/camellia-cfb.txt");
    let mut key_lens = Vec::new();
    for record in text.split("COUNT = ").skip(1) {
        let get = |label: &str| {
            let line = record.lines().find(|l| l.starts_with(label)).unwrap();
            unhex(line.split_once(" = ").unwrap().1.trim())
        };
        let key = get("KEY");
        let iv: [u8; 16] = get("IV").try_into().unwrap();
        let (plaintext, ciphertext) = (get("PLAINTEXT"), get("CIPHERTEXT"));
        key_lens.push(key.len());
        let after: [u8; 16] = ciphertext[..].try_into().unwrap();
        let ctx = CamelliaCfb128::new(&key).unwrap();
        let mut chain = iv;
        let mut buffer = plaintext.clone();
        ctx.encrypt(&mut chain, &mut buffer);
        assert_eq!(buffer, ciphertext);
        assert_eq!(chain, after);
        let mut chain = iv;
        ctx.decrypt(&mut chain, &mut buffer);
        assert_eq!(buffer, plaintext);
        assert_eq!(chain, after);
    }
    assert_eq!(key_lens, [16, 16, 16, 16, 24, 24, 24, 24, 32, 32, 32, 32]);
}

/// Every length up to 20 blocks, in each direction, whole and split at
/// every block.
#[test]
fn from_ecb() {
    let data: Vec<u8> = (0..16 * 20).map(|i| (i * 31 + 7) as u8).collect();
    let iv: [u8; 16] = core::array::from_fn(|i| (i * 11 + 5) as u8);
    for key_len in [16, 24, 32] {
        let key: Vec<u8> = (0..key_len).map(|i| (17 * i + 3) as u8).collect();
        let ctx = CamelliaCfb128::new(&key).unwrap();
        for len in 0..=data.len() {
            for encrypt in [true, false] {
                let (output, after) = reference(&key, iv, &data[..len], encrypt);
                for offset in (0..=len).step_by(16) {
                    let mut chain = iv;
                    let mut buffer = data[..len].to_vec();
                    let (a, b) = buffer.split_at_mut(offset);
                    if encrypt {
                        ctx.encrypt(&mut chain, a);
                        ctx.encrypt(&mut chain, b);
                    } else {
                        ctx.decrypt(&mut chain, a);
                        ctx.decrypt(&mut chain, b);
                    }
                    assert_eq!(buffer, output);
                    assert_eq!(chain, after);
                }
            }
        }
    }
}

#[test]
fn errors() {
    for len in [0, 15, 17, 33] {
        assert_eq!(
            CamelliaCfb128::new(&vec![0; len]).err(),
            Some(InvalidKeyLength)
        );
    }
}
