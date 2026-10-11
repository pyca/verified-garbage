//! Camellia-OFB: OpenSSL's test vectors as pyca/cryptography vendors them,
//! unmodified under vectors/; and OFB from ECB (`CamelliaEcb`, tested on RFC
//! 3713's and NTT's vectors) on every length up to a few blocks, partial last
//! blocks included, for each key length.

#![cfg(target_arch = "x86_64")]

use verified_garbage::camellia_ecb::CamelliaEcb;
use verified_garbage::camellia_ofb::{CamelliaOfb, InvalidKeyLength};

use super::unhex;

/// OFB from ECB: the output and the last output block used.
fn reference(key: &[u8], iv: [u8; 16], data: &[u8]) -> (Vec<u8>, [u8; 16]) {
    let ecb = CamelliaEcb::new(key).unwrap();
    let mut o = iv;
    let mut out = Vec::new();
    for block in data.chunks(16) {
        ecb.encrypt(&mut o).unwrap();
        out.extend(block.iter().zip(&o).map(|(x, y)| x ^ y));
    }
    (out, o)
}

#[test]
fn openssl_vectors() {
    let text = include_str!("../../vectors/cryptography-camellia-ofb/camellia-ofb.txt");
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
        let after: [u8; 16] = core::array::from_fn(|i| plaintext[i] ^ ciphertext[i]);
        let ctx = CamelliaOfb::new(&key).unwrap();
        for (input, output) in [(&plaintext, &ciphertext), (&ciphertext, &plaintext)] {
            let mut chain = iv;
            let mut buffer = input.clone();
            ctx.apply_keystream(&mut chain, &mut buffer);
            assert_eq!(&buffer, output);
            assert_eq!(chain, after);
        }
    }
    assert_eq!(key_lens, [16, 16, 16, 16, 24, 24, 24, 24, 32, 32, 32, 32]);
}

/// Every length up to 20 blocks, whole and split at every block.
#[test]
fn from_ecb() {
    let data: Vec<u8> = (0..16 * 20).map(|i| (i * 31 + 7) as u8).collect();
    let iv: [u8; 16] = core::array::from_fn(|i| (i * 11 + 5) as u8);
    for key_len in [16, 24, 32] {
        let key: Vec<u8> = (0..key_len).map(|i| (17 * i + 3) as u8).collect();
        let ctx = CamelliaOfb::new(&key).unwrap();
        for len in 0..=data.len() {
            let (output, after) = reference(&key, iv, &data[..len]);
            for offset in (0..=len).step_by(16) {
                let mut chain = iv;
                let mut buffer = data[..len].to_vec();
                ctx.apply_keystream(&mut chain, &mut buffer[..offset]);
                ctx.apply_keystream(&mut chain, &mut buffer[offset..]);
                assert_eq!(buffer, output);
                assert_eq!(chain, after);
            }
        }
    }
}

#[test]
fn errors() {
    for len in [0, 15, 17, 33] {
        assert_eq!(
            CamelliaOfb::new(&vec![0; len]).err(),
            Some(InvalidKeyLength)
        );
    }
}
