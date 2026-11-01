//! Blowfish-OFB: pyca/cryptography's vector (reformatted from Schneier's
//! test vectors, with a partial last block), unmodified under vectors/; and
//! OFB from ECB (`BlowfishEcbEncryptor`, tested on Schneier's vectors) on
//! every length up to 20 blocks, partial last blocks included, for keys of
//! the shortest, a middle and the longest length.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::blowfish_ecb::BlowfishEcbEncryptor;
use verified_garbage::blowfish_ofb::{BlowfishOfb, InvalidKeyLength};

use super::unhex;

/// OFB from ECB: the output and the last output block used.
fn reference(ecb: &mut BlowfishEcbEncryptor, iv: [u8; 8], data: &[u8]) -> (Vec<u8>, [u8; 8]) {
    let mut o = iv;
    let mut out = Vec::new();
    for block in data.chunks(8) {
        let prev = o;
        assert_eq!(ecb.update(&prev, &mut o).unwrap(), 8);
        out.extend(block.iter().zip(&o).map(|(x, y)| x ^ y));
    }
    (out, o)
}

/// OFB of `input` with `ctx`, whole and split at every block, gives
/// `output` and leaves `after` as the block to continue from.
fn check(ctx: &BlowfishOfb, iv: [u8; 8], input: &[u8], output: &[u8], after: [u8; 8]) {
    for offset in (0..=input.len()).step_by(8) {
        let mut chain = iv;
        let mut buffer = input.to_vec();
        ctx.apply_keystream(&mut chain, &mut buffer[..offset]);
        ctx.apply_keystream(&mut chain, &mut buffer[offset..]);
        assert_eq!(buffer, output);
        assert_eq!(chain, after);
    }
}

#[test]
fn pyca_vectors() {
    let text = crate::vectors::text("vectors/cryptography-blowfish-ofb/bf-ofb.txt");
    let mut key_lens = Vec::new();
    for record in text.split("COUNT = ").skip(1) {
        let get = |label: &str| {
            let line = record.lines().find(|l| l.starts_with(label)).unwrap();
            unhex(line.split_once(" = ").unwrap().1.trim())
        };
        let key = get("KEY");
        let iv: [u8; 8] = get("IV").try_into().unwrap();
        let (plaintext, ciphertext) = (get("PLAINTEXT"), get("CIPHERTEXT"));
        key_lens.push(key.len());
        let mut ecb = BlowfishEcbEncryptor::new(&key).unwrap();
        // The last output block, which the vector gives only in part.
        let (expected, after) = reference(&mut ecb, iv, &plaintext);
        ecb.finalize().unwrap();
        assert_eq!(expected, ciphertext);
        let ctx = BlowfishOfb::new(&key).unwrap();
        check(&ctx, iv, &plaintext, &ciphertext, after);
        check(&ctx, iv, &ciphertext, &plaintext, after);
    }
    assert_eq!(key_lens, [16]);
}

/// Every length up to 20 blocks, whole and split at every block.
#[test]
fn from_ecb() {
    let data: Vec<u8> = (0..8 * 20).map(|i| (i * 31 + 7) as u8).collect();
    let iv: [u8; 8] = core::array::from_fn(|i| (i * 11 + 5) as u8);
    for key_len in [4, 16, 56] {
        let key: Vec<u8> = (0..key_len).map(|i| (17 * i + 3) as u8).collect();
        let mut ecb = BlowfishEcbEncryptor::new(&key).unwrap();
        let ctx = BlowfishOfb::new(&key).unwrap();
        for len in 0..=data.len() {
            let (output, after) = reference(&mut ecb, iv, &data[..len]);
            check(&ctx, iv, &data[..len], &output, after);
        }
        ecb.finalize().unwrap();
    }
}

#[test]
fn errors() {
    for len in [0, 1, 3, 57, 64] {
        assert_eq!(
            BlowfishOfb::new(&vec![0; len]).err(),
            Some(InvalidKeyLength)
        );
    }
}
