//! Camellia-CFB128: OpenSSL's test vectors as pyca/cryptography vendors
//! them, unmodified under vectors/; and CFB128 from ECB (`CamelliaEcb`,
//! tested on RFC 3713's and NTT's vectors) on every length up to a few
//! blocks, partial last segments included, for each key length.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::camellia_cfb::{CamelliaCfb128, InvalidKeyLength};
use verified_garbage::camellia_ecb::CamelliaEcb;

use verified_garbage_test_vectors::unhex;

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
fn openssl_vectors() {
    let text = crate::vectors::text("vectors/cryptography-camellia-cfb/camellia-cfb.txt");
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
    let data: Vec<u8> = crate::bytes::pattern(16 * 20, 31, 7);
    let iv: [u8; 16] = crate::bytes::pattern_array(11, 5);
    for key_len in [16, 24, 32] {
        let key: Vec<u8> = crate::bytes::pattern(key_len, 17, 3);
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

/// Independent batches must gather original ciphertext before overwriting it,
/// including short batches and unaligned data and IV buffers.
#[test]
fn decrypt_batches_unaligned() {
    let iv = crate::bytes::pattern_array(11, 5);
    for key_len in [16, 24, 32] {
        let key: Vec<u8> = crate::bytes::pattern(key_len, 17, 3);
        let ctx = CamelliaCfb128::new(&key).unwrap();
        for blocks in [0, 1, 2, 3, 4, 7, 8, 9, 15, 16, 17, 31, 32, 33, 64, 65, 1024] {
            for tail in [0, 7] {
                let len = 16 * blocks + tail;
                let input: Vec<u8> = crate::bytes::pattern(len, 31, 7);
                let (output, after) = reference(&key, iv, &input, false);
                for offset in 0..16 {
                    let mut buffer = vec![0xa5; len + 32];
                    buffer[offset..offset + len].copy_from_slice(&input);
                    let mut chain = [0xa5; 48];
                    chain[offset..offset + 16].copy_from_slice(&iv);
                    ctx.decrypt(
                        (&mut chain[offset..offset + 16]).try_into().unwrap(),
                        &mut buffer[offset..offset + len],
                    );
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
