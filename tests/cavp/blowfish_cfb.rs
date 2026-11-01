//! Blowfish-CFB64: pyca/cryptography's vector (reformatted from Schneier's
//! test vectors, with a partial last segment), unmodified under vectors/;
//! and CFB64 from ECB (`BlowfishEcbEncryptor`, tested on Schneier's vectors)
//! on every length up to 20 blocks, partial last segments included, for keys
//! of the shortest, a middle and the longest length.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::blowfish_cfb::{BlowfishCfb64, InvalidKeyLength};
use verified_garbage::blowfish_ecb::BlowfishEcbEncryptor;

use super::unhex;

/// CFB64 from ECB: the output and the block to continue from (the last
/// ciphertext block, or after a partial segment `CIPH_K` of the last whole
/// one's).
fn reference(
    ecb: &mut BlowfishEcbEncryptor,
    iv: [u8; 8],
    data: &[u8],
    encrypt: bool,
) -> (Vec<u8>, [u8; 8]) {
    let mut chain = iv;
    let mut out = Vec::new();
    for block in data.chunks(8) {
        let mut o = [0; 8];
        assert_eq!(ecb.update(&chain, &mut o).unwrap(), 8);
        let y: Vec<u8> = block.iter().zip(&o).map(|(x, y)| x ^ y).collect();
        let c = if encrypt { &y[..] } else { block };
        chain = if block.len() == 8 {
            c.try_into().unwrap()
        } else {
            o
        };
        out.extend(y);
    }
    (out, chain)
}

/// Encrypts or decrypts `data` with `ctx`, whole and split at every block,
/// and checks the output and the block to continue from.
fn check(
    ctx: &BlowfishCfb64,
    iv: [u8; 8],
    data: &[u8],
    encrypt: bool,
    output: &[u8],
    after: [u8; 8],
) {
    for offset in (0..=data.len()).step_by(8) {
        let mut chain = iv;
        let mut buffer = data.to_vec();
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

#[test]
fn pyca_vectors() {
    let text = crate::vectors::text("vectors/cryptography-blowfish-cfb/bf-cfb.txt");
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
        // The block to continue from, which the vector does not give.
        let (expected, after) = reference(&mut ecb, iv, &plaintext, true);
        ecb.finalize().unwrap();
        assert_eq!(expected, ciphertext);
        let ctx = BlowfishCfb64::new(&key).unwrap();
        check(&ctx, iv, &plaintext, true, &ciphertext, after);
        check(&ctx, iv, &ciphertext, false, &plaintext, after);
    }
    assert_eq!(key_lens, [16]);
}

/// Every length up to 20 blocks, in each direction, whole and split at
/// every block.
#[test]
fn from_ecb() {
    let data: Vec<u8> = (0..8 * 20).map(|i| (i * 31 + 7) as u8).collect();
    let iv: [u8; 8] = core::array::from_fn(|i| (i * 11 + 5) as u8);
    for key_len in [4, 16, 56] {
        let key: Vec<u8> = (0..key_len).map(|i| (17 * i + 3) as u8).collect();
        let mut ecb = BlowfishEcbEncryptor::new(&key).unwrap();
        let ctx = BlowfishCfb64::new(&key).unwrap();
        for len in 0..=data.len() {
            for encrypt in [true, false] {
                let (output, after) = reference(&mut ecb, iv, &data[..len], encrypt);
                check(&ctx, iv, &data[..len], encrypt, &output, after);
            }
        }
        ecb.finalize().unwrap();
    }
}

#[test]
fn errors() {
    for len in [0, 1, 3, 57, 64] {
        assert_eq!(
            BlowfishCfb64::new(&vec![0; len]).err(),
            Some(InvalidKeyLength)
        );
    }
}
