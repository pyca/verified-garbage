//! SEED-CFB128: pyca/cryptography's vectors (derived from the AESVS MMT data, verified
//! against Botan), unmodified under vectors/; and CFB128 from ECB
//! (`SeedEcb`, tested on RFC 4269's vectors) on every length up to 20 blocks, partial last segments included.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::seed_cfb::{InvalidKeyLength, SeedCfb128};
use verified_garbage::seed_ecb::SeedEcb;

use super::unhex;

/// CFB64 from ECB: the output and the block to continue from (the last
/// ciphertext block, or after a partial segment `CIPH_K` of the last whole
/// one's).
fn reference(key: &[u8], iv: [u8; 16], data: &[u8], encrypt: bool) -> (Vec<u8>, [u8; 16]) {
    let ecb = SeedEcb::new(key.try_into().unwrap());
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
fn pyca_vectors() {
    let text = crate::vectors::text("vectors/cryptography-seed-cfb/seed-cfb.txt");
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
        let after: [u8; 16] = ciphertext[ciphertext.len() - 16..].try_into().unwrap();
        let ctx = SeedCfb128::new(&key).unwrap();
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
    assert_eq!(key_lens, [16; 20]);
}

/// Every length up to 20 blocks, in each direction, whole and split at
/// every block.
#[test]
fn from_ecb() {
    let data: Vec<u8> = crate::bytes::pattern(16 * 20, 31, 7);
    let iv: [u8; 16] = crate::bytes::pattern_array(11, 5);
    {
        let key: Vec<u8> = crate::bytes::pattern(16, 17, 3);
        let ctx = SeedCfb128::new(&key).unwrap();
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
    for len in [0, 8, 15, 17, 24, 32] {
        assert_eq!(SeedCfb128::new(&vec![0; len]).err(), Some(InvalidKeyLength));
    }
}
