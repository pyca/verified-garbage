//! SEED-OFB: pyca/cryptography's vectors (derived from the AESVS MMT data, verified
//! against Botan), unmodified under vectors/; and OFB from ECB
//! (`SeedEcb`, tested on RFC 4269's vectors) on every length up to 20 blocks, partial last blocks included.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::seed_ecb::SeedEcb;
use verified_garbage::seed_ofb::{InvalidKeyLength, SeedOfb};

use verified_garbage_test_vectors::unhex;

/// OFB from ECB: the output and the last output block used.
fn reference(key: &[u8], iv: [u8; 16], data: &[u8]) -> (Vec<u8>, [u8; 16]) {
    let ecb = SeedEcb::new(key.try_into().unwrap());
    let mut o = iv;
    let mut out = Vec::new();
    for block in data.chunks(16) {
        ecb.encrypt(&mut o).unwrap();
        out.extend(crate::bytes::xor(block, &o));
    }
    (out, o)
}

#[test]
fn pyca_vectors() {
    let text = crate::vectors::text("vectors/cryptography-seed-ofb/seed-ofb.txt");
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
        let last = plaintext.len() - 16;
        let after: [u8; 16] = core::array::from_fn(|i| plaintext[last + i] ^ ciphertext[last + i]);
        let ctx = SeedOfb::new(&key).unwrap();
        for (input, output) in [(&plaintext, &ciphertext), (&ciphertext, &plaintext)] {
            let mut chain = iv;
            let mut buffer = input.clone();
            ctx.apply_keystream(&mut chain, &mut buffer);
            assert_eq!(&buffer, output);
            assert_eq!(chain, after);
        }
    }
    assert_eq!(key_lens, [16; 20]);
}

/// Every length up to 20 blocks, whole and split at every block.
#[test]
fn from_ecb() {
    let data: Vec<u8> = crate::bytes::pattern(16 * 20, 31, 7);
    let iv: [u8; 16] = crate::bytes::pattern_array(11, 5);
    {
        let key: Vec<u8> = crate::bytes::pattern(16, 17, 3);
        let ctx = SeedOfb::new(&key).unwrap();
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
    for len in [0, 8, 15, 17, 24, 32] {
        assert_eq!(SeedOfb::new(&vec![0; len]).err(), Some(InvalidKeyLength));
    }
}
