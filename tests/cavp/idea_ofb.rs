//! IDEA-OFB: pyca/cryptography's vectors (derived from the AESVS MMT data,
//! verified against Botan), unmodified under vectors/; and OFB from ECB
//! (`IdeaEcb`, tested on the NESSIE vectors) on every length up to 20 blocks,
//! partial last blocks included.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::idea_ecb::IdeaEcb;
use verified_garbage::idea_ofb::{IdeaOfb, InvalidKeyLength};

use super::unhex;

/// OFB from ECB: the output and the last output block used.
fn reference(key: &[u8], iv: [u8; 8], data: &[u8]) -> (Vec<u8>, [u8; 8]) {
    let ecb = IdeaEcb::new(key).unwrap();
    let mut o = iv;
    let mut out = Vec::new();
    for block in data.chunks(8) {
        ecb.encrypt(&mut o).unwrap();
        out.extend(crate::bytes::xor(block, &o));
    }
    (out, o)
}

#[test]
fn pyca_vectors() {
    let text = crate::vectors::text("vectors/cryptography-idea-ofb/idea-ofb.txt");
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
        let last = plaintext.len() - 8;
        let after: [u8; 8] = core::array::from_fn(|i| plaintext[last + i] ^ ciphertext[last + i]);
        let ctx = IdeaOfb::new(&key).unwrap();
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
    let data: Vec<u8> = crate::bytes::pattern(8 * 20, 31, 7);
    let iv: [u8; 8] = crate::bytes::pattern_array(11, 5);
    {
        let key: Vec<u8> = crate::bytes::pattern(16, 17, 3);
        let ctx = IdeaOfb::new(&key).unwrap();
        for len in 0..=data.len() {
            let (output, after) = reference(&key, iv, &data[..len]);
            for offset in (0..=len).step_by(8) {
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
        assert_eq!(IdeaOfb::new(&vec![0; len]).err(), Some(InvalidKeyLength));
    }
}
