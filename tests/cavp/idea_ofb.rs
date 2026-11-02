//! IDEA-OFB: pyca/cryptography's vectors (derived from the AESVS MMT data,
//! verified against Botan), unmodified under vectors/, truncated and split
//! (`tests/modes.rs`).

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::idea_ofb::{IdeaOfb, InvalidKeyLength};

use verified_garbage_test_vectors::unhex;

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
        let ctx = IdeaOfb::new(&key).unwrap();
        let vector = (&plaintext[..], &ciphertext[..]);
        for io in [vector, (&ciphertext[..], &plaintext[..])] {
            crate::modes::check(crate::modes::Feedback::Output, iv, vector, io, &|iv, b| {
                ctx.apply_keystream(iv, b)
            });
        }
    }
    assert_eq!(key_lens, [16; 20]);
}

#[test]
fn errors() {
    for len in [0, 8, 15, 17, 24, 32] {
        assert_eq!(IdeaOfb::new(&vec![0; len]).err(), Some(InvalidKeyLength));
    }
}
