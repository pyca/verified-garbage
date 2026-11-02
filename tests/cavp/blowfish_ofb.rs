//! Blowfish-OFB: pyca/cryptography's vector (reformatted from Schneier's
//! test vectors, with a partial last block), unmodified under vectors/,
//! truncated and split (`tests/modes.rs`).

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::blowfish_ofb::{BlowfishOfb, InvalidKeyLength};

use verified_garbage_test_vectors::unhex;

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
        let ctx = BlowfishOfb::new(&key).unwrap();
        let vector = (&plaintext[..], &ciphertext[..]);
        for io in [vector, (&ciphertext[..], &plaintext[..])] {
            crate::modes::check(crate::modes::Feedback::Output, iv, vector, io, &|iv, b| {
                ctx.apply_keystream(iv, b)
            });
        }
    }
    assert_eq!(key_lens, [16]);
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
