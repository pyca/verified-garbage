//! SEED-OFB: pyca/cryptography's vectors (derived from the AESVS MMT data,
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

use verified_garbage::cipher::seed::SeedOfb;

use verified_garbage_test_vectors::unhex;

#[test]
fn pyca_vectors() {
    let text = crate::vectors::text("vectors/cryptography-seed-ofb/seed-ofb.txt");
    let mut key_lens = Vec::new();
    for record in text.split("COUNT = ").skip(1) {
        let get = |label: &str| {
            let line = record.lines().find(|l| l.starts_with(label)).unwrap();
            unhex(line.split_once(" = ").unwrap().1.trim())
        };
        let key: [u8; 16] = get("KEY").try_into().unwrap();
        let iv: [u8; 16] = get("IV").try_into().unwrap();
        let (plaintext, ciphertext) = (get("PLAINTEXT"), get("CIPHERTEXT"));
        key_lens.push(key.len());
        let vector = (&plaintext[..], &ciphertext[..]);
        for io in [vector, (&ciphertext[..], &plaintext[..])] {
            crate::modes::check(
                iv,
                io,
                &|iv| SeedOfb::new(&key, iv),
                SeedOfb::apply_keystream,
                SeedOfb::apply_keystream_final,
            );
        }
    }
    assert_eq!(key_lens, [16; 20]);
}
