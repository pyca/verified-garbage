#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::cast5_ofb::{Cast5Ofb, InvalidKeyLength};

#[test]
fn vectors() {
    let records = super::records(&crate::vectors::text(
        "vectors/cryptography-cast5-ofb/cast5-ofb.txt",
    ));
    assert_eq!(records.len(), 20);
    for (key, iv, plaintext, ciphertext) in records {
        let cipher = Cast5Ofb::new(&key).unwrap();
        // Whole, both ways.
        let mut chain = iv;
        let mut data = plaintext.clone();
        cipher.apply_keystream(&mut chain, &mut data);
        assert_eq!(data, ciphertext);
        let mut chain = iv;
        cipher.apply_keystream(&mut chain, &mut data);
        assert_eq!(data, plaintext);
        // A block at a time.
        let mut chain = iv;
        for block in data.chunks_mut(8) {
            cipher.apply_keystream(&mut chain, block);
        }
        assert_eq!(data, ciphertext);
        // Every prefix, its last segment partial or not.
        for len in 0..=plaintext.len() {
            let mut chain = iv;
            let mut data = plaintext[..len].to_vec();
            cipher.apply_keystream(&mut chain, &mut data);
            assert_eq!(data, ciphertext[..len]);
        }
    }
}

#[test]
fn errors_and_empty_input() {
    assert!(matches!(Cast5Ofb::new(&[0; 17]), Err(InvalidKeyLength)));
    let cipher = Cast5Ofb::new(&[7; 16]).unwrap();
    let mut iv = [0x5a; 8];
    cipher.apply_keystream(&mut iv, &mut []);
    assert_eq!(iv, [0x5a; 8]);
}
