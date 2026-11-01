#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::cast5_cfb::{Cast5Cfb64, InvalidKeyLength};

#[test]
fn vectors() {
    let records = super::records(crate::vectors::text(
        "vectors/cryptography-cast5-cfb/cast5-cfb.txt",
    ));
    assert_eq!(records.len(), 20);
    for (key, iv, plaintext, ciphertext) in records {
        let cipher = Cast5Cfb64::new(&key).unwrap();
        // Whole.
        let mut chain = iv;
        let mut data = plaintext.clone();
        cipher.encrypt(&mut chain, &mut data);
        assert_eq!(data, ciphertext);
        assert_eq!(chain[..], ciphertext[ciphertext.len() - 8..]);
        let mut chain = iv;
        cipher.decrypt(&mut chain, &mut data);
        assert_eq!(data, plaintext);
        assert_eq!(chain[..], ciphertext[ciphertext.len() - 8..]);
        // A block at a time.
        let mut chain = iv;
        for block in data.chunks_mut(8) {
            cipher.encrypt(&mut chain, block);
        }
        assert_eq!(data, ciphertext);
        let mut chain = iv;
        for block in data.chunks_mut(8) {
            cipher.decrypt(&mut chain, block);
        }
        assert_eq!(data, plaintext);
        // Every prefix, its last segment partial or not.
        for len in 0..=plaintext.len() {
            let mut chain = iv;
            let mut data = plaintext[..len].to_vec();
            cipher.encrypt(&mut chain, &mut data);
            assert_eq!(data, ciphertext[..len]);
            let mut chain = iv;
            cipher.decrypt(&mut chain, &mut data);
            assert_eq!(data, plaintext[..len]);
        }
    }
}

#[test]
fn errors_and_empty_input() {
    assert!(matches!(Cast5Cfb64::new(&[]), Err(InvalidKeyLength)));
    let cipher = Cast5Cfb64::new(&[7; 5]).unwrap();
    let mut iv = [0x5a; 8];
    cipher.encrypt(&mut iv, &mut []);
    cipher.decrypt(&mut iv, &mut []);
    assert_eq!(iv, [0x5a; 8]);
}
