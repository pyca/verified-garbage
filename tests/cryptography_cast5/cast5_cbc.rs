#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::cast5_cbc::{Cast5Cbc, Error};

const VECTORS: &str = include_str!("../../vectors/cryptography-cast5/cast5-cbc.txt");

#[test]
fn vectors() {
    let records = super::records(VECTORS);
    assert_eq!(records.len(), 20);
    for (key, iv, plaintext, ciphertext) in records {
        let cipher = Cast5Cbc::new(&key).unwrap();
        // Whole.
        let mut chain = iv;
        let mut data = plaintext.clone();
        cipher.encrypt(&mut chain, &mut data).unwrap();
        assert_eq!(data, ciphertext);
        assert_eq!(chain[..], ciphertext[ciphertext.len() - 8..]);
        let mut chain = iv;
        cipher.decrypt(&mut chain, &mut data).unwrap();
        assert_eq!(data, plaintext);
        assert_eq!(chain[..], ciphertext[ciphertext.len() - 8..]);
        // A block at a time, each continuing from the chaining value the
        // last left.
        let mut chain = iv;
        let mut data = plaintext.clone();
        for block in data.chunks_mut(8) {
            cipher.encrypt(&mut chain, block).unwrap();
        }
        assert_eq!(data, ciphertext);
        let mut chain = iv;
        for block in data.chunks_mut(8) {
            cipher.decrypt(&mut chain, block).unwrap();
        }
        assert_eq!(data, plaintext);
    }
}

#[test]
fn errors_and_empty_input() {
    assert!(matches!(
        Cast5Cbc::new(&[0; 4]),
        Err(Error::InvalidKeyLength)
    ));
    let cipher = Cast5Cbc::new(&[7; 10]).unwrap();
    let mut iv = [0x5a; 8];
    let mut data = [0xa5; 12];
    assert_eq!(
        cipher.encrypt(&mut iv, &mut data),
        Err(Error::IncompleteBlock)
    );
    assert_eq!(
        cipher.decrypt(&mut iv, &mut data),
        Err(Error::IncompleteBlock)
    );
    assert_eq!((iv, data), ([0x5a; 8], [0xa5; 12]));
    cipher.encrypt(&mut iv, &mut []).unwrap();
    cipher.decrypt(&mut iv, &mut []).unwrap();
    assert_eq!(iv, [0x5a; 8]);
}
