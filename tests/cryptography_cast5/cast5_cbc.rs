#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::cast5_cbc::{Cast5CbcDecryptor, Cast5CbcEncryptor, Error};

#[test]
fn vectors() {
    let records = super::records(&crate::vectors::text(
        "vectors/cryptography-cast5/cast5-cbc.txt",
    ));
    assert_eq!(records.len(), 20);
    for (key, iv, plaintext, ciphertext) in records {
        // Whole.
        let mut data = plaintext.clone();
        let mut encryptor = Cast5CbcEncryptor::new(&key, &iv).unwrap();
        encryptor.encrypt(&mut data).unwrap();
        assert_eq!(data, ciphertext);
        let mut decryptor = Cast5CbcDecryptor::new(&key, &iv).unwrap();
        decryptor.decrypt(&mut data).unwrap();
        assert_eq!(data, plaintext);
        // A block at a time, each continuing the message.
        let mut encryptor = Cast5CbcEncryptor::new(&key, &iv).unwrap();
        for block in data.chunks_mut(8) {
            encryptor.encrypt(block).unwrap();
        }
        assert_eq!(data, ciphertext);
        let mut decryptor = Cast5CbcDecryptor::new(&key, &iv).unwrap();
        for block in data.chunks_mut(8) {
            decryptor.decrypt(block).unwrap();
        }
        assert_eq!(data, plaintext);
    }
}

#[test]
fn errors_and_empty_input() {
    assert!(matches!(
        Cast5CbcEncryptor::new(&[0; 4], &[0; 8]),
        Err(Error::InvalidKeyLength)
    ));
    assert!(matches!(
        Cast5CbcDecryptor::new(&[0; 4], &[0; 8]),
        Err(Error::InvalidKeyLength)
    ));
    let (key, iv) = ([7; 10], [0x5a; 8]);
    let mut encryptor = Cast5CbcEncryptor::new(&key, &iv).unwrap();
    let mut decryptor = Cast5CbcDecryptor::new(&key, &iv).unwrap();
    let mut data = [0xa5; 12];
    assert_eq!(encryptor.encrypt(&mut data), Err(Error::IncompleteBlock));
    assert_eq!(decryptor.decrypt(&mut data), Err(Error::IncompleteBlock));
    assert_eq!(data, [0xa5; 12]);
    encryptor.encrypt(&mut []).unwrap();
    decryptor.decrypt(&mut []).unwrap();
    // None of these calls changed the chaining value.
    let mut data = [0xa5; 16];
    let mut expected = data;
    Cast5CbcEncryptor::new(&key, &iv)
        .unwrap()
        .encrypt(&mut expected)
        .unwrap();
    encryptor.encrypt(&mut data).unwrap();
    assert_eq!(data, expected);
    decryptor.decrypt(&mut data).unwrap();
    assert_eq!(data, [0xa5; 16]);
}
