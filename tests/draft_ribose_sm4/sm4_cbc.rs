//! SM4-CBC: the CBC examples (A.2.2) of the Internet-Draft
//! draft-ribose-cfrg-sm4-10, unmodified under vectors/, whole, in pieces,
//! and in place in unaligned buffers.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::error::IncompleteBlock;

use verified_garbage::cipher::sm4::{Sm4CbcDecryptor, Sm4CbcEncryptor};

use super::{field, section};

/// An example: key, IV, plaintext and ciphertext.
type Example = ([u8; 16], [u8; 16], Vec<u8>, Vec<u8>);

/// The examples.
fn examples() -> Vec<Example> {
    let mut examples = Vec::new();
    for (from, to) in [
        ("A.2.2.1.  Example 1", "A.2.2.2.  Example 2"),
        ("A.2.2.2.  Example 2", "A.2.3.  SM4-OFB Examples"),
    ] {
        let text = &section(from, to);
        examples.push((
            field(text, "Encryption Key:").try_into().unwrap(),
            field(text, "IV:").try_into().unwrap(),
            field(text, "Plaintext:"),
            field(text, "Ciphertext:"),
        ));
    }
    examples
}

/// `plaintext` encrypts to `ciphertext` and decrypts back, whole and split
/// at every block boundary.
fn check(key: &[u8; 16], iv: [u8; 16], plaintext: &[u8], ciphertext: &[u8]) {
    for offset in (0..=plaintext.len()).step_by(16) {
        let mut buffer = plaintext.to_vec();
        let mut encryptor = Sm4CbcEncryptor::new(key, &iv);
        encryptor.encrypt(&mut buffer[..offset]).unwrap();
        encryptor.encrypt(&mut buffer[offset..]).unwrap();
        assert_eq!(buffer, ciphertext);
        let mut decryptor = Sm4CbcDecryptor::new(key, &iv);
        decryptor.decrypt(&mut buffer[..offset]).unwrap();
        decryptor.decrypt(&mut buffer[offset..]).unwrap();
        assert_eq!(buffer, plaintext);
    }
}

#[test]
fn draft_examples() {
    for (key, iv, plaintext, ciphertext) in examples() {
        check(&key, iv, &plaintext, &ciphertext);
    }
}

/// A piece that is not a whole number of blocks is refused, changing neither
/// it nor the chaining value.
#[test]
fn incomplete_blocks() {
    let mut encryptor = Sm4CbcEncryptor::new(&[0; 16], &[7; 16]);
    let mut decryptor = Sm4CbcDecryptor::new(&[0; 16], &[7; 16]);
    for len in [1, 15, 17, 31] {
        let mut buffer = vec![0x5a; len];
        assert_eq!(encryptor.encrypt(&mut buffer), Err(IncompleteBlock));
        assert_eq!(decryptor.decrypt(&mut buffer), Err(IncompleteBlock));
        assert_eq!(buffer, vec![0x5a; len]);
    }
    let mut buffer = [0x5a; 32];
    let mut expected = buffer;
    Sm4CbcEncryptor::new(&[0; 16], &[7; 16])
        .encrypt(&mut expected)
        .unwrap();
    encryptor.encrypt(&mut buffer).unwrap();
    assert_eq!(buffer, expected);
    decryptor.decrypt(&mut buffer).unwrap();
    assert_eq!(buffer, [0x5a; 32]);
}

/// The examples in place, at every offset of the data, leave the bytes
/// around them unchanged.
#[test]
fn unaligned_guarded() {
    for (key, iv, plaintext, ciphertext) in examples() {
        crate::modes::check_unaligned(
            iv,
            (&plaintext, &ciphertext),
            &|iv| Sm4CbcEncryptor::new(&key, iv),
            |mut c, b| c.encrypt(b).unwrap(),
        );
        crate::modes::check_unaligned(
            iv,
            (&ciphertext, &plaintext),
            &|iv| Sm4CbcDecryptor::new(&key, iv),
            |mut c, b| c.decrypt(b).unwrap(),
        );
    }
}

/// Many blocks at once, at lengths around multiples of sixteen blocks (the
/// groups decryption deciphers together), agree with one at a time and with
/// the message decrypted in two pieces, and encryption undoes decryption.
#[test]
fn batches() {
    // Generated inputs test agreement between lengths, not known answers.
    let (key, iv) = ([7; 16], [9; 16]);
    let input = crate::bytes::pattern(16 * 50, 1, 0);
    for blocks in [1, 15, 16, 17, 31, 32, 33, 50] {
        let input = &input[..16 * blocks];
        let mut whole = input.to_vec();
        Sm4CbcDecryptor::new(&key, &iv).decrypt(&mut whole).unwrap();
        let mut single = input.to_vec();
        let mut decryptor = Sm4CbcDecryptor::new(&key, &iv);
        for block in single.chunks_mut(16) {
            decryptor.decrypt(block).unwrap();
        }
        assert_eq!(whole, single);
        let mut rest = input.to_vec();
        let mut decryptor = Sm4CbcDecryptor::new(&key, &iv);
        decryptor.decrypt(&mut rest[..16 * blocks - 16]).unwrap();
        decryptor.decrypt(&mut rest[16 * blocks - 16..]).unwrap();
        assert_eq!(rest, single);
        Sm4CbcEncryptor::new(&key, &iv).encrypt(&mut whole).unwrap();
        assert_eq!(whole, input);
    }
}
