//! SM4-CFB128: the CFB examples (A.2.4) of the Internet-Draft
//! draft-ribose-cfrg-sm4-10, unmodified under vectors/, truncated and split
//! (`tests/modes.rs`), and in place in unaligned buffers.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::cipher::sm4::{Sm4Cfb128Decryptor, Sm4Cfb128Encryptor};

use super::{field, section};

/// An example: key, IV, plaintext and ciphertext.
type Example = ([u8; 16], [u8; 16], Vec<u8>, Vec<u8>);

/// The examples.
fn examples() -> Vec<Example> {
    let mut examples = Vec::new();
    for (from, to) in [
        ("A.2.4.1.  Example 1", "A.2.4.2.  Example 2"),
        ("A.2.4.2.  Example 2", "A.2.5.  SM4-CTR Examples"),
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

#[test]
fn draft_examples() {
    for (key, iv, plaintext, ciphertext) in examples() {
        let vector = (&plaintext[..], &ciphertext[..]);
        crate::modes::check(
            iv,
            vector,
            &|iv| Sm4Cfb128Encryptor::new(&key, iv),
            Sm4Cfb128Encryptor::encrypt,
            Sm4Cfb128Encryptor::encrypt_final,
        );
        crate::modes::check(
            iv,
            (&ciphertext, &plaintext),
            &|iv| Sm4Cfb128Decryptor::new(&key, iv),
            Sm4Cfb128Decryptor::decrypt,
            Sm4Cfb128Decryptor::decrypt_final,
        );
    }
}

/// The examples in place, at every offset of the data, leave the bytes
/// around them unchanged.
#[test]
fn feedback_buffers_unaligned() {
    for (key, iv, plaintext, ciphertext) in examples() {
        crate::modes::check_unaligned(
            iv,
            (&plaintext, &ciphertext),
            &|iv| Sm4Cfb128Encryptor::new(&key, iv),
            Sm4Cfb128Encryptor::encrypt_final,
        );
        crate::modes::check_unaligned(
            iv,
            (&ciphertext, &plaintext),
            &|iv| Sm4Cfb128Decryptor::new(&key, iv),
            Sm4Cfb128Decryptor::decrypt_final,
        );
    }
}

/// Many blocks at once, at lengths around multiples of sixteen blocks (the
/// groups decryption enciphers together), agree with one at a time and with
/// the message decrypted in two pieces, and encryption undoes decryption.
#[test]
fn batches() {
    // Generated inputs test agreement between lengths, not known answers.
    let (key, iv) = ([7; 16], [9; 16]);
    let input = crate::bytes::pattern(16 * 50, 1, 0);
    for blocks in [1, 15, 16, 17, 31, 32, 33, 50] {
        let input = &input[..16 * blocks];
        let mut whole = input.to_vec();
        Sm4Cfb128Decryptor::new(&key, &iv)
            .decrypt(&mut whole)
            .unwrap();
        let mut single = input.to_vec();
        let mut decryptor = Sm4Cfb128Decryptor::new(&key, &iv);
        for block in single.chunks_mut(16) {
            decryptor.decrypt(block).unwrap();
        }
        assert_eq!(whole, single);
        Sm4Cfb128Encryptor::new(&key, &iv)
            .encrypt(&mut whole)
            .unwrap();
        assert_eq!(whole, input);
        let mut rest = input.to_vec();
        let mut decryptor = Sm4Cfb128Decryptor::new(&key, &iv);
        decryptor.decrypt(&mut rest[..16 * blocks - 16]).unwrap();
        decryptor.decrypt_final(&mut rest[16 * blocks - 16..]);
        assert_eq!(rest, single);
    }
}
