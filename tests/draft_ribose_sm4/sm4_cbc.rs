//! SM4-CBC: the CBC examples (A.2.2) of the Internet-Draft
//! draft-ribose-cfrg-sm4-10, unmodified under vectors/, whole, in pieces,
//! and in place in unaligned buffers; and, since each is two blocks and
//! decryption deciphers many blocks at a time, messages of up to 34 blocks,
//! which decryption takes back to what was encrypted.

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

/// Every number of blocks up to 34 round-trips: decryption, which deciphers
/// many blocks at a time, undoes encryption, in one call in place
/// between guards, and with the last block in a call of its own.
#[test]
fn round_trips() {
    let iv = [0x3c; 16];
    let key: [u8; 16] = crate::bytes::pattern(16, 17, 3).try_into().unwrap();
    let message: Vec<_> = crate::bytes::pattern(16 * 34, 7, 1);
    for blocks in 0..=34 {
        let n = 16 * blocks;
        let mut buffer = message[..n].to_vec();
        Sm4CbcEncryptor::new(&key, &iv)
            .encrypt(&mut buffer)
            .unwrap();
        let mut guarded = vec![0xa5; 1 + n + 16];
        guarded[1..1 + n].copy_from_slice(&buffer);
        Sm4CbcDecryptor::new(&key, &iv)
            .decrypt(&mut guarded[1..1 + n])
            .unwrap();
        assert_eq!(guarded[1..1 + n], message[..n]);
        assert!(crate::bytes::all_equal(&guarded[..1], 0xa5));
        assert!(crate::bytes::all_equal(&guarded[1 + n..], 0xa5));
        let mut decryptor = Sm4CbcDecryptor::new(&key, &iv);
        let (head, last) = buffer.split_at_mut(n.saturating_sub(16));
        decryptor.decrypt(head).unwrap();
        decryptor.decrypt(last).unwrap();
        assert_eq!(buffer, message[..n]);
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
