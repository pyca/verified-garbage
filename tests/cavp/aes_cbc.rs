//! NIST CAVP AES-CBC known-answer (KAT) and multi-block message (MMT)
//! vectors, with unmodified sources under vectors/.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::aes_cbc::{AesCbcDecryptor, AesCbcEncryptor, Error};

use verified_garbage_test_vectors::{cavp_records, unhex};

/// Encrypts (or decrypts) `buffer` with `key` from `iv`, in the pieces
/// `lens` gives (the rest in a last piece), each a whole number of blocks.
fn run(key: &[u8], iv: &[u8; 16], encrypt: bool, buffer: &mut [u8], lens: &[usize]) {
    let mut encryptor = AesCbcEncryptor::new(key, iv).unwrap();
    let mut decryptor = AesCbcDecryptor::new(key, iv).unwrap();
    let mut rest = buffer;
    for &len in lens.iter().chain([&usize::MAX]) {
        let (piece, tail) = rest.split_at_mut(len.min(rest.len()));
        if encrypt {
            encryptor.encrypt(piece).unwrap();
        } else {
            decryptor.decrypt(piece).unwrap();
        }
        rest = tail;
    }
}

/// Checks a vector in both directions, in one call; with `split`, also in
/// two calls split at each block boundary (after an empty one) and one call
/// per block, each continuing the message, and in one call at every
/// alignment, with guards around the output.
fn check(key: &[u8], iv: &[u8], plaintext: &[u8], ciphertext: &[u8], split: bool) {
    assert_eq!(plaintext.len(), ciphertext.len());
    let iv: [u8; 16] = iv.try_into().unwrap();
    for (encrypt, input, expected) in [
        (true, plaintext, ciphertext),
        (false, ciphertext, plaintext),
    ] {
        let mut output = input.to_vec();
        run(key, &iv, encrypt, &mut output, &[]);
        assert_eq!(output, expected);
        if split {
            for offset in 0..16 {
                let mut storage = vec![0xa5; offset + input.len() + 16];
                storage[offset..offset + input.len()].copy_from_slice(input);
                run(
                    key,
                    &iv,
                    encrypt,
                    &mut storage[offset..offset + input.len()],
                    &[],
                );
                assert_eq!(&storage[offset..offset + input.len()], expected);
                assert!(crate::bytes::all_equal(&storage[..offset], 0xa5));
                assert!(crate::bytes::all_equal(
                    &storage[offset + input.len()..],
                    0xa5
                ));
            }
            for offset in (0..=input.len()).step_by(16) {
                let mut output = input.to_vec();
                run(key, &iv, encrypt, &mut output, &[0, offset]);
                assert_eq!(output, expected);
            }
            let mut output = input.to_vec();
            run(key, &iv, encrypt, &mut output, &vec![16; input.len() / 16]);
            assert_eq!(output, expected);
        }
    }
}

/// Checks every vector of a response file, and returns how many there were.
fn check_file(text: &str, split: bool) -> usize {
    let mut count = 0;
    for fields in cavp_records(text) {
        check(
            &unhex(fields["KEY"]),
            &unhex(fields["IV"]),
            &unhex(fields["PLAINTEXT"]),
            &unhex(fields["CIPHERTEXT"]),
            split,
        );
        count += 1;
    }
    count
}

#[test]
fn nist_cbc() {
    let files = [
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cbc/CBCGFSbox128.rsp"),
            14,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cbc/CBCGFSbox192.rsp"),
            12,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cbc/CBCGFSbox256.rsp"),
            10,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cbc/CBCKeySbox128.rsp"),
            42,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cbc/CBCKeySbox192.rsp"),
            48,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cbc/CBCKeySbox256.rsp"),
            32,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cbc/CBCVarKey128.rsp"),
            256,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cbc/CBCVarKey192.rsp"),
            384,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cbc/CBCVarKey256.rsp"),
            512,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cbc/CBCVarTxt128.rsp"),
            256,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cbc/CBCVarTxt192.rsp"),
            256,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cbc/CBCVarTxt256.rsp"),
            256,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-mmt/CBCMMT128.rsp"),
            20,
            true,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-mmt/CBCMMT192.rsp"),
            20,
            true,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-mmt/CBCMMT256.rsp"),
            20,
            true,
        ),
    ];
    let mut total = 0;
    for (text, expected, split) in files {
        let count = check_file(text, split);
        assert_eq!(count, expected);
        total += count;
    }
    assert_eq!(total, 2138);
}

#[test]
fn limits_and_empty_input() {
    let iv = [0x3c; 16];
    for len in 0..=40 {
        let key: Vec<_> = crate::bytes::pattern(len, 17, 3);
        if !matches!(len, 16 | 24 | 32) {
            assert!(matches!(
                AesCbcEncryptor::new(&key, &iv),
                Err(Error::InvalidKeyLength)
            ));
            assert!(matches!(
                AesCbcDecryptor::new(&key, &iv),
                Err(Error::InvalidKeyLength)
            ));
            continue;
        }
        let mut encryptor = AesCbcEncryptor::new(&key, &iv).unwrap();
        let mut decryptor = AesCbcDecryptor::new(&key, &iv).unwrap();
        encryptor.encrypt(&mut []).unwrap();
        decryptor.decrypt(&mut []).unwrap();
        for n in 1usize..48 {
            if n.is_multiple_of(16) {
                continue;
            }
            let mut buffer = vec![0x5a; n];
            assert_eq!(encryptor.encrypt(&mut buffer), Err(Error::IncompleteBlock));
            assert_eq!(buffer, vec![0x5a; n]);
            assert_eq!(decryptor.decrypt(&mut buffer), Err(Error::IncompleteBlock));
            assert_eq!(buffer, vec![0x5a; n]);
        }
        // The calls before changed nothing: many blocks in one call encrypt
        // as from a new encryptor, equal blocks to different blocks, and
        // round-trip; and a further call continues the message.
        let mut buffer = vec![0xa5; 16 * 67];
        encryptor.encrypt(&mut buffer).unwrap();
        let mut whole = vec![0xa5; 16 * 68];
        run(&key, &iv, true, &mut whole, &[]);
        assert_eq!(buffer, whole[..16 * 67]);
        assert!(buffer.chunks(16).skip(1).all(|b| b != &buffer[..16]));
        let mut last = [0xa5; 16];
        encryptor.encrypt(&mut last).unwrap();
        assert_eq!(last, whole[16 * 67..]);
        decryptor.decrypt(&mut buffer).unwrap();
        assert_eq!(buffer, vec![0xa5; 16 * 67]);
    }
}
