//! Blowfish-ECB against Eric Young's test vectors, as Schneier publishes
//! them, read from the byte-for-byte vendored file: every ECB record, every
//! `set_key` record (and the rejection of keys shorter than 32 bits), and
//! the CBC record, chained here a block at a time through ECB. Then ECB of
//! many blocks at once against one block at a time, and the streaming
//! wrapper's splits and errors.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::blowfish_ecb::{BlowfishEcbDecryptor, BlowfishEcbEncryptor, Error};
use verified_garbage_test_vectors::unhex_spaced;

/// The vectors' file (`crate::vectors`).
fn text() -> String {
    crate::vectors::text("vectors/schneier-blowfish-vectors/vectors-2.txt")
}

fn encrypt(key: &[u8], input: &[u8]) -> Vec<u8> {
    let mut cipher = BlowfishEcbEncryptor::new(key).unwrap();
    let mut output = vec![0; input.len()];
    assert_eq!(cipher.update(input, &mut output), Ok(input.len()));
    cipher.finalize().unwrap();
    output
}

fn decrypt(key: &[u8], input: &[u8]) -> Vec<u8> {
    let mut cipher = BlowfishEcbDecryptor::new(key).unwrap();
    let mut output = vec![0; input.len()];
    assert_eq!(cipher.update(input, &mut output), Ok(input.len()));
    cipher.finalize().unwrap();
    output
}

/// The lines of the file after the one starting with `start`, up to the
/// one starting with `end`, trimmed (the file has CRLF line endings).
fn section(start: &str, end: &str) -> Vec<String> {
    text()
        .lines()
        .map(str::trim)
        .skip_while(|line| !line.starts_with(start))
        .skip(1)
        .take_while(|line| !line.starts_with(end))
        .map(str::to_owned)
        .collect()
}

#[test]
fn ecb_records() {
    let mut count = 0;
    for line in section("key bytes", "set_key test data") {
        let fields: Vec<&str> = line.split_whitespace().collect();
        let [key, clear, cipher]: [&str; 3] = fields.try_into().unwrap();
        let (key, clear, cipher) = (unhex_spaced(key), unhex_spaced(clear), unhex_spaced(cipher));
        assert_eq!(encrypt(&key, &clear), cipher);
        assert_eq!(decrypt(&key, &cipher), clear);
        count += 1;
    }
    assert_eq!(count, 34);
}

#[test]
fn set_key_records() {
    let records = section("set_key test data", "chaining mode test data");
    let mut lines = records.into_iter();
    let clear = unhex_spaced(lines.next().unwrap().strip_prefix("data[8]= ").unwrap());
    let mut count = 0;
    for line in lines.filter(|line| !line.is_empty()) {
        let (cipher, key) = line.strip_prefix("c=").unwrap().split_once(" k[").unwrap();
        let (length, key) = key.split_once("]=").unwrap();
        let length: usize = length.trim().parse().unwrap();
        let (cipher, key) = (unhex_spaced(cipher), unhex_spaced(key));
        assert_eq!(key.len(), length);
        if length < 4 {
            assert!(matches!(
                BlowfishEcbEncryptor::new(&key),
                Err(Error::InvalidKeyLength)
            ));
            assert!(matches!(
                BlowfishEcbDecryptor::new(&key),
                Err(Error::InvalidKeyLength)
            ));
        } else {
            assert_eq!(encrypt(&key, &clear), cipher);
            assert_eq!(decrypt(&key, &cipher), clear);
        }
        count += 1;
    }
    assert_eq!(count, 24);
}

/// The CBC record, through ECB a block at a time: the data, with its
/// trailing zero, is zero-padded to four blocks, as the record's 32 bytes of
/// ciphertext show.
#[test]
fn cbc_record() {
    let text = text();
    let value = |name: &str| {
        let line = text.lines().find(|line| line.starts_with(name)).unwrap();
        unhex_spaced(line.split_once("= ").unwrap().1.trim())
    };
    let key = value("key[16]");
    let iv = value("iv[8]");
    let data = text
        .lines()
        .filter(|line| line.starts_with("data[29]  = 3"))
        .map(|line| unhex_spaced(line.split_once("= ").unwrap().1.trim()))
        .next()
        .unwrap();
    let expected = value("cipher[32]");
    let mut clear = data.clone();
    clear.resize(32, 0);
    let mut encryptor = BlowfishEcbEncryptor::new(&key).unwrap();
    let mut decryptor = BlowfishEcbDecryptor::new(&key).unwrap();
    let mut chain = iv.clone();
    let mut cipher = Vec::new();
    for block in clear.chunks(8) {
        let input: Vec<u8> = crate::bytes::xor(block, &chain);
        let mut output = [0; 8];
        assert_eq!(encryptor.update(&input, &mut output), Ok(8));
        cipher.extend_from_slice(&output);
        chain = output.to_vec();
    }
    assert_eq!(cipher, expected);
    let mut chain = iv;
    let mut decrypted = Vec::new();
    for block in cipher.chunks(8) {
        let mut output = [0; 8];
        assert_eq!(decryptor.update(block, &mut output), Ok(8));
        decrypted.extend(crate::bytes::xor(&output, &chain));
        chain = block.to_vec();
    }
    assert_eq!(decrypted, clear);
    encryptor.finalize().unwrap();
    decryptor.finalize().unwrap();
}

/// Many blocks at once (sixteen at a time, then the rest) match one block
/// at a time, for every count up to past three batches, with the longest
/// key.
#[test]
fn many_blocks() {
    let key: Vec<u8> = crate::bytes::pattern(56, 37, 11);
    let data: Vec<u8> = crate::bytes::pattern(8 * 50, 101, 7);
    let mut single = Vec::new();
    for block in data.chunks(8) {
        single.extend(encrypt(&key, block));
    }
    for n in 0..=50 {
        let cipher = encrypt(&key, &data[..8 * n]);
        assert_eq!(cipher, single[..8 * n]);
        assert_eq!(decrypt(&key, &cipher), data[..8 * n]);
    }
}

/// Updates of every split of the input write the same blocks, and keep a
/// partial block for the next. Each split consumes the whole input, which
/// leaves nothing pending, so one encryptor and one decryptor (one key
/// expansion each, the costliest step) serve every split in turn.
#[test]
fn streaming_splits() {
    let key = unhex_spaced("0123456789ABCDEFF0E1D2C3B4A59687");
    let data: Vec<u8> = crate::bytes::pattern(8 * 20, 13, 5);
    let whole = encrypt(&key, &data);
    let mut cipher = BlowfishEcbEncryptor::new(&key).unwrap();
    let mut decipher = BlowfishEcbDecryptor::new(&key).unwrap();
    for first in 0..=data.len() {
        for second in [0, 1, 7, 8, 9, 23] {
            let second = (first + second).min(data.len());
            let mut output = vec![0; data.len() + 7];
            let mut written = 0;
            for range in [0..first, first..second, second..data.len()] {
                let expected = cipher.output_len(range.len());
                let n = cipher.update(&data[range], &mut output[written..]).unwrap();
                assert_eq!(n, expected);
                written += n;
            }
            assert_eq!(written, data.len());
            assert_eq!(output[..written], whole[..]);
            // Nothing pending, as for a new encryptor.
            assert_eq!(cipher.output_len(7), 0);
            let mut clear = vec![0; data.len() + 7];
            let mut read = 0;
            for range in [0..first, first..second, second..data.len()] {
                let expected = decipher.output_len(range.len());
                let n = decipher.update(&whole[range], &mut clear[read..]).unwrap();
                assert_eq!(n, expected);
                read += n;
            }
            assert_eq!(clear[..read], data[..]);
            assert_eq!(decipher.output_len(7), 0);
        }
    }
    cipher.finalize().unwrap();
    decipher.finalize().unwrap();
}

#[test]
fn errors() {
    for length in [0, 3, 57, 100] {
        assert!(matches!(
            BlowfishEcbEncryptor::new(&vec![1; length]),
            Err(Error::InvalidKeyLength)
        ));
        assert!(matches!(
            BlowfishEcbDecryptor::new(&vec![1; length]),
            Err(Error::InvalidKeyLength)
        ));
    }
    let key = [7; 16];
    let mut cipher = BlowfishEcbEncryptor::new(&key).unwrap();
    let mut output = [0; 15];
    assert_eq!(cipher.update(&[1; 3], &mut []), Ok(0));
    assert_eq!(cipher.output_len(usize::MAX), usize::MAX);
    assert_eq!(
        cipher.update(&[2; 13], &mut output),
        Err(Error::OutputTooSmall)
    );
    assert_eq!(output, [0; 15]);
    assert_eq!(cipher.update(&[2; 13], &mut [0; 16]), Ok(16));
    assert_eq!(cipher.update(&[3; 2], &mut []), Ok(0));
    assert_eq!(cipher.finalize(), Err(Error::IncompleteBlock));
    let mut decipher = BlowfishEcbDecryptor::new(&key).unwrap();
    assert_eq!(
        decipher.update(&[1; 9], &mut [0; 7]),
        Err(Error::OutputTooSmall)
    );
    assert_eq!(decipher.update(&[1; 9], &mut [0; 8]), Ok(8));
    assert_eq!(decipher.finalize(), Err(Error::IncompleteBlock));
}
