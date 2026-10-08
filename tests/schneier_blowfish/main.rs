//! Blowfish-ECB against Eric Young's test vectors, as Schneier publishes
//! them, read from the byte-for-byte vendored file: every ECB record, every
//! `set_key` record (and the rejection of keys shorter than 32 bits), and
//! the CBC record, chained here a block at a time through ECB. Then ECB of
//! many blocks at once against one block at a time, and the streaming
//! wrapper's splits and errors.

#![cfg(target_arch = "aarch64")]

use verified_garbage::blowfish_ecb::{BlowfishEcbDecryptor, BlowfishEcbEncryptor, Error};

const TEXT: &str = include_str!("../../vectors/schneier-blowfish-vectors/vectors-2.txt");

fn unhex(text: &str) -> Vec<u8> {
    let hex: String = text.chars().filter(|c| !c.is_whitespace()).collect();
    assert_eq!(hex.len() % 2, 0);
    (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).unwrap())
        .collect()
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
fn section(start: &str, end: &str) -> Vec<&'static str> {
    TEXT.lines()
        .map(str::trim)
        .skip_while(|line| !line.starts_with(start))
        .skip(1)
        .take_while(|line| !line.starts_with(end))
        .collect()
}

#[test]
fn ecb_records() {
    let mut count = 0;
    for line in section("key bytes", "set_key test data") {
        let fields: Vec<&str> = line.split_whitespace().collect();
        let [key, clear, cipher]: [&str; 3] = fields.try_into().unwrap();
        let (key, clear, cipher) = (unhex(key), unhex(clear), unhex(cipher));
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
    let clear = unhex(lines.next().unwrap().strip_prefix("data[8]= ").unwrap());
    let mut count = 0;
    for line in lines.filter(|line| !line.is_empty()) {
        let (cipher, key) = line.strip_prefix("c=").unwrap().split_once(" k[").unwrap();
        let (length, key) = key.split_once("]=").unwrap();
        let length: usize = length.trim().parse().unwrap();
        let (cipher, key) = (unhex(cipher), unhex(key));
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
    let value = |name: &str| {
        let line = TEXT.lines().find(|line| line.starts_with(name)).unwrap();
        unhex(line.split_once("= ").unwrap().1.trim())
    };
    let key = value("key[16]");
    let iv = value("iv[8]");
    let data = TEXT
        .lines()
        .filter(|line| line.starts_with("data[29]  = 3"))
        .map(|line| unhex(line.split_once("= ").unwrap().1.trim()))
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
        let input: Vec<u8> = block.iter().zip(&chain).map(|(a, b)| a ^ b).collect();
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
        decrypted.extend(output.iter().zip(&chain).map(|(a, b)| a ^ b));
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
    let key: Vec<u8> = (0..56).map(|i| (i * 37 + 11) as u8).collect();
    let data: Vec<u8> = (0..8 * 50).map(|i| (i * 101 + 7) as u8).collect();
    let single: Vec<u8> = data
        .chunks(8)
        .flat_map(|block| encrypt(&key, block))
        .collect();
    for n in 0..=50 {
        let cipher = encrypt(&key, &data[..8 * n]);
        assert_eq!(cipher, single[..8 * n]);
        assert_eq!(decrypt(&key, &cipher), data[..8 * n]);
    }
}

/// Updates of every split of the input write the same blocks, and keep a
/// partial block for the next.
#[test]
fn streaming_splits() {
    let key = unhex("0123456789ABCDEFF0E1D2C3B4A59687");
    let data: Vec<u8> = (0..8 * 20).map(|i| (i * 13 + 5) as u8).collect();
    let whole = encrypt(&key, &data);
    for first in 0..=data.len() {
        for second in [0, 1, 7, 8, 9, 23] {
            let second = (first + second).min(data.len());
            let mut cipher = BlowfishEcbEncryptor::new(&key).unwrap();
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
            cipher.finalize().unwrap();
            let mut decipher = BlowfishEcbDecryptor::new(&key).unwrap();
            let mut clear = vec![0; data.len() + 7];
            let mut read = 0;
            for range in [0..first, first..second, second..data.len()] {
                let expected = decipher.output_len(range.len());
                let n = decipher.update(&whole[range], &mut clear[read..]).unwrap();
                assert_eq!(n, expected);
                read += n;
            }
            assert_eq!(clear[..read], data[..]);
            decipher.finalize().unwrap();
        }
    }
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
