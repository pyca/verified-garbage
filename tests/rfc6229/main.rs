//! RC4: all RFC 6229 §2 answers, read from the byte-for-byte vendored RFC,
//! whole and streaming; and round trips under keys of the lengths it has
//! none of.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::rc4::{Error, Rc4};
use verified_garbage_test_vectors::unhex_spaced;

#[test]
fn every_published_answer_and_streaming_split() {
    let mut keys = 0;
    let mut answers = 0;
    for record in crate::vectors::text("vectors/rfc6229/rfc6229.txt")
        .split(" Key length: ")
        .skip(1)
    {
        let bits: usize = record.split_once(" bits.").unwrap().0.parse().unwrap();
        let key = record
            .lines()
            .find_map(|line| line.trim().strip_prefix("key: 0x"))
            .map(unhex_spaced)
            .unwrap();
        assert_eq!(bits, key.len() * 8);
        let mut stream = vec![0; 4112];
        let mut cipher = Rc4::new(&key).unwrap();
        cipher.apply_keystream(&mut []);
        cipher.apply_keystream(&mut stream);
        cipher.apply_keystream(&mut []);
        cipher.finalize();
        let mut count = 0;
        for line in record.lines().map(str::trim) {
            if !line.starts_with("DEC") {
                continue;
            }
            let (position, bytes) = line.split_once(':').unwrap();
            let offset: usize = position.split_whitespace().nth(1).unwrap().parse().unwrap();
            let expected = unhex_spaced(bytes);
            assert_eq!(expected.len(), 16);
            assert_eq!(&stream[offset..offset + 16], expected);
            let mut cipher = Rc4::new(&key).unwrap();
            let mut skipped = vec![0; offset];
            cipher.apply_keystream(&mut skipped);
            let mut decrypted = expected;
            cipher.apply_keystream(&mut decrypted);
            assert_eq!(decrypted, [0; 16]);
            count += 1;
        }
        assert_eq!(count, 18);
        for split in 0..=32 {
            let mut actual = [0; 32];
            let mut cipher = Rc4::new(&key).unwrap();
            cipher.apply_keystream(&mut actual[..split]);
            cipher.apply_keystream(&mut []);
            cipher.apply_keystream(&mut actual[split..]);
            assert_eq!(actual, stream[..32]);
        }
        for split in [0, 1, 255, 256, 257, 4096, 4112] {
            let mut actual = vec![0; stream.len()];
            let mut cipher = Rc4::new(&key).unwrap();
            cipher.apply_keystream(&mut actual[..split]);
            cipher.apply_keystream(&mut []);
            cipher.apply_keystream(&mut actual[split..]);
            assert_eq!(actual, stream);
        }
        let mut actual = vec![0; stream.len()];
        let mut cipher = Rc4::new(&key).unwrap();
        for byte in &mut actual {
            cipher.apply_keystream(core::slice::from_mut(byte));
        }
        assert_eq!(actual, stream);
        keys += 1;
        answers += count;
    }
    assert_eq!(keys, 14);
    assert_eq!(answers, 252);
}

/// Keys outside 1–256 bytes are errors; under keys of lengths RFC 6229 has
/// none of (1, 2, 255 and 256 bytes), decryption in pieces undoes
/// encryption.
#[test]
fn key_lengths_and_round_trips() {
    assert_eq!(Rc4::new(&[]).err(), Some(Error::InvalidKeyLength));
    assert_eq!(Rc4::new(&[0; 257]).err(), Some(Error::InvalidKeyLength));
    for length in [1, 2, 255, 256] {
        let key: Vec<u8> = crate::bytes::pattern(length, 37, 0);
        let original: Vec<u8> = crate::bytes::pattern(513, 19, 7);
        let mut data = original.clone();
        let mut cipher = Rc4::new(&key).unwrap();
        cipher.apply_keystream(&mut data);
        assert_ne!(data, original);
        let mut cipher = Rc4::new(&key).unwrap();
        for chunk in data.chunks_mut(17) {
            cipher.apply_keystream(chunk);
        }
        assert_eq!(data, original);
        cipher.finalize();
    }
}
