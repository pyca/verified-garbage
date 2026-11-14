//! Published RC2 vectors; unmodified sources and provenance live under vectors/.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "arm",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use verified_garbage::cipher::rc2::{Error, Rc2CbcDecryptor, Rc2CbcEncryptor};
use verified_garbage::error::{IncompleteBlock, InvalidKeyLength};

use verified_garbage_test_vectors::{Record, unhex};

/// What [`Rc2CbcEncryptor`] and [`Rc2CbcDecryptor`] both have, so that
/// each test runs in both directions.
trait Cbc: Sized {
    fn new(key: &[u8], iv: &[u8; 8]) -> Result<Self, InvalidKeyLength>;
    fn with_bits(key: &[u8], iv: &[u8; 8], bits: usize) -> Result<Self, Error>;
    fn crypt(&mut self, buffer: &mut [u8]) -> Result<(), IncompleteBlock>;
}

macro_rules! cbc {
    ($t:ty, $crypt:ident) => {
        impl Cbc for $t {
            fn new(key: &[u8], iv: &[u8; 8]) -> Result<Self, InvalidKeyLength> {
                <$t>::new(key, iv)
            }
            fn with_bits(key: &[u8], iv: &[u8; 8], bits: usize) -> Result<Self, Error> {
                <$t>::new_with_effective_bits(key, iv, bits)
            }
            fn crypt(&mut self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
                <$t>::$crypt(self, buffer)
            }
        }
    };
}
cbc!(Rc2CbcEncryptor, encrypt);
cbc!(Rc2CbcDecryptor, decrypt);

/// Rejected partial blocks preserve the buffer and the chaining state;
/// the caller then continues checking the published answer.
fn reject_partial<C: Cbc>(ctx: &mut C) {
    for len in [1, 7, 9, 15, 1025] {
        let mut invalid = vec![0xa5; len];
        assert_eq!(ctx.crypt(&mut invalid), Err(IncompleteBlock));
        assert_eq!(invalid, vec![0xa5; len]);
    }
}

/// Check every block boundary, unaligned buffers, empty calls, and rejected
/// partial blocks both before and after processing part of the message.
fn check_one<C: Cbc>(key: &[u8], iv: &[u8; 8], bits: usize, input: &[u8], expected: &[u8]) {
    for offset in 0..8 {
        for split in (0..=input.len()).step_by(8) {
            let mut ctx = C::with_bits(key, iv, bits).unwrap();
            let mut storage = vec![0xa5; offset + input.len() + 1];
            storage[offset..offset + input.len()].copy_from_slice(input);
            let buffer = &mut storage[offset..offset + input.len()];
            reject_partial(&mut ctx);
            ctx.crypt(&mut []).unwrap();
            ctx.crypt(&mut buffer[..split]).unwrap();
            reject_partial(&mut ctx);
            ctx.crypt(&mut []).unwrap();
            ctx.crypt(&mut buffer[split..]).unwrap();
            assert_eq!(buffer, expected);
            assert!(storage[..offset].iter().all(|&b| b == 0xa5));
            assert_eq!(storage[offset + input.len()], 0xa5);
        }
    }
}

fn check(key: &[u8], iv: &[u8; 8], bits: usize, plaintext: &[u8], ciphertext: &[u8]) {
    assert_eq!(plaintext.len(), ciphertext.len());
    check_one::<Rc2CbcEncryptor>(key, iv, bits, plaintext, ciphertext);
    check_one::<Rc2CbcDecryptor>(key, iv, bits, ciphertext, plaintext);
}

#[test]
fn rfc2268() {
    let text = crate::vectors::text("vectors/rfc2268/rfc2268.txt");
    let excerpt = text
        .split("5. Test vectors")
        .nth(1)
        .unwrap()
        .split("6. RC2 Algorithm Object Identifier")
        .next()
        .unwrap();
    let mut count = 0;
    for record in excerpt.split("   Key length (bytes) = ").skip(1) {
        let f = Record::parse(record);
        let key_lines = record.split("   Key = ").nth(1).unwrap();
        let mut lines = key_lines.lines();
        let mut key_hex = lines.next().unwrap().to_owned();
        for line in lines.take_while(|line| line.starts_with("         ")) {
            key_hex.push_str(line.trim());
        }
        let key = unhex(&key_hex.replace(' ', ""));
        assert_eq!(
            key.len(),
            record
                .lines()
                .next()
                .unwrap()
                .trim()
                .parse::<usize>()
                .unwrap()
        );
        let bits = f["Effective key length (bits)"].parse().unwrap();
        // A single CBC block with a zero IV is exactly the RFC's block-cipher operation.
        check(
            &key,
            &[0; 8],
            bits,
            &unhex(&f["Plaintext"].replace(' ', "")),
            &unhex(&f["Ciphertext"].replace(' ', "")),
        );
        count += 1;
    }
    assert_eq!(count, 8);
}

#[test]
fn openssl_cbc() {
    let text = crate::vectors::text("vectors/openssl-rc2/evpciph_rc2.txt");
    let mut count = 0;
    for record in text.split("\n\n") {
        let f = Record::parse(record);
        let Some(cipher) = f.get("Cipher").filter(|name| name.ends_with("CBC")) else {
            continue;
        };
        let default_bits = match cipher {
            "RC2-40-CBC" => 40,
            "RC2-64-CBC" => 64,
            name => {
                assert_eq!(name, "RC2-CBC");
                128
            }
        };
        let bits = f
            .get("KeyBits")
            .map_or(default_bits, |value| value.parse().unwrap());
        check(
            &unhex(f["Key"]),
            &unhex(f["IV"]).try_into().unwrap(),
            bits,
            &unhex(f["Plaintext"]),
            &unhex(f["Ciphertext"]),
        );
        count += 1;
    }
    assert_eq!(count, 7);
}

#[test]
fn cryptography_cbc_and_default_bits() {
    let text = crate::vectors::text("vectors/cryptography-rc2/rc2-cbc.txt");
    let f = Record::parse(&text);
    let key = unhex(f["Key"]);
    let iv: [u8; 8] = unhex(f["IV"]).try_into().unwrap();
    let plaintext = unhex(f["Plaintext"]);
    let ciphertext = unhex(f["Ciphertext"]);
    check(&key, &iv, 128, &plaintext, &ciphertext);
    let mut output = plaintext.clone();
    Rc2CbcEncryptor::new(&key, &iv)
        .unwrap()
        .encrypt(&mut output)
        .unwrap();
    assert_eq!(output, ciphertext);
    Rc2CbcDecryptor::new(&key, &iv)
        .unwrap()
        .decrypt(&mut output)
        .unwrap();
    assert_eq!(output, plaintext);
}

fn invalid_parameters_of<C: Cbc>() {
    let key = [0; 16];
    let iv = [0; 8];
    for key in [&[][..], &[0; 129][..]] {
        assert_eq!(C::new(key, &iv).err(), Some(InvalidKeyLength));
        assert_eq!(
            C::with_bits(key, &iv, 128).err(),
            Some(Error::InvalidKeyLength)
        );
    }
    for bits in [0, 1025, usize::MAX] {
        assert_eq!(
            C::with_bits(&key, &iv, bits).err(),
            Some(Error::InvalidEffectiveBits)
        );
    }
}

#[test]
fn invalid_parameters() {
    invalid_parameters_of::<Rc2CbcEncryptor>();
    invalid_parameters_of::<Rc2CbcDecryptor>();
}

#[test]
fn boundary_key_sizes_roundtrip() {
    // Generated inputs test round trips, not published known answers.
    let input = crate::bytes::pattern(2056, 1, 0);
    for len in [1, 8, 128] {
        let key: Vec<u8> = crate::bytes::pattern(len, 1, 0);
        for bits in [1, 7, 8, 9, 63, 64, 65, 1023, 1024] {
            let mut ciphertext = input.clone();
            let mut enc = Rc2CbcEncryptor::new_with_effective_bits(&key, &[1; 8], bits).unwrap();
            enc.encrypt(&mut ciphertext).unwrap();
            let mut pieces = input.clone();
            let mut enc = Rc2CbcEncryptor::new_with_effective_bits(&key, &[1; 8], bits).unwrap();
            for block in pieces.chunks_mut(8) {
                enc.encrypt(block).unwrap();
            }
            assert_eq!(pieces, ciphertext);
            let mut plaintext = ciphertext;
            let mut dec = Rc2CbcDecryptor::new_with_effective_bits(&key, &[1; 8], bits).unwrap();
            dec.decrypt(&mut plaintext).unwrap();
            assert_eq!(plaintext[..], input[..]);
        }
    }
}
