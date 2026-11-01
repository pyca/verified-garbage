//! SM4-GCM against RFC 8998's example and a reference GCM over SM4-ECB.

use verified_garbage::sm4_ecb::Sm4Ecb;
use verified_garbage::sm4_gcm::{Error, Sm4Gcm};

fn unhex(text: &str) -> Vec<u8> {
    let hex: String = text.chars().filter(|c| !c.is_whitespace()).collect();
    assert_eq!(hex.len() % 2, 0);
    (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).unwrap())
        .collect()
}

/// The value of the field `label` of Appendix A.1: the hex after `label:`,
/// and on the lines after it that hold nothing but hex.
fn field(label: &str) -> Vec<u8> {
    let text = crate::vectors::text("vectors/rfc8998/rfc8998.txt");
    let section = text
        .split("\nA.1.  SM4-GCM Test Vectors\n")
        .nth(1)
        .unwrap()
        .split("\nA.2.  SM4-CCM Test Vectors\n")
        .next()
        .unwrap();
    let mut lines = section.lines();
    let first = lines
        .by_ref()
        .find_map(|line| line.trim().strip_prefix(label)?.strip_prefix(':'))
        .unwrap();
    let mut hex = first.to_string();
    for line in lines {
        let line = line.trim();
        if line.is_empty() || !line.chars().all(|c| c.is_ascii_hexdigit()) {
            break;
        }
        hex.push_str(line);
    }
    unhex(&hex)
}

struct Example {
    key: [u8; 16],
    nonce: Vec<u8>,
    aad: Vec<u8>,
    plaintext: Vec<u8>,
    ciphertext: Vec<u8>,
    tag: [u8; 16],
}

fn example() -> Example {
    let e = Example {
        key: field("Key").try_into().unwrap(),
        nonce: field("Initialization Vector"),
        aad: field("Associated Data"),
        plaintext: field("Plaintext"),
        ciphertext: field("CipherText"),
        tag: field("Authentication Tag").try_into().unwrap(),
    };
    assert_eq!(
        (e.nonce.len(), e.aad.len(), e.plaintext.len()),
        (12, 20, 64)
    );
    assert_eq!(e.ciphertext.len(), 64);
    e
}

#[test]
fn rfc8998_example() {
    let e = example();
    let key = Sm4Gcm::new(&e.key);
    let mut data = e.plaintext.clone();
    assert_eq!(key.encrypt_in_place(&e.nonce, &e.aad, &mut data), Ok(e.tag));
    assert_eq!(data, e.ciphertext);
    assert_eq!(
        key.decrypt_in_place(&e.nonce, &e.aad, &mut data, &e.tag),
        Ok(())
    );
    assert_eq!(data, e.plaintext);
    // A truncated tag is the first bytes of the full one.
    let mut data = e.ciphertext.clone();
    let short: [u8; 12] = e.tag[..12].try_into().unwrap();
    assert_eq!(
        key.decrypt_in_place_truncated(&e.nonce, &e.aad, &mut data, &short),
        Ok(())
    );
    assert_eq!(data, e.plaintext);
}

#[test]
fn rfc8998_example_rejects_changes() {
    let e = example();
    let key = Sm4Gcm::new(&e.key);
    let reject = |nonce: &[u8], aad: &[u8], ct: &[u8], tag: &[u8; 16]| {
        let mut data = ct.to_vec();
        assert_eq!(
            key.decrypt_in_place(nonce, aad, &mut data, tag),
            Err(Error::TagMismatch)
        );
        // The data is left as it was.
        assert_eq!(data, ct);
        let mut d = key.decryptor(nonce).unwrap();
        d.update_aad(aad).unwrap();
        let mut data = ct.to_vec();
        d.update(&mut data).unwrap();
        assert_eq!(d.finalize(tag), Err(Error::TagMismatch));
    };
    let flip = |x: &[u8], i: usize| {
        let mut y = x.to_vec();
        y[i] ^= 1;
        y
    };
    let mut tag = e.tag;
    tag[15] ^= 0x80;
    reject(&e.nonce, &e.aad, &e.ciphertext, &tag);
    reject(&e.nonce, &e.aad, &flip(&e.ciphertext, 0), &e.tag);
    reject(&e.nonce, &e.aad, &flip(&e.ciphertext, 63), &e.tag);
    reject(&e.nonce, &flip(&e.aad, 19), &e.ciphertext, &e.tag);
    reject(&flip(&e.nonce, 11), &e.aad, &e.ciphertext, &e.tag);
    reject(&e.nonce, &e.aad[..19], &e.ciphertext, &e.tag);
    reject(&e.nonce, &e.aad, &e.ciphertext[..63], &e.tag);
    let mut truncated = [0; 4];
    truncated.copy_from_slice(&e.tag[..4]);
    truncated[3] ^= 1;
    let mut data = e.ciphertext.clone();
    assert_eq!(
        key.decrypt_in_place_truncated(&e.nonce, &e.aad, &mut data, &truncated),
        Err(Error::TagMismatch)
    );
}

/// The example in two pieces of additional data and three of text, split at
/// every pair of points.
#[test]
fn rfc8998_example_in_pieces() {
    let e = example();
    let key = Sm4Gcm::new(&e.key);
    for a in 0..=e.aad.len() {
        for (i, j) in [
            (0, 0),
            (1, 17),
            (15, 16),
            (16, 48),
            (31, 33),
            (64, 64),
            (5, 64),
        ] {
            let mut enc = key.encryptor(&e.nonce).unwrap();
            enc.update_aad(&e.aad[..a]).unwrap();
            enc.update_aad(&e.aad[a..]).unwrap();
            let mut data = e.plaintext.clone();
            let (x, rest) = data.split_at_mut(i);
            let (y, z) = rest.split_at_mut(j - i);
            enc.update(x).unwrap();
            enc.update(y).unwrap();
            enc.update(z).unwrap();
            assert_eq!(enc.update_aad(b""), Err(Error::AadAfterText));
            assert_eq!(enc.finalize(), e.tag);
            assert_eq!(data, e.ciphertext);
            let mut dec = key.decryptor(&e.nonce).unwrap();
            dec.update_aad(&e.aad[..a]).unwrap();
            dec.update_aad(&e.aad[a..]).unwrap();
            let (x, rest) = data.split_at_mut(i);
            let (y, z) = rest.split_at_mut(j - i);
            dec.update(x).unwrap();
            dec.update(y).unwrap();
            dec.update(z).unwrap();
            assert_eq!(dec.update_aad(b""), Err(Error::AadAfterText));
            assert_eq!(
                dec.clone()
                    .finalize_truncated::<8>(&e.tag[..8].try_into().unwrap()),
                Ok(())
            );
            assert_eq!(dec.finalize(&e.tag), Ok(()));
            assert_eq!(data, e.plaintext);
        }
    }
}

/// GF(2¹²⁸) multiplication, SP 800-38D §6.3 Algorithm 1, bit by bit.
fn mul(x: u128, y: u128) -> u128 {
    let r = 0xE1u128 << 120;
    let (mut z, mut v) = (0u128, y);
    for i in 0..128 {
        if (x >> (127 - i)) & 1 == 1 {
            z ^= v;
        }
        v = if v & 1 == 1 { (v >> 1) ^ r } else { v >> 1 };
    }
    z
}

/// GHASH (§6.4) of `data` padded with zeros to whole blocks.
fn ghash(h: u128, y: u128, data: &[u8]) -> u128 {
    data.chunks(16).fold(y, |y, c| {
        let mut b = [0; 16];
        b[..c.len()].copy_from_slice(c);
        mul(y ^ u128::from_be_bytes(b), h)
    })
}

/// GCM-AE (§7.1) over SM4-ECB, from the definitions.
fn reference(key: &[u8; 16], nonce: &[u8], aad: &[u8], pt: &[u8]) -> (Vec<u8>, [u8; 16]) {
    let ecb = Sm4Ecb::new(key);
    let ciph = |x: u128| {
        let mut b = x.to_be_bytes();
        ecb.encrypt(&mut b).unwrap();
        u128::from_be_bytes(b)
    };
    let h = ciph(0);
    let j0 = if nonce.len() == 12 {
        let mut b = [0; 16];
        b[..12].copy_from_slice(nonce);
        b[15] = 1;
        u128::from_be_bytes(b)
    } else {
        ghash(
            h,
            ghash(h, 0, nonce),
            &(8 * nonce.len() as u128).to_be_bytes(),
        )
    };
    let inc32 = |x: u128, k: u32| (x & !0xFFFF_FFFF) | (x as u32).wrapping_add(k) as u128;
    let ct: Vec<u8> = pt
        .chunks(16)
        .enumerate()
        .flat_map(|(i, c)| {
            let ks = ciph(inc32(j0, i as u32 + 1)).to_be_bytes();
            c.iter().zip(ks).map(|(x, k)| x ^ k).collect::<Vec<_>>()
        })
        .collect();
    let lens = ((8 * aad.len() as u128) << 64) | (8 * ct.len() as u128);
    let s = mul(ghash(h, ghash(h, 0, aad), &ct) ^ lens, h);
    (ct, (s ^ ciph(j0)).to_be_bytes())
}

/// Bytes that are not a pattern.
fn bytes(seed: u8, n: usize) -> Vec<u8> {
    (0..n)
        .map(|i| {
            (i as u32)
                .wrapping_mul(2654435761)
                .wrapping_add(seed as u32)
                .to_be_bytes()[0]
        })
        .collect()
}

fn check(key: &Sm4Gcm, k: &[u8; 16], nonce: &[u8], aad: &[u8], pt: &[u8]) {
    let (ct, tag) = reference(k, nonce, aad, pt);
    let mut data = pt.to_vec();
    assert_eq!(key.encrypt_in_place(nonce, aad, &mut data), Ok(tag));
    assert_eq!(data, ct);
    assert_eq!(key.decrypt_in_place(nonce, aad, &mut data, &tag), Ok(()));
    assert_eq!(data, pt);
}

/// Every nonce length up to 33 bytes, every length of additional data and
/// text up to 3 blocks and more, against the reference.
#[test]
fn against_reference() {
    let k: [u8; 16] = bytes(1, 16).try_into().unwrap();
    let key = Sm4Gcm::new(&k);
    for nonce_len in 1..=33 {
        check(&key, &k, &bytes(2, nonce_len), &bytes(3, 21), &bytes(4, 37));
    }
    for aad_len in 0..=50 {
        for text_len in (0..=50).chain([63, 64, 65, 255, 256, 257, 4095, 4096, 4097, 4129]) {
            check(
                &key,
                &k,
                &bytes(5, 12),
                &bytes(6, aad_len),
                &bytes(7, text_len),
            );
        }
    }
    // Several chunks of counter mode and GHASH, unaligned.
    let long = bytes(8, 70_001);
    check(&key, &k, &bytes(9, 12), &bytes(10, 3), &long);
    check(&key, &k, &bytes(9, 7), &bytes(10, 3), &long[1..]);
}

/// A long text in pieces of every length up to 40 bytes, against the
/// reference.
#[test]
fn pieces_against_reference() {
    let k: [u8; 16] = bytes(11, 16).try_into().unwrap();
    let key = Sm4Gcm::new(&k);
    let nonce = bytes(12, 16);
    let aad = bytes(13, 29);
    let pt = bytes(14, 9000);
    let (ct, tag) = reference(&k, &nonce, &aad, &pt);
    for step in 1..=40 {
        let mut enc = key.encryptor(&nonce).unwrap();
        for piece in aad.chunks(step) {
            enc.update_aad(piece).unwrap();
        }
        let mut data = pt.clone();
        for (i, piece) in data.chunks_mut(step * 97 % 5000 + step).enumerate() {
            // Pieces of the step's length and a long one in turn.
            let (a, b) = piece.split_at_mut(piece.len().min(step + i % 3));
            enc.update(a).unwrap();
            enc.update(b).unwrap();
        }
        assert_eq!(enc.finalize(), tag);
        assert_eq!(data, ct);
        let mut dec = key.decryptor(&nonce).unwrap();
        dec.update_aad(&aad).unwrap();
        for piece in data.chunks_mut(step) {
            dec.update(piece).unwrap();
        }
        assert_eq!(dec.finalize(&tag), Ok(()));
        assert_eq!(data, pt);
    }
}

/// An empty nonce is an error; empty messages have tags.
#[test]
fn nonces_and_empty_messages() {
    let k = [0x5a; 16];
    let key = Sm4Gcm::new(&k);
    assert_eq!(
        key.encrypt_in_place(&[], &[], &mut []),
        Err(Error::InvalidNonceLength)
    );
    assert_eq!(
        key.decrypt_in_place(&[], &[], &mut [], &[0; 16]),
        Err(Error::InvalidNonceLength)
    );
    assert!(key.encryptor(&[]).is_err());
    assert!(key.decryptor(&[]).is_err());
    let (_, tag) = reference(&k, &[1], &[], &[]);
    assert_eq!(key.encryptor(&[1]).unwrap().finalize(), tag);
    assert_eq!(key.decryptor(&[1]).unwrap().finalize(&tag), Ok(()));
    assert_eq!(Error::TagMismatch.to_string(), "SM4-GCM tag does not match");
}
