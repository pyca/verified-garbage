//! SM4-GCM on RFC 8998's example; Wycheproof's vectors are in
//! `tests/wycheproof/sm4_gcm.rs`.

use verified_garbage::sm4_gcm::{Error, Sm4Gcm};
use verified_garbage_test_vectors::unhex_spaced;

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
    unhex_spaced(&hex)
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

/// An empty nonce is an error; an empty message has a tag, the same
/// streaming as at once.
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
    let tag = key.encrypt_in_place(&[1], &[], &mut []).unwrap();
    assert_eq!(key.encryptor(&[1]).unwrap().finalize(), tag);
    assert_eq!(key.decrypt_in_place(&[1], &[], &mut [], &tag), Ok(()));
    assert_eq!(key.decryptor(&[1]).unwrap().finalize(&tag), Ok(()));
    assert_eq!(Error::TagMismatch.to_string(), "SM4-GCM tag does not match");
}
