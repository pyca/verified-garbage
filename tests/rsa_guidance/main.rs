//! RSAES-PKCS1-v1_5 decryption with implicit rejection: the test vectors of
//! the vendored draft-irtf-cfrg-rsa-guidance-10, Appendix B (a key of 2048,
//! 2049, 3072 and 4096 bits, each with ciphertexts of valid paddings and of
//! invalid ones, and the message each decrypts to), and encryption with
//! their keys.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use verified_garbage::rsa::{PrivateKey, PublicKey};
use verified_garbage::rsa_pkcs1_enc::{Error, decrypt, encrypt};

const TEXT: &str = include_str!(
    "../../vectors/draft-irtf-cfrg-rsa-guidance-10/draft-irtf-cfrg-rsa-guidance-10.txt"
);

fn unhex(s: &str) -> Vec<u8> {
    assert_eq!(s.len() % 2, 0, "{s}");
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

/// The bytes of the base64 text `s` (with its padding).
fn unbase64(s: &str) -> Vec<u8> {
    const ALPHABET: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut out = Vec::new();
    let (mut acc, mut bits) = (0u32, 0);
    for c in s.bytes().filter(|&c| c != b'=') {
        let v = ALPHABET.iter().position(|&a| a == c).unwrap() as u32;
        acc = acc << 6 | v;
        bits += 6;
        if bits >= 8 {
            bits -= 8;
            out.push((acc >> bits) as u8);
        }
    }
    out
}

/// The first DER element of `der`: its tag, its contents and what follows.
fn element(der: &[u8]) -> (u8, &[u8], &[u8]) {
    let (tag, first) = (der[0], der[1]);
    let (len, start) = if first < 0x80 {
        (first as usize, 2)
    } else {
        let n = (first & 0x7f) as usize;
        let len = der[2..2 + n].iter().fold(0, |l, &b| l << 8 | b as usize);
        (len, 2 + n)
    };
    (tag, &der[start..start + len], &der[start + len..])
}

/// The integers of a DER sequence, without their leading zero bytes.
fn integers(mut seq: &[u8]) -> Vec<&[u8]> {
    let mut ints = Vec::new();
    while !seq.is_empty() {
        let (tag, value, rest) = element(seq);
        assert_eq!(tag, 0x02);
        ints.push(&value[value.iter().take_while(|&&b| b == 0).count()..]);
        seq = rest;
    }
    ints
}

/// The base64 text between the PEM lines of `lines` (trimmed), as DER.
fn pem(lines: &[&str]) -> Vec<u8> {
    let b = lines
        .iter()
        .position(|l| *l == "-----BEGIN PRIVATE KEY-----")
        .unwrap();
    let e = lines
        .iter()
        .position(|l| *l == "-----END PRIVATE KEY-----")
        .unwrap();
    let b64: String = lines[b + 1..e]
        .iter()
        .filter(|l| !l.is_empty() && !l.contains(' '))
        .copied()
        .collect();
    unbase64(&b64)
}

/// The integers of the `RSAPrivateKey` of a PKCS #8 `PrivateKeyInfo`:
/// the version, `n`, `e`, `d`, `p`, `q`, `dP`, `dQ` and `qInv`.
fn components(der: &[u8]) -> Vec<&[u8]> {
    let (_, info, _) = element(der);
    let (_, _version, rest) = element(info);
    let (_, _algorithm, rest) = element(rest);
    let (tag, octets, _) = element(rest);
    assert_eq!(tag, 0x04);
    let (_, rsa, _) = element(octets);
    let v = integers(rsa);
    assert_eq!(v.len(), 9);
    v
}

/// The key of a PKCS #8 `PrivateKeyInfo` holding an `RSAPrivateKey`.
fn key(der: &[u8]) -> (PrivateKey, PublicKey) {
    let v = components(der);
    let private = PrivateKey::from_crt(v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8]).unwrap();
    (private, PublicKey::new(v[1], v[2]).unwrap())
}

/// The hex lines of `lines`, joined.
fn hex_lines(lines: &[&str]) -> Vec<u8> {
    let hex: String = lines
        .iter()
        .filter(|l| !l.is_empty() && l.bytes().all(|b| b.is_ascii_hexdigit()))
        .copied()
        .collect();
    unhex(&hex)
}

/// A vector: its title, its ciphertext and the message it decrypts to.
struct Vector {
    title: String,
    ct: Vec<u8>,
    msg: Vec<u8>,
}

/// The vector of the section `title`, whose `lines` are trimmed.
fn vector(title: &str, lines: &[&str]) -> Vector {
    let at = |marker: &str| lines.iter().position(|l| l.starts_with(marker));
    let c = at("Hex encoded ciphertext:").unwrap();
    let (end, msg) = if let Some(i) = at("ASCII encoded") {
        let text = lines[i + 1..].iter().find(|l| !l.is_empty()).unwrap();
        (i, text.as_bytes().to_vec())
    } else if let Some(i) =
        at("Hex encoded decrypted message:").or_else(|| at("Hex encoded message:"))
    {
        (i, hex_lines(&lines[i + 1..]))
    } else {
        (
            at("The result of decryption is a message of length 0.").unwrap(),
            Vec::new(),
        )
    };
    Vector {
        title: title.to_string(),
        ct: hex_lines(&lines[c + 1..end]),
        msg,
    }
}

/// Each key of Appendix B, with its vectors.
fn keys() -> Vec<(PrivateKey, PublicKey, Vec<Vector>)> {
    let text = TEXT.split_once("\nAppendix B.  Test Vectors\n").unwrap().1;
    let text = text.split_once("\nAuthor's Address\n").unwrap().0;
    let mut sections: Vec<(&str, Vec<&str>)> = Vec::new();
    for line in text.lines() {
        if line.starts_with("B.") {
            sections.push((line, Vec::new()));
        } else if let Some(s) = sections.last_mut() {
            s.1.push(line.trim());
        }
    }
    let mut keys = Vec::new();
    for (title, lines) in &sections {
        if title.ends_with("Private key") {
            let (private, public) = key(&pem(lines));
            keys.push((private, public, Vec::new()));
        } else if lines
            .iter()
            .any(|l| l.starts_with("Hex encoded ciphertext:"))
        {
            keys.last_mut().unwrap().2.push(vector(title, lines));
        }
    }
    keys
}

#[test]
fn rsa_pkcs1_appendix_b() {
    let keys = keys();
    assert_eq!(keys.len(), 4);
    for (private, public, vectors) in &keys {
        assert_eq!(vectors.len(), 12);
        for v in vectors {
            assert_eq!(v.ct.len(), private.modulus_len(), "{}", v.title);
            assert_eq!(decrypt(private, &v.ct).as_ref(), Ok(&v.msg), "{}", v.title);
            if v.title.contains("Valid") {
                let c = encrypt(public, &v.msg).unwrap();
                assert_eq!(decrypt(private, &c).as_ref(), Ok(&v.msg), "{}", v.title);
            }
        }
    }
}

#[test]
fn rsa_pkcs1_lengths() {
    let (private, public, vectors) = &keys()[1];
    let k = public.modulus_len();
    for len in [0, 1, k - 11] {
        let m: Vec<u8> = (0..len).map(|i| i as u8).collect();
        let c = encrypt(public, &m).unwrap();
        assert_eq!(c.len(), k);
        // A fresh padding string each time.
        assert_ne!(encrypt(public, &m).unwrap(), c);
        assert_eq!(decrypt(private, &c), Ok(m));
    }
    assert_eq!(
        encrypt(public, &vec![1; k - 10]),
        Err(Error::MessageTooLong)
    );
    let ct = &vectors[0].ct;
    assert_eq!(decrypt(private, &ct[1..]), Err(Error::InvalidLength));
    assert_eq!(
        decrypt(private, &vec![0xff; k]),
        Err(Error::InputOutOfRange)
    );
}

/// Keys whose private exponent or CRT values do not match.
#[test]
fn rsa_pkcs1_bad_keys() {
    let text = TEXT.split_once("\nB.1.1.  Private key\n").unwrap().1;
    let lines: Vec<&str> = text.lines().map(str::trim).collect();
    let der = pem(&lines);
    let v = components(&der);
    let ct = &keys()[0].2[0].ct;
    let with_d =
        |d: &[u8]| PrivateKey::from_crt(v[1], v[2], d, v[4], v[5], v[6], v[7], v[8]).unwrap();
    assert_eq!(decrypt(&with_d(&[]), ct), Err(Error::InvalidPrivateKey));
    assert_eq!(decrypt(&with_d(&[0, 0]), ct), Err(Error::InvalidPrivateKey));
    assert_eq!(
        decrypt(&with_d(&vec![1; 257]), ct),
        Err(Error::InvalidPrivateKey)
    );
    // `d` with leading zeros is the same number.
    let mut d = vec![0, 0];
    d.extend_from_slice(v[3]);
    assert!(decrypt(&with_d(&d), ct).is_ok());
    // A `dP` that does not match: the result fails its check.
    let mut dp = v[6].to_vec();
    *dp.last_mut().unwrap() ^= 2;
    let key = PrivateKey::from_crt(v[1], v[2], v[3], v[4], v[5], &dp, v[7], v[8]).unwrap();
    assert_eq!(decrypt(&key, ct), Err(Error::Fault));
}
