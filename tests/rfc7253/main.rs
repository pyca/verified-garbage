//! The sample results of RFC 7253 (Appendix A), which Wycheproof does not
//! have: the 16 `(N, A, P, C)` tuples with a 128-bit tag, the tuple with a
//! 96-bit tag, and the output of the iterative test for each parameter set
//! of §3.1 (AES-128, AES-192 and AES-256, with tags of 128, 96 and 64 bits).
//!
//! The RFC is vendored under `vectors/rfc7253/` (see
//! `vectors/sources/rfc7253.toml` for where it comes from) and compiled into
//! the test binary, so these tests always run. Each value is read from the
//! RFC's text: a field `X: hex` of a tuple, continued on the rows of hex
//! after it, and the `Output` lines of the iterative test.

#![cfg(target_arch = "x86_64")]

use verified_garbage::aes_ocb::{AesOcb, Error};

const TEXT: &str = include_str!("../../vectors/rfc7253/rfc7253.txt");

/// The lines of Appendix A, without the page breaks.
fn appendix() -> impl Iterator<Item = &'static str> {
    TEXT.lines()
        .skip_while(|l| !l.starts_with("Appendix A.  Sample Results"))
        .take_while(|l| !l.starts_with("Authors' Addresses"))
        .map(str::trim)
        .filter(|l| !(l.starts_with("Krovetz & Rogaway") || l.starts_with("RFC 7253 ")))
}

fn unhex(s: &str) -> Option<Vec<u8>> {
    if !s.len().is_multiple_of(2) || !s.bytes().all(|b| b.is_ascii_hexdigit()) {
        return None;
    }
    let b = s.as_bytes();
    Some(
        (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(core::str::from_utf8(&b[i..i + 2]).unwrap(), 16).unwrap())
            .collect(),
    )
}

/// A tuple: `C = OCB-ENCRYPT(K, N, A, P)`, the ciphertext followed by the
/// tag.
struct Tuple {
    k: Vec<u8>,
    n: Vec<u8>,
    a: Vec<u8>,
    p: Vec<u8>,
    c: Vec<u8>,
}

/// The tuples of Appendix A: a field `K`, `N`, `A`, `P` or `C` (`X: hex`,
/// the hex possibly empty) continues on the rows of hex after it, and a `C`
/// ends a tuple, with the last `K`.
fn tuples() -> Vec<Tuple> {
    let mut fields: [Vec<u8>; 5] = Default::default();
    let mut current = None;
    let mut out = Vec::new();
    for line in appendix() {
        let field = line.split_once(':').and_then(|(name, value)| {
            let i = ["K", "N", "A", "P", "C"]
                .iter()
                .position(|&f| f == name.trim())?;
            Some((i, unhex(value.trim())?))
        });
        if let Some((i, value)) = field {
            fields[i] = value;
            current = Some(i);
        } else if let (Some(i), Some(row)) = (current, unhex(line).filter(|r| !r.is_empty())) {
            fields[i].extend(row);
        } else {
            if current == Some(4) {
                let [k, n, a, p, c] = fields.clone();
                out.push(Tuple { k, n, a, p, c });
            }
            current = None;
        }
    }
    out
}

/// Checks `tuple`, whose tag has `T` bytes: it encrypts to `C`, `C`
/// decrypts back, and changing a bit of the tag, the ciphertext, the
/// associated data or the nonce fails decryption, which leaves zeros.
fn check<const T: usize>(tuple: &Tuple) {
    let key = AesOcb::new(&tuple.k).unwrap();
    let (ct, tag) = tuple.c.split_at(tuple.p.len());
    let tag: &[u8; T] = tag.try_into().unwrap();
    let mut buf = tuple.p.clone();
    let t = key
        .encrypt_in_place::<T>(&tuple.n, &tuple.a, &mut buf)
        .unwrap();
    assert_eq!((&buf[..], &t), (ct, tag));
    key.decrypt_in_place(&tuple.n, &tuple.a, &mut buf, tag)
        .unwrap();
    assert_eq!(buf, tuple.p);

    let flip = |v: &[u8], i: usize| {
        let mut v = v.to_vec();
        v[i / 8] ^= 1 << (i % 8);
        v
    };
    let mut cases = vec![(tuple.n.clone(), tuple.a.clone(), ct.to_vec(), flip(tag, 0))];
    cases.push((
        tuple.n.clone(),
        tuple.a.clone(),
        ct.to_vec(),
        flip(tag, 8 * T - 1),
    ));
    cases.push((
        flip(&tuple.n, 0),
        tuple.a.clone(),
        ct.to_vec(),
        tag.to_vec(),
    ));
    if !ct.is_empty() {
        cases.push((
            tuple.n.clone(),
            tuple.a.clone(),
            flip(ct, 8 * ct.len() - 1),
            tag.to_vec(),
        ));
    }
    if !tuple.a.is_empty() {
        cases.push((
            tuple.n.clone(),
            flip(&tuple.a, 3),
            ct.to_vec(),
            tag.to_vec(),
        ));
    }
    for (n, a, mut c, t) in cases {
        let t: &[u8; T] = t.as_slice().try_into().unwrap();
        assert_eq!(
            key.decrypt_in_place(&n, &a, &mut c, t),
            Err(Error::TagMismatch)
        );
        assert!(c.iter().all(|&b| b == 0));
    }
}

#[test]
fn aes_ocb_sample_results() {
    let tuples = tuples();
    assert_eq!(tuples.len(), 17);
    for (i, tuple) in tuples.iter().enumerate() {
        // The first 16 have a 128-bit tag; the last a 96-bit one.
        let tag_len = tuple.c.len() - tuple.p.len();
        if i < 16 {
            assert_eq!(tag_len, 16, "tuple {i}");
            check::<16>(tuple);
        } else {
            assert_eq!(tag_len, 12, "tuple {i}");
            check::<12>(tuple);
        }
    }
}

/// The iterative test for a key of `key_len` bytes and a tag of `T` bytes:
/// its output.
fn iterate<const T: usize>(key_len: usize) -> [u8; T] {
    let mut k = vec![0u8; key_len];
    k[key_len - 1] = (8 * T) as u8;
    let key = AesOcb::new(&k).unwrap();
    let nonce = |i: u32| {
        let mut n = [0u8; 12];
        n[8..].copy_from_slice(&i.to_be_bytes());
        n
    };
    let mut c = Vec::new();
    let mut seal = |i, a: &[u8], p: &[u8]| {
        let mut buf = p.to_vec();
        let t = key.encrypt_in_place::<T>(&nonce(i), a, &mut buf).unwrap();
        let mut back = buf.clone();
        key.decrypt_in_place(&nonce(i), a, &mut back, &t).unwrap();
        assert_eq!(back, p);
        c.extend(buf);
        c.extend(t);
    };
    for i in 0..128 {
        let s = vec![0u8; i as usize];
        seal(3 * i + 1, &s, &s);
        seal(3 * i + 2, &[], &s);
        seal(3 * i + 3, &s, &[]);
    }
    assert_eq!(c.len(), 128 * 127 + 128 * 3 * T);
    key.encrypt_in_place::<T>(&nonce(385), &c, &mut []).unwrap()
}

#[test]
fn aes_ocb_iterative() {
    let mut outputs = 0;
    for line in appendix() {
        let Some(rest) = line.strip_prefix("AEAD_AES_") else {
            continue;
        };
        let (bits, rest) = rest.split_once("_OCB_TAGLEN").unwrap();
        let (tag_bits, output) = rest.split_once("Output").unwrap();
        let expected = unhex(output.trim_start_matches([' ', ':'])).unwrap();
        let key_len = bits.parse::<usize>().unwrap() / 8;
        let got = match tag_bits.trim() {
            "128" => iterate::<16>(key_len).to_vec(),
            "96" => iterate::<12>(key_len).to_vec(),
            other => {
                assert_eq!(other, "64");
                iterate::<8>(key_len).to_vec()
            }
        };
        assert_eq!(got, expected, "{line}");
        outputs += 1;
    }
    assert_eq!(outputs, 9);
}
