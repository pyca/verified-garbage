//! Shared decoder for the published OpenSSL DSA interoperability fixture.
extern crate alloc;
use alloc::vec::Vec;

/// Published OpenSSL parameters, kept byte for byte in vectors/. This decoder
/// only reads that trusted fixture; it is not an API for untrusted ASN.1.
pub fn parameters() -> (Vec<u8>, Vec<u8>, Vec<u8>) {
    const ALPHABET: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let text = include_str!("../vectors/openssl-dsa-legacy/p2048_q160_t1862.pem");
    let mut der = Vec::new();
    let (mut acc, mut bits) = (0u32, 0);
    for line in text.lines().filter(|line| !line.starts_with('-')) {
        for c in line.bytes().filter(|&c| c != b'=') {
            let v = ALPHABET.iter().position(|&a| a == c).unwrap() as u32;
            acc = acc << 6 | v;
            bits += 6;
            if bits >= 8 {
                bits -= 8;
                der.push((acc >> bits) as u8);
            }
        }
    }
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
    let (tag, mut seq, rest) = element(&der);
    assert_eq!(tag, 0x30);
    assert!(rest.is_empty());
    let mut values = Vec::new();
    while !seq.is_empty() {
        let (tag, value, rest) = element(seq);
        assert_eq!(tag, 2);
        values.push(value[value.iter().take_while(|&&b| b == 0).count()..].to_vec());
        seq = rest;
    }
    assert_eq!(values.len(), 3);
    let g = values.pop().unwrap();
    let q = values.pop().unwrap();
    let p = values.pop().unwrap();
    assert_eq!((p.len(), q.len(), g.len()), (256, 20, 256));
    (p, q, g)
}
