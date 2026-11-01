//! pyca/cryptography's SM3 vectors (`hashes/SM3/oscca.txt`, in the NIST
//! response file format).

use super::{check, unhex};

#[test]
fn oscca() {
    let text = include_str!("../../vectors/cryptography-sm3/oscca.txt");
    let lines: Vec<&str> = text
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .collect();
    assert_eq!(lines.len(), 18);
    for v in lines.chunks(3) {
        let len: usize = v[0].strip_prefix("Len = ").unwrap().parse().unwrap();
        let msg = unhex(v[1].strip_prefix("Msg = ").unwrap());
        let md = unhex(v[2].strip_prefix("MD = ").unwrap());
        // `Len` is in bits; the empty message is written as `Msg = 00`.
        check(&msg[..len / 8], &md);
    }
}
