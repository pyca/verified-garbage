//! Local check of the unproven `vg_rsa_recover_primes_det` (bench branch
//! only), against the two-prime private keys of Wycheproof's
//! `rsa_*_test.json`, read from the checkout at `WYCHEPROOF_ROOT`.
#![cfg(target_arch = "riscv64")]
use std::collections::BTreeSet;

use verified_garbage_asm_riscv64::rsa_proto4::vg_rsa_recover_primes_det;

fn hex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

fn trim(x: &[u8]) -> Vec<u8> {
    let i = x.iter().position(|&b| b != 0).unwrap_or(x.len());
    x[i..].to_vec()
}

fn pad(x: &[u8], l: usize) -> Vec<u8> {
    let x = trim(x);
    let mut v = vec![0; l - x.len()];
    v.extend(x);
    v
}

/// The string value of `"name"` in `obj`.
fn field(obj: &str, name: &str) -> Option<String> {
    let k = format!("\"{name}\"");
    let i = obj.find(&k)? + k.len();
    let rest = &obj[i..];
    let a = rest.find('"')? + 1;
    let b = rest[a..].find('"')? + a;
    Some(rest[a..b].to_string())
}

/// `(n, e, d, p, q)` of every two-prime private key, trimmed.
fn keys() -> Vec<[Vec<u8>; 5]> {
    let root = std::env::var("WYCHEPROOF_ROOT").expect("WYCHEPROOF_ROOT");
    let mut set = BTreeSet::new();
    let dir = format!("{root}/testvectors_v1");
    for ent in std::fs::read_dir(&dir).unwrap() {
        let path = ent.unwrap().path();
        let name = path.file_name().unwrap().to_str().unwrap().to_string();
        if !(name.starts_with("rsa_") && name.ends_with("_test.json")) {
            continue;
        }
        let s = std::fs::read_to_string(&path).unwrap();
        let mut at = 0;
        while let Some(i) = s[at..].find("\"privateKey\"") {
            let start = at + i;
            let Some(o) = s[start..].find('{') else { break };
            let Some(c) = s[start + o..].find('}') else {
                break;
            };
            let obj = &s[start + o..start + o + c];
            at = start + o + c;
            if obj.contains("otherPrimeInfos") {
                continue;
            }
            let fs = [
                "modulus",
                "publicExponent",
                "privateExponent",
                "prime1",
                "prime2",
            ]
            .map(|f| field(obj, f));
            if fs.iter().all(Option::is_some) {
                set.insert(fs.map(|f| trim(&hex(&f.unwrap()))));
            }
        }
    }
    set.into_iter().collect()
}

fn recover(n: &[u8], e: &[u8], d: &[u8]) -> (u32, Vec<u8>, Vec<u8>) {
    let k = n.len();
    let (mut p, mut q) = (vec![0xaa; k], vec![0xaa; k]);
    let mut s = vec![0x5a5a5a5a5a5a5a5au64; 16 * k + 32];
    let r = unsafe {
        vg_rsa_recover_primes_det(
            p.as_mut_ptr(),
            k,
            q.as_mut_ptr(),
            k,
            n.as_ptr(),
            k,
            e.as_ptr(),
            e.len(),
            d.as_ptr(),
            d.len(),
            s.as_mut_ptr(),
            s.len(),
        )
    };
    (r, p, q)
}

/// The primes, the larger first, as `k` octets.
fn primes(f: &[Vec<u8>; 5]) -> (Vec<u8>, Vec<u8>) {
    let k = f[0].len();
    let (a, b) = (pad(&f[3], k), pad(&f[4], k));
    if a > b { (a, b) } else { (b, a) }
}

#[test]
fn recovers_every_key() {
    let ks = keys();
    assert!(ks.len() > 100, "{} keys", ks.len());
    for f in &ks {
        let k = f[0].len();
        let (p, q) = primes(f);
        assert_eq!(
            recover(&f[0], &f[1], &f[2]),
            (1, p.clone(), q.clone()),
            "k = {k}"
        );
        // `d` with leading zeros, up to `n`'s length.
        assert_eq!(
            recover(&f[0], &f[1], &pad(&f[2], k)),
            (1, p, q),
            "k = {k}, padded d"
        );
    }
}

#[test]
fn refuses_or_factors() {
    for f in &keys() {
        let k = f[0].len();
        let (p, q) = primes(f);
        let zero = vec![0; k];
        // `d` changed: no factors, or the factors.
        for (j, m) in [(f[2].len() - 1, 1u8), (f[2].len() - 1, 2), (0, 1)] {
            let mut d = f[2].clone();
            d[j] ^= m;
            if d[0] == 0 {
                continue;
            }
            let r = recover(&f[0], &f[1], &d);
            assert!(
                r == (0, zero.clone(), zero.clone()) || r == (1, p.clone(), q.clone()),
                "k = {k}, d bit"
            );
        }
        // `n` even or its first byte zero: not a modulus.
        let mut n = f[0].clone();
        n[k - 1] ^= 1;
        assert_eq!(
            recover(&n, &f[1], &f[2]),
            (0, zero.clone(), zero.clone()),
            "k = {k}, n even"
        );
        let mut n = f[0].clone();
        n[0] = 0;
        assert_eq!(
            recover(&n, &f[1], &f[2]),
            (0, zero.clone(), zero.clone()),
            "k = {k}, n's first byte"
        );
        // `d e < 2`.
        assert_eq!(
            recover(&f[0], &[1], &[1]),
            (0, zero.clone(), zero.clone()),
            "k = {k}, d e = 1"
        );
        assert_eq!(
            recover(&f[0], &[1], &[0]),
            (0, zero.clone(), zero.clone()),
            "k = {k}, d e = 0"
        );
    }
}

#[test]
fn repeated_calls() {
    let ks = keys();
    let f = &ks[0];
    let want = primes(f);
    for _ in 0..3 {
        let (r, p, q) = recover(&f[0], &f[1], &f[2]);
        assert_eq!((r, p, q), (1, want.0.clone(), want.1.clone()));
    }
}
