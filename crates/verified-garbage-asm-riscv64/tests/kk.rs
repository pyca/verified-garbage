//! Local check of the unproven RISC-V `vg_rsa_keygen_key` (bench branch
//! only), against the two-prime private keys of Wycheproof's
//! `rsa_*_test.json`, read from the checkout at `WYCHEPROOF_ROOT`: each
//! key's `n`, `p`, `q`, `dP`, `dQ` and `qInv` from its primes in either
//! order, its `d` for all but the one key whose `d` is not the least, and
//! the inputs the contract rejects.
#![cfg(target_arch = "riscv64")]
use std::collections::BTreeMap;

use verified_garbage_asm_riscv64::rsa_proto9::{
    vg_rsa_keygen_key_odd_proto, vg_rsa_keygen_key_proto,
};
use verified_garbage_asm_riscv64::rsa_proto10::vg_rsa_keygen_key_ib_proto;

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

fn widen(x: &[u8], len: usize) -> Vec<u8> {
    let x = trim(x);
    let mut v = vec![0; len - x.len()];
    v.extend_from_slice(&x);
    v
}

fn field(obj: &str, name: &str) -> Option<String> {
    let k = format!("\"{name}\"");
    let i = obj.find(&k)? + k.len();
    let rest = &obj[i..];
    let a = rest.find('"')? + 1;
    let b = rest[a..].find('"')? + a;
    Some(rest[a..b].to_string())
}

const F: [&str; 8] = [
    "publicExponent",
    "prime1",
    "prime2",
    "modulus",
    "privateExponent",
    "exponent1",
    "exponent2",
    "coefficient",
];

/// Every two-prime private key with all its CRT components, once by its `p`.
fn keys() -> Vec<[Vec<u8>; 8]> {
    let mut map = BTreeMap::new();
    let dir = format!(
        "{}/testvectors_v1",
        std::env::var("WYCHEPROOF_ROOT").unwrap()
    );
    let mut names: Vec<_> = std::fs::read_dir(&dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .collect();
    names.sort();
    for path in names {
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
            let fs = F.map(|f| field(obj, f));
            if !fs.iter().all(Option::is_some) {
                continue;
            }
            let k = fs.map(|f| trim(&hex(&f.unwrap())));
            let len = k[1].len();
            if k[2].len() != len || len % 8 != 0 || !(32..=512).contains(&len) || k[0].len() > 8 {
                continue;
            }
            map.entry(k[1].clone()).or_insert(k);
        }
    }
    map.into_values().collect()
}

type Fn = unsafe extern "C" fn(
    *mut u8,
    usize,
    *mut u8,
    usize,
    *mut u8,
    usize,
    *mut u8,
    usize,
    *mut u8,
    usize,
    *mut u8,
    usize,
    *mut u8,
    usize,
    *const u8,
    usize,
    *mut u64,
    usize,
) -> u32;

/// The status and the seven outputs from `e`, `p` and `q`.
fn run(f: Fn, e: &[u8], p: &[u8], q: &[u8]) -> (u32, [Vec<u8>; 7]) {
    let len = p.len();
    let mut o = [
        vec![0xa5u8; 2 * len],
        vec![0xa5; 2 * len],
        p.to_vec(),
        q.to_vec(),
        vec![0xa5; len],
        vec![0xa5; len],
        vec![0xa5; len],
    ];
    let mut scratch = vec![0x5a5a5a5a5a5a5a5au64; 16 * 2 * len + 32];
    let [n, d, kp, kq, dp, dq, qi] = &mut o;
    let r = unsafe {
        f(
            n.as_mut_ptr(),
            n.len(),
            d.as_mut_ptr(),
            d.len(),
            kp.as_mut_ptr(),
            kp.len(),
            kq.as_mut_ptr(),
            kq.len(),
            dp.as_mut_ptr(),
            dp.len(),
            dq.as_mut_ptr(),
            dq.len(),
            qi.as_mut_ptr(),
            qi.len(),
            e.as_ptr(),
            e.len(),
            scratch.as_mut_ptr(),
            scratch.len(),
        )
    };
    (r, o)
}

fn zeros(o: &[Vec<u8>; 7]) -> bool {
    o.iter().all(|v| v.iter().all(|&b| b == 0))
}

#[test]
fn keys_from_primes() {
    let keys = keys();
    assert!(!keys.is_empty());
    let mut same_d = 0;
    for k in &keys {
        let [e, p, q, n, d, dp, dq, qi] = k;
        let len = p.len();
        assert!(p > q);
        for (a, b) in [(p, q), (q, p)] {
            for f in [
                vg_rsa_keygen_key_proto as Fn,
                vg_rsa_keygen_key_odd_proto as Fn,
                vg_rsa_keygen_key_ib_proto as Fn,
            ] {
                let (r, o) = run(f, e, a, b);
                assert_eq!(r, 1, "len {len}");
                assert_eq!(o[0], widen(n, 2 * len));
                assert_eq!((&o[2], &o[3]), (p, q));
                assert_eq!(o[4], widen(dp, len));
                assert_eq!(o[5], widen(dq, len));
                assert_eq!(o[6], widen(qi, len));
                if o[1] == widen(d, 2 * len) {
                    same_d += 1;
                }
            }
        }
    }
    // One key's `d` is not the least (it is the least plus 12 `lcm`).
    assert_eq!(same_d, 6 * (keys.len() - 1), "{} keys", keys.len());
    eprintln!("{} keys checked", keys.len());
}

#[test]
fn rejected() {
    let keys = keys();
    for k in keys.iter().take(40) {
        let [e, p, q, ..] = k;
        // p even: not a key.
        let mut pe = p.clone();
        *pe.last_mut().unwrap() &= 0xfe;
        // e even: no inverse.
        let e2 = [2u8];
        // p = q: L = p - 1, so d < p - 1 < 2^(8 p_len), the status 2.
        // An even p: not a key, whether d exists (0) or is small (2).
        for f in [
            vg_rsa_keygen_key_proto as Fn,
            vg_rsa_keygen_key_ib_proto as Fn,
        ] {
            for (ee, a, b, ok) in [
                (&e[..], &pe, q, [0, 2]),
                (&e2[..], p, q, [0, 0]),
                (&e[..], p, p, [2, 2]),
            ] {
                let (r, o) = run(f, ee, a, b);
                assert!(ok.contains(&r), "{r}");
                assert!(zeros(&o));
            }
            // Repeated calls agree.
            let a = run(f, e, p, q);
            let b = run(f, e, p, q);
            assert_eq!(a, b);
        }
    }
}
