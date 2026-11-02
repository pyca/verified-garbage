//! Local check of the unproven RISC-V `vg_rsa_keygen_candidate` (bench
//! branch only), against the two-prime private keys of Wycheproof's
//! `rsa_*_test.json` and the numbers of its `primality_test.json`, read from
//! the checkout at `WYCHEPROOF_ROOT`, and against the function itself.
#![cfg(target_arch = "riscv64")]
use std::collections::BTreeSet;

use verified_garbage_asm_riscv64::rsa_proto6::vg_rsa_keygen_candidate_proto;

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

fn field(obj: &str, name: &str) -> Option<String> {
    let k = format!("\"{name}\"");
    let i = obj.find(&k)? + k.len();
    let rest = &obj[i..];
    let a = rest.find('"')? + 1;
    let b = rest[a..].find('"')? + a;
    Some(rest[a..b].to_string())
}

fn root() -> String {
    std::env::var("WYCHEPROOF_ROOT").expect("WYCHEPROOF_ROOT")
}

/// `(e, p, q)` of every two-prime private key, trimmed.
fn keys() -> Vec<[Vec<u8>; 3]> {
    let mut set = BTreeSet::new();
    let dir = format!("{}/testvectors_v1", root());
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
            let fs = ["publicExponent", "prime1", "prime2"].map(|f| field(obj, f));
            if fs.iter().all(Option::is_some) {
                set.insert(fs.map(|f| trim(&hex(&f.unwrap()))));
            }
        }
    }
    set.into_iter().collect()
}

/// Whether `x` is a candidate as the function makes it from its octets.
fn candidate(x: &[u8]) -> bool {
    x.len() % 8 == 0 && (32..=512).contains(&x.len()) && x[0] >> 6 == 3 && x[x.len() - 1] & 1 == 1
}

struct Rng(u64);
impl Rng {
    fn fill(&mut self, v: &mut [u8]) {
        for b in v {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            *b = (self.0 >> 24) as u8;
        }
    }
}

/// `x`, then random octets for 64 witnesses of its length.
fn then_random(x: &[u8], rng: &mut Rng) -> Vec<u8> {
    let mut v = x.to_vec();
    v.resize(65 * x.len(), 0);
    rng.fill(&mut v[x.len()..]);
    v
}

/// `(result, out, used)` of one candidate.
fn cand(len: usize, e: &[u8], p: Option<&[u8]>, rand: &[u8]) -> (u32, Vec<u8>, u64) {
    let mut out = vec![0xaa; len];
    let mut used = 0xdead_u64;
    let mut s = vec![0x5a5a5a5a5a5a5a5au64; 16 * len + 32];
    let (pp, pl) = p.map_or((core::ptr::null(), 0), |p| (p.as_ptr(), p.len()));
    let r = unsafe {
        vg_rsa_keygen_candidate_proto(
            out.as_mut_ptr(),
            len,
            &mut used,
            e.as_ptr(),
            e.len(),
            pp,
            pl,
            rand.as_ptr(),
            rand.len(),
            s.as_mut_ptr(),
            s.len(),
        )
    };
    (r, out, used)
}

#[test]
fn primes() {
    let mut rng = Rng(0x9e3779b97f4a7c15);
    let mut n = 0;
    for [e, p, q] in keys() {
        if p.len() != q.len() {
            continue;
        }
        for (prime, other) in [(&p, &q), (&q, &p)] {
            if !candidate(prime) {
                continue;
            }
            let len = prime.len();
            let rand = then_random(prime, &mut rng);
            let (r, out, used) = cand(len, &e, None, &rand);
            assert_eq!((r, &out), (1, prime), "alone, {len}");
            let used = used as usize;
            assert!(used >= 17 * len && used % len == 0, "{used}");
            // With the other prime given: accepted, reading as many.
            assert_eq!(
                cand(len, &e, Some(other), &rand),
                (1, prime.clone(), used as u64)
            );
            // The prime itself, as the other prime: too close; its octets only.
            assert_eq!(
                cand(len, &e, Some(prime), &rand),
                (2, vec![0; len], len as u64)
            );
            // Too short: 0, zeros, nothing read.
            assert_eq!(cand(len, &e, None, &rand[..len - 1]), (0, vec![0; len], 0));
            // Runs out of witnesses: 0.
            assert_eq!(cand(len, &e, None, &rand[..used - 1]), (0, vec![0; len], 0));
            // An even e: gcd(c - 1, e) ≠ 1.
            assert_eq!(cand(len, &[2], None, &rand), (3, vec![0; len], len as u64));
            n += 1;
        }
    }
    assert!(n > 0);
    eprintln!("{n} primes");
}

#[test]
fn composites() {
    let s =
        std::fs::read_to_string(format!("{}/testvectors_v1/primality_test.json", root())).unwrap();
    let mut rng = Rng(12345);
    let mut at = 0;
    let (mut n, mut primes) = (0, 0);
    while let Some(i) = s[at..].find("\"tcId\"") {
        let start = at + i;
        let end = s[start..].find('}').unwrap() + start;
        let obj = &s[start..end];
        at = end;
        let v = hex(&field(obj, "value").unwrap());
        let x = trim(&v);
        if v.first() != Some(&0) || !candidate(&x) {
            continue;
        }
        let valid = field(obj, "result").unwrap() == "valid";
        let (r, out, _) = cand(x.len(), &[1], None, &then_random(&x, &mut rng));
        assert_eq!(r == 1 && out == x, valid, "{obj}");
        n += 1;
        primes += valid as usize;
    }
    assert!(n > 0);
    eprintln!("{n} numbers, {primes} primes");
}

/// The function against itself: candidates from random octets until one is
/// accepted, which is then accepted again as the first candidate and with
/// `e = 3` only if `gcd(c - 1, 3) = 1`.
#[test]
fn random() {
    let mut rng = Rng(777);
    for len in [32usize, 64, 128] {
        let mut rand = vec![0; 200 * len];
        let (mut tries, mut tooclose) = (0, 0);
        let prime = loop {
            rng.fill(&mut rand);
            let (r, out, used) = cand(len, &[1, 0, 1], None, &rand);
            tries += 1;
            match r {
                1 => break (out, used),
                3 => assert_eq!((out, used), (vec![0; len], used)),
                2 => tooclose += 1,
                _ => panic!("{r}"),
            }
        };
        assert_eq!(tooclose, 0);
        let (c, used) = prime;
        assert!(candidate(&c));
        assert_eq!(
            &c[..],
            &{
                let mut x = rand[..len].to_vec();
                x[0] |= 0xc0;
                x[len - 1] |= 1;
                x
            }[..]
        );
        assert_eq!(cand(len, &[1, 0, 1], None, &rand).1, c);
        assert_eq!(cand(len, &[1, 0, 1], None, &rand).2, used);
        eprintln!("{len}: {tries} candidates");
    }
}
