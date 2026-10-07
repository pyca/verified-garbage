//! RSA prime generation (`verified_garbage::rsa_keygen`), with the octets of
//! known numbers as the first candidate:
//!
//! * each prime of the two-prime private keys of the RSA test vector files
//!   (`rsa_*_test.json`) whose length `generate_prime_from` takes and whose
//!   two most significant bits are set, as a candidate sets them: followed
//!   by random octets for its witnesses, it is accepted, with the key's
//!   public exponent, and with the key's other prime as the other prime;
//!   given as the other prime itself, it is too close, and the key's other
//!   prime, following it, is accepted;
//! * each number of `primality_test.json` of such a length and form (only
//!   composites, Carmichael numbers and worst cases for Miller–Rabin):
//!   followed by random octets, it is never the prime returned, with `e = 1`
//!   (so that only trial division and Miller–Rabin can reject it);
//! * each two-prime private key of the RSA test vector files whose primes
//!   `key_from_primes` takes, from its primes and public exponent: the key
//!   it returns has the key's `n`, `p`, `q`, `dP`, `dQ` and `qInv`, passes
//!   `check_key` (`d e ≡ 1` modulo `p - 1` and `q - 1`), and has the key's
//!   `d` but where the key's `d` is not the least (all keys but one).

#![cfg(all(
    any(target_arch = "x86_64", target_arch = "aarch64"),
    feature = "alloc"
))]

use std::collections::BTreeMap;

use serde::Deserialize;
use verified_garbage::rsa_keygen::{generate_prime_from, key_from_primes};

use super::harness::{self, Count, Expectation, Hex, TestFile};
use crate::require_vectors;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Key {
    public_exponent: Hex,
    prime1: Option<Hex>,
    prime2: Option<Hex>,
    modulus: Option<Hex>,
    private_exponent: Option<Hex>,
    exponent1: Option<Hex>,
    exponent2: Option<Hex>,
    coefficient: Option<Hex>,
    other_prime_infos: Option<serde_json::Value>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Group {
    private_key: Option<Key>,
}

#[derive(Deserialize)]
struct Case {}

#[derive(Deserialize)]
struct PrimalityGroup {}

#[derive(Deserialize)]
struct PrimalityCase {
    value: Hex,
}

/// A prime, with the file it is from, the key's other prime and its public
/// exponent.
struct Prime {
    p: Vec<u8>,
    name: String,
    q: Vec<u8>,
    e: Vec<u8>,
}

/// `x` without its leading zero bytes (the vectors write numbers in DER's
/// form, with a zero byte before a top bit that is set).
fn trim(x: &[u8]) -> &[u8] {
    &x[x.iter().take_while(|&&b| b == 0).count()..]
}

/// Whether `x` is a candidate as `generate_prime_from` makes it from its
/// octets: of a length it takes, with its two top bits and its low bit set.
fn candidate(x: &[u8]) -> bool {
    x.len().is_multiple_of(8)
        && (32..=512).contains(&x.len())
        && x[0] >> 6 == 3
        && x[x.len() - 1] & 1 == 1
}

/// `x`, followed by random octets for 64 witnesses of its length (a prime of
/// `n` octets needs 16, and more only for witnesses not below it).
fn then_random(x: &[u8]) -> Vec<u8> {
    let mut v = x.to_vec();
    v.resize(65 * x.len(), 0);
    getrandom::fill(&mut v[x.len()..]).unwrap();
    v
}

/// Checks the prime `p` of the key with the other prime `q` (as long) and
/// the public exponent `e`, from the file `name`.
fn check_prime(name: &str, p: &[u8], q: &[u8], e: &[u8]) {
    let len = p.len();
    let bits = 8 * len;
    let rand = then_random(p);
    let (got, used) = generate_prime_from(bits, e, None, &rand).unwrap();
    assert_eq!(got, p, "{name}");
    let whole = used >= 17 * len && used.is_multiple_of(len);
    assert!(whole, "{name}: {used}");
    let (got, used2) = generate_prime_from(bits, e, Some(q), &rand).unwrap();
    assert_eq!((&got[..], used2), (p, used), "{name}: with q");
    if candidate(q) {
        let mut rand = p.to_vec();
        rand.extend(then_random(q));
        let (got, used) = generate_prime_from(bits, e, Some(p), &rand).unwrap();
        assert_eq!(got, q, "{name}: after p, too close");
        assert!(used >= 18 * len, "{name}: {used}");
    }
}

#[test]
fn rsa_keygen_primes() {
    require_vectors!();
    // Each prime once, with the first file that has it.
    let mut primes: BTreeMap<Vec<u8>, (String, Vec<u8>, Vec<u8>)> = BTreeMap::new();
    for name in harness::all_files().unwrap() {
        if !(name.starts_with("rsa_") && name.ends_with("_test.json")) {
            continue;
        }
        let file: TestFile<Group, Case> = harness::load(&name);
        for group in file.test_groups {
            let Some(Key {
                public_exponent,
                prime1: Some(p),
                prime2: Some(q),
                ..
            }) = group.params.private_key
            else {
                continue;
            };
            let (p, q) = (trim(&p.0), trim(&q.0));
            for (a, b) in [(p, q), (q, p)] {
                // Every key's primes are as long as each other.
                if candidate(a) && b.len() == a.len() {
                    primes.entry(a.to_vec()).or_insert((
                        name.clone(),
                        b.to_vec(),
                        public_exponent.0.clone(),
                    ));
                }
            }
        }
    }
    let primes: Vec<Prime> = primes
        .into_iter()
        .map(|(p, (name, q, e))| Prime { p, name, q, e })
        .collect();
    assert!(!primes.is_empty());
    harness::par_each(&primes, |x| check_prime(&x.name, &x.p, &x.q, &x.e));
}

#[test]
fn rsa_keygen_composites() {
    require_vectors!();
    let file: TestFile<PrimalityGroup, PrimalityCase> = harness::load("primality_test.json");
    let checked = Count::default();
    file.par_tests(|_, t| {
        let v = &t.case.value.0;
        // A negative number has its top bit set; a positive one with its
        // top bit set has a zero byte before it.
        let x = trim(v);
        if v.first() != Some(&0) || !candidate(x) {
            return;
        }
        let r = generate_prime_from(8 * x.len(), &[1], None, &then_random(x));
        // A valid number (a prime) is the first candidate, accepted; an
        // invalid one is rejected.
        let accepted = r.is_ok_and(|(p, _)| p == x);
        let expected = t.result == Expectation::Valid;
        let ok = t.result == Expectation::Acceptable || accepted == expected;
        assert!(ok, "tcId {}", t.tc_id);
        checked.add();
    });
    assert!(checked.get() > 0);
}

/// `x` in `len` bytes (big-endian).
fn widen(x: &[u8], len: usize) -> Vec<u8> {
    let x = trim(x);
    let mut v = vec![0; len - x.len()];
    v.extend_from_slice(x);
    v
}

/// Checks that `key_from_primes` makes the key `k` (of the file `name`)
/// from its primes, in either order; returns how many of the two keys have
/// its `d`.
fn check_key(name: &str, k: &Key) -> usize {
    let [p, q, n, d, dp, dq, qinv] = [
        &k.prime1,
        &k.prime2,
        &k.modulus,
        &k.private_exponent,
        &k.exponent1,
        &k.exponent2,
        &k.coefficient,
    ]
    .map(|x| &x.as_ref().unwrap().0);
    let (p, q) = (trim(p), trim(q));
    let len = p.len();
    let e = trim(&k.public_exponent.0);
    // The key's `p` is the larger, as `key_from_primes` makes it.
    assert!(p > q, "{name}");
    let mut same_d = 0;
    for (a, b) in [(p, q), (q, p)] {
        let key = key_from_primes(e, a, b).unwrap();
        let [kn, ke, kd, kp, kq, kdp, kdq, kqinv] = key.components();
        assert_eq!((kn, ke), (trim(n), e), "{name}");
        assert_eq!((kp, kq), (p, q), "{name}");
        assert_eq!(kdp, widen(dp, len), "{name}");
        assert_eq!(kdq, widen(dq, len), "{name}");
        assert_eq!(kqinv, widen(qinv, len), "{name}");
        assert!(key.check_key(), "{name}");
        if kd == widen(d, 2 * len) {
            same_d += 1;
        }
    }
    same_d
}

#[test]
fn rsa_keygen_keys() {
    require_vectors!();
    // Each two-prime key with every CRT component whose primes
    // `key_from_primes` takes, once (by its `p`), with the first file that
    // has it.
    let mut keys: BTreeMap<Vec<u8>, (String, Key)> = BTreeMap::new();
    for name in harness::all_files().unwrap() {
        if !(name.starts_with("rsa_") && name.ends_with("_test.json")) {
            continue;
        }
        let file: TestFile<Group, Case> = harness::load(&name);
        for group in file.test_groups {
            let Some(k) = group.params.private_key else {
                continue;
            };
            let Key {
                public_exponent: e,
                prime1: Some(p),
                prime2: Some(q),
                modulus: Some(_),
                private_exponent: Some(_),
                exponent1: Some(_),
                exponent2: Some(_),
                coefficient: Some(_),
                other_prime_infos: None,
            } = &k
            else {
                continue;
            };
            let (p, q) = (trim(&p.0), trim(&q.0));
            let len = p.len();
            if q.len() != len
                || !len.is_multiple_of(8)
                || !(32..=512).contains(&len)
                || trim(&e.0).len() > 8
            {
                continue;
            }
            keys.entry(p.to_vec()).or_insert((name.clone(), k));
        }
    }
    let keys: Vec<(String, Key)> = keys.into_values().collect();
    let same_d = Count::default();
    harness::par_each(&keys, |(name, k)| same_d.add_n(check_key(name, k)));
    assert!(!keys.is_empty());
    // One key's `d` is the least plus 12 `lcm(p - 1, q - 1)`.
    assert_eq!(same_d.get(), 2 * (keys.len() - 1));
}
