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
//!   (so that only trial division and Miller–Rabin can reject it).

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering};

use serde::Deserialize;
use verified_garbage::rsa_keygen::generate_prime_from;

use crate::harness::{self, Expectation, Hex, TestFile};
use crate::require_vectors;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Key {
    public_exponent: Hex,
    prime1: Option<Hex>,
    prime2: Option<Hex>,
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
    assert!(
        used >= 17 * len && used.is_multiple_of(len),
        "{name}: {used}"
    );
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
    // Miller–Rabin's exponentiations are this test's time: shared among as
    // many threads as the machine runs at once.
    let workers = std::thread::available_parallelism().map_or(1, |n| n.get());
    let next = AtomicUsize::new(0);
    std::thread::scope(|s| {
        for _ in 0..workers.min(primes.len()) {
            s.spawn(|| {
                while let Some(x) = primes.get(next.fetch_add(1, Ordering::Relaxed)) {
                    check_prime(&x.name, &x.p, &x.q, &x.e);
                }
            });
        }
    });
}

#[test]
fn rsa_keygen_composites() {
    require_vectors!();
    let file: TestFile<PrimalityGroup, PrimalityCase> = harness::load("primality_test.json");
    let mut checked = 0;
    for (_, t) in file.tests() {
        let v = &t.case.value.0;
        // A negative number has its top bit set; a positive one with its
        // top bit set has a zero byte before it.
        let x = trim(v);
        if v.first() != Some(&0) || !candidate(x) {
            continue;
        }
        let r = generate_prime_from(8 * x.len(), &[1], None, &then_random(x));
        // A valid number (a prime) is the first candidate, accepted; an
        // invalid one is rejected.
        let accepted = r.is_ok_and(|(p, _)| p == x);
        let expected = t.result == Expectation::Valid;
        assert!(
            t.result == Expectation::Acceptable || accepted == expected,
            "tcId {}",
            t.tc_id
        );
        checked += 1;
    }
    assert!(checked > 0);
}
