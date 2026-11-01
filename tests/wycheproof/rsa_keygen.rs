//! RSA prime generation (`verified_garbage::rsa_keygen`), with the octets of
//! known numbers as the first candidate:
//!
//! * each two-prime private key of the RSA test vector files
//!   (`rsa_*_test.json`) whose primes are as long as each other, of a length
//!   `generate_prime_from` takes, with their two most significant bits set
//!   (as a candidate sets them): with the key's public exponent, each prime,
//!   given as the other prime and as the first candidate, is too close, and
//!   the key's other prime, following it (and random octets for its
//!   witnesses), is accepted. Each accepted test costs at least 16
//!   Miller–Rabin rounds, so each prime is accepted once, in the run that
//!   also rejects the other prime as too close; and for the first key of
//!   each length the prime is also accepted with no other prime from the
//!   same octets, reading as many. (A key with one such prime only accepts
//!   it with the other prime given.)
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
    any(
        target_arch = "x86_64",
        target_arch = "x86",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64"
    ),
    feature = "alloc"
))]

use std::collections::{BTreeMap, BTreeSet};

use crate::json_struct;
use verified_garbage::rsa_keygen::{generate_prime_from, key_from_primes};

use super::harness::{self, Count, Expectation, Fields, Hex, TestFile};
use super::schema::{RsaAnyKeyGroup, RsaAnyPrivateKey};
use crate::bytes::trim_zeros;
use crate::require_vectors;

json_struct! {
    struct PrimalityCase {
        value: Hex,
    }
}

/// A key's primes `p` and `q` (as long as each other), with the file it is
/// from and its public exponent.
struct Pair {
    p: Vec<u8>,
    q: Vec<u8>,
    name: String,
    e: Vec<u8>,
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

/// Checks that `prime` is accepted as the first candidate with `other`,
/// the key's other prime (as long), as the other prime and the public
/// exponent `e`: after `other` itself, too close, if `other` is a candidate;
/// and, if `alone`, with no other prime from the same octets.
fn check_prime(name: &str, prime: &[u8], other: &[u8], e: &[u8], alone: bool) {
    let len = prime.len();
    let bits = 8 * len;
    let rand = then_random(prime);
    // The octets `prime`'s test read, from where `prime` starts.
    let read = if candidate(other) {
        let mut after = other.to_vec();
        after.extend_from_slice(&rand);
        let (got, used) = generate_prime_from(bits, e, Some(other), &after).unwrap();
        assert_eq!(got, prime, "{name}: after the other prime, too close");
        // The other prime, too close, reads its own octets only.
        assert!(used >= len, "{name}: {used}");
        used - len
    } else {
        let (got, used) = generate_prime_from(bits, e, Some(other), &rand).unwrap();
        assert_eq!(got, prime, "{name}: with the other prime");
        used
    };
    assert!(
        read >= 17 * len && read.is_multiple_of(len),
        "{name}: {read}"
    );
    if alone {
        let (got, used) = generate_prime_from(bits, e, None, &rand).unwrap();
        assert_eq!((&got[..], used), (prime, read), "{name}: alone");
    }
}

#[test]
fn rsa_keygen_primes() {
    require_vectors!();
    // Each key once (by its primes), with the first file that has it.
    let mut pairs: BTreeMap<(Vec<u8>, Vec<u8>), Pair> = BTreeMap::new();
    for name in harness::all_files().unwrap() {
        if !(name.starts_with("rsa_") && name.ends_with("_test.json")) {
            continue;
        }
        let file: TestFile<RsaAnyKeyGroup, Fields> = harness::load(&name);
        for group in file.test_groups {
            let Some(RsaAnyPrivateKey {
                public_exponent,
                prime1: Some(p),
                prime2: Some(q),
                ..
            }) = group.params.private_key
            else {
                continue;
            };
            let (p, q) = (trim_zeros(&p.0), trim_zeros(&q.0));
            if p.len() == q.len() && (candidate(p) || candidate(q)) {
                pairs
                    .entry((p.to_vec(), q.to_vec()))
                    .or_insert_with(|| Pair {
                        p: p.to_vec(),
                        q: q.to_vec(),
                        name: name.clone(),
                        e: public_exponent.0.clone(),
                    });
            }
        }
    }
    let pairs: Vec<Pair> = pairs.into_values().collect();
    assert!(!pairs.is_empty());
    // Each test: the key, the prime accepted, the other prime, and whether
    // the prime is also accepted alone (the first test of each length).
    let mut tests: Vec<(&Pair, &[u8], &[u8], bool)> = Vec::new();
    let mut lengths = BTreeSet::new();
    for x in &pairs {
        for (prime, other) in [(&x.p, &x.q), (&x.q, &x.p)] {
            if candidate(prime) {
                tests.push((x, prime, other, lengths.insert(prime.len())));
            }
        }
    }
    harness::par_each(&tests, |&(x, prime, other, alone)| {
        check_prime(&x.name, prime, other, &x.e, alone)
    });
}

#[test]
fn rsa_keygen_composites() {
    require_vectors!();
    let file: TestFile<Fields, PrimalityCase> = harness::load("primality_test.json");
    let checked = Count::default();
    file.par_tests(|_, t| {
        let v = &t.case.value.0;
        // A negative number has its top bit set; a positive one with its
        // top bit set has a zero byte before it.
        let x = trim_zeros(v);
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
    let x = trim_zeros(x);
    let mut v = vec![0; len - x.len()];
    v.extend_from_slice(x);
    v
}

/// Checks that `key_from_primes` makes the key `k` (of the file `name`)
/// from its primes, in either order; returns how many of the two keys have
/// its `d`.
fn check_key(name: &str, k: &RsaAnyPrivateKey) -> usize {
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
    let (p, q) = (trim_zeros(p), trim_zeros(q));
    let len = p.len();
    let e = trim_zeros(&k.public_exponent.0);
    // The key's `p` is the larger, as `key_from_primes` makes it.
    assert!(p > q, "{name}");
    let mut same_d = 0;
    for (a, b) in [(p, q), (q, p)] {
        let key = key_from_primes(e, a, b).unwrap();
        let [kn, ke, kd, kp, kq, kdp, kdq, kqinv] = key.components();
        assert_eq!((kn, ke), (trim_zeros(n), e), "{name}");
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
    let mut keys: BTreeMap<Vec<u8>, (String, RsaAnyPrivateKey)> = BTreeMap::new();
    for name in harness::all_files().unwrap() {
        if !(name.starts_with("rsa_") && name.ends_with("_test.json")) {
            continue;
        }
        let file: TestFile<RsaAnyKeyGroup, Fields> = harness::load(&name);
        for group in file.test_groups {
            let Some(k) = group.params.private_key else {
                continue;
            };
            let RsaAnyPrivateKey {
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
            let (p, q) = (trim_zeros(&p.0), trim_zeros(&q.0));
            let len = p.len();
            if q.len() != len
                || !len.is_multiple_of(8)
                || !(32..=512).contains(&len)
                || trim_zeros(&e.0).len() > 8
            {
                continue;
            }
            keys.entry(p.to_vec()).or_insert((name.clone(), k));
        }
    }
    let keys: Vec<(String, RsaAnyPrivateKey)> = keys.into_values().collect();
    let same_d = Count::default();
    harness::par_each(&keys, |(name, k)| same_d.add_n(check_key(name, k)));
    assert!(!keys.is_empty());
    // One key's `d` is the least plus 12 `lcm(p - 1, q - 1)`.
    assert_eq!(same_d.get(), 2 * (keys.len() - 1));
}
