//! Prime generation and the key from its primes, with Wycheproof's numbers
//! (<https://github.com/C2SP/wycheproof>, read from the checkout named by
//! `WYCHEPROOF_ROOT`; if it is not set, the tests are skipped, and CI always
//! sets it) as the candidates:
//!
//! * each two-prime private key of the RSA test vector files
//!   (`rsa_*_test.json`) whose primes are as long as each other, of a length
//!   the prime search takes, with their two most significant bits set (as a
//!   candidate sets them): with the key's public exponent, each prime, given
//!   as the other prime and as the first candidate, is too close, and the
//!   key's other prime, following it (and random octets for its witnesses),
//!   is accepted. Each accepted test costs at least 16 Miller–Rabin rounds,
//!   so each prime is accepted once, in the run that also rejects the other
//!   prime as too close; and for the first key of each length the prime is
//!   also accepted with no other prime from the same octets, reading as
//!   many. (A key with one such prime only accepts it with the other prime
//!   given.)
//! * each number of `primality_test.json` of such a length and form (only
//!   composites, Carmichael numbers and worst cases for Miller–Rabin):
//!   followed by random octets, it is never the prime returned, with `e = 1`
//!   (so that only trial division and Miller–Rabin can reject it);
//! * each two-prime private key of the RSA test vector files whose primes
//!   `key_from_primes` takes, from its primes and public exponent: the key
//!   it returns has the key's `n`, `p`, `q`, `dP`, `dQ` and `qInv`, passes
//!   BoringSSL's `RSA_check_key` (it loads again with `PrivateKey::from_crt`),
//!   and has the key's `d` but where the key's `d` is not the least (all
//!   keys but one).
//!
//! The functions are the module's own, which are not public: these tests
//! are the library's, rather than in `tests/wycheproof/`.

extern crate std;

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::string::{String, ToString};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::vec::Vec;

use serde_json::Value;
use verified_garbage_test_vectors::unhex;

use super::tests::reloads;
use super::{key_from_primes, prime_from};
use crate::rsa::trim;

/// The directory of the test vector files, or `None` if `WYCHEPROOF_ROOT`
/// is not set (a relative path is relative to the crate root).
fn vectors_dir() -> Option<PathBuf> {
    let root =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(std::env::var_os("WYCHEPROOF_ROOT")?);
    let dir = root.join("testvectors_v1");
    assert!(dir.is_dir());
    Some(dir)
}

/// The test vector file `name` of `dir`.
fn load(dir: &std::path::Path, name: &str) -> Value {
    let text = std::fs::read_to_string(dir.join(name)).unwrap();
    serde_json::from_str(&text).unwrap()
}

/// The RSA test vector files of `dir`, `rsa_*_test.json`, by name.
fn rsa_files(dir: &std::path::Path) -> Vec<(String, Value)> {
    let mut names: Vec<String> = std::fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().file_name().into_string().unwrap())
        .filter(|n| n.starts_with("rsa_") && n.ends_with("_test.json"))
        .collect();
    names.sort();
    names
        .into_iter()
        .map(|n| {
            let v = load(dir, &n);
            (n, v)
        })
        .collect()
}

/// The private keys of the groups of the file `file`.
fn private_keys(file: &Value) -> impl Iterator<Item = &Value> {
    file["testGroups"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|g| g.get("privateKey").filter(|k| !k.is_null()))
}

/// Whether `key` has the field `name` (and it is not `null`).
fn field_present(key: &Value, name: &str) -> bool {
    key.get(name).is_some_and(|v| !v.is_null())
}

/// The bytes of the field `name` of `key` (a hex string), if it has it.
fn field(key: &Value, name: &str) -> Option<Vec<u8>> {
    field_present(key, name).then(|| unhex(key[name].as_str().unwrap()))
}

/// Runs `f` on each of `items`, on every core.
fn par_each<T: Sync>(items: &[T], f: impl Fn(&T) + Sync) {
    let next = AtomicUsize::new(0);
    let threads = std::thread::available_parallelism().map_or(1, |n| n.get());
    std::thread::scope(|scope| {
        for _ in 0..threads {
            scope.spawn(|| {
                while let Some(x) = items.get(next.fetch_add(1, Ordering::Relaxed)) {
                    f(x);
                }
            });
        }
    });
}

/// The most candidates the search for a prime of `bits` bits with the
/// public exponent `e` may reject (`VG.Spec.RsaKeyGen.primeLimit`).
fn limit(bits: usize, e: &[u8]) -> usize {
    if trim(e) == [3] { 8 * bits } else { 5 * bits }
}

/// Whether `x` is a candidate as the search makes it from its octets: of a
/// length it takes, with its two top bits and its low bit set.
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

/// A key's primes `p` and `q` (as long as each other), with the file it is
/// from and its public exponent.
struct Pair {
    p: Vec<u8>,
    q: Vec<u8>,
    name: String,
    e: Vec<u8>,
}

/// Checks that `prime` is accepted as the first candidate with `other`,
/// the key's other prime (as long), as the other prime and the public
/// exponent `e`: after `other` itself, too close, if `other` is a candidate;
/// and, if `alone`, with no other prime from the same octets.
fn check_prime(name: &str, prime: &[u8], other: &[u8], e: &[u8], alone: bool) {
    let len = prime.len();
    let (e, limit) = (trim(e), limit(8 * len, e));
    let rand = then_random(prime);
    // The octets `prime`'s test read, from where `prime` starts.
    let read = if candidate(other) {
        let mut after = other.to_vec();
        after.extend_from_slice(&rand);
        let (got, used) = prime_from(len, limit, e, Some(other), &after);
        assert_eq!(
            got.unwrap(),
            prime,
            "{name}: after the other prime, too close"
        );
        // The other prime, too close, reads its own octets only.
        assert!(used >= len, "{name}: {used}");
        used - len
    } else {
        let (got, used) = prime_from(len, limit, e, Some(other), &rand);
        assert_eq!(got.unwrap(), prime, "{name}: with the other prime");
        used
    };
    assert!(
        read >= 17 * len && read.is_multiple_of(len),
        "{name}: {read}"
    );
    if alone {
        let (got, used) = prime_from(len, limit, e, None, &rand);
        assert_eq!(
            (got.unwrap(), used),
            (prime.to_vec(), read),
            "{name}: alone"
        );
    }
}

#[test]
fn rsa_keygen_primes() {
    if let Some(dir) = vectors_dir() {
        primes(&dir);
    }
}

#[test]
fn rsa_keygen_composites() {
    if let Some(dir) = vectors_dir() {
        composites(&dir);
    }
}

#[test]
fn rsa_keygen_keys() {
    if let Some(dir) = vectors_dir() {
        keys(&dir);
    }
}

/// The primes of the keys of the files of `dir`.
fn primes(dir: &std::path::Path) {
    // Each key once (by its primes), with the first file that has it.
    let mut pairs: BTreeMap<(Vec<u8>, Vec<u8>), Pair> = BTreeMap::new();
    for (name, file) in rsa_files(dir) {
        for key in private_keys(&file) {
            let (Some(p), Some(q)) = (field(key, "prime1"), field(key, "prime2")) else {
                continue;
            };
            let (p, q) = (trim(&p), trim(&q));
            if p.len() == q.len() && (candidate(p) || candidate(q)) {
                pairs
                    .entry((p.to_vec(), q.to_vec()))
                    .or_insert_with(|| Pair {
                        p: p.to_vec(),
                        q: q.to_vec(),
                        name: name.clone(),
                        e: field(key, "publicExponent").unwrap(),
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
    par_each(&tests, |&(x, prime, other, alone)| {
        check_prime(&x.name, prime, other, &x.e, alone)
    });
}

/// The numbers of `primality_test.json`, of `dir`.
fn composites(dir: &std::path::Path) {
    let file = load(dir, "primality_test.json");
    let tests: Vec<&Value> = file["testGroups"]
        .as_array()
        .unwrap()
        .iter()
        .flat_map(|g| g["tests"].as_array().unwrap())
        .collect();
    let checked = AtomicUsize::new(0);
    par_each(&tests, |t| {
        let v = field(t, "value").unwrap();
        // A negative number has its top bit set; a positive one with its
        // top bit set has a zero byte before it.
        let x = trim(&v);
        if v.first() != Some(&0) || !candidate(x) {
            return;
        }
        let (r, _) = prime_from(
            x.len(),
            limit(8 * x.len(), &[1]),
            &[1],
            None,
            &then_random(x),
        );
        // A valid number (a prime) is the first candidate, accepted; an
        // invalid one is rejected.
        let accepted = r.is_ok_and(|p| p == x);
        let result = t["result"].as_str().unwrap();
        let ok = result == "acceptable" || accepted == (result == "valid");
        assert!(ok, "tcId {}", t["tcId"]);
        checked.fetch_add(1, Ordering::Relaxed);
    });
    assert!(checked.into_inner() > 0);
}

/// `x` in `len` bytes (big-endian).
fn widen(x: &[u8], len: usize) -> Vec<u8> {
    let x = trim(x);
    let mut v = std::vec![0; len - x.len()];
    v.extend_from_slice(x);
    v
}

/// Checks that `key_from_primes` makes the key `k` (of the file `name`)
/// from its primes, in either order; returns how many of the two keys have
/// its `d`.
fn check_key(name: &str, k: &Value) -> usize {
    let [p, q, n, d, dp, dq, qinv] = [
        "prime1",
        "prime2",
        "modulus",
        "privateExponent",
        "exponent1",
        "exponent2",
        "coefficient",
    ]
    .map(|f| field(k, f).unwrap());
    let (p, q) = (trim(&p), trim(&q));
    let len = p.len();
    let e = field(k, "publicExponent").unwrap();
    let e = trim(&e);
    // The key's `p` is the larger, as `key_from_primes` makes it.
    assert!(p > q, "{name}");
    let mut same_d = 0;
    for (a, b) in [(p, q), (q, p)] {
        let key = key_from_primes(e, a, b).unwrap().unwrap();
        let [kn, ke, kd, kp, kq, kdp, kdq, kqinv] = key.components();
        assert_eq!((kn, ke), (trim(&n), e), "{name}");
        assert_eq!((kp, kq), (p, q), "{name}");
        assert_eq!(kdp, widen(&dp, len), "{name}");
        assert_eq!(kdq, widen(&dq, len), "{name}");
        assert_eq!(kqinv, widen(&qinv, len), "{name}");
        assert!(reloads(&key), "{name}");
        if kd == widen(&d, 2 * len) {
            same_d += 1;
        }
    }
    same_d
}

/// The keys of the files of `dir` from their primes.
fn keys(dir: &std::path::Path) {
    // Each two-prime key with every CRT component whose primes
    // `key_from_primes` takes, once (by its `p`), with the first file that
    // has it.
    let mut keys: BTreeMap<Vec<u8>, (String, Value)> = BTreeMap::new();
    let fields = [
        "modulus",
        "privateExponent",
        "prime1",
        "prime2",
        "exponent1",
        "exponent2",
        "coefficient",
    ];
    for (name, file) in rsa_files(dir) {
        for k in private_keys(&file) {
            if field_present(k, "otherPrimeInfos") || fields.iter().any(|f| !field_present(k, f)) {
                continue;
            }
            let (p, q) = (field(k, "prime1").unwrap(), field(k, "prime2").unwrap());
            let (p, q) = (trim(&p), trim(&q));
            let len = p.len();
            if q.len() != len
                || !len.is_multiple_of(8)
                || !(32..=512).contains(&len)
                || trim(&field(k, "publicExponent").unwrap()).len() > 8
            {
                continue;
            }
            keys.entry(p.to_vec())
                .or_insert_with(|| (name.to_string(), k.clone()));
        }
    }
    let keys: Vec<(String, Value)> = keys.into_values().collect();
    let same_d = AtomicUsize::new(0);
    par_each(&keys, |(name, k)| {
        same_d.fetch_add(check_key(name, k), Ordering::Relaxed);
    });
    assert!(!keys.is_empty());
    // One key's `d` is the least plus 12 `lcm(p - 1, q - 1)`.
    assert_eq!(same_d.into_inner(), 2 * (keys.len() - 1));
}
