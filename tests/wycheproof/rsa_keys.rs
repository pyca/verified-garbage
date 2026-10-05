//! RSA private keys loaded from their components: from `(n, e, d, p, q)`
//! (the CRT values by `vg_rsa_crt_values`) and from `(n, e, d)` (the primes
//! recovered by `vg_rsa_recover_primes`), with the two-prime private keys of
//! the RSA test vector files (`rsa_*_test.json`; keys with other primes are
//! skipped).
//!
//! Each key's operation is `x^d mod n` (by the public-key operation with `d`
//! as the exponent) on a few inputs, as is the operation of the key loaded
//! from its CRT values when the file gives them.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering};

use serde::Deserialize;
use verified_garbage::rsa::{PrivateKey, PublicKey};

use crate::harness::{self, Hex, TestFile};
use crate::require_vectors;

#[derive(Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
struct Key {
    modulus: Hex,
    private_exponent: Hex,
    public_exponent: Hex,
    prime1: Option<Hex>,
    prime2: Option<Hex>,
    exponent1: Option<Hex>,
    exponent2: Option<Hex>,
    coefficient: Option<Hex>,
    other_prime_infos: Option<serde::de::IgnoredAny>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Group {
    private_key: Option<Key>,
}

#[derive(Deserialize)]
struct Case {}

/// `x` without its leading zero bytes (the vectors write numbers in DER's
/// form, with a zero byte before a top bit that is set).
fn trim(x: &[u8]) -> &[u8] {
    &x[x.iter().take_while(|&&b| b == 0).count()..]
}

/// `key`'s operation on `x`, which must succeed.
fn private(key: &PrivateKey, x: &[u8]) -> Vec<u8> {
    let mut out = vec![0; x.len()];
    key.private_op(x, &mut out).unwrap();
    out
}

/// Checks the key `k` of the file `name`. Returns whether it had its primes.
fn check_key(name: &str, k: &Key) -> bool {
    let n = trim(&k.modulus.0);
    let (e, d) = (&k.public_exponent.0, &k.private_exponent.0);
    let len = n.len();
    let by_d = PublicKey::new(n, trim(d)).unwrap();
    // 2, and `n` with its top byte halved, both below `n`.
    let mut x = vec![0; len];
    x[len - 1] = 2;
    let mut y = n.to_vec();
    y[0] >>= 1;
    let expect: Vec<Vec<u8>> = [&x, &y]
        .iter()
        .map(|v| {
            let mut out = vec![0; len];
            by_d.public_op(v, &mut out).unwrap();
            out
        })
        .collect();
    let check = |key: &PrivateKey, how: &str| {
        assert_eq!(key.modulus_len(), len, "{name}: {how}");
        assert_eq!(private(key, &x), expect[0], "{name}: {how}");
        assert_eq!(private(key, &y), expect[1], "{name}: {how}");
    };
    let key = PrivateKey::from_components(n, e, d).unwrap_or_else(|err| panic!("{name}: {err}"));
    check(&key, "from_components");
    let (Some(p), Some(q), Some(dp), Some(dq), Some(qi)) = (
        &k.prime1,
        &k.prime2,
        &k.exponent1,
        &k.exponent2,
        &k.coefficient,
    ) else {
        return false;
    };
    let key =
        PrivateKey::from_primes(n, e, d, &p.0, &q.0).unwrap_or_else(|err| panic!("{name}: {err}"));
    check(&key, "from_primes");
    let key = PrivateKey::from_crt(n, &p.0, &q.0, &dp.0, &dq.0, &qi.0).unwrap();
    check(&key, "from_crt");
    true
}

#[test]
fn rsa_keys_from_components() {
    require_vectors!();
    // Each two-prime key once, with the first file that has it.
    let mut keys: BTreeMap<Vec<u8>, (String, Key)> = BTreeMap::new();
    for name in harness::all_files().unwrap() {
        if !(name.starts_with("rsa_") && name.ends_with("_test.json")) {
            continue;
        }
        let file: TestFile<Group, Case> = harness::load(&name);
        for group in file.test_groups {
            if let Some(k) = group.params.private_key
                && k.other_prime_infos.is_none()
            {
                keys.entry(k.modulus.0.clone()).or_insert((name.clone(), k));
            }
        }
    }
    let keys: Vec<(String, Key)> = keys.into_values().collect();
    // The recoveries are most of this test's time: shared among as many
    // threads as the machine runs at once.
    let workers = std::thread::available_parallelism().map_or(1, |n| n.get());
    let next = AtomicUsize::new(0);
    let with_primes = AtomicUsize::new(0);
    std::thread::scope(|s| {
        for _ in 0..workers.min(keys.len()) {
            s.spawn(|| {
                while let Some((name, k)) = keys.get(next.fetch_add(1, Ordering::Relaxed)) {
                    if check_key(name, k) {
                        with_primes.fetch_add(1, Ordering::Relaxed);
                    }
                }
            });
        }
    });
    let with_primes = with_primes.into_inner();
    assert!(with_primes > 0 && with_primes < keys.len());
}
