//! RSA private keys loaded from their components: from `(n, e, d, p, q)`
//! (the CRT values by `vg_rsa_crt_values`) and from `(n, e, d)` (the primes
//! recovered by `vg_rsa_recover_primes_det` on i686, and if it does not find
//! them, by `vg_rsa_recover_primes`), with the two-prime private keys of
//! the RSA test vector files (`rsa_*_test.json`; keys with other primes are
//! skipped).
//!
//! On a few inputs, RSAEP of each key's result gives back the input, and the
//! keys loaded from `(n, e, d, p, q)` and from the CRT values the file gives
//! agree with it. Every key passes `check_key`, and fails it with `d`, `dP`,
//! `dQ` or `qInv` changed by one; with `dP`, `dQ` or `qInv` changed it does
//! not load, as loading checks them. (Every key's public exponent, 3 or 65537,
//! is within BoringSSL's limits.)
//!
//! From each prime `p` and its CRT exponent `dP = e⁻¹ mod (p - 1)`, the key
//! `(3 p, e, dP)` (`λ(3 p) = p - 1`) loads from its components too: one of
//! its primes is 3, so `p + q - 1` is about `n / 3` and Appendix C.2's
//! method, which `from_components` tries first on i686, does not find them
//! (`vg_rsa_recover_primes_det` returns 0 on every such key here), and
//! Appendix C.1's does.

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

use std::collections::BTreeMap;

use verified_garbage::rsa::{PrivateKey, PublicKey};

use super::harness::{self, Count, Fields, TestFile};
use super::schema::{RsaAnyKeyGroup, RsaAnyPrivateKey};
use crate::bytes::trim_zeros;
use crate::require_vectors;

/// `key`'s operation on `x`, which must succeed.
fn private(key: &PrivateKey, x: &[u8]) -> Vec<u8> {
    let mut out = vec![0; x.len()];
    key.private_op(x, &mut out).unwrap();
    out
}

/// `3 x`, big-endian, without leading zeros.
fn triple(x: &[u8]) -> Vec<u8> {
    let mut carry = 0u16;
    let mut r: Vec<u8> = trim_zeros(x)
        .iter()
        .rev()
        .map(|&b| {
            let v = 3 * u16::from(b) + carry;
            carry = v >> 8;
            v as u8
        })
        .collect();
    r.push(carry as u8);
    r.reverse();
    trim_zeros(&r).to_vec()
}

/// Whether Appendix C.2's method (`vg_rsa_recover_primes_det`) does not
/// find the primes of `(n, e, d)`.
#[cfg(target_arch = "x86")]
fn det_fails(n: &[u8], e: &[u8], d: &[u8]) -> bool {
    let (e, d) = (trim_zeros(e), trim_zeros(d));
    let k = n.len();
    let (mut p, mut q) = (vec![0; k], vec![0; k]);
    let mut scratch = vec![0u64; 16 * k + 32];
    // SAFETY: each pointer is valid for its length (`p`, `q` and `scratch`
    // for writes), and none overlaps another, as they are distinct
    // allocations; `n` is a modulus of 64 to 1024 bytes, `1 ≤ e_len ≤ 8`,
    // `1 ≤ d_len ≤ n_len`, `p_len = q_len = n_len` and
    // `scratch_len = 16 n_len + 32`.
    let r = unsafe {
        verified_garbage_asm_x86::rsa::vg_rsa_recover_primes_det(
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
            scratch.as_mut_ptr(),
            scratch.len(),
        )
    };
    r == 0
}

/// The key `(3 p, e, dP)` of the prime `p` (of the file `name`) and its CRT
/// exponent `dP` loads from its components, by Appendix C.1 where
/// Appendix C.2 does not find its primes.
fn check_triple(name: &str, e: &[u8], p: &[u8], dp: &[u8]) {
    let n = triple(p);
    #[cfg(target_arch = "x86")]
    assert!(det_fails(&n, e, dp), "{name}: Appendix C.2 on 3 p");
    let key =
        PrivateKey::from_components(&n, e, dp).unwrap_or_else(|err| panic!("{name}: 3 p: {err}"));
    assert!(key.check_key(), "{name}: 3 p");
    // RSAEP of the result for 2 gives it back.
    let len = n.len();
    let mut x = vec![0; len];
    x[len - 1] = 2;
    let out = private(&key, &x);
    let mut back = vec![0; len];
    PublicKey::new(&n, e)
        .unwrap()
        .public_op(&out, &mut back)
        .unwrap();
    assert_eq!(back, x, "{name}: 3 p");
}

/// Checks the key `k` of the file `name`. Returns whether it had its primes.
fn check_key(name: &str, k: &RsaAnyPrivateKey) -> bool {
    let n = trim_zeros(&k.modulus.as_ref().unwrap().0);
    let (e, d) = (
        &k.public_exponent.0,
        &k.private_exponent.as_ref().unwrap().0,
    );
    let len = n.len();
    let public = PublicKey::new(n, e).unwrap();
    // 2, and `n` with its top byte halved, both below `n`.
    let mut x = vec![0; len];
    x[len - 1] = 2;
    let mut y = n.to_vec();
    y[0] >>= 1;
    let (p, q, dp, dq, qi) = (
        &k.prime1,
        &k.prime2,
        &k.exponent1,
        &k.exponent2,
        &k.coefficient,
    );
    // The key from `(n, e, d)`.
    let key = PrivateKey::from_components(n, e, d).unwrap_or_else(|err| panic!("{name}: {err}"));
    assert!(key.check_key(), "{name}: from_components");
    assert_eq!(key.modulus_len(), len, "{name}");
    // RSAEP of each result gives back the input.
    let expect: Vec<Vec<u8>> = [&x, &y]
        .iter()
        .map(|v| {
            let out = private(&key, v);
            let mut back = vec![0; len];
            public.public_op(&out, &mut back).unwrap();
            assert_eq!(&back, *v, "{name}");
            out
        })
        .collect();
    let check = |key: &PrivateKey, how: &str| {
        assert_eq!(private(key, &x), expect[0], "{name}: {how}");
        assert_eq!(private(key, &y), expect[1], "{name}: {how}");
        assert!(key.check_key(), "{name}: {how}");
    };
    let (Some(p), Some(q), Some(dp), Some(dq), Some(qi)) = (p, q, dp, dq, qi) else {
        return false;
    };
    let key =
        PrivateKey::from_primes(n, e, d, &p.0, &q.0).unwrap_or_else(|err| panic!("{name}: {err}"));
    check(&key, "from_primes");
    let key = PrivateKey::from_crt(n, e, d, &p.0, &q.0, &dp.0, &dq.0, &qi.0).unwrap();
    check(&key, "from_crt");
    check_triple(name, e, &p.0, &dp.0);
    check_triple(name, e, &q.0, &dq.0);
    // `d`, `dP`, `dQ` or `qInv` with its low bit flipped: `e d`, `e dP` and
    // `e dQ` change by `e` and `q qInv` by `q`, none a multiple of the
    // modulus they are checked against.
    let flip = |x: &[u8]| {
        let mut x = x.to_vec();
        *x.last_mut().unwrap() ^= 1;
        x
    };
    for (i, how) in ["d", "dP", "dQ", "qInv"].iter().enumerate() {
        let mut v = [d.clone(), dp.0.clone(), dq.0.clone(), qi.0.clone()];
        v[i] = flip(&v[i]);
        let key = PrivateKey::from_crt(n, e, &v[0], &p.0, &q.0, &v[1], &v[2], &v[3]);
        // Loading checks the CRT values, not `d`.
        assert_eq!(key.is_ok(), i == 0, "{name}: {how}");
        assert!(!key.is_ok_and(|key| key.check_key()), "{name}: {how}");
    }
    true
}

#[test]
fn rsa_keys_from_components() {
    require_vectors!();
    // Each two-prime key once, with the first file that has it.
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
            assert!(
                k.modulus.is_some() && k.private_exponent.is_some(),
                "{name}"
            );
            let n = &k.modulus.as_ref().unwrap().0;
            if k.other_prime_infos.is_none() && harness::rsa_key_tested(n) {
                keys.entry(n.clone()).or_insert((name.clone(), k));
            }
        }
    }
    let keys: Vec<(String, RsaAnyPrivateKey)> = keys.into_values().collect();
    let (with_primes, without_primes) = (Count::default(), Count::default());
    harness::par_each(&keys, |(name, k)| {
        if check_key(name, k) {
            with_primes.add();
        } else {
            without_primes.add();
        }
    });
    assert!(with_primes.get() > 0 && without_primes.get() > 0);
}
