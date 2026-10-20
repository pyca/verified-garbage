//! Throughput of each public API, next to the same operation in OpenSSL
//! (through rust-openssl) and, where it has one, in aws-lc-rs, at a few
//! message sizes.
//!
//! Every benchmark is one complete operation (setup included), as a caller
//! of either library would do it. Benchmark ids are
//! `<primitive>/<library>/<bytes>`; `ci/bench_compare.py` relies on this.
//!
//! Each algorithm's benchmarks are in a module of their own, whose `bench`
//! runs them (and does nothing on architectures the algorithm doesn't
//! support yet), so that adding one adds a file.

use std::hint::black_box;

use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use openssl::hash::{MessageDigest, hash};
use openssl::pkey::PKey;
use openssl::sign::Signer;

mod aes_cbc;
mod aes_ccm;
mod aes_cfb;
mod aes_cfb8;
mod aes_ctr;
mod aes_ecb;
mod aes_gcm;
mod aes_gcm_siv;
mod aes_ocb;
mod aes_ofb;
mod aes_siv;
mod aes_xts;
mod argon2;
mod blake2b;
mod blake2s;
mod blowfish_cbc;
mod blowfish_cfb;
mod blowfish_ecb;
mod blowfish_ofb;
mod camellia_cbc;
mod camellia_cfb;
mod camellia_ctr;
mod camellia_ecb;
mod camellia_ofb;
mod cast5_cbc;
mod cast5_cfb;
mod cast5_ecb;
mod cast5_ofb;
mod chacha20;
mod chacha20poly1305;
mod cmac_aes;
mod cmac_triple_des;
mod dsa;
mod dsa_parameters;
mod ecdh_brainpoolp256r1;
mod ecdh_brainpoolp384r1;
mod ecdh_brainpoolp512r1;
mod ecdh_p192;
mod ecdh_p224;
mod ecdh_p256;
mod ecdh_p384;
mod ecdh_p521;
mod ecdh_secp256k1;
mod ecdsa_brainpoolp256r1;
mod ecdsa_brainpoolp384r1;
mod ecdsa_brainpoolp512r1;
mod ecdsa_p192;
mod ecdsa_p224;
mod ecdsa_p256;
mod ecdsa_p384;
mod ecdsa_p521;
mod ecdsa_secp256k1;
mod ed25519;
mod ed448;
mod ffdh;
mod hmac_md5;
mod hmac_sha1;
mod hmac_sha224;
mod hmac_sha256;
mod hmac_sha384;
mod hmac_sha512;
mod hmac_sha512_224;
mod hmac_sha512_256;
mod idea_cbc;
mod idea_cfb;
mod idea_ecb;
mod idea_ofb;
mod md5;
mod mldsa44;
mod mldsa65;
mod mldsa87;
mod mlkem;
mod mlkem1024;
mod mlkem768;
mod pbkdf2_md5;
mod pbkdf2_sha1;
mod pbkdf2_sha224;
mod pbkdf2_sha256;
mod pbkdf2_sha384;
mod pbkdf2_sha512;
mod pbkdf2_sha512_224;
mod pbkdf2_sha512_256;
mod poly1305;
mod rc2_cbc;
mod rc4;
mod rsa;
mod rsa_keygen;
mod rsa_oaep;
mod rsa_pkcs1_enc;
mod rsa_pkcs1_sig;
mod rsa_pss;
mod rsa_public;
mod scrypt;
mod seed_cbc;
mod seed_cfb;
mod seed_ecb;
mod seed_ofb;
mod sha1;
mod sha224;
mod sha256;
mod sha3;
mod sha384;
mod sha512;
mod sha512_224;
mod sha512_256;
mod sm3;
mod sm4_cbc;
mod sm4_cfb;
mod sm4_ctr;
mod sm4_ecb;
mod sm4_ofb;
mod triple_des_cbc;
mod triple_des_cfb;
mod triple_des_cfb8;
mod triple_des_ecb;
mod triple_des_ofb;
mod x25519;
mod x448;

const SIZES: [usize; 3] = [64, 1024, 16384];

/// A buffer of `len` bytes for an operation in place, into which each
/// iteration first copies `source`.
///
/// Its first byte is 2 KiB past `source`'s modulo 4 KiB. Two `Vec`s of the
/// same size allocated one after the other start a few bytes apart modulo
/// 4 KiB. At 16 KiB, glibc copies with `rep movsb`, which on Zen 3 (EPYC
/// 7763) is 20 to 40 times slower at that distance (5.4 µs where other CPUs
/// take 0.1–0.3 µs). That made every such benchmark measure the copy rather
/// than the library.
pub(crate) struct InPlace {
    storage: Vec<u8>,
    start: usize,
    len: usize,
}

impl InPlace {
    pub(crate) fn new(len: usize, source: &[u8]) -> Self {
        let storage = vec![0; len + 4096];
        let start =
            (source.as_ptr() as usize + 2048).wrapping_sub(storage.as_ptr() as usize) % 4096;
        Self {
            storage,
            start,
            len,
        }
    }
}

impl std::ops::Deref for InPlace {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        &self.storage[self.start..self.start + self.len]
    }
}

impl std::ops::DerefMut for InPlace {
    fn deref_mut(&mut self) -> &mut [u8] {
        &mut self.storage[self.start..self.start + self.len]
    }
}

const VG: &str = "verified-garbage";
const OPENSSL: &str = "openssl";
const AWS_LC: &str = "aws-lc-rs";

/// Benchmarks the hash `vg` against OpenSSL's `md` and, if it has the hash,
/// aws-lc-rs's `aws_lc`.
pub(crate) fn hash_group<const N: usize>(
    c: &mut Criterion,
    name: &str,
    vg: fn(&[u8]) -> [u8; N],
    md: MessageDigest,
    aws_lc: Option<&'static aws_lc_rs::digest::Algorithm>,
) {
    let mut g = c.benchmark_group(name);
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| vg(black_box(&data)))
        });
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| hash(md, black_box(&data)).unwrap())
        });
        if let Some(alg) = aws_lc {
            assert_eq!(
                aws_lc_rs::digest::digest(alg, &data).as_ref(),
                &vg(&data)[..]
            );
            g.bench_function(BenchmarkId::new(AWS_LC, size), |b| {
                b.iter(|| aws_lc_rs::digest::digest(alg, black_box(&data)))
            });
        }
    }
    g.finish();
}

/// Benchmarks checking the digest of the data with `vg`, which computes it
/// and compares it with the expected one in constant time, against
/// OpenSSL's `md` and `CRYPTO_memcmp`.
pub(crate) fn hash_verify_group<const N: usize>(
    c: &mut Criterion,
    name: &str,
    digest: fn(&[u8]) -> [u8; N],
    vg: fn(&[u8], &[u8]) -> bool,
    md: MessageDigest,
) {
    let mut g = c.benchmark_group(name);
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        let expected = digest(&data);
        assert_eq!(hash(md, &data).unwrap()[..], expected[..]);
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| assert!(vg(black_box(&data), black_box(&expected))))
        });
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let d = hash(md, black_box(&data)).unwrap();
                assert!(openssl::memcmp::eq(&d, black_box(&expected)))
            })
        });
    }
    g.finish();
}

/// Benchmarks HMAC with the hash of `vg` and `md` (32-byte key) against
/// OpenSSL's and, if it has the hash, aws-lc-rs's `aws_lc`. aws-lc-rs makes
/// its `hmac::Key`, which keys the hash, in each iteration, as OpenSSL makes
/// its `Signer`.
pub(crate) fn hmac_group<O: AsRef<[u8]>>(
    c: &mut Criterion,
    name: &str,
    vg: fn(&[u8], &[u8]) -> O,
    md: MessageDigest,
    aws_lc: Option<aws_lc_rs::hmac::Algorithm>,
) {
    let key = [0x0b; 32];
    let pkey = PKey::hmac(&key).unwrap();
    let mut g = c.benchmark_group(name);
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| vg(black_box(&key), black_box(&data)))
        });
        let mut out = [0u8; 64];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut s = Signer::new(md, &pkey).unwrap();
                s.sign_oneshot(&mut out, black_box(&data)).unwrap()
            })
        });
        if let Some(alg) = aws_lc {
            use aws_lc_rs::hmac;
            let tag = hmac::sign(&hmac::Key::new(alg, &key), &data);
            assert_eq!(tag.as_ref(), vg(&key, &data).as_ref());
            g.bench_function(BenchmarkId::new(AWS_LC, size), |b| {
                b.iter(|| hmac::sign(&hmac::Key::new(alg, black_box(&key)), black_box(&data)))
            });
        }
    }
    g.finish();
}

/// Benchmarks checking an HMAC with the hash `H` and `md` (32-byte key)
/// against OpenSSL's and, if it has the hash, aws-lc-rs's `aws_lc`:
/// computing the MAC of the data and comparing it with the expected one in
/// constant time (`Hmac::verify`; OpenSSL's `CRYPTO_memcmp`; aws-lc-rs's
/// `hmac::verify`, making its key in each iteration).
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
pub(crate) fn hmac_verify_group<H: verified_garbage::hmac::HmacHash>(
    c: &mut Criterion,
    name: &str,
    md: MessageDigest,
    aws_lc: Option<aws_lc_rs::hmac::Algorithm>,
) {
    use verified_garbage::hmac::Hmac;
    let key = [0x0b; 32];
    let pkey = PKey::hmac(&key).unwrap();
    let mut g = c.benchmark_group(name);
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        let mac = Hmac::<H>::mac(&key, &data);
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let mut h = Hmac::<H>::new(black_box(&key));
                h.update(black_box(&data));
                h.verify(black_box(mac.as_ref())).unwrap()
            })
        });
        let mut out = [0u8; 64];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut s = Signer::new(md, &pkey).unwrap();
                let n = s.sign_oneshot(&mut out, black_box(&data)).unwrap();
                assert!(openssl::memcmp::eq(&out[..n], black_box(mac.as_ref())))
            })
        });
        if let Some(alg) = aws_lc {
            use aws_lc_rs::hmac;
            hmac::verify(&hmac::Key::new(alg, &key), &data, mac.as_ref()).unwrap();
            g.bench_function(BenchmarkId::new(AWS_LC, size), |b| {
                b.iter(|| {
                    let k = hmac::Key::new(alg, black_box(&key));
                    hmac::verify(&k, black_box(&data), black_box(mac.as_ref())).unwrap()
                })
            });
        }
    }
    g.finish();
}

/// Benchmarks PBKDF2 with the hash of `vg` and `md` against OpenSSL's and,
/// if it has the hash, aws-lc-rs's `aws_lc`, of a 32-byte password, deriving
/// `len` bytes (a digest), with the sizes as the iteration counts.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
pub(crate) fn pbkdf2_group(
    c: &mut Criterion,
    name: &str,
    vg: fn(&[u8], &[u8], std::num::NonZeroU32, &mut [u8]),
    md: MessageDigest,
    aws_lc: Option<aws_lc_rs::pbkdf2::Algorithm>,
    len: usize,
) {
    let password = [0x0b; 32];
    let salt = [0x5a; 16];
    let mut g = c.benchmark_group(name);
    for iterations in SIZES {
        g.throughput(Throughput::Elements(iterations as u64));
        let mut out = vec![0u8; len];
        let n = std::num::NonZeroU32::new(iterations as u32).unwrap();
        g.bench_function(BenchmarkId::new(VG, iterations), |b| {
            b.iter(|| vg(black_box(&password), black_box(&salt), n, &mut out))
        });
        g.bench_function(BenchmarkId::new(OPENSSL, iterations), |b| {
            b.iter(|| {
                openssl::pkcs5::pbkdf2_hmac(
                    black_box(&password),
                    black_box(&salt),
                    iterations,
                    md,
                    &mut out,
                )
                .unwrap()
            })
        });
        if let Some(alg) = aws_lc {
            let mut expected = vec![0u8; len];
            vg(&password, &salt, n, &mut expected);
            aws_lc_rs::pbkdf2::derive(alg, n, &salt, &password, &mut out);
            assert_eq!(out, expected);
            g.bench_function(BenchmarkId::new(AWS_LC, iterations), |b| {
                b.iter(|| {
                    aws_lc_rs::pbkdf2::derive(
                        alg,
                        n,
                        black_box(&salt),
                        black_box(&password),
                        &mut out,
                    )
                })
            });
        }
    }
    g.finish();
}

/// Each algorithm's `bench`, with its name (its file's) and the library
/// modules whose code it runs (its `USES`, which `ci/bench_arches.py` reads).
type Bench = (&'static str, &'static [&'static str], fn(&mut Criterion));

/// `BENCHES`, from each benchmark's `USES` and `bench`, one per line (as
/// `ci/bench_arches.py` reads them), named by its module.
macro_rules! benches {
    ($(($name:ident::USES, $bench:ident::bench),)*) => {
        const BENCHES: &[Bench] = &[$((stringify!($name), $name::USES, $bench::bench)),*];
    };
}

benches! {
    (aes_cbc::USES, aes_cbc::bench),
    (aes_ccm::USES, aes_ccm::bench),
    (aes_cfb::USES, aes_cfb::bench),
    (aes_cfb8::USES, aes_cfb8::bench),
    (aes_ctr::USES, aes_ctr::bench),
    (aes_ecb::USES, aes_ecb::bench),
    (aes_gcm::USES, aes_gcm::bench),
    (aes_gcm_siv::USES, aes_gcm_siv::bench),
    (aes_ocb::USES, aes_ocb::bench),
    (aes_ofb::USES, aes_ofb::bench),
    (aes_siv::USES, aes_siv::bench),
    (aes_xts::USES, aes_xts::bench),
    (blake2b::USES, blake2b::bench),
    (blake2s::USES, blake2s::bench),
    (blowfish_cbc::USES, blowfish_cbc::bench),
    (blowfish_cfb::USES, blowfish_cfb::bench),
    (blowfish_ecb::USES, blowfish_ecb::bench),
    (blowfish_ofb::USES, blowfish_ofb::bench),
    (camellia_cbc::USES, camellia_cbc::bench),
    (camellia_cfb::USES, camellia_cfb::bench),
    (camellia_ctr::USES, camellia_ctr::bench),
    (camellia_ecb::USES, camellia_ecb::bench),
    (camellia_ofb::USES, camellia_ofb::bench),
    (cast5_cbc::USES, cast5_cbc::bench),
    (cast5_cfb::USES, cast5_cfb::bench),
    (cast5_ecb::USES, cast5_ecb::bench),
    (cast5_ofb::USES, cast5_ofb::bench),
    (chacha20::USES, chacha20::bench),
    (chacha20poly1305::USES, chacha20poly1305::bench),
    (cmac_aes::USES, cmac_aes::bench),
    (cmac_triple_des::USES, cmac_triple_des::bench),
    (hmac_md5::USES, hmac_md5::bench),
    (hmac_sha1::USES, hmac_sha1::bench),
    (hmac_sha224::USES, hmac_sha224::bench),
    (hmac_sha256::USES, hmac_sha256::bench),
    (hmac_sha384::USES, hmac_sha384::bench),
    (hmac_sha512::USES, hmac_sha512::bench),
    (hmac_sha512_224::USES, hmac_sha512_224::bench),
    (hmac_sha512_256::USES, hmac_sha512_256::bench),
    (idea_cbc::USES, idea_cbc::bench),
    (idea_cfb::USES, idea_cfb::bench),
    (idea_ecb::USES, idea_ecb::bench),
    (idea_ofb::USES, idea_ofb::bench),
    (md5::USES, md5::bench),
    (mldsa44::USES, mldsa44::bench),
    (mldsa65::USES, mldsa65::bench),
    (mldsa87::USES, mldsa87::bench),
    (mlkem1024::USES, mlkem1024::bench),
    (mlkem768::USES, mlkem768::bench),
    (pbkdf2_md5::USES, pbkdf2_md5::bench),
    (pbkdf2_sha1::USES, pbkdf2_sha1::bench),
    (pbkdf2_sha224::USES, pbkdf2_sha224::bench),
    (pbkdf2_sha256::USES, pbkdf2_sha256::bench),
    (pbkdf2_sha384::USES, pbkdf2_sha384::bench),
    (pbkdf2_sha512::USES, pbkdf2_sha512::bench),
    (pbkdf2_sha512_224::USES, pbkdf2_sha512_224::bench),
    (pbkdf2_sha512_256::USES, pbkdf2_sha512_256::bench),
    (poly1305::USES, poly1305::bench),
    (rc2_cbc::USES, rc2_cbc::bench),
    (rc4::USES, rc4::bench),
    (rsa::USES, rsa::bench),
    (ffdh::USES, ffdh::bench),
    (rsa_keygen::USES, rsa_keygen::bench),
    (rsa_oaep::USES, rsa_oaep::bench),
    (rsa_pkcs1_enc::USES, rsa_pkcs1_enc::bench),
    (rsa_pkcs1_sig::USES, rsa_pkcs1_sig::bench),
    (rsa_pss::USES, rsa_pss::bench),
    (rsa_public::USES, rsa_public::bench),
    (triple_des_cbc::USES, triple_des_cbc::bench),
    (triple_des_cfb::USES, triple_des_cfb::bench),
    (triple_des_cfb8::USES, triple_des_cfb8::bench),
    (triple_des_ecb::USES, triple_des_ecb::bench),
    (triple_des_ofb::USES, triple_des_ofb::bench),
    (seed_cbc::USES, seed_cbc::bench),
    (seed_cfb::USES, seed_cfb::bench),
    (seed_ecb::USES, seed_ecb::bench),
    (seed_ofb::USES, seed_ofb::bench),
    (sm4_cbc::USES, sm4_cbc::bench),
    (sm4_cfb::USES, sm4_cfb::bench),
    (sm4_ctr::USES, sm4_ctr::bench),
    (sm4_ecb::USES, sm4_ecb::bench),
    (sm4_ofb::USES, sm4_ofb::bench),
    (argon2::USES, argon2::bench),
    (scrypt::USES, scrypt::bench),
    (sha1::USES, sha1::bench),
    (sha224::USES, sha224::bench),
    (sha256::USES, sha256::bench),
    (sha3::USES, sha3::bench),
    (sha384::USES, sha384::bench),
    (sha512::USES, sha512::bench),
    (sha512_224::USES, sha512_224::bench),
    (sha512_256::USES, sha512_256::bench),
    (sm3::USES, sm3::bench),
    (x25519::USES, x25519::bench),
    (x448::USES, x448::bench),
    (ed25519::USES, ed25519::bench),
    (ed448::USES, ed448::bench),
    (ecdsa_p192::USES, ecdsa_p192::bench),
    (ecdsa_p224::USES, ecdsa_p224::bench),
    (ecdsa_secp256k1::USES, ecdsa_secp256k1::bench),
    (ecdsa_brainpoolp256r1::USES, ecdsa_brainpoolp256r1::bench),
    (ecdsa_brainpoolp384r1::USES, ecdsa_brainpoolp384r1::bench),
    (ecdsa_brainpoolp512r1::USES, ecdsa_brainpoolp512r1::bench),
    (dsa::USES, dsa::bench),
    (dsa_parameters::USES, dsa_parameters::bench),
    (ecdsa_p256::USES, ecdsa_p256::bench),
    (ecdsa_p384::USES, ecdsa_p384::bench),
    (ecdsa_p521::USES, ecdsa_p521::bench),
    (ecdh_p192::USES, ecdh_p192::bench),
    (ecdh_p224::USES, ecdh_p224::bench),
    (ecdh_secp256k1::USES, ecdh_secp256k1::bench),
    (ecdh_brainpoolp256r1::USES, ecdh_brainpoolp256r1::bench),
    (ecdh_brainpoolp384r1::USES, ecdh_brainpoolp384r1::bench),
    (ecdh_brainpoolp512r1::USES, ecdh_brainpoolp512r1::bench),
    (ecdh_p256::USES, ecdh_p256::bench),
    (ecdh_p384::USES, ecdh_p384::bench),
    (ecdh_p521::USES, ecdh_p521::bench),
}

/// Runs the benchmarks that use any of the modules in `$VG_BENCH_MODULES`
/// (space-separated), or every benchmark if it is unset or empty. The CI
/// selector requests all benchmarks for shared or unknown dependencies. An
/// unknown explicit module is an error, rather than silently running everything.
///
/// `$VG_BENCHES` (space-separated names of `BENCHES`) narrows them to those
/// benchmarks, so that `ci/bench_compare.py` can run one at a time, base and
/// head alternately, setting up (generating keys, …) only that one. With
/// `$VG_BENCH_NAMES` set, each benchmark's name is printed before it, as
/// `<name>: bench`, so that `--list` tells which one has each group.
fn all(c: &mut Criterion) {
    let modules = std::env::var("VG_BENCH_MODULES").unwrap_or_default();
    let modules: Vec<&str> = modules.split_whitespace().collect();
    let used = |m: &&str| BENCHES.iter().any(|(_, uses, _)| uses.contains(m));
    assert!(
        modules.iter().all(used),
        "VG_BENCH_MODULES names a module absent from the benchmark registry"
    );
    let names = std::env::var("VG_BENCHES").unwrap_or_default();
    let names: Vec<&str> = names.split_whitespace().collect();
    assert!(
        names
            .iter()
            .all(|n| BENCHES.iter().any(|(name, _, _)| name == n)),
        "VG_BENCHES names a benchmark absent from the registry"
    );
    let announce = std::env::var_os("VG_BENCH_NAMES").is_some();
    for (name, uses, bench) in BENCHES {
        if (modules.is_empty() || uses.iter().any(|u| modules.contains(u)))
            && (names.is_empty() || names.contains(name))
        {
            if announce {
                println!("{name}: bench");
            }
            bench(c);
        }
    }
}

criterion_group!(benches, all);
criterion_main!(benches);
