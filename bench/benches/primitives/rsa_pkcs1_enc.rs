//! RSAES-PKCS1-v1_5 encryption, and decryption with implicit rejection
//! (draft-irtf-cfrg-rsa-guidance-10 §7.2), of a 32-byte message.

use criterion::Criterion;

pub const USES: &[&str] = &["rsa_pkcs1_enc", "rsa", "sha256", "hmac_sha256"];

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use openssl::bn::BigNum;
    use openssl::rsa::{Padding, Rsa};
    use verified_garbage::rsa::{PrivateKey, PublicKey};
    use verified_garbage::rsa_pkcs1_enc::{decrypt, encrypt};

    use crate::{OPENSSL, VG};
    // Moduli of 2048, 3072 and 4096 bits with the exponent 65537; the ids'
    // size is the modulus' bytes. Each library loads the key once, outside
    // the measurements. Both draw a fresh padding string per encryption.
    let msg = [0x42u8; 32];
    let mut g = c.benchmark_group("rsa_pkcs1_encrypt");
    for bits in [2048, 3072, 4096] {
        let key = Rsa::generate(bits).unwrap();
        let (n, e) = (key.n().to_vec(), key.e().to_vec());
        let k = n.len();
        let vg_key = PublicKey::new(&n, &e).unwrap();
        let openssl_key = Rsa::from_public_components(
            BigNum::from_slice(&n).unwrap(),
            BigNum::from_slice(&e).unwrap(),
        )
        .unwrap();
        let mut out = vec![0; k];
        g.bench_function(BenchmarkId::new(VG, k), |b| {
            b.iter(|| encrypt(black_box(&vg_key), black_box(&msg)).unwrap())
        });
        g.bench_function(BenchmarkId::new(OPENSSL, k), |b| {
            b.iter(|| {
                black_box(&openssl_key)
                    .public_encrypt(black_box(&msg), &mut out, Padding::PKCS1)
                    .unwrap()
            })
        });
    }
    g.finish();

    // The same sizes, each library holding the private key in the CRT form
    // (OpenSSL with its default blinding and, since 3.2, its implicit
    // rejection, the same as the draft's), decrypting a valid ciphertext.
    let mut g = c.benchmark_group("rsa_pkcs1_decrypt");
    for bits in [2048, 3072, 4096] {
        let key = Rsa::generate(bits).unwrap();
        let n = key.n().to_vec();
        let k = n.len();
        let vg_key = PrivateKey::from_crt(
            &n,
            &key.e().to_vec(),
            &key.d().to_vec(),
            &key.p().unwrap().to_vec(),
            &key.q().unwrap().to_vec(),
            &key.dmp1().unwrap().to_vec(),
            &key.dmq1().unwrap().to_vec(),
            &key.iqmp().unwrap().to_vec(),
        )
        .unwrap();
        let mut ct = vec![0; k];
        key.public_encrypt(&msg, &mut ct, Padding::PKCS1).unwrap();
        let mut out = vec![0; k];
        g.bench_function(BenchmarkId::new(VG, k), |b| {
            b.iter(|| decrypt(black_box(&vg_key), black_box(&ct)).unwrap())
        });
        g.bench_function(BenchmarkId::new(OPENSSL, k), |b| {
            b.iter(|| {
                black_box(&key)
                    .private_decrypt(black_box(&ct), &mut out, Padding::PKCS1)
                    .unwrap()
            })
        });
    }
    g.finish();
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
pub fn bench(_: &mut Criterion) {}
