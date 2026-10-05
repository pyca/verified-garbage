//! RSAES-OAEP encryption and decryption with SHA-256 and MGF1 over SHA-256,
//! of a 32-byte message with an empty label.

use criterion::Criterion;

pub const USES: &[&str] = &["rsa_oaep_sha256_mgf1_sha256", "rsa", "sha256"];

#[cfg(target_arch = "x86_64")]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use openssl::bn::BigNum;
    use openssl::encrypt::{Decrypter, Encrypter};
    use openssl::hash::MessageDigest;
    use openssl::pkey::PKey;
    use openssl::rsa::{Padding, Rsa};
    use verified_garbage::rsa::{PrivateKey, PublicKey};
    use verified_garbage::rsa_oaep::{Hash, decrypt, encrypt};

    use crate::{OPENSSL, VG};
    // Moduli of 2048, 3072 and 4096 bits with the exponent 65537; the ids'
    // size is the modulus' bytes. Each library loads the key once, outside
    // the measurements. Both draw a fresh seed per encryption.
    let msg = [0x42u8; 32];
    let mut g = c.benchmark_group("rsa_oaep_encrypt");
    for bits in [2048, 3072, 4096] {
        let key = Rsa::generate(bits).unwrap();
        let (n, e) = (key.n().to_vec(), key.e().to_vec());
        let k = n.len();
        let vg_key = PublicKey::new(&n, &e).unwrap();
        let openssl_key = PKey::from_rsa(
            Rsa::from_public_components(
                BigNum::from_slice(&n).unwrap(),
                BigNum::from_slice(&e).unwrap(),
            )
            .unwrap(),
        )
        .unwrap();
        let mut enc = Encrypter::new(&openssl_key).unwrap();
        enc.set_rsa_padding(Padding::PKCS1_OAEP).unwrap();
        enc.set_rsa_oaep_md(MessageDigest::sha256()).unwrap();
        enc.set_rsa_mgf1_md(MessageDigest::sha256()).unwrap();
        let mut out = vec![0; k];
        g.bench_function(BenchmarkId::new(VG, k), |b| {
            b.iter(|| {
                encrypt(
                    black_box(&vg_key),
                    black_box(&msg),
                    Hash::Sha256,
                    Hash::Sha256,
                    b"",
                )
                .unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(OPENSSL, k), |b| {
            b.iter(|| black_box(&enc).encrypt(black_box(&msg), &mut out).unwrap())
        });
    }
    g.finish();

    // The same sizes, each library holding the private key in the CRT form
    // (OpenSSL with its default blinding), decrypting a valid ciphertext.
    let mut g = c.benchmark_group("rsa_oaep_decrypt");
    for bits in [2048, 3072, 4096] {
        let key = Rsa::generate(bits).unwrap();
        let (n, e) = (key.n().to_vec(), key.e().to_vec());
        let k = n.len();
        let vg_key = PrivateKey::from_crt(
            &n,
            &e,
            &key.d().to_vec(),
            &key.p().unwrap().to_vec(),
            &key.q().unwrap().to_vec(),
            &key.dmp1().unwrap().to_vec(),
            &key.dmq1().unwrap().to_vec(),
            &key.iqmp().unwrap().to_vec(),
        )
        .unwrap();
        let pkey = PKey::from_rsa(key).unwrap();
        let mut dec = Decrypter::new(&pkey).unwrap();
        dec.set_rsa_padding(Padding::PKCS1_OAEP).unwrap();
        dec.set_rsa_oaep_md(MessageDigest::sha256()).unwrap();
        dec.set_rsa_mgf1_md(MessageDigest::sha256()).unwrap();
        let ct = encrypt(
            &PublicKey::new(&n, &e).unwrap(),
            &msg,
            Hash::Sha256,
            Hash::Sha256,
            b"",
        )
        .unwrap();
        let mut out = vec![0; k];
        g.bench_function(BenchmarkId::new(VG, k), |b| {
            b.iter(|| {
                decrypt(
                    black_box(&vg_key),
                    black_box(&ct),
                    Hash::Sha256,
                    Hash::Sha256,
                    b"",
                )
                .unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(OPENSSL, k), |b| {
            b.iter(|| black_box(&dec).decrypt(black_box(&ct), &mut out).unwrap())
        });
    }
    g.finish();
}

#[cfg(not(target_arch = "x86_64"))]
pub fn bench(_: &mut Criterion) {}
