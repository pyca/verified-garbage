//! RSAES-OAEP encryption and decryption of a 32-byte message with an empty
//! label, with each supported pair of hash function and MGF1 hash: every
//! pair with a 2048-bit modulus, and SHA-256 with MGF1 over SHA-256 with
//! 3072- and 4096-bit moduli too; beside OpenSSL and, for the pairs it has
//! (SHA-1, SHA-256, SHA-384 and SHA-512, each with MGF1 over itself),
//! aws-lc-rs.

use criterion::Criterion;

pub const USES: &[&str] = &[
    "rsa_oaep",
    "rsa_oaep_sha1_mgf1_sha1",
    "rsa_oaep_sha224_mgf1_sha1",
    "rsa_oaep_sha224_mgf1_sha224",
    "rsa_oaep_sha256_mgf1_sha1",
    "rsa_oaep_sha256_mgf1_sha256",
    "rsa_oaep_sha384_mgf1_sha1",
    "rsa_oaep_sha384_mgf1_sha384",
    "rsa_oaep_sha512_mgf1_sha1",
    "rsa_oaep_sha512_mgf1_sha512",
    "rsa_oaep_sha512_224_mgf1_sha1",
    "rsa_oaep_sha512_224_mgf1_sha512_224",
    "rsa_oaep_sha512_256_mgf1_sha1",
    "rsa_oaep_sha512_256_mgf1_sha512_256",
    "rsa",
    "sha1",
    "sha224",
    "sha256",
    "sha384",
    "sha512",
    "sha512_224",
    "sha512_256",
];

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use aws_lc_rs::rsa::{
        OAEP_SHA1_MGF1SHA1, OAEP_SHA256_MGF1SHA256, OAEP_SHA384_MGF1SHA384, OAEP_SHA512_MGF1SHA512,
        OaepPrivateDecryptingKey, OaepPublicEncryptingKey, PrivateDecryptingKey,
        PublicEncryptingKey, PublicKeyComponents,
    };
    use criterion::BenchmarkId;
    use openssl::bn::BigNum;
    use openssl::encrypt::{Decrypter, Encrypter};
    use openssl::hash::MessageDigest;
    use openssl::pkey::PKey;
    use openssl::rsa::{Padding, Rsa};
    use verified_garbage::rsa::{PrivateKey, PublicKey};
    use verified_garbage::rsa_oaep::{Hash, decrypt, encrypt};

    use crate::{AWS_LC, OPENSSL, VG};

    // Each supported hash function, by the name its modules have and
    // OpenSSL's, and aws-lc-rs's algorithm with MGF1 over the same hash, if
    // it has one.
    let hashes = [
        ("sha1", Hash::Sha1, "SHA1", Some(&OAEP_SHA1_MGF1SHA1)),
        ("sha224", Hash::Sha224, "SHA224", None),
        (
            "sha256",
            Hash::Sha256,
            "SHA256",
            Some(&OAEP_SHA256_MGF1SHA256),
        ),
        (
            "sha384",
            Hash::Sha384,
            "SHA384",
            Some(&OAEP_SHA384_MGF1SHA384),
        ),
        (
            "sha512",
            Hash::Sha512,
            "SHA512",
            Some(&OAEP_SHA512_MGF1SHA512),
        ),
        ("sha512_224", Hash::Sha512_224, "SHA512-224", None),
        ("sha512_256", Hash::Sha512_256, "SHA512-256", None),
    ];
    // Moduli of 2048, 3072 and 4096 bits with the exponent 65537, generated
    // once; the ids' size is the modulus' bytes. Each library loads the key
    // once, outside the measurements. All draw a fresh seed per encryption.
    // aws-lc-rs sets up its `EVP_PKEY_CTX` in every operation, where OpenSSL
    // reuses one.
    let keys: Vec<_> = [2048, 3072, 4096]
        .into_iter()
        .map(|bits| Rsa::generate(bits).unwrap())
        .collect();
    let msg = [0x42u8; 32];
    // Every pair with MGF1 over the hash itself or over SHA-1 (as
    // `rsa_oaep` supports), in the groups `rsa_oaep_<H>_mgf1_<G>_encrypt`
    // and `_decrypt`.
    let pairs = hashes.iter().flat_map(|h| {
        [h, &hashes[0]]
            .into_iter()
            .take(if h.0 == "sha1" { 1 } else { 2 })
            .map(move |g| (h, g))
    });
    for ((h_name, h, h_md, aws_lc), (g_name, g, g_md, _)) in pairs {
        let aws_lc = if h_name == g_name { *aws_lc } else { None };
        let (h_md, g_md) = (
            MessageDigest::from_name(h_md).unwrap(),
            MessageDigest::from_name(g_md).unwrap(),
        );
        let sizes = if *h_name == "sha256" && *g_name == "sha256" {
            &keys[..]
        } else {
            &keys[..1]
        };
        let name = format!("rsa_oaep_{h_name}_mgf1_{g_name}");

        let mut group = c.benchmark_group(format!("{name}_encrypt"));
        for key in sizes {
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
            enc.set_rsa_oaep_md(h_md).unwrap();
            enc.set_rsa_mgf1_md(g_md).unwrap();
            let mut out = vec![0; k];
            group.bench_function(BenchmarkId::new(VG, k), |b| {
                b.iter(|| encrypt(black_box(&vg_key), black_box(&msg), *h, *g, b"").unwrap())
            });
            group.bench_function(BenchmarkId::new(OPENSSL, k), |b| {
                b.iter(|| black_box(&enc).encrypt(black_box(&msg), &mut out).unwrap())
            });
            if let Some(alg) = aws_lc {
                let public: PublicEncryptingKey =
                    PublicKeyComponents { n: &n, e: &e }.try_into().unwrap();
                let aws_key = OaepPublicEncryptingKey::new(public).unwrap();
                // verified-garbage decrypts aws-lc-rs's ciphertext.
                let ct = aws_key.encrypt(alg, &msg, &mut out, None).unwrap();
                let vg_private = PrivateKey::from_crt(
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
                assert_eq!(decrypt(&vg_private, ct, *h, *g, b"").unwrap(), msg);
                group.bench_function(BenchmarkId::new(AWS_LC, k), |b| {
                    b.iter(|| {
                        black_box(&aws_key)
                            .encrypt(alg, black_box(&msg), &mut out, None)
                            .unwrap()
                            .len()
                    })
                });
            }
        }
        group.finish();

        // The same sizes, each library holding the private key in the CRT
        // form (OpenSSL with its default blinding), decrypting a valid
        // ciphertext.
        let mut group = c.benchmark_group(format!("{name}_decrypt"));
        for key in sizes {
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
            let pkey = PKey::from_rsa(key.clone()).unwrap();
            let mut dec = Decrypter::new(&pkey).unwrap();
            dec.set_rsa_padding(Padding::PKCS1_OAEP).unwrap();
            dec.set_rsa_oaep_md(h_md).unwrap();
            dec.set_rsa_mgf1_md(g_md).unwrap();
            let ct = encrypt(&PublicKey::new(&n, &e).unwrap(), &msg, *h, *g, b"").unwrap();
            let mut out = vec![0; k];
            group.bench_function(BenchmarkId::new(VG, k), |b| {
                b.iter(|| decrypt(black_box(&vg_key), black_box(&ct), *h, *g, b"").unwrap())
            });
            group.bench_function(BenchmarkId::new(OPENSSL, k), |b| {
                b.iter(|| black_box(&dec).decrypt(black_box(&ct), &mut out).unwrap())
            });
            if let Some(alg) = aws_lc {
                let aws_key = OaepPrivateDecryptingKey::new(
                    PrivateDecryptingKey::from_pkcs8(&pkey.private_key_to_pkcs8().unwrap())
                        .unwrap(),
                )
                .unwrap();
                assert_eq!(aws_key.decrypt(alg, &ct, &mut out, None).unwrap(), msg);
                group.bench_function(BenchmarkId::new(AWS_LC, k), |b| {
                    b.iter(|| {
                        black_box(&aws_key)
                            .decrypt(alg, black_box(&ct), &mut out, None)
                            .unwrap()
                            .len()
                    })
                });
            }
        }
        group.finish();
    }
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
pub fn bench(_: &mut Criterion) {}
