//! Times verified-garbage's primitives against aws-lc-rs's through each
//! library's own API, to tell the libraries' costs from the provider's.
//!
//! `aws-lc-compare <dir>` reads `rsa2048.der`, `rsa3072.der` and
//! `rsa4096.der` (PKCS #1) from `dir`; `aws-lc-compare <dir> aead` times
//! only the AEADs, and `aws-lc-compare <dir> sweep` the AEADs at sizes
//! up to 2 KiB.

// rust-asn1's `ParseError` is large, in the code its derive generates.
#![allow(clippy::result_large_err)]

use std::hint::black_box;
use std::time::{Duration, Instant};

use aws_lc_rs::signature::KeyPair;
use aws_lc_rs::{aead, agreement, rand, signature};
use verified_garbage as vg;

fn time(mut f: impl FnMut()) -> f64 {
    let start = Instant::now();
    let mut n = 0u64;
    while start.elapsed() < Duration::from_millis(20) || n < 3 {
        f();
        n += 1;
    }
    let per = start.elapsed().as_secs_f64() / n as f64;
    let iters = ((0.04 / per).ceil() as u64).max(1);
    let mut samples = vec![];
    for _ in 0..9 {
        let t = Instant::now();
        for _ in 0..iters {
            f();
        }
        samples.push(t.elapsed().as_secs_f64() * 1e9 / iters as f64);
    }
    samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
    samples[4]
}

/// A row: both times, and verified-garbage's speed relative to aws-lc-rs's
/// (below 1 is slower).
fn row(name: &str, aws: f64, vg: f64) {
    println!("{name:<52} {aws:>11.0} {vg:>11.0} {:>7.2}", aws / vg);
}

#[derive(asn1::Asn1Read)]
struct RsaPrivateKey<'a> {
    _version: u8,
    n: asn1::BigUint<'a>,
    e: asn1::BigUint<'a>,
    d: asn1::BigUint<'a>,
    p: asn1::BigUint<'a>,
    q: asn1::BigUint<'a>,
    dp: asn1::BigUint<'a>,
    dq: asn1::BigUint<'a>,
    qinv: asn1::BigUint<'a>,
}

fn trim(x: &[u8]) -> &[u8] {
    let z = x.iter().take_while(|&&b| b == 0).count();
    &x[z..]
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let dir = std::path::PathBuf::from(
        args.get(1)
            .expect("usage: aws-lc-compare <dir> [aead|sweep]"),
    );
    let only_aead = args.iter().any(|a| a == "aead" || a == "sweep");
    println!(
        "{:<52} {:>11} {:>11} {:>8}",
        "ns per operation", "aws-lc", "vg", "speed"
    );
    // --- AEAD at several sizes: in place, separate tag.
    for (name, klen) in [
        ("AES-128-GCM", 16usize),
        ("AES-256-GCM", 32),
        ("ChaCha20-Poly1305", 32),
    ] {
        let key = vec![7u8; klen];
        let alg = match name {
            "AES-128-GCM" => &aead::AES_128_GCM,
            "AES-256-GCM" => &aead::AES_256_GCM,
            _ => &aead::CHACHA20_POLY1305,
        };
        let aws = aead::LessSafeKey::new(aead::UnboundKey::new(alg, &key).unwrap());
        let gcm =
            (klen == 16 || name == "AES-256-GCM").then(|| vg::aes_gcm::AesGcm::new(&key).unwrap());
        let cp = vg::chacha20poly1305::ChaCha20Poly1305::new(&[7u8; 32]);
        let sizes: &[usize] = if std::env::args().any(|a| a == "sweep") {
            &[64, 128, 192, 256, 384, 512, 640, 768, 1024, 1088, 2048]
        } else {
            &[0, 16, 256, 1024, 4096, 16384]
        };
        for &len in sizes {
            let mut buf = vec![0x41u8; len];
            let aad = [1u8; 5];
            let a = time(|| {
                let n = aead::Nonce::assume_unique_for_key([3u8; 12]);
                let _ = black_box(
                    aws.seal_in_place_separate_tag(n, aead::Aad::from(&aad), &mut buf)
                        .unwrap(),
                );
            });
            let v = time(|| {
                black_box(match &gcm {
                    Some(g) => g.encrypt_in_place(&[3u8; 12], &aad, &mut buf).unwrap(),
                    None => cp.encrypt_in_place(&[3u8; 12], &aad, &mut buf).unwrap(),
                });
            });
            row(&format!("{name} seal in place {len} B"), a, v);
        }
        // Out of place, as the provider seals a TLS 1.3 record: the payload
        // and its content type byte, two pieces, into a separate buffer
        // (against aws-lc-rs sealing as many bytes in place).
        let Some(g) = &gcm else { continue };
        for &len in sizes {
            let payload = vec![0x41u8; len];
            let mut out = vec![0u8; len + 1];
            let mut buf = vec![0x41u8; len + 1];
            let aad = [1u8; 5];
            let a = time(|| {
                let n = aead::Nonce::assume_unique_for_key([3u8; 12]);
                let _ = black_box(
                    aws.seal_in_place_separate_tag(n, aead::Aad::from(&aad), &mut buf)
                        .unwrap(),
                );
            });
            let v = time(|| {
                black_box(
                    g.encrypt(&[3u8; 12], &aad, &[&payload, &[0x17]], &mut out)
                        .unwrap(),
                );
            });
            row(&format!("{name} seal out of place {len}+1 B"), a, v);
        }
    }
    let src = vec![0x41u8; 16384];
    let mut dst = vec![0u8; 16384];
    let c = time(|| {
        dst.copy_from_slice(black_box(&src));
        black_box(&dst);
    });
    row("memcpy 16384 B (the ChaCha20 copy into `out`)", c, c);

    if only_aead {
        return;
    }
    // --- RSA.
    for bits in [2048, 3072, 4096] {
        let der = std::fs::read(dir.join(format!("rsa{bits}.der"))).unwrap();
        let k = asn1::parse_single::<RsaPrivateKey<'_>>(&der).unwrap();
        let n = trim(k.n.as_bytes());
        let e = k.e.as_bytes();
        let aws_kp = signature::RsaKeyPair::from_der(&der).unwrap();
        let vg_key = vg::rsa::PrivateKey::from_crt(
            n,
            e,
            k.d.as_bytes(),
            k.p.as_bytes(),
            k.q.as_bytes(),
            k.dp.as_bytes(),
            k.dq.as_bytes(),
            k.qinv.as_bytes(),
        )
        .unwrap();
        let msg = [0x20u8; 130];
        let digest = vg::hashes::sha256::Sha256::digest(&msg);
        let rng = rand::SystemRandom::new();
        let mut sig = vec![0u8; n.len()];
        let a = time(|| {
            aws_kp
                .sign(&signature::RSA_PSS_SHA256, &rng, &msg, &mut sig)
                .unwrap();
        });
        let v = time(|| {
            black_box(
                vg::rsa_pss::sign(
                    &vg_key,
                    &digest,
                    vg::rsa_pss::Hash::Sha256,
                    vg::rsa_pss::Hash::Sha256,
                    32,
                )
                .unwrap(),
            );
        });
        row(&format!("RSA-{bits} PSS sign"), a, v);
        let a = time(|| {
            black_box(signature::RsaKeyPair::from_der(&der).unwrap());
        });
        let v = time(|| {
            black_box(
                vg::rsa::PrivateKey::from_crt(
                    n,
                    e,
                    k.d.as_bytes(),
                    k.p.as_bytes(),
                    k.q.as_bytes(),
                    k.dp.as_bytes(),
                    k.dq.as_bytes(),
                    k.qinv.as_bytes(),
                )
                .unwrap(),
            );
        });
        row(&format!("RSA-{bits} load private key"), a, v);

        let sig = vg::rsa_pss::sign(
            &vg_key,
            &digest,
            vg::rsa_pss::Hash::Sha256,
            vg::rsa_pss::Hash::Sha256,
            32,
        )
        .unwrap();
        let spki_key = aws_kp.public_key().as_ref().to_vec();
        let a = time(|| {
            signature::UnparsedPublicKey::new(&signature::RSA_PSS_2048_8192_SHA256, &spki_key)
                .verify(&msg, &sig)
                .unwrap();
        });
        let v = time(|| {
            let pk = vg::rsa::PublicKey::new(n, e).unwrap();
            let d = vg::hashes::sha256::Sha256::digest(&msg);
            assert!(vg::rsa_pss::verify(
                &pk,
                &sig,
                &d,
                vg::rsa_pss::Hash::Sha256,
                vg::rsa_pss::Hash::Sha256,
                vg::rsa_pss::SaltLength::Len(32)
            ));
        });
        row(&format!("RSA-{bits} PSS verify (parse key + verify)"), a, v);
        let pk = vg::rsa::PublicKey::new(n, e).unwrap();
        let v1 = time(|| {
            black_box(vg::rsa::PublicKey::new(n, e).unwrap());
        });
        let v2 = time(|| {
            assert!(vg::rsa_pss::verify(
                &pk,
                &sig,
                &digest,
                vg::rsa_pss::Hash::Sha256,
                vg::rsa_pss::Hash::Sha256,
                vg::rsa_pss::SaltLength::Len(32)
            ));
        });
        let mut out = vec![0u8; n.len()];
        let v3 = time(|| {
            pk.public_op(&sig, &mut out).unwrap();
        });
        row(
            &format!("  vg RSA-{bits} PublicKey::new (computes lazily)"),
            a,
            v1,
        );
        row(
            &format!("  vg RSA-{bits} rsa_pss::verify (precomputed)"),
            a,
            v2,
        );
        row(
            &format!("  vg RSA-{bits} public_op (precomputed, ADX)"),
            a,
            v3,
        );
    }

    // --- P-256.
    let rng = rand::SystemRandom::new();
    let a = time(|| {
        let k = agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P256, &rng).unwrap();
        black_box(k.compute_public_key().unwrap());
    });
    let d = [0x5au8; 32];
    let v = time(|| {
        black_box(
            vg::ecdh::PrivateKey::<vg::ecdh::P256>::from_bytes(&d)
                .public_key()
                .unwrap(),
        );
    });
    row("P-256 keygen (fixed-base [k]G)", a, v);
    let peer = vg::ecdh::PrivateKey::<vg::ecdh::P256>::from_bytes(&[0x33u8; 32])
        .public_key()
        .unwrap();
    let a = time(|| {
        let k = agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P256, &rng).unwrap();
        agreement::agree_ephemeral(
            k,
            agreement::UnparsedPublicKey::new(&agreement::ECDH_P256, &peer),
            (),
            |s| {
                black_box(s);
                Ok(())
            },
        )
        .unwrap();
    });
    let vk = vg::ecdh::PrivateKey::<vg::ecdh::P256>::from_bytes(&d);
    let v = time(|| {
        black_box(vk.diffie_hellman(&peer).unwrap());
    });
    row("P-256 ECDH (aws: keygen + [k]P; vg: [k]P)", a, v);
    let pkcs8 =
        signature::EcdsaKeyPair::generate_pkcs8(&signature::ECDSA_P256_SHA256_FIXED_SIGNING, &rng)
            .unwrap();
    let aws_ec = signature::EcdsaKeyPair::from_pkcs8(
        &signature::ECDSA_P256_SHA256_FIXED_SIGNING,
        pkcs8.as_ref(),
    )
    .unwrap();
    let msg = [0x20u8; 130];
    let a = time(|| {
        black_box(aws_ec.sign(&rng, &msg).unwrap());
    });
    let sk = vg::ecdsa::SigningKey::<vg::ecdsa::P256>::from_bytes(&d);
    let v = time(|| {
        black_box(sk.sign::<vg::hashes::sha256::Sha256>(&msg).unwrap());
    });
    row("P-256 ECDSA sign", a, v);
    let aws_sig = aws_ec.sign(&rng, &msg).unwrap();
    let aws_pub = aws_ec.public_key().as_ref().to_vec();
    let a = time(|| {
        signature::UnparsedPublicKey::new(&signature::ECDSA_P256_SHA256_FIXED, &aws_pub)
            .verify(&msg, aws_sig.as_ref())
            .unwrap();
    });
    let vk = vg::ecdsa::VerifyingKey::<vg::ecdsa::P256>::from_bytes(
        aws_pub.as_slice().try_into().unwrap(),
    );
    let s: [u8; 64] = aws_sig.as_ref().try_into().unwrap();
    let v = time(|| {
        vk.verify::<vg::hashes::sha256::Sha256>(&msg, &s).unwrap();
    });
    row("P-256 ECDSA verify", a, v);

    // --- X25519.
    let a = time(|| {
        let k = agreement::EphemeralPrivateKey::generate(&agreement::X25519, &rng).unwrap();
        black_box(k.compute_public_key().unwrap());
    });
    let xk = vg::x25519::PrivateKey::from_bytes(&[9u8; 32]);
    let v = time(|| {
        black_box(xk.public_key());
    });
    row("X25519 keygen (fixed-base)", a, v);
    let peer = xk.public_key();
    let a = time(|| {
        let k = agreement::EphemeralPrivateKey::generate(&agreement::X25519, &rng).unwrap();
        agreement::agree_ephemeral(
            k,
            agreement::UnparsedPublicKey::new(&agreement::X25519, &peer),
            (),
            |s| {
                black_box(s);
                Ok(())
            },
        )
        .unwrap();
    });
    let v = time(|| {
        black_box(xk.diffie_hellman(&peer).unwrap());
    });
    row("X25519 DH (aws: keygen + DH; vg: DH)", a, v);

    // --- HMAC and HKDF, as TLS 1.3's key schedule uses them: a 32- or
    // 48-byte key and secret, and one block of output.
    hkdf_rows::<vg::hashes::sha256::Sha256>(
        "SHA-256",
        aws_lc_rs::hmac::HMAC_SHA256,
        aws_lc_rs::hkdf::HKDF_SHA256,
        32,
    );
    hkdf_rows::<vg::hashes::sha384::Sha384>(
        "SHA-384",
        aws_lc_rs::hmac::HMAC_SHA384,
        aws_lc_rs::hkdf::HKDF_SHA384,
        48,
    );
}

fn hkdf_rows<H: vg::hmac::HmacHash>(
    name: &str,
    hmac_alg: aws_lc_rs::hmac::Algorithm,
    hkdf_alg: aws_lc_rs::hkdf::Algorithm,
    len: usize,
) where
    H::Output: AsRef<[u8]>,
{
    let key = vec![7u8; len];
    let msg = [3u8; 32];
    let a = time(|| {
        let k = aws_lc_rs::hmac::Key::new(hmac_alg, &key);
        black_box(aws_lc_rs::hmac::sign(&k, &msg));
    });
    let v = time(|| {
        black_box(vg::hmac::Hmac::<H>::mac(&key, &msg));
    });
    row(&format!("HMAC-{name}, {len}-byte key, 32 B"), a, v);

    let info = [5u8; 20];
    let mut out = vec![0u8; len];
    let a = time(|| {
        let prk = aws_lc_rs::hkdf::Salt::new(hkdf_alg, &key).extract(&msg);
        let info: &[&[u8]] = &[&info];
        let okm = prk.expand(info, OutLen(len)).unwrap();
        okm.fill(&mut out).unwrap();
        black_box(&out);
    });
    let v = time(|| {
        let prk = vg::hmac::Hmac::<H>::mac(&key, &msg);
        let mut h = vg::hmac::Hmac::<H>::new(prk.as_ref());
        h.update(&info);
        h.update(&[1]);
        out.copy_from_slice(&h.finalize().as_ref()[..len]);
        black_box(&out);
    });
    row(&format!("HKDF-{name} extract + expand ({len} B)"), a, v);
}

/// An output length for aws-lc-rs's HKDF.
struct OutLen(usize);

impl aws_lc_rs::hkdf::KeyType for OutLen {
    fn len(&self) -> usize {
        self.0
    }
}
