//! Triple DES-CBC, including key expansion and in-place
//! encryption/decryption, beside OpenSSL.
//!
//! aws-lc-rs has Triple DES only behind its `legacy-des` feature (see
//! `triple_des_ecb.rs`), so there is nothing of its to compare with.

use criterion::Criterion;

/// The library modules whose code these benchmarks run.
pub const USES: &[&str] = &["triple_des_cbc", "triple_des"];

#[cfg(target_arch = "x86_64")]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::symm::{Cipher, Crypter, Mode};
    use verified_garbage::triple_des_cbc::TripleDesCbc;

    use crate::{OPENSSL, SIZES, VG};

    let key: Vec<_> = (0..24).map(|i| (17 * i + 3) as u8).collect();
    let iv = [0x3c; 8];
    let cipher = Cipher::des_ede3_cbc();
    for (operation, encrypt, mode) in [
        ("encrypt", true, Mode::Encrypt),
        ("decrypt", false, Mode::Decrypt),
    ] {
        let mut group = c.benchmark_group(format!("triple-des-cbc-{operation}"));
        for size in SIZES {
            group.throughput(Throughput::Bytes(size as u64));
            let data = vec![0x5a; size];
            let mut buffer = vec![0; size];
            group.bench_function(BenchmarkId::new(VG, size), |b| {
                b.iter(|| {
                    let ctx = TripleDesCbc::new(black_box(&key)).unwrap();
                    let mut chain = black_box(iv);
                    buffer.copy_from_slice(black_box(&data));
                    if encrypt {
                        ctx.encrypt(&mut chain, black_box(&mut buffer)).unwrap();
                    } else {
                        ctx.decrypt(&mut chain, black_box(&mut buffer)).unwrap();
                    }
                    black_box(&buffer);
                })
            });
            let mut output = vec![0; size + 8];
            group.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
                b.iter(|| {
                    let mut ctx =
                        Crypter::new(cipher, mode, black_box(&key), Some(black_box(&iv))).unwrap();
                    ctx.pad(false);
                    let n = ctx.update(black_box(&data), &mut output).unwrap();
                    let n = n + ctx.finalize(&mut output[n..]).unwrap();
                    black_box(&output[..n]);
                })
            });
        }
        group.finish();
    }
}

#[cfg(not(target_arch = "x86_64"))]
pub fn bench(_: &mut Criterion) {}
