//! scrypt.

use criterion::Criterion;

pub const USES: &[&str] = &["scrypt", "pbkdf2_sha256", "hmac_sha256", "sha256"];

/// scrypt with `r = 8` and `p = 1` (the RFC 7914 vectors' block size) at a
/// few costs `N`, deriving a 64-byte key, and checking a password against it
/// (`verify`; OpenSSL derives the key and compares it with
/// `CRYPTO_memcmp`). The ids' sizes are `N`. aws-lc-rs has no scrypt.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    target_arch = "riscv64",
    target_arch = "powerpc64"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;
    // Proto22 (bench branch only): main's ROMix next to it with its copy and XOR four
    // doublewords a step, r = 8.
    #[cfg(target_arch = "riscv64")]
    {
        use verified_garbage_asm_riscv64::scrypt_proto22 as p22;
        type RoMix = unsafe extern "C" fn(*mut u8, usize, *mut u8, usize, *mut u8, *mut u64);
        let fs: [(&str, RoMix); 2] = [
            ("base", p22::vg_p22_romix_base),
            ("u4", p22::vg_p22_romix_u4),
        ];
        let r = 8usize;
        for (name, f) in fs {
            let mut g = c.benchmark_group(format!("scrypt_p22_romix_{name}"));
            g.sample_size(10);
            for n in [1024usize, 16384] {
                let mut b = vec![0u64; 16 * r];
                for (i, w) in b.iter_mut().enumerate() {
                    *w = (i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15);
                }
                let mut v = vec![0u64; 16 * r * n];
                let mut t = vec![0u64; 16 * r];
                let mut save = vec![0u64; 32];
                g.bench_with_input(criterion::BenchmarkId::new(crate::VG, n), &n, |bch, &n| {
                    bch.iter(|| unsafe {
                        f(
                            b.as_mut_ptr().cast(),
                            r,
                            v.as_mut_ptr().cast(),
                            n * r,
                            t.as_mut_ptr().cast(),
                            save.as_mut_ptr(),
                        )
                    })
                });
            }
            g.finish();
        }
    }

    use criterion::BenchmarkId;
    use verified_garbage::scrypt::{scrypt, verify};

    use crate::{BenchDyn, OPENSSL, VG};
    let mut g = c.benchmark_group("scrypt");
    g.sample_size(10);
    for n in [1024u64, 16384] {
        let mut out = [0u8; 64];
        g.bench(BenchmarkId::new(VG, n), |b| {
            b.iter(|| {
                scrypt(
                    black_box(b"password"),
                    black_box(b"NaCl"),
                    n,
                    8,
                    1,
                    usize::MAX,
                    &mut out,
                )
                .unwrap()
            })
        });
        g.bench(BenchmarkId::new(OPENSSL, n), |b| {
            b.iter(|| {
                openssl::pkcs5::scrypt(
                    black_box(b"password"),
                    black_box(b"NaCl"),
                    n,
                    8,
                    1,
                    u64::MAX,
                    &mut out,
                )
                .unwrap()
            })
        });
    }
    g.finish();

    let mut g = c.benchmark_group("scrypt-verify");
    g.sample_size(10);
    for n in [1024u64, 16384] {
        let mut expected = [0u8; 64];
        scrypt(b"password", b"NaCl", n, 8, 1, usize::MAX, &mut expected).unwrap();
        g.bench(BenchmarkId::new(VG, n), |b| {
            b.iter(|| {
                verify(
                    black_box(b"password"),
                    black_box(b"NaCl"),
                    n,
                    8,
                    1,
                    usize::MAX,
                    black_box(&expected),
                )
                .unwrap()
            })
        });
        let mut out = [0u8; 64];
        g.bench(BenchmarkId::new(OPENSSL, n), |b| {
            b.iter(|| {
                openssl::pkcs5::scrypt(
                    black_box(b"password"),
                    black_box(b"NaCl"),
                    n,
                    8,
                    1,
                    u64::MAX,
                    &mut out,
                )
                .unwrap();
                assert!(openssl::memcmp::eq(&out, black_box(&expected)))
            })
        });
    }
    g.finish();
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    target_arch = "riscv64",
    target_arch = "powerpc64"
)))]
pub fn bench(_: &mut Criterion) {}
