//! Poly1305.

use criterion::Criterion;

pub const USES: &[&str] = &["poly1305"];

// aws-lc-rs has no public Poly1305 (only ChaCha20-Poly1305), so there is no
// aws-lc-rs entry.

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::pkey::{Id, PKey};
    use openssl::sign::Signer;
    use verified_garbage::poly1305::Poly1305;

    use crate::{BenchDyn, OPENSSL, VG};
    // The shared sizes, and TLS 1.3's records of 1 KiB and 4 KiB of payload,
    // whose plaintext is one byte longer (the content type): a partial last
    // block, which ChaCha20-Poly1305 authenticates at these sizes too; and
    // 480 bytes (30 blocks).
    const SIZES: [usize; 6] = [64, 480, 1024, 1025, 4097, 16384];
    let key = [0x0b; 32];
    let mut g = c.benchmark_group("poly1305");
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        g.bench(BenchmarkId::new(VG, size), |b| {
            b.iter(|| Poly1305::mac(black_box(&key), black_box(&data)))
        });
        let mut out = [0u8; 16];
        g.bench(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let pkey = PKey::private_key_from_raw_bytes(black_box(&key), Id::POLY1305).unwrap();
                let mut s = Signer::new_without_digest(&pkey).unwrap();
                s.sign_oneshot(&mut out, black_box(&data)).unwrap()
            })
        });
    }
    g.finish();

    let pkey = PKey::private_key_from_raw_bytes(&key, Id::POLY1305).unwrap();
    let mut g = c.benchmark_group("poly1305-verify");
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        let tag = Poly1305::mac(&key, &data);
        let mut reference = [0; 16];
        let mut signer = Signer::new_without_digest(&pkey).unwrap();
        assert_eq!(signer.sign_oneshot(&mut reference, &data).unwrap(), 16);
        assert_eq!(reference, tag);
        g.bench(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let mut p = Poly1305::new(black_box(&key));
                p.update(black_box(&data));
                p.verify(black_box(&tag)).unwrap()
            })
        });
        let mut out = [0u8; 16];
        g.bench(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let pkey = PKey::private_key_from_raw_bytes(black_box(&key), Id::POLY1305).unwrap();
                let mut s = Signer::new_without_digest(&pkey).unwrap();
                let n = s.sign_oneshot(&mut out, black_box(&data)).unwrap();
                assert!(openssl::memcmp::eq(&out[..n], black_box(&tag)))
            })
        });
    }
    g.finish();

    // MEASURING PROTOTYPE, NOT FOR MERGING: what makes the SSE2 loop of
    // x86's `vg_poly1305_update` slow in `poly1305-verify` on CI's AMD
    // machines (run 7668)? Each group below is `poly1305-verify`'s closure
    // with one thing changed.
    #[cfg(target_arch = "x86")]
    {
        use std::arch::asm;

        const DIAG: [usize; 5] = [480, 1024, 1025, 4097, 16384];

        /// Bit `i` is set if the upper half of `ymm<i>` is not zero.
        fn upper_mask() -> u32 {
            if !std::is_x86_feature_detected!("avx2") {
                return u32::MAX;
            }
            let mut out = [[0u8; 16]; 8];
            // SAFETY: AVX2 is available; the eight stores are inside `out`.
            unsafe {
                asm!(
                    "vextracti128 [{p}], ymm0, 1",
                    "vextracti128 [{p}+16], ymm1, 1",
                    "vextracti128 [{p}+32], ymm2, 1",
                    "vextracti128 [{p}+48], ymm3, 1",
                    "vextracti128 [{p}+64], ymm4, 1",
                    "vextracti128 [{p}+80], ymm5, 1",
                    "vextracti128 [{p}+96], ymm6, 1",
                    "vextracti128 [{p}+112], ymm7, 1",
                    p = in(reg) out.as_mut_ptr(),
                    options(nostack),
                );
            }
            (0..8).fold(0, |m, i| m | (u32::from(out[i] != [0; 16]) << i))
        }
        #[inline(always)]
        fn vzeroupper() {
            // SAFETY: only run where AVX is available (checked below).
            unsafe {
                asm!("vzeroupper",
                    out("xmm0") _, out("xmm1") _, out("xmm2") _, out("xmm3") _,
                    out("xmm4") _, out("xmm5") _, out("xmm6") _, out("xmm7") _,
                    options(nostack, nomem));
            }
        }
        #[inline(always)]
        fn dirty() {
            // SAFETY: only run where AVX2 is available (checked below).
            unsafe {
                asm!("vpcmpeqd ymm5, ymm5, ymm5", "vpcmpeqd ymm6, ymm6, ymm6", "vpcmpeqd ymm7, ymm7, ymm7",
                    out("xmm5") _, out("xmm6") _, out("xmm7") _,
                    options(nostack, nomem));
            }
        }
        assert!(std::is_x86_feature_detected!("avx2"), "the prototype needs AVX2");
        let openssl_once = |data: &[u8]| {
            let mut reference = [0; 16];
            let mut signer = Signer::new_without_digest(&pkey).unwrap();
            assert_eq!(signer.sign_oneshot(&mut reference, data).unwrap(), 16);
            reference
        };
        let verify = |data: &[u8], tag: &[u8; 16]| {
            let mut p = Poly1305::new(black_box(&key));
            p.update(black_box(data));
            p.verify(black_box(tag)).unwrap()
        };

        // No OpenSSL call in the setup.
        let mut g = c.benchmark_group("xdiag-a-no-openssl");
        for size in DIAG {
            let data = vec![0x5a; size];
            let tag = Poly1305::mac(&key, &data);
            eprintln!("xdiag a {size}: uppers {:#04x} data {:p} local {:p}", upper_mask(), data.as_ptr(), &tag);
            g.bench(BenchmarkId::new(VG, size), |b| b.iter(|| verify(&data[..], &tag)));
            eprintln!("xdiag a {size}: uppers after {:#04x}", upper_mask());
        }
        g.finish();

        // The OpenSSL call in the setup, as in `poly1305-verify`.
        let mut g = c.benchmark_group("xdiag-b-openssl");
        for size in DIAG {
            let data = vec![0x5a; size];
            let tag = openssl_once(&data[..]);
            eprintln!("xdiag b {size}: uppers {:#04x} data {:p} local {:p}", upper_mask(), data.as_ptr(), &tag);
            g.bench(BenchmarkId::new(VG, size), |b| b.iter(|| verify(&data[..], &tag)));
            eprintln!("xdiag b {size}: uppers after {:#04x}", upper_mask());
        }
        g.finish();

        // The OpenSSL call in the setup, and `vzeroupper` in every iteration.
        let mut g = c.benchmark_group("xdiag-c-openssl-vzeroupper");
        for size in DIAG {
            let data = vec![0x5a; size];
            let tag = openssl_once(&data[..]);
            g.bench(BenchmarkId::new(VG, size), |b| {
                b.iter(|| {
                    vzeroupper();
                    verify(&data[..], &tag)
                })
            });
        }
        g.finish();

        // No OpenSSL call; the upper halves of ymm5-ymm7 set in every
        // iteration.
        let mut g = c.benchmark_group("xdiag-d-dirty");
        for size in DIAG {
            let data = vec![0x5a; size];
            let tag = Poly1305::mac(&key, &data);
            g.bench(BenchmarkId::new(VG, size), |b| {
                b.iter(|| {
                    dirty();
                    verify(&data[..], &tag)
                })
            });
        }
        g.finish();
        vzeroupper();

        // No OpenSSL call, after the groups above: `vzeroupper` once in the
        // setup, then nothing.
        let mut g = c.benchmark_group("xdiag-e-after");
        for size in DIAG {
            let data = vec![0x5a; size];
            let tag = Poly1305::mac(&key, &data);
            vzeroupper();
            eprintln!("xdiag e {size}: uppers {:#04x}", upper_mask());
            g.bench(BenchmarkId::new(VG, size), |b| b.iter(|| verify(&data[..], &tag)));
            eprintln!("xdiag e {size}: uppers after {:#04x}", upper_mask());
        }
        g.finish();
    }
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
)))]
pub fn bench(_: &mut Criterion) {}
