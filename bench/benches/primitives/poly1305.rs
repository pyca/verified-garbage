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
    #[cfg(target_arch = "x86")]
    xprobe::report("start", &key);
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
        #[cfg(target_arch = "x86")]
        xprobe::report(&format!("after poly1305-verify {size}"), &key);
    }
    g.finish();
    #[cfg(target_arch = "x86")]
    xprobe::timeline(&key, &pkey);

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

/// MEASURING PROTOTYPE, NOT FOR MERGING: probes of the state the SSE2 loop
/// of x86's `vg_poly1305_update` runs in.
#[cfg(target_arch = "x86")]
mod xprobe {
    use std::arch::asm;
    use std::hint::black_box;
    use std::time::Instant;

    use openssl::pkey::{PKey, Private};
    use openssl::sign::Signer;
    use verified_garbage::poly1305::Poly1305;

    /// XGETBV with ECX = 1: the state components in use (XINUSE), or
    /// `u32::MAX` where the processor does not have it.
    pub fn xinuse() -> u32 {
        // SAFETY: CPUID is available on every x86 these benchmarks run on.
        #[allow(unused_unsafe)]
        let has = unsafe { std::arch::x86::__cpuid_count(0xd, 1) }.eax & 4 != 0;
        if !has {
            return u32::MAX;
        }
        let lo: u32;
        // SAFETY: XGETBV with ECX = 1 is supported (checked above).
        unsafe {
            asm!("xgetbv", in("ecx") 1u32, out("eax") lo, out("edx") _, options(nostack, nomem));
        }
        lo
    }

    /// Bit `i`: the upper half of `ymm<i>` is not zero; bit `8 + i`: the
    /// upper half of `zmm<i>` is not zero.
    pub fn uppers() -> u32 {
        let mut m = 0;
        if std::is_x86_feature_detected!("avx2") {
            let mut out = [[0u8; 16]; 8];
            // SAFETY: AVX2 is available; the stores are inside `out`.
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
            m |= (0..8).fold(0, |m, i| m | (u32::from(out[i] != [0; 16]) << i));
        }
        if std::is_x86_feature_detected!("avx512f") {
            let mut out = [[0u8; 32]; 8];
            // SAFETY: AVX-512F is available; the stores are inside `out`.
            unsafe {
                asm!(
                    "vextracti64x4 [{p}], zmm0, 1",
                    "vextracti64x4 [{p}+32], zmm1, 1",
                    "vextracti64x4 [{p}+64], zmm2, 1",
                    "vextracti64x4 [{p}+96], zmm3, 1",
                    "vextracti64x4 [{p}+128], zmm4, 1",
                    "vextracti64x4 [{p}+160], zmm5, 1",
                    "vextracti64x4 [{p}+192], zmm6, 1",
                    "vextracti64x4 [{p}+224], zmm7, 1",
                    p = in(reg) out.as_mut_ptr(),
                    options(nostack),
                );
            }
            m |= (0..8).fold(0, |m, i| m | (u32::from(out[i] != [0; 32]) << (8 + i)));
        }
        m
    }

    pub fn vzeroupper() {
        if std::is_x86_feature_detected!("avx") {
            // SAFETY: AVX is available.
            unsafe {
                asm!("vzeroupper",
                    out("xmm0") _, out("xmm1") _, out("xmm2") _, out("xmm3") _,
                    out("xmm4") _, out("xmm5") _, out("xmm6") _, out("xmm7") _,
                    options(nostack, nomem));
            }
        }
    }

    fn dirty_ymm() {
        if std::is_x86_feature_detected!("avx2") {
            // SAFETY: AVX2 is available.
            unsafe {
                asm!("vpcmpeqd ymm5, ymm5, ymm5", "vpcmpeqd ymm6, ymm6, ymm6", "vpcmpeqd ymm7, ymm7, ymm7",
                    out("xmm5") _, out("xmm6") _, out("xmm7") _, options(nostack, nomem));
            }
        }
    }

    fn dirty_zmm() {
        if std::is_x86_feature_detected!("avx512f") {
            // SAFETY: AVX-512F is available.
            unsafe {
                asm!("vpternlogd zmm5, zmm5, zmm5, 0xff", "vpternlogd zmm6, zmm6, zmm6, 0xff",
                    "vpternlogd zmm7, zmm7, zmm7, 0xff",
                    out("xmm5") _, out("xmm6") _, out("xmm7") _, options(nostack, nomem));
            }
        }
    }

    /// Nanoseconds for one MAC of `data`: the fastest of 3 batches of 12.
    #[inline(never)]
    pub fn mac_ns(key: &[u8; 32], data: &[u8]) -> u32 {
        let mut best = u128::MAX;
        for _ in 0..3 {
            let t = Instant::now();
            for _ in 0..12 {
                black_box(Poly1305::mac(black_box(key), black_box(data)));
            }
            best = best.min(t.elapsed().as_nanos() / 12);
        }
        best as u32
    }

    /// As `mac_ns`, with the stack `N` bytes lower.
    #[inline(never)]
    fn mac_ns_deeper<const N: usize>(key: &[u8; 32], data: &[u8]) -> u32 {
        let pad = [0u8; N];
        black_box(&pad);
        let r = mac_ns(key, data);
        black_box(&pad);
        r
    }

    static DATA: [u8; 16384 + 64] = [0x5a; 16384 + 64];

    /// One line: the state, and the time of a MAC of 16 KiB from a static
    /// buffer, from a fresh allocation, at three other alignments and
    /// with the stack lower.
    pub fn report(what: &str, key: &[u8; 32]) {
        let (x, u) = (xinuse(), uppers());
        let a = mac_ns(key, &DATA[..16384]);
        let fresh = vec![0x5a; 16384];
        let b = mac_ns(key, &fresh);
        let c = mac_ns(key, &DATA[8..16384 + 8]);
        let d = mac_ns(key, &DATA[1..16384 + 1]);
        let e = mac_ns_deeper::<48>(key, &DATA[..16384]);
        let f = mac_ns_deeper::<1040>(key, &DATA[..16384]);
        let local = 0u8;
        eprintln!(
            "xprobe {what}: xinuse {x:#x} uppers {u:#06x} | static {a} fresh {b} +8 {c} +1 {d} deeper48 {e} deeper1040 {f} ns | \
             static {:p} fresh {:p} local {:p} | xinuse after {:#x}",
            DATA.as_ptr(), fresh.as_ptr(), &local, xinuse()
        );
    }

    /// What changes the mode, and what restores it.
    pub fn timeline(key: &[u8; 32], pkey: &PKey<Private>) {
        let data = &DATA[..16384];
        let openssl = |n: usize| {
            let mut out = [0u8; 16];
            let mut s = Signer::new_without_digest(pkey).unwrap();
            s.sign_oneshot(&mut out, &DATA[..n]).unwrap();
        };
        for round in 0..3 {
            report(&format!("timeline {round}: start"), key);
            for n in [64usize, 480, 1024, 1025, 4097, 16384] {
                openssl(n);
                report(&format!("timeline {round}: after OpenSSL {n}"), key);
            }
            std::thread::yield_now();
            report(&format!("timeline {round}: after yield"), key);
            std::thread::sleep(std::time::Duration::from_millis(3));
            report(&format!("timeline {round}: after sleep"), key);
            openssl(480);
            std::thread::sleep(std::time::Duration::from_millis(3));
            report(&format!("timeline {round}: after OpenSSL 480 and sleep"), key);
            vzeroupper();
            report(&format!("timeline {round}: after vzeroupper"), key);
            dirty_ymm();
            report(&format!("timeline {round}: after dirty ymm"), key);
            vzeroupper();
            dirty_zmm();
            report(&format!("timeline {round}: after dirty zmm"), key);
            std::thread::sleep(std::time::Duration::from_millis(3));
            report(&format!("timeline {round}: after dirty zmm and sleep"), key);
            vzeroupper();
            report(&format!("timeline {round}: after vzeroupper again"), key);
            // A second of probes: every change of mode, and what a slow
            // mode needs to end.
            let start = Instant::now();
            let mut fastest = mac_ns(key, data);
            let mut slow = false;
            let mut changes = 0;
            while start.elapsed().as_millis() < 1000 {
                let t = mac_ns(key, data);
                fastest = fastest.min(t);
                let now_slow = t > fastest + fastest / 2;
                if now_slow != slow && changes < 12 {
                    changes += 1;
                    slow = now_slow;
                    eprintln!(
                        "xprobe timeline {round}: at {} ms mode {} ({t} ns, fastest {fastest}) xinuse {:#x} uppers {:#06x}",
                        start.elapsed().as_millis(), if slow { "SLOW" } else { "fast" }, xinuse(), uppers()
                    );
                    if slow {
                        let again = mac_ns(key, data);
                        let deeper = mac_ns_deeper::<1040>(key, data);
                        let other = mac_ns(key, &DATA[8..16384 + 8]);
                        vzeroupper();
                        let cleaned = mac_ns(key, data);
                        eprintln!(
                            "xprobe timeline {round}:   slow: again {again} deeper {deeper} other data {other}; after vzeroupper {cleaned} xinuse {:#x}",
                            xinuse()
                        );
                    }
                }
            }
            eprintln!("xprobe timeline {round}: passive second done, fastest {fastest}, {changes} change(s)");
        }
    }
}
