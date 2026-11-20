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
    // The prototype's sections. A launch runs only the newest (`xghash`),
    // unless `VG_XOLD` is set, which also runs the earlier ones (`xcand`,
    // `xsize`, `xprobe`, `xmodes`, the `xdiag` groups); none where the
    // benchmarks are only listed.
    #[cfg(target_arch = "x86")]
    let xlist = std::env::args().any(|a| a == "--list");
    #[cfg(target_arch = "x86")]
    let xold = !xlist && std::env::var_os("VG_XOLD").is_some();
    #[cfg(target_arch = "x86")]
    if !xlist {
        for round in 0..3 {
            xghash::candidates(round);
        }
    }
    #[cfg(target_arch = "x86")]
    if xold {
        for round in 0..3 {
            xcand::candidates(&key, round);
        }
        xprobe::report("start", &key);
    }
    #[cfg(target_arch = "x86")]
    let xmodes = if xold { xmodes::Setup::new() } else { None };
    #[cfg(target_arch = "x86")]
    if let Some(x) = &xmodes {
        x.run(0);
    }
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
        if xold {
            xprobe::report(&format!("after poly1305-verify {size}"), &key);
        }
    }
    g.finish();
    #[cfg(target_arch = "x86")]
    if xold {
        xprobe::timeline(&key, &pkey);
        for round in 3..5 {
            xcand::candidates(&key, round);
        }
    }
    #[cfg(target_arch = "x86")]
    if let Some(x) = &xmodes {
        x.run(1);
    }

    // MEASURING PROTOTYPE, NOT FOR MERGING: what makes the SSE2 loop of
    // x86's `vg_poly1305_update` slow in `poly1305-verify` on CI's AMD
    // machines (run 7668)? Each group below is `poly1305-verify`'s closure
    // with one thing changed.
    #[cfg(target_arch = "x86")]
    if xold {
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

// XCAND BEGIN (generated by scratchpad/poly/zen4/mkproto.py)
/// MEASURING PROTOTYPE, NOT FOR MERGING: candidate bodies for the loop of
/// `lanes` (the pairs of blocks of x86's `vg_poly1305_update`), written by
/// hand for this measurement only, each timed on dummy lanes in the two
/// modes of the processor: the AVX state not in use (XGETBV(1) = 0x3), and
/// in use with the upper halves zero (0x7, after a 256-bit instruction and
/// `vzeroupper`), where on Zen 4 a legacy-SSE write of a whole register
/// waits for the register's previous value.
#[cfg(target_arch = "x86")]
mod xcand {
    use std::arch::asm;
    use std::hint::black_box;
    use std::time::Instant;

    use verified_garbage::poly1305::Poly1305;

    use super::xprobe::xinuse;

    // Each function: cdecl (frame, data, pairs). `frame` + 76 + 16 j is slot
    // j of the frame of `pairs` (as at `esp` inside its MCDT frame): the
    // multipliers in slots 0..10, the mask and the bit 2^24 in slots 20 and
    // 21, and the spare slots; `data` is 32 bytes a pair.
    std::arch::global_asm!(
        ".globl vgx_cand_stage1",
        ".type vgx_cand_stage1, @function",
        ".p2align 6",
        "vgx_cand_stage1:",
        "    push ebx",
        "    push esi",
        "    mov ebx, DWORD PTR [esp+12]",
        "    mov esi, DWORD PTR [esp+16]",
        "    mov ecx, DWORD PTR [esp+20]",
        "    movdqu xmm0, XMMWORD PTR [ebx+428]",
        "    movdqu xmm1, XMMWORD PTR [ebx+444]",
        "    movdqu xmm2, XMMWORD PTR [ebx+460]",
        "    movdqu xmm3, XMMWORD PTR [ebx+476]",
        "    movdqu xmm4, XMMWORD PTR [ebx+492]",
        "    .p2align 4",
        "2:",
        "    movdqu xmm5, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm5, xmm0",
        "    movdqu xmm6, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm6, xmm1",
        "    paddq xmm5, xmm6",
        "    movdqu xmm6, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm6, xmm2",
        "    paddq xmm5, xmm6",
        "    movdqu xmm6, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm6, xmm3",
        "    paddq xmm5, xmm6",
        "    movdqu xmm6, XMMWORD PTR [ebx+188]",
        "    pmuludq xmm6, xmm4",
        "    paddq xmm5, xmm6",
        "    movdqu XMMWORD PTR [ebx+428], xmm5",
        "    movdqu xmm5, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm5, xmm0",
        "    movdqu xmm6, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm6, xmm1",
        "    paddq xmm5, xmm6",
        "    movdqu xmm6, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm6, xmm2",
        "    paddq xmm5, xmm6",
        "    movdqu xmm6, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm6, xmm3",
        "    paddq xmm5, xmm6",
        "    movdqu xmm6, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm6, xmm4",
        "    paddq xmm5, xmm6",
        "    movdqu XMMWORD PTR [ebx+444], xmm5",
        "    movdqu xmm5, XMMWORD PTR [ebx+124]",
        "    pmuludq xmm5, xmm0",
        "    movdqu xmm6, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm6, xmm1",
        "    paddq xmm5, xmm6",
        "    movdqu xmm6, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm6, xmm2",
        "    paddq xmm5, xmm6",
        "    movdqu xmm6, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm6, xmm3",
        "    paddq xmm5, xmm6",
        "    movdqu xmm6, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm6, xmm4",
        "    paddq xmm5, xmm6",
        "    movdqu XMMWORD PTR [ebx+460], xmm5",
        "    movdqu xmm5, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm5, xmm0",
        "    movdqu xmm6, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm6, xmm1",
        "    paddq xmm5, xmm6",
        "    movdqu xmm6, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm6, xmm2",
        "    paddq xmm5, xmm6",
        "    movdqu xmm6, XMMWORD PTR [ebx+188]",
        "    pmuludq xmm6, xmm3",
        "    paddq xmm5, xmm6",
        "    movdqu xmm6, XMMWORD PTR [ebx+172]",
        "    pmuludq xmm6, xmm4",
        "    paddq xmm5, xmm6",
        "    movdqa xmm7, xmm5",
        "    movdqu xmm5, XMMWORD PTR [ebx+140]",
        "    pmuludq xmm5, xmm0",
        "    movdqu xmm6, XMMWORD PTR [ebx+124]",
        "    pmuludq xmm6, xmm1",
        "    paddq xmm5, xmm6",
        "    movdqu xmm6, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm6, xmm2",
        "    paddq xmm5, xmm6",
        "    movdqu xmm6, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm6, xmm3",
        "    paddq xmm5, xmm6",
        "    movdqu xmm6, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm6, xmm4",
        "    paddq xmm5, xmm6",
        "    movdqa xmm4, xmm5",
        "    movdqa xmm0, xmm7",
        "    movdqu xmm1, XMMWORD PTR [ebx+428]",
        "    movdqu xmm2, XMMWORD PTR [ebx+444]",
        "    movdqu xmm3, XMMWORD PTR [ebx+460]",
        "    movdqu xmm5, XMMWORD PTR [ebx+396]",
        "    movdqa xmm6, xmm0",
        "    psrlq xmm6, 26",
        "    pand xmm0, xmm5",
        "    paddq xmm1, xmm6",
        "    movdqa xmm6, xmm3",
        "    psrlq xmm6, 26",
        "    pand xmm3, xmm5",
        "    paddq xmm4, xmm6",
        "    movdqa xmm6, xmm1",
        "    psrlq xmm6, 26",
        "    pand xmm1, xmm5",
        "    paddq xmm2, xmm6",
        "    movdqa xmm6, xmm4",
        "    psrlq xmm6, 26",
        "    pand xmm4, xmm5",
        "    movdqa xmm7, xmm6",
        "    psllq xmm7, 2",
        "    paddq xmm6, xmm7",
        "    paddq xmm0, xmm6",
        "    movdqa xmm6, xmm2",
        "    psrlq xmm6, 26",
        "    pand xmm2, xmm5",
        "    paddq xmm3, xmm6",
        "    movdqa xmm6, xmm0",
        "    psrlq xmm6, 26",
        "    pand xmm0, xmm5",
        "    paddq xmm1, xmm6",
        "    movdqa xmm6, xmm3",
        "    psrlq xmm6, 26",
        "    pand xmm3, xmm5",
        "    paddq xmm4, xmm6",
        "    movq xmm6, QWORD PTR [esi]",
        "    movq xmm7, QWORD PTR [esi+16]",
        "    punpcklqdq xmm6, xmm7",
        "    psrlq xmm6, 0",
        "    pand xmm6, xmm5",
        "    paddq xmm0, xmm6",
        "    movq xmm6, QWORD PTR [esi]",
        "    movq xmm7, QWORD PTR [esi+16]",
        "    punpcklqdq xmm6, xmm7",
        "    psrlq xmm6, 26",
        "    pand xmm6, xmm5",
        "    paddq xmm1, xmm6",
        "    movq xmm6, QWORD PTR [esi+6]",
        "    movq xmm7, QWORD PTR [esi+22]",
        "    punpcklqdq xmm6, xmm7",
        "    psrlq xmm6, 4",
        "    pand xmm6, xmm5",
        "    paddq xmm2, xmm6",
        "    movq xmm6, QWORD PTR [esi+8]",
        "    movq xmm7, QWORD PTR [esi+24]",
        "    punpcklqdq xmm6, xmm7",
        "    psrlq xmm6, 14",
        "    pand xmm6, xmm5",
        "    paddq xmm3, xmm6",
        "    movq xmm6, QWORD PTR [esi+8]",
        "    movq xmm7, QWORD PTR [esi+24]",
        "    punpcklqdq xmm6, xmm7",
        "    psrlq xmm6, 40",
        "    pand xmm6, xmm5",
        "    paddq xmm4, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+412]",
        "    paddq xmm4, xmm7",
        "    add esi, 32",
        "    sub ecx, 1",
        "    jne 2b",
        "    pop esi",
        "    pop ebx",
        "    ret",
        ".size vgx_cand_stage1, .-vgx_cand_stage1",
        ".globl vgx_cand_alt2",
        ".type vgx_cand_alt2, @function",
        ".p2align 6",
        "vgx_cand_alt2:",
        "    push ebx",
        "    push esi",
        "    mov ebx, DWORD PTR [esp+12]",
        "    mov esi, DWORD PTR [esp+16]",
        "    mov ecx, DWORD PTR [esp+20]",
        "    movdqu xmm0, XMMWORD PTR [ebx+428]",
        "    movdqu xmm1, XMMWORD PTR [ebx+444]",
        "    movdqu xmm2, XMMWORD PTR [ebx+460]",
        "    movdqu xmm3, XMMWORD PTR [ebx+476]",
        "    movdqu xmm4, XMMWORD PTR [ebx+492]",
        "    .p2align 4",
        "2:",
        "    movdqu xmm5, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm5, xmm0",
        "    movdqu xmm6, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm6, xmm1",
        "    paddq xmm5, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm7, xmm2",
        "    paddq xmm5, xmm7",
        "    movdqu xmm6, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm6, xmm3",
        "    paddq xmm5, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+188]",
        "    pmuludq xmm7, xmm4",
        "    paddq xmm5, xmm7",
        "    movdqu XMMWORD PTR [ebx+444], xmm5",
        "    movdqu xmm5, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm5, xmm0",
        "    movdqu xmm6, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm6, xmm1",
        "    paddq xmm5, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm7, xmm2",
        "    paddq xmm5, xmm7",
        "    movdqu xmm6, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm6, xmm3",
        "    paddq xmm5, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm7, xmm4",
        "    paddq xmm5, xmm7",
        "    movdqu XMMWORD PTR [ebx+460], xmm5",
        "    movdqu xmm5, XMMWORD PTR [ebx+124]",
        "    pmuludq xmm5, xmm0",
        "    movdqu xmm6, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm6, xmm1",
        "    paddq xmm5, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm7, xmm2",
        "    paddq xmm5, xmm7",
        "    movdqu xmm6, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm6, xmm3",
        "    paddq xmm5, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm7, xmm4",
        "    paddq xmm5, xmm7",
        "    movdqu XMMWORD PTR [ebx+476], xmm5",
        "    movdqu xmm5, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm5, xmm0",
        "    movdqu xmm6, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm6, xmm1",
        "    paddq xmm5, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm7, xmm2",
        "    paddq xmm5, xmm7",
        "    movdqu xmm6, XMMWORD PTR [ebx+188]",
        "    pmuludq xmm6, xmm3",
        "    paddq xmm5, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+172]",
        "    pmuludq xmm7, xmm4",
        "    paddq xmm5, xmm7",
        "    movdqu XMMWORD PTR [ebx+428], xmm5",
        "    movdqu xmm5, XMMWORD PTR [ebx+140]",
        "    pmuludq xmm5, xmm0",
        "    movdqu xmm6, XMMWORD PTR [ebx+124]",
        "    pmuludq xmm6, xmm1",
        "    paddq xmm5, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm7, xmm2",
        "    paddq xmm5, xmm7",
        "    movdqu xmm6, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm6, xmm3",
        "    paddq xmm5, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm7, xmm4",
        "    paddq xmm5, xmm7",
        "    movdqa xmm4, xmm5",
        "    movdqu xmm0, XMMWORD PTR [ebx+428]",
        "    movdqu xmm1, XMMWORD PTR [ebx+444]",
        "    movdqu xmm2, XMMWORD PTR [ebx+460]",
        "    movdqu xmm3, XMMWORD PTR [ebx+476]",
        "    movdqu xmm5, XMMWORD PTR [ebx+396]",
        "    movdqa xmm6, xmm0",
        "    psrlq xmm6, 26",
        "    pand xmm0, xmm5",
        "    paddq xmm1, xmm6",
        "    movdqa xmm7, xmm3",
        "    psrlq xmm7, 26",
        "    pand xmm3, xmm5",
        "    paddq xmm4, xmm7",
        "    movdqa xmm6, xmm1",
        "    psrlq xmm6, 26",
        "    pand xmm1, xmm5",
        "    paddq xmm2, xmm6",
        "    movdqa xmm7, xmm4",
        "    psrlq xmm7, 26",
        "    pand xmm4, xmm5",
        "    movdqa xmm6, xmm7",
        "    psllq xmm6, 2",
        "    paddq xmm7, xmm6",
        "    paddq xmm0, xmm7",
        "    movdqa xmm6, xmm2",
        "    psrlq xmm6, 26",
        "    pand xmm2, xmm5",
        "    paddq xmm3, xmm6",
        "    movdqa xmm7, xmm0",
        "    psrlq xmm7, 26",
        "    pand xmm0, xmm5",
        "    paddq xmm1, xmm7",
        "    movdqa xmm6, xmm3",
        "    psrlq xmm6, 26",
        "    pand xmm3, xmm5",
        "    paddq xmm4, xmm6",
        "    movq xmm7, QWORD PTR [esi+0]",
        "    movq xmm6, QWORD PTR [esi+16]",
        "    punpcklqdq xmm7, xmm6",
        "    psrlq xmm7, 0",
        "    pand xmm7, xmm5",
        "    paddq xmm0, xmm7",
        "    movq xmm6, QWORD PTR [esi+0]",
        "    movq xmm7, QWORD PTR [esi+16]",
        "    punpcklqdq xmm6, xmm7",
        "    psrlq xmm6, 26",
        "    pand xmm6, xmm5",
        "    paddq xmm1, xmm6",
        "    movq xmm7, QWORD PTR [esi+6]",
        "    movq xmm6, QWORD PTR [esi+22]",
        "    punpcklqdq xmm7, xmm6",
        "    psrlq xmm7, 4",
        "    pand xmm7, xmm5",
        "    paddq xmm2, xmm7",
        "    movq xmm6, QWORD PTR [esi+8]",
        "    movq xmm7, QWORD PTR [esi+24]",
        "    punpcklqdq xmm6, xmm7",
        "    psrlq xmm6, 14",
        "    pand xmm6, xmm5",
        "    paddq xmm3, xmm6",
        "    movq xmm7, QWORD PTR [esi+8]",
        "    movq xmm6, QWORD PTR [esi+24]",
        "    punpcklqdq xmm7, xmm6",
        "    psrlq xmm7, 40",
        "    pand xmm7, xmm5",
        "    paddq xmm4, xmm7",
        "    movdqu xmm6, XMMWORD PTR [ebx+412]",
        "    paddq xmm4, xmm6",
        "    add esi, 32",
        "    sub ecx, 1",
        "    jne 2b",
        "    pop esi",
        "    pop ebx",
        "    ret",
        ".size vgx_cand_alt2, .-vgx_cand_alt2",
        ".globl vgx_cand_rot3d",
        ".type vgx_cand_rot3d, @function",
        ".p2align 6",
        "vgx_cand_rot3d:",
        "    push ebx",
        "    push esi",
        "    mov ebx, DWORD PTR [esp+12]",
        "    mov esi, DWORD PTR [esp+16]",
        "    mov ecx, DWORD PTR [esp+20]",
        "    movdqu xmm0, XMMWORD PTR [ebx+428]",
        "    movdqu xmm1, XMMWORD PTR [ebx+444]",
        "    movdqu xmm2, XMMWORD PTR [ebx+460]",
        "    movdqu xmm3, XMMWORD PTR [ebx+476]",
        "    movdqu xmm4, XMMWORD PTR [ebx+492]",
        "    .p2align 4",
        "2:",
        "    movdqu xmm7, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm7, xmm0",
        "    movdqu xmm5, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm5, xmm1",
        "    paddq xmm7, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm6, xmm2",
        "    paddq xmm7, xmm6",
        "    movdqu xmm5, XMMWORD PTR [ebx+188]",
        "    pmuludq xmm5, xmm3",
        "    paddq xmm7, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+172]",
        "    pmuludq xmm6, xmm4",
        "    paddq xmm7, xmm6",
        "    movdqu XMMWORD PTR [ebx+428], xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+124]",
        "    pmuludq xmm5, xmm0",
        "    movdqu xmm6, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm6, xmm1",
        "    paddq xmm5, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm7, xmm2",
        "    paddq xmm5, xmm7",
        "    movdqu xmm6, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm6, xmm3",
        "    paddq xmm5, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm7, xmm4",
        "    paddq xmm5, xmm7",
        "    movdqu XMMWORD PTR [ebx+476], xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm6, xmm0",
        "    movdqu xmm7, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm7, xmm1",
        "    paddq xmm6, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm5, xmm2",
        "    paddq xmm6, xmm5",
        "    movdqu xmm7, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm7, xmm3",
        "    paddq xmm6, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+188]",
        "    pmuludq xmm5, xmm4",
        "    paddq xmm6, xmm5",
        "    movdqu XMMWORD PTR [ebx+444], xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+140]",
        "    pmuludq xmm7, xmm0",
        "    movdqu xmm5, XMMWORD PTR [ebx+124]",
        "    pmuludq xmm5, xmm1",
        "    paddq xmm7, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm6, xmm2",
        "    paddq xmm7, xmm6",
        "    movdqu xmm5, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm5, xmm3",
        "    paddq xmm7, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm6, xmm4",
        "    paddq xmm7, xmm6",
        "    movdqu XMMWORD PTR [ebx+492], xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm0, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm1, xmm6",
        "    movdqu xmm5, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm2, xmm5",
        "    movdqu xmm7, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm3, xmm7",
        "    movdqu xmm6, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm4, xmm6",
        "    paddq xmm2, xmm0",
        "    paddq xmm2, xmm1",
        "    paddq xmm2, xmm3",
        "    paddq xmm2, xmm4",
        "    movdqu xmm0, XMMWORD PTR [ebx+428]",
        "    movdqu xmm3, XMMWORD PTR [ebx+476]",
        "    movdqu xmm1, XMMWORD PTR [ebx+444]",
        "    movdqu xmm4, XMMWORD PTR [ebx+492]",
        "    movdqa xmm5, xmm0",
        "    psrlq xmm5, 26",
        "    psllq xmm0, 38",
        "    psrlq xmm0, 38",
        "    paddq xmm1, xmm5",
        "    movdqa xmm7, xmm3",
        "    psrlq xmm7, 26",
        "    psllq xmm3, 38",
        "    psrlq xmm3, 38",
        "    paddq xmm4, xmm7",
        "    movdqa xmm6, xmm1",
        "    psrlq xmm6, 26",
        "    psllq xmm1, 38",
        "    psrlq xmm1, 38",
        "    paddq xmm2, xmm6",
        "    movdqa xmm5, xmm4",
        "    psrlq xmm5, 26",
        "    psllq xmm4, 38",
        "    psrlq xmm4, 38",
        "    movdqa xmm6, xmm5",
        "    psllq xmm6, 2",
        "    paddq xmm5, xmm6",
        "    paddq xmm0, xmm5",
        "    movdqa xmm7, xmm2",
        "    psrlq xmm7, 26",
        "    psllq xmm2, 38",
        "    psrlq xmm2, 38",
        "    paddq xmm3, xmm7",
        "    movdqa xmm6, xmm0",
        "    psrlq xmm6, 26",
        "    psllq xmm0, 38",
        "    psrlq xmm0, 38",
        "    paddq xmm1, xmm6",
        "    movdqa xmm7, xmm3",
        "    psrlq xmm7, 26",
        "    psllq xmm3, 38",
        "    psrlq xmm3, 38",
        "    paddq xmm4, xmm7",
        "    movq xmm5, QWORD PTR [esi+0]",
        "    movq xmm7, QWORD PTR [esi+16]",
        "    punpcklqdq xmm5, xmm7",
        "    psllq xmm5, 38",
        "    psrlq xmm5, 38",
        "    paddq xmm0, xmm5",
        "    movq xmm6, QWORD PTR [esi+0]",
        "    movq xmm7, QWORD PTR [esi+16]",
        "    punpcklqdq xmm6, xmm7",
        "    psllq xmm6, 12",
        "    psrlq xmm6, 38",
        "    paddq xmm1, xmm6",
        "    movq xmm7, QWORD PTR [esi+6]",
        "    movq xmm5, QWORD PTR [esi+22]",
        "    punpcklqdq xmm7, xmm5",
        "    psllq xmm7, 34",
        "    psrlq xmm7, 38",
        "    paddq xmm2, xmm7",
        "    movq xmm5, QWORD PTR [esi+8]",
        "    movq xmm6, QWORD PTR [esi+24]",
        "    punpcklqdq xmm5, xmm6",
        "    psllq xmm5, 24",
        "    psrlq xmm5, 38",
        "    paddq xmm3, xmm5",
        "    movq xmm6, QWORD PTR [esi+8]",
        "    movq xmm7, QWORD PTR [esi+24]",
        "    punpcklqdq xmm6, xmm7",
        "    psrlq xmm6, 40",
        "    paddq xmm4, xmm6",
        "    movdqu xmm5, XMMWORD PTR [ebx+412]",
        "    paddq xmm4, xmm5",
        "    add esi, 32",
        "    sub ecx, 1",
        "    jne 2b",
        "    pop esi",
        "    pop ebx",
        "    ret",
        ".size vgx_cand_rot3d, .-vgx_cand_rot3d",
        ".globl vgx_cand_rot3m",
        ".type vgx_cand_rot3m, @function",
        ".p2align 6",
        "vgx_cand_rot3m:",
        "    push ebx",
        "    push esi",
        "    mov ebx, DWORD PTR [esp+12]",
        "    mov esi, DWORD PTR [esp+16]",
        "    mov ecx, DWORD PTR [esp+20]",
        "    movdqu xmm0, XMMWORD PTR [ebx+428]",
        "    movdqu xmm1, XMMWORD PTR [ebx+444]",
        "    movdqu xmm2, XMMWORD PTR [ebx+460]",
        "    movdqu xmm3, XMMWORD PTR [ebx+476]",
        "    movdqu xmm4, XMMWORD PTR [ebx+492]",
        "    .p2align 4",
        "2:",
        "    movdqu xmm7, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm7, xmm0",
        "    movdqu xmm5, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm5, xmm1",
        "    paddq xmm7, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm6, xmm2",
        "    paddq xmm7, xmm6",
        "    movdqu xmm5, XMMWORD PTR [ebx+188]",
        "    pmuludq xmm5, xmm3",
        "    paddq xmm7, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+172]",
        "    pmuludq xmm6, xmm4",
        "    paddq xmm7, xmm6",
        "    movq xmm5, QWORD PTR [esi+0]",
        "    movq xmm6, QWORD PTR [esi+16]",
        "    punpcklqdq xmm5, xmm6",
        "    psllq xmm5, 38",
        "    psrlq xmm5, 38",
        "    paddq xmm7, xmm5",
        "    movdqu XMMWORD PTR [ebx+428], xmm7",
        "    movdqu xmm6, XMMWORD PTR [ebx+124]",
        "    pmuludq xmm6, xmm0",
        "    movdqu xmm5, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm5, xmm1",
        "    paddq xmm6, xmm5",
        "    movdqu xmm7, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm7, xmm2",
        "    paddq xmm6, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm5, xmm3",
        "    paddq xmm6, xmm5",
        "    movdqu xmm7, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm7, xmm4",
        "    paddq xmm6, xmm7",
        "    movq xmm5, QWORD PTR [esi+8]",
        "    movq xmm7, QWORD PTR [esi+24]",
        "    punpcklqdq xmm5, xmm7",
        "    psllq xmm5, 24",
        "    psrlq xmm5, 38",
        "    paddq xmm6, xmm5",
        "    movdqu XMMWORD PTR [ebx+476], xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm7, xmm0",
        "    movdqu xmm5, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm5, xmm1",
        "    paddq xmm7, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm6, xmm2",
        "    paddq xmm7, xmm6",
        "    movdqu xmm5, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm5, xmm3",
        "    paddq xmm7, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+188]",
        "    pmuludq xmm6, xmm4",
        "    paddq xmm7, xmm6",
        "    movq xmm5, QWORD PTR [esi+0]",
        "    movq xmm6, QWORD PTR [esi+16]",
        "    punpcklqdq xmm5, xmm6",
        "    psllq xmm5, 12",
        "    psrlq xmm5, 38",
        "    paddq xmm7, xmm5",
        "    movdqu XMMWORD PTR [ebx+444], xmm7",
        "    movdqu xmm6, XMMWORD PTR [ebx+140]",
        "    pmuludq xmm6, xmm0",
        "    movdqu xmm5, XMMWORD PTR [ebx+124]",
        "    pmuludq xmm5, xmm1",
        "    paddq xmm6, xmm5",
        "    movdqu xmm7, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm7, xmm2",
        "    paddq xmm6, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm5, xmm3",
        "    paddq xmm6, xmm5",
        "    movdqu xmm7, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm7, xmm4",
        "    paddq xmm6, xmm7",
        "    movq xmm5, QWORD PTR [esi+8]",
        "    movq xmm7, QWORD PTR [esi+24]",
        "    punpcklqdq xmm5, xmm7",
        "    psrlq xmm5, 40",
        "    paddq xmm6, xmm5",
        "    movdqu xmm7, XMMWORD PTR [ebx+412]",
        "    paddq xmm6, xmm7",
        "    movdqu XMMWORD PTR [ebx+492], xmm6",
        "    movdqu xmm5, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm0, xmm5",
        "    movdqu xmm7, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm1, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm2, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm3, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm4, xmm7",
        "    paddq xmm2, xmm0",
        "    paddq xmm2, xmm1",
        "    paddq xmm2, xmm3",
        "    paddq xmm2, xmm4",
        "    movq xmm5, QWORD PTR [esi+6]",
        "    movq xmm6, QWORD PTR [esi+22]",
        "    punpcklqdq xmm5, xmm6",
        "    psllq xmm5, 34",
        "    psrlq xmm5, 38",
        "    paddq xmm2, xmm5",
        "    movdqu xmm0, XMMWORD PTR [ebx+428]",
        "    movdqu xmm3, XMMWORD PTR [ebx+476]",
        "    movdqu xmm1, XMMWORD PTR [ebx+444]",
        "    movdqu xmm4, XMMWORD PTR [ebx+492]",
        "    movdqa xmm7, xmm0",
        "    psrlq xmm7, 26",
        "    psllq xmm0, 38",
        "    psrlq xmm0, 38",
        "    paddq xmm1, xmm7",
        "    movdqa xmm6, xmm3",
        "    psrlq xmm6, 26",
        "    psllq xmm3, 38",
        "    psrlq xmm3, 38",
        "    paddq xmm4, xmm6",
        "    movdqa xmm7, xmm1",
        "    psrlq xmm7, 26",
        "    psllq xmm1, 38",
        "    psrlq xmm1, 38",
        "    paddq xmm2, xmm7",
        "    movdqa xmm5, xmm4",
        "    psrlq xmm5, 26",
        "    psllq xmm4, 38",
        "    psrlq xmm4, 38",
        "    movdqa xmm6, xmm5",
        "    psllq xmm6, 2",
        "    paddq xmm5, xmm6",
        "    paddq xmm0, xmm5",
        "    movdqa xmm7, xmm2",
        "    psrlq xmm7, 26",
        "    psllq xmm2, 38",
        "    psrlq xmm2, 38",
        "    paddq xmm3, xmm7",
        "    movdqa xmm6, xmm0",
        "    psrlq xmm6, 26",
        "    psllq xmm0, 38",
        "    psrlq xmm0, 38",
        "    paddq xmm1, xmm6",
        "    movdqa xmm5, xmm3",
        "    psrlq xmm5, 26",
        "    psllq xmm3, 38",
        "    psrlq xmm3, 38",
        "    paddq xmm4, xmm5",
        "    add esi, 32",
        "    sub ecx, 1",
        "    jne 2b",
        "    pop esi",
        "    pop ebx",
        "    ret",
        ".size vgx_cand_rot3m, .-vgx_cand_rot3m",
        ".globl vgx_cand_frame",
        ".type vgx_cand_frame, @function",
        ".p2align 6",
        "vgx_cand_frame:",
        "    push ebx",
        "    push esi",
        "    mov ebx, DWORD PTR [esp+12]",
        "    mov esi, DWORD PTR [esp+16]",
        "    mov ecx, DWORD PTR [esp+20]",
        "    movdqu xmm0, XMMWORD PTR [ebx+428]",
        "    movdqu xmm1, XMMWORD PTR [ebx+444]",
        "    movdqu xmm2, XMMWORD PTR [ebx+460]",
        "    movdqu xmm3, XMMWORD PTR [ebx+476]",
        "    movdqu xmm4, XMMWORD PTR [ebx+492]",
        "    .p2align 4",
        "2:",
        "    movdqu xmm0, XMMWORD PTR [ebx+428]",
        "    movdqu xmm7, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm0, xmm7",
        "    movdqu xmm7, XMMWORD PTR [ebx+444]",
        "    movdqu xmm2, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm7, xmm2",
        "    paddq xmm0, xmm7",
        "    movdqu xmm6, XMMWORD PTR [ebx+460]",
        "    movdqu xmm2, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm6, xmm2",
        "    paddq xmm0, xmm6",
        "    movdqu xmm5, XMMWORD PTR [ebx+476]",
        "    movdqu xmm1, XMMWORD PTR [ebx+188]",
        "    pmuludq xmm5, xmm1",
        "    paddq xmm0, xmm5",
        "    movdqu xmm3, XMMWORD PTR [ebx+492]",
        "    movdqu xmm2, XMMWORD PTR [ebx+172]",
        "    pmuludq xmm3, xmm2",
        "    paddq xmm0, xmm3",
        "    movdqu xmm1, XMMWORD PTR [ebx+428]",
        "    movdqu xmm4, XMMWORD PTR [ebx+124]",
        "    pmuludq xmm1, xmm4",
        "    movdqu xmm2, XMMWORD PTR [ebx+444]",
        "    movdqu xmm4, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm2, xmm4",
        "    paddq xmm1, xmm2",
        "    movdqu xmm7, XMMWORD PTR [ebx+460]",
        "    movdqu xmm4, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm7, xmm4",
        "    paddq xmm1, xmm7",
        "    movdqu xmm6, XMMWORD PTR [ebx+476]",
        "    movdqu xmm4, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm6, xmm4",
        "    paddq xmm1, xmm6",
        "    movdqu xmm2, XMMWORD PTR [ebx+492]",
        "    movdqu xmm5, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm2, xmm5",
        "    paddq xmm1, xmm2",
        "    movdqu xmm4, XMMWORD PTR [ebx+428]",
        "    movdqu xmm5, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm4, xmm5",
        "    movdqu xmm7, XMMWORD PTR [ebx+444]",
        "    movdqu xmm3, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm7, xmm3",
        "    paddq xmm4, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+460]",
        "    movdqu xmm6, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm5, xmm6",
        "    paddq xmm4, xmm5",
        "    movdqu xmm2, XMMWORD PTR [ebx+476]",
        "    movdqu xmm3, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm2, xmm3",
        "    paddq xmm4, xmm2",
        "    movdqu xmm6, XMMWORD PTR [ebx+492]",
        "    movdqu xmm3, XMMWORD PTR [ebx+188]",
        "    pmuludq xmm6, xmm3",
        "    paddq xmm4, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+428]",
        "    movdqu xmm3, XMMWORD PTR [ebx+140]",
        "    pmuludq xmm7, xmm3",
        "    movdqu xmm5, XMMWORD PTR [ebx+444]",
        "    movdqu xmm2, XMMWORD PTR [ebx+124]",
        "    pmuludq xmm5, xmm2",
        "    paddq xmm7, xmm5",
        "    movdqu xmm3, XMMWORD PTR [ebx+460]",
        "    movdqu xmm2, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm3, xmm2",
        "    paddq xmm7, xmm3",
        "    movdqu xmm6, XMMWORD PTR [ebx+476]",
        "    movdqu xmm2, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm6, xmm2",
        "    paddq xmm7, xmm6",
        "    movdqu xmm5, XMMWORD PTR [ebx+492]",
        "    movdqu xmm2, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm5, xmm2",
        "    paddq xmm7, xmm5",
        "    movdqu xmm3, XMMWORD PTR [ebx+428]",
        "    movdqu xmm2, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm3, xmm2",
        "    movdqu xmm6, XMMWORD PTR [ebx+444]",
        "    movdqu xmm2, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm6, xmm2",
        "    paddq xmm3, xmm6",
        "    movdqu xmm5, XMMWORD PTR [ebx+460]",
        "    movdqu xmm2, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm5, xmm2",
        "    paddq xmm3, xmm5",
        "    movdqu xmm2, XMMWORD PTR [ebx+476]",
        "    movdqu xmm6, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm2, xmm6",
        "    paddq xmm3, xmm2",
        "    movdqu xmm5, XMMWORD PTR [ebx+492]",
        "    movdqu xmm6, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm5, xmm6",
        "    paddq xmm3, xmm5",
        "    movdqa xmm6, xmm0",
        "    psrlq xmm6, 26",
        "    psllq xmm0, 38",
        "    psrlq xmm0, 38",
        "    paddq xmm4, xmm6",
        "    movdqa xmm2, xmm1",
        "    psrlq xmm2, 26",
        "    psllq xmm1, 38",
        "    psrlq xmm1, 38",
        "    paddq xmm7, xmm2",
        "    movdqa xmm6, xmm4",
        "    psrlq xmm6, 26",
        "    psllq xmm4, 38",
        "    psrlq xmm4, 38",
        "    paddq xmm3, xmm6",
        "    movdqa xmm2, xmm7",
        "    psrlq xmm2, 26",
        "    psllq xmm7, 38",
        "    psrlq xmm7, 38",
        "    movdqa xmm5, xmm2",
        "    psllq xmm5, 2",
        "    paddq xmm2, xmm5",
        "    paddq xmm0, xmm2",
        "    movdqa xmm6, xmm3",
        "    psrlq xmm6, 26",
        "    psllq xmm3, 38",
        "    psrlq xmm3, 38",
        "    paddq xmm1, xmm6",
        "    movdqa xmm5, xmm0",
        "    psrlq xmm5, 26",
        "    psllq xmm0, 38",
        "    psrlq xmm0, 38",
        "    paddq xmm4, xmm5",
        "    movdqa xmm6, xmm1",
        "    psrlq xmm6, 26",
        "    psllq xmm1, 38",
        "    psrlq xmm1, 38",
        "    paddq xmm7, xmm6",
        "    movq xmm2, QWORD PTR [esi+0]",
        "    movq xmm6, QWORD PTR [esi+16]",
        "    punpcklqdq xmm2, xmm6",
        "    psllq xmm2, 38",
        "    psrlq xmm2, 38",
        "    paddq xmm0, xmm2",
        "    movq xmm5, QWORD PTR [esi+0]",
        "    movq xmm6, QWORD PTR [esi+16]",
        "    punpcklqdq xmm5, xmm6",
        "    psllq xmm5, 12",
        "    psrlq xmm5, 38",
        "    paddq xmm4, xmm5",
        "    movq xmm6, QWORD PTR [esi+6]",
        "    movq xmm2, QWORD PTR [esi+22]",
        "    punpcklqdq xmm6, xmm2",
        "    psllq xmm6, 34",
        "    psrlq xmm6, 38",
        "    paddq xmm3, xmm6",
        "    movq xmm2, QWORD PTR [esi+8]",
        "    movq xmm5, QWORD PTR [esi+24]",
        "    punpcklqdq xmm2, xmm5",
        "    psllq xmm2, 24",
        "    psrlq xmm2, 38",
        "    paddq xmm1, xmm2",
        "    movq xmm5, QWORD PTR [esi+8]",
        "    movq xmm6, QWORD PTR [esi+24]",
        "    punpcklqdq xmm5, xmm6",
        "    psrlq xmm5, 40",
        "    paddq xmm7, xmm5",
        "    movdqu xmm2, XMMWORD PTR [ebx+412]",
        "    paddq xmm7, xmm2",
        "    movdqu XMMWORD PTR [ebx+428], xmm0",
        "    movdqu XMMWORD PTR [ebx+444], xmm4",
        "    movdqu XMMWORD PTR [ebx+460], xmm3",
        "    movdqu XMMWORD PTR [ebx+476], xmm1",
        "    movdqu XMMWORD PTR [ebx+492], xmm7",
        "    add esi, 32",
        "    sub ecx, 1",
        "    jne 2b",
        "    pop esi",
        "    pop ebx",
        "    ret",
        ".size vgx_cand_frame, .-vgx_cand_frame",
        ".globl vgx_cand_frame_k2",
        ".type vgx_cand_frame_k2, @function",
        ".p2align 6",
        "vgx_cand_frame_k2:",
        "    push ebx",
        "    push esi",
        "    mov ebx, DWORD PTR [esp+12]",
        "    mov esi, DWORD PTR [esp+16]",
        "    mov ecx, DWORD PTR [esp+20]",
        "    movdqu xmm0, XMMWORD PTR [ebx+428]",
        "    movdqu xmm1, XMMWORD PTR [ebx+444]",
        "    movdqu xmm2, XMMWORD PTR [ebx+460]",
        "    movdqu xmm3, XMMWORD PTR [ebx+476]",
        "    movdqu xmm4, XMMWORD PTR [ebx+492]",
        "    .p2align 4",
        "2:",
        "    movdqu xmm4, XMMWORD PTR [ebx+428]",
        "    movdqu xmm7, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm4, xmm7",
        "    movdqu xmm7, XMMWORD PTR [ebx+444]",
        "    movdqu xmm0, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm7, xmm0",
        "    paddq xmm4, xmm7",
        "    movdqu xmm3, XMMWORD PTR [ebx+460]",
        "    movdqu xmm0, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm3, xmm0",
        "    paddq xmm4, xmm3",
        "    movdqu xmm2, XMMWORD PTR [ebx+476]",
        "    movdqu xmm1, XMMWORD PTR [ebx+188]",
        "    pmuludq xmm2, xmm1",
        "    paddq xmm4, xmm2",
        "    movdqu xmm6, XMMWORD PTR [ebx+492]",
        "    movdqu xmm0, XMMWORD PTR [ebx+172]",
        "    pmuludq xmm6, xmm0",
        "    paddq xmm4, xmm6",
        "    movdqu XMMWORD PTR [ebx+508], xmm4",
        "    movdqu xmm1, XMMWORD PTR [ebx+428]",
        "    movdqu xmm5, XMMWORD PTR [ebx+124]",
        "    pmuludq xmm1, xmm5",
        "    movdqu xmm0, XMMWORD PTR [ebx+444]",
        "    movdqu xmm5, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm0, xmm5",
        "    paddq xmm1, xmm0",
        "    movdqu xmm7, XMMWORD PTR [ebx+460]",
        "    movdqu xmm5, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm7, xmm5",
        "    paddq xmm1, xmm7",
        "    movdqu xmm3, XMMWORD PTR [ebx+476]",
        "    movdqu xmm5, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm3, xmm5",
        "    paddq xmm1, xmm3",
        "    movdqu xmm0, XMMWORD PTR [ebx+492]",
        "    movdqu xmm2, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm0, xmm2",
        "    paddq xmm1, xmm0",
        "    movdqu XMMWORD PTR [ebx+44], xmm1",
        "    movdqu xmm5, XMMWORD PTR [ebx+428]",
        "    movdqu xmm2, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm5, xmm2",
        "    movdqu xmm7, XMMWORD PTR [ebx+444]",
        "    movdqu xmm6, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm7, xmm6",
        "    paddq xmm5, xmm7",
        "    movdqu xmm2, XMMWORD PTR [ebx+460]",
        "    movdqu xmm3, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm2, xmm3",
        "    paddq xmm5, xmm2",
        "    movdqu xmm4, XMMWORD PTR [ebx+476]",
        "    movdqu xmm0, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm4, xmm0",
        "    paddq xmm5, xmm4",
        "    movdqu xmm6, XMMWORD PTR [ebx+492]",
        "    movdqu xmm1, XMMWORD PTR [ebx+188]",
        "    pmuludq xmm6, xmm1",
        "    paddq xmm5, xmm6",
        "    movdqu XMMWORD PTR [ebx+60], xmm5",
        "    movdqu xmm3, XMMWORD PTR [ebx+428]",
        "    movdqu xmm0, XMMWORD PTR [ebx+140]",
        "    pmuludq xmm3, xmm0",
        "    movdqu xmm1, XMMWORD PTR [ebx+444]",
        "    movdqu xmm7, XMMWORD PTR [ebx+124]",
        "    pmuludq xmm1, xmm7",
        "    paddq xmm3, xmm1",
        "    movdqu xmm0, XMMWORD PTR [ebx+460]",
        "    movdqu xmm2, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm0, xmm2",
        "    paddq xmm3, xmm0",
        "    movdqu xmm4, XMMWORD PTR [ebx+476]",
        "    movdqu xmm7, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm4, xmm7",
        "    paddq xmm3, xmm4",
        "    movdqu xmm2, XMMWORD PTR [ebx+492]",
        "    movdqu xmm6, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm2, xmm6",
        "    paddq xmm3, xmm2",
        "    movdqu xmm5, XMMWORD PTR [ebx+428]",
        "    movdqu xmm7, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm5, xmm7",
        "    movdqu xmm1, XMMWORD PTR [ebx+444]",
        "    movdqu xmm6, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm1, xmm6",
        "    paddq xmm5, xmm1",
        "    movdqu xmm0, XMMWORD PTR [ebx+460]",
        "    movdqu xmm7, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm0, xmm7",
        "    paddq xmm5, xmm0",
        "    movdqu xmm4, XMMWORD PTR [ebx+476]",
        "    movdqu xmm6, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm4, xmm6",
        "    paddq xmm5, xmm4",
        "    movdqu xmm2, XMMWORD PTR [ebx+492]",
        "    movdqu xmm7, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm2, xmm7",
        "    paddq xmm5, xmm2",
        "    movdqu xmm6, XMMWORD PTR [ebx+508]",
        "    movdqu xmm1, XMMWORD PTR [ebx+44]",
        "    movdqu xmm7, XMMWORD PTR [ebx+60]",
        "    movdqa xmm0, xmm6",
        "    psrlq xmm0, 26",
        "    psllq xmm6, 38",
        "    psrlq xmm6, 38",
        "    paddq xmm7, xmm0",
        "    movdqa xmm4, xmm1",
        "    psrlq xmm4, 26",
        "    psllq xmm1, 38",
        "    psrlq xmm1, 38",
        "    paddq xmm3, xmm4",
        "    movdqa xmm0, xmm7",
        "    psrlq xmm0, 26",
        "    psllq xmm7, 38",
        "    psrlq xmm7, 38",
        "    paddq xmm5, xmm0",
        "    movdqa xmm2, xmm3",
        "    psrlq xmm2, 26",
        "    psllq xmm3, 38",
        "    psrlq xmm3, 38",
        "    movdqa xmm4, xmm2",
        "    psllq xmm4, 2",
        "    paddq xmm2, xmm4",
        "    paddq xmm6, xmm2",
        "    movdqa xmm0, xmm5",
        "    psrlq xmm0, 26",
        "    psllq xmm5, 38",
        "    psrlq xmm5, 38",
        "    paddq xmm1, xmm0",
        "    movdqa xmm0, xmm6",
        "    psrlq xmm0, 26",
        "    psllq xmm6, 38",
        "    psrlq xmm6, 38",
        "    paddq xmm7, xmm0",
        "    movdqa xmm4, xmm1",
        "    psrlq xmm4, 26",
        "    psllq xmm1, 38",
        "    psrlq xmm1, 38",
        "    paddq xmm3, xmm4",
        "    movq xmm2, QWORD PTR [esi+0]",
        "    movq xmm4, QWORD PTR [esi+16]",
        "    punpcklqdq xmm2, xmm4",
        "    psllq xmm2, 38",
        "    psrlq xmm2, 38",
        "    paddq xmm6, xmm2",
        "    movq xmm0, QWORD PTR [esi+0]",
        "    movq xmm4, QWORD PTR [esi+16]",
        "    punpcklqdq xmm0, xmm4",
        "    psllq xmm0, 12",
        "    psrlq xmm0, 38",
        "    paddq xmm7, xmm0",
        "    movq xmm4, QWORD PTR [esi+6]",
        "    movq xmm2, QWORD PTR [esi+22]",
        "    punpcklqdq xmm4, xmm2",
        "    psllq xmm4, 34",
        "    psrlq xmm4, 38",
        "    paddq xmm5, xmm4",
        "    movq xmm0, QWORD PTR [esi+8]",
        "    movq xmm2, QWORD PTR [esi+24]",
        "    punpcklqdq xmm0, xmm2",
        "    psllq xmm0, 24",
        "    psrlq xmm0, 38",
        "    paddq xmm1, xmm0",
        "    movq xmm2, QWORD PTR [esi+8]",
        "    movq xmm4, QWORD PTR [esi+24]",
        "    punpcklqdq xmm2, xmm4",
        "    psrlq xmm2, 40",
        "    paddq xmm3, xmm2",
        "    movdqu xmm0, XMMWORD PTR [ebx+412]",
        "    paddq xmm3, xmm0",
        "    movdqu XMMWORD PTR [ebx+428], xmm6",
        "    movdqu XMMWORD PTR [ebx+444], xmm7",
        "    movdqu XMMWORD PTR [ebx+460], xmm5",
        "    movdqu XMMWORD PTR [ebx+476], xmm1",
        "    movdqu XMMWORD PTR [ebx+492], xmm3",
        "    add esi, 32",
        "    sub ecx, 1",
        "    jne 2b",
        "    pop esi",
        "    pop ebx",
        "    ret",
        ".size vgx_cand_frame_k2, .-vgx_cand_frame_k2",
        ".globl vgx_cand_fg_3_2",
        ".type vgx_cand_fg_3_2, @function",
        ".p2align 6",
        "vgx_cand_fg_3_2:",
        "    push ebx",
        "    push esi",
        "    mov ebx, DWORD PTR [esp+12]",
        "    mov esi, DWORD PTR [esp+16]",
        "    mov ecx, DWORD PTR [esp+20]",
        "    movdqu xmm0, XMMWORD PTR [ebx+428]",
        "    movdqu xmm1, XMMWORD PTR [ebx+444]",
        "    movdqu xmm2, XMMWORD PTR [ebx+460]",
        "    movdqu xmm3, XMMWORD PTR [ebx+476]",
        "    movdqu xmm4, XMMWORD PTR [ebx+492]",
        "    .p2align 4",
        "2:",
        "    movdqu xmm0, XMMWORD PTR [ebx+428]",
        "    movdqu xmm3, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm3, xmm0",
        "    movdqu xmm6, XMMWORD PTR [ebx+124]",
        "    pmuludq xmm6, xmm0",
        "    movdqu xmm2, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm2, xmm0",
        "    movdqu xmm0, XMMWORD PTR [ebx+444]",
        "    movdqu xmm4, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm4, xmm0",
        "    paddq xmm3, xmm4",
        "    movdqu xmm1, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm1, xmm0",
        "    paddq xmm6, xmm1",
        "    movdqu xmm7, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm7, xmm0",
        "    paddq xmm2, xmm7",
        "    movdqu xmm0, XMMWORD PTR [ebx+460]",
        "    movdqu xmm5, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm5, xmm0",
        "    paddq xmm3, xmm5",
        "    movdqu xmm4, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm4, xmm0",
        "    paddq xmm6, xmm4",
        "    movdqu xmm1, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm1, xmm0",
        "    paddq xmm2, xmm1",
        "    movdqu xmm0, XMMWORD PTR [ebx+476]",
        "    movdqu xmm7, XMMWORD PTR [ebx+188]",
        "    pmuludq xmm7, xmm0",
        "    paddq xmm3, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm5, xmm0",
        "    paddq xmm6, xmm5",
        "    movdqu xmm4, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm4, xmm0",
        "    paddq xmm2, xmm4",
        "    movdqu xmm0, XMMWORD PTR [ebx+492]",
        "    movdqu xmm1, XMMWORD PTR [ebx+172]",
        "    pmuludq xmm1, xmm0",
        "    paddq xmm3, xmm1",
        "    movdqu xmm7, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm7, xmm0",
        "    paddq xmm6, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+188]",
        "    pmuludq xmm5, xmm0",
        "    paddq xmm2, xmm5",
        "    movdqu XMMWORD PTR [ebx+508], xmm3",
        "    movdqu XMMWORD PTR [ebx+44], xmm6",
        "    movdqu XMMWORD PTR [ebx+60], xmm2",
        "    movdqu xmm0, XMMWORD PTR [ebx+428]",
        "    movdqu xmm4, XMMWORD PTR [ebx+140]",
        "    pmuludq xmm4, xmm0",
        "    movdqu xmm1, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm1, xmm0",
        "    movdqu xmm0, XMMWORD PTR [ebx+444]",
        "    movdqu xmm7, XMMWORD PTR [ebx+124]",
        "    pmuludq xmm7, xmm0",
        "    paddq xmm4, xmm7",
        "    movdqu xmm3, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm3, xmm0",
        "    paddq xmm1, xmm3",
        "    movdqu xmm0, XMMWORD PTR [ebx+460]",
        "    movdqu xmm6, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm6, xmm0",
        "    paddq xmm4, xmm6",
        "    movdqu xmm5, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm5, xmm0",
        "    paddq xmm1, xmm5",
        "    movdqu xmm0, XMMWORD PTR [ebx+476]",
        "    movdqu xmm2, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm2, xmm0",
        "    paddq xmm4, xmm2",
        "    movdqu xmm7, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm7, xmm0",
        "    paddq xmm1, xmm7",
        "    movdqu xmm0, XMMWORD PTR [ebx+492]",
        "    movdqu xmm3, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm3, xmm0",
        "    paddq xmm4, xmm3",
        "    movdqu xmm6, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm6, xmm0",
        "    paddq xmm1, xmm6",
        "    movdqu xmm0, XMMWORD PTR [ebx+508]",
        "    movdqu xmm5, XMMWORD PTR [ebx+44]",
        "    movdqu xmm2, XMMWORD PTR [ebx+60]",
        "    movdqa xmm7, xmm0",
        "    psrlq xmm7, 26",
        "    psllq xmm0, 38",
        "    psrlq xmm0, 38",
        "    paddq xmm2, xmm7",
        "    movdqa xmm3, xmm5",
        "    psrlq xmm3, 26",
        "    psllq xmm5, 38",
        "    psrlq xmm5, 38",
        "    paddq xmm4, xmm3",
        "    movdqa xmm6, xmm2",
        "    psrlq xmm6, 26",
        "    psllq xmm2, 38",
        "    psrlq xmm2, 38",
        "    paddq xmm1, xmm6",
        "    movdqa xmm7, xmm4",
        "    psrlq xmm7, 26",
        "    psllq xmm4, 38",
        "    psrlq xmm4, 38",
        "    movdqa xmm3, xmm7",
        "    psllq xmm3, 2",
        "    paddq xmm7, xmm3",
        "    paddq xmm0, xmm7",
        "    movdqa xmm6, xmm1",
        "    psrlq xmm6, 26",
        "    psllq xmm1, 38",
        "    psrlq xmm1, 38",
        "    paddq xmm5, xmm6",
        "    movdqa xmm3, xmm0",
        "    psrlq xmm3, 26",
        "    psllq xmm0, 38",
        "    psrlq xmm0, 38",
        "    paddq xmm2, xmm3",
        "    movdqa xmm6, xmm5",
        "    psrlq xmm6, 26",
        "    psllq xmm5, 38",
        "    psrlq xmm5, 38",
        "    paddq xmm4, xmm6",
        "    movq xmm7, QWORD PTR [esi+0]",
        "    movq xmm6, QWORD PTR [esi+16]",
        "    punpcklqdq xmm7, xmm6",
        "    psllq xmm7, 38",
        "    psrlq xmm7, 38",
        "    paddq xmm0, xmm7",
        "    movq xmm3, QWORD PTR [esi+0]",
        "    movq xmm6, QWORD PTR [esi+16]",
        "    punpcklqdq xmm3, xmm6",
        "    psllq xmm3, 12",
        "    psrlq xmm3, 38",
        "    paddq xmm2, xmm3",
        "    movq xmm6, QWORD PTR [esi+6]",
        "    movq xmm7, QWORD PTR [esi+22]",
        "    punpcklqdq xmm6, xmm7",
        "    psllq xmm6, 34",
        "    psrlq xmm6, 38",
        "    paddq xmm1, xmm6",
        "    movq xmm3, QWORD PTR [esi+8]",
        "    movq xmm7, QWORD PTR [esi+24]",
        "    punpcklqdq xmm3, xmm7",
        "    psllq xmm3, 24",
        "    psrlq xmm3, 38",
        "    paddq xmm5, xmm3",
        "    movq xmm7, QWORD PTR [esi+8]",
        "    movq xmm6, QWORD PTR [esi+24]",
        "    punpcklqdq xmm7, xmm6",
        "    psrlq xmm7, 40",
        "    paddq xmm4, xmm7",
        "    movdqu xmm3, XMMWORD PTR [ebx+412]",
        "    paddq xmm4, xmm3",
        "    movdqu XMMWORD PTR [ebx+428], xmm0",
        "    movdqu XMMWORD PTR [ebx+444], xmm2",
        "    movdqu XMMWORD PTR [ebx+460], xmm1",
        "    movdqu XMMWORD PTR [ebx+476], xmm5",
        "    movdqu XMMWORD PTR [ebx+492], xmm4",
        "    add esi, 32",
        "    sub ecx, 1",
        "    jne 2b",
        "    pop esi",
        "    pop ebx",
        "    ret",
        ".size vgx_cand_fg_3_2, .-vgx_cand_fg_3_2",
        ".globl vgx_cand_frame_d",
        ".type vgx_cand_frame_d, @function",
        ".p2align 6",
        "vgx_cand_frame_d:",
        "    push ebx",
        "    push esi",
        "    mov ebx, DWORD PTR [esp+12]",
        "    mov esi, DWORD PTR [esp+16]",
        "    mov ecx, DWORD PTR [esp+20]",
        "    movdqu xmm0, XMMWORD PTR [ebx+428]",
        "    movdqu xmm1, XMMWORD PTR [ebx+444]",
        "    movdqu xmm2, XMMWORD PTR [ebx+460]",
        "    movdqu xmm3, XMMWORD PTR [ebx+476]",
        "    movdqu xmm4, XMMWORD PTR [ebx+492]",
        "    .p2align 4",
        "2:",
        "    movdqu xmm7, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm0, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm1, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm2, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+188]",
        "    pmuludq xmm3, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+172]",
        "    pmuludq xmm4, xmm5",
        "    paddq xmm0, xmm1",
        "    paddq xmm0, xmm2",
        "    paddq xmm0, xmm3",
        "    paddq xmm0, xmm4",
        "    movdqu xmm3, XMMWORD PTR [ebx+428]",
        "    movdqu xmm6, XMMWORD PTR [ebx+124]",
        "    pmuludq xmm3, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+444]",
        "    movdqu xmm5, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm7, xmm5",
        "    paddq xmm3, xmm7",
        "    movdqu xmm6, XMMWORD PTR [ebx+460]",
        "    movdqu xmm1, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm6, xmm1",
        "    paddq xmm3, xmm6",
        "    movdqu xmm2, XMMWORD PTR [ebx+476]",
        "    movdqu xmm5, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm2, xmm5",
        "    paddq xmm3, xmm2",
        "    movdqu xmm1, XMMWORD PTR [ebx+492]",
        "    movdqu xmm4, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm1, xmm4",
        "    paddq xmm3, xmm1",
        "    movdqu xmm1, XMMWORD PTR [ebx+428]",
        "    movdqu xmm5, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm1, xmm5",
        "    movdqu xmm4, XMMWORD PTR [ebx+444]",
        "    movdqu xmm7, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm4, xmm7",
        "    paddq xmm1, xmm4",
        "    movdqu xmm5, XMMWORD PTR [ebx+460]",
        "    movdqu xmm6, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm5, xmm6",
        "    paddq xmm1, xmm5",
        "    movdqu xmm2, XMMWORD PTR [ebx+476]",
        "    movdqu xmm7, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm2, xmm7",
        "    paddq xmm1, xmm2",
        "    movdqu xmm6, XMMWORD PTR [ebx+492]",
        "    movdqu xmm7, XMMWORD PTR [ebx+188]",
        "    pmuludq xmm6, xmm7",
        "    paddq xmm1, xmm6",
        "    movdqu xmm4, XMMWORD PTR [ebx+428]",
        "    movdqu xmm5, XMMWORD PTR [ebx+140]",
        "    pmuludq xmm4, xmm5",
        "    movdqu xmm7, XMMWORD PTR [ebx+444]",
        "    movdqu xmm2, XMMWORD PTR [ebx+124]",
        "    pmuludq xmm7, xmm2",
        "    paddq xmm4, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+460]",
        "    movdqu xmm2, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm5, xmm2",
        "    paddq xmm4, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+476]",
        "    movdqu xmm2, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm6, xmm2",
        "    paddq xmm4, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+492]",
        "    movdqu xmm2, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm7, xmm2",
        "    paddq xmm4, xmm7",
        "    movdqu xmm2, XMMWORD PTR [ebx+428]",
        "    movdqu xmm5, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm2, xmm5",
        "    movdqu xmm5, XMMWORD PTR [ebx+444]",
        "    movdqu xmm6, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm5, xmm6",
        "    paddq xmm2, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+460]",
        "    movdqu xmm7, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm6, xmm7",
        "    paddq xmm2, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+476]",
        "    movdqu xmm5, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm7, xmm5",
        "    paddq xmm2, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+492]",
        "    movdqu xmm6, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm5, xmm6",
        "    paddq xmm2, xmm5",
        "    movdqa xmm6, xmm0",
        "    psrlq xmm6, 26",
        "    psllq xmm0, 38",
        "    psrlq xmm0, 38",
        "    paddq xmm1, xmm6",
        "    movdqa xmm7, xmm3",
        "    psrlq xmm7, 26",
        "    psllq xmm3, 38",
        "    psrlq xmm3, 38",
        "    paddq xmm4, xmm7",
        "    movdqa xmm6, xmm1",
        "    psrlq xmm6, 26",
        "    psllq xmm1, 38",
        "    psrlq xmm1, 38",
        "    paddq xmm2, xmm6",
        "    movdqa xmm5, xmm4",
        "    psrlq xmm5, 26",
        "    psllq xmm4, 38",
        "    psrlq xmm4, 38",
        "    movdqa xmm7, xmm5",
        "    psllq xmm7, 2",
        "    paddq xmm5, xmm7",
        "    paddq xmm0, xmm5",
        "    movdqa xmm6, xmm2",
        "    psrlq xmm6, 26",
        "    psllq xmm2, 38",
        "    psrlq xmm2, 38",
        "    paddq xmm3, xmm6",
        "    movdqa xmm6, xmm0",
        "    psrlq xmm6, 26",
        "    psllq xmm0, 38",
        "    psrlq xmm0, 38",
        "    paddq xmm1, xmm6",
        "    movdqa xmm7, xmm3",
        "    psrlq xmm7, 26",
        "    psllq xmm3, 38",
        "    psrlq xmm3, 38",
        "    paddq xmm4, xmm7",
        "    movq xmm5, QWORD PTR [esi+0]",
        "    movq xmm7, QWORD PTR [esi+16]",
        "    punpcklqdq xmm5, xmm7",
        "    psllq xmm5, 38",
        "    psrlq xmm5, 38",
        "    paddq xmm0, xmm5",
        "    movq xmm6, QWORD PTR [esi+0]",
        "    movq xmm7, QWORD PTR [esi+16]",
        "    punpcklqdq xmm6, xmm7",
        "    psllq xmm6, 12",
        "    psrlq xmm6, 38",
        "    paddq xmm1, xmm6",
        "    movq xmm7, QWORD PTR [esi+6]",
        "    movq xmm5, QWORD PTR [esi+22]",
        "    punpcklqdq xmm7, xmm5",
        "    psllq xmm7, 34",
        "    psrlq xmm7, 38",
        "    paddq xmm2, xmm7",
        "    movq xmm5, QWORD PTR [esi+8]",
        "    movq xmm6, QWORD PTR [esi+24]",
        "    punpcklqdq xmm5, xmm6",
        "    psllq xmm5, 24",
        "    psrlq xmm5, 38",
        "    paddq xmm3, xmm5",
        "    movq xmm6, QWORD PTR [esi+8]",
        "    movq xmm7, QWORD PTR [esi+24]",
        "    punpcklqdq xmm6, xmm7",
        "    psrlq xmm6, 40",
        "    paddq xmm4, xmm6",
        "    movdqu xmm5, XMMWORD PTR [ebx+412]",
        "    paddq xmm4, xmm5",
        "    movdqu XMMWORD PTR [ebx+428], xmm0",
        "    movdqu XMMWORD PTR [ebx+444], xmm1",
        "    movdqu XMMWORD PTR [ebx+460], xmm2",
        "    movdqu XMMWORD PTR [ebx+476], xmm3",
        "    movdqu XMMWORD PTR [ebx+492], xmm4",
        "    add esi, 32",
        "    sub ecx, 1",
        "    jne 2b",
        "    pop esi",
        "    pop ebx",
        "    ret",
        ".size vgx_cand_frame_d, .-vgx_cand_frame_d",
        ".globl vgx_cand_fd_g22",
        ".type vgx_cand_fd_g22, @function",
        ".p2align 6",
        "vgx_cand_fd_g22:",
        "    push ebx",
        "    push esi",
        "    mov ebx, DWORD PTR [esp+12]",
        "    mov esi, DWORD PTR [esp+16]",
        "    mov ecx, DWORD PTR [esp+20]",
        "    movdqu xmm0, XMMWORD PTR [ebx+428]",
        "    movdqu xmm1, XMMWORD PTR [ebx+444]",
        "    movdqu xmm2, XMMWORD PTR [ebx+460]",
        "    movdqu xmm3, XMMWORD PTR [ebx+476]",
        "    movdqu xmm4, XMMWORD PTR [ebx+492]",
        "    .p2align 4",
        "2:",
        "    movdqu xmm6, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm0, xmm6",
        "    movdqu xmm5, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm1, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm2, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+188]",
        "    pmuludq xmm3, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+172]",
        "    pmuludq xmm4, xmm5",
        "    paddq xmm0, xmm1",
        "    paddq xmm0, xmm2",
        "    paddq xmm0, xmm3",
        "    paddq xmm0, xmm4",
        "    movdqu xmm6, XMMWORD PTR [ebx+428]",
        "    movdqu xmm3, XMMWORD PTR [ebx+124]",
        "    pmuludq xmm3, xmm6",
        "    movdqu xmm1, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm1, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+444]",
        "    movdqu xmm5, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm5, xmm7",
        "    paddq xmm3, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm6, xmm7",
        "    paddq xmm1, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+460]",
        "    movdqu xmm2, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm2, xmm7",
        "    paddq xmm3, xmm2",
        "    movdqu xmm4, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm4, xmm7",
        "    paddq xmm1, xmm4",
        "    movdqu xmm7, XMMWORD PTR [ebx+476]",
        "    movdqu xmm5, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm5, xmm7",
        "    paddq xmm3, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm6, xmm7",
        "    paddq xmm1, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+492]",
        "    movdqu xmm2, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm2, xmm7",
        "    paddq xmm3, xmm2",
        "    movdqu xmm4, XMMWORD PTR [ebx+188]",
        "    pmuludq xmm4, xmm7",
        "    paddq xmm1, xmm4",
        "    movdqu xmm7, XMMWORD PTR [ebx+428]",
        "    movdqu xmm4, XMMWORD PTR [ebx+140]",
        "    pmuludq xmm4, xmm7",
        "    movdqu xmm2, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm2, xmm7",
        "    movdqu xmm7, XMMWORD PTR [ebx+444]",
        "    movdqu xmm5, XMMWORD PTR [ebx+124]",
        "    pmuludq xmm5, xmm7",
        "    paddq xmm4, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm6, xmm7",
        "    paddq xmm2, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+460]",
        "    movdqu xmm5, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm5, xmm7",
        "    paddq xmm4, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm6, xmm7",
        "    paddq xmm2, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+476]",
        "    movdqu xmm5, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm5, xmm7",
        "    paddq xmm4, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm6, xmm7",
        "    paddq xmm2, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+492]",
        "    movdqu xmm5, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm5, xmm7",
        "    paddq xmm4, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm6, xmm7",
        "    paddq xmm2, xmm6",
        "    movdqa xmm7, xmm0",
        "    psrlq xmm7, 26",
        "    psllq xmm0, 38",
        "    psrlq xmm0, 38",
        "    paddq xmm1, xmm7",
        "    movdqa xmm7, xmm3",
        "    psrlq xmm7, 26",
        "    psllq xmm3, 38",
        "    psrlq xmm3, 38",
        "    paddq xmm4, xmm7",
        "    movdqa xmm7, xmm1",
        "    psrlq xmm7, 26",
        "    psllq xmm1, 38",
        "    psrlq xmm1, 38",
        "    paddq xmm2, xmm7",
        "    movdqa xmm7, xmm4",
        "    psrlq xmm7, 26",
        "    psllq xmm4, 38",
        "    psrlq xmm4, 38",
        "    movdqa xmm5, xmm7",
        "    psllq xmm5, 2",
        "    paddq xmm7, xmm5",
        "    paddq xmm0, xmm7",
        "    movdqa xmm6, xmm2",
        "    psrlq xmm6, 26",
        "    psllq xmm2, 38",
        "    psrlq xmm2, 38",
        "    paddq xmm3, xmm6",
        "    movdqa xmm6, xmm0",
        "    psrlq xmm6, 26",
        "    psllq xmm0, 38",
        "    psrlq xmm0, 38",
        "    paddq xmm1, xmm6",
        "    movdqa xmm5, xmm3",
        "    psrlq xmm5, 26",
        "    psllq xmm3, 38",
        "    psrlq xmm3, 38",
        "    paddq xmm4, xmm5",
        "    movq xmm7, QWORD PTR [esi+0]",
        "    movq xmm5, QWORD PTR [esi+16]",
        "    punpcklqdq xmm7, xmm5",
        "    psllq xmm7, 38",
        "    psrlq xmm7, 38",
        "    paddq xmm0, xmm7",
        "    movq xmm6, QWORD PTR [esi+0]",
        "    movq xmm5, QWORD PTR [esi+16]",
        "    punpcklqdq xmm6, xmm5",
        "    psllq xmm6, 12",
        "    psrlq xmm6, 38",
        "    paddq xmm1, xmm6",
        "    movq xmm5, QWORD PTR [esi+6]",
        "    movq xmm7, QWORD PTR [esi+22]",
        "    punpcklqdq xmm5, xmm7",
        "    psllq xmm5, 34",
        "    psrlq xmm5, 38",
        "    paddq xmm2, xmm5",
        "    movq xmm6, QWORD PTR [esi+8]",
        "    movq xmm7, QWORD PTR [esi+24]",
        "    punpcklqdq xmm6, xmm7",
        "    psllq xmm6, 24",
        "    psrlq xmm6, 38",
        "    paddq xmm3, xmm6",
        "    movq xmm7, QWORD PTR [esi+8]",
        "    movq xmm5, QWORD PTR [esi+24]",
        "    punpcklqdq xmm7, xmm5",
        "    psrlq xmm7, 40",
        "    paddq xmm4, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+412]",
        "    paddq xmm4, xmm5",
        "    movdqu XMMWORD PTR [ebx+428], xmm0",
        "    movdqu XMMWORD PTR [ebx+444], xmm1",
        "    movdqu XMMWORD PTR [ebx+460], xmm2",
        "    movdqu XMMWORD PTR [ebx+476], xmm3",
        "    movdqu XMMWORD PTR [ebx+492], xmm4",
        "    add esi, 32",
        "    sub ecx, 1",
        "    jne 2b",
        "    pop esi",
        "    pop ebx",
        "    ret",
        ".size vgx_cand_fd_g22, .-vgx_cand_fd_g22",
        ".globl vgx_cand_fdm_g22",
        ".type vgx_cand_fdm_g22, @function",
        ".p2align 6",
        "vgx_cand_fdm_g22:",
        "    push ebx",
        "    push esi",
        "    mov ebx, DWORD PTR [esp+12]",
        "    mov esi, DWORD PTR [esp+16]",
        "    mov ecx, DWORD PTR [esp+20]",
        "    movdqu xmm0, XMMWORD PTR [ebx+428]",
        "    movdqu xmm1, XMMWORD PTR [ebx+444]",
        "    movdqu xmm2, XMMWORD PTR [ebx+460]",
        "    movdqu xmm3, XMMWORD PTR [ebx+476]",
        "    movdqu xmm4, XMMWORD PTR [ebx+492]",
        "    .p2align 4",
        "2:",
        "    movdqu xmm6, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm0, xmm6",
        "    movdqu xmm5, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm1, xmm5",
        "    movdqu xmm7, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm2, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+188]",
        "    pmuludq xmm3, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+172]",
        "    pmuludq xmm4, xmm6",
        "    paddq xmm0, xmm1",
        "    paddq xmm0, xmm2",
        "    paddq xmm0, xmm3",
        "    paddq xmm0, xmm4",
        "    movq xmm7, QWORD PTR [esi+0]",
        "    movq xmm5, QWORD PTR [esi+16]",
        "    punpcklqdq xmm7, xmm5",
        "    psllq xmm7, 38",
        "    psrlq xmm7, 38",
        "    paddq xmm0, xmm7",
        "    movdqu xmm6, XMMWORD PTR [ebx+428]",
        "    movdqu xmm3, XMMWORD PTR [ebx+124]",
        "    pmuludq xmm3, xmm6",
        "    movdqu xmm1, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm1, xmm6",
        "    movq xmm2, QWORD PTR [esi+8]",
        "    movq xmm5, QWORD PTR [esi+24]",
        "    punpcklqdq xmm2, xmm5",
        "    psllq xmm2, 24",
        "    psrlq xmm2, 38",
        "    paddq xmm3, xmm2",
        "    movq xmm4, QWORD PTR [esi+0]",
        "    movq xmm6, QWORD PTR [esi+16]",
        "    punpcklqdq xmm4, xmm6",
        "    psllq xmm4, 12",
        "    psrlq xmm4, 38",
        "    paddq xmm1, xmm4",
        "    movdqu xmm5, XMMWORD PTR [ebx+444]",
        "    movdqu xmm6, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm6, xmm5",
        "    paddq xmm3, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm7, xmm5",
        "    paddq xmm1, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+460]",
        "    movdqu xmm2, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm2, xmm5",
        "    paddq xmm3, xmm2",
        "    movdqu xmm4, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm4, xmm5",
        "    paddq xmm1, xmm4",
        "    movdqu xmm5, XMMWORD PTR [ebx+476]",
        "    movdqu xmm6, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm6, xmm5",
        "    paddq xmm3, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm7, xmm5",
        "    paddq xmm1, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+492]",
        "    movdqu xmm2, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm2, xmm5",
        "    paddq xmm3, xmm2",
        "    movdqu xmm4, XMMWORD PTR [ebx+188]",
        "    pmuludq xmm4, xmm5",
        "    paddq xmm1, xmm4",
        "    movdqu xmm5, XMMWORD PTR [ebx+428]",
        "    movdqu xmm4, XMMWORD PTR [ebx+140]",
        "    pmuludq xmm4, xmm5",
        "    movdqu xmm2, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm2, xmm5",
        "    movq xmm5, QWORD PTR [esi+8]",
        "    movq xmm6, QWORD PTR [esi+24]",
        "    punpcklqdq xmm5, xmm6",
        "    psrlq xmm5, 40",
        "    paddq xmm4, xmm5",
        "    movdqu xmm7, XMMWORD PTR [ebx+412]",
        "    paddq xmm4, xmm7",
        "    movq xmm6, QWORD PTR [esi+6]",
        "    movq xmm7, QWORD PTR [esi+22]",
        "    punpcklqdq xmm6, xmm7",
        "    psllq xmm6, 34",
        "    psrlq xmm6, 38",
        "    paddq xmm2, xmm6",
        "    movdqu xmm5, XMMWORD PTR [ebx+444]",
        "    movdqu xmm7, XMMWORD PTR [ebx+124]",
        "    pmuludq xmm7, xmm5",
        "    paddq xmm4, xmm7",
        "    movdqu xmm6, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm6, xmm5",
        "    paddq xmm2, xmm6",
        "    movdqu xmm5, XMMWORD PTR [ebx+460]",
        "    movdqu xmm7, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm7, xmm5",
        "    paddq xmm4, xmm7",
        "    movdqu xmm6, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm6, xmm5",
        "    paddq xmm2, xmm6",
        "    movdqu xmm5, XMMWORD PTR [ebx+476]",
        "    movdqu xmm7, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm7, xmm5",
        "    paddq xmm4, xmm7",
        "    movdqu xmm6, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm6, xmm5",
        "    paddq xmm2, xmm6",
        "    movdqu xmm5, XMMWORD PTR [ebx+492]",
        "    movdqu xmm7, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm7, xmm5",
        "    paddq xmm4, xmm7",
        "    movdqu xmm6, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm6, xmm5",
        "    paddq xmm2, xmm6",
        "    movdqa xmm5, xmm0",
        "    psrlq xmm5, 26",
        "    psllq xmm0, 38",
        "    psrlq xmm0, 38",
        "    paddq xmm1, xmm5",
        "    movdqa xmm5, xmm3",
        "    psrlq xmm5, 26",
        "    psllq xmm3, 38",
        "    psrlq xmm3, 38",
        "    paddq xmm4, xmm5",
        "    movdqa xmm5, xmm1",
        "    psrlq xmm5, 26",
        "    psllq xmm1, 38",
        "    psrlq xmm1, 38",
        "    paddq xmm2, xmm5",
        "    movdqa xmm5, xmm4",
        "    psrlq xmm5, 26",
        "    psllq xmm4, 38",
        "    psrlq xmm4, 38",
        "    movdqa xmm7, xmm5",
        "    psllq xmm7, 2",
        "    paddq xmm5, xmm7",
        "    paddq xmm0, xmm5",
        "    movdqa xmm6, xmm2",
        "    psrlq xmm6, 26",
        "    psllq xmm2, 38",
        "    psrlq xmm2, 38",
        "    paddq xmm3, xmm6",
        "    movdqa xmm7, xmm0",
        "    psrlq xmm7, 26",
        "    psllq xmm0, 38",
        "    psrlq xmm0, 38",
        "    paddq xmm1, xmm7",
        "    movdqa xmm5, xmm3",
        "    psrlq xmm5, 26",
        "    psllq xmm3, 38",
        "    psrlq xmm3, 38",
        "    paddq xmm4, xmm5",
        "    movdqu XMMWORD PTR [ebx+428], xmm0",
        "    movdqu XMMWORD PTR [ebx+444], xmm1",
        "    movdqu XMMWORD PTR [ebx+460], xmm2",
        "    movdqu XMMWORD PTR [ebx+476], xmm3",
        "    movdqu XMMWORD PTR [ebx+492], xmm4",
        "    add esi, 32",
        "    sub ecx, 1",
        "    jne 2b",
        "    pop esi",
        "    pop ebx",
        "    ret",
        ".size vgx_cand_fdm_g22, .-vgx_cand_fdm_g22",
        ".globl vgx_cand_fdm_g31",
        ".type vgx_cand_fdm_g31, @function",
        ".p2align 6",
        "vgx_cand_fdm_g31:",
        "    push ebx",
        "    push esi",
        "    mov ebx, DWORD PTR [esp+12]",
        "    mov esi, DWORD PTR [esp+16]",
        "    mov ecx, DWORD PTR [esp+20]",
        "    movdqu xmm0, XMMWORD PTR [ebx+428]",
        "    movdqu xmm1, XMMWORD PTR [ebx+444]",
        "    movdqu xmm2, XMMWORD PTR [ebx+460]",
        "    movdqu xmm3, XMMWORD PTR [ebx+476]",
        "    movdqu xmm4, XMMWORD PTR [ebx+492]",
        "    .p2align 4",
        "2:",
        "    movdqu xmm5, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm0, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm1, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm2, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+188]",
        "    pmuludq xmm3, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+172]",
        "    pmuludq xmm4, xmm6",
        "    paddq xmm0, xmm1",
        "    paddq xmm0, xmm2",
        "    paddq xmm0, xmm3",
        "    paddq xmm0, xmm4",
        "    movq xmm7, QWORD PTR [esi+0]",
        "    movq xmm5, QWORD PTR [esi+16]",
        "    punpcklqdq xmm7, xmm5",
        "    psllq xmm7, 38",
        "    psrlq xmm7, 38",
        "    paddq xmm0, xmm7",
        "    movdqu xmm6, XMMWORD PTR [ebx+428]",
        "    movdqu xmm3, XMMWORD PTR [ebx+124]",
        "    pmuludq xmm3, xmm6",
        "    movdqu xmm1, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm1, xmm6",
        "    movdqu xmm4, XMMWORD PTR [ebx+140]",
        "    pmuludq xmm4, xmm6",
        "    movq xmm2, QWORD PTR [esi+8]",
        "    movq xmm5, QWORD PTR [esi+24]",
        "    punpcklqdq xmm2, xmm5",
        "    psllq xmm2, 24",
        "    psrlq xmm2, 38",
        "    paddq xmm3, xmm2",
        "    movq xmm6, QWORD PTR [esi+0]",
        "    movq xmm5, QWORD PTR [esi+16]",
        "    punpcklqdq xmm6, xmm5",
        "    psllq xmm6, 12",
        "    psrlq xmm6, 38",
        "    paddq xmm1, xmm6",
        "    movq xmm7, QWORD PTR [esi+8]",
        "    movq xmm5, QWORD PTR [esi+24]",
        "    punpcklqdq xmm7, xmm5",
        "    psrlq xmm7, 40",
        "    paddq xmm4, xmm7",
        "    movdqu xmm2, XMMWORD PTR [ebx+412]",
        "    paddq xmm4, xmm2",
        "    movdqu xmm5, XMMWORD PTR [ebx+444]",
        "    movdqu xmm2, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm2, xmm5",
        "    paddq xmm3, xmm2",
        "    movdqu xmm6, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm6, xmm5",
        "    paddq xmm1, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+124]",
        "    pmuludq xmm7, xmm5",
        "    paddq xmm4, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+460]",
        "    movdqu xmm2, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm2, xmm5",
        "    paddq xmm3, xmm2",
        "    movdqu xmm6, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm6, xmm5",
        "    paddq xmm1, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm7, xmm5",
        "    paddq xmm4, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+476]",
        "    movdqu xmm2, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm2, xmm5",
        "    paddq xmm3, xmm2",
        "    movdqu xmm6, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm6, xmm5",
        "    paddq xmm1, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm7, xmm5",
        "    paddq xmm4, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+492]",
        "    movdqu xmm2, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm2, xmm5",
        "    paddq xmm3, xmm2",
        "    movdqu xmm6, XMMWORD PTR [ebx+188]",
        "    pmuludq xmm6, xmm5",
        "    paddq xmm1, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm7, xmm5",
        "    paddq xmm4, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+428]",
        "    movdqu xmm2, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm2, xmm5",
        "    movq xmm5, QWORD PTR [esi+6]",
        "    movq xmm6, QWORD PTR [esi+22]",
        "    punpcklqdq xmm5, xmm6",
        "    psllq xmm5, 34",
        "    psrlq xmm5, 38",
        "    paddq xmm2, xmm5",
        "    movdqu xmm7, XMMWORD PTR [ebx+444]",
        "    movdqu xmm6, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm6, xmm7",
        "    paddq xmm2, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+460]",
        "    movdqu xmm5, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm5, xmm7",
        "    paddq xmm2, xmm5",
        "    movdqu xmm7, XMMWORD PTR [ebx+476]",
        "    movdqu xmm6, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm6, xmm7",
        "    paddq xmm2, xmm6",
        "    movdqu xmm7, XMMWORD PTR [ebx+492]",
        "    movdqu xmm5, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm5, xmm7",
        "    paddq xmm2, xmm5",
        "    movdqa xmm7, xmm0",
        "    psrlq xmm7, 26",
        "    psllq xmm0, 38",
        "    psrlq xmm0, 38",
        "    paddq xmm1, xmm7",
        "    movdqa xmm7, xmm3",
        "    psrlq xmm7, 26",
        "    psllq xmm3, 38",
        "    psrlq xmm3, 38",
        "    paddq xmm4, xmm7",
        "    movdqa xmm6, xmm1",
        "    psrlq xmm6, 26",
        "    psllq xmm1, 38",
        "    psrlq xmm1, 38",
        "    paddq xmm2, xmm6",
        "    movdqa xmm7, xmm4",
        "    psrlq xmm7, 26",
        "    psllq xmm4, 38",
        "    psrlq xmm4, 38",
        "    movdqa xmm6, xmm7",
        "    psllq xmm6, 2",
        "    paddq xmm7, xmm6",
        "    paddq xmm0, xmm7",
        "    movdqa xmm5, xmm2",
        "    psrlq xmm5, 26",
        "    psllq xmm2, 38",
        "    psrlq xmm2, 38",
        "    paddq xmm3, xmm5",
        "    movdqa xmm6, xmm0",
        "    psrlq xmm6, 26",
        "    psllq xmm0, 38",
        "    psrlq xmm0, 38",
        "    paddq xmm1, xmm6",
        "    movdqa xmm7, xmm3",
        "    psrlq xmm7, 26",
        "    psllq xmm3, 38",
        "    psrlq xmm3, 38",
        "    paddq xmm4, xmm7",
        "    movdqu XMMWORD PTR [ebx+428], xmm0",
        "    movdqu XMMWORD PTR [ebx+444], xmm1",
        "    movdqu XMMWORD PTR [ebx+460], xmm2",
        "    movdqu XMMWORD PTR [ebx+476], xmm3",
        "    movdqu XMMWORD PTR [ebx+492], xmm4",
        "    add esi, 32",
        "    sub ecx, 1",
        "    jne 2b",
        "    pop esi",
        "    pop ebx",
        "    ret",
        ".size vgx_cand_fdm_g31, .-vgx_cand_fdm_g31",
        ".globl vgx_cand_fdm_g211",
        ".type vgx_cand_fdm_g211, @function",
        ".p2align 6",
        "vgx_cand_fdm_g211:",
        "    push ebx",
        "    push esi",
        "    mov ebx, DWORD PTR [esp+12]",
        "    mov esi, DWORD PTR [esp+16]",
        "    mov ecx, DWORD PTR [esp+20]",
        "    movdqu xmm0, XMMWORD PTR [ebx+428]",
        "    movdqu xmm1, XMMWORD PTR [ebx+444]",
        "    movdqu xmm2, XMMWORD PTR [ebx+460]",
        "    movdqu xmm3, XMMWORD PTR [ebx+476]",
        "    movdqu xmm4, XMMWORD PTR [ebx+492]",
        "    .p2align 4",
        "2:",
        "    movdqu xmm7, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm0, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm1, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm2, xmm6",
        "    movdqu xmm5, XMMWORD PTR [ebx+188]",
        "    pmuludq xmm3, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+172]",
        "    pmuludq xmm4, xmm6",
        "    paddq xmm0, xmm1",
        "    paddq xmm0, xmm2",
        "    paddq xmm0, xmm3",
        "    paddq xmm0, xmm4",
        "    movq xmm7, QWORD PTR [esi+0]",
        "    movq xmm5, QWORD PTR [esi+16]",
        "    punpcklqdq xmm7, xmm5",
        "    psllq xmm7, 38",
        "    psrlq xmm7, 38",
        "    paddq xmm0, xmm7",
        "    movdqu xmm6, XMMWORD PTR [ebx+428]",
        "    movdqu xmm3, XMMWORD PTR [ebx+124]",
        "    pmuludq xmm3, xmm6",
        "    movdqu xmm1, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm1, xmm6",
        "    movq xmm2, QWORD PTR [esi+8]",
        "    movq xmm5, QWORD PTR [esi+24]",
        "    punpcklqdq xmm2, xmm5",
        "    psllq xmm2, 24",
        "    psrlq xmm2, 38",
        "    paddq xmm3, xmm2",
        "    movq xmm4, QWORD PTR [esi+0]",
        "    movq xmm5, QWORD PTR [esi+16]",
        "    punpcklqdq xmm4, xmm5",
        "    psllq xmm4, 12",
        "    psrlq xmm4, 38",
        "    paddq xmm1, xmm4",
        "    movdqu xmm6, XMMWORD PTR [ebx+444]",
        "    movdqu xmm7, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm7, xmm6",
        "    paddq xmm3, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm5, xmm6",
        "    paddq xmm1, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+460]",
        "    movdqu xmm2, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm2, xmm6",
        "    paddq xmm3, xmm2",
        "    movdqu xmm4, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm4, xmm6",
        "    paddq xmm1, xmm4",
        "    movdqu xmm6, XMMWORD PTR [ebx+476]",
        "    movdqu xmm7, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm7, xmm6",
        "    paddq xmm3, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm5, xmm6",
        "    paddq xmm1, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+492]",
        "    movdqu xmm2, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm2, xmm6",
        "    paddq xmm3, xmm2",
        "    movdqu xmm4, XMMWORD PTR [ebx+188]",
        "    pmuludq xmm4, xmm6",
        "    paddq xmm1, xmm4",
        "    movdqu xmm6, XMMWORD PTR [ebx+428]",
        "    movdqu xmm4, XMMWORD PTR [ebx+140]",
        "    pmuludq xmm4, xmm6",
        "    movq xmm6, QWORD PTR [esi+8]",
        "    movq xmm7, QWORD PTR [esi+24]",
        "    punpcklqdq xmm6, xmm7",
        "    psrlq xmm6, 40",
        "    paddq xmm4, xmm6",
        "    movdqu xmm5, XMMWORD PTR [ebx+412]",
        "    paddq xmm4, xmm5",
        "    movdqu xmm2, XMMWORD PTR [ebx+444]",
        "    movdqu xmm7, XMMWORD PTR [ebx+124]",
        "    pmuludq xmm7, xmm2",
        "    paddq xmm4, xmm7",
        "    movdqu xmm5, XMMWORD PTR [ebx+460]",
        "    movdqu xmm2, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm2, xmm5",
        "    paddq xmm4, xmm2",
        "    movdqu xmm6, XMMWORD PTR [ebx+476]",
        "    movdqu xmm5, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm5, xmm6",
        "    paddq xmm4, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+492]",
        "    movdqu xmm7, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm7, xmm6",
        "    paddq xmm4, xmm7",
        "    movdqu xmm6, XMMWORD PTR [ebx+428]",
        "    movdqu xmm2, XMMWORD PTR [ebx+108]",
        "    pmuludq xmm2, xmm6",
        "    movq xmm5, QWORD PTR [esi+6]",
        "    movq xmm6, QWORD PTR [esi+22]",
        "    punpcklqdq xmm5, xmm6",
        "    psllq xmm5, 34",
        "    psrlq xmm5, 38",
        "    paddq xmm2, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+444]",
        "    movdqu xmm7, XMMWORD PTR [ebx+92]",
        "    pmuludq xmm7, xmm6",
        "    paddq xmm2, xmm7",
        "    movdqu xmm6, XMMWORD PTR [ebx+460]",
        "    movdqu xmm5, XMMWORD PTR [ebx+76]",
        "    pmuludq xmm5, xmm6",
        "    paddq xmm2, xmm5",
        "    movdqu xmm6, XMMWORD PTR [ebx+476]",
        "    movdqu xmm7, XMMWORD PTR [ebx+220]",
        "    pmuludq xmm7, xmm6",
        "    paddq xmm2, xmm7",
        "    movdqu xmm6, XMMWORD PTR [ebx+492]",
        "    movdqu xmm5, XMMWORD PTR [ebx+204]",
        "    pmuludq xmm5, xmm6",
        "    paddq xmm2, xmm5",
        "    movdqa xmm6, xmm0",
        "    psrlq xmm6, 26",
        "    psllq xmm0, 38",
        "    psrlq xmm0, 38",
        "    paddq xmm1, xmm6",
        "    movdqa xmm6, xmm3",
        "    psrlq xmm6, 26",
        "    psllq xmm3, 38",
        "    psrlq xmm3, 38",
        "    paddq xmm4, xmm6",
        "    movdqa xmm7, xmm1",
        "    psrlq xmm7, 26",
        "    psllq xmm1, 38",
        "    psrlq xmm1, 38",
        "    paddq xmm2, xmm7",
        "    movdqa xmm6, xmm4",
        "    psrlq xmm6, 26",
        "    psllq xmm4, 38",
        "    psrlq xmm4, 38",
        "    movdqa xmm7, xmm6",
        "    psllq xmm7, 2",
        "    paddq xmm6, xmm7",
        "    paddq xmm0, xmm6",
        "    movdqa xmm5, xmm2",
        "    psrlq xmm5, 26",
        "    psllq xmm2, 38",
        "    psrlq xmm2, 38",
        "    paddq xmm3, xmm5",
        "    movdqa xmm7, xmm0",
        "    psrlq xmm7, 26",
        "    psllq xmm0, 38",
        "    psrlq xmm0, 38",
        "    paddq xmm1, xmm7",
        "    movdqa xmm5, xmm3",
        "    psrlq xmm5, 26",
        "    psllq xmm3, 38",
        "    psrlq xmm3, 38",
        "    paddq xmm4, xmm5",
        "    movdqu XMMWORD PTR [ebx+428], xmm0",
        "    movdqu XMMWORD PTR [ebx+444], xmm1",
        "    movdqu XMMWORD PTR [ebx+460], xmm2",
        "    movdqu XMMWORD PTR [ebx+476], xmm3",
        "    movdqu XMMWORD PTR [ebx+492], xmm4",
        "    add esi, 32",
        "    sub ecx, 1",
        "    jne 2b",
        "    pop esi",
        "    pop ebx",
        "    ret",
        ".size vgx_cand_fdm_g211, .-vgx_cand_fdm_g211",
    );

    type Cand = unsafe extern "C" fn(*mut u8, *const u8, u32);
    unsafe extern "C" {
        fn vgx_cand_stage1(frame: *mut u8, data: *const u8, pairs: u32);
        fn vgx_cand_alt2(frame: *mut u8, data: *const u8, pairs: u32);
        fn vgx_cand_rot3d(frame: *mut u8, data: *const u8, pairs: u32);
        fn vgx_cand_rot3m(frame: *mut u8, data: *const u8, pairs: u32);
        fn vgx_cand_frame(frame: *mut u8, data: *const u8, pairs: u32);
        fn vgx_cand_frame_k2(frame: *mut u8, data: *const u8, pairs: u32);
        fn vgx_cand_fg_3_2(frame: *mut u8, data: *const u8, pairs: u32);
        fn vgx_cand_frame_d(frame: *mut u8, data: *const u8, pairs: u32);
        fn vgx_cand_fd_g22(frame: *mut u8, data: *const u8, pairs: u32);
        fn vgx_cand_fdm_g22(frame: *mut u8, data: *const u8, pairs: u32);
        fn vgx_cand_fdm_g31(frame: *mut u8, data: *const u8, pairs: u32);
        fn vgx_cand_fdm_g211(frame: *mut u8, data: *const u8, pairs: u32);
    }
    const CANDS: [(&str, Cand); 12] = [
        ("stage1", vgx_cand_stage1),
        ("alt2", vgx_cand_alt2),
        ("rot3d", vgx_cand_rot3d),
        ("rot3m", vgx_cand_rot3m),
        ("frame", vgx_cand_frame),
        ("frame_k2", vgx_cand_frame_k2),
        ("fg_3_2", vgx_cand_fg_3_2),
        ("frame_d", vgx_cand_frame_d),
        ("fd_g22", vgx_cand_fd_g22),
        ("fdm_g22", vgx_cand_fdm_g22),
        ("fdm_g31", vgx_cand_fdm_g31),
        ("fdm_g211", vgx_cand_fdm_g211),
    ];

    const PAIRS: usize = 512;
    static DATA: [u8; 32 * PAIRS] = [0x5a; 32 * PAIRS];

    #[repr(C, align(64))]
    struct Frame([u64; 128]);

    fn new_frame() -> Frame {
        // Every 64-bit lane below 2^26, as the limbs and the multipliers are.
        let mut f = Frame(core::array::from_fn(|i| (0x9e3779b9u64.wrapping_mul(i as u64 + 1) >> 7) & 0x3ff_ffff));
        // `frame` is 4 bytes into the buffer, so that the slots are 16-byte
        // aligned as they are under the ABI's stack alignment: slot j is the
        // lanes 10 + 2 j and 11 + 2 j.
        (f.0[50], f.0[51]) = (0x3ff_ffff, 0x3ff_ffff);
        (f.0[52], f.0[53]) = (1 << 24, 1 << 24);
        f
    }

    /// The AVX state in use, with the upper halves zero.
    fn dirty() -> bool {
        if !std::is_x86_feature_detected!("avx2") {
            return false;
        }
        // SAFETY: AVX2 is available.
        unsafe {
            asm!("vpcmpeqd ymm0, ymm0, ymm0", "vzeroupper",
                out("xmm0") _, out("xmm1") _, out("xmm2") _, out("xmm3") _,
                out("xmm4") _, out("xmm5") _, out("xmm6") _, out("xmm7") _,
                options(nostack, nomem));
        }
        true
    }

    /// The AVX state in use, with the upper halves of ymm0-ymm7 not zero.
    fn dirty_nz() -> bool {
        if !std::is_x86_feature_detected!("avx2") {
            return false;
        }
        // SAFETY: AVX2 is available.
        unsafe {
            asm!("vpcmpeqd ymm0, ymm0, ymm0", "vpcmpeqd ymm1, ymm1, ymm1",
                "vpcmpeqd ymm2, ymm2, ymm2", "vpcmpeqd ymm3, ymm3, ymm3",
                "vpcmpeqd ymm4, ymm4, ymm4", "vpcmpeqd ymm5, ymm5, ymm5",
                "vpcmpeqd ymm6, ymm6, ymm6", "vpcmpeqd ymm7, ymm7, ymm7",
                out("xmm0") _, out("xmm1") _, out("xmm2") _, out("xmm3") _,
                out("xmm4") _, out("xmm5") _, out("xmm6") _, out("xmm7") _,
                options(nostack, nomem));
        }
        true
    }

    /// The fastest and the median of 41 timings of `f`, in nanoseconds.
    fn time(mut f: impl FnMut()) -> (u32, u32) {
        let mut t = [0u32; 41];
        for t in &mut t {
            let start = Instant::now();
            f();
            *t = start.elapsed().as_nanos() as u32;
        }
        t.sort_unstable();
        (t[0], t[20])
    }

    /// One line a candidate and mode: XGETBV(1) before and after, the
    /// fastest and the median time of 512 pairs (16 KiB), and the median in
    /// picoseconds a pair. `lib-pairs` is the library's `update` of 16 KiB
    /// at once (the pairs, with `new` and `finalize`), `lib-scalar` the same
    /// data 240 bytes at a time (a block at a time).
    pub fn candidates(key: &[u8; 32], round: u32) {
        let line = |mode: &str, name: &str, before: u32, (min, med): (u32, u32)| {
            eprintln!(
                "xcand {round} {mode} {name:<12} xinuse {before:#x}->{:#x} min {min:>6} median {med:>6} ns, {:>6} ps/pair",
                xinuse(), u64::from(med) * 1000 / PAIRS as u64
            );
        };
        for mode in ["fast", "slow", "nonzero"] {
            let set = || {
                if mode == "fast" {
                    std::thread::sleep(std::time::Duration::from_millis(3));
                    true
                } else if mode == "slow" {
                    dirty()
                } else {
                    dirty_nz()
                }
            };
            for (name, f) in CANDS {
                let mut frame = new_frame();
                // SAFETY: the 524 bytes at `p` are within `frame`.
                let p = unsafe { frame.0.as_mut_ptr().cast::<u8>().add(4) };
                if !set() {
                    continue;
                }
                let before = xinuse();
                // SAFETY: the candidates read and write the 524 bytes of the
                // frame, read 32 bytes of data a pair, and follow cdecl.
                let t = time(|| unsafe { f(black_box(p), black_box(DATA.as_ptr()), PAIRS as u32) });
                line(mode, name, before, t);
            }
            // The slots' alignment: the new loop with the frame 8 and 4
            // bytes further (slots at 8 and at 4 modulo 16, as
            // `vg_poly1305_blocks` has them when ChaCha20-Poly1305's seal
            // and open, and its gathered seal, call it), next to
            // `fdm_g22` above (slots at 0 modulo 16, as `update` and
            // `open_to` have them). One slot in four then straddles a
            // cache line.
            for (name, off) in [("fdm_g22+8", 8), ("fdm_g22+4", 4)] {
                let mut frame = new_frame();
                // SAFETY: the 524 bytes at `p` are within `frame`.
                let p = unsafe { frame.0.as_mut_ptr().cast::<u8>().add(4 + off) };
                if !set() {
                    continue;
                }
                let before = xinuse();
                // SAFETY: as above.
                let t = time(|| unsafe { vgx_cand_fdm_g22(black_box(p), black_box(DATA.as_ptr()), PAIRS as u32) });
                line(mode, name, before, t);
            }
            if set() {
                let before = xinuse();
                let t = time(|| {
                    black_box(Poly1305::mac(black_box(key), black_box(&DATA)));
                });
                line(mode, "lib-pairs", before, t);
            }
            if set() {
                let before = xinuse();
                let t = time(|| {
                    let mut p = Poly1305::new(black_box(key));
                    for c in black_box(&DATA).chunks(240) {
                        p.update(c);
                    }
                    black_box(p.finalize());
                });
                line(mode, "lib-scalar", before, t);
            }
            // The threshold: the library's MAC of the whole buffer (the
            // pairs of blocks from 256 bytes on) against the same bytes
            // fed 240 at a time (a block at a time), per size and mode.
            // One line each: `xsize <round> <mode> <name> <bytes> xinuse
            // <before>-><after> min <ns> median <ns> ns` (a call, from 41
            // timings of 64 calls each below 4 KiB, of one call from there).
            for size in [256usize, 480, 1024, 16384] {
                let calls = if size < 4096 { 64 } else { 1 };
                let report = |name: &str, before: u32, (min, med): (u32, u32)| {
                    eprintln!(
                        "xsize {round} {mode} {name:<10} {size:>5} xinuse {before:#x}->{:#x} min {:>8.1} median {:>8.1} ns",
                        xinuse(), f64::from(min) / f64::from(calls), f64::from(med) / f64::from(calls)
                    );
                };
                if set() {
                    let before = xinuse();
                    let t = time(|| {
                        for _ in 0..calls {
                            black_box(Poly1305::mac(black_box(key), black_box(&DATA[..size])));
                        }
                    });
                    report("lib-pairs", before, t);
                }
                if set() {
                    let before = xinuse();
                    let t = time(|| {
                        for _ in 0..calls {
                            let mut p = Poly1305::new(black_box(key));
                            for c in black_box(&DATA[..size]).chunks(240) {
                                p.update(c);
                            }
                            black_box(p.finalize());
                        }
                    });
                    report("lib-scalar", before, t);
                }
            }
        }
        super::xprobe::vzeroupper();
    }
}
// XCAND END

// XMODES BEGIN
/// MEASURING PROTOTYPE, NOT FOR MERGING: which x86 functions that use xmm
/// registers are slower once the AVX state is in use? One library call for
/// each family of them (`scratchpad/poly/zen4/xsurvey.py` lists them from the
/// generated assembly), at a size where its loop is most of the time, timed
/// in three states of the processor:
///
/// * `fast`: the AVX state not in use (XGETBV(1) = 0x3: after `vzeroupper`
///   and a sleep, whose context switch restores the initial state);
/// * `slow`: in use with the upper halves zero (after `vpcmpeqd ymm0` and
///   `vzeroupper`, again before every timing);
/// * `nonzero`: in use with the upper halves of ymm0-ymm7 not zero (set
///   again before every timing).
///
/// One line each: `xmodes <round> <mode> <name> <bytes> xinuse
/// <before>-><after> min <ns> median <ns> ns x<timings>*<calls>`, the
/// nanoseconds of one call. The library chooses its implementations as
/// always, so `VG_CPU_FEATURES` chooses what is measured.
#[cfg(target_arch = "x86")]
mod xmodes {
    use std::arch::asm;
    use std::hint::black_box;
    use std::time::{Duration, Instant};

    use openssl::rsa::Rsa;
    use verified_garbage::aead::aes_gcm::AesGcm;
    use verified_garbage::aead::aes_gcm_siv::AesGcmSiv;
    use verified_garbage::aead::chacha20poly1305::ChaCha20Poly1305;
    use verified_garbage::cipher::aes::{AesCbcDecryptor, AesCtr, AesEcb, AesXts};
    use verified_garbage::cipher::cast5::Cast5CbcEncryptor;
    use verified_garbage::cipher::chacha20::ChaCha20;
    use verified_garbage::cipher::rc2::Rc2CbcEncryptor;
    use verified_garbage::cmac::aes::AesCmac;
    use verified_garbage::ec::{P256, PrivateKey as EcPrivateKey, PublicKey as EcPublicKey};
    use verified_garbage::hashes::blake2s::Blake2s256;
    use verified_garbage::hashes::sha1::Sha1;
    use verified_garbage::hashes::sha256::Sha256;
    use verified_garbage::hashes::sha512::Sha512;
    use verified_garbage::kdf::scrypt;
    use verified_garbage::poly1305::Poly1305;
    use verified_garbage::rsa::pkcs1_sig::Hash;
    use verified_garbage::rsa::{BigUint, PrivateKey as RsaPrivateKey};

    use super::xprobe::{vzeroupper, xinuse};

    const MODES: [&str; 3] = ["fast", "slow", "nonzero"];

    /// The nanoseconds of timings an item gets in each mode (5 timings at
    /// least, 31 at most).
    const BUDGET: u64 = 6_000_000;

    /// Puts the processor in mode `m` of `MODES`, but for the sleep `fast`
    /// needs; false where it has no AVX2 to do so.
    fn set(m: usize) -> bool {
        if m == 0 {
            vzeroupper();
            return true;
        }
        if !std::is_x86_feature_detected!("avx2") {
            return false;
        }
        // SAFETY: AVX2 is available.
        unsafe {
            if m == 1 {
                asm!("vpcmpeqd ymm0, ymm0, ymm0", "vzeroupper",
                    out("xmm0") _, out("xmm1") _, out("xmm2") _, out("xmm3") _,
                    out("xmm4") _, out("xmm5") _, out("xmm6") _, out("xmm7") _,
                    options(nostack, nomem));
            } else {
                asm!("vpcmpeqd ymm0, ymm0, ymm0", "vpcmpeqd ymm1, ymm1, ymm1",
                    "vpcmpeqd ymm2, ymm2, ymm2", "vpcmpeqd ymm3, ymm3, ymm3",
                    "vpcmpeqd ymm4, ymm4, ymm4", "vpcmpeqd ymm5, ymm5, ymm5",
                    "vpcmpeqd ymm6, ymm6, ymm6", "vpcmpeqd ymm7, ymm7, ymm7",
                    out("xmm0") _, out("xmm1") _, out("xmm2") _, out("xmm3") _,
                    out("xmm4") _, out("xmm5") _, out("xmm6") _, out("xmm7") _,
                    options(nostack, nomem));
            }
        }
        true
    }

    /// Times `f` in each mode: calls short of 20 microseconds in batches of
    /// up to 64, and as many timings as `BUDGET` allows.
    fn item(round: u32, name: &str, bytes: usize, f: &mut dyn FnMut()) {
        f();
        let start = Instant::now();
        f();
        let one = (start.elapsed().as_nanos() as u64).max(1);
        let calls = (20_000 / one).clamp(1, 64);
        let n = (BUDGET / (one * calls)).clamp(5, 31) as usize;
        let mut t = vec![0u64; n];
        for (m, mode) in MODES.iter().enumerate() {
            if !set(m) {
                continue;
            }
            if m == 0 {
                std::thread::sleep(Duration::from_millis(3));
            }
            let before = xinuse();
            for t in &mut t {
                // A context switch may have ended a mode with the AVX state
                // in use: set it again. (`fast` runs no AVX instruction.)
                if m != 0 {
                    set(m);
                }
                let start = Instant::now();
                for _ in 0..calls {
                    f();
                }
                *t = start.elapsed().as_nanos() as u64;
            }
            let after = xinuse();
            t.sort_unstable();
            eprintln!(
                "xmodes {round} {mode:<7} {name:<24} {bytes:>6} xinuse {before:#x}->{after:#x} min {:>12.1} median {:>12.1} ns x{n}*{calls}",
                t[0] as f64 / calls as f64,
                t[n / 2] as f64 / calls as f64
            );
        }
    }

    pub struct Setup {
        rsa: RsaPrivateKey,
    }

    impl Setup {
        /// The RSA key, once a launch; nothing where the benchmarks are only
        /// listed.
        pub fn new() -> Option<Self> {
            if std::env::args().any(|a| a == "--list") {
                return None;
            }
            let key = Rsa::generate(2048).unwrap();
            let rsa = RsaPrivateKey::from_crt(
                BigUint::from_be_bytes(&key.n().to_vec()),
                BigUint::from_be_bytes(&key.e().to_vec()),
                BigUint::from_be_bytes(&key.d().to_vec()),
                BigUint::from_be_bytes(&key.p().unwrap().to_vec()),
                BigUint::from_be_bytes(&key.q().unwrap().to_vec()),
                BigUint::from_be_bytes(&key.dmp1().unwrap().to_vec()),
                BigUint::from_be_bytes(&key.dmq1().unwrap().to_vec()),
                BigUint::from_be_bytes(&key.iqmp().unwrap().to_vec()),
            )
            .unwrap();
            Some(Self { rsa })
        }

        pub fn run(&self, round: u32) {
            const N: usize = 16384;
            let started = Instant::now();
            let key: [u8; 32] = core::array::from_fn(|i| (17 * i + 3) as u8);
            let k16 = &key[..16];
            let (iv, iv8, nonce, aad) = ([0x3c; 16], [0x3c; 8], [0x24; 12], [0x11; 16]);
            let data = vec![0x5au8; N];
            let mut buf = vec![0u8; N];
            let mut out = vec![0u8; N];
            let mut empty = [0u8; 0];

            // Poly1305's pairs of blocks; ChaCha20 (SSE2, or SSSE3), alone and
            // with them; the gathered seal's copy.
            item(round, "poly1305", N, &mut || {
                black_box(Poly1305::mac(black_box(&key), black_box(&data)));
            });
            item(round, "chacha20", N, &mut || {
                ChaCha20::new(black_box(&key), &iv).apply_keystream(black_box(&mut buf));
            });
            for size in [N, 1024] {
                item(round, "chacha20poly1305-seal", size, &mut || {
                    black_box(
                        ChaCha20Poly1305::new(black_box(&key))
                            .encrypt_in_place(&nonce, &aad, black_box(&mut buf[..size]))
                            .unwrap(),
                    );
                });
            }
            item(round, "chacha20poly1305-gather", N, &mut || {
                black_box(
                    ChaCha20Poly1305::new(black_box(&key))
                        .encrypt(&nonce, &aad, &[black_box(&data[..])], black_box(&mut out))
                        .unwrap(),
                );
            });

            // AES (AES-NI, or the code without it): the blocks of CTR, ECB,
            // CBC decryption and XTS; CMAC and CBC encryption wait for each
            // block anyway.
            item(round, "aes128-ctr", N, &mut || {
                AesCtr::new(black_box(k16), &iv).unwrap().apply_keystream_final(black_box(&mut buf));
            });
            item(round, "aes128-ecb-encrypt", N, &mut || {
                AesEcb::new(black_box(k16)).unwrap().encrypt(black_box(&mut buf)).unwrap();
            });
            item(round, "aes128-cbc-decrypt", N, &mut || {
                AesCbcDecryptor::new(black_box(k16), &iv).unwrap().decrypt(black_box(&mut buf)).unwrap();
            });
            item(round, "aes128-xts-encrypt", N, &mut || {
                AesXts::new(black_box(&key)).unwrap().encrypt_in_place(&iv, black_box(&mut buf)).unwrap();
            });
            item(round, "aes128-cmac", N, &mut || {
                black_box(AesCmac::mac(black_box(k16), black_box(&data)).unwrap());
            });

            // AES-GCM: CTR with GHASH (PCLMULQDQ, or the code without it);
            // GHASH alone (16 KiB of additional data, no plaintext); the
            // gathered seal's copy; AES-GCM-SIV's POLYVAL and CTR.
            for size in [N, 1024] {
                item(round, "aes128-gcm-seal", size, &mut || {
                    black_box(
                        AesGcm::new(black_box(k16))
                            .unwrap()
                            .encrypt_in_place(&nonce, &aad, black_box(&mut buf[..size]))
                            .unwrap(),
                    );
                });
            }
            item(round, "aes128-gcm-aad-only", N, &mut || {
                black_box(
                    AesGcm::new(black_box(k16))
                        .unwrap()
                        .encrypt_in_place(&nonce, black_box(&data), &mut empty)
                        .unwrap(),
                );
            });
            item(round, "aes128-gcm-gather", N, &mut || {
                black_box(
                    AesGcm::new(black_box(k16))
                        .unwrap()
                        .encrypt(&nonce, &aad, &[black_box(&data[..])], black_box(&mut out))
                        .unwrap(),
                );
            });
            item(round, "aes128-gcm-siv-seal", N, &mut || {
                black_box(
                    AesGcmSiv::new(black_box(k16))
                        .unwrap()
                        .encrypt_in_place(&nonce, &aad, black_box(&mut buf))
                        .unwrap(),
                );
            });

            // Hashes: SHA-512's compression is SSE2 on this target; SHA-1 and
            // SHA-256 use xmm registers only with SHA-NI; BLAKE2s.
            item(round, "sha512", N, &mut || {
                black_box(Sha512::digest(black_box(&data)));
            });
            item(round, "sha256", N, &mut || {
                black_box(Sha256::digest(black_box(&data)));
            });
            item(round, "sha1", N, &mut || {
                black_box(Sha1::digest(black_box(&data)));
            });
            item(round, "blake2s256", N, &mut || {
                black_box(Blake2s256::digest(black_box(&data)));
            });

            // CAST5 and RC2 read their tables by masked scans in xmm
            // registers; scrypt's Salsa20/8 and its xors.
            item(round, "cast5-cbc-encrypt", 1024, &mut || {
                Cast5CbcEncryptor::new(black_box(k16), &iv8).unwrap().encrypt(black_box(&mut buf[..1024])).unwrap();
            });
            item(round, "rc2-cbc-encrypt", 1024, &mut || {
                Rc2CbcEncryptor::new(black_box(k16), &iv8).unwrap().encrypt(black_box(&mut buf[..1024])).unwrap();
            });
            let mut derived = [0u8; 64];
            item(round, "scrypt-1024-8-1", 64, &mut || {
                scrypt::derive(black_box(b"password"), b"NaCl", 1024, 8, 1, usize::MAX, &mut derived).unwrap();
            });

            // The Montgomery multiplication (SSE2) and the copies under a
            // mask behind RSA, FFDH and DSA; the curves' masked reads of
            // their tables of points (the field arithmetic uses no xmm).
            let digest = [0x42; 32];
            item(round, "rsa2048-pkcs1-sign", 256, &mut || {
                black_box(black_box(&self.rsa).sign_pkcs1v15(black_box(&digest), Hash::Sha256).unwrap());
            });
            let d = [0x42; 32];
            let ec = EcPrivateKey::<P256>::from_bytes(&d);
            let peer = *EcPrivateKey::<P256>::from_bytes(&[0x24; 32]).public_key().unwrap().as_bytes();
            item(round, "ecdsa-p256-sha256-sign", 64, &mut || {
                black_box(ec.sign::<Sha256>(black_box(&data[..64])).unwrap());
            });
            item(round, "ecdh-p256", 32, &mut || {
                black_box(black_box(&ec).exchange(&EcPublicKey::from_bytes(black_box(&peer))).unwrap());
            });
            item(round, "p256-public-key", 65, &mut || {
                black_box(EcPrivateKey::<P256>::from_bytes(black_box(&d)).public_key().unwrap());
            });
            vzeroupper();
            eprintln!("xmodes {round} done in {} ms", started.elapsed().as_millis());
        }
    }
}
// XMODES END

// XGHASH BEGIN (generated by scratchpad/ghash/mkghash.py)
/// MEASURING PROTOTYPE, NOT FOR MERGING: candidate bodies for the eight-block
/// loop of x86's `vg_ghash_pclmul` (`body8`, `Impl/Gcm/X86/Pclmul.lean`),
/// written by hand for this measurement only (`cur` is the loop as emitted),
/// each timed alone on 16 KiB (128 turns) in three states of the processor:
/// `fast`, the AVX state not in use (XGETBV(1) = 0x3); `slow`, in use with
/// the upper halves zero (after `vpcmpeqd ymm0` and `vzeroupper`); `nonzero`,
/// in use with the upper halves of ymm0-ymm7 not zero. Next to them, the
/// library's AES-128-GCM with additional data only (GHASH over 16 KiB and
/// over 1 KiB, with the key schedule, the powers and the tag), which shows
/// what a call adds to the loop.
///
/// One line each: `xghash <round> <mode> <name> <bytes> xinuse
/// <before>-><after> min <ns> median <ns> ns, <ps> ps/block`.
#[cfg(target_arch = "x86")]
mod xghash {
    use std::arch::asm;
    use std::hint::black_box;
    use std::time::{Duration, Instant};

    use verified_garbage::aead::aes_gcm::AesGcm;

    use super::xprobe::{vzeroupper, xinuse};

    // Each function: cdecl (scratch, data, turns). `scratch + 16 k` is the
    // slot k: the powers in 0..8, Y in 8 (read on entry, written on return),
    // the reduction constant in 9, what a candidate adds for each power in
    // 10..18 (kind 1: [lo ^ hi | lo ^ hi]; kind 2: [lo ^ hi | hi]) and the
    // byte-reversal mask in 18; `data` is 128 bytes a turn.
    std::arch::global_asm!(
        ".globl vgx_gh_cur",
        ".type vgx_gh_cur, @function",
        ".p2align 6",
        "vgx_gh_cur:",
        "    mov ecx, DWORD PTR [esp+4]",
        "    mov edx, DWORD PTR [esp+8]",
        "    mov eax, DWORD PTR [esp+12]",
        "    movdqu xmm0, XMMWORD PTR [ecx+288]",
        "    movdqu xmm1, XMMWORD PTR [ecx+144]",
        "    movdqu xmm2, XMMWORD PTR [ecx+128]",
        "    movdqu xmm3, XMMWORD PTR [ecx]",
        "    shl eax, 3",
        "    .p2align 4",
        "2:",
        "    movdqu xmm7, XMMWORD PTR [edx]",
        "    pshufb xmm7, xmm0",
        "    pxor xmm2, xmm7",
        "    movdqu xmm3, XMMWORD PTR [ecx+112]",
        "    pxor xmm4, xmm4",
        "    pxor xmm5, xmm5",
        "    pxor xmm6, xmm6",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 17",
        "    pxor xmm6, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 16",
        "    pxor xmm5, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+16]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+96]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 17",
        "    pxor xmm6, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 16",
        "    pxor xmm5, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+32]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+80]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 17",
        "    pxor xmm6, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 16",
        "    pxor xmm5, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+48]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+64]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 17",
        "    pxor xmm6, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 16",
        "    pxor xmm5, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+64]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+48]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 17",
        "    pxor xmm6, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 16",
        "    pxor xmm5, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+80]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+32]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 17",
        "    pxor xmm6, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 16",
        "    pxor xmm5, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+96]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+16]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 17",
        "    pxor xmm6, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 16",
        "    pxor xmm5, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+112]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 17",
        "    pxor xmm6, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 16",
        "    pxor xmm5, xmm7",
        "    movdqa xmm7, xmm5",
        "    psrldq xmm7, 8",
        "    pxor xmm6, xmm7",
        "    pslldq xmm5, 8",
        "    pxor xmm4, xmm5",
        "    movdqa xmm7, xmm4",
        "    pclmulqdq xmm7, xmm1, 16",
        "    pshufd xmm4, xmm4, 78",
        "    pxor xmm4, xmm7",
        "    movdqa xmm7, xmm4",
        "    pclmulqdq xmm7, xmm1, 16",
        "    pshufd xmm4, xmm4, 78",
        "    pxor xmm4, xmm7",
        "    movdqa xmm2, xmm6",
        "    pxor xmm2, xmm4",
        "    add edx, 128",
        "    sub eax, 8",
        "    cmp eax, 8",
        "    jae 2b",
        "    movdqu XMMWORD PTR [ecx+128], xmm2",
        "    ret",
        ".size vgx_gh_cur, .-vgx_gh_cur",
        ".globl vgx_gh_i1",
        ".type vgx_gh_i1, @function",
        ".p2align 6",
        "vgx_gh_i1:",
        "    mov ecx, DWORD PTR [esp+4]",
        "    mov edx, DWORD PTR [esp+8]",
        "    mov eax, DWORD PTR [esp+12]",
        "    movdqu xmm0, XMMWORD PTR [ecx+288]",
        "    movdqu xmm1, XMMWORD PTR [ecx+144]",
        "    movdqu xmm2, XMMWORD PTR [ecx+128]",
        "    movdqu xmm3, XMMWORD PTR [ecx]",
        "    shl eax, 3",
        "    .p2align 4",
        "2:",
        "    movdqu xmm7, XMMWORD PTR [edx]",
        "    pshufb xmm7, xmm0",
        "    pxor xmm2, xmm7",
        "    movdqu xmm3, XMMWORD PTR [ecx+112]",
        "    pxor xmm4, xmm4",
        "    pxor xmm5, xmm5",
        "    pxor xmm6, xmm6",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 17",
        "    pxor xmm6, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    pclmulqdq xmm2, xmm3, 16",
        "    pxor xmm5, xmm2",
        "    movdqu xmm2, XMMWORD PTR [edx+16]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+96]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 17",
        "    pxor xmm6, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    pclmulqdq xmm2, xmm3, 16",
        "    pxor xmm5, xmm2",
        "    movdqu xmm2, XMMWORD PTR [edx+32]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+80]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 17",
        "    pxor xmm6, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    pclmulqdq xmm2, xmm3, 16",
        "    pxor xmm5, xmm2",
        "    movdqu xmm2, XMMWORD PTR [edx+48]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+64]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 17",
        "    pxor xmm6, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    pclmulqdq xmm2, xmm3, 16",
        "    pxor xmm5, xmm2",
        "    movdqu xmm2, XMMWORD PTR [edx+64]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+48]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 17",
        "    pxor xmm6, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    pclmulqdq xmm2, xmm3, 16",
        "    pxor xmm5, xmm2",
        "    movdqu xmm2, XMMWORD PTR [edx+80]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+32]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 17",
        "    pxor xmm6, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    pclmulqdq xmm2, xmm3, 16",
        "    pxor xmm5, xmm2",
        "    movdqu xmm2, XMMWORD PTR [edx+96]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+16]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 17",
        "    pxor xmm6, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    pclmulqdq xmm2, xmm3, 16",
        "    pxor xmm5, xmm2",
        "    movdqu xmm2, XMMWORD PTR [edx+112]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 17",
        "    pxor xmm6, xmm7",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    pclmulqdq xmm2, xmm3, 16",
        "    pxor xmm5, xmm2",
        "    movdqa xmm7, xmm5",
        "    psrldq xmm7, 8",
        "    pxor xmm6, xmm7",
        "    pslldq xmm5, 8",
        "    pxor xmm4, xmm5",
        "    movdqa xmm7, xmm4",
        "    pclmulqdq xmm7, xmm1, 16",
        "    pshufd xmm4, xmm4, 78",
        "    pxor xmm4, xmm7",
        "    movdqa xmm7, xmm4",
        "    pclmulqdq xmm7, xmm1, 16",
        "    pshufd xmm4, xmm4, 78",
        "    pxor xmm4, xmm7",
        "    movdqa xmm2, xmm6",
        "    pxor xmm2, xmm4",
        "    add edx, 128",
        "    sub eax, 8",
        "    cmp eax, 8",
        "    jae 2b",
        "    movdqu XMMWORD PTR [ecx+128], xmm2",
        "    ret",
        ".size vgx_gh_i1, .-vgx_gh_i1",
        ".globl vgx_gh_t2",
        ".type vgx_gh_t2, @function",
        ".p2align 6",
        "vgx_gh_t2:",
        "    mov ecx, DWORD PTR [esp+4]",
        "    mov edx, DWORD PTR [esp+8]",
        "    mov eax, DWORD PTR [esp+12]",
        "    movdqu xmm0, XMMWORD PTR [ecx+288]",
        "    movdqu xmm1, XMMWORD PTR [ecx+144]",
        "    movdqu xmm2, XMMWORD PTR [ecx+128]",
        "    movdqu xmm3, XMMWORD PTR [ecx]",
        "    shl eax, 3",
        "    .p2align 4",
        "2:",
        "    movdqu xmm7, XMMWORD PTR [edx]",
        "    pshufb xmm7, xmm0",
        "    pxor xmm2, xmm7",
        "    movdqu xmm3, XMMWORD PTR [ecx+112]",
        "    pxor xmm4, xmm4",
        "    pxor xmm5, xmm5",
        "    pxor xmm6, xmm6",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 17",
        "    pxor xmm6, xmm1",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 16",
        "    pxor xmm5, xmm1",
        "    movdqu xmm2, XMMWORD PTR [edx+16]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+96]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 17",
        "    pxor xmm6, xmm1",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 16",
        "    pxor xmm5, xmm1",
        "    movdqu xmm2, XMMWORD PTR [edx+32]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+80]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 17",
        "    pxor xmm6, xmm1",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 16",
        "    pxor xmm5, xmm1",
        "    movdqu xmm2, XMMWORD PTR [edx+48]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+64]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 17",
        "    pxor xmm6, xmm1",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 16",
        "    pxor xmm5, xmm1",
        "    movdqu xmm2, XMMWORD PTR [edx+64]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+48]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 17",
        "    pxor xmm6, xmm1",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 16",
        "    pxor xmm5, xmm1",
        "    movdqu xmm2, XMMWORD PTR [edx+80]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+32]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 17",
        "    pxor xmm6, xmm1",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 16",
        "    pxor xmm5, xmm1",
        "    movdqu xmm2, XMMWORD PTR [edx+96]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+16]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 17",
        "    pxor xmm6, xmm1",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 16",
        "    pxor xmm5, xmm1",
        "    movdqu xmm2, XMMWORD PTR [edx+112]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 17",
        "    pxor xmm6, xmm1",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 16",
        "    pxor xmm5, xmm1",
        "    movdqa xmm7, xmm5",
        "    psrldq xmm7, 8",
        "    pxor xmm6, xmm7",
        "    pslldq xmm5, 8",
        "    pxor xmm4, xmm5",
        "    movdqu xmm1, XMMWORD PTR [ecx+144]",
        "    movdqa xmm7, xmm4",
        "    pclmulqdq xmm7, xmm1, 16",
        "    pshufd xmm4, xmm4, 78",
        "    pxor xmm4, xmm7",
        "    movdqa xmm7, xmm4",
        "    pclmulqdq xmm7, xmm1, 16",
        "    pshufd xmm4, xmm4, 78",
        "    pxor xmm4, xmm7",
        "    movdqa xmm2, xmm6",
        "    pxor xmm2, xmm4",
        "    add edx, 128",
        "    sub eax, 8",
        "    cmp eax, 8",
        "    jae 2b",
        "    movdqu XMMWORD PTR [ecx+128], xmm2",
        "    ret",
        ".size vgx_gh_t2, .-vgx_gh_t2",
        ".globl vgx_gh_t2i",
        ".type vgx_gh_t2i, @function",
        ".p2align 6",
        "vgx_gh_t2i:",
        "    mov ecx, DWORD PTR [esp+4]",
        "    mov edx, DWORD PTR [esp+8]",
        "    mov eax, DWORD PTR [esp+12]",
        "    movdqu xmm0, XMMWORD PTR [ecx+288]",
        "    movdqu xmm1, XMMWORD PTR [ecx+144]",
        "    movdqu xmm2, XMMWORD PTR [ecx+128]",
        "    movdqu xmm3, XMMWORD PTR [ecx]",
        "    shl eax, 3",
        "    .p2align 4",
        "2:",
        "    movdqu xmm7, XMMWORD PTR [edx]",
        "    pshufb xmm7, xmm0",
        "    pxor xmm2, xmm7",
        "    movdqu xmm3, XMMWORD PTR [ecx+112]",
        "    pxor xmm4, xmm4",
        "    pxor xmm5, xmm5",
        "    pxor xmm6, xmm6",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 17",
        "    pxor xmm6, xmm1",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    pclmulqdq xmm2, xmm3, 16",
        "    pxor xmm5, xmm2",
        "    movdqu xmm2, XMMWORD PTR [edx+16]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+96]",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 0",
        "    pxor xmm4, xmm1",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 17",
        "    pxor xmm6, xmm7",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 1",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm2, xmm3, 16",
        "    pxor xmm5, xmm2",
        "    movdqu xmm2, XMMWORD PTR [edx+32]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+80]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 17",
        "    pxor xmm6, xmm1",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    pclmulqdq xmm2, xmm3, 16",
        "    pxor xmm5, xmm2",
        "    movdqu xmm2, XMMWORD PTR [edx+48]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+64]",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 0",
        "    pxor xmm4, xmm1",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 17",
        "    pxor xmm6, xmm7",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 1",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm2, xmm3, 16",
        "    pxor xmm5, xmm2",
        "    movdqu xmm2, XMMWORD PTR [edx+64]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+48]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 17",
        "    pxor xmm6, xmm1",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    pclmulqdq xmm2, xmm3, 16",
        "    pxor xmm5, xmm2",
        "    movdqu xmm2, XMMWORD PTR [edx+80]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+32]",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 0",
        "    pxor xmm4, xmm1",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 17",
        "    pxor xmm6, xmm7",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 1",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm2, xmm3, 16",
        "    pxor xmm5, xmm2",
        "    movdqu xmm2, XMMWORD PTR [edx+96]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+16]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 17",
        "    pxor xmm6, xmm1",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 1",
        "    pxor xmm5, xmm7",
        "    pclmulqdq xmm2, xmm3, 16",
        "    pxor xmm5, xmm2",
        "    movdqu xmm2, XMMWORD PTR [edx+112]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx]",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 0",
        "    pxor xmm4, xmm1",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 17",
        "    pxor xmm6, xmm7",
        "    movdqa xmm1, xmm2",
        "    pclmulqdq xmm1, xmm3, 1",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm2, xmm3, 16",
        "    pxor xmm5, xmm2",
        "    movdqa xmm7, xmm5",
        "    psrldq xmm7, 8",
        "    pxor xmm6, xmm7",
        "    pslldq xmm5, 8",
        "    pxor xmm4, xmm5",
        "    movdqu xmm1, XMMWORD PTR [ecx+144]",
        "    movdqa xmm7, xmm4",
        "    pclmulqdq xmm7, xmm1, 16",
        "    pshufd xmm4, xmm4, 78",
        "    pxor xmm4, xmm7",
        "    movdqa xmm7, xmm4",
        "    pclmulqdq xmm7, xmm1, 16",
        "    pshufd xmm4, xmm4, 78",
        "    pxor xmm4, xmm7",
        "    movdqa xmm2, xmm6",
        "    pxor xmm2, xmm4",
        "    add edx, 128",
        "    sub eax, 8",
        "    cmp eax, 8",
        "    jae 2b",
        "    movdqu XMMWORD PTR [ecx+128], xmm2",
        "    ret",
        ".size vgx_gh_t2i, .-vgx_gh_t2i",
        ".globl vgx_gh_k1",
        ".type vgx_gh_k1, @function",
        ".p2align 6",
        "vgx_gh_k1:",
        "    mov ecx, DWORD PTR [esp+4]",
        "    mov edx, DWORD PTR [esp+8]",
        "    mov eax, DWORD PTR [esp+12]",
        "    movdqu xmm0, XMMWORD PTR [ecx+288]",
        "    movdqu xmm1, XMMWORD PTR [ecx+144]",
        "    movdqu xmm2, XMMWORD PTR [ecx+128]",
        "    movdqu xmm3, XMMWORD PTR [ecx]",
        "    shl eax, 3",
        "    .p2align 4",
        "2:",
        "    movdqu xmm7, XMMWORD PTR [edx]",
        "    pshufb xmm7, xmm0",
        "    pxor xmm2, xmm7",
        "    movdqu xmm3, XMMWORD PTR [ecx+112]",
        "    pxor xmm4, xmm4",
        "    pxor xmm5, xmm5",
        "    pxor xmm6, xmm6",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    pshufd xmm7, xmm2, 78",
        "    pxor xmm7, xmm2",
        "    pclmulqdq xmm2, xmm3, 17",
        "    pxor xmm6, xmm2",
        "    movdqu xmm3, XMMWORD PTR [ecx+272]",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm5, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+16]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+96]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    pshufd xmm7, xmm2, 78",
        "    pxor xmm7, xmm2",
        "    pclmulqdq xmm2, xmm3, 17",
        "    pxor xmm6, xmm2",
        "    movdqu xmm3, XMMWORD PTR [ecx+256]",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm5, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+32]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+80]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    pshufd xmm7, xmm2, 78",
        "    pxor xmm7, xmm2",
        "    pclmulqdq xmm2, xmm3, 17",
        "    pxor xmm6, xmm2",
        "    movdqu xmm3, XMMWORD PTR [ecx+240]",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm5, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+48]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+64]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    pshufd xmm7, xmm2, 78",
        "    pxor xmm7, xmm2",
        "    pclmulqdq xmm2, xmm3, 17",
        "    pxor xmm6, xmm2",
        "    movdqu xmm3, XMMWORD PTR [ecx+224]",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm5, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+64]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+48]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    pshufd xmm7, xmm2, 78",
        "    pxor xmm7, xmm2",
        "    pclmulqdq xmm2, xmm3, 17",
        "    pxor xmm6, xmm2",
        "    movdqu xmm3, XMMWORD PTR [ecx+208]",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm5, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+80]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+32]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    pshufd xmm7, xmm2, 78",
        "    pxor xmm7, xmm2",
        "    pclmulqdq xmm2, xmm3, 17",
        "    pxor xmm6, xmm2",
        "    movdqu xmm3, XMMWORD PTR [ecx+192]",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm5, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+96]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+16]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    pshufd xmm7, xmm2, 78",
        "    pxor xmm7, xmm2",
        "    pclmulqdq xmm2, xmm3, 17",
        "    pxor xmm6, xmm2",
        "    movdqu xmm3, XMMWORD PTR [ecx+176]",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm5, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+112]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    pshufd xmm7, xmm2, 78",
        "    pxor xmm7, xmm2",
        "    pclmulqdq xmm2, xmm3, 17",
        "    pxor xmm6, xmm2",
        "    movdqu xmm3, XMMWORD PTR [ecx+160]",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm5, xmm7",
        "    pxor xmm5, xmm4",
        "    pxor xmm5, xmm6",
        "    movdqa xmm7, xmm5",
        "    psrldq xmm7, 8",
        "    pxor xmm6, xmm7",
        "    pslldq xmm5, 8",
        "    pxor xmm4, xmm5",
        "    movdqa xmm7, xmm4",
        "    pclmulqdq xmm7, xmm1, 16",
        "    pshufd xmm4, xmm4, 78",
        "    pxor xmm4, xmm7",
        "    movdqa xmm7, xmm4",
        "    pclmulqdq xmm7, xmm1, 16",
        "    pshufd xmm4, xmm4, 78",
        "    pxor xmm4, xmm7",
        "    movdqa xmm2, xmm6",
        "    pxor xmm2, xmm4",
        "    add edx, 128",
        "    sub eax, 8",
        "    cmp eax, 8",
        "    jae 2b",
        "    movdqu XMMWORD PTR [ecx+128], xmm2",
        "    ret",
        ".size vgx_gh_k1, .-vgx_gh_k1",
        ".globl vgx_gh_k",
        ".type vgx_gh_k, @function",
        ".p2align 6",
        "vgx_gh_k:",
        "    mov ecx, DWORD PTR [esp+4]",
        "    mov edx, DWORD PTR [esp+8]",
        "    mov eax, DWORD PTR [esp+12]",
        "    movdqu xmm0, XMMWORD PTR [ecx+288]",
        "    movdqu xmm1, XMMWORD PTR [ecx+144]",
        "    movdqu xmm2, XMMWORD PTR [ecx+128]",
        "    movdqu xmm3, XMMWORD PTR [ecx]",
        "    shl eax, 3",
        "    .p2align 4",
        "2:",
        "    movdqu xmm3, XMMWORD PTR [edx]",
        "    pshufb xmm3, xmm0",
        "    pxor xmm2, xmm3",
        "    movdqu xmm3, XMMWORD PTR [ecx+112]",
        "    pxor xmm4, xmm4",
        "    pxor xmm5, xmm5",
        "    pxor xmm6, xmm6",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm2, xmm3, 17",
        "    pxor xmm6, xmm2",
        "    movdqu xmm3, XMMWORD PTR [ecx+272]",
        "    pclmulqdq xmm1, xmm3, 0",
        "    pxor xmm5, xmm1",
        "    movdqu xmm2, XMMWORD PTR [edx+16]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+96]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm2, xmm3, 17",
        "    pxor xmm6, xmm2",
        "    movdqu xmm3, XMMWORD PTR [ecx+256]",
        "    pclmulqdq xmm1, xmm3, 0",
        "    pxor xmm5, xmm1",
        "    movdqu xmm2, XMMWORD PTR [edx+32]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+80]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm2, xmm3, 17",
        "    pxor xmm6, xmm2",
        "    movdqu xmm3, XMMWORD PTR [ecx+240]",
        "    pclmulqdq xmm1, xmm3, 0",
        "    pxor xmm5, xmm1",
        "    movdqu xmm2, XMMWORD PTR [edx+48]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+64]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm2, xmm3, 17",
        "    pxor xmm6, xmm2",
        "    movdqu xmm3, XMMWORD PTR [ecx+224]",
        "    pclmulqdq xmm1, xmm3, 0",
        "    pxor xmm5, xmm1",
        "    movdqu xmm2, XMMWORD PTR [edx+64]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+48]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm2, xmm3, 17",
        "    pxor xmm6, xmm2",
        "    movdqu xmm3, XMMWORD PTR [ecx+208]",
        "    pclmulqdq xmm1, xmm3, 0",
        "    pxor xmm5, xmm1",
        "    movdqu xmm2, XMMWORD PTR [edx+80]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+32]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm2, xmm3, 17",
        "    pxor xmm6, xmm2",
        "    movdqu xmm3, XMMWORD PTR [ecx+192]",
        "    pclmulqdq xmm1, xmm3, 0",
        "    pxor xmm5, xmm1",
        "    movdqu xmm2, XMMWORD PTR [edx+96]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+16]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm2, xmm3, 17",
        "    pxor xmm6, xmm2",
        "    movdqu xmm3, XMMWORD PTR [ecx+176]",
        "    pclmulqdq xmm1, xmm3, 0",
        "    pxor xmm5, xmm1",
        "    movdqu xmm2, XMMWORD PTR [edx+112]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx]",
        "    movdqa xmm7, xmm2",
        "    pclmulqdq xmm7, xmm3, 0",
        "    pxor xmm4, xmm7",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm2, xmm3, 17",
        "    pxor xmm6, xmm2",
        "    movdqu xmm3, XMMWORD PTR [ecx+160]",
        "    pclmulqdq xmm1, xmm3, 0",
        "    pxor xmm5, xmm1",
        "    pxor xmm5, xmm4",
        "    pxor xmm5, xmm6",
        "    movdqa xmm7, xmm5",
        "    psrldq xmm7, 8",
        "    pxor xmm6, xmm7",
        "    pslldq xmm5, 8",
        "    pxor xmm4, xmm5",
        "    movdqu xmm1, XMMWORD PTR [ecx+144]",
        "    movdqa xmm7, xmm4",
        "    pclmulqdq xmm7, xmm1, 16",
        "    pshufd xmm4, xmm4, 78",
        "    pxor xmm4, xmm7",
        "    movdqa xmm7, xmm4",
        "    pclmulqdq xmm7, xmm1, 16",
        "    pshufd xmm4, xmm4, 78",
        "    pxor xmm4, xmm7",
        "    movdqa xmm2, xmm6",
        "    pxor xmm2, xmm4",
        "    add edx, 128",
        "    sub eax, 8",
        "    cmp eax, 8",
        "    jae 2b",
        "    movdqu XMMWORD PTR [ecx+128], xmm2",
        "    ret",
        ".size vgx_gh_k, .-vgx_gh_k",
        ".globl vgx_gh_kl",
        ".type vgx_gh_kl, @function",
        ".p2align 6",
        "vgx_gh_kl:",
        "    mov ecx, DWORD PTR [esp+4]",
        "    mov edx, DWORD PTR [esp+8]",
        "    mov eax, DWORD PTR [esp+12]",
        "    movdqu xmm0, XMMWORD PTR [ecx+288]",
        "    movdqu xmm1, XMMWORD PTR [ecx+144]",
        "    movdqu xmm2, XMMWORD PTR [ecx+128]",
        "    movdqu xmm3, XMMWORD PTR [ecx]",
        "    shl eax, 3",
        "    .p2align 4",
        "2:",
        "    movdqu xmm3, XMMWORD PTR [edx]",
        "    pshufb xmm3, xmm0",
        "    pxor xmm2, xmm3",
        "    movdqu xmm3, XMMWORD PTR [ecx+112]",
        "    movdqu xmm7, XMMWORD PTR [ecx+272]",
        "    pxor xmm4, xmm4",
        "    pxor xmm5, xmm5",
        "    pxor xmm6, xmm6",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm3, xmm2, 0",
        "    pxor xmm4, xmm3",
        "    pclmulqdq xmm1, xmm7, 0",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm7, xmm2, 17",
        "    pxor xmm6, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+16]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+96]",
        "    movdqu xmm7, XMMWORD PTR [ecx+256]",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm3, xmm2, 0",
        "    pxor xmm4, xmm3",
        "    pclmulqdq xmm1, xmm7, 0",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm7, xmm2, 17",
        "    pxor xmm6, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+32]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+80]",
        "    movdqu xmm7, XMMWORD PTR [ecx+240]",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm3, xmm2, 0",
        "    pxor xmm4, xmm3",
        "    pclmulqdq xmm1, xmm7, 0",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm7, xmm2, 17",
        "    pxor xmm6, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+48]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+64]",
        "    movdqu xmm7, XMMWORD PTR [ecx+224]",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm3, xmm2, 0",
        "    pxor xmm4, xmm3",
        "    pclmulqdq xmm1, xmm7, 0",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm7, xmm2, 17",
        "    pxor xmm6, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+64]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+48]",
        "    movdqu xmm7, XMMWORD PTR [ecx+208]",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm3, xmm2, 0",
        "    pxor xmm4, xmm3",
        "    pclmulqdq xmm1, xmm7, 0",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm7, xmm2, 17",
        "    pxor xmm6, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+80]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+32]",
        "    movdqu xmm7, XMMWORD PTR [ecx+192]",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm3, xmm2, 0",
        "    pxor xmm4, xmm3",
        "    pclmulqdq xmm1, xmm7, 0",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm7, xmm2, 17",
        "    pxor xmm6, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+96]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+16]",
        "    movdqu xmm7, XMMWORD PTR [ecx+176]",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm3, xmm2, 0",
        "    pxor xmm4, xmm3",
        "    pclmulqdq xmm1, xmm7, 0",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm7, xmm2, 17",
        "    pxor xmm6, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+112]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx]",
        "    movdqu xmm7, XMMWORD PTR [ecx+160]",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm3, xmm2, 0",
        "    pxor xmm4, xmm3",
        "    pclmulqdq xmm1, xmm7, 0",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm7, xmm2, 17",
        "    pxor xmm6, xmm7",
        "    pxor xmm5, xmm4",
        "    pxor xmm5, xmm6",
        "    movdqa xmm7, xmm5",
        "    psrldq xmm7, 8",
        "    pxor xmm6, xmm7",
        "    pslldq xmm5, 8",
        "    pxor xmm4, xmm5",
        "    movdqu xmm1, XMMWORD PTR [ecx+144]",
        "    movdqa xmm7, xmm4",
        "    pclmulqdq xmm7, xmm1, 16",
        "    pshufd xmm4, xmm4, 78",
        "    pxor xmm4, xmm7",
        "    movdqa xmm7, xmm4",
        "    pclmulqdq xmm7, xmm1, 16",
        "    pshufd xmm4, xmm4, 78",
        "    pxor xmm4, xmm7",
        "    movdqa xmm2, xmm6",
        "    pxor xmm2, xmm4",
        "    add edx, 128",
        "    sub eax, 8",
        "    cmp eax, 8",
        "    jae 2b",
        "    movdqu XMMWORD PTR [ecx+128], xmm2",
        "    ret",
        ".size vgx_gh_kl, .-vgx_gh_kl",
        ".globl vgx_gh_kly",
        ".type vgx_gh_kly, @function",
        ".p2align 6",
        "vgx_gh_kly:",
        "    mov ecx, DWORD PTR [esp+4]",
        "    mov edx, DWORD PTR [esp+8]",
        "    mov eax, DWORD PTR [esp+12]",
        "    movdqu xmm0, XMMWORD PTR [ecx+288]",
        "    movdqu xmm1, XMMWORD PTR [ecx+144]",
        "    movdqu xmm2, XMMWORD PTR [ecx+128]",
        "    movdqu xmm3, XMMWORD PTR [ecx]",
        "    shl eax, 3",
        "    .p2align 4",
        "2:",
        "    movdqu xmm2, XMMWORD PTR [edx+16]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+96]",
        "    movdqu xmm7, XMMWORD PTR [ecx+256]",
        "    pxor xmm4, xmm4",
        "    pxor xmm5, xmm5",
        "    pxor xmm6, xmm6",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm3, xmm2, 0",
        "    pxor xmm4, xmm3",
        "    pclmulqdq xmm1, xmm7, 0",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm7, xmm2, 17",
        "    pxor xmm6, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+32]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+80]",
        "    movdqu xmm7, XMMWORD PTR [ecx+240]",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm3, xmm2, 0",
        "    pxor xmm4, xmm3",
        "    pclmulqdq xmm1, xmm7, 0",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm7, xmm2, 17",
        "    pxor xmm6, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+48]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+64]",
        "    movdqu xmm7, XMMWORD PTR [ecx+224]",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm3, xmm2, 0",
        "    pxor xmm4, xmm3",
        "    pclmulqdq xmm1, xmm7, 0",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm7, xmm2, 17",
        "    pxor xmm6, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+64]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+48]",
        "    movdqu xmm7, XMMWORD PTR [ecx+208]",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm3, xmm2, 0",
        "    pxor xmm4, xmm3",
        "    pclmulqdq xmm1, xmm7, 0",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm7, xmm2, 17",
        "    pxor xmm6, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+80]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+32]",
        "    movdqu xmm7, XMMWORD PTR [ecx+192]",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm3, xmm2, 0",
        "    pxor xmm4, xmm3",
        "    pclmulqdq xmm1, xmm7, 0",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm7, xmm2, 17",
        "    pxor xmm6, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+96]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+16]",
        "    movdqu xmm7, XMMWORD PTR [ecx+176]",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm3, xmm2, 0",
        "    pxor xmm4, xmm3",
        "    pclmulqdq xmm1, xmm7, 0",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm7, xmm2, 17",
        "    pxor xmm6, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+112]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx]",
        "    movdqu xmm7, XMMWORD PTR [ecx+160]",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm3, xmm2, 0",
        "    pxor xmm4, xmm3",
        "    pclmulqdq xmm1, xmm7, 0",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm7, xmm2, 17",
        "    pxor xmm6, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+128]",
        "    pxor xmm2, xmm3",
        "    movdqu xmm3, XMMWORD PTR [ecx+112]",
        "    movdqu xmm7, XMMWORD PTR [ecx+272]",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm3, xmm2, 0",
        "    pxor xmm4, xmm3",
        "    pclmulqdq xmm1, xmm7, 0",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm7, xmm2, 17",
        "    pxor xmm6, xmm7",
        "    pxor xmm5, xmm4",
        "    pxor xmm5, xmm6",
        "    movdqa xmm7, xmm5",
        "    psrldq xmm7, 8",
        "    pxor xmm6, xmm7",
        "    pslldq xmm5, 8",
        "    pxor xmm4, xmm5",
        "    movdqu xmm1, XMMWORD PTR [ecx+144]",
        "    movdqa xmm7, xmm4",
        "    pclmulqdq xmm7, xmm1, 16",
        "    pshufd xmm4, xmm4, 78",
        "    pxor xmm4, xmm7",
        "    movdqa xmm7, xmm4",
        "    pclmulqdq xmm7, xmm1, 16",
        "    pshufd xmm4, xmm4, 78",
        "    pxor xmm4, xmm7",
        "    movdqa xmm2, xmm6",
        "    pxor xmm2, xmm4",
        "    movdqu XMMWORD PTR [ecx+128], xmm2",
        "    add edx, 128",
        "    sub eax, 8",
        "    cmp eax, 8",
        "    jae 2b",
        "    movdqu XMMWORD PTR [ecx+128], xmm2",
        "    ret",
        ".size vgx_gh_kly, .-vgx_gh_kly",
        ".globl vgx_gh_klz",
        ".type vgx_gh_klz, @function",
        ".p2align 6",
        "vgx_gh_klz:",
        "    mov ecx, DWORD PTR [esp+4]",
        "    mov edx, DWORD PTR [esp+8]",
        "    mov eax, DWORD PTR [esp+12]",
        "    movdqu xmm0, XMMWORD PTR [ecx+288]",
        "    movdqu xmm1, XMMWORD PTR [ecx+144]",
        "    movdqu xmm2, XMMWORD PTR [ecx+128]",
        "    movdqu xmm3, XMMWORD PTR [ecx]",
        "    shl eax, 3",
        "    .p2align 4",
        "2:",
        "    movdqu xmm2, XMMWORD PTR [edx+16]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+96]",
        "    movdqu xmm7, XMMWORD PTR [ecx+256]",
        "    pxor xmm4, xmm4",
        "    pxor xmm5, xmm5",
        "    pxor xmm6, xmm6",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm3, xmm2, 0",
        "    pxor xmm4, xmm3",
        "    pclmulqdq xmm1, xmm7, 0",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm7, xmm2, 17",
        "    pxor xmm6, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+32]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+80]",
        "    movdqu xmm7, XMMWORD PTR [ecx+240]",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm3, xmm2, 0",
        "    pxor xmm4, xmm3",
        "    pclmulqdq xmm1, xmm7, 0",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm7, xmm2, 17",
        "    pxor xmm6, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+48]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+64]",
        "    movdqu xmm7, XMMWORD PTR [ecx+224]",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm3, xmm2, 0",
        "    pxor xmm4, xmm3",
        "    pclmulqdq xmm1, xmm7, 0",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm7, xmm2, 17",
        "    pxor xmm6, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+64]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+48]",
        "    movdqu xmm7, XMMWORD PTR [ecx+208]",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm3, xmm2, 0",
        "    pxor xmm4, xmm3",
        "    pclmulqdq xmm1, xmm7, 0",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm7, xmm2, 17",
        "    pxor xmm6, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+80]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+32]",
        "    movdqu xmm7, XMMWORD PTR [ecx+192]",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm3, xmm2, 0",
        "    pxor xmm4, xmm3",
        "    pclmulqdq xmm1, xmm7, 0",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm7, xmm2, 17",
        "    pxor xmm6, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+96]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+16]",
        "    movdqu xmm7, XMMWORD PTR [ecx+176]",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm3, xmm2, 0",
        "    pxor xmm4, xmm3",
        "    pclmulqdq xmm1, xmm7, 0",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm7, xmm2, 17",
        "    pxor xmm6, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx+112]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx]",
        "    movdqu xmm7, XMMWORD PTR [ecx+160]",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm3, xmm2, 0",
        "    pxor xmm4, xmm3",
        "    pclmulqdq xmm1, xmm7, 0",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm7, xmm2, 17",
        "    pxor xmm6, xmm7",
        "    movdqu xmm2, XMMWORD PTR [edx]",
        "    pshufb xmm2, xmm0",
        "    movdqu xmm3, XMMWORD PTR [ecx+128]",
        "    pxor xmm2, xmm3",
        "    movdqu xmm3, XMMWORD PTR [ecx+112]",
        "    movdqu xmm7, XMMWORD PTR [ecx+272]",
        "    pshufd xmm1, xmm2, 78",
        "    pxor xmm1, xmm2",
        "    pclmulqdq xmm3, xmm2, 0",
        "    pxor xmm4, xmm3",
        "    pclmulqdq xmm1, xmm7, 0",
        "    pxor xmm5, xmm1",
        "    pclmulqdq xmm7, xmm2, 17",
        "    pxor xmm6, xmm7",
        "    pxor xmm5, xmm4",
        "    pxor xmm5, xmm6",
        "    movdqa xmm7, xmm5",
        "    psrldq xmm7, 8",
        "    pxor xmm6, xmm7",
        "    pslldq xmm5, 8",
        "    pxor xmm4, xmm5",
        "    movdqu xmm1, XMMWORD PTR [ecx+144]",
        "    movdqa xmm5, xmm4",
        "    pclmulqdq xmm5, xmm1, 16",
        "    pshufd xmm4, xmm4, 78",
        "    pxor xmm4, xmm5",
        "    movdqa xmm5, xmm4",
        "    pclmulqdq xmm5, xmm1, 16",
        "    pshufd xmm4, xmm4, 78",
        "    pxor xmm4, xmm5",
        "    pxor xmm6, xmm4",
        "    movdqu XMMWORD PTR [ecx+128], xmm6",
        "    add edx, 128",
        "    sub eax, 8",
        "    cmp eax, 8",
        "    jae 2b",
        "    movdqu XMMWORD PTR [ecx+128], xmm6",
        "    ret",
        ".size vgx_gh_klz, .-vgx_gh_klz",
    );

    type Cand = unsafe extern "C" fn(*mut u8, *const u8, u32);
    unsafe extern "C" {
        fn vgx_gh_cur(scratch: *mut u8, data: *const u8, turns: u32);
        fn vgx_gh_i1(scratch: *mut u8, data: *const u8, turns: u32);
        fn vgx_gh_t2(scratch: *mut u8, data: *const u8, turns: u32);
        fn vgx_gh_t2i(scratch: *mut u8, data: *const u8, turns: u32);
        fn vgx_gh_k1(scratch: *mut u8, data: *const u8, turns: u32);
        fn vgx_gh_k(scratch: *mut u8, data: *const u8, turns: u32);
        fn vgx_gh_kl(scratch: *mut u8, data: *const u8, turns: u32);
        fn vgx_gh_kly(scratch: *mut u8, data: *const u8, turns: u32);
        fn vgx_gh_klz(scratch: *mut u8, data: *const u8, turns: u32);
    }
    /// The candidates, with the kind of what their slots 10..18 hold.
    const CANDS: [(&str, Cand, u8); 9] = [
        ("cur", vgx_gh_cur, 0),
        ("i1", vgx_gh_i1, 0),
        ("t2", vgx_gh_t2, 0),
        ("t2i", vgx_gh_t2i, 0),
        ("k1", vgx_gh_k1, 1),
        ("k", vgx_gh_k, 1),
        ("kl", vgx_gh_kl, 2),
        ("kly", vgx_gh_kly, 2),
        ("klz", vgx_gh_klz, 2),
    ];

    const TURNS: usize = 128;
    static DATA: [u8; 128 * TURNS] = {
        let mut d = [0u8; 128 * TURNS];
        let mut i = 0;
        while i < d.len() {
            d[i] = (i * 131 + (i >> 8) * 17 + 5) as u8;
            i += 1;
        }
        d
    };

    #[repr(C, align(64))]
    struct Scratch([u8; 512]);

    /// Eight "powers" (any values time alike), Y, the constants, and the
    /// slots 10..18 of the kind `kind`.
    fn scratch(kind: u8) -> Scratch {
        let mut s = Scratch([0; 512]);
        for (i, b) in s.0[..144].iter_mut().enumerate() {
            *b = (i as u32).wrapping_mul(0x9e37_79b9).rotate_left(11) as u8 ^ 0x5a;
        }
        s.0[144 + 15] = 0xc2;
        for k in 0..8 {
            let (lo, hi) = (
                u64::from_le_bytes(s.0[16 * k..16 * k + 8].try_into().unwrap()),
                u64::from_le_bytes(s.0[16 * k + 8..16 * k + 16].try_into().unwrap()),
            );
            let o = 160 + 16 * k;
            s.0[o..o + 8].copy_from_slice(&(lo ^ hi).to_le_bytes());
            s.0[o + 8..o + 16].copy_from_slice(&(if kind == 2 { hi } else { lo ^ hi }).to_le_bytes());
        }
        for i in 0..16 {
            s.0[288 + i] = 15 - i as u8;
        }
        s
    }

    const MODES: [&str; 3] = ["fast", "slow", "nonzero"];

    /// Puts the processor in mode `m` of `MODES`, but for the sleep `fast`
    /// needs; false where it has no AVX2 to do so.
    fn set(m: usize) -> bool {
        if m == 0 {
            vzeroupper();
            return true;
        }
        if !std::is_x86_feature_detected!("avx2") {
            return false;
        }
        // SAFETY: AVX2 is available.
        unsafe {
            if m == 1 {
                asm!("vpcmpeqd ymm0, ymm0, ymm0", "vzeroupper",
                    out("xmm0") _, out("xmm1") _, out("xmm2") _, out("xmm3") _,
                    out("xmm4") _, out("xmm5") _, out("xmm6") _, out("xmm7") _,
                    options(nostack, nomem));
            } else {
                asm!("vpcmpeqd ymm0, ymm0, ymm0", "vpcmpeqd ymm1, ymm1, ymm1",
                    "vpcmpeqd ymm2, ymm2, ymm2", "vpcmpeqd ymm3, ymm3, ymm3",
                    "vpcmpeqd ymm4, ymm4, ymm4", "vpcmpeqd ymm5, ymm5, ymm5",
                    "vpcmpeqd ymm6, ymm6, ymm6", "vpcmpeqd ymm7, ymm7, ymm7",
                    out("xmm0") _, out("xmm1") _, out("xmm2") _, out("xmm3") _,
                    out("xmm4") _, out("xmm5") _, out("xmm6") _, out("xmm7") _,
                    options(nostack, nomem));
            }
        }
        true
    }

    /// The fastest and the median of 41 timings of `f` in mode `m`, set again
    /// before each (a context switch may have ended it), in nanoseconds, with
    /// XGETBV(1) before and after; `None` where the mode cannot be set.
    fn time(m: usize, mut f: impl FnMut()) -> Option<(u32, u32, u32, u32)> {
        if !set(m) {
            return None;
        }
        if m == 0 {
            std::thread::sleep(Duration::from_millis(3));
        }
        f();
        let before = xinuse();
        let mut t = [0u32; 41];
        for t in &mut t {
            if m != 0 {
                set(m);
            }
            let start = Instant::now();
            f();
            *t = start.elapsed().as_nanos() as u32;
        }
        let after = xinuse();
        t.sort_unstable();
        Some((before, after, t[0], t[20]))
    }

    pub fn candidates(round: u32) {
        if !(std::is_x86_feature_detected!("pclmulqdq") && std::is_x86_feature_detected!("ssse3")) {
            eprintln!("xghash {round} skip: the processor has no PCLMULQDQ or no SSSE3");
            return;
        }
        // Every candidate leaves the Y that the loop as emitted leaves.
        let want = {
            let mut s = scratch(0);
            // SAFETY: the 512 bytes of the scratch and the 128 bytes a turn of
            // the data are valid; the functions follow cdecl; the processor
            // has PCLMULQDQ and SSSE3.
            unsafe { vgx_gh_cur(s.0.as_mut_ptr(), DATA.as_ptr(), TURNS as u32) };
            s.0[128..144].to_vec()
        };
        let line = |mode: &str, name: &str, bytes: usize, calls: u32, (before, after, min, med): (u32, u32, u32, u32)| {
            eprintln!(
                "xghash {round} {mode:<7} {name:<10} {bytes:>5} xinuse {before:#x}->{after:#x} min {:>8.1} median {:>8.1} ns, {:>6} ps/block",
                f64::from(min) / f64::from(calls),
                f64::from(med) / f64::from(calls),
                u64::from(med) * 1000 / (u64::from(calls) * (bytes as u64 / 16))
            );
        };
        for (m, mode) in MODES.iter().enumerate() {
            for (name, f, kind) in CANDS {
                let mut s = scratch(kind);
                // SAFETY: as above.
                unsafe { f(s.0.as_mut_ptr(), DATA.as_ptr(), TURNS as u32) };
                if s.0[128..144] != want[..] {
                    eprintln!("xghash {round} {mode} {name} WRONG: not the Y of the loop as emitted");
                    continue;
                }
                let p = s.0.as_mut_ptr();
                // SAFETY: as above.
                if let Some(t) = time(m, || unsafe { f(black_box(p), black_box(DATA.as_ptr()), TURNS as u32) }) {
                    line(mode, name, 128 * TURNS, 1, t);
                }
            }
            // The library: AES-128-GCM over additional data only, whose GHASH
            // is the eight-block loop (with PCLMULQDQ and SSSE3 among the
            // features the library uses), with all that a call adds.
            let key = [0x42u8; 16];
            let nonce = [0x24u8; 12];
            for (bytes, calls) in [(128 * TURNS, 1u32), (1024, 16)] {
                let mut empty = [0u8; 0];
                let t = time(m, || {
                    for _ in 0..calls {
                        black_box(
                            AesGcm::new(black_box(&key))
                                .unwrap()
                                .encrypt_in_place(&nonce, black_box(&DATA[..bytes]), &mut empty)
                                .unwrap(),
                        );
                    }
                });
                if let Some(t) = t {
                    line(mode, "lib-gmac", bytes, calls, t);
                }
            }
        }
        vzeroupper();
    }
}
// XGHASH END
