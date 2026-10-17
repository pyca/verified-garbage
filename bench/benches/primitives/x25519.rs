//! X25519.

use criterion::Criterion;

pub const USES: &[&str] = &["x25519"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use aws_lc_rs::agreement::{self, UnparsedPublicKey};
    use aws_lc_rs::encoding::{AsBigEndian, Curve25519SeedBin};
    use aws_lc_rs::error::Unspecified;
    use criterion::BenchmarkId;
    use openssl::derive::Deriver;
    use openssl::pkey::{Id, PKey};
    use verified_garbage::x25519::{PrivateKey, x25519};

    use crate::{AWS_LC, OPENSSL, VG};
    #[cfg(target_arch = "aarch64")]
    tmp_inv::bench(c);
    let private = [0x42; 32];
    let peer = PrivateKey::from_bytes(&[0x24; 32]).public_key();
    // Each side's private key is loaded once, outside the measurements, as a
    // party holds its key across exchanges (OpenSSL's and aws-lc-rs's imports
    // also derive the public key, a second scalar multiplication); the peer's
    // public key comes with each exchange.
    let vg_private = PrivateKey::from_bytes(&private);
    let openssl_private = PKey::private_key_from_raw_bytes(&private, Id::X25519).unwrap();
    let aws_lc_private =
        agreement::PrivateKey::from_private_key(&agreement::X25519, &private).unwrap();
    // aws-lc-rs's Diffie-Hellman (which also rejects an all-zero secret),
    // decoding the peer's public key as OpenSSL's does.
    let aws_lc_agree = |private: &agreement::PrivateKey, peer: &[u8; 32]| {
        agreement::agree(
            private,
            UnparsedPublicKey::new(&agreement::X25519, peer),
            Unspecified,
            |s| Ok(s.to_vec()),
        )
        .unwrap()
    };
    assert_eq!(
        aws_lc_agree(&aws_lc_private, &peer),
        vg_private.diffie_hellman(&peer).unwrap()
    );
    assert_eq!(
        aws_lc_private.compute_public_key().unwrap().as_ref(),
        vg_private.public_key()
    );
    let mut g = c.benchmark_group("x25519");
    // One Diffie-Hellman: a shared secret from a private key and the peer's
    // public key. The ids' size is the bytes of the shared secret.
    g.bench_function(BenchmarkId::new(VG, 32), |b| {
        b.iter(|| {
            black_box(&vg_private)
                .diffie_hellman(black_box(&peer))
                .unwrap()
        })
    });
    g.bench_function(BenchmarkId::new(OPENSSL, 32), |b| {
        b.iter(|| {
            let peer = PKey::public_key_from_raw_bytes(black_box(&peer), Id::X25519).unwrap();
            let mut d = Deriver::new(black_box(&openssl_private)).unwrap();
            d.set_peer(&peer).unwrap();
            d.derive_to_vec().unwrap()
        })
    });
    g.bench_function(BenchmarkId::new(AWS_LC, 32), |b| {
        b.iter(|| aws_lc_agree(black_box(&aws_lc_private), black_box(&peer)))
    });
    g.finish();

    // Neither OpenSSL nor aws-lc-rs has a function of the scalar
    // multiplication alone: their nearest is the same Diffie-Hellman (which
    // also rejects an all-zero secret).
    let mut g = c.benchmark_group("x25519_raw");
    g.bench_function(BenchmarkId::new(VG, 32), |b| {
        b.iter(|| x25519(black_box(&private), black_box(&peer)))
    });
    g.bench_function(BenchmarkId::new(OPENSSL, 32), |b| {
        b.iter(|| {
            let peer = PKey::public_key_from_raw_bytes(black_box(&peer), Id::X25519).unwrap();
            let mut d = Deriver::new(black_box(&openssl_private)).unwrap();
            d.set_peer(&peer).unwrap();
            d.derive_to_vec().unwrap()
        })
    });
    g.bench_function(BenchmarkId::new(AWS_LC, 32), |b| {
        b.iter(|| aws_lc_agree(black_box(&aws_lc_private), black_box(&peer)))
    });
    g.finish();

    let mut g = c.benchmark_group("x25519_public_key");
    g.bench_function(BenchmarkId::new(VG, 32), |b| {
        b.iter(|| PrivateKey::from_bytes(black_box(&private)).public_key())
    });
    g.bench_function(BenchmarkId::new(OPENSSL, 32), |b| {
        b.iter(|| {
            PKey::private_key_from_raw_bytes(black_box(&private), Id::X25519)
                .unwrap()
                .raw_public_key()
                .unwrap()
        })
    });
    g.bench_function(BenchmarkId::new(AWS_LC, 32), |b| {
        b.iter(|| {
            agreement::PrivateKey::from_private_key(&agreement::X25519, black_box(&private))
                .unwrap()
                .compute_public_key()
                .unwrap()
        })
    });
    g.finish();

    // A new key pair: a random private key and its public key, which
    // OpenSSL's and aws-lc-rs's key generation always derive.
    let mut g = c.benchmark_group("x25519_generate");
    g.bench_function(BenchmarkId::new(VG, 32), |b| {
        b.iter(|| {
            let key = PrivateKey::generate().unwrap();
            (*key.as_bytes(), key.public_key())
        })
    });
    g.bench_function(BenchmarkId::new(OPENSSL, 32), |b| {
        b.iter(|| {
            let key = PKey::generate_x25519().unwrap();
            (
                key.raw_private_key().unwrap(),
                key.raw_public_key().unwrap(),
            )
        })
    });
    g.bench_function(BenchmarkId::new(AWS_LC, 32), |b| {
        b.iter(|| {
            let key = agreement::PrivateKey::generate(&agreement::X25519).unwrap();
            let private: Curve25519SeedBin = key.as_be_bytes().unwrap();
            (private, key.compute_public_key().unwrap())
        })
    });
    g.finish();
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64"
)))]
pub fn bench(_: &mut Criterion) {}

// THROWAWAY: our divstep inversion (the span of vg_x25519 after lastSwap)
// against s2n-bignum's bignum_inv_p25519, in isolation.
#[cfg(target_arch = "aarch64")]
mod tmp_inv {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::global_asm!(
        ".p2align 2",
        ".globl vg_tmp_s2n_inv",
        "vg_tmp_s2n_inv:",
        include_str!("tmp_s2n_inv.s")
    );
    #[cfg(target_vendor = "apple")]
    core::arch::global_asm!(
        ".p2align 2",
        ".globl _vg_tmp_s2n_inv",
        "_vg_tmp_s2n_inv:",
        include_str!("tmp_s2n_inv.s")
    );
    unsafe extern "C" {
        pub fn vg_tmp_s2n_inv(z: *mut u64, x: *const u64);
    }
    /// ws[16..20] in, ws[68..72] out.
    #[unsafe(naked)]
    pub unsafe extern "C" fn vg_tmp_our_inv(ws: *mut u64) {
        core::arch::naked_asm!(
            "stp x19, x20, [sp, #-48]!",
            "stp x21, x22, [sp, #16]",
            "stp x23, x24, [sp, #32]",
            include_str!("tmp_our_inv.s"),
            "ldp x21, x22, [sp, #16]",
            "ldp x23, x24, [sp, #32]",
            "ldp x19, x20, [sp], #48",
            "ret"
        )
    }
    /// Ten batches of 59 divsteps, each batch's inputs mixed with the
    /// last matrix (as the real loop's are), from x1 = d, x2 = f, x3 = g.
    #[unsafe(naked)]
    pub unsafe extern "C" fn vg_tmp_our_ds(st: *mut u64) {
        core::arch::naked_asm!(
            "stp x19, x20, [sp, #-16]!",
            "mov x20, x0",
            "ldp x1, x2, [x20]",
            "ldr x3, [x20, #16]",
            "movz x19, #10",
            "31:",
            include_str!("tmp_our_ds.s"),
            "eor x2, x2, x4",
            "eor x3, x3, x6",
            "orr x2, x2, #1",
            "subs x19, x19, #1",
            "b.ne 31b",
            "stp x1, x2, [x20]",
            "str x3, [x20, #16]",
            "ldp x19, x20, [sp], #16",
            "ret"
        )
    }
    #[unsafe(naked)]
    pub unsafe extern "C" fn vg_tmp_s2n_ds(st: *mut u64) {
        core::arch::naked_asm!(
            "stp x19, x20, [sp, #-16]!",
            "mov x20, x0",
            "ldp x1, x2, [x20]",
            "ldr x3, [x20, #16]",
            "movz x19, #10",
            "32:",
            include_str!("tmp_s2n_ds.s"),
            "eor x2, x2, x10",
            "eor x3, x3, x12",
            "orr x2, x2, #1",
            "subs x19, x19, #1",
            "b.ne 32b",
            "stp x1, x2, [x20]",
            "str x3, [x20, #16]",
            "ldp x19, x20, [sp], #16",
            "ret"
        )
    }
    const P: [u64; 4] = [
        0xffff_ffff_ffff_ffed,
        u64::MAX,
        u64::MAX,
        0x7fff_ffff_ffff_ffff,
    ];
    pub fn reduce(mut x: [u64; 4]) -> [u64; 4] {
        loop {
            let ge = (0..4)
                .rev()
                .find(|&i| x[i] != P[i])
                .is_none_or(|i| x[i] > P[i]);
            if !ge {
                return x;
            }
            let mut b = false;
            for i in 0..4 {
                let (d, b1) = x[i].overflowing_sub(P[i]);
                let (d, b2) = d.overflowing_sub(b as u64);
                x[i] = d;
                b = b1 || b2;
            }
        }
    }
    pub fn bench(c: &mut criterion::Criterion) {
        use criterion::BenchmarkId;
        use std::hint::black_box;
        let x: [u64; 4] = [
            0x0123_4567_89ab_cdef,
            0xfedc_ba98_7654_3210,
            0x1111_2222_3333_4444,
            0x5555_6666_7777_0888,
        ];
        let mut ws = vec![0u64; 512];
        ws[16..20].copy_from_slice(&x);
        unsafe { vg_tmp_our_inv(ws.as_mut_ptr()) };
        let ours: [u64; 4] = ws[68..72].try_into().unwrap();
        let mut z = [0u64; 4];
        unsafe { vg_tmp_s2n_inv(z.as_mut_ptr(), x.as_ptr()) };
        assert_eq!(reduce(ours), reduce(z));
        let mut g = c.benchmark_group("x25519_inv");
        g.bench_function(BenchmarkId::new(crate::VG, 32), |b| {
            b.iter(|| {
                ws[16..20].copy_from_slice(black_box(&x));
                unsafe { vg_tmp_our_inv(ws.as_mut_ptr()) };
                black_box(ws[68])
            })
        });
        g.bench_function(BenchmarkId::new(crate::AWS_LC, 32), |b| {
            b.iter(|| {
                unsafe { vg_tmp_s2n_inv(z.as_mut_ptr(), black_box(&x).as_ptr()) };
                black_box(z[0])
            })
        });
        g.finish();
        let mut g = c.benchmark_group("x25519_ds590");
        let mut st = [1u64, 0x1234_5678_9abc_def1, 0x0fed_cba9_8765_4321];
        g.bench_function(BenchmarkId::new(crate::VG, 32), |b| {
            b.iter(|| {
                unsafe { vg_tmp_our_ds(black_box(&mut st).as_mut_ptr()) };
                black_box(st[0])
            })
        });
        g.bench_function(BenchmarkId::new(crate::AWS_LC, 32), |b| {
            b.iter(|| {
                unsafe { vg_tmp_s2n_ds(black_box(&mut st).as_mut_ptr()) };
                black_box(st[0])
            })
        });
        g.finish();
    }
}
