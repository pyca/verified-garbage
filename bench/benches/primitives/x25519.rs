//! X25519.

use criterion::Criterion;

pub const USES: &[&str] = &["x25519"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use aws_lc_rs::agreement::{self, UnparsedPublicKey};
    use aws_lc_rs::encoding::{AsBigEndian, Curve25519SeedBin};
    use aws_lc_rs::error::Unspecified;
    use criterion::BenchmarkId;
    use openssl::derive::Deriver;
    use openssl::pkey::{Id, PKey};
    use verified_garbage::x25519::PrivateKey;

    use crate::{AWS_LC, BenchDyn, OPENSSL, VG, fixed_tape};
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
    let peer_bytes = *peer.as_bytes();
    assert_eq!(
        aws_lc_agree(&aws_lc_private, &peer_bytes),
        vg_private.exchange(&peer).unwrap()
    );
    assert_eq!(
        aws_lc_private.compute_public_key().unwrap().as_ref(),
        vg_private.public_key().as_bytes()
    );
    let mut g = c.benchmark_group("x25519");
    // One Diffie-Hellman: a shared secret from a private key and the peer's
    // public key. The ids' size is the bytes of the shared secret.
    g.bench(BenchmarkId::new(VG, 32), |b| {
        b.iter(|| black_box(&vg_private).exchange(black_box(&peer)).unwrap())
    });
    g.bench(BenchmarkId::new(OPENSSL, 32), |b| {
        b.iter(|| {
            let peer = PKey::public_key_from_raw_bytes(black_box(&peer_bytes), Id::X25519).unwrap();
            let mut d = Deriver::new(black_box(&openssl_private)).unwrap();
            d.set_peer(&peer).unwrap();
            d.derive_to_vec().unwrap()
        })
    });
    g.bench(BenchmarkId::new(AWS_LC, 32), |b| {
        b.iter(|| aws_lc_agree(black_box(&aws_lc_private), black_box(&peer_bytes)))
    });
    probes(&mut g);
    g.finish();

    let mut g = c.benchmark_group("x25519_public_key");
    g.bench(BenchmarkId::new(VG, 32), |b| {
        b.iter(|| PrivateKey::from_bytes(black_box(&private)).public_key())
    });
    g.bench(BenchmarkId::new(OPENSSL, 32), |b| {
        b.iter(|| {
            PKey::private_key_from_raw_bytes(black_box(&private), Id::X25519)
                .unwrap()
                .raw_public_key()
                .unwrap()
        })
    });
    g.bench(BenchmarkId::new(AWS_LC, 32), |b| {
        b.iter(|| {
            agreement::PrivateKey::from_private_key(&agreement::X25519, black_box(&private))
                .unwrap()
                .compute_public_key()
                .unwrap()
        })
    });
    g.finish();

    // A new key pair: a private key and its public key, which OpenSSL's and
    // aws-lc-rs's key generation always derive. verified-garbage's private
    // key is from a fixed tape (`PrivateKey::generate` but for `getrandom`);
    // the others draw from their own generators.
    let mut g = c.benchmark_group("x25519_generate");
    g.bench(BenchmarkId::new(VG, 32), |b| {
        b.iter(|| {
            let mut bytes = [0; 32];
            fixed_tape(32)(&mut bytes);
            let key = PrivateKey::from_bytes(&bytes);
            (*key.as_bytes(), key.public_key())
        })
    });
    g.bench(BenchmarkId::new(OPENSSL, 32), |b| {
        b.iter(|| {
            let key = PKey::generate_x25519().unwrap();
            (
                key.raw_private_key().unwrap(),
                key.raw_public_key().unwrap(),
            )
        })
    });
    g.bench(BenchmarkId::new(AWS_LC, 32), |b| {
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
    target_arch = "aarch64",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
)))]
pub fn bench(_: &mut Criterion) {}

// Measurement only, not for merging: probes of the CPU's instruction costs,
// each 2000 iterations of eight instructions.
#[cfg(all(target_arch = "powerpc64", target_endian = "little"))]
core::arch::global_asm!(
    r#"
.text
.globl vg_probe_1
.type vg_probe_1,@function
vg_probe_1:
	mr %r4, %r3
	li %r3, 2000
	mtctr %r3
	li %r11, 12345
	li %r12, 6789
	li %r5, 3
1:
	mulld %r5, %r11, %r12
	mulld %r6, %r11, %r12
	mulld %r7, %r11, %r12
	mulld %r8, %r11, %r12
	mulld %r9, %r11, %r12
	mulld %r10, %r11, %r12
	mulld %r0, %r11, %r12
	mulld %r3, %r11, %r12
	bdnz 1b
	blr
.globl vg_probe_2
.type vg_probe_2,@function
vg_probe_2:
	mr %r4, %r3
	li %r3, 2000
	mtctr %r3
	li %r11, 12345
	li %r12, 6789
	li %r5, 3
1:
	mulhdu %r5, %r11, %r12
	mulhdu %r6, %r11, %r12
	mulhdu %r7, %r11, %r12
	mulhdu %r8, %r11, %r12
	mulhdu %r9, %r11, %r12
	mulhdu %r10, %r11, %r12
	mulhdu %r0, %r11, %r12
	mulhdu %r3, %r11, %r12
	bdnz 1b
	blr
.globl vg_probe_3
.type vg_probe_3,@function
vg_probe_3:
	mr %r4, %r3
	li %r3, 2000
	mtctr %r3
	li %r11, 12345
	li %r12, 6789
	li %r5, 3
1:
	add %r5, %r11, %r12
	add %r6, %r11, %r12
	add %r7, %r11, %r12
	add %r8, %r11, %r12
	add %r9, %r11, %r12
	add %r10, %r11, %r12
	add %r0, %r11, %r12
	add %r3, %r11, %r12
	bdnz 1b
	blr
.globl vg_probe_4
.type vg_probe_4,@function
vg_probe_4:
	mr %r4, %r3
	li %r3, 2000
	mtctr %r3
	li %r11, 12345
	li %r12, 6789
	li %r5, 3
1:
	addc %r5, %r11, %r12
	addc %r6, %r11, %r12
	addc %r7, %r11, %r12
	addc %r8, %r11, %r12
	addc %r9, %r11, %r12
	addc %r10, %r11, %r12
	addc %r0, %r11, %r12
	addc %r3, %r11, %r12
	bdnz 1b
	blr
.globl vg_probe_5
.type vg_probe_5,@function
vg_probe_5:
	mr %r4, %r3
	li %r3, 2000
	mtctr %r3
	li %r11, 12345
	li %r12, 6789
	li %r5, 3
1:
	addc %r5, %r11, %r12
	adde %r6, %r11, %r12
	addc %r7, %r11, %r12
	adde %r8, %r11, %r12
	addc %r9, %r11, %r12
	adde %r10, %r11, %r12
	addc %r0, %r11, %r12
	adde %r3, %r11, %r12
	bdnz 1b
	blr
.globl vg_probe_6
.type vg_probe_6,@function
vg_probe_6:
	mr %r4, %r3
	li %r3, 2000
	mtctr %r3
	li %r11, 12345
	li %r12, 6789
	li %r5, 3
1:
	addc %r5, %r11, %r12
	adde %r6, %r11, %r12
	adde %r7, %r11, %r12
	adde %r8, %r11, %r12
	adde %r9, %r11, %r12
	adde %r10, %r11, %r12
	adde %r0, %r11, %r12
	adde %r3, %r11, %r12
	bdnz 1b
	blr
.globl vg_probe_7
.type vg_probe_7,@function
vg_probe_7:
	mr %r4, %r3
	li %r3, 2000
	mtctr %r3
	li %r11, 12345
	li %r12, 6789
	li %r5, 3
1:
	mulld %r5, %r11, %r12
	mulhdu %r6, %r11, %r12
	mulld %r7, %r11, %r12
	mulhdu %r8, %r11, %r12
	mulld %r9, %r11, %r12
	mulhdu %r10, %r11, %r12
	mulld %r0, %r11, %r12
	mulhdu %r3, %r11, %r12
	bdnz 1b
	blr
.globl vg_probe_8
.type vg_probe_8,@function
vg_probe_8:
	mr %r4, %r3
	li %r3, 2000
	mtctr %r3
	li %r11, 12345
	li %r12, 6789
	li %r5, 3
1:

	bdnz 1b
	blr
.globl vg_probe_9
.type vg_probe_9,@function
vg_probe_9:
	mr %r4, %r3
	li %r3, 2000
	mtctr %r3
	li %r11, 12345
	li %r12, 6789
	li %r5, 3
1:
	add %r5, %r5, %r12
	add %r5, %r5, %r12
	add %r5, %r5, %r12
	add %r5, %r5, %r12
	add %r5, %r5, %r12
	add %r5, %r5, %r12
	add %r5, %r5, %r12
	add %r5, %r5, %r12
	bdnz 1b
	blr
.globl vg_probe_10
.type vg_probe_10,@function
vg_probe_10:
	mr %r4, %r3
	li %r3, 2000
	mtctr %r3
	li %r11, 12345
	li %r12, 6789
	li %r5, 3
1:
	mulld %r5, %r5, %r12
	mulld %r5, %r5, %r12
	mulld %r5, %r5, %r12
	mulld %r5, %r5, %r12
	mulld %r5, %r5, %r12
	mulld %r5, %r5, %r12
	mulld %r5, %r5, %r12
	mulld %r5, %r5, %r12
	bdnz 1b
	blr
.globl vg_probe_11
.type vg_probe_11,@function
vg_probe_11:
	mr %r4, %r3
	li %r3, 2000
	mtctr %r3
	li %r11, 12345
	li %r12, 6789
	li %r5, 3
1:
	ld %r5, 0(%r4)
	ld %r6, 8(%r4)
	ld %r7, 16(%r4)
	ld %r8, 24(%r4)
	ld %r9, 32(%r4)
	ld %r10, 40(%r4)
	ld %r0, 48(%r4)
	ld %r3, 56(%r4)
	bdnz 1b
	blr
.globl vg_probe_12
.type vg_probe_12,@function
vg_probe_12:
	mr %r4, %r3
	li %r3, 2000
	mtctr %r3
	li %r11, 12345
	li %r12, 6789
	li %r5, 3
1:
	std %r11, 0(%r4)
	ld %r5, 0(%r4)
	std %r11, 8(%r4)
	ld %r6, 8(%r4)
	std %r11, 16(%r4)
	ld %r7, 16(%r4)
	std %r11, 24(%r4)
	ld %r8, 24(%r4)
	bdnz 1b
	blr
.globl vg_probe_13
.type vg_probe_13,@function
vg_probe_13:
	mr %r4, %r3
	li %r3, 2000
	mtctr %r3
	li %r11, 12345
	li %r12, 6789
	li %r5, 3
1:
	std %r5, 0(%r4)
	ld %r5, 0(%r4)
	std %r5, 0(%r4)
	ld %r5, 0(%r4)
	std %r5, 0(%r4)
	ld %r5, 0(%r4)
	std %r5, 0(%r4)
	ld %r5, 0(%r4)
	bdnz 1b
	blr
.globl vg_probe_14
.type vg_probe_14,@function
vg_probe_14:
	mr %r4, %r3
	li %r3, 2000
	mtctr %r3
	li %r11, 12345
	li %r12, 6789
	li %r5, 3
1:
	addze %r5, %r11
	addze %r6, %r11
	addze %r7, %r11
	addze %r8, %r11
	addze %r9, %r11
	addze %r10, %r11
	addze %r0, %r11
	addze %r3, %r11
	bdnz 1b
	blr
.globl vg_probe_15
.type vg_probe_15,@function
vg_probe_15:
	mr %r4, %r3
	li %r3, 2000
	mtctr %r3
	li %r11, 12345
	li %r12, 6789
	li %r5, 3
1:
	mulld %r5, %r11, %r12
	srdi %r5, %r5, 13
	add %r9, %r9, %r5
	mulhdu %r5, %r11, %r12
	mulld %r6, %r11, %r12
	srdi %r6, %r6, 13
	add %r10, %r10, %r6
	mulhdu %r6, %r11, %r12
	bdnz 1b
	blr
.globl vg_probe_16
.type vg_probe_16,@function
vg_probe_16:
	mr %r4, %r3
	li %r3, 2000
	mtctr %r3
	li %r11, 12345
	li %r12, 6789
	li %r5, 3
1:
	srdi %r5, %r11, 13
	srdi %r6, %r11, 13
	srdi %r7, %r11, 13
	srdi %r8, %r11, 13
	srdi %r9, %r11, 13
	srdi %r10, %r11, 13
	srdi %r0, %r11, 13
	srdi %r3, %r11, 13
	bdnz 1b
	blr
.globl vg_probe_17
.type vg_probe_17,@function
vg_probe_17:
	mr %r4, %r3
	li %r3, 2000
	mtctr %r3
	li %r11, 12345
	li %r12, 6789
	li %r5, 3
1:
	subfc %r5, %r11, %r12
	subfe %r6, %r11, %r12
	subfc %r7, %r11, %r12
	subfe %r8, %r11, %r12
	subfc %r9, %r11, %r12
	subfe %r10, %r11, %r12
	subfc %r0, %r11, %r12
	subfe %r3, %r11, %r12
	bdnz 1b
	blr
"#
);
#[cfg(all(target_arch = "powerpc64", target_endian = "little"))]
unsafe extern "C" {
    fn vg_probe_1(buf: *mut u64);
    fn vg_probe_2(buf: *mut u64);
    fn vg_probe_3(buf: *mut u64);
    fn vg_probe_4(buf: *mut u64);
    fn vg_probe_5(buf: *mut u64);
    fn vg_probe_6(buf: *mut u64);
    fn vg_probe_7(buf: *mut u64);
    fn vg_probe_8(buf: *mut u64);
    fn vg_probe_9(buf: *mut u64);
    fn vg_probe_10(buf: *mut u64);
    fn vg_probe_11(buf: *mut u64);
    fn vg_probe_12(buf: *mut u64);
    fn vg_probe_13(buf: *mut u64);
    fn vg_probe_14(buf: *mut u64);
    fn vg_probe_15(buf: *mut u64);
    fn vg_probe_16(buf: *mut u64);
    fn vg_probe_17(buf: *mut u64);
}
#[cfg(all(target_arch = "powerpc64", target_endian = "little"))]
fn probes(g: &mut criterion::BenchmarkGroup<'_, criterion::measurement::WallTime>) {
    use crate::BenchDyn;
    use criterion::BenchmarkId;
    let mut buf = [0u64; 16];
    g.bench(BenchmarkId::new(crate::VG, 1001), |b| {
        b.iter(|| unsafe { vg_probe_1(buf.as_mut_ptr()) })
    });
    g.bench(BenchmarkId::new(crate::VG, 1002), |b| {
        b.iter(|| unsafe { vg_probe_2(buf.as_mut_ptr()) })
    });
    g.bench(BenchmarkId::new(crate::VG, 1003), |b| {
        b.iter(|| unsafe { vg_probe_3(buf.as_mut_ptr()) })
    });
    g.bench(BenchmarkId::new(crate::VG, 1004), |b| {
        b.iter(|| unsafe { vg_probe_4(buf.as_mut_ptr()) })
    });
    g.bench(BenchmarkId::new(crate::VG, 1005), |b| {
        b.iter(|| unsafe { vg_probe_5(buf.as_mut_ptr()) })
    });
    g.bench(BenchmarkId::new(crate::VG, 1006), |b| {
        b.iter(|| unsafe { vg_probe_6(buf.as_mut_ptr()) })
    });
    g.bench(BenchmarkId::new(crate::VG, 1007), |b| {
        b.iter(|| unsafe { vg_probe_7(buf.as_mut_ptr()) })
    });
    g.bench(BenchmarkId::new(crate::VG, 1008), |b| {
        b.iter(|| unsafe { vg_probe_8(buf.as_mut_ptr()) })
    });
    g.bench(BenchmarkId::new(crate::VG, 1009), |b| {
        b.iter(|| unsafe { vg_probe_9(buf.as_mut_ptr()) })
    });
    g.bench(BenchmarkId::new(crate::VG, 1010), |b| {
        b.iter(|| unsafe { vg_probe_10(buf.as_mut_ptr()) })
    });
    g.bench(BenchmarkId::new(crate::VG, 1011), |b| {
        b.iter(|| unsafe { vg_probe_11(buf.as_mut_ptr()) })
    });
    g.bench(BenchmarkId::new(crate::VG, 1012), |b| {
        b.iter(|| unsafe { vg_probe_12(buf.as_mut_ptr()) })
    });
    g.bench(BenchmarkId::new(crate::VG, 1013), |b| {
        b.iter(|| unsafe { vg_probe_13(buf.as_mut_ptr()) })
    });
    g.bench(BenchmarkId::new(crate::VG, 1014), |b| {
        b.iter(|| unsafe { vg_probe_14(buf.as_mut_ptr()) })
    });
    g.bench(BenchmarkId::new(crate::VG, 1015), |b| {
        b.iter(|| unsafe { vg_probe_15(buf.as_mut_ptr()) })
    });
    g.bench(BenchmarkId::new(crate::VG, 1016), |b| {
        b.iter(|| unsafe { vg_probe_16(buf.as_mut_ptr()) })
    });
    g.bench(BenchmarkId::new(crate::VG, 1017), |b| {
        b.iter(|| unsafe { vg_probe_17(buf.as_mut_ptr()) })
    });
}
#[cfg(not(all(target_arch = "powerpc64", target_endian = "little")))]
fn probes(_: &mut criterion::BenchmarkGroup<'_, criterion::measurement::WallTime>) {}
