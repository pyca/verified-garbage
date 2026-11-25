//! ML-KEM-768: the benchmarks of `mlkem.rs`.

use criterion::Criterion;

pub const USES: &[&str] = &["mlkem768", "mlkem_common", "mlkem", "sha3"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
))]
pub fn bench(c: &mut Criterion) {
    #[cfg(target_arch = "aarch64")]
    ntt_variants::bench(c);
    crate::mlkem::mlkem_bench!(
        c,
        verified_garbage::mlkem768,
        DecapsulationKey768,
        EncapsulationKey768,
        ML_KEM_768,
        ML_KEM_768
    );
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
)))]
pub fn bench(_: &mut Criterion) {}

#[cfg(target_arch = "aarch64")]
mod ntt_variants {
    core::arch::global_asm!(include_str!("b_ls.s"));
    core::arch::global_asm!(include_str!("b_a1.s"));
    core::arch::global_asm!(include_str!("b_a2.s"));
    core::arch::global_asm!(include_str!("b_a3.s"));
    core::arch::global_asm!(include_str!("b_b2.s"));
    core::arch::global_asm!(include_str!("b_b3.s"));
    core::arch::global_asm!(include_str!("b_c2.s"));
    unsafe extern "C" {
        fn cr_fwd_ls(p: *mut i16, w: *mut i16);
        fn cr_fwd_a1(p: *mut i16, w: *mut i16);
        fn cr_fwd_a2(p: *mut i16, w: *mut i16);
        fn cr_fwd_a3(p: *mut i16, w: *mut i16);
        fn cr_fwd_b2(p: *mut i16, w: *mut i16);
        fn cr_fwd_b3(p: *mut i16, w: *mut i16);
        fn cr_fwd_c2(p: *mut i16, w: *mut i16);
        fn cr_inv_ls(p: *mut i16, w: *mut i16);
        fn cr_inv_a1(p: *mut i16, w: *mut i16);
        fn cr_inv_a2(p: *mut i16, w: *mut i16);
        fn cr_inv_a3(p: *mut i16, w: *mut i16);
        fn cr_inv_b2(p: *mut i16, w: *mut i16);
        fn cr_inv_b3(p: *mut i16, w: *mut i16);
        fn cr_inv_c2(p: *mut i16, w: *mut i16);
    }
    type F = unsafe extern "C" fn(*mut i16, *mut i16);
    #[repr(align(64))]
    struct A([i16; 256], [i16; 256]);
    pub fn bench(c: &mut criterion::Criterion) {
        let old: [F; 2] = unsafe {
            [
                core::mem::transmute::<unsafe extern "C" fn(), F>(verified_garbage::ntt_hook::fwd),
                core::mem::transmute::<unsafe extern "C" fn(), F>(verified_garbage::ntt_hook::inv),
            ]
        };
        let v: [(&str, [F; 8]); 2] = [
            ("cr-fwd", [old[0], cr_fwd_ls, cr_fwd_a1, cr_fwd_a2, cr_fwd_a3, cr_fwd_b2, cr_fwd_b3, cr_fwd_c2]),
            ("cr-inv", [old[1], cr_inv_ls, cr_inv_a1, cr_inv_a2, cr_inv_a3, cr_inv_b2, cr_inv_b3, cr_inv_c2]),
        ];
        for (name, fs) in v {
            let mut g = c.benchmark_group(name);
            for (i, f) in fs.iter().enumerate() {
                let mut a = A([0; 256], [0; 256]);
                for k in 0..256 {
                    a.0[k] = (k as i16 * 13) % 3329;
                }
                let r: [i16; 256] = {
                    let mut b = A(a.0, [0; 256]);
                    unsafe { fs[0](b.0.as_mut_ptr(), b.1.as_mut_ptr()) };
                    b.0
                };
                {
                    let mut b = A(a.0, [0; 256]);
                    unsafe { f(b.0.as_mut_ptr(), b.1.as_mut_ptr()) };
                    assert_eq!(b.0, r);
                }
                g.bench_function(criterion::BenchmarkId::new("verified-garbage", i), |b| {
                    b.iter(|| unsafe { f(a.0.as_mut_ptr(), a.1.as_mut_ptr()) })
                });
            }
            g.finish();
        }
    }
}
