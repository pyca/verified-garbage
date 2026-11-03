//! Prototype check (bench branch only): Proto18's microbenchmark loops run and return.
#![cfg(target_arch = "riscv64")]
use verified_garbage_asm_riscv64::rsa_proto18 as p18;

#[test]
fn p18_runs() {
    let fs: [unsafe extern "C" fn(usize); 12] = [
        p18::vg_p18_add8,
        p18::vg_p18_mul_ind,
        p18::vg_p18_mulhu_ind,
        p18::vg_p18_alt_ind,
        p18::vg_p18_pair_ind,
        p18::vg_p18_mul_acc4,
        p18::vg_p18_mul_acc8,
        p18::vg_p18_mulhu_acc4,
        p18::vg_p18_mulhu_acc8,
        p18::vg_p18_mul_dep,
        p18::vg_p18_mulhu_dep,
        p18::vg_p18_mix_1to3,
    ];
    for f in fs {
        unsafe { f(3) };
    }
}
