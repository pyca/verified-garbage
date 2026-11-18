// PROTOTYPE (bench/ only): hand-edited, unproven.
//! The internal function `vg_ghash` for `riscv64`, whose text is in
//! `assembly/internal/vg_ghash.s`.
#![allow(dead_code)]

/// An internal function of the verified functions of this crate (`VG.Rust.Internal`): code that they call, which is not itself an artifact. It has no contract of its own: the proof of each function that calls it covers its code, which the model runs for the call (`Code.call`), and the emitter checks that every call of it is of this code.
///
/// # Safety
///
/// * Only the verified functions of this crate may call it, as their code does: it is not visible outside the crate.
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_ghash() {
    core::arch::naked_asm!(
        r#".option push
.option arch, +m, +c
beqz a3, 20f
addi sp, sp, -2032
addi sp, sp, -16
addi t0, sp, 0
sd s0, 320(t0)
sd s1, 328(t0)
sd s2, 336(t0)
sd s3, 344(t0)
sd s4, 352(t0)
sd s5, 360(t0)
sd s6, 368(t0)
sd s7, 376(t0)
sd s8, 384(t0)
sd s9, 392(t0)
addi s9, sp, 0
lui s0, 69905
addi s0, s0, 273
slli a7, s0, 32
or s0, s0, a7
slli s1, s0, 1
slli s2, s0, 2
slli s3, s0, 3
lbu a4, 0(a1)
slli a4, a4, 8
lbu t2, 1(a1)
or a4, a4, t2
slli a4, a4, 8
lbu t2, 2(a1)
or a4, a4, t2
slli a4, a4, 8
lbu t2, 3(a1)
or a4, a4, t2
slli a4, a4, 8
lbu t2, 4(a1)
or a4, a4, t2
slli a4, a4, 8
lbu t2, 5(a1)
or a4, a4, t2
slli a4, a4, 8
lbu t2, 6(a1)
or a4, a4, t2
slli a4, a4, 8
lbu t2, 7(a1)
or a4, a4, t2
lbu a5, 8(a1)
slli a5, a5, 8
lbu t2, 9(a1)
or a5, a5, t2
slli a5, a5, 8
lbu t2, 10(a1)
or a5, a5, t2
slli a5, a5, 8
lbu t2, 11(a1)
or a5, a5, t2
slli a5, a5, 8
lbu t2, 12(a1)
or a5, a5, t2
slli a5, a5, 8
lbu t2, 13(a1)
or a5, a5, t2
slli a5, a5, 8
lbu t2, 14(a1)
or a5, a5, t2
slli a5, a5, 8
lbu t2, 15(a1)
or a5, a5, t2
22:
lbu t0, 0(a2)
slli t0, t0, 8
lbu t2, 1(a2)
or t0, t0, t2
slli t0, t0, 8
lbu t2, 2(a2)
or t0, t0, t2
slli t0, t0, 8
lbu t2, 3(a2)
or t0, t0, t2
slli t0, t0, 8
lbu t2, 4(a2)
or t0, t0, t2
slli t0, t0, 8
lbu t2, 5(a2)
or t0, t0, t2
slli t0, t0, 8
lbu t2, 6(a2)
or t0, t0, t2
slli t0, t0, 8
lbu t2, 7(a2)
or t0, t0, t2
lbu t1, 8(a2)
slli t1, t1, 8
lbu t2, 9(a2)
or t1, t1, t2
slli t1, t1, 8
lbu t2, 10(a2)
or t1, t1, t2
slli t1, t1, 8
lbu t2, 11(a2)
or t1, t1, t2
slli t1, t1, 8
lbu t2, 12(a2)
or t1, t1, t2
slli t1, t1, 8
lbu t2, 13(a2)
or t1, t1, t2
slli t1, t1, 8
lbu t2, 14(a2)
or t1, t1, t2
slli t1, t1, 8
lbu t2, 15(a2)
or t1, t1, t2
xor a4, a4, t0
xor a5, a5, t1
srli s5, a4, 32
slli s4, a4, 32
srli s4, s4, 32
and t0, s4, s0
and t1, s4, s1
and t2, s4, s2
and t3, s4, s3
ld a6, 0(s9)
mul t4, t0, a6
mul t5, t1, a6
mul t6, t2, a6
mul s8, t3, a6
ld a6, 8(s9)
mul a7, t0, a6
xor t5, t5, a7
mul a7, t1, a6
xor t6, t6, a7
mul a7, t2, a6
xor s8, s8, a7
mul a7, t3, a6
xor t4, t4, a7
ld a6, 16(s9)
mul a7, t0, a6
xor t6, t6, a7
mul a7, t1, a6
xor s8, s8, a7
mul a7, t2, a6
xor t4, t4, a7
mul a7, t3, a6
xor t5, t5, a7
ld a6, 24(s9)
mul a7, t0, a6
xor s8, s8, a7
mul a7, t1, a6
xor t4, t4, a7
mul a7, t2, a6
xor t5, t5, a7
mul a7, t3, a6
xor t6, t6, a7
and t4, t4, s0
and t5, t5, s1
and t6, t6, s2
and s8, s8, s3
or t4, t4, t5
or t4, t4, t6
or t4, t4, s8
addi s6, t4, 0
xor s4, s4, s5
and t0, s4, s0
and t1, s4, s1
and t2, s4, s2
and t3, s4, s3
ld a6, 64(s9)
mul t4, t0, a6
mul t5, t1, a6
mul t6, t2, a6
mul s8, t3, a6
ld a6, 72(s9)
mul a7, t0, a6
xor t5, t5, a7
mul a7, t1, a6
xor t6, t6, a7
mul a7, t2, a6
xor s8, s8, a7
mul a7, t3, a6
xor t4, t4, a7
ld a6, 80(s9)
mul a7, t0, a6
xor t6, t6, a7
mul a7, t1, a6
xor s8, s8, a7
mul a7, t2, a6
xor t4, t4, a7
mul a7, t3, a6
xor t5, t5, a7
ld a6, 88(s9)
mul a7, t0, a6
xor s8, s8, a7
mul a7, t1, a6
xor t4, t4, a7
mul a7, t2, a6
xor t5, t5, a7
mul a7, t3, a6
xor t6, t6, a7
and t4, t4, s0
and t5, t5, s1
and t6, t6, s2
and s8, s8, s3
or t4, t4, t5
or t4, t4, t6
or t4, t4, s8
addi s7, t4, 0
addi s4, s5, 0
and t0, s4, s0
and t1, s4, s1
and t2, s4, s2
and t3, s4, s3
ld a6, 32(s9)
mul t4, t0, a6
mul t5, t1, a6
mul t6, t2, a6
mul s8, t3, a6
ld a6, 40(s9)
mul a7, t0, a6
xor t5, t5, a7
mul a7, t1, a6
xor t6, t6, a7
mul a7, t2, a6
xor s8, s8, a7
mul a7, t3, a6
xor t4, t4, a7
ld a6, 48(s9)
mul a7, t0, a6
xor t6, t6, a7
mul a7, t1, a6
xor s8, s8, a7
mul a7, t2, a6
xor t4, t4, a7
mul a7, t3, a6
xor t5, t5, a7
ld a6, 56(s9)
mul a7, t0, a6
xor s8, s8, a7
mul a7, t1, a6
xor t4, t4, a7
mul a7, t2, a6
xor t5, t5, a7
mul a7, t3, a6
xor t6, t6, a7
and t4, t4, s0
and t5, t5, s1
and t6, t6, s2
and s8, s8, s3
or t4, t4, t5
or t4, t4, t6
or t4, t4, s8
xor s7, s7, s6
xor s7, s7, t4
slli a7, s7, 32
xor s6, s6, a7
srli a7, s7, 32
xor t4, t4, a7
sd s6, 288(s9)
sd t4, 296(s9)
srli s5, a5, 32
slli s4, a5, 32
srli s4, s4, 32
and t0, s4, s0
and t1, s4, s1
and t2, s4, s2
and t3, s4, s3
ld a6, 96(s9)
mul t4, t0, a6
mul t5, t1, a6
mul t6, t2, a6
mul s8, t3, a6
ld a6, 104(s9)
mul a7, t0, a6
xor t5, t5, a7
mul a7, t1, a6
xor t6, t6, a7
mul a7, t2, a6
xor s8, s8, a7
mul a7, t3, a6
xor t4, t4, a7
ld a6, 112(s9)
mul a7, t0, a6
xor t6, t6, a7
mul a7, t1, a6
xor s8, s8, a7
mul a7, t2, a6
xor t4, t4, a7
mul a7, t3, a6
xor t5, t5, a7
ld a6, 120(s9)
mul a7, t0, a6
xor s8, s8, a7
mul a7, t1, a6
xor t4, t4, a7
mul a7, t2, a6
xor t5, t5, a7
mul a7, t3, a6
xor t6, t6, a7
and t4, t4, s0
and t5, t5, s1
and t6, t6, s2
and s8, s8, s3
or t4, t4, t5
or t4, t4, t6
or t4, t4, s8
addi s6, t4, 0
xor s4, s4, s5
and t0, s4, s0
and t1, s4, s1
and t2, s4, s2
and t3, s4, s3
ld a6, 160(s9)
mul t4, t0, a6
mul t5, t1, a6
mul t6, t2, a6
mul s8, t3, a6
ld a6, 168(s9)
mul a7, t0, a6
xor t5, t5, a7
mul a7, t1, a6
xor t6, t6, a7
mul a7, t2, a6
xor s8, s8, a7
mul a7, t3, a6
xor t4, t4, a7
ld a6, 176(s9)
mul a7, t0, a6
xor t6, t6, a7
mul a7, t1, a6
xor s8, s8, a7
mul a7, t2, a6
xor t4, t4, a7
mul a7, t3, a6
xor t5, t5, a7
ld a6, 184(s9)
mul a7, t0, a6
xor s8, s8, a7
mul a7, t1, a6
xor t4, t4, a7
mul a7, t2, a6
xor t5, t5, a7
mul a7, t3, a6
xor t6, t6, a7
and t4, t4, s0
and t5, t5, s1
and t6, t6, s2
and s8, s8, s3
or t4, t4, t5
or t4, t4, t6
or t4, t4, s8
addi s7, t4, 0
addi s4, s5, 0
and t0, s4, s0
and t1, s4, s1
and t2, s4, s2
and t3, s4, s3
ld a6, 128(s9)
mul t4, t0, a6
mul t5, t1, a6
mul t6, t2, a6
mul s8, t3, a6
ld a6, 136(s9)
mul a7, t0, a6
xor t5, t5, a7
mul a7, t1, a6
xor t6, t6, a7
mul a7, t2, a6
xor s8, s8, a7
mul a7, t3, a6
xor t4, t4, a7
ld a6, 144(s9)
mul a7, t0, a6
xor t6, t6, a7
mul a7, t1, a6
xor s8, s8, a7
mul a7, t2, a6
xor t4, t4, a7
mul a7, t3, a6
xor t5, t5, a7
ld a6, 152(s9)
mul a7, t0, a6
xor s8, s8, a7
mul a7, t1, a6
xor t4, t4, a7
mul a7, t2, a6
xor t5, t5, a7
mul a7, t3, a6
xor t6, t6, a7
and t4, t4, s0
and t5, t5, s1
and t6, t6, s2
and s8, s8, s3
or t4, t4, t5
or t4, t4, t6
or t4, t4, s8
xor s7, s7, s6
xor s7, s7, t4
slli a7, s7, 32
xor s6, s6, a7
srli a7, s7, 32
xor t4, t4, a7
sd s6, 304(s9)
sd t4, 312(s9)
xor a4, a4, a5
srli s5, a4, 32
slli s4, a4, 32
srli s4, s4, 32
and t0, s4, s0
and t1, s4, s1
and t2, s4, s2
and t3, s4, s3
ld a6, 192(s9)
mul t4, t0, a6
mul t5, t1, a6
mul t6, t2, a6
mul s8, t3, a6
ld a6, 200(s9)
mul a7, t0, a6
xor t5, t5, a7
mul a7, t1, a6
xor t6, t6, a7
mul a7, t2, a6
xor s8, s8, a7
mul a7, t3, a6
xor t4, t4, a7
ld a6, 208(s9)
mul a7, t0, a6
xor t6, t6, a7
mul a7, t1, a6
xor s8, s8, a7
mul a7, t2, a6
xor t4, t4, a7
mul a7, t3, a6
xor t5, t5, a7
ld a6, 216(s9)
mul a7, t0, a6
xor s8, s8, a7
mul a7, t1, a6
xor t4, t4, a7
mul a7, t2, a6
xor t5, t5, a7
mul a7, t3, a6
xor t6, t6, a7
and t4, t4, s0
and t5, t5, s1
and t6, t6, s2
and s8, s8, s3
or t4, t4, t5
or t4, t4, t6
or t4, t4, s8
addi s6, t4, 0
xor s4, s4, s5
and t0, s4, s0
and t1, s4, s1
and t2, s4, s2
and t3, s4, s3
ld a6, 256(s9)
mul t4, t0, a6
mul t5, t1, a6
mul t6, t2, a6
mul s8, t3, a6
ld a6, 264(s9)
mul a7, t0, a6
xor t5, t5, a7
mul a7, t1, a6
xor t6, t6, a7
mul a7, t2, a6
xor s8, s8, a7
mul a7, t3, a6
xor t4, t4, a7
ld a6, 272(s9)
mul a7, t0, a6
xor t6, t6, a7
mul a7, t1, a6
xor s8, s8, a7
mul a7, t2, a6
xor t4, t4, a7
mul a7, t3, a6
xor t5, t5, a7
ld a6, 280(s9)
mul a7, t0, a6
xor s8, s8, a7
mul a7, t1, a6
xor t4, t4, a7
mul a7, t2, a6
xor t5, t5, a7
mul a7, t3, a6
xor t6, t6, a7
and t4, t4, s0
and t5, t5, s1
and t6, t6, s2
and s8, s8, s3
or t4, t4, t5
or t4, t4, t6
or t4, t4, s8
addi s7, t4, 0
addi s4, s5, 0
and t0, s4, s0
and t1, s4, s1
and t2, s4, s2
and t3, s4, s3
ld a6, 224(s9)
mul t4, t0, a6
mul t5, t1, a6
mul t6, t2, a6
mul s8, t3, a6
ld a6, 232(s9)
mul a7, t0, a6
xor t5, t5, a7
mul a7, t1, a6
xor t6, t6, a7
mul a7, t2, a6
xor s8, s8, a7
mul a7, t3, a6
xor t4, t4, a7
ld a6, 240(s9)
mul a7, t0, a6
xor t6, t6, a7
mul a7, t1, a6
xor s8, s8, a7
mul a7, t2, a6
xor t4, t4, a7
mul a7, t3, a6
xor t5, t5, a7
ld a6, 248(s9)
mul a7, t0, a6
xor s8, s8, a7
mul a7, t1, a6
xor t4, t4, a7
mul a7, t2, a6
xor t5, t5, a7
mul a7, t3, a6
xor t6, t6, a7
and t4, t4, s0
and t5, t5, s1
and t6, t6, s2
and s8, s8, s3
or t4, t4, t5
or t4, t4, t6
or t4, t4, s8
xor s7, s7, s6
xor s7, s7, t4
slli a7, s7, 32
xor s6, s6, a7
srli a7, s7, 32
xor t4, t4, a7
ld t0, 288(s9)
ld t1, 296(s9)
ld t2, 304(s9)
ld t3, 312(s9)
xor a6, t4, t1
xor a6, a6, t3
xor a6, t0, a6
xor a7, s6, t0
xor a7, a7, t2
xor a7, a7, t3
slli t4, t2, 63
xor a7, a7, t4
slli t4, t2, 62
xor a7, a7, t4
slli t4, t2, 57
xor a7, a7, t4
xor a6, a6, t2
srli t4, t2, 1
xor a6, a6, t4
srli t4, t2, 2
xor a6, a6, t4
srli t4, t2, 7
xor a6, a6, t4
xor a4, t1, a7
srli t4, a7, 1
xor a4, a4, t4
srli t4, a7, 2
xor a4, a4, t4
srli t4, a7, 7
xor a4, a4, t4
slli t4, a7, 63
xor a5, a6, t4
slli t4, a7, 62
xor a5, a5, t4
slli t4, a7, 57
xor a5, a5, t4
addi a2, a2, 16
addi a3, a3, -1
bnez a3, 22b
srli t2, a4, 56
sb t2, 0(a1)
srli t2, a4, 48
sb t2, 1(a1)
srli t2, a4, 40
sb t2, 2(a1)
srli t2, a4, 32
sb t2, 3(a1)
srli t2, a4, 24
sb t2, 4(a1)
srli t2, a4, 16
sb t2, 5(a1)
srli t2, a4, 8
sb t2, 6(a1)
srli t2, a4, 0
sb t2, 7(a1)
srli t2, a5, 56
sb t2, 8(a1)
srli t2, a5, 48
sb t2, 9(a1)
srli t2, a5, 40
sb t2, 10(a1)
srli t2, a5, 32
sb t2, 11(a1)
srli t2, a5, 24
sb t2, 12(a1)
srli t2, a5, 16
sb t2, 13(a1)
srli t2, a5, 8
sb t2, 14(a1)
srli t2, a5, 0
sb t2, 15(a1)
addi t0, sp, 0
ld s0, 320(t0)
ld s1, 328(t0)
ld s2, 336(t0)
ld s3, 344(t0)
ld s4, 352(t0)
ld s5, 360(t0)
ld s6, 368(t0)
ld s7, 376(t0)
ld s8, 384(t0)
ld s9, 392(t0)
addi t5, sp, 0
addi t6, zero, 0
sd t6, 0(t5)
sd t6, 8(t5)
sd t6, 16(t5)
sd t6, 24(t5)
sd t6, 32(t5)
sd t6, 40(t5)
sd t6, 48(t5)
sd t6, 56(t5)
sd t6, 64(t5)
sd t6, 72(t5)
sd t6, 80(t5)
sd t6, 88(t5)
sd t6, 96(t5)
sd t6, 104(t5)
sd t6, 112(t5)
sd t6, 120(t5)
sd t6, 128(t5)
sd t6, 136(t5)
sd t6, 144(t5)
sd t6, 152(t5)
sd t6, 160(t5)
sd t6, 168(t5)
sd t6, 176(t5)
sd t6, 184(t5)
sd t6, 192(t5)
sd t6, 200(t5)
sd t6, 208(t5)
sd t6, 216(t5)
sd t6, 224(t5)
sd t6, 232(t5)
sd t6, 240(t5)
sd t6, 248(t5)
sd t6, 256(t5)
sd t6, 264(t5)
sd t6, 272(t5)
sd t6, 280(t5)
sd t6, 288(t5)
sd t6, 296(t5)
sd t6, 304(t5)
sd t6, 312(t5)
sd t6, 320(t5)
sd t6, 328(t5)
sd t6, 336(t5)
sd t6, 344(t5)
sd t6, 352(t5)
sd t6, 360(t5)
sd t6, 368(t5)
sd t6, 376(t5)
sd t6, 384(t5)
sd t6, 392(t5)
addi sp, sp, 16
addi sp, sp, 2032
j 21f
20:
21:
ret
.option pop"#,
    )
}
