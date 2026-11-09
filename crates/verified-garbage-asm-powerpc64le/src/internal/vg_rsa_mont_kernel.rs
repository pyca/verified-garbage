// PROTOTYPE, hand-written and unverified: for a bench/ branch's Benchmarks runs only, never merged.
//! The internal function `vg_rsa_mont_kernel` for `powerpc64le`, whose text is in
//! `assembly/internal/vg_rsa_mont_kernel.s`.
#![allow(dead_code)]

/// An internal function of the verified functions of this crate (`VG.Rust.Internal`): code that they call, which is not itself an artifact. It has no contract of its own: the proof of each function that calls it covers its code, which the model runs for the call (`Code.call`), and the emitter checks that every call of it is of this code.
///
/// # Safety
///
/// * Only the verified functions of this crate may call it, as their code does: it is not visible outside the crate.
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_rsa_mont_kernel() {
    core::arch::naked_asm!(
        r#"addi %r12, %r3, 0
addi %r11, %r4, 0
sldi %r3, %r4, 2
add %r3, %r9, %r3
std %r14, 8(%r3)
ld %r3, 0(%r10)
mulld %r22, %r3, %r12
addi %r22, %r22, 2
mulld %r22, %r22, %r12
sldi %r14, %r11, 2
add %r14, %r14, %r8
std %r22, 8(%r14)
srdi %r4, %r11, 1
addi %r14, %r8, 0
addi %r17, %r4, 1
li %r3, 0
1:
std %r3, 0(%r14)
addi %r14, %r14, 8
addi %r17, %r17, -1
cmpldi %cr0, %r17, 0
bne %cr0, 1b
sldi %r9, %r11, 2
add %r16, %r10, %r9
add %r15, %r7, %r9
sldi %r17, %r4, 32
2:
subf %r9, %r10, %r16
addi %r16, %r10, 0
subf %r15, %r9, %r15
add %r3, %r9, %r9
add %r3, %r3, %r10
addi %r14, %r3, 32
add %r4, %r3, %r9
ld %r19, 40(%r4)
srdi %r7, %r9, 3
addi %r7, %r7, -1
srdi %r8, %r7, 2
add %r17, %r17, %r8
sldi %r9, %r7, 62
srdi %r9, %r9, 62
ld %r18, 0(%r6)
addi %r6, %r6, 8
ld %r3, 0(%r14)
ld %r0, 0(%r15)
mulhdu %r20, %r18, %r0
mulld %r0, %r18, %r0
addc %r3, %r3, %r0
subfe %r12, %r12, %r12
mulld %r19, %r19, %r3
ld %r0, 0(%r16)
mulhdu %r22, %r19, %r0
mulld %r0, %r19, %r0
addc %r3, %r3, %r0
subfe %r11, %r11, %r11
addi %r15, %r15, 8
addi %r16, %r16, 8
cmpldi %cr0, %r9, 0
beq %cr0, 30f
addi %r9, %r9, -1
cmpldi %cr0, %r9, 0
beq %cr0, 31f
addi %r9, %r9, -1
cmpldi %cr0, %r9, 0
beq %cr0, 32f
ld %r3, 8(%r14)
ld %r4, 16(%r14)
ld %r7, 24(%r14)
subfc %r12, %r12, %r10
ld %r9, 0(%r15)
mulld %r0, %r18, %r9
adde %r3, %r3, %r0
ld %r9, 8(%r15)
mulld %r0, %r18, %r9
adde %r4, %r4, %r0
ld %r9, 16(%r15)
mulld %r0, %r18, %r9
adde %r7, %r7, %r0
mulhdu %r9, %r18, %r9
subfe %r12, %r12, %r12
addc %r3, %r3, %r20
ld %r0, 0(%r15)
mulhdu %r0, %r18, %r0
adde %r4, %r4, %r0
ld %r0, 8(%r15)
mulhdu %r0, %r18, %r0
adde %r7, %r7, %r0
addze %r20, %r9
subfc %r11, %r11, %r10
ld %r9, 0(%r16)
mulld %r0, %r19, %r9
adde %r3, %r3, %r0
ld %r9, 8(%r16)
mulld %r0, %r19, %r9
adde %r4, %r4, %r0
ld %r9, 16(%r16)
mulld %r0, %r19, %r9
adde %r7, %r7, %r0
mulhdu %r9, %r19, %r9
subfe %r11, %r11, %r11
addc %r3, %r3, %r22
ld %r0, 0(%r16)
mulhdu %r0, %r19, %r0
adde %r4, %r4, %r0
ld %r0, 8(%r16)
mulhdu %r0, %r19, %r0
adde %r7, %r7, %r0
addze %r22, %r9
std %r3, 0(%r14)
std %r4, 8(%r14)
std %r7, 16(%r14)
addi %r14, %r14, 24
addi %r15, %r15, 24
addi %r16, %r16, 24
b 30f
31:
ld %r3, 8(%r14)
subfc %r12, %r12, %r10
ld %r9, 0(%r15)
mulld %r0, %r18, %r9
adde %r3, %r3, %r0
mulhdu %r9, %r18, %r9
subfe %r12, %r12, %r12
addc %r3, %r3, %r20
addze %r20, %r9
subfc %r11, %r11, %r10
ld %r9, 0(%r16)
mulld %r0, %r19, %r9
adde %r3, %r3, %r0
mulhdu %r9, %r19, %r9
subfe %r11, %r11, %r11
addc %r3, %r3, %r22
addze %r22, %r9
std %r3, 0(%r14)
addi %r14, %r14, 8
addi %r15, %r15, 8
addi %r16, %r16, 8
b 30f
32:
ld %r3, 8(%r14)
ld %r4, 16(%r14)
subfc %r12, %r12, %r10
ld %r9, 0(%r15)
mulld %r0, %r18, %r9
adde %r3, %r3, %r0
ld %r9, 8(%r15)
mulld %r0, %r18, %r9
adde %r4, %r4, %r0
mulhdu %r9, %r18, %r9
subfe %r12, %r12, %r12
addc %r3, %r3, %r20
ld %r0, 0(%r15)
mulhdu %r0, %r18, %r0
adde %r4, %r4, %r0
addze %r20, %r9
subfc %r11, %r11, %r10
ld %r9, 0(%r16)
mulld %r0, %r19, %r9
adde %r3, %r3, %r0
ld %r9, 8(%r16)
mulld %r0, %r19, %r9
adde %r4, %r4, %r0
mulhdu %r9, %r19, %r9
subfe %r11, %r11, %r11
addc %r3, %r3, %r22
ld %r0, 0(%r16)
mulhdu %r0, %r19, %r0
adde %r4, %r4, %r0
addze %r22, %r9
std %r3, 0(%r14)
std %r4, 8(%r14)
addi %r14, %r14, 16
addi %r15, %r15, 16
addi %r16, %r16, 16
30:
cmplwi %cr0, %r17, 0
beq %cr0, 35f
34:
ld %r3, 8(%r14)
ld %r4, 16(%r14)
ld %r7, 24(%r14)
ld %r8, 32(%r14)
subfc %r12, %r12, %r10
ld %r9, 0(%r15)
mulld %r0, %r18, %r9
adde %r3, %r3, %r0
ld %r9, 8(%r15)
mulld %r0, %r18, %r9
adde %r4, %r4, %r0
ld %r9, 16(%r15)
mulld %r0, %r18, %r9
adde %r7, %r7, %r0
ld %r9, 24(%r15)
mulld %r0, %r18, %r9
adde %r8, %r8, %r0
mulhdu %r9, %r18, %r9
subfe %r12, %r12, %r12
addc %r3, %r3, %r20
ld %r0, 0(%r15)
mulhdu %r0, %r18, %r0
adde %r4, %r4, %r0
ld %r0, 8(%r15)
mulhdu %r0, %r18, %r0
adde %r7, %r7, %r0
ld %r0, 16(%r15)
mulhdu %r0, %r18, %r0
adde %r8, %r8, %r0
addze %r20, %r9
subfc %r11, %r11, %r10
ld %r9, 0(%r16)
mulld %r0, %r19, %r9
adde %r3, %r3, %r0
ld %r9, 8(%r16)
mulld %r0, %r19, %r9
adde %r4, %r4, %r0
ld %r9, 16(%r16)
mulld %r0, %r19, %r9
adde %r7, %r7, %r0
ld %r9, 24(%r16)
mulld %r0, %r19, %r9
adde %r8, %r8, %r0
mulhdu %r9, %r19, %r9
subfe %r11, %r11, %r11
addc %r3, %r3, %r22
ld %r0, 0(%r16)
mulhdu %r0, %r19, %r0
adde %r4, %r4, %r0
ld %r0, 8(%r16)
mulhdu %r0, %r19, %r0
adde %r7, %r7, %r0
ld %r0, 16(%r16)
mulhdu %r0, %r19, %r0
adde %r8, %r8, %r0
addze %r22, %r9
std %r3, 0(%r14)
std %r4, 8(%r14)
std %r7, 16(%r14)
std %r8, 24(%r14)
addi %r14, %r14, 32
addi %r15, %r15, 32
addi %r16, %r16, 32
addi %r17, %r17, -1
cmplwi %cr0, %r17, 0
bne %cr0, 34b
35:
ld %r3, 8(%r14)
li %r4, 0
subfc %r12, %r12, %r10
adde %r3, %r3, %r20
addze %r4, %r4
subfc %r11, %r11, %r10
adde %r3, %r3, %r22
addze %r4, %r4
std %r3, 0(%r14)
std %r4, 8(%r14)
li %r9, 1
sldi %r9, %r9, 32
subf %r17, %r9, %r17
srdi %r9, %r17, 32
cmpldi %cr0, %r9, 0
bne %cr0, 2b
subf %r3, %r10, %r16
srdi %r11, %r3, 2
subf %r7, %r3, %r15
add %r8, %r3, %r3
add %r8, %r8, %r10
addi %r8, %r8, 32
add %r9, %r8, %r3
addi %r9, %r9, 16
add %r4, %r8, %r3
ld %r22, 8(%r4)
sldi %r12, %r22, 32
srdi %r12, %r12, 32
addi %r14, %r8, 0
addi %r15, %r9, 0
addi %r16, %r10, 0
srdi %r17, %r11, 1
subfc %r0, %r0, %r0
5:
ld %r0, 0(%r14)
ld %r3, 0(%r16)
subfe %r0, %r3, %r0
std %r0, 0(%r15)
addi %r14, %r14, 8
addi %r15, %r15, 8
addi %r16, %r16, 8
addi %r17, %r17, -1
cmpldi %cr0, %r17, 0
bne %cr0, 5b
ld %r0, 0(%r14)
li %r3, 0
subfe %r0, %r3, %r0
subfe %r20, %r20, %r20
addi %r14, %r8, 0
addi %r15, %r9, 0
addi %r16, %r5, 0
srdi %r17, %r11, 1
6:
ld %r0, 0(%r15)
ld %r3, 0(%r14)
xor %r3, %r3, %r0
and %r3, %r3, %r20
xor %r3, %r3, %r0
std %r3, 0(%r16)
addi %r14, %r14, 8
addi %r15, %r15, 8
addi %r16, %r16, 8
addi %r17, %r17, -1
cmpldi %cr0, %r17, 0
bne %cr0, 6b
sldi %r3, %r11, 2
add %r3, %r9, %r3
ld %r14, 8(%r3)
blr
"#,
    )
}
