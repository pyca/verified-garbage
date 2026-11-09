// PROTOTYPE, hand-written and unverified: for a bench/ branch's Benchmarks runs only, never merged.
#![allow(dead_code)]
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn vg_rsa_mont_kernel() {
    core::arch::naked_asm!(
        r#"std %r14, -8(%r1)
std %r21, -16(%r1)
std %r23, -24(%r1)
std %r24, -32(%r1)
std %r25, -40(%r1)
std %r26, -48(%r1)
std %r27, -56(%r1)
std %r28, -64(%r1)
std %r29, -72(%r1)
std %r30, -80(%r1)
std %r31, -88(%r1)
std %r5, -96(%r1)
std %r9, -104(%r1)
std %r6, -136(%r1)
std %r7, -144(%r1)
std %r8, -152(%r1)
std %r10, -160(%r1)
mr %r12, %r3
ld %r0, 0(%r10)
mulld %r3, %r0, %r12
addi %r3, %r3, 2
mulld %r3, %r3, %r12
std %r3, -112(%r1)
srdi %r4, %r4, 1
std %r4, -120(%r1)
std %r4, -128(%r1)
addi %r0, %r4, -1
andi. %r3, %r0, 3
std %r3, -168(%r1)
srdi %r0, %r0, 2
std %r0, -176(%r1)
mr %r29, %r8
addi %r30, %r4, 1
li %r0, 0
1:
std %r0, 0(%r29)
addi %r29, %r29, 8
addi %r30, %r30, -1
cmpldi %cr0, %r30, 0
bne %cr0, 1b
li %r12, 0
2:
ld %r3, -136(%r1)
ld %r17, 0(%r3)
addi %r3, %r3, 8
std %r3, -136(%r1)
ld %r6, -152(%r1)
ld %r7, -144(%r1)
ld %r10, -160(%r1)
ld %r16, -112(%r1)
ld %r27, 0(%r6)
ld %r18, 0(%r7)
ld %r23, 0(%r10)
mulld %r31, %r17, %r18
mulhdu %r14, %r17, %r18
addc %r27, %r27, %r31
addze %r3, %r12
mulld %r16, %r16, %r27
mulld %r31, %r16, %r23
mulhdu %r15, %r16, %r23
addc %r27, %r27, %r31
addze %r5, %r12
li %r4, 0
li %r9, 0
addi %r6, %r6, 8
addi %r7, %r7, 8
addi %r10, %r10, 8
ld %r8, -168(%r1)
cmpldi %cr0, %r8, 1
beq %cr0, 31f
cmpldi %cr0, %r8, 2
beq %cr0, 32f
cmpldi %cr0, %r8, 3
beq %cr0, 33f
b 30f
31:
ld %r18, 0(%r7)
ld %r23, 0(%r10)
ld %r27, 0(%r6)
mulld %r31, %r17, %r18
mulhdu %r18, %r17, %r18
addic %r3, %r3, -1
adde %r27, %r27, %r31
addze %r3, %r12
addic %r4, %r4, -1
adde %r27, %r27, %r14
addze %r4, %r12
mr %r14, %r18
mulld %r31, %r16, %r23
mulhdu %r23, %r16, %r23
addic %r5, %r5, -1
adde %r27, %r27, %r31
addze %r5, %r12
addic %r9, %r9, -1
adde %r27, %r27, %r15
addze %r9, %r12
mr %r15, %r23
std %r27, -8(%r6)
addi %r6, %r6, 8
addi %r7, %r7, 8
addi %r10, %r10, 8
b 30f
32:
ld %r18, 0(%r7)
ld %r19, 8(%r7)
ld %r23, 0(%r10)
ld %r24, 8(%r10)
ld %r27, 0(%r6)
ld %r28, 8(%r6)
mulld %r31, %r17, %r18
mulhdu %r18, %r17, %r18
mulld %r21, %r17, %r19
mulhdu %r19, %r17, %r19
addic %r3, %r3, -1
adde %r27, %r27, %r31
adde %r28, %r28, %r21
addze %r3, %r12
addic %r4, %r4, -1
adde %r27, %r27, %r14
adde %r28, %r28, %r18
addze %r4, %r12
mr %r14, %r19
mulld %r31, %r16, %r23
mulhdu %r23, %r16, %r23
mulld %r21, %r16, %r24
mulhdu %r24, %r16, %r24
addic %r5, %r5, -1
adde %r27, %r27, %r31
adde %r28, %r28, %r21
addze %r5, %r12
addic %r9, %r9, -1
adde %r27, %r27, %r15
adde %r28, %r28, %r23
addze %r9, %r12
mr %r15, %r24
std %r27, -8(%r6)
std %r28, 0(%r6)
addi %r6, %r6, 16
addi %r7, %r7, 16
addi %r10, %r10, 16
b 30f
33:
ld %r18, 0(%r7)
ld %r19, 8(%r7)
ld %r20, 16(%r7)
ld %r23, 0(%r10)
ld %r24, 8(%r10)
ld %r25, 16(%r10)
ld %r27, 0(%r6)
ld %r28, 8(%r6)
ld %r29, 16(%r6)
mulld %r31, %r17, %r18
mulhdu %r18, %r17, %r18
mulld %r21, %r17, %r19
mulhdu %r19, %r17, %r19
mulld %r0, %r17, %r20
mulhdu %r20, %r17, %r20
addic %r3, %r3, -1
adde %r27, %r27, %r31
adde %r28, %r28, %r21
adde %r29, %r29, %r0
addze %r3, %r12
addic %r4, %r4, -1
adde %r27, %r27, %r14
adde %r28, %r28, %r18
adde %r29, %r29, %r19
addze %r4, %r12
mr %r14, %r20
mulld %r31, %r16, %r23
mulhdu %r23, %r16, %r23
mulld %r21, %r16, %r24
mulhdu %r24, %r16, %r24
mulld %r0, %r16, %r25
mulhdu %r25, %r16, %r25
addic %r5, %r5, -1
adde %r27, %r27, %r31
adde %r28, %r28, %r21
adde %r29, %r29, %r0
addze %r5, %r12
addic %r9, %r9, -1
adde %r27, %r27, %r15
adde %r28, %r28, %r23
adde %r29, %r29, %r24
addze %r9, %r12
mr %r15, %r25
std %r27, -8(%r6)
std %r28, 0(%r6)
std %r29, 8(%r6)
addi %r6, %r6, 24
addi %r7, %r7, 24
addi %r10, %r10, 24
b 30f
30:
ld %r8, -176(%r1)
cmpldi %cr0, %r8, 0
beq %cr0, 35f
34:
ld %r18, 0(%r7)
ld %r19, 8(%r7)
ld %r20, 16(%r7)
ld %r22, 24(%r7)
ld %r23, 0(%r10)
ld %r24, 8(%r10)
ld %r25, 16(%r10)
ld %r26, 24(%r10)
ld %r27, 0(%r6)
ld %r28, 8(%r6)
ld %r29, 16(%r6)
ld %r30, 24(%r6)
mulld %r31, %r17, %r18
mulhdu %r18, %r17, %r18
mulld %r21, %r17, %r19
mulhdu %r19, %r17, %r19
mulld %r0, %r17, %r20
mulhdu %r20, %r17, %r20
mulld %r11, %r17, %r22
mulhdu %r22, %r17, %r22
addic %r3, %r3, -1
adde %r27, %r27, %r31
adde %r28, %r28, %r21
adde %r29, %r29, %r0
adde %r30, %r30, %r11
addze %r3, %r12
addic %r4, %r4, -1
adde %r27, %r27, %r14
adde %r28, %r28, %r18
adde %r29, %r29, %r19
adde %r30, %r30, %r20
addze %r4, %r12
mr %r14, %r22
mulld %r31, %r16, %r23
mulhdu %r23, %r16, %r23
mulld %r21, %r16, %r24
mulhdu %r24, %r16, %r24
mulld %r0, %r16, %r25
mulhdu %r25, %r16, %r25
mulld %r11, %r16, %r26
mulhdu %r26, %r16, %r26
addic %r5, %r5, -1
adde %r27, %r27, %r31
adde %r28, %r28, %r21
adde %r29, %r29, %r0
adde %r30, %r30, %r11
addze %r5, %r12
addic %r9, %r9, -1
adde %r27, %r27, %r15
adde %r28, %r28, %r23
adde %r29, %r29, %r24
adde %r30, %r30, %r25
addze %r9, %r12
mr %r15, %r26
std %r27, -8(%r6)
std %r28, 0(%r6)
std %r29, 8(%r6)
std %r30, 16(%r6)
addi %r6, %r6, 32
addi %r7, %r7, 32
addi %r10, %r10, 32
addi %r8, %r8, -1
cmpldi %cr0, %r8, 0
bne %cr0, 34b
35:
ld %r27, 0(%r6)
addic %r3, %r3, -1
adde %r27, %r27, %r12
addze %r28, %r12
addic %r4, %r4, -1
adde %r27, %r27, %r14
addze %r28, %r28
addic %r5, %r5, -1
adde %r27, %r27, %r12
addze %r28, %r28
addic %r9, %r9, -1
adde %r27, %r27, %r15
addze %r28, %r28
std %r27, -8(%r6)
std %r28, 0(%r6)
ld %r3, -128(%r1)
addi %r3, %r3, -1
std %r3, -128(%r1)
cmpldi %cr0, %r3, 0
bne %cr0, 2b
ld %r5, -96(%r1)
ld %r9, -104(%r1)
ld %r8, -152(%r1)
ld %r10, -160(%r1)
ld %r4, -120(%r1)
sldi %r11, %r4, 1
ld %r3, -112(%r1)
sldi %r12, %r3, 32
srdi %r12, %r12, 32
addi %r14, %r8, 0
addi %r15, %r9, 0
addi %r16, %r10, 0
mr %r17, %r4
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
mr %r17, %r4
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
ld %r14, -8(%r1)
ld %r21, -16(%r1)
ld %r23, -24(%r1)
ld %r24, -32(%r1)
ld %r25, -40(%r1)
ld %r26, -48(%r1)
ld %r27, -56(%r1)
ld %r28, -64(%r1)
ld %r29, -72(%r1)
ld %r30, -80(%r1)
ld %r31, -88(%r1)
ld %r10, -160(%r1)
blr"#
    )
}
