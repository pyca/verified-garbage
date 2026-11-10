// The functions of `src/internal/vg_rsa_mont_kernel.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_mont_kernel:
	mtvsrd 32, %r27
	mtvsrd 33, %r28
	mtvsrd 34, %r29
	mtvsrd 35, %r30
	mtvsrd 36, %r31
	mtvsrd 37, %r2
	mtvsrd 38, %r23
	mtvsrd 39, %r24
	mtvsrd 40, %r25
	mtvsrd 41, %r26
	addi %r12, %r3, 0
	addi %r11, %r4, 0
	rldicr %r3, %r4, 2, 61
	add %r3, %r9, %r3
	std %r14, 8(%r3)
	ld %r3, 0(%r10)
	mulld %r22, %r3, %r12
	addi %r22, %r22, 2
	mulld %r22, %r22, %r12
	rldicr %r14, %r11, 2, 61
	add %r14, %r14, %r8
	std %r22, 8(%r14)
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r3, 0
20:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 20b
	rldicr %r3, %r11, 61, 2
	rldicl %r3, %r3, 2, 62
	cmpldi %cr0, %r3, 0
	beq %cr0, 21f
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
23:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 61, 3
	add %r17, %r17, %r8
	rldicr %r27, %r7, 61, 2
	rldicl %r27, %r27, 1, 63
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
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
	beq %cr0, 24f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 26f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 28f
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
	b 29f
28:
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
29:
	b 27f
26:
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
27:
	b 25f
24:
25:
	cmpldi %cr0, %r27, 0
	beq %cr0, 210f
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
	b 211f
210:
211:
	cmplwi %cr0, %r17, 0
	beq %cr0, 212f
214:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	ld %r28, 40(%r14)
	ld %r29, 48(%r14)
	ld %r30, 56(%r14)
	ld %r31, 64(%r14)
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
	ld %r9, 32(%r15)
	mulld %r0, %r18, %r9
	adde %r28, %r28, %r0
	ld %r9, 40(%r15)
	mulld %r0, %r18, %r9
	adde %r29, %r29, %r0
	ld %r9, 48(%r15)
	mulld %r0, %r18, %r9
	adde %r30, %r30, %r0
	ld %r9, 56(%r15)
	mulld %r0, %r18, %r9
	adde %r31, %r31, %r0
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
	ld %r0, 24(%r15)
	mulhdu %r0, %r18, %r0
	adde %r28, %r28, %r0
	ld %r0, 32(%r15)
	mulhdu %r0, %r18, %r0
	adde %r29, %r29, %r0
	ld %r0, 40(%r15)
	mulhdu %r0, %r18, %r0
	adde %r30, %r30, %r0
	ld %r0, 48(%r15)
	mulhdu %r0, %r18, %r0
	adde %r31, %r31, %r0
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
	ld %r9, 32(%r16)
	mulld %r0, %r19, %r9
	adde %r28, %r28, %r0
	ld %r9, 40(%r16)
	mulld %r0, %r19, %r9
	adde %r29, %r29, %r0
	ld %r9, 48(%r16)
	mulld %r0, %r19, %r9
	adde %r30, %r30, %r0
	ld %r9, 56(%r16)
	mulld %r0, %r19, %r9
	adde %r31, %r31, %r0
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
	ld %r0, 24(%r16)
	mulhdu %r0, %r19, %r0
	adde %r28, %r28, %r0
	ld %r0, 32(%r16)
	mulhdu %r0, %r19, %r0
	adde %r29, %r29, %r0
	ld %r0, 40(%r16)
	mulhdu %r0, %r19, %r0
	adde %r30, %r30, %r0
	ld %r0, 48(%r16)
	mulhdu %r0, %r19, %r0
	adde %r31, %r31, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	std %r28, 32(%r14)
	std %r29, 40(%r14)
	std %r30, 48(%r14)
	std %r31, 56(%r14)
	addi %r14, %r14, 64
	addi %r15, %r15, 64
	addi %r16, %r16, 64
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 214b
	b 213f
212:
213:
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
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 23b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	b 22f
21:
	li %r0, 0
	rldicl %r4, %r11, 61, 3
215:
	addi %r9, %r8, 0
	addi %r12, %r10, 0
	rldicr %r22, %r11, 2, 61
	add %r22, %r22, %r8
	ld %r23, 8(%r22)
	rldicl %r3, %r11, 61, 3
	addi %r3, %r3, -1
	ld %r14, 0(%r7)
	ld %r15, 8(%r7)
	ld %r16, 16(%r7)
	ld %r17, 24(%r7)
	ld %r18, 0(%r12)
	ld %r19, 8(%r12)
	ld %r20, 16(%r12)
	ld %r2, 24(%r12)
	addi %r7, %r7, 32
	addi %r12, %r12, 32
	ld %r27, 0(%r9)
	ld %r28, 8(%r9)
	ld %r29, 16(%r9)
	ld %r30, 24(%r9)
	li %r26, 0
	addc %r27, %r27, %r0
	addze %r26, %r26
	ld %r24, 0(%r6)
	mulld %r22, %r14, %r24
	addc %r27, %r27, %r22
	mulld %r22, %r15, %r24
	adde %r28, %r28, %r22
	mulld %r22, %r16, %r24
	adde %r29, %r29, %r22
	mulld %r22, %r17, %r24
	adde %r30, %r30, %r22
	addze %r31, %r0
	mulhdu %r22, %r14, %r24
	addc %r28, %r28, %r22
	mulhdu %r22, %r15, %r24
	adde %r29, %r29, %r22
	mulhdu %r22, %r16, %r24
	adde %r30, %r30, %r22
	mulhdu %r22, %r17, %r24
	adde %r31, %r31, %r22
	mulld %r25, %r27, %r23
	std %r25, 0(%r9)
	mulld %r22, %r18, %r25
	addc %r27, %r27, %r22
	mulld %r22, %r19, %r25
	adde %r28, %r28, %r22
	mulld %r22, %r20, %r25
	adde %r29, %r29, %r22
	mulld %r22, %r2, %r25
	adde %r30, %r30, %r22
	adde %r31, %r31, %r26
	addze %r26, %r0
	mulhdu %r22, %r18, %r25
	addc %r27, %r28, %r22
	mulhdu %r22, %r19, %r25
	adde %r28, %r29, %r22
	mulhdu %r22, %r20, %r25
	adde %r29, %r30, %r22
	mulhdu %r22, %r2, %r25
	adde %r30, %r31, %r22
	addze %r26, %r26
	ld %r24, 8(%r6)
	mulld %r22, %r14, %r24
	addc %r27, %r27, %r22
	mulld %r22, %r15, %r24
	adde %r28, %r28, %r22
	mulld %r22, %r16, %r24
	adde %r29, %r29, %r22
	mulld %r22, %r17, %r24
	adde %r30, %r30, %r22
	addze %r31, %r0
	mulhdu %r22, %r14, %r24
	addc %r28, %r28, %r22
	mulhdu %r22, %r15, %r24
	adde %r29, %r29, %r22
	mulhdu %r22, %r16, %r24
	adde %r30, %r30, %r22
	mulhdu %r22, %r17, %r24
	adde %r31, %r31, %r22
	mulld %r25, %r27, %r23
	std %r25, 8(%r9)
	mulld %r22, %r18, %r25
	addc %r27, %r27, %r22
	mulld %r22, %r19, %r25
	adde %r28, %r28, %r22
	mulld %r22, %r20, %r25
	adde %r29, %r29, %r22
	mulld %r22, %r2, %r25
	adde %r30, %r30, %r22
	adde %r31, %r31, %r26
	addze %r26, %r0
	mulhdu %r22, %r18, %r25
	addc %r27, %r28, %r22
	mulhdu %r22, %r19, %r25
	adde %r28, %r29, %r22
	mulhdu %r22, %r20, %r25
	adde %r29, %r30, %r22
	mulhdu %r22, %r2, %r25
	adde %r30, %r31, %r22
	addze %r26, %r26
	ld %r24, 16(%r6)
	mulld %r22, %r14, %r24
	addc %r27, %r27, %r22
	mulld %r22, %r15, %r24
	adde %r28, %r28, %r22
	mulld %r22, %r16, %r24
	adde %r29, %r29, %r22
	mulld %r22, %r17, %r24
	adde %r30, %r30, %r22
	addze %r31, %r0
	mulhdu %r22, %r14, %r24
	addc %r28, %r28, %r22
	mulhdu %r22, %r15, %r24
	adde %r29, %r29, %r22
	mulhdu %r22, %r16, %r24
	adde %r30, %r30, %r22
	mulhdu %r22, %r17, %r24
	adde %r31, %r31, %r22
	mulld %r25, %r27, %r23
	std %r25, 16(%r9)
	mulld %r22, %r18, %r25
	addc %r27, %r27, %r22
	mulld %r22, %r19, %r25
	adde %r28, %r28, %r22
	mulld %r22, %r20, %r25
	adde %r29, %r29, %r22
	mulld %r22, %r2, %r25
	adde %r30, %r30, %r22
	adde %r31, %r31, %r26
	addze %r26, %r0
	mulhdu %r22, %r18, %r25
	addc %r27, %r28, %r22
	mulhdu %r22, %r19, %r25
	adde %r28, %r29, %r22
	mulhdu %r22, %r20, %r25
	adde %r29, %r30, %r22
	mulhdu %r22, %r2, %r25
	adde %r30, %r31, %r22
	addze %r26, %r26
	ld %r24, 24(%r6)
	mulld %r22, %r14, %r24
	addc %r27, %r27, %r22
	mulld %r22, %r15, %r24
	adde %r28, %r28, %r22
	mulld %r22, %r16, %r24
	adde %r29, %r29, %r22
	mulld %r22, %r17, %r24
	adde %r30, %r30, %r22
	addze %r31, %r0
	mulhdu %r22, %r14, %r24
	addc %r28, %r28, %r22
	mulhdu %r22, %r15, %r24
	adde %r29, %r29, %r22
	mulhdu %r22, %r16, %r24
	adde %r30, %r30, %r22
	mulhdu %r22, %r17, %r24
	adde %r31, %r31, %r22
	mulld %r25, %r27, %r23
	std %r25, 24(%r9)
	mulld %r22, %r18, %r25
	addc %r27, %r27, %r22
	mulld %r22, %r19, %r25
	adde %r28, %r28, %r22
	mulld %r22, %r20, %r25
	adde %r29, %r29, %r22
	mulld %r22, %r2, %r25
	adde %r30, %r30, %r22
	adde %r31, %r31, %r26
	addze %r26, %r0
	mulhdu %r22, %r18, %r25
	addc %r27, %r28, %r22
	mulhdu %r22, %r19, %r25
	adde %r28, %r29, %r22
	mulhdu %r22, %r20, %r25
	adde %r29, %r30, %r22
	mulhdu %r22, %r2, %r25
	adde %r30, %r31, %r22
	cmpldi %cr0, %r3, 0
	beq %cr0, 216f
218:
	addze %r26, %r26
	ld %r22, 32(%r9)
	addc %r27, %r27, %r22
	ld %r22, 40(%r9)
	adde %r28, %r28, %r22
	ld %r22, 48(%r9)
	adde %r29, %r29, %r22
	ld %r22, 56(%r9)
	adde %r30, %r30, %r22
	ld %r14, 0(%r7)
	ld %r15, 8(%r7)
	ld %r16, 16(%r7)
	ld %r17, 24(%r7)
	ld %r18, 0(%r12)
	ld %r19, 8(%r12)
	ld %r20, 16(%r12)
	ld %r2, 24(%r12)
	addi %r7, %r7, 32
	addi %r12, %r12, 32
	addze %r26, %r26
	ld %r24, 0(%r6)
	ld %r25, 0(%r9)
	std %r25, 32(%r9)
	mulld %r22, %r14, %r24
	addc %r27, %r27, %r22
	mulld %r22, %r15, %r24
	adde %r28, %r28, %r22
	mulld %r22, %r16, %r24
	adde %r29, %r29, %r22
	mulld %r22, %r17, %r24
	adde %r30, %r30, %r22
	addze %r31, %r0
	mulhdu %r22, %r14, %r24
	addc %r28, %r28, %r22
	mulhdu %r22, %r15, %r24
	adde %r29, %r29, %r22
	mulhdu %r22, %r16, %r24
	adde %r30, %r30, %r22
	mulhdu %r22, %r17, %r24
	adde %r31, %r31, %r22
	mulld %r22, %r18, %r25
	addc %r27, %r27, %r22
	mulld %r22, %r19, %r25
	adde %r28, %r28, %r22
	mulld %r22, %r20, %r25
	adde %r29, %r29, %r22
	mulld %r22, %r2, %r25
	adde %r30, %r30, %r22
	adde %r31, %r31, %r26
	addze %r26, %r0
	std %r27, 0(%r9)
	mulhdu %r22, %r18, %r25
	addc %r27, %r28, %r22
	mulhdu %r22, %r19, %r25
	adde %r28, %r29, %r22
	mulhdu %r22, %r20, %r25
	adde %r29, %r30, %r22
	mulhdu %r22, %r2, %r25
	adde %r30, %r31, %r22
	addze %r26, %r26
	ld %r24, 8(%r6)
	ld %r25, 8(%r9)
	std %r25, 40(%r9)
	mulld %r22, %r14, %r24
	addc %r27, %r27, %r22
	mulld %r22, %r15, %r24
	adde %r28, %r28, %r22
	mulld %r22, %r16, %r24
	adde %r29, %r29, %r22
	mulld %r22, %r17, %r24
	adde %r30, %r30, %r22
	addze %r31, %r0
	mulhdu %r22, %r14, %r24
	addc %r28, %r28, %r22
	mulhdu %r22, %r15, %r24
	adde %r29, %r29, %r22
	mulhdu %r22, %r16, %r24
	adde %r30, %r30, %r22
	mulhdu %r22, %r17, %r24
	adde %r31, %r31, %r22
	mulld %r22, %r18, %r25
	addc %r27, %r27, %r22
	mulld %r22, %r19, %r25
	adde %r28, %r28, %r22
	mulld %r22, %r20, %r25
	adde %r29, %r29, %r22
	mulld %r22, %r2, %r25
	adde %r30, %r30, %r22
	adde %r31, %r31, %r26
	addze %r26, %r0
	std %r27, 8(%r9)
	mulhdu %r22, %r18, %r25
	addc %r27, %r28, %r22
	mulhdu %r22, %r19, %r25
	adde %r28, %r29, %r22
	mulhdu %r22, %r20, %r25
	adde %r29, %r30, %r22
	mulhdu %r22, %r2, %r25
	adde %r30, %r31, %r22
	addze %r26, %r26
	ld %r24, 16(%r6)
	ld %r25, 16(%r9)
	std %r25, 48(%r9)
	mulld %r22, %r14, %r24
	addc %r27, %r27, %r22
	mulld %r22, %r15, %r24
	adde %r28, %r28, %r22
	mulld %r22, %r16, %r24
	adde %r29, %r29, %r22
	mulld %r22, %r17, %r24
	adde %r30, %r30, %r22
	addze %r31, %r0
	mulhdu %r22, %r14, %r24
	addc %r28, %r28, %r22
	mulhdu %r22, %r15, %r24
	adde %r29, %r29, %r22
	mulhdu %r22, %r16, %r24
	adde %r30, %r30, %r22
	mulhdu %r22, %r17, %r24
	adde %r31, %r31, %r22
	mulld %r22, %r18, %r25
	addc %r27, %r27, %r22
	mulld %r22, %r19, %r25
	adde %r28, %r28, %r22
	mulld %r22, %r20, %r25
	adde %r29, %r29, %r22
	mulld %r22, %r2, %r25
	adde %r30, %r30, %r22
	adde %r31, %r31, %r26
	addze %r26, %r0
	std %r27, 16(%r9)
	mulhdu %r22, %r18, %r25
	addc %r27, %r28, %r22
	mulhdu %r22, %r19, %r25
	adde %r28, %r29, %r22
	mulhdu %r22, %r20, %r25
	adde %r29, %r30, %r22
	mulhdu %r22, %r2, %r25
	adde %r30, %r31, %r22
	addze %r26, %r26
	ld %r24, 24(%r6)
	ld %r25, 24(%r9)
	std %r25, 56(%r9)
	mulld %r22, %r14, %r24
	addc %r27, %r27, %r22
	mulld %r22, %r15, %r24
	adde %r28, %r28, %r22
	mulld %r22, %r16, %r24
	adde %r29, %r29, %r22
	mulld %r22, %r17, %r24
	adde %r30, %r30, %r22
	addze %r31, %r0
	mulhdu %r22, %r14, %r24
	addc %r28, %r28, %r22
	mulhdu %r22, %r15, %r24
	adde %r29, %r29, %r22
	mulhdu %r22, %r16, %r24
	adde %r30, %r30, %r22
	mulhdu %r22, %r17, %r24
	adde %r31, %r31, %r22
	mulld %r22, %r18, %r25
	addc %r27, %r27, %r22
	mulld %r22, %r19, %r25
	adde %r28, %r28, %r22
	mulld %r22, %r20, %r25
	adde %r29, %r29, %r22
	mulld %r22, %r2, %r25
	adde %r30, %r30, %r22
	adde %r31, %r31, %r26
	addze %r26, %r0
	std %r27, 24(%r9)
	mulhdu %r22, %r18, %r25
	addc %r27, %r28, %r22
	mulhdu %r22, %r19, %r25
	adde %r28, %r29, %r22
	mulhdu %r22, %r20, %r25
	adde %r29, %r30, %r22
	mulhdu %r22, %r2, %r25
	adde %r30, %r31, %r22
	addi %r9, %r9, 32
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 218b
	b 217f
216:
217:
	addze %r26, %r26
	ld %r22, 32(%r9)
	addc %r27, %r27, %r22
	addze %r28, %r28
	addze %r29, %r29
	addze %r30, %r30
	addze %r26, %r26
	std %r27, 0(%r9)
	std %r28, 8(%r9)
	std %r29, 16(%r9)
	std %r30, 24(%r9)
	std %r26, 32(%r9)
	rldicr %r22, %r11, 2, 61
	subf %r7, %r22, %r7
	addi %r6, %r6, 32
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 215b
	rldicr %r22, %r11, 2, 61
	add %r9, %r8, %r22
	ld %r22, 8(%r9)
	addi %r9, %r9, 16
22:
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
219:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 219b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
220:
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
	bne %cr0, 220b
	rldicr %r3, %r11, 2, 61
	add %r3, %r9, %r3
	ld %r14, 8(%r3)
	mfvsrd %r27, 32
	mfvsrd %r28, 33
	mfvsrd %r29, 34
	mfvsrd %r30, 35
	mfvsrd %r31, 36
	mfvsrd %r2, 37
	mfvsrd %r23, 38
	mfvsrd %r24, 39
	mfvsrd %r25, 40
	mfvsrd %r26, 41
	blr
