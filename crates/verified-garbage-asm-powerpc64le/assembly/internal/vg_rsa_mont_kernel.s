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
	mtvsrd 42, %r10
	addi %r12, %r3, 0
	addi %r11, %r4, 0
	rldicr %r3, %r4, 2, 61
	add %r3, %r9, %r3
	std %r14, 8(%r3)
	li %r0, 0
	subf %r3, %r7, %r6
	rldicr %r4, %r11, 60, 3
	rldicl %r4, %r4, 4, 60
	or %r3, %r3, %r4
	subf %r4, %r9, %r6
	subf %r30, %r4, %r0
	or %r4, %r4, %r30
	rldicl %r4, %r4, 1, 63
	li %r30, 1
	subf %r4, %r4, %r30
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	beq %cr0, 20f
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
22:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 22b
	rldicr %r3, %r11, 61, 2
	rldicl %r3, %r3, 2, 62
	cmpldi %cr0, %r3, 0
	beq %cr0, 23f
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
25:
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
	beq %cr0, 26f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 28f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 210f
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
	b 211f
210:
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
211:
	b 29f
28:
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
29:
	b 27f
26:
27:
	cmpldi %cr0, %r27, 0
	beq %cr0, 212f
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
	b 213f
212:
213:
	cmplwi %cr0, %r17, 0
	beq %cr0, 214f
216:
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
	bne %cr0, 216b
	b 215f
214:
215:
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
	bne %cr0, 25b
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
	b 24f
23:
	li %r0, 0
	rldicl %r4, %r11, 61, 3
217:
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
	beq %cr0, 218f
220:
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
	bne %cr0, 220b
	b 219f
218:
219:
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
	bne %cr0, 217b
	rldicr %r22, %r11, 2, 61
	add %r9, %r8, %r22
	ld %r22, 8(%r9)
	addi %r9, %r9, 16
24:
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
221:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 221b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
222:
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
	bne %cr0, 222b
	b 21f
20:
	li %r0, 0
	ld %r3, 0(%r10)
	mulld %r3, %r3, %r12
	addi %r3, %r3, 2
	mulld %r3, %r3, %r12
	rldicr %r30, %r11, 3, 60
	add %r31, %r8, %r30
	std %r3, 8(%r31)
	std %r0, 0(%r31)
	addi %r31, %r8, 0
	rldicl %r3, %r11, 60, 4
223:
	std %r0, 0(%r31)
	std %r0, 8(%r31)
	std %r0, 16(%r31)
	std %r0, 24(%r31)
	std %r0, 32(%r31)
	std %r0, 40(%r31)
	std %r0, 48(%r31)
	std %r0, 56(%r31)
	std %r0, 64(%r31)
	std %r0, 72(%r31)
	std %r0, 80(%r31)
	std %r0, 88(%r31)
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	std %r0, 112(%r31)
	std %r0, 120(%r31)
	addi %r31, %r31, 128
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 223b
	addi %r10, %r8, 0
	rldicl %r30, %r11, 60, 4
	rldicr %r9, %r30, 32, 31
224:
	ld %r14, 0(%r6)
	ld %r15, 8(%r6)
	ld %r16, 16(%r6)
	ld %r17, 24(%r6)
	ld %r18, 32(%r6)
	ld %r19, 40(%r6)
	ld %r20, 48(%r6)
	ld %r2, 56(%r6)
	addi %r12, %r10, 0
	ld %r22, 0(%r12)
	ld %r23, 8(%r12)
	ld %r24, 16(%r12)
	ld %r25, 24(%r12)
	ld %r26, 32(%r12)
	ld %r27, 40(%r12)
	ld %r28, 48(%r12)
	ld %r29, 56(%r12)
	li %r4, 0
	addc %r30, %r0, %r0
	addze %r4, %r4
	addc %r22, %r22, %r0
	addze %r23, %r23
	addze %r24, %r24
	addze %r25, %r25
	addze %r26, %r26
	addze %r27, %r27
	addze %r28, %r28
	addze %r29, %r29
	addze %r4, %r4
	std %r22, 0(%r12)
	addc %r22, %r23, %r0
	addze %r23, %r24
	addze %r24, %r25
	addze %r25, %r26
	addze %r26, %r27
	addze %r27, %r28
	addze %r28, %r29
	addze %r29, %r4
	addze %r4, %r0
	mulld %r30, %r14, %r15
	addc %r22, %r22, %r30
	addze %r23, %r23
	addze %r24, %r24
	addze %r25, %r25
	addze %r26, %r26
	addze %r27, %r27
	addze %r28, %r28
	addze %r29, %r29
	addze %r4, %r4
	std %r22, 8(%r12)
	mulhdu %r30, %r14, %r15
	addc %r22, %r23, %r30
	addze %r23, %r24
	addze %r24, %r25
	addze %r25, %r26
	addze %r26, %r27
	addze %r27, %r28
	addze %r28, %r29
	addze %r29, %r4
	addze %r4, %r0
	mulld %r30, %r14, %r16
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r16
	adde %r23, %r23, %r30
	addze %r24, %r24
	addze %r25, %r25
	addze %r26, %r26
	addze %r27, %r27
	addze %r28, %r28
	addze %r29, %r29
	addze %r4, %r4
	std %r22, 16(%r12)
	mulhdu %r30, %r14, %r16
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r16
	adde %r23, %r24, %r30
	addze %r24, %r25
	addze %r25, %r26
	addze %r26, %r27
	addze %r27, %r28
	addze %r28, %r29
	addze %r29, %r4
	addze %r4, %r0
	mulld %r30, %r14, %r17
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r17
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r17
	adde %r24, %r24, %r30
	addze %r25, %r25
	addze %r26, %r26
	addze %r27, %r27
	addze %r28, %r28
	addze %r29, %r29
	addze %r4, %r4
	std %r22, 24(%r12)
	mulhdu %r30, %r14, %r17
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r17
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r17
	adde %r24, %r25, %r30
	addze %r25, %r26
	addze %r26, %r27
	addze %r27, %r28
	addze %r28, %r29
	addze %r29, %r4
	addze %r4, %r0
	mulld %r30, %r14, %r18
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r18
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r18
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r18
	adde %r25, %r25, %r30
	addze %r26, %r26
	addze %r27, %r27
	addze %r28, %r28
	addze %r29, %r29
	addze %r4, %r4
	std %r22, 32(%r12)
	mulhdu %r30, %r14, %r18
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r18
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r18
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r18
	adde %r25, %r26, %r30
	addze %r26, %r27
	addze %r27, %r28
	addze %r28, %r29
	addze %r29, %r4
	addze %r4, %r0
	mulld %r30, %r14, %r19
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r19
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r19
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r19
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r19
	adde %r26, %r26, %r30
	addze %r27, %r27
	addze %r28, %r28
	addze %r29, %r29
	addze %r4, %r4
	std %r22, 40(%r12)
	mulhdu %r30, %r14, %r19
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r19
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r19
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r19
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r19
	adde %r26, %r27, %r30
	addze %r27, %r28
	addze %r28, %r29
	addze %r29, %r4
	addze %r4, %r0
	mulld %r30, %r14, %r20
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r20
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r20
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r20
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r20
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r20
	adde %r27, %r27, %r30
	addze %r28, %r28
	addze %r29, %r29
	addze %r4, %r4
	std %r22, 48(%r12)
	mulhdu %r30, %r14, %r20
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r20
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r20
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r20
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r20
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r20
	adde %r27, %r28, %r30
	addze %r28, %r29
	addze %r29, %r4
	addze %r4, %r0
	mulld %r30, %r14, %r2
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r2
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r2
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r2
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r2
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r2
	adde %r27, %r27, %r30
	mulld %r30, %r20, %r2
	adde %r28, %r28, %r30
	addze %r29, %r29
	addze %r4, %r4
	std %r22, 56(%r12)
	mulhdu %r30, %r14, %r2
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r2
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r2
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r2
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r2
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r2
	adde %r27, %r28, %r30
	mulhdu %r30, %r20, %r2
	adde %r28, %r29, %r30
	addze %r29, %r4
	addi %r12, %r12, 64
	addze %r4, %r0
	ld %r30, 0(%r12)
	addc %r22, %r22, %r30
	ld %r30, 8(%r12)
	adde %r23, %r23, %r30
	ld %r30, 16(%r12)
	adde %r24, %r24, %r30
	ld %r30, 24(%r12)
	adde %r25, %r25, %r30
	ld %r30, 32(%r12)
	adde %r26, %r26, %r30
	ld %r30, 40(%r12)
	adde %r27, %r27, %r30
	ld %r30, 48(%r12)
	adde %r28, %r28, %r30
	ld %r30, 56(%r12)
	adde %r29, %r29, %r30
	addze %r4, %r4
	rldicl %r30, %r9, 32, 32
	addi %r30, %r30, -1
	or %r9, %r9, %r30
	addi %r7, %r6, 64
	cmplwi %cr0, %r9, 0
	beq %cr0, 225f
227:
	addze %r4, %r4
	ld %r3, 0(%r7)
	mulld %r30, %r14, %r3
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r3
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r3
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r3
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r3
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r3
	adde %r27, %r27, %r30
	mulld %r30, %r20, %r3
	adde %r28, %r28, %r30
	mulld %r30, %r2, %r3
	adde %r29, %r29, %r30
	addze %r4, %r4
	std %r22, 0(%r12)
	mulhdu %r30, %r14, %r3
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r3
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r3
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r3
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r3
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r3
	adde %r27, %r28, %r30
	mulhdu %r30, %r20, %r3
	adde %r28, %r29, %r30
	mulhdu %r30, %r2, %r3
	adde %r29, %r4, %r30
	addze %r4, %r0
	ld %r3, 8(%r7)
	mulld %r30, %r14, %r3
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r3
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r3
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r3
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r3
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r3
	adde %r27, %r27, %r30
	mulld %r30, %r20, %r3
	adde %r28, %r28, %r30
	mulld %r30, %r2, %r3
	adde %r29, %r29, %r30
	addze %r4, %r4
	std %r22, 8(%r12)
	mulhdu %r30, %r14, %r3
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r3
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r3
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r3
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r3
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r3
	adde %r27, %r28, %r30
	mulhdu %r30, %r20, %r3
	adde %r28, %r29, %r30
	mulhdu %r30, %r2, %r3
	adde %r29, %r4, %r30
	addze %r4, %r0
	ld %r3, 16(%r7)
	mulld %r30, %r14, %r3
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r3
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r3
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r3
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r3
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r3
	adde %r27, %r27, %r30
	mulld %r30, %r20, %r3
	adde %r28, %r28, %r30
	mulld %r30, %r2, %r3
	adde %r29, %r29, %r30
	addze %r4, %r4
	std %r22, 16(%r12)
	mulhdu %r30, %r14, %r3
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r3
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r3
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r3
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r3
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r3
	adde %r27, %r28, %r30
	mulhdu %r30, %r20, %r3
	adde %r28, %r29, %r30
	mulhdu %r30, %r2, %r3
	adde %r29, %r4, %r30
	addze %r4, %r0
	ld %r3, 24(%r7)
	mulld %r30, %r14, %r3
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r3
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r3
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r3
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r3
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r3
	adde %r27, %r27, %r30
	mulld %r30, %r20, %r3
	adde %r28, %r28, %r30
	mulld %r30, %r2, %r3
	adde %r29, %r29, %r30
	addze %r4, %r4
	std %r22, 24(%r12)
	mulhdu %r30, %r14, %r3
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r3
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r3
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r3
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r3
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r3
	adde %r27, %r28, %r30
	mulhdu %r30, %r20, %r3
	adde %r28, %r29, %r30
	mulhdu %r30, %r2, %r3
	adde %r29, %r4, %r30
	addze %r4, %r0
	ld %r3, 32(%r7)
	mulld %r30, %r14, %r3
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r3
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r3
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r3
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r3
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r3
	adde %r27, %r27, %r30
	mulld %r30, %r20, %r3
	adde %r28, %r28, %r30
	mulld %r30, %r2, %r3
	adde %r29, %r29, %r30
	addze %r4, %r4
	std %r22, 32(%r12)
	mulhdu %r30, %r14, %r3
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r3
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r3
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r3
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r3
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r3
	adde %r27, %r28, %r30
	mulhdu %r30, %r20, %r3
	adde %r28, %r29, %r30
	mulhdu %r30, %r2, %r3
	adde %r29, %r4, %r30
	addze %r4, %r0
	ld %r3, 40(%r7)
	mulld %r30, %r14, %r3
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r3
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r3
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r3
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r3
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r3
	adde %r27, %r27, %r30
	mulld %r30, %r20, %r3
	adde %r28, %r28, %r30
	mulld %r30, %r2, %r3
	adde %r29, %r29, %r30
	addze %r4, %r4
	std %r22, 40(%r12)
	mulhdu %r30, %r14, %r3
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r3
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r3
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r3
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r3
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r3
	adde %r27, %r28, %r30
	mulhdu %r30, %r20, %r3
	adde %r28, %r29, %r30
	mulhdu %r30, %r2, %r3
	adde %r29, %r4, %r30
	addze %r4, %r0
	ld %r3, 48(%r7)
	mulld %r30, %r14, %r3
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r3
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r3
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r3
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r3
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r3
	adde %r27, %r27, %r30
	mulld %r30, %r20, %r3
	adde %r28, %r28, %r30
	mulld %r30, %r2, %r3
	adde %r29, %r29, %r30
	addze %r4, %r4
	std %r22, 48(%r12)
	mulhdu %r30, %r14, %r3
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r3
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r3
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r3
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r3
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r3
	adde %r27, %r28, %r30
	mulhdu %r30, %r20, %r3
	adde %r28, %r29, %r30
	mulhdu %r30, %r2, %r3
	adde %r29, %r4, %r30
	addze %r4, %r0
	ld %r3, 56(%r7)
	mulld %r30, %r14, %r3
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r3
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r3
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r3
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r3
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r3
	adde %r27, %r27, %r30
	mulld %r30, %r20, %r3
	adde %r28, %r28, %r30
	mulld %r30, %r2, %r3
	adde %r29, %r29, %r30
	addze %r4, %r4
	std %r22, 56(%r12)
	mulhdu %r30, %r14, %r3
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r3
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r3
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r3
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r3
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r3
	adde %r27, %r28, %r30
	mulhdu %r30, %r20, %r3
	adde %r28, %r29, %r30
	mulhdu %r30, %r2, %r3
	adde %r29, %r4, %r30
	addi %r12, %r12, 64
	addi %r7, %r7, 64
	addze %r4, %r0
	ld %r30, 0(%r12)
	addc %r22, %r22, %r30
	ld %r30, 8(%r12)
	adde %r23, %r23, %r30
	ld %r30, 16(%r12)
	adde %r24, %r24, %r30
	ld %r30, 24(%r12)
	adde %r25, %r25, %r30
	ld %r30, 32(%r12)
	adde %r26, %r26, %r30
	ld %r30, 40(%r12)
	adde %r27, %r27, %r30
	ld %r30, 48(%r12)
	adde %r28, %r28, %r30
	ld %r30, 56(%r12)
	adde %r29, %r29, %r30
	addze %r4, %r4
	addi %r9, %r9, -1
	cmplwi %cr0, %r9, 0
	bne %cr0, 227b
	b 226f
225:
226:
	std %r22, 0(%r12)
	std %r23, 8(%r12)
	std %r24, 16(%r12)
	std %r25, 24(%r12)
	std %r26, 32(%r12)
	std %r27, 40(%r12)
	std %r28, 48(%r12)
	std %r29, 56(%r12)
	std %r4, 64(%r12)
	addi %r6, %r6, 64
	addi %r10, %r10, 128
	li %r30, 1
	rldicr %r30, %r30, 32, 31
	subf %r9, %r30, %r9
	rldicl %r30, %r9, 32, 32
	cmpldi %cr0, %r30, 0
	bne %cr0, 224b
	rldicr %r30, %r11, 2, 61
	subf %r6, %r30, %r6
	subf %r10, %r30, %r10
	subf %r10, %r30, %r10
	addi %r12, %r10, 0
	addi %r7, %r6, 0
	rldicl %r9, %r11, 63, 1
	li %r3, 0
	addc %r30, %r0, %r0
228:
	ld %r22, 0(%r12)
	ld %r23, 8(%r12)
	ld %r24, 0(%r7)
	mulld %r25, %r24, %r24
	mulhdu %r26, %r24, %r24
	rldicr %r27, %r22, 1, 62
	or %r27, %r27, %r3
	rldicl %r28, %r22, 1, 63
	rldicr %r29, %r23, 1, 62
	or %r29, %r29, %r28
	rldicl %r3, %r23, 1, 63
	adde %r27, %r27, %r25
	adde %r29, %r29, %r26
	std %r27, 0(%r12)
	std %r29, 8(%r12)
	addi %r12, %r12, 16
	addi %r7, %r7, 8
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 228b
	rldicr %r30, %r11, 3, 60
	subf %r7, %r30, %r10
	addi %r7, %r7, -32
	li %r8, 0
	rldicl %r30, %r11, 60, 4
	rldicr %r9, %r30, 32, 31
229:
	ld %r22, 0(%r10)
	ld %r23, 8(%r10)
	ld %r24, 16(%r10)
	ld %r25, 24(%r10)
	ld %r26, 32(%r10)
	ld %r27, 40(%r10)
	ld %r28, 48(%r10)
	ld %r29, 56(%r10)
	ld %r14, 0(%r7)
	ld %r15, 8(%r7)
	ld %r16, 16(%r7)
	ld %r17, 24(%r7)
	ld %r18, 32(%r7)
	ld %r19, 40(%r7)
	ld %r20, 48(%r7)
	ld %r2, 56(%r7)
	li %r4, 0
	addc %r30, %r0, %r0
	rldicr %r31, %r11, 4, 59
	add %r31, %r31, %r7
	ld %r31, 40(%r31)
	addze %r4, %r4
	mulld %r3, %r22, %r31
	std %r3, 0(%r10)
	mulld %r30, %r14, %r3
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r3
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r3
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r3
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r3
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r3
	adde %r27, %r27, %r30
	mulld %r30, %r20, %r3
	adde %r28, %r28, %r30
	mulld %r30, %r2, %r3
	adde %r29, %r29, %r30
	addze %r4, %r4
	mulhdu %r30, %r14, %r3
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r3
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r3
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r3
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r3
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r3
	adde %r27, %r28, %r30
	mulhdu %r30, %r20, %r3
	adde %r28, %r29, %r30
	mulhdu %r30, %r2, %r3
	adde %r29, %r4, %r30
	addze %r4, %r0
	mulld %r3, %r22, %r31
	std %r3, 8(%r10)
	mulld %r30, %r14, %r3
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r3
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r3
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r3
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r3
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r3
	adde %r27, %r27, %r30
	mulld %r30, %r20, %r3
	adde %r28, %r28, %r30
	mulld %r30, %r2, %r3
	adde %r29, %r29, %r30
	addze %r4, %r4
	mulhdu %r30, %r14, %r3
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r3
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r3
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r3
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r3
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r3
	adde %r27, %r28, %r30
	mulhdu %r30, %r20, %r3
	adde %r28, %r29, %r30
	mulhdu %r30, %r2, %r3
	adde %r29, %r4, %r30
	addze %r4, %r0
	mulld %r3, %r22, %r31
	std %r3, 16(%r10)
	mulld %r30, %r14, %r3
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r3
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r3
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r3
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r3
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r3
	adde %r27, %r27, %r30
	mulld %r30, %r20, %r3
	adde %r28, %r28, %r30
	mulld %r30, %r2, %r3
	adde %r29, %r29, %r30
	addze %r4, %r4
	mulhdu %r30, %r14, %r3
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r3
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r3
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r3
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r3
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r3
	adde %r27, %r28, %r30
	mulhdu %r30, %r20, %r3
	adde %r28, %r29, %r30
	mulhdu %r30, %r2, %r3
	adde %r29, %r4, %r30
	addze %r4, %r0
	mulld %r3, %r22, %r31
	std %r3, 24(%r10)
	mulld %r30, %r14, %r3
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r3
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r3
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r3
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r3
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r3
	adde %r27, %r27, %r30
	mulld %r30, %r20, %r3
	adde %r28, %r28, %r30
	mulld %r30, %r2, %r3
	adde %r29, %r29, %r30
	addze %r4, %r4
	mulhdu %r30, %r14, %r3
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r3
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r3
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r3
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r3
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r3
	adde %r27, %r28, %r30
	mulhdu %r30, %r20, %r3
	adde %r28, %r29, %r30
	mulhdu %r30, %r2, %r3
	adde %r29, %r4, %r30
	addze %r4, %r0
	mulld %r3, %r22, %r31
	std %r3, 32(%r10)
	mulld %r30, %r14, %r3
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r3
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r3
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r3
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r3
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r3
	adde %r27, %r27, %r30
	mulld %r30, %r20, %r3
	adde %r28, %r28, %r30
	mulld %r30, %r2, %r3
	adde %r29, %r29, %r30
	addze %r4, %r4
	mulhdu %r30, %r14, %r3
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r3
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r3
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r3
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r3
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r3
	adde %r27, %r28, %r30
	mulhdu %r30, %r20, %r3
	adde %r28, %r29, %r30
	mulhdu %r30, %r2, %r3
	adde %r29, %r4, %r30
	addze %r4, %r0
	mulld %r3, %r22, %r31
	std %r3, 40(%r10)
	mulld %r30, %r14, %r3
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r3
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r3
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r3
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r3
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r3
	adde %r27, %r27, %r30
	mulld %r30, %r20, %r3
	adde %r28, %r28, %r30
	mulld %r30, %r2, %r3
	adde %r29, %r29, %r30
	addze %r4, %r4
	mulhdu %r30, %r14, %r3
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r3
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r3
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r3
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r3
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r3
	adde %r27, %r28, %r30
	mulhdu %r30, %r20, %r3
	adde %r28, %r29, %r30
	mulhdu %r30, %r2, %r3
	adde %r29, %r4, %r30
	addze %r4, %r0
	mulld %r3, %r22, %r31
	std %r3, 48(%r10)
	mulld %r30, %r14, %r3
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r3
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r3
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r3
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r3
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r3
	adde %r27, %r27, %r30
	mulld %r30, %r20, %r3
	adde %r28, %r28, %r30
	mulld %r30, %r2, %r3
	adde %r29, %r29, %r30
	addze %r4, %r4
	mulhdu %r30, %r14, %r3
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r3
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r3
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r3
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r3
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r3
	adde %r27, %r28, %r30
	mulhdu %r30, %r20, %r3
	adde %r28, %r29, %r30
	mulhdu %r30, %r2, %r3
	adde %r29, %r4, %r30
	addze %r4, %r0
	mulld %r3, %r22, %r31
	std %r3, 56(%r10)
	mulld %r30, %r14, %r3
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r3
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r3
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r3
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r3
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r3
	adde %r27, %r27, %r30
	mulld %r30, %r20, %r3
	adde %r28, %r28, %r30
	mulld %r30, %r2, %r3
	adde %r29, %r29, %r30
	addze %r4, %r4
	mulhdu %r30, %r14, %r3
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r3
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r3
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r3
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r3
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r3
	adde %r27, %r28, %r30
	mulhdu %r30, %r20, %r3
	adde %r28, %r29, %r30
	mulhdu %r30, %r2, %r3
	adde %r29, %r4, %r30
	addi %r7, %r7, 64
	addi %r12, %r10, 64
	rldicl %r30, %r11, 60, 4
	addi %r30, %r30, -1
	or %r9, %r9, %r30
	cmplwi %cr0, %r9, 0
	beq %cr0, 230f
232:
	addze %r4, %r0
	ld %r30, 0(%r12)
	addc %r22, %r22, %r30
	ld %r30, 8(%r12)
	adde %r23, %r23, %r30
	ld %r30, 16(%r12)
	adde %r24, %r24, %r30
	ld %r30, 24(%r12)
	adde %r25, %r25, %r30
	ld %r30, 32(%r12)
	adde %r26, %r26, %r30
	ld %r30, 40(%r12)
	adde %r27, %r27, %r30
	ld %r30, 48(%r12)
	adde %r28, %r28, %r30
	ld %r30, 56(%r12)
	adde %r29, %r29, %r30
	addze %r4, %r4
	ld %r14, 0(%r7)
	ld %r15, 8(%r7)
	ld %r16, 16(%r7)
	ld %r17, 24(%r7)
	ld %r18, 32(%r7)
	ld %r19, 40(%r7)
	ld %r20, 48(%r7)
	ld %r2, 56(%r7)
	addze %r4, %r4
	ld %r3, 0(%r10)
	mulld %r30, %r14, %r3
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r3
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r3
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r3
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r3
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r3
	adde %r27, %r27, %r30
	mulld %r30, %r20, %r3
	adde %r28, %r28, %r30
	mulld %r30, %r2, %r3
	adde %r29, %r29, %r30
	addze %r4, %r4
	std %r22, 0(%r12)
	mulhdu %r30, %r14, %r3
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r3
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r3
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r3
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r3
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r3
	adde %r27, %r28, %r30
	mulhdu %r30, %r20, %r3
	adde %r28, %r29, %r30
	mulhdu %r30, %r2, %r3
	adde %r29, %r4, %r30
	addze %r4, %r0
	ld %r3, 8(%r10)
	mulld %r30, %r14, %r3
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r3
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r3
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r3
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r3
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r3
	adde %r27, %r27, %r30
	mulld %r30, %r20, %r3
	adde %r28, %r28, %r30
	mulld %r30, %r2, %r3
	adde %r29, %r29, %r30
	addze %r4, %r4
	std %r22, 8(%r12)
	mulhdu %r30, %r14, %r3
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r3
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r3
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r3
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r3
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r3
	adde %r27, %r28, %r30
	mulhdu %r30, %r20, %r3
	adde %r28, %r29, %r30
	mulhdu %r30, %r2, %r3
	adde %r29, %r4, %r30
	addze %r4, %r0
	ld %r3, 16(%r10)
	mulld %r30, %r14, %r3
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r3
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r3
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r3
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r3
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r3
	adde %r27, %r27, %r30
	mulld %r30, %r20, %r3
	adde %r28, %r28, %r30
	mulld %r30, %r2, %r3
	adde %r29, %r29, %r30
	addze %r4, %r4
	std %r22, 16(%r12)
	mulhdu %r30, %r14, %r3
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r3
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r3
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r3
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r3
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r3
	adde %r27, %r28, %r30
	mulhdu %r30, %r20, %r3
	adde %r28, %r29, %r30
	mulhdu %r30, %r2, %r3
	adde %r29, %r4, %r30
	addze %r4, %r0
	ld %r3, 24(%r10)
	mulld %r30, %r14, %r3
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r3
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r3
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r3
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r3
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r3
	adde %r27, %r27, %r30
	mulld %r30, %r20, %r3
	adde %r28, %r28, %r30
	mulld %r30, %r2, %r3
	adde %r29, %r29, %r30
	addze %r4, %r4
	std %r22, 24(%r12)
	mulhdu %r30, %r14, %r3
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r3
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r3
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r3
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r3
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r3
	adde %r27, %r28, %r30
	mulhdu %r30, %r20, %r3
	adde %r28, %r29, %r30
	mulhdu %r30, %r2, %r3
	adde %r29, %r4, %r30
	addze %r4, %r0
	ld %r3, 32(%r10)
	mulld %r30, %r14, %r3
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r3
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r3
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r3
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r3
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r3
	adde %r27, %r27, %r30
	mulld %r30, %r20, %r3
	adde %r28, %r28, %r30
	mulld %r30, %r2, %r3
	adde %r29, %r29, %r30
	addze %r4, %r4
	std %r22, 32(%r12)
	mulhdu %r30, %r14, %r3
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r3
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r3
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r3
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r3
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r3
	adde %r27, %r28, %r30
	mulhdu %r30, %r20, %r3
	adde %r28, %r29, %r30
	mulhdu %r30, %r2, %r3
	adde %r29, %r4, %r30
	addze %r4, %r0
	ld %r3, 40(%r10)
	mulld %r30, %r14, %r3
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r3
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r3
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r3
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r3
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r3
	adde %r27, %r27, %r30
	mulld %r30, %r20, %r3
	adde %r28, %r28, %r30
	mulld %r30, %r2, %r3
	adde %r29, %r29, %r30
	addze %r4, %r4
	std %r22, 40(%r12)
	mulhdu %r30, %r14, %r3
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r3
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r3
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r3
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r3
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r3
	adde %r27, %r28, %r30
	mulhdu %r30, %r20, %r3
	adde %r28, %r29, %r30
	mulhdu %r30, %r2, %r3
	adde %r29, %r4, %r30
	addze %r4, %r0
	ld %r3, 48(%r10)
	mulld %r30, %r14, %r3
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r3
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r3
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r3
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r3
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r3
	adde %r27, %r27, %r30
	mulld %r30, %r20, %r3
	adde %r28, %r28, %r30
	mulld %r30, %r2, %r3
	adde %r29, %r29, %r30
	addze %r4, %r4
	std %r22, 48(%r12)
	mulhdu %r30, %r14, %r3
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r3
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r3
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r3
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r3
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r3
	adde %r27, %r28, %r30
	mulhdu %r30, %r20, %r3
	adde %r28, %r29, %r30
	mulhdu %r30, %r2, %r3
	adde %r29, %r4, %r30
	addze %r4, %r0
	ld %r3, 56(%r10)
	mulld %r30, %r14, %r3
	addc %r22, %r22, %r30
	mulld %r30, %r15, %r3
	adde %r23, %r23, %r30
	mulld %r30, %r16, %r3
	adde %r24, %r24, %r30
	mulld %r30, %r17, %r3
	adde %r25, %r25, %r30
	mulld %r30, %r18, %r3
	adde %r26, %r26, %r30
	mulld %r30, %r19, %r3
	adde %r27, %r27, %r30
	mulld %r30, %r20, %r3
	adde %r28, %r28, %r30
	mulld %r30, %r2, %r3
	adde %r29, %r29, %r30
	addze %r4, %r4
	std %r22, 56(%r12)
	mulhdu %r30, %r14, %r3
	addc %r22, %r23, %r30
	mulhdu %r30, %r15, %r3
	adde %r23, %r24, %r30
	mulhdu %r30, %r16, %r3
	adde %r24, %r25, %r30
	mulhdu %r30, %r17, %r3
	adde %r25, %r26, %r30
	mulhdu %r30, %r18, %r3
	adde %r26, %r27, %r30
	mulhdu %r30, %r19, %r3
	adde %r27, %r28, %r30
	mulhdu %r30, %r20, %r3
	adde %r28, %r29, %r30
	mulhdu %r30, %r2, %r3
	adde %r29, %r4, %r30
	addi %r12, %r12, 64
	addi %r7, %r7, 64
	addi %r9, %r9, -1
	cmplwi %cr0, %r9, 0
	bne %cr0, 232b
	b 231f
230:
231:
	addze %r4, %r0
	ld %r30, 0(%r12)
	addc %r22, %r22, %r30
	ld %r30, 8(%r12)
	adde %r23, %r23, %r30
	ld %r30, 16(%r12)
	adde %r24, %r24, %r30
	ld %r30, 24(%r12)
	adde %r25, %r25, %r30
	ld %r30, 32(%r12)
	adde %r26, %r26, %r30
	ld %r30, 40(%r12)
	adde %r27, %r27, %r30
	ld %r30, 48(%r12)
	adde %r28, %r28, %r30
	ld %r30, 56(%r12)
	adde %r29, %r29, %r30
	addze %r4, %r4
	addc %r22, %r22, %r8
	addze %r23, %r23
	addze %r24, %r24
	addze %r25, %r25
	addze %r26, %r26
	addze %r27, %r27
	addze %r28, %r28
	addze %r29, %r29
	addze %r4, %r4
	std %r22, 0(%r12)
	std %r23, 8(%r12)
	std %r24, 16(%r12)
	std %r25, 24(%r12)
	std %r26, 32(%r12)
	std %r27, 40(%r12)
	std %r28, 48(%r12)
	std %r29, 56(%r12)
	addi %r8, %r4, 0
	rldicr %r30, %r11, 2, 61
	subf %r7, %r30, %r7
	addi %r10, %r10, 64
	li %r30, 1
	rldicr %r30, %r30, 32, 31
	subf %r9, %r30, %r9
	rldicl %r30, %r9, 32, 32
	cmpldi %cr0, %r30, 0
	bne %cr0, 229b
	rldicr %r30, %r11, 2, 61
	subf %r12, %r30, %r10
	rldicl %r9, %r11, 60, 4
	addi %r31, %r12, 0
233:
	ld %r22, 0(%r10)
	ld %r23, 8(%r10)
	ld %r24, 16(%r10)
	ld %r25, 24(%r10)
	ld %r26, 32(%r10)
	ld %r27, 40(%r10)
	ld %r28, 48(%r10)
	ld %r29, 56(%r10)
	std %r22, 0(%r31)
	std %r23, 8(%r31)
	std %r24, 16(%r31)
	std %r25, 24(%r31)
	std %r26, 32(%r31)
	std %r27, 40(%r31)
	std %r28, 48(%r31)
	std %r29, 56(%r31)
	addi %r10, %r10, 64
	addi %r31, %r31, 64
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 233b
	std %r8, 0(%r31)
	addi %r8, %r12, 0
	rldicr %r30, %r11, 2, 61
	add %r9, %r8, %r30
	addi %r9, %r9, 16
	rldicr %r30, %r11, 3, 60
	subf %r10, %r30, %r8
	addi %r10, %r10, -32
	rldicr %r30, %r11, 2, 61
	add %r30, %r9, %r30
	addi %r30, %r30, -8
	ld %r22, 0(%r30)
	addi %r7, %r6, 0
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
234:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 234b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
235:
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
	bne %cr0, 235b
21:
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
	mfvsrd %r10, 42
	blr
