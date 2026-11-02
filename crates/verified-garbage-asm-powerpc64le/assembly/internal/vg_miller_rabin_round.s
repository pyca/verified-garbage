// The functions of `src/internal/vg_miller_rabin_round.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_miller_rabin_round:
	stdu %r1, -176(%r1)
	addi %r5, %r1, 32
	std %r14, 0(%r5)
	std %r15, 8(%r5)
	std %r16, 16(%r5)
	std %r17, 24(%r5)
	std %r18, 32(%r5)
	std %r19, 40(%r5)
	std %r20, 48(%r5)
	std %r22, 56(%r5)
	std %r23, 64(%r5)
	std %r24, 72(%r5)
	std %r25, 80(%r5)
	std %r26, 88(%r5)
	std %r27, 96(%r5)
	std %r28, 104(%r5)
	std %r29, 112(%r5)
	std %r30, 120(%r5)
	std %r31, 128(%r5)
	std %r21, 136(%r5)
	addi %r21, %r5, 0
	addi %r31, %r3, 0
	addi %r10, %r3, 256
	ld %r11, 48(%r3)
	rldicr %r29, %r11, 3, 60
	addi %r29, %r29, 16
	rldicr %r11, %r11, 1, 62
	lwz %r12, 56(%r3)
	li %r30, 0
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r30, 11
	mulld %r8, %r8, %r29
	add %r8, %r8, %r10
	addi %r5, %r8, 0
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
20:
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
	bne %cr0, 20b
	li %r30, 1
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r30, 11
	mulld %r8, %r8, %r29
	add %r8, %r8, %r10
	addi %r5, %r8, 0
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
21:
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
	bne %cr0, 21b
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
22:
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
	bne %cr0, 22b
	li %r30, 2
23:
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r6, %r10, 0
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	addi %r7, %r10, 0
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r4, %r11, 0
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
24:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 24b
25:
	ld %r17, 0(%r6)
	addi %r6, %r6, 8
	ld %r19, 0(%r7)
	ld %r20, 0(%r8)
	mulld %r18, %r17, %r19
	mulhdu %r19, %r17, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r3, 0(%r10)
	mulld %r22, %r3, %r12
	addi %r22, %r22, 2
	mulld %r22, %r22, %r12
	mulld %r0, %r20, %r22
	mulld %r22, %r0, %r3
	mulhdu %r19, %r0, %r3
	addc %r22, %r22, %r20
	addze %r22, %r19
	addi %r14, %r8, 0
	addi %r15, %r7, 0
	addi %r3, %r10, 0
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicr %r16, %r16, 62, 1
	rldicl %r16, %r16, 2, 62
	cmpldi %cr0, %r16, 0
	beq %cr0, 26f
28:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r3, %r3, 8
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 28b
	b 27f
26:
27:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 29f
211:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	ld %r19, 16(%r14)
	addc %r18, %r18, %r19
	ld %r19, 16(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 16(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 8(%r14)
	ld %r19, 24(%r14)
	addc %r18, %r18, %r19
	ld %r19, 24(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 24(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 16(%r14)
	ld %r19, 32(%r14)
	addc %r18, %r18, %r19
	ld %r19, 32(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 32(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r3, %r3, 32
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 211b
	b 210f
29:
210:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	li %r19, 0
	addze %r19, %r19
	addc %r18, %r18, %r22
	addze %r19, %r19
	std %r18, 0(%r14)
	std %r19, 8(%r14)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 25b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
212:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 212b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
213:
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
	bne %cr0, 213b
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r30, 11
	mulld %r8, %r8, %r29
	add %r8, %r8, %r10
	addi %r5, %r8, 0
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
214:
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
	bne %cr0, 214b
	addi %r30, %r30, 1
	addi %r4, %r30, -16
	cmpldi %cr0, %r4, 0
	bne %cr0, 23b
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
215:
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
	bne %cr0, 215b
	li %r23, 0
	rldicl %r26, %r11, 63, 1
	addi %r25, %r10, 0
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	add %r25, %r25, %r29
	rldicr %r0, %r26, 3, 60
	add %r25, %r25, %r0
216:
	addi %r25, %r25, -8
	ld %r24, 0(%r25)
	li %r27, 16
217:
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r6, %r10, 0
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	addi %r7, %r10, 0
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r4, %r11, 0
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
218:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 218b
219:
	ld %r17, 0(%r6)
	addi %r6, %r6, 8
	ld %r19, 0(%r7)
	ld %r20, 0(%r8)
	mulld %r18, %r17, %r19
	mulhdu %r19, %r17, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r3, 0(%r10)
	mulld %r22, %r3, %r12
	addi %r22, %r22, 2
	mulld %r22, %r22, %r12
	mulld %r0, %r20, %r22
	mulld %r22, %r0, %r3
	mulhdu %r19, %r0, %r3
	addc %r22, %r22, %r20
	addze %r22, %r19
	addi %r14, %r8, 0
	addi %r15, %r7, 0
	addi %r3, %r10, 0
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicr %r16, %r16, 62, 1
	rldicl %r16, %r16, 2, 62
	cmpldi %cr0, %r16, 0
	beq %cr0, 220f
222:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r3, %r3, 8
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 222b
	b 221f
220:
221:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 223f
225:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	ld %r19, 16(%r14)
	addc %r18, %r18, %r19
	ld %r19, 16(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 16(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 8(%r14)
	ld %r19, 24(%r14)
	addc %r18, %r18, %r19
	ld %r19, 24(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 24(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 16(%r14)
	ld %r19, 32(%r14)
	addc %r18, %r18, %r19
	ld %r19, 32(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 32(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r3, %r3, 32
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 225b
	b 224f
223:
224:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	li %r19, 0
	addze %r19, %r19
	addc %r18, %r18, %r22
	addze %r19, %r19
	std %r18, 0(%r14)
	std %r19, 8(%r14)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 219b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
226:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 226b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
227:
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
	bne %cr0, 227b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
	li %r3, 0
228:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 228b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r20, %r3, %r0
	or %r23, %r23, %r20
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r6, %r10, 0
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	addi %r7, %r10, 0
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r4, %r11, 0
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
229:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 229b
230:
	ld %r17, 0(%r6)
	addi %r6, %r6, 8
	ld %r19, 0(%r7)
	ld %r20, 0(%r8)
	mulld %r18, %r17, %r19
	mulhdu %r19, %r17, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r3, 0(%r10)
	mulld %r22, %r3, %r12
	addi %r22, %r22, 2
	mulld %r22, %r22, %r12
	mulld %r0, %r20, %r22
	mulld %r22, %r0, %r3
	mulhdu %r19, %r0, %r3
	addc %r22, %r22, %r20
	addze %r22, %r19
	addi %r14, %r8, 0
	addi %r15, %r7, 0
	addi %r3, %r10, 0
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicr %r16, %r16, 62, 1
	rldicl %r16, %r16, 2, 62
	cmpldi %cr0, %r16, 0
	beq %cr0, 231f
233:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r3, %r3, 8
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 233b
	b 232f
231:
232:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 234f
236:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	ld %r19, 16(%r14)
	addc %r18, %r18, %r19
	ld %r19, 16(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 16(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 8(%r14)
	ld %r19, 24(%r14)
	addc %r18, %r18, %r19
	ld %r19, 24(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 24(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 16(%r14)
	ld %r19, 32(%r14)
	addc %r18, %r18, %r19
	ld %r19, 32(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 32(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r3, %r3, 32
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 236b
	b 235f
234:
235:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	li %r19, 0
	addze %r19, %r19
	addc %r18, %r18, %r22
	addze %r19, %r19
	std %r18, 0(%r14)
	std %r19, 8(%r14)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 230b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
237:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 237b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
238:
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
	bne %cr0, 238b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
	li %r3, 0
239:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 239b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r20, %r3, %r0
	or %r23, %r23, %r20
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r6, %r10, 0
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	addi %r7, %r10, 0
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r4, %r11, 0
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
240:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 240b
241:
	ld %r17, 0(%r6)
	addi %r6, %r6, 8
	ld %r19, 0(%r7)
	ld %r20, 0(%r8)
	mulld %r18, %r17, %r19
	mulhdu %r19, %r17, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r3, 0(%r10)
	mulld %r22, %r3, %r12
	addi %r22, %r22, 2
	mulld %r22, %r22, %r12
	mulld %r0, %r20, %r22
	mulld %r22, %r0, %r3
	mulhdu %r19, %r0, %r3
	addc %r22, %r22, %r20
	addze %r22, %r19
	addi %r14, %r8, 0
	addi %r15, %r7, 0
	addi %r3, %r10, 0
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicr %r16, %r16, 62, 1
	rldicl %r16, %r16, 2, 62
	cmpldi %cr0, %r16, 0
	beq %cr0, 242f
244:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r3, %r3, 8
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 244b
	b 243f
242:
243:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 245f
247:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	ld %r19, 16(%r14)
	addc %r18, %r18, %r19
	ld %r19, 16(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 16(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 8(%r14)
	ld %r19, 24(%r14)
	addc %r18, %r18, %r19
	ld %r19, 24(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 24(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 16(%r14)
	ld %r19, 32(%r14)
	addc %r18, %r18, %r19
	ld %r19, 32(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 32(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r3, %r3, 32
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 247b
	b 246f
245:
246:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	li %r19, 0
	addze %r19, %r19
	addc %r18, %r18, %r22
	addze %r19, %r19
	std %r18, 0(%r14)
	std %r19, 8(%r14)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 241b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
248:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 248b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
249:
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
	bne %cr0, 249b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
	li %r3, 0
250:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 250b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r20, %r3, %r0
	or %r23, %r23, %r20
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r6, %r10, 0
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	addi %r7, %r10, 0
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r4, %r11, 0
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
251:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 251b
252:
	ld %r17, 0(%r6)
	addi %r6, %r6, 8
	ld %r19, 0(%r7)
	ld %r20, 0(%r8)
	mulld %r18, %r17, %r19
	mulhdu %r19, %r17, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r3, 0(%r10)
	mulld %r22, %r3, %r12
	addi %r22, %r22, 2
	mulld %r22, %r22, %r12
	mulld %r0, %r20, %r22
	mulld %r22, %r0, %r3
	mulhdu %r19, %r0, %r3
	addc %r22, %r22, %r20
	addze %r22, %r19
	addi %r14, %r8, 0
	addi %r15, %r7, 0
	addi %r3, %r10, 0
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicr %r16, %r16, 62, 1
	rldicl %r16, %r16, 2, 62
	cmpldi %cr0, %r16, 0
	beq %cr0, 253f
255:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r3, %r3, 8
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 255b
	b 254f
253:
254:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 256f
258:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	ld %r19, 16(%r14)
	addc %r18, %r18, %r19
	ld %r19, 16(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 16(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 8(%r14)
	ld %r19, 24(%r14)
	addc %r18, %r18, %r19
	ld %r19, 24(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 24(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 16(%r14)
	ld %r19, 32(%r14)
	addc %r18, %r18, %r19
	ld %r19, 32(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 32(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r3, %r3, 32
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 258b
	b 257f
256:
257:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	li %r19, 0
	addze %r19, %r19
	addc %r18, %r18, %r22
	addze %r19, %r19
	std %r18, 0(%r14)
	std %r19, 8(%r14)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 252b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
259:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 259b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
260:
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
	bne %cr0, 260b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
	li %r3, 0
261:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 261b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r20, %r3, %r0
	or %r23, %r23, %r20
	rldicl %r28, %r24, 4, 60
	li %r30, 0
262:
	xor %r3, %r30, %r28
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	li %r0, 0
	subf %r20, %r3, %r0
	addi %r8, %r30, 11
	mulld %r8, %r8, %r29
	add %r8, %r8, %r10
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
263:
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
	bne %cr0, 263b
	addi %r30, %r30, 1
	xor %r3, %r30, %r28
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	li %r0, 0
	subf %r20, %r3, %r0
	addi %r8, %r30, 11
	mulld %r8, %r8, %r29
	add %r8, %r8, %r10
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
264:
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
	bne %cr0, 264b
	addi %r30, %r30, 1
	addi %r4, %r30, -16
	cmpldi %cr0, %r4, 0
	bne %cr0, 262b
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r6, %r10, 0
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	addi %r7, %r10, 0
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r4, %r11, 0
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
265:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 265b
266:
	ld %r17, 0(%r6)
	addi %r6, %r6, 8
	ld %r19, 0(%r7)
	ld %r20, 0(%r8)
	mulld %r18, %r17, %r19
	mulhdu %r19, %r17, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r3, 0(%r10)
	mulld %r22, %r3, %r12
	addi %r22, %r22, 2
	mulld %r22, %r22, %r12
	mulld %r0, %r20, %r22
	mulld %r22, %r0, %r3
	mulhdu %r19, %r0, %r3
	addc %r22, %r22, %r20
	addze %r22, %r19
	addi %r14, %r8, 0
	addi %r15, %r7, 0
	addi %r3, %r10, 0
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicr %r16, %r16, 62, 1
	rldicl %r16, %r16, 2, 62
	cmpldi %cr0, %r16, 0
	beq %cr0, 267f
269:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r3, %r3, 8
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 269b
	b 268f
267:
268:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 270f
272:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	ld %r19, 16(%r14)
	addc %r18, %r18, %r19
	ld %r19, 16(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 16(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 8(%r14)
	ld %r19, 24(%r14)
	addc %r18, %r18, %r19
	ld %r19, 24(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 24(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 16(%r14)
	ld %r19, 32(%r14)
	addc %r18, %r18, %r19
	ld %r19, 32(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 32(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r3, %r3, 32
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 272b
	b 271f
270:
271:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	li %r19, 0
	addze %r19, %r19
	addc %r18, %r18, %r22
	addze %r19, %r19
	std %r18, 0(%r14)
	std %r19, 8(%r14)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 266b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
273:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 273b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
274:
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
	bne %cr0, 274b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
	li %r3, 0
275:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 275b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r20, %r3, %r0
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
	li %r3, 0
276:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 276b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	li %r0, 0
	subf %r3, %r28, %r0
	rldicl %r3, %r3, 1, 63
	subf %r3, %r3, %r0
	xor %r20, %r20, %r23
	and %r20, %r20, %r3
	xor %r23, %r23, %r20
	rldicr %r24, %r24, 4, 59
	addi %r27, %r27, -1
	cmpldi %cr0, %r27, 0
	bne %cr0, 217b
	addi %r26, %r26, -1
	cmpldi %cr0, %r26, 0
	bne %cr0, 216b
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r6, %r10, 0
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	addi %r7, %r10, 0
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r4, %r11, 0
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
277:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 277b
278:
	ld %r17, 0(%r6)
	addi %r6, %r6, 8
	ld %r19, 0(%r7)
	ld %r20, 0(%r8)
	mulld %r18, %r17, %r19
	mulhdu %r19, %r17, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r3, 0(%r10)
	mulld %r22, %r3, %r12
	addi %r22, %r22, 2
	mulld %r22, %r22, %r12
	mulld %r0, %r20, %r22
	mulld %r22, %r0, %r3
	mulhdu %r19, %r0, %r3
	addc %r22, %r22, %r20
	addze %r22, %r19
	addi %r14, %r8, 0
	addi %r15, %r7, 0
	addi %r3, %r10, 0
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicr %r16, %r16, 62, 1
	rldicl %r16, %r16, 2, 62
	cmpldi %cr0, %r16, 0
	beq %cr0, 279f
281:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r3, %r3, 8
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 281b
	b 280f
279:
280:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 282f
284:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	ld %r19, 16(%r14)
	addc %r18, %r18, %r19
	ld %r19, 16(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 16(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 8(%r14)
	ld %r19, 24(%r14)
	addc %r18, %r18, %r19
	ld %r19, 24(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 24(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 16(%r14)
	ld %r19, 32(%r14)
	addc %r18, %r18, %r19
	ld %r19, 32(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 32(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r3, %r3, 32
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 284b
	b 283f
282:
283:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	li %r19, 0
	addze %r19, %r19
	addc %r18, %r18, %r22
	addze %r19, %r19
	std %r18, 0(%r14)
	std %r19, 8(%r14)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 278b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
285:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 285b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
286:
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
	bne %cr0, 286b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
	li %r3, 0
287:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 287b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r20, %r3, %r0
	addi %r3, %r10, 0
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	rldicl %r0, %r11, 63, 1
	rldicr %r0, %r0, 3, 60
	add %r3, %r3, %r0
	ld %r3, 0(%r3)
	lis %r4, -8739
	ori %r4, %r4, 56797
	rldicr %r4, %r4, 32, 31
	oris %r4, %r4, 56797
	ori %r4, %r4, 56797
	and %r3, %r3, %r4
	rldicl %r4, %r3, 63, 1
	li %r0, 1
	and %r0, %r3, %r0
	or %r3, %r4, %r0
	li %r0, 0
	subf %r3, %r3, %r0
	rldicl %r3, %r3, 1, 63
	subf %r3, %r3, %r0
	and %r20, %r20, %r3
	or %r23, %r23, %r20
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r6, %r10, 0
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	addi %r7, %r10, 0
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r4, %r11, 0
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
288:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 288b
289:
	ld %r17, 0(%r6)
	addi %r6, %r6, 8
	ld %r19, 0(%r7)
	ld %r20, 0(%r8)
	mulld %r18, %r17, %r19
	mulhdu %r19, %r17, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r3, 0(%r10)
	mulld %r22, %r3, %r12
	addi %r22, %r22, 2
	mulld %r22, %r22, %r12
	mulld %r0, %r20, %r22
	mulld %r22, %r0, %r3
	mulhdu %r19, %r0, %r3
	addc %r22, %r22, %r20
	addze %r22, %r19
	addi %r14, %r8, 0
	addi %r15, %r7, 0
	addi %r3, %r10, 0
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicr %r16, %r16, 62, 1
	rldicl %r16, %r16, 2, 62
	cmpldi %cr0, %r16, 0
	beq %cr0, 290f
292:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r3, %r3, 8
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 292b
	b 291f
290:
291:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 293f
295:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	ld %r19, 16(%r14)
	addc %r18, %r18, %r19
	ld %r19, 16(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 16(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 8(%r14)
	ld %r19, 24(%r14)
	addc %r18, %r18, %r19
	ld %r19, 24(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 24(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 16(%r14)
	ld %r19, 32(%r14)
	addc %r18, %r18, %r19
	ld %r19, 32(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 32(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r3, %r3, 32
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 295b
	b 294f
293:
294:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	li %r19, 0
	addze %r19, %r19
	addc %r18, %r18, %r22
	addze %r19, %r19
	std %r18, 0(%r14)
	std %r19, 8(%r14)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 289b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
296:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 296b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
297:
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
	bne %cr0, 297b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
	li %r3, 0
298:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 298b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r20, %r3, %r0
	addi %r3, %r10, 0
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	rldicl %r0, %r11, 63, 1
	rldicr %r0, %r0, 3, 60
	add %r3, %r3, %r0
	ld %r3, 0(%r3)
	lis %r4, -26215
	ori %r4, %r4, 39321
	rldicr %r4, %r4, 32, 31
	oris %r4, %r4, 39321
	ori %r4, %r4, 39321
	and %r3, %r3, %r4
	rldicl %r4, %r3, 63, 1
	li %r0, 1
	and %r0, %r3, %r0
	or %r3, %r4, %r0
	li %r0, 0
	subf %r3, %r3, %r0
	rldicl %r3, %r3, 1, 63
	subf %r3, %r3, %r0
	and %r20, %r20, %r3
	or %r23, %r23, %r20
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r6, %r10, 0
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	addi %r7, %r10, 0
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r4, %r11, 0
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
299:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 299b
2100:
	ld %r17, 0(%r6)
	addi %r6, %r6, 8
	ld %r19, 0(%r7)
	ld %r20, 0(%r8)
	mulld %r18, %r17, %r19
	mulhdu %r19, %r17, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r3, 0(%r10)
	mulld %r22, %r3, %r12
	addi %r22, %r22, 2
	mulld %r22, %r22, %r12
	mulld %r0, %r20, %r22
	mulld %r22, %r0, %r3
	mulhdu %r19, %r0, %r3
	addc %r22, %r22, %r20
	addze %r22, %r19
	addi %r14, %r8, 0
	addi %r15, %r7, 0
	addi %r3, %r10, 0
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicr %r16, %r16, 62, 1
	rldicl %r16, %r16, 2, 62
	cmpldi %cr0, %r16, 0
	beq %cr0, 2101f
2103:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r3, %r3, 8
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 2103b
	b 2102f
2101:
2102:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2104f
2106:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	ld %r19, 16(%r14)
	addc %r18, %r18, %r19
	ld %r19, 16(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 16(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 8(%r14)
	ld %r19, 24(%r14)
	addc %r18, %r18, %r19
	ld %r19, 24(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 24(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 16(%r14)
	ld %r19, 32(%r14)
	addc %r18, %r18, %r19
	ld %r19, 32(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 32(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r3, %r3, 32
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 2106b
	b 2105f
2104:
2105:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	li %r19, 0
	addze %r19, %r19
	addc %r18, %r18, %r22
	addze %r19, %r19
	std %r18, 0(%r14)
	std %r19, 8(%r14)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2100b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2107:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2107b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2108:
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
	bne %cr0, 2108b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
	li %r3, 0
2109:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2109b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r20, %r3, %r0
	addi %r3, %r10, 0
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	rldicl %r0, %r11, 63, 1
	rldicr %r0, %r0, 3, 60
	add %r3, %r3, %r0
	ld %r3, 0(%r3)
	lis %r4, 4369
	ori %r4, %r4, 4369
	rldicr %r4, %r4, 32, 31
	oris %r4, %r4, 4369
	ori %r4, %r4, 4369
	and %r3, %r3, %r4
	rldicl %r4, %r3, 63, 1
	li %r0, 1
	and %r0, %r3, %r0
	or %r3, %r4, %r0
	li %r0, 0
	subf %r3, %r3, %r0
	rldicl %r3, %r3, 1, 63
	subf %r3, %r3, %r0
	and %r20, %r20, %r3
	or %r23, %r23, %r20
	li %r3, 1
	and %r3, %r3, %r23
	ld %r14, 0(%r21)
	ld %r15, 8(%r21)
	ld %r16, 16(%r21)
	ld %r17, 24(%r21)
	ld %r18, 32(%r21)
	ld %r19, 40(%r21)
	ld %r20, 48(%r21)
	ld %r22, 56(%r21)
	ld %r23, 64(%r21)
	ld %r24, 72(%r21)
	ld %r25, 80(%r21)
	ld %r26, 88(%r21)
	ld %r27, 96(%r21)
	ld %r28, 104(%r21)
	ld %r29, 112(%r21)
	ld %r30, 120(%r21)
	ld %r31, 128(%r21)
	ld %r21, 136(%r21)
	addi %r1, %r1, 176
	blr
