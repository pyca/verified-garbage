// The functions of `src/rsa.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_public_precompute:
	std %r14, 128(%r7)
	std %r15, 136(%r7)
	std %r16, 144(%r7)
	std %r17, 152(%r7)
	std %r18, 160(%r7)
	std %r19, 168(%r7)
	std %r20, 176(%r7)
	std %r22, 184(%r7)
	std %r21, 192(%r7)
	addi %r21, %r7, 0
	addi %r19, %r3, 0
	addi %r12, %r5, 0
	addi %r11, %r6, 7
	rldicl %r11, %r11, 61, 3
	std %r11, 48(%r21)
	rldicr %r4, %r11, 3, 60
	addi %r4, %r4, 16
	addi %r10, %r21, 256
	add %r5, %r10, %r4
	add %r8, %r5, %r4
	add %r9, %r8, %r4
	rldicr %r11, %r11, 1, 62
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
20:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 20b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
21:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 21b
	add %r15, %r12, %r6
	addi %r15, %r15, -1
	lbz %r0, 0(%r15)
	li %r18, 1
	and %r0, %r0, %r18
	xor %r0, %r0, %r18
	lbz %r15, 0(%r12)
	cmpldi %cr0, %r15, 0
	beq %cr0, 22f
	b 23f
22:
	li %r0, 1
23:
	addi %r16, %r6, -64
	cmpldi %cr0, %r16, 0
	beq %cr0, 24f
	b 25f
24:
	rldicl %r15, %r15, 57, 7
	xor %r15, %r15, %r18
	or %r0, %r0, %r15
25:
	cmpldi %cr0, %r0, 0
	beq %cr0, 26f
	addi %r14, %r19, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
28:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 28b
	rldicl %r17, %r11, 63, 1
	li %r0, 0
29:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 29b
	li %r3, 0
	b 27f
26:
	rldicr %r14, %r11, 2, 61
	add %r14, %r14, %r10
	addi %r14, %r14, -16
	ld %r15, 8(%r14)
	ld %r16, 0(%r14)
	li %r6, 1
	li %r20, 0
	li %r22, 1
	li %r17, 63
210:
	rldicl %r3, %r15, 1, 63
	xor %r3, %r3, %r22
	subf %r3, %r3, %r20
	and %r0, %r15, %r3
	add %r15, %r15, %r0
	and %r0, %r6, %r3
	add %r6, %r6, %r0
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 210b
	mulhdu %r0, %r16, %r6
	add %r15, %r15, %r0
	mulld %r16, %r16, %r6
	addi %r3, %r14, -8
	ld %r3, 0(%r3)
	mulhdu %r3, %r3, %r6
	add %r16, %r16, %r3
	std %r6, 0(%r9)
	std %r15, 8(%r9)
	std %r16, 24(%r9)
	ld %r7, 8(%r9)
	li %r20, 0
	addi %r16, %r20, -1
	subf %r15, %r7, %r16
	li %r18, 0
	li %r17, 64
211:
	rldicl %r3, %r15, 1, 63
	add %r15, %r15, %r15
	rldicl %r0, %r16, 1, 63
	add %r15, %r15, %r0
	add %r16, %r16, %r16
	subfc %r0, %r7, %r15
	addze %r12, %r20
	or %r3, %r3, %r12
	subf %r12, %r3, %r20
	and %r0, %r7, %r12
	subf %r15, %r0, %r15
	add %r18, %r18, %r18
	add %r18, %r18, %r3
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 211b
	std %r18, 16(%r9)
	addi %r14, %r5, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
212:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 212b
	rldicr %r14, %r11, 2, 61
	add %r14, %r14, %r5
	addi %r14, %r14, -8
	li %r0, 1
	std %r0, 0(%r14)
	rldicl %r4, %r11, 63, 1
	addi %r4, %r4, 1
213:
	rldicr %r14, %r11, 2, 61
	add %r14, %r14, %r5
	addi %r14, %r14, -24
	ld %r0, 16(%r14)
	ld %r3, 8(%r14)
	ld %r12, 0(%r14)
	ld %r6, 0(%r9)
	ld %r7, 8(%r9)
	ld %r18, 16(%r9)
	mulld %r15, %r0, %r6
	mulhdu %r16, %r3, %r6
	add %r15, %r15, %r16
	mulld %r16, %r3, %r6
	mulhdu %r0, %r12, %r6
	add %r16, %r16, %r0
	subf %r22, %r15, %r7
	li %r20, 0
	mulld %r0, %r18, %r15
	mulhdu %r3, %r18, %r15
	addc %r0, %r0, %r16
	adde %r3, %r3, %r15
	addi %r3, %r3, 1
	mulld %r12, %r3, %r7
	subf %r12, %r12, %r16
	subfc %r17, %r12, %r0
	subfe %r17, %r20, %r20
	add %r3, %r3, %r17
	and %r17, %r17, %r7
	add %r12, %r12, %r17
	subfc %r17, %r7, %r12
	addze %r18, %r3
	subf %r12, %r22, %r20
	or %r12, %r12, %r22
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	or %r18, %r18, %r12
	ld %r0, 0(%r14)
	mulld %r0, %r0, %r6
	addi %r3, %r14, -8
	ld %r3, 0(%r3)
	mulhdu %r3, %r3, %r6
	add %r0, %r0, %r3
	ld %r22, 24(%r9)
	mulld %r12, %r18, %r22
	mulhdu %r3, %r18, %r22
	mulld %r17, %r18, %r7
	mulhdu %r6, %r18, %r7
	addc %r17, %r17, %r3
	addze %r6, %r6
	subfc %r0, %r12, %r0
	subfe %r16, %r17, %r16
	subfe %r15, %r6, %r15
	rldicl %r3, %r15, 1, 63
	subf %r18, %r3, %r18
	subf %r3, %r3, %r20
	and %r12, %r22, %r3
	and %r17, %r7, %r3
	addc %r0, %r0, %r12
	adde %r16, %r16, %r17
	addze %r15, %r15
	rldicl %r3, %r15, 1, 63
	subf %r18, %r3, %r18
	addi %r14, %r5, 0
	addi %r15, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r3, 0
	li %r22, 1
	li %r16, 0
	addi %r6, %r20, -1
214:
	ld %r0, 0(%r15)
	mulld %r12, %r0, %r18
	mulhdu %r0, %r0, %r18
	addc %r12, %r12, %r3
	addze %r3, %r0
	ld %r7, 0(%r14)
	addc %r0, %r22, %r6
	subfe %r12, %r12, %r16
	addze %r22, %r20
	std %r12, 0(%r14)
	addi %r16, %r7, 0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 214b
	addc %r0, %r22, %r6
	subfe %r12, %r3, %r16
	std %r12, 0(%r14)
	rldicr %r14, %r11, 2, 61
	add %r14, %r14, %r5
	ld %r0, 0(%r14)
	rldicl %r0, %r0, 1, 63
	subf %r12, %r0, %r20
	addi %r14, %r5, 0
	addi %r15, %r10, 0
	rldicl %r17, %r11, 63, 1
	addc %r0, %r20, %r20
215:
	ld %r0, 0(%r15)
	and %r0, %r0, %r12
	ld %r3, 0(%r14)
	adde %r3, %r3, %r0
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 215b
	ld %r3, 0(%r14)
	adde %r3, %r3, %r20
	std %r3, 0(%r14)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 213b
	addi %r14, %r19, 0
	addi %r15, %r10, 0
	rldicl %r17, %r11, 63, 1
216:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 216b
	addi %r15, %r5, 0
	rldicl %r17, %r11, 63, 1
217:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 217b
	li %r3, 1
27:
	ld %r14, 128(%r21)
	ld %r15, 136(%r21)
	ld %r16, 144(%r21)
	ld %r17, 152(%r21)
	ld %r18, 160(%r21)
	ld %r19, 168(%r21)
	ld %r20, 176(%r21)
	ld %r22, 184(%r21)
	ld %r21, 192(%r21)
	blr

vg_rsa_private_precompute:
	addi %r11, %r1, 96
	ld %r11, 0(%r11)
	std %r14, 112(%r11)
	std %r15, 120(%r11)
	std %r16, 128(%r11)
	std %r17, 136(%r11)
	std %r18, 144(%r11)
	std %r19, 152(%r11)
	std %r20, 160(%r11)
	std %r21, 168(%r11)
	std %r22, 176(%r11)
	std %r24, 184(%r11)
	std %r25, 192(%r11)
	std %r26, 200(%r11)
	std %r27, 208(%r11)
	std %r28, 216(%r11)
	std %r29, 224(%r11)
	std %r30, 232(%r11)
	std %r31, 240(%r11)
	std %r23, 248(%r11)
	addi %r23, %r11, 0
	std %r3, 0(%r23)
	std %r5, 8(%r23)
	std %r6, 16(%r23)
	std %r3, 24(%r23)
	std %r7, 32(%r23)
	std %r8, 40(%r23)
	std %r9, 48(%r23)
	std %r10, 56(%r23)
	std %r3, 80(%r23)
	addi %r14, %r3, 0
	addi %r11, %r6, 7
	rldicl %r11, %r11, 61, 3
	rldicr %r11, %r11, 1, 62
	rldicl %r17, %r11, 63, 1
	li %r0, 0
20:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 20b
	addi %r4, %r6, 7
	rldicl %r4, %r4, 61, 3
	rldicr %r4, %r4, 1, 62
	addi %r10, %r23, 256
	addi %r21, %r10, 0
	rldicr %r29, %r4, 3, 60
	addi %r29, %r29, 16
	rldicr %r11, %r4, 1, 62
	addi %r27, %r10, 0
	addi %r28, %r29, 0
	rldicr %r5, %r29, 3, 60
	add %r5, %r10, %r5
	std %r5, 96(%r23)
	ld %r3, 40(%r23)
	addi %r4, %r3, 7
	rldicl %r4, %r4, 61, 3
	addi %r0, %r4, -2
	rldicl %r0, %r0, 1, 63
	add %r4, %r4, %r0
	rldicr %r3, %r4, 3, 60
	addi %r3, %r3, 16
	rldicr %r3, %r3, 3, 60
	add %r0, %r3, %r3
	add %r3, %r3, %r0
	addi %r3, %r3, 256
	add %r5, %r5, %r3
	std %r5, 104(%r23)
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
	li %r3, 1
	subf %r0, %r3, %r0
21:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 21b
	ld %r12, 8(%r23)
	ld %r6, 16(%r23)
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
22:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 22b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
23:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 23b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r21, 0
	ld %r12, 32(%r23)
	ld %r6, 40(%r23)
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
24:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 24b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
25:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 25b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r21, 0
	ld %r12, 48(%r23)
	ld %r6, 56(%r23)
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
26:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 26b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
27:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 27b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r21, 0
	ld %r12, 24(%r23)
	ld %r6, 16(%r23)
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
28:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 28b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
29:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 29b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r21, 0
	ld %r12, 80(%r23)
	ld %r6, 40(%r23)
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
210:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 210b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
211:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 211b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r21, 0
	ld %r5, 40(%r23)
	addi %r5, %r5, 7
	rldicl %r5, %r5, 61, 3
	ld %r7, 56(%r23)
	addi %r7, %r7, 7
	rldicl %r7, %r7, 61, 3
	ld %r12, 8(%r23)
	ld %r6, 16(%r23)
	add %r15, %r12, %r6
	addi %r15, %r15, -1
	lbz %r0, 0(%r15)
	li %r18, 1
	and %r0, %r0, %r18
	xor %r0, %r0, %r18
	lbz %r15, 0(%r12)
	cmpldi %cr0, %r15, 0
	beq %cr0, 212f
	b 213f
212:
	li %r0, 1
213:
	addi %r16, %r6, -64
	cmpldi %cr0, %r16, 0
	beq %cr0, 214f
	b 215f
214:
	rldicl %r15, %r15, 57, 7
	xor %r15, %r15, %r18
	or %r0, %r0, %r15
215:
	rldicl %r3, %r0, 63, 1
	li %r4, 1
	and %r4, %r0, %r4
	or %r3, %r3, %r4
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	li %r4, 0
	subf %r26, %r3, %r4
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
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
216:
	lwz %r0, 0(%r14)
	lwz %r3, 0(%r16)
	subf %r0, %r3, %r0
	subf %r0, %r20, %r0
	stw %r0, 0(%r15)
	rldicl %r20, %r0, 1, 63
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 216b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r21, 0
	and %r26, %r26, %r20
	addi %r8, %r10, 0
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
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
217:
	lwz %r0, 0(%r14)
	lwz %r3, 0(%r16)
	subf %r0, %r3, %r0
	subf %r0, %r20, %r0
	stw %r0, 0(%r15)
	rldicl %r20, %r0, 1, 63
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 217b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r21, 0
	and %r26, %r26, %r20
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
218:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 218b
	addi %r8, %r10, 0
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
219:
	ld %r12, 0(%r8)
	addi %r14, %r9, 0
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r16, %r7, 0
	li %r3, 0
220:
	ld %r0, 0(%r15)
	mulld %r4, %r0, %r12
	mulhdu %r0, %r0, %r12
	ld %r6, 0(%r14)
	addc %r4, %r4, %r6
	addze %r0, %r0
	addc %r4, %r4, %r3
	addze %r3, %r0
	std %r4, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 220b
	std %r3, 0(%r14)
	addi %r8, %r8, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 219b
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
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
221:
	lwz %r0, 0(%r14)
	lwz %r3, 0(%r16)
	subf %r0, %r3, %r0
	subf %r0, %r20, %r0
	stw %r0, 0(%r15)
	rldicl %r20, %r0, 1, 63
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 221b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r21, 0
	addi %r24, %r20, 0
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
222:
	lwz %r0, 0(%r14)
	lwz %r3, 0(%r16)
	subf %r0, %r3, %r0
	subf %r0, %r20, %r0
	stw %r0, 0(%r15)
	rldicl %r20, %r0, 1, 63
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 222b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r21, 0
	or %r0, %r24, %r20
	li %r3, 0
	addi %r3, %r3, -1
	xor %r0, %r0, %r3
	and %r26, %r26, %r0
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
223:
	ld %r0, 0(%r14)
	and %r0, %r0, %r26
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 223b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	ld %r0, 0(%r14)
	li %r3, 0
	addi %r3, %r3, -1
	xor %r3, %r3, %r26
	li %r4, 3
	and %r3, %r3, %r4
	or %r0, %r0, %r3
	std %r0, 0(%r14)
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
224:
	ld %r0, 0(%r14)
	and %r0, %r0, %r26
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 224b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	ld %r0, 0(%r14)
	li %r3, 0
	addi %r3, %r3, -1
	xor %r3, %r3, %r26
	li %r4, 3
	and %r3, %r3, %r4
	or %r0, %r0, %r3
	std %r0, 0(%r14)
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
225:
	ld %r0, 0(%r14)
	and %r0, %r0, %r26
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 225b
	ld %r19, 0(%r23)
	ld %r12, 8(%r23)
	ld %r6, 16(%r23)
	addi %r21, %r23, 0
	addi %r11, %r6, 7
	rldicl %r11, %r11, 61, 3
	rldicr %r4, %r11, 3, 60
	addi %r4, %r4, 16
	addi %r10, %r21, 256
	add %r5, %r10, %r4
	add %r8, %r5, %r4
	add %r9, %r8, %r4
	rldicr %r11, %r11, 1, 62
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
226:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 226b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
227:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 227b
	add %r15, %r12, %r6
	addi %r15, %r15, -1
	lbz %r0, 0(%r15)
	li %r18, 1
	and %r0, %r0, %r18
	xor %r0, %r0, %r18
	lbz %r15, 0(%r12)
	cmpldi %cr0, %r15, 0
	beq %cr0, 228f
	b 229f
228:
	li %r0, 1
229:
	addi %r16, %r6, -64
	cmpldi %cr0, %r16, 0
	beq %cr0, 230f
	b 231f
230:
	rldicl %r15, %r15, 57, 7
	xor %r15, %r15, %r18
	or %r0, %r0, %r15
231:
	cmpldi %cr0, %r0, 0
	beq %cr0, 232f
	addi %r14, %r19, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
234:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 234b
	rldicl %r17, %r11, 63, 1
	li %r0, 0
235:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 235b
	li %r3, 0
	b 233f
232:
	rldicr %r14, %r11, 2, 61
	add %r14, %r14, %r10
	addi %r14, %r14, -16
	ld %r15, 8(%r14)
	ld %r16, 0(%r14)
	li %r6, 1
	li %r20, 0
	li %r22, 1
	li %r17, 63
236:
	rldicl %r3, %r15, 1, 63
	xor %r3, %r3, %r22
	subf %r3, %r3, %r20
	and %r0, %r15, %r3
	add %r15, %r15, %r0
	and %r0, %r6, %r3
	add %r6, %r6, %r0
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 236b
	mulhdu %r0, %r16, %r6
	add %r15, %r15, %r0
	mulld %r16, %r16, %r6
	addi %r3, %r14, -8
	ld %r3, 0(%r3)
	mulhdu %r3, %r3, %r6
	add %r16, %r16, %r3
	std %r6, 0(%r9)
	std %r15, 8(%r9)
	std %r16, 24(%r9)
	ld %r7, 8(%r9)
	li %r20, 0
	addi %r16, %r20, -1
	subf %r15, %r7, %r16
	li %r18, 0
	li %r17, 64
237:
	rldicl %r3, %r15, 1, 63
	add %r15, %r15, %r15
	rldicl %r0, %r16, 1, 63
	add %r15, %r15, %r0
	add %r16, %r16, %r16
	subfc %r0, %r7, %r15
	addze %r12, %r20
	or %r3, %r3, %r12
	subf %r12, %r3, %r20
	and %r0, %r7, %r12
	subf %r15, %r0, %r15
	add %r18, %r18, %r18
	add %r18, %r18, %r3
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 237b
	std %r18, 16(%r9)
	addi %r14, %r5, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
238:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 238b
	rldicr %r14, %r11, 2, 61
	add %r14, %r14, %r5
	addi %r14, %r14, -8
	li %r0, 1
	std %r0, 0(%r14)
	rldicl %r4, %r11, 63, 1
	addi %r4, %r4, 1
239:
	rldicr %r14, %r11, 2, 61
	add %r14, %r14, %r5
	addi %r14, %r14, -24
	ld %r0, 16(%r14)
	ld %r3, 8(%r14)
	ld %r12, 0(%r14)
	ld %r6, 0(%r9)
	ld %r7, 8(%r9)
	ld %r18, 16(%r9)
	mulld %r15, %r0, %r6
	mulhdu %r16, %r3, %r6
	add %r15, %r15, %r16
	mulld %r16, %r3, %r6
	mulhdu %r0, %r12, %r6
	add %r16, %r16, %r0
	subf %r22, %r15, %r7
	li %r20, 0
	mulld %r0, %r18, %r15
	mulhdu %r3, %r18, %r15
	addc %r0, %r0, %r16
	adde %r3, %r3, %r15
	addi %r3, %r3, 1
	mulld %r12, %r3, %r7
	subf %r12, %r12, %r16
	subfc %r17, %r12, %r0
	subfe %r17, %r20, %r20
	add %r3, %r3, %r17
	and %r17, %r17, %r7
	add %r12, %r12, %r17
	subfc %r17, %r7, %r12
	addze %r18, %r3
	subf %r12, %r22, %r20
	or %r12, %r12, %r22
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	or %r18, %r18, %r12
	ld %r0, 0(%r14)
	mulld %r0, %r0, %r6
	addi %r3, %r14, -8
	ld %r3, 0(%r3)
	mulhdu %r3, %r3, %r6
	add %r0, %r0, %r3
	ld %r22, 24(%r9)
	mulld %r12, %r18, %r22
	mulhdu %r3, %r18, %r22
	mulld %r17, %r18, %r7
	mulhdu %r6, %r18, %r7
	addc %r17, %r17, %r3
	addze %r6, %r6
	subfc %r0, %r12, %r0
	subfe %r16, %r17, %r16
	subfe %r15, %r6, %r15
	rldicl %r3, %r15, 1, 63
	subf %r18, %r3, %r18
	subf %r3, %r3, %r20
	and %r12, %r22, %r3
	and %r17, %r7, %r3
	addc %r0, %r0, %r12
	adde %r16, %r16, %r17
	addze %r15, %r15
	rldicl %r3, %r15, 1, 63
	subf %r18, %r3, %r18
	addi %r14, %r5, 0
	addi %r15, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r3, 0
	li %r22, 1
	li %r16, 0
	addi %r6, %r20, -1
240:
	ld %r0, 0(%r15)
	mulld %r12, %r0, %r18
	mulhdu %r0, %r0, %r18
	addc %r12, %r12, %r3
	addze %r3, %r0
	ld %r7, 0(%r14)
	addc %r0, %r22, %r6
	subfe %r12, %r12, %r16
	addze %r22, %r20
	std %r12, 0(%r14)
	addi %r16, %r7, 0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 240b
	addc %r0, %r22, %r6
	subfe %r12, %r3, %r16
	std %r12, 0(%r14)
	rldicr %r14, %r11, 2, 61
	add %r14, %r14, %r5
	ld %r0, 0(%r14)
	rldicl %r0, %r0, 1, 63
	subf %r12, %r0, %r20
	addi %r14, %r5, 0
	addi %r15, %r10, 0
	rldicl %r17, %r11, 63, 1
	addc %r0, %r20, %r20
241:
	ld %r0, 0(%r15)
	and %r0, %r0, %r12
	ld %r3, 0(%r14)
	adde %r3, %r3, %r0
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 241b
	ld %r3, 0(%r14)
	adde %r3, %r3, %r20
	std %r3, 0(%r14)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 239b
	addi %r14, %r19, 0
	addi %r15, %r10, 0
	rldicl %r17, %r11, 63, 1
242:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 242b
	addi %r15, %r5, 0
	rldicl %r17, %r11, 63, 1
243:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 243b
	li %r3, 1
233:
	addi %r14, %r27, 0
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	rldicr %r11, %r11, 1, 62
	rldicl %r17, %r11, 63, 1
	li %r0, 0
244:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 244b
	rldicl %r11, %r11, 63, 1
	addi %r14, %r27, 0
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	rldicr %r3, %r11, 2, 61
	add %r15, %r19, %r3
	rldicl %r17, %r11, 63, 1
245:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 245b
	ld %r30, 0(%r23)
	ld %r3, 16(%r23)
	addi %r3, %r3, 7
	rldicl %r3, %r3, 61, 3
	rldicr %r3, %r3, 4, 59
	add %r30, %r30, %r3
	ld %r3, 40(%r23)
	addi %r4, %r3, 7
	rldicl %r4, %r4, 61, 3
	addi %r0, %r4, -2
	rldicl %r0, %r0, 1, 63
	add %r4, %r4, %r0
	ld %r3, 96(%r23)
	addi %r10, %r3, 256
	addi %r21, %r10, 0
	rldicr %r29, %r4, 3, 60
	addi %r29, %r29, 16
	rldicr %r11, %r4, 1, 62
	addi %r14, %r10, 0
	addi %r15, %r27, 0
	add %r15, %r15, %r28
	add %r15, %r15, %r28
	add %r15, %r15, %r28
	add %r15, %r15, %r28
	rldicl %r17, %r11, 63, 1
246:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 246b
	ld %r0, 0(%r10)
	ld %r12, 0(%r10)
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	li %r3, 0
	subf %r12, %r12, %r3
	rldicr %r12, %r12, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r5, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
247:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 247b
	li %r0, 1
	stw %r0, 0(%r5)
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
248:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 248b
	addi %r25, %r27, 0
	add %r25, %r25, %r28
	add %r25, %r25, %r28
	add %r25, %r25, %r28
	add %r25, %r25, %r28
	add %r25, %r25, %r28
	add %r25, %r25, %r28
	rldicl %r31, %r28, 60, 4
	addi %r31, %r31, -1
249:
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r25, 0
	rldicl %r17, %r11, 63, 1
250:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 250b
	addi %r25, %r15, 0
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
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
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r4, %r11, 0
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r6, %r10, 0
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	addi %r7, %r10, 0
	add %r7, %r7, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r4, %r11, 0
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
251:
	lwz %r0, 0(%r14)
	lwz %r3, 0(%r16)
	subf %r0, %r3, %r0
	subf %r0, %r20, %r0
	stw %r0, 0(%r15)
	rldicl %r20, %r0, 1, 63
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 251b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r21, 0
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r24, 0
252:
	lwz %r0, 0(%r15)
	lwz %r3, 0(%r16)
	and %r3, %r3, %r20
	add %r0, %r0, %r3
	add %r0, %r0, %r24
	stw %r0, 0(%r15)
	rldicl %r24, %r0, 32, 32
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 252b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
253:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 253b
	rldicl %r3, %r11, 63, 1
	subf %r31, %r3, %r31
	addi %r3, %r31, -1
	rldicl %r3, %r3, 1, 63
	li %r0, 1
	xor %r3, %r3, %r0
	cmpldi %cr0, %r3, 0
	bne %cr0, 249b
	rldicl %r3, %r28, 60, 4
	addi %r3, %r3, -1
	add %r31, %r31, %r3
	subf %r3, %r31, %r11
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 254f
	b 255f
254:
256:
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r6, %r10, 0
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	addi %r7, %r10, 0
	add %r7, %r7, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r4, %r11, 0
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	rldicl %r3, %r11, 63, 1
	subf %r31, %r3, %r31
	subf %r3, %r31, %r11
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 256b
255:
	addi %r14, %r10, 0
	add %r14, %r14, %r29
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
	rldicl %r17, %r11, 63, 1
257:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 257b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
258:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 258b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
259:
	lwz %r0, 0(%r14)
	lwz %r3, 0(%r16)
	subf %r0, %r3, %r0
	subf %r0, %r20, %r0
	stw %r0, 0(%r15)
	rldicl %r20, %r0, 1, 63
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 259b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r21, 0
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r24, 0
260:
	lwz %r0, 0(%r15)
	lwz %r3, 0(%r16)
	and %r3, %r3, %r20
	add %r0, %r0, %r3
	add %r0, %r0, %r24
	stw %r0, 0(%r15)
	rldicl %r24, %r0, 32, 32
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 260b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
261:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 261b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
262:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 262b
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	rldicl %r4, %r11, 63, 1
	subf %r3, %r31, %r4
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 263f
	rldicl %r4, %r11, 63, 1
	subf %r3, %r31, %r4
	rldicr %r3, %r3, 6, 57
	add %r4, %r3, %r4
265:
	li %r20, 0
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	rldicl %r17, %r11, 63, 1
266:
	ld %r0, 0(%r15)
	rldicr %r3, %r0, 1, 62
	add %r3, %r3, %r20
	rldicl %r20, %r0, 1, 63
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 266b
	std %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
267:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 267b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
268:
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
	bne %cr0, 268b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 265b
	li %r24, 6
269:
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	addi %r4, %r11, 0
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
270:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 270b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
271:
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
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
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
	beq %cr0, 272f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 274f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 276f
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
	b 277f
276:
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
277:
	b 275f
274:
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
275:
	b 273f
272:
273:
	cmplwi %cr0, %r17, 0
	beq %cr0, 278f
280:
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
	bne %cr0, 280b
	b 279f
278:
279:
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
	bne %cr0, 271b
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
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
281:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 281b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
282:
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
	bne %cr0, 282b
	addi %r24, %r24, -1
	cmpldi %cr0, %r24, 0
	bne %cr0, 269b
	b 264f
263:
	subf %r4, %r31, %r11
	rldicr %r4, %r4, 6, 57
	cmpldi %cr0, %r4, 0
	bne %cr0, 283f
	b 284f
283:
285:
	li %r20, 0
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	rldicl %r17, %r11, 63, 1
286:
	ld %r0, 0(%r15)
	rldicr %r3, %r0, 1, 62
	add %r3, %r3, %r20
	rldicl %r20, %r0, 1, 63
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 286b
	std %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
287:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 287b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
288:
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
	bne %cr0, 288b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 285b
284:
264:
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
289:
	ld %r0, 0(%r15)
	and %r0, %r0, %r26
	std %r0, 0(%r30)
	addi %r15, %r15, 8
	addi %r30, %r30, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 289b
	ld %r3, 56(%r23)
	addi %r4, %r3, 7
	rldicl %r4, %r4, 61, 3
	addi %r0, %r4, -2
	rldicl %r0, %r0, 1, 63
	add %r4, %r4, %r0
	ld %r3, 104(%r23)
	addi %r10, %r3, 256
	addi %r21, %r10, 0
	rldicr %r29, %r4, 3, 60
	addi %r29, %r29, 16
	rldicr %r11, %r4, 1, 62
	addi %r14, %r10, 0
	addi %r15, %r27, 0
	add %r15, %r15, %r28
	add %r15, %r15, %r28
	add %r15, %r15, %r28
	add %r15, %r15, %r28
	add %r15, %r15, %r28
	rldicl %r17, %r11, 63, 1
290:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 290b
	ld %r0, 0(%r10)
	ld %r12, 0(%r10)
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	li %r3, 0
	subf %r12, %r12, %r3
	rldicr %r12, %r12, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r5, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
291:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 291b
	li %r0, 1
	stw %r0, 0(%r5)
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
292:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 292b
	addi %r25, %r27, 0
	add %r25, %r25, %r28
	add %r25, %r25, %r28
	add %r25, %r25, %r28
	add %r25, %r25, %r28
	add %r25, %r25, %r28
	add %r25, %r25, %r28
	rldicl %r31, %r28, 60, 4
	addi %r31, %r31, -1
293:
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r25, 0
	rldicl %r17, %r11, 63, 1
294:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 294b
	addi %r25, %r15, 0
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
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
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r4, %r11, 0
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r6, %r10, 0
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	addi %r7, %r10, 0
	add %r7, %r7, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r4, %r11, 0
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
295:
	lwz %r0, 0(%r14)
	lwz %r3, 0(%r16)
	subf %r0, %r3, %r0
	subf %r0, %r20, %r0
	stw %r0, 0(%r15)
	rldicl %r20, %r0, 1, 63
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 295b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r21, 0
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r24, 0
296:
	lwz %r0, 0(%r15)
	lwz %r3, 0(%r16)
	and %r3, %r3, %r20
	add %r0, %r0, %r3
	add %r0, %r0, %r24
	stw %r0, 0(%r15)
	rldicl %r24, %r0, 32, 32
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 296b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
297:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 297b
	rldicl %r3, %r11, 63, 1
	subf %r31, %r3, %r31
	addi %r3, %r31, -1
	rldicl %r3, %r3, 1, 63
	li %r0, 1
	xor %r3, %r3, %r0
	cmpldi %cr0, %r3, 0
	bne %cr0, 293b
	rldicl %r3, %r28, 60, 4
	addi %r3, %r3, -1
	add %r31, %r31, %r3
	subf %r3, %r31, %r11
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 298f
	b 299f
298:
2100:
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r6, %r10, 0
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	addi %r7, %r10, 0
	add %r7, %r7, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r4, %r11, 0
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	rldicl %r3, %r11, 63, 1
	subf %r31, %r3, %r31
	subf %r3, %r31, %r11
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 2100b
299:
	addi %r14, %r10, 0
	add %r14, %r14, %r29
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
	rldicl %r17, %r11, 63, 1
2101:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2101b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2102:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2102b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2103:
	lwz %r0, 0(%r14)
	lwz %r3, 0(%r16)
	subf %r0, %r3, %r0
	subf %r0, %r20, %r0
	stw %r0, 0(%r15)
	rldicl %r20, %r0, 1, 63
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2103b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r21, 0
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r24, 0
2104:
	lwz %r0, 0(%r15)
	lwz %r3, 0(%r16)
	and %r3, %r3, %r20
	add %r0, %r0, %r3
	add %r0, %r0, %r24
	stw %r0, 0(%r15)
	rldicl %r24, %r0, 32, 32
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2104b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
2105:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2105b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
2106:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2106b
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	rldicl %r4, %r11, 63, 1
	subf %r3, %r31, %r4
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 2107f
	rldicl %r4, %r11, 63, 1
	subf %r3, %r31, %r4
	rldicr %r3, %r3, 6, 57
	add %r4, %r3, %r4
2109:
	li %r20, 0
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	rldicl %r17, %r11, 63, 1
2110:
	ld %r0, 0(%r15)
	rldicr %r3, %r0, 1, 62
	add %r3, %r3, %r20
	rldicl %r20, %r0, 1, 63
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2110b
	std %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2111:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2111b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2112:
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
	bne %cr0, 2112b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2109b
	li %r24, 6
2113:
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	addi %r4, %r11, 0
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
2114:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2114b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
2115:
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
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
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
	beq %cr0, 2116f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2118f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2120f
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
	b 2121f
2120:
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
2121:
	b 2119f
2118:
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
2119:
	b 2117f
2116:
2117:
	cmplwi %cr0, %r17, 0
	beq %cr0, 2122f
2124:
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
	bne %cr0, 2124b
	b 2123f
2122:
2123:
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
	bne %cr0, 2115b
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
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2125:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2125b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2126:
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
	bne %cr0, 2126b
	addi %r24, %r24, -1
	cmpldi %cr0, %r24, 0
	bne %cr0, 2113b
	b 2108f
2107:
	subf %r4, %r31, %r11
	rldicr %r4, %r4, 6, 57
	cmpldi %cr0, %r4, 0
	bne %cr0, 2127f
	b 2128f
2127:
2129:
	li %r20, 0
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	rldicl %r17, %r11, 63, 1
2130:
	ld %r0, 0(%r15)
	rldicr %r3, %r0, 1, 62
	add %r3, %r3, %r20
	rldicl %r20, %r0, 1, 63
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2130b
	std %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2131:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2131b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2132:
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
	bne %cr0, 2132b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2129b
2128:
2108:
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
2133:
	ld %r0, 0(%r15)
	and %r0, %r0, %r26
	std %r0, 0(%r30)
	addi %r15, %r15, 8
	addi %r30, %r30, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2133b
	ld %r14, 0(%r23)
	ld %r17, 16(%r23)
	addi %r17, %r17, 7
	rldicl %r17, %r17, 61, 3
	rldicr %r17, %r17, 1, 62
2134:
	ld %r0, 0(%r14)
	and %r0, %r0, %r26
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2134b
	li %r3, 1
	and %r3, %r3, %r26
	ld %r14, 112(%r23)
	ld %r15, 120(%r23)
	ld %r16, 128(%r23)
	ld %r17, 136(%r23)
	ld %r18, 144(%r23)
	ld %r19, 152(%r23)
	ld %r20, 160(%r23)
	ld %r21, 168(%r23)
	ld %r22, 176(%r23)
	ld %r24, 184(%r23)
	ld %r25, 192(%r23)
	ld %r26, 200(%r23)
	ld %r27, 208(%r23)
	ld %r28, 216(%r23)
	ld %r29, 224(%r23)
	ld %r30, 232(%r23)
	ld %r31, 240(%r23)
	ld %r23, 248(%r23)
	blr

vg_rsa_crt_values:
	addi %r11, %r1, 144
	ld %r11, 0(%r11)
	std %r14, 0(%r11)
	std %r15, 8(%r11)
	std %r16, 16(%r11)
	std %r17, 24(%r11)
	std %r18, 32(%r11)
	std %r19, 40(%r11)
	std %r20, 48(%r11)
	std %r21, 56(%r11)
	std %r22, 64(%r11)
	std %r23, 72(%r11)
	std %r24, 80(%r11)
	std %r29, 88(%r11)
	std %r30, 96(%r11)
	std %r31, 104(%r11)
	addi %r31, %r11, 0
	addi %r14, %r3, 0
	addi %r15, %r5, 0
	addi %r16, %r7, 0
	addi %r17, %r9, 0
	addi %r18, %r10, 0
	addi %r19, %r1, 96
	ld %r19, 0(%r19)
	addi %r20, %r1, 104
	ld %r20, 0(%r20)
	addi %r21, %r1, 112
	ld %r21, 0(%r21)
	addi %r22, %r1, 120
	ld %r22, 0(%r22)
	addi %r23, %r1, 128
	ld %r23, 0(%r23)
	addi %r24, %r1, 136
	ld %r24, 0(%r24)
	add %r11, %r9, %r10
	addi %r11, %r11, -1
	lbz %r0, 0(%r11)
	li %r12, 1
	and %r0, %r0, %r12
	xor %r0, %r0, %r12
	lbz %r11, 0(%r9)
	cmpldi %cr0, %r11, 0
	beq %cr0, 20f
	b 21f
20:
	li %r0, 1
21:
	addi %r12, %r10, -64
	cmpldi %cr0, %r12, 0
	beq %cr0, 22f
	b 23f
22:
	rldicl %r11, %r11, 57, 7
	li %r12, 1
	xor %r11, %r11, %r12
	or %r0, %r0, %r11
23:
	cmpldi %cr0, %r0, 0
	beq %cr0, 24f
	addi %r5, %r14, 0
	addi %r8, %r20, 0
	li %r0, 0
26:
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 26b
	addi %r5, %r15, 0
	addi %r8, %r22, 0
	li %r0, 0
27:
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 27b
	addi %r5, %r16, 0
	addi %r8, %r20, 0
	li %r0, 0
28:
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 28b
	li %r3, 0
	b 25f
24:
	addi %r29, %r18, 3
	rldicl %r29, %r29, 62, 2
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	li %r8, 25
	mulld %r8, %r8, %r30
	rldicl %r8, %r8, 62, 2
	addi %r5, %r31, 160
	li %r0, 0
29:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 29b
	addi %r6, %r17, 0
	addi %r8, %r18, 0
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
210:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 210b
	addi %r6, %r19, 0
	addi %r8, %r20, 0
	li %r5, 17
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
211:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 211b
	addi %r6, %r21, 0
	addi %r8, %r22, 0
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
212:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 212b
	addi %r6, %r23, 0
	addi %r8, %r24, 0
	li %r5, 24
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
213:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 213b
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 17
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 214f
	addi %r8, %r29, 0
216:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 216b
	b 215f
214:
	rldicl %r8, %r29, 63, 1
217:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 217b
215:
	li %r5, 17
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 136(%r31)
	addi %r12, %r20, 0
	addi %r12, %r12, 7
	rldicl %r12, %r12, 61, 3
	rldicr %r12, %r12, 1, 62
	subf %r0, %r12, %r29
	rldicl %r0, %r0, 1, 63
	cmpldi %cr0, %r0, 0
	beq %cr0, 218f
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
220:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 220b
	rldicr %r4, %r29, 5, 58
221:
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 222f
	addi %r8, %r29, 0
224:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 224b
	b 223f
222:
	rldicl %r8, %r29, 63, 1
225:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 225b
223:
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 226f
	addi %r8, %r29, 1
228:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 228b
	b 227f
226:
	rldicl %r8, %r29, 63, 1
229:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 229b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
227:
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 19
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 20
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 230f
	addi %r8, %r29, 1
	li %r9, 0
232:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 232b
	b 231f
230:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
233:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 233b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
231:
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 19
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 234f
	addi %r8, %r29, 1
236:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 236b
	b 235f
234:
	rldicl %r8, %r29, 63, 1
237:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 237b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
235:
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 221b
	b 219f
218:
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
238:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 238b
	rldicr %r4, %r29, 5, 58
239:
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 240f
	addi %r8, %r29, 0
242:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 242b
	b 241f
240:
	rldicl %r8, %r29, 63, 1
243:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 243b
241:
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicl %r8, %r12, 63, 1
244:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 244b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 19
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 20
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicl %r8, %r12, 63, 1
	subfc %r0, %r8, %r8
245:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 245b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 19
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicl %r8, %r12, 63, 1
246:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 246b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 239b
219:
	li %r6, 18
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 16
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 247f
	addi %r8, %r29, 0
249:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 249b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 140(%r31)
	b 248f
247:
	rldicl %r8, %r29, 63, 1
250:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 250b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 140(%r31)
248:
	li %r6, 19
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 10
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 251f
	addi %r8, %r29, 0
253:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 253b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 144(%r31)
	b 252f
251:
	rldicl %r8, %r29, 63, 1
254:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 254b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 144(%r31)
252:
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 16
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 255f
	addi %r8, %r29, 0
257:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 257b
	b 256f
255:
	rldicl %r8, %r29, 63, 1
258:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 258b
256:
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 17
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 259f
	addi %r8, %r29, 0
261:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 261b
	b 260f
259:
	rldicl %r8, %r29, 63, 1
262:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 262b
260:
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	li %r5, 15
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	stw %r0, 0(%r5)
	subf %r11, %r22, %r20
	rldicl %r0, %r11, 1, 63
	li %r3, 0
	subf %r0, %r0, %r3
	and %r11, %r11, %r0
	subf %r11, %r11, %r20
	addi %r11, %r11, 3
	rldicl %r11, %r11, 62, 2
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 8
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	addi %r10, %r11, 0
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
263:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 263b
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	rldicr %r8, %r8, 2, 61
	add %r6, %r6, %r8
	li %r0, 0
	stw %r0, 0(%r6)
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
264:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 264b
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	stw %r0, 0(%r5)
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 7
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
265:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 265b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	rldicr %r0, %r0, 1, 62
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r3, 0(%r5)
	or %r3, %r3, %r0
	stw %r3, 0(%r5)
	li %r10, 2
	mulld %r10, %r10, %r30
	add %r10, %r10, %r31
	addi %r10, %r10, 160
	ld %r0, 0(%r10)
	ld %r12, 0(%r10)
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	li %r3, 0
	subf %r12, %r12, %r3
	rldicr %r12, %r12, 32, 31
	rldicl %r12, %r12, 32, 32
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	std %r12, 40(%r5)
	addi %r10, %r11, 0
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
266:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 266b
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r11, 0(%r5)
	rldicr %r11, %r11, 63, 0
	rldicl %r11, %r11, 1, 63
	li %r0, 1
	xor %r11, %r11, %r0
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	li %r9, 0
267:
	lwz %r0, 0(%r7)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r6)
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 267b
	stw %r9, 0(%r5)
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r0, 0
268:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 268b
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	std %r0, 0(%r5)
	addi %r3, %r10, 1
	add %r0, %r3, %r3
	add %r3, %r3, %r0
	rldicr %r3, %r3, 15, 48
	add %r10, %r10, %r3
269:
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r4, 0(%r5)
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r5, 0(%r5)
	li %r3, 14
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r3, 0(%r3)
	li %r6, 1
	li %r7, 0
	li %r8, 0
	li %r9, 1
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	li %r4, 14
	mulld %r4, %r4, %r30
	add %r4, %r4, %r31
	addi %r4, %r4, 160
	std %r3, 0(%r4)
	std %r6, 8(%r4)
	std %r7, 16(%r4)
	std %r8, 24(%r4)
	std %r9, 32(%r4)
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 5
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r11, 14
	mulld %r11, %r11, %r30
	add %r11, %r11, %r31
	addi %r11, %r11, 160
	ld %r11, 8(%r11)
	li %r12, 14
	mulld %r12, %r12, %r30
	add %r12, %r12, %r31
	addi %r12, %r12, 160
	ld %r12, 16(%r12)
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	li %r9, 0
270:
	lwz %r0, 0(%r6)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r7)
	mulld %r3, %r12, %r3
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	rldicl %r3, %r0, 1, 63
	rldicr %r3, %r3, 32, 31
	subf %r9, %r3, %r9
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 270b
	lwz %r0, 0(%r6)
	rldicl %r4, %r0, 33, 31
	rldicr %r4, %r4, 32, 31
	subf %r0, %r4, %r0
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r7)
	rldicl %r4, %r3, 33, 31
	rldicr %r4, %r4, 32, 31
	subf %r3, %r4, %r3
	mulld %r3, %r12, %r3
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	rldicl %r3, %r0, 1, 63
	rldicr %r3, %r3, 32, 31
	subf %r9, %r3, %r9
	stw %r9, 4(%r5)
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 5
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r11, 14
	mulld %r11, %r11, %r30
	add %r11, %r11, %r31
	addi %r11, %r11, 160
	ld %r11, 24(%r11)
	li %r12, 14
	mulld %r12, %r12, %r30
	add %r12, %r12, %r31
	addi %r12, %r12, 160
	ld %r12, 32(%r12)
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	li %r9, 0
271:
	lwz %r0, 0(%r6)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r7)
	mulld %r3, %r12, %r3
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	rldicl %r3, %r0, 1, 63
	rldicr %r3, %r3, 32, 31
	subf %r9, %r3, %r9
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 271b
	lwz %r0, 0(%r6)
	rldicl %r4, %r0, 33, 31
	rldicr %r4, %r4, 32, 31
	subf %r0, %r4, %r0
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r7)
	rldicl %r4, %r3, 33, 31
	rldicr %r4, %r4, 32, 31
	subf %r3, %r4, %r3
	mulld %r3, %r12, %r3
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	rldicl %r3, %r0, 1, 63
	rldicr %r3, %r3, 32, 31
	subf %r9, %r3, %r9
	stw %r9, 4(%r5)
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
272:
	lwz %r0, 0(%r6)
	lwz %r3, 4(%r6)
	rldicl %r0, %r0, 34, 30
	rldicr %r3, %r3, 2, 61
	add %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 272b
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 12
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
273:
	lwz %r0, 0(%r6)
	lwz %r3, 4(%r6)
	rldicl %r0, %r0, 34, 30
	rldicr %r3, %r3, 2, 61
	add %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 273b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 7
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r11, 14
	mulld %r11, %r11, %r30
	add %r11, %r11, %r31
	addi %r11, %r11, 160
	ld %r11, 8(%r11)
	li %r12, 14
	mulld %r12, %r12, %r30
	add %r12, %r12, %r31
	addi %r12, %r12, 160
	ld %r12, 16(%r12)
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	li %r9, 0
274:
	lwz %r0, 0(%r6)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r7)
	mulld %r3, %r12, %r3
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	rldicl %r3, %r0, 1, 63
	rldicr %r3, %r3, 32, 31
	subf %r9, %r3, %r9
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 274b
	lwz %r0, 0(%r6)
	rldicl %r4, %r0, 33, 31
	rldicr %r4, %r4, 32, 31
	subf %r0, %r4, %r0
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r7)
	rldicl %r4, %r3, 33, 31
	rldicr %r4, %r4, 32, 31
	subf %r3, %r4, %r3
	mulld %r3, %r12, %r3
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	rldicl %r3, %r0, 1, 63
	rldicr %r3, %r3, 32, 31
	subf %r9, %r3, %r9
	stw %r9, 4(%r5)
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 7
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r11, 14
	mulld %r11, %r11, %r30
	add %r11, %r11, %r31
	addi %r11, %r11, 160
	ld %r11, 24(%r11)
	li %r12, 14
	mulld %r12, %r12, %r30
	add %r12, %r12, %r31
	addi %r12, %r12, 160
	ld %r12, 32(%r12)
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	li %r9, 0
275:
	lwz %r0, 0(%r6)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r7)
	mulld %r3, %r12, %r3
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	rldicl %r3, %r0, 1, 63
	rldicr %r3, %r3, 32, 31
	subf %r9, %r3, %r9
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 275b
	lwz %r0, 0(%r6)
	rldicl %r4, %r0, 33, 31
	rldicr %r4, %r4, 32, 31
	subf %r0, %r4, %r0
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r7)
	rldicl %r4, %r3, 33, 31
	rldicr %r4, %r4, 32, 31
	subf %r3, %r4, %r3
	mulld %r3, %r12, %r3
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	rldicl %r3, %r0, 1, 63
	rldicr %r3, %r3, 32, 31
	subf %r9, %r3, %r9
	stw %r9, 4(%r5)
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r3, 14
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r3, 40(%r3)
	lwz %r0, 0(%r5)
	mulld %r11, %r0, %r3
	rlwinm %r11, %r11, 0, 0, 31
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
276:
	lwz %r0, 0(%r7)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r6)
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 276b
	lwz %r0, 0(%r5)
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	addi %r6, %r6, 4
	li %r11, 1
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
277:
	lwz %r0, 0(%r7)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r6)
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 277b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
278:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 278b
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r0, 0
	subf %r9, %r9, %r0
279:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 279b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
280:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 280b
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r0, 0
	subf %r9, %r9, %r0
281:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 281b
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r3, 14
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r3, 40(%r3)
	lwz %r0, 0(%r5)
	mulld %r11, %r0, %r3
	rlwinm %r11, %r11, 0, 0, 31
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 12
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
282:
	lwz %r0, 0(%r7)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r6)
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 282b
	lwz %r0, 0(%r5)
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 12
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	addi %r6, %r6, 4
	li %r11, 1
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
283:
	lwz %r0, 0(%r7)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r6)
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 283b
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
284:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 284b
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 12
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r0, 0
	subf %r9, %r9, %r0
285:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 285b
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
286:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 286b
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 12
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r0, 0
	subf %r9, %r9, %r0
287:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 287b
	addi %r10, %r10, -32768
	rldicl %r3, %r10, 49, 15
	cmpldi %cr0, %r3, 0
	bne %cr0, 269b
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
288:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 288b
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	rldicr %r8, %r8, 2, 61
	add %r6, %r6, %r8
	lwz %r9, 0(%r6)
	rldicl %r9, %r9, 33, 31
	li %r0, 0
	subf %r9, %r9, %r0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
289:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 289b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
290:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 290b
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r0, 0
	subf %r9, %r9, %r0
291:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 291b
	addi %r3, %r10, 1
	add %r0, %r3, %r3
	add %r3, %r3, %r0
	add %r3, %r3, %r3
	rldicr %r3, %r3, 15, 48
	add %r10, %r10, %r3
292:
	li %r11, 1
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
293:
	lwz %r0, 0(%r7)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r6)
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 293b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
294:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 294b
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r0, 0
	subf %r9, %r9, %r0
295:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 295b
	addi %r10, %r10, -32768
	rldicl %r3, %r10, 49, 15
	cmpldi %cr0, %r3, 0
	bne %cr0, 292b
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
296:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 296b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 4
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
297:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 297b
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	rldicr %r8, %r8, 2, 61
	add %r6, %r6, %r8
	lwz %r9, 0(%r6)
	rldicl %r9, %r9, 33, 31
	li %r0, 0
	subf %r9, %r9, %r0
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
298:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 298b
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
299:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 299b
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
2100:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2100b
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 15
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2101f
	addi %r8, %r29, 0
2103:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2103b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 148(%r31)
	b 2102f
2101:
	rldicl %r8, %r29, 63, 1
2104:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2104b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 148(%r31)
2102:
	lwz %r0, 136(%r31)
	lwz %r3, 140(%r31)
	and %r0, %r0, %r3
	stw %r0, 152(%r31)
	lwz %r0, 152(%r31)
	lwz %r3, 144(%r31)
	and %r0, %r0, %r3
	stw %r0, 152(%r31)
	lwz %r0, 152(%r31)
	lwz %r3, 148(%r31)
	and %r0, %r0, %r3
	stw %r0, 152(%r31)
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 24
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2105f
	addi %r8, %r29, 0
2107:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2107b
	b 2106f
2105:
	rldicl %r8, %r29, 63, 1
2108:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2108b
2106:
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 17
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2109f
	addi %r8, %r29, 0
2111:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2111b
	b 2110f
2109:
	rldicl %r8, %r29, 63, 1
2112:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2112b
2110:
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	rldicl %r0, %r0, 63, 1
	rldicr %r0, %r0, 1, 62
	stw %r0, 0(%r5)
	addi %r12, %r20, 0
	addi %r12, %r12, 7
	rldicl %r12, %r12, 61, 3
	rldicr %r12, %r12, 1, 62
	subf %r0, %r12, %r29
	rldicl %r0, %r0, 1, 63
	cmpldi %cr0, %r0, 0
	beq %cr0, 2113f
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2115:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2115b
	rldicr %r4, %r29, 5, 58
2116:
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2117f
	addi %r8, %r29, 0
2119:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2119b
	b 2118f
2117:
	rldicl %r8, %r29, 63, 1
2120:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2120b
2118:
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2121f
	addi %r8, %r29, 1
2123:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2123b
	b 2122f
2121:
	rldicl %r8, %r29, 63, 1
2124:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2124b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
2122:
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 22
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 20
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2125f
	addi %r8, %r29, 1
	li %r9, 0
2127:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2127b
	b 2126f
2125:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2128:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2128b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
2126:
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 22
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2129f
	addi %r8, %r29, 1
2131:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2131b
	b 2130f
2129:
	rldicl %r8, %r29, 63, 1
2132:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2132b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
2130:
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2116b
	b 2114f
2113:
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2133:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2133b
	rldicr %r4, %r29, 5, 58
2134:
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2135f
	addi %r8, %r29, 0
2137:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2137b
	b 2136f
2135:
	rldicl %r8, %r29, 63, 1
2138:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2138b
2136:
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicl %r8, %r12, 63, 1
2139:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2139b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 22
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 20
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicl %r8, %r12, 63, 1
	subfc %r0, %r8, %r8
2140:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2140b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 22
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicl %r8, %r12, 63, 1
2141:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2141b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2134b
2114:
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 24
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2142f
	addi %r8, %r29, 0
2144:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2144b
	b 2143f
2142:
	rldicl %r8, %r29, 63, 1
2145:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2145b
2143:
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 16
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2146f
	addi %r8, %r29, 0
2148:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2148b
	b 2147f
2146:
	rldicl %r8, %r29, 63, 1
2149:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2149b
2147:
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	rldicl %r0, %r0, 63, 1
	rldicr %r0, %r0, 1, 62
	stw %r0, 0(%r5)
	addi %r12, %r22, 0
	addi %r12, %r12, 7
	rldicl %r12, %r12, 61, 3
	rldicr %r12, %r12, 1, 62
	subf %r0, %r12, %r29
	rldicl %r0, %r0, 1, 63
	cmpldi %cr0, %r0, 0
	beq %cr0, 2150f
	li %r5, 23
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2152:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2152b
	rldicr %r4, %r29, 5, 58
2153:
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2154f
	addi %r8, %r29, 0
2156:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2156b
	b 2155f
2154:
	rldicl %r8, %r29, 63, 1
2157:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2157b
2155:
	li %r5, 23
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2158f
	addi %r8, %r29, 1
2160:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2160b
	b 2159f
2158:
	rldicl %r8, %r29, 63, 1
2161:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2161b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
2159:
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 23
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 20
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2162f
	addi %r8, %r29, 1
	li %r9, 0
2164:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2164b
	b 2163f
2162:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2165:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2165b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
2163:
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 23
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 23
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2166f
	addi %r8, %r29, 1
2168:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2168b
	b 2167f
2166:
	rldicl %r8, %r29, 63, 1
2169:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2169b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
2167:
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2153b
	b 2151f
2150:
	li %r5, 23
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2170:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2170b
	rldicr %r4, %r29, 5, 58
2171:
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2172f
	addi %r8, %r29, 0
2174:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2174b
	b 2173f
2172:
	rldicl %r8, %r29, 63, 1
2175:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2175b
2173:
	li %r5, 23
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicl %r8, %r12, 63, 1
2176:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2176b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 23
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 20
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicl %r8, %r12, 63, 1
	subfc %r0, %r8, %r8
2177:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2177b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 23
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 23
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicl %r8, %r12, 63, 1
2178:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2178b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2171b
2151:
	addi %r5, %r14, 0
	addi %r8, %r20, 0
	lwz %r9, 152(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r6, 22
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	add %r6, %r6, %r8
	addi %r6, %r6, -1
2179:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2179b
	addi %r5, %r15, 0
	addi %r8, %r22, 0
	lwz %r9, 152(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r6, 23
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	add %r6, %r6, %r8
	addi %r6, %r6, -1
2180:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2180b
	addi %r5, %r16, 0
	addi %r8, %r20, 0
	lwz %r9, 152(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r6, 3
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	add %r6, %r6, %r8
	addi %r6, %r6, -1
2181:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2181b
	lwz %r3, 152(%r31)
25:
	ld %r14, 0(%r31)
	ld %r15, 8(%r31)
	ld %r16, 16(%r31)
	ld %r17, 24(%r31)
	ld %r18, 32(%r31)
	ld %r19, 40(%r31)
	ld %r20, 48(%r31)
	ld %r21, 56(%r31)
	ld %r22, 64(%r31)
	ld %r23, 72(%r31)
	ld %r24, 80(%r31)
	ld %r29, 88(%r31)
	ld %r30, 96(%r31)
	ld %r31, 104(%r31)
	blr

vg_rsa_check_key:
	addi %r11, %r1, 160
	ld %r11, 0(%r11)
	std %r14, 0(%r11)
	std %r15, 8(%r11)
	std %r16, 16(%r11)
	std %r17, 24(%r11)
	std %r18, 32(%r11)
	std %r19, 40(%r11)
	std %r20, 48(%r11)
	std %r21, 56(%r11)
	std %r22, 64(%r11)
	std %r23, 72(%r11)
	std %r24, 80(%r11)
	std %r26, 88(%r11)
	std %r29, 96(%r11)
	std %r30, 104(%r11)
	std %r31, 112(%r11)
	addi %r31, %r11, 0
	addi %r14, %r3, 0
	addi %r15, %r4, 0
	addi %r16, %r7, 0
	addi %r17, %r8, 0
	addi %r18, %r9, 0
	addi %r19, %r10, 0
	addi %r7, %r5, 0
	addi %r8, %r6, 0
	li %r24, 0
20:
	lbz %r0, 0(%r7)
	rldicr %r24, %r24, 8, 55
	or %r24, %r24, %r0
	rldicl %r3, %r24, 31, 33
	li %r4, 0
	subf %r3, %r3, %r4
	rldicl %r3, %r3, 1, 63
	subf %r3, %r3, %r4
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	xor %r0, %r24, %r4
	and %r0, %r0, %r3
	xor %r24, %r24, %r0
	addi %r7, %r7, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 20b
	li %r4, 1
	and %r0, %r24, %r4
	addi %r3, %r24, -3
	rldicl %r3, %r3, 1, 63
	xor %r3, %r3, %r4
	and %r0, %r0, %r3
	rldicr %r3, %r4, 33, 30
	subf %r3, %r3, %r24
	rldicl %r3, %r3, 1, 63
	and %r0, %r0, %r3
	li %r3, 0
	subf %r26, %r0, %r3
	rldicr %r24, %r24, 31, 32
	cmpldi %cr0, %r26, 0
	beq %cr0, 21f
	addi %r20, %r1, 96
	ld %r20, 0(%r20)
	addi %r21, %r1, 104
	ld %r21, 0(%r21)
	addi %r22, %r1, 112
	ld %r22, 0(%r22)
	addi %r23, %r1, 128
	ld %r23, 0(%r23)
	addi %r26, %r1, 144
	ld %r26, 0(%r26)
	addi %r9, %r14, 0
	addi %r10, %r15, 0
	add %r11, %r9, %r10
	addi %r11, %r11, -1
	lbz %r0, 0(%r11)
	li %r12, 1
	and %r0, %r0, %r12
	xor %r0, %r0, %r12
	lbz %r11, 0(%r9)
	cmpldi %cr0, %r11, 0
	beq %cr0, 23f
	b 24f
23:
	li %r0, 1
24:
	addi %r12, %r10, -64
	cmpldi %cr0, %r12, 0
	beq %cr0, 25f
	b 26f
25:
	rldicl %r11, %r11, 57, 7
	li %r12, 1
	xor %r11, %r11, %r12
	or %r0, %r0, %r11
26:
	cmpldi %cr0, %r0, 0
	beq %cr0, 27f
	li %r3, 0
	b 28f
27:
	addi %r29, %r15, 3
	rldicl %r29, %r29, 62, 2
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	li %r8, 24
	mulld %r8, %r8, %r30
	rldicl %r8, %r8, 62, 2
	addi %r5, %r31, 160
	li %r0, 0
29:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 29b
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicl %r0, %r24, 33, 31
	stw %r0, 0(%r5)
	rldicl %r0, %r0, 32, 32
	stw %r0, 4(%r5)
	addi %r6, %r14, 0
	addi %r8, %r15, 0
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
210:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 210b
	addi %r6, %r16, 0
	addi %r8, %r17, 0
	li %r5, 9
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
211:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 211b
	addi %r6, %r18, 0
	addi %r8, %r19, 0
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
212:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 212b
	addi %r6, %r20, 0
	addi %r8, %r21, 0
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
213:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 213b
	addi %r6, %r22, 0
	addi %r8, %r19, 0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
214:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 214b
	addi %r6, %r23, 0
	addi %r8, %r21, 0
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
215:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 215b
	addi %r6, %r26, 0
	addi %r8, %r19, 0
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
216:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 216b
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	stw %r0, 0(%r5)
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 0
	li %r0, 0
217:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 217b
	li %r10, 4
	mulld %r10, %r10, %r30
	add %r10, %r10, %r31
	addi %r10, %r10, 160
	addi %r4, %r19, 3
	rldicl %r4, %r4, 62, 2
	addi %r12, %r29, 0
218:
	lwz %r11, 0(%r10)
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	subf %r6, %r6, %r10
	add %r5, %r5, %r6
	addi %r6, %r5, 0
	li %r7, 5
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	addi %r8, %r12, 0
	li %r9, 0
219:
	lwz %r0, 0(%r7)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r6)
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 219b
	addi %r10, %r10, 4
	addi %r12, %r12, -1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 218b
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 220f
	addi %r8, %r29, 0
222:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 222b
	b 221f
220:
	rldicl %r8, %r29, 63, 1
223:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 223b
221:
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r0, %r29, 2, 61
	add %r5, %r5, %r0
	li %r3, 0
	stw %r3, 0(%r5)
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r0
	stw %r3, 0(%r5)
	li %r10, 14
	mulld %r10, %r10, %r30
	add %r10, %r10, %r31
	addi %r10, %r10, 160
	ld %r0, 0(%r10)
	ld %r12, 0(%r10)
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	li %r3, 0
	subf %r12, %r12, %r3
	rldicr %r12, %r12, 32, 31
	rldicl %r12, %r12, 32, 32
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	stw %r12, 0(%r5)
	addi %r12, %r19, 3
	rldicl %r12, %r12, 62, 2
	addi %r12, %r12, 1
	li %r10, 2
	mulld %r10, %r10, %r30
	add %r10, %r10, %r31
	addi %r10, %r10, 160
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 2
	li %r0, 0
224:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 224b
	addi %r4, %r29, 0
225:
	lwz %r11, 0(%r10)
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 1
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	addi %r8, %r12, 0
	li %r9, 0
226:
	lwz %r0, 0(%r7)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r6)
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 226b
	stw %r9, 0(%r5)
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r3, 0(%r5)
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	mulld %r11, %r0, %r3
	rlwinm %r11, %r11, 0, 0, 31
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	addi %r8, %r12, 0
	li %r9, 0
227:
	lwz %r0, 0(%r7)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r6)
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 227b
	lwz %r0, 0(%r5)
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r6, %r5, 4
	addi %r8, %r12, 0
228:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 228b
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r0, %r12, 2, 61
	add %r5, %r5, %r0
	li %r0, 0
	stw %r0, 0(%r5)
	addi %r10, %r10, 4
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 225b
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	addi %r8, %r12, 0
	li %r9, 0
229:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 229b
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 19
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	addi %r8, %r12, 0
	li %r0, 0
	subf %r9, %r9, %r0
230:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 230b
	li %r6, 12
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 231f
	addi %r8, %r29, 0
233:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 233b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
	b 232f
231:
	rldicl %r8, %r29, 63, 1
234:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 234b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
232:
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 0
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 235f
	addi %r8, %r29, 0
237:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 237b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
	b 236f
235:
	rldicl %r8, %r29, 63, 1
238:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 238b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
236:
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 10
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 239f
	addi %r8, %r29, 0
241:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 241b
	b 240f
239:
	rldicl %r8, %r29, 63, 1
242:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 242b
240:
	li %r5, 10
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	rldicl %r0, %r0, 63, 1
	rldicr %r0, %r0, 1, 62
	stw %r0, 0(%r5)
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 5
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 243f
	addi %r8, %r29, 0
245:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 245b
	b 244f
243:
	rldicl %r8, %r29, 63, 1
246:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 246b
244:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	rldicl %r0, %r0, 63, 1
	rldicr %r0, %r0, 1, 62
	stw %r0, 0(%r5)
	li %r5, 23
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 10
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 247f
	addi %r8, %r29, 0
	li %r9, 0
249:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 249b
	b 248f
247:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
250:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 250b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
248:
	stw %r9, 136(%r31)
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 3
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 251f
	addi %r8, %r29, 0
253:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 253b
	b 252f
251:
	rldicl %r8, %r29, 63, 1
254:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 254b
252:
	li %r5, 17
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 255f
	addi %r8, %r29, 0
257:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 257b
	b 256f
255:
	rldicl %r8, %r29, 63, 1
258:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 258b
256:
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 259f
	addi %r8, %r29, 0
261:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 261b
	b 260f
259:
	rldicl %r8, %r29, 63, 1
262:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 262b
260:
	li %r4, 33
263:
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 128(%r31)
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 17
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 264f
	addi %r8, %r29, 0
266:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 266b
	b 265f
264:
	rldicl %r8, %r29, 63, 1
267:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 267b
265:
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 19
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 268f
	addi %r8, %r29, 0
	li %r9, 0
270:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 270b
	b 269f
268:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
271:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 271b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
269:
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 18
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 20
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 272f
	addi %r8, %r29, 0
	li %r9, 0
274:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 274b
	b 273f
272:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
275:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 275b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
273:
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 21
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 10
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 276f
	addi %r8, %r29, 0
	li %r9, 0
278:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 278b
	b 277f
276:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
279:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 279b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
277:
	stw %r9, 132(%r31)
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 22
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 280f
	addi %r8, %r29, 0
282:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 282b
	b 281f
280:
	rldicl %r8, %r29, 63, 1
283:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 283b
281:
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 17
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 284f
	addi %r8, %r29, 0
	li %r9, 0
286:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 286b
	b 285f
284:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
287:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 287b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
285:
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 17
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 20
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 288f
	addi %r8, %r29, 0
	li %r9, 0
290:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 290b
	b 289f
288:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
291:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 291b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
289:
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 21
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 10
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 292f
	addi %r8, %r29, 0
	li %r9, 0
294:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 294b
	b 293f
292:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
295:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 295b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
293:
	stw %r9, 132(%r31)
	li %r5, 17
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 22
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 296f
	addi %r8, %r29, 0
298:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 298b
	b 297f
296:
	rldicl %r8, %r29, 63, 1
299:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 299b
297:
	li %r9, 0
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2100f
	addi %r8, %r29, 0
2102:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2102b
	b 2101f
2100:
	rldicl %r8, %r29, 63, 1
2103:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2103b
2101:
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 263b
	li %r6, 18
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 1
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2104f
	addi %r8, %r29, 0
2106:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2106b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
	b 2105f
2104:
	rldicl %r8, %r29, 63, 1
2107:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2107b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
2105:
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 23
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 7
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2108f
	addi %r8, %r29, 0
	li %r9, 0
2110:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2110b
	b 2109f
2108:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2111:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2111b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2109:
	stw %r9, 136(%r31)
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 3
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2112f
	addi %r8, %r29, 0
2114:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2114b
	b 2113f
2112:
	rldicl %r8, %r29, 63, 1
2115:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2115b
2113:
	li %r5, 17
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 7
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2116f
	addi %r8, %r29, 0
2118:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2118b
	b 2117f
2116:
	rldicl %r8, %r29, 63, 1
2119:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2119b
2117:
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2120f
	addi %r8, %r29, 0
2122:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2122b
	b 2121f
2120:
	rldicl %r8, %r29, 63, 1
2123:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2123b
2121:
	li %r4, 33
2124:
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 128(%r31)
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 17
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2125f
	addi %r8, %r29, 0
2127:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2127b
	b 2126f
2125:
	rldicl %r8, %r29, 63, 1
2128:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2128b
2126:
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 19
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2129f
	addi %r8, %r29, 0
	li %r9, 0
2131:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2131b
	b 2130f
2129:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2132:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2132b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2130:
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 18
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 20
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2133f
	addi %r8, %r29, 0
	li %r9, 0
2135:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2135b
	b 2134f
2133:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2136:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2136b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2134:
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 21
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2137f
	addi %r8, %r29, 0
	li %r9, 0
2139:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2139b
	b 2138f
2137:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2140:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2140b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2138:
	stw %r9, 132(%r31)
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 22
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2141f
	addi %r8, %r29, 0
2143:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2143b
	b 2142f
2141:
	rldicl %r8, %r29, 63, 1
2144:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2144b
2142:
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 17
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2145f
	addi %r8, %r29, 0
	li %r9, 0
2147:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2147b
	b 2146f
2145:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2148:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2148b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2146:
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 17
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 20
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2149f
	addi %r8, %r29, 0
	li %r9, 0
2151:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2151b
	b 2150f
2149:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2152:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2152b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2150:
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 21
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2153f
	addi %r8, %r29, 0
	li %r9, 0
2155:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2155b
	b 2154f
2153:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2156:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2156b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2154:
	stw %r9, 132(%r31)
	li %r5, 17
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 22
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2157f
	addi %r8, %r29, 0
2159:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2159b
	b 2158f
2157:
	rldicl %r8, %r29, 63, 1
2160:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2160b
2158:
	li %r9, 0
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2161f
	addi %r8, %r29, 0
2163:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2163b
	b 2162f
2161:
	rldicl %r8, %r29, 63, 1
2164:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2164b
2162:
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2124b
	li %r6, 18
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 1
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2165f
	addi %r8, %r29, 0
2167:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2167b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
	b 2166f
2165:
	rldicl %r8, %r29, 63, 1
2168:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2168b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
2166:
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 23
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 8
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 4
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2169f
	addi %r8, %r29, 0
	li %r9, 0
2171:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2171b
	b 2170f
2169:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2172:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2172b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2170:
	stw %r9, 136(%r31)
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r0, %r29, 2, 61
	add %r5, %r5, %r0
	li %r3, 0
	stw %r3, 0(%r5)
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r0
	stw %r3, 0(%r5)
	li %r10, 14
	mulld %r10, %r10, %r30
	add %r10, %r10, %r31
	addi %r10, %r10, 160
	ld %r0, 0(%r10)
	ld %r12, 0(%r10)
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	li %r3, 0
	subf %r12, %r12, %r3
	rldicr %r12, %r12, 32, 31
	rldicl %r12, %r12, 32, 32
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	stw %r12, 0(%r5)
	addi %r12, %r19, 3
	rldicl %r12, %r12, 62, 2
	addi %r12, %r12, 1
	li %r10, 5
	mulld %r10, %r10, %r30
	add %r10, %r10, %r31
	addi %r10, %r10, 160
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 2
	li %r0, 0
2173:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2173b
	addi %r4, %r29, 0
2174:
	lwz %r11, 0(%r10)
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 18
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 8
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	addi %r8, %r12, 0
	li %r9, 0
2175:
	lwz %r0, 0(%r7)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r6)
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2175b
	stw %r9, 0(%r5)
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r3, 0(%r5)
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	mulld %r11, %r0, %r3
	rlwinm %r11, %r11, 0, 0, 31
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 18
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	addi %r8, %r12, 0
	li %r9, 0
2176:
	lwz %r0, 0(%r7)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r6)
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2176b
	lwz %r0, 0(%r5)
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r6, %r5, 4
	addi %r8, %r12, 0
2177:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2177b
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r0, %r12, 2, 61
	add %r5, %r5, %r0
	li %r0, 0
	stw %r0, 0(%r5)
	addi %r10, %r10, 4
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2174b
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 18
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	addi %r8, %r12, 0
	li %r9, 0
2178:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2178b
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 19
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 18
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	addi %r8, %r12, 0
	li %r0, 0
	subf %r9, %r9, %r0
2179:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2179b
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r0, %r29, 2, 61
	add %r5, %r5, %r0
	li %r3, 0
	stw %r3, 0(%r5)
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r0
	stw %r3, 0(%r5)
	li %r10, 14
	mulld %r10, %r10, %r30
	add %r10, %r10, %r31
	addi %r10, %r10, 160
	ld %r0, 0(%r10)
	ld %r12, 0(%r10)
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	li %r3, 0
	subf %r12, %r12, %r3
	rldicr %r12, %r12, 32, 31
	rldicl %r12, %r12, 32, 32
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	stw %r12, 0(%r5)
	addi %r12, %r19, 3
	rldicl %r12, %r12, 62, 2
	addi %r12, %r12, 1
	li %r10, 1
	mulld %r10, %r10, %r30
	add %r10, %r10, %r31
	addi %r10, %r10, 160
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 2
	li %r0, 0
2180:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2180b
	addi %r4, %r29, 0
2181:
	lwz %r11, 0(%r10)
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 16
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 1
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	addi %r8, %r12, 0
	li %r9, 0
2182:
	lwz %r0, 0(%r7)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r6)
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2182b
	stw %r9, 0(%r5)
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r3, 0(%r5)
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	mulld %r11, %r0, %r3
	rlwinm %r11, %r11, 0, 0, 31
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 16
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	addi %r8, %r12, 0
	li %r9, 0
2183:
	lwz %r0, 0(%r7)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r6)
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2183b
	lwz %r0, 0(%r5)
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r6, %r5, 4
	addi %r8, %r12, 0
2184:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2184b
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r0, %r12, 2, 61
	add %r5, %r5, %r0
	li %r0, 0
	stw %r0, 0(%r5)
	addi %r10, %r10, 4
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2181b
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 16
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	addi %r8, %r12, 0
	li %r9, 0
2185:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2185b
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 19
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 16
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	addi %r8, %r12, 0
	li %r0, 0
	subf %r9, %r9, %r0
2186:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2186b
	li %r6, 18
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 16
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2187f
	addi %r8, %r29, 0
2189:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2189b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
	b 2188f
2187:
	rldicl %r8, %r29, 63, 1
2190:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2190b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
2188:
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 23
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 9
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2191f
	addi %r8, %r29, 0
	li %r9, 0
2193:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2193b
	b 2192f
2191:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2194:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2194b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2192:
	stw %r9, 136(%r31)
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 9
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2195f
	addi %r8, %r29, 0
2197:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2197b
	b 2196f
2195:
	rldicl %r8, %r29, 63, 1
2198:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2198b
2196:
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2199f
	addi %r8, %r29, 0
2201:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2201b
	b 2200f
2199:
	rldicl %r8, %r29, 63, 1
2202:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2202b
2200:
	addi %r12, %r19, 0
	addi %r12, %r12, 7
	rldicl %r12, %r12, 61, 3
	rldicr %r12, %r12, 1, 62
	subf %r0, %r12, %r29
	rldicl %r0, %r0, 1, 63
	cmpldi %cr0, %r0, 0
	beq %cr0, 2203f
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2205:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2205b
	rldicr %r4, %r29, 5, 58
2206:
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2207f
	addi %r8, %r29, 0
2209:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2209b
	b 2208f
2207:
	rldicl %r8, %r29, 63, 1
2210:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2210b
2208:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2211f
	addi %r8, %r29, 1
2213:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2213b
	b 2212f
2211:
	rldicl %r8, %r29, 63, 1
2214:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2214b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
2212:
	li %r5, 15
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2215f
	addi %r8, %r29, 1
	li %r9, 0
2217:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2217b
	b 2216f
2215:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2218:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2218b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
2216:
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 15
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2219f
	addi %r8, %r29, 1
2221:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2221b
	b 2220f
2219:
	rldicl %r8, %r29, 63, 1
2222:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2222b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
2220:
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2206b
	b 2204f
2203:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2223:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2223b
	rldicr %r4, %r29, 5, 58
2224:
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2225f
	addi %r8, %r29, 0
2227:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2227b
	b 2226f
2225:
	rldicl %r8, %r29, 63, 1
2228:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2228b
2226:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicl %r8, %r12, 63, 1
2229:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2229b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	li %r5, 15
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicl %r8, %r12, 63, 1
	subfc %r0, %r8, %r8
2230:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2230b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 15
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicl %r8, %r12, 63, 1
2231:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2231b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2224b
2204:
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2232f
	addi %r8, %r29, 0
2234:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2234b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
	b 2233f
2232:
	rldicl %r8, %r29, 63, 1
2235:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2235b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
2233:
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 9
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2236f
	addi %r8, %r29, 0
2238:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2238b
	b 2237f
2236:
	rldicl %r8, %r29, 63, 1
2239:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2239b
2237:
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2240f
	addi %r8, %r29, 0
2242:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2242b
	b 2241f
2240:
	rldicl %r8, %r29, 63, 1
2243:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2243b
2241:
	addi %r12, %r21, 0
	addi %r12, %r12, 7
	rldicl %r12, %r12, 61, 3
	rldicr %r12, %r12, 1, 62
	subf %r0, %r12, %r29
	rldicl %r0, %r0, 1, 63
	cmpldi %cr0, %r0, 0
	beq %cr0, 2244f
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2246:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2246b
	rldicr %r4, %r29, 5, 58
2247:
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2248f
	addi %r8, %r29, 0
2250:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2250b
	b 2249f
2248:
	rldicl %r8, %r29, 63, 1
2251:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2251b
2249:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2252f
	addi %r8, %r29, 1
2254:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2254b
	b 2253f
2252:
	rldicl %r8, %r29, 63, 1
2255:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2255b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
2253:
	li %r5, 15
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2256f
	addi %r8, %r29, 1
	li %r9, 0
2258:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2258b
	b 2257f
2256:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2259:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2259b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
2257:
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 15
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2260f
	addi %r8, %r29, 1
2262:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2262b
	b 2261f
2260:
	rldicl %r8, %r29, 63, 1
2263:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2263b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
2261:
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2247b
	b 2245f
2244:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2264:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2264b
	rldicr %r4, %r29, 5, 58
2265:
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2266f
	addi %r8, %r29, 0
2268:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2268b
	b 2267f
2266:
	rldicl %r8, %r29, 63, 1
2269:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2269b
2267:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicl %r8, %r12, 63, 1
2270:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2270b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	li %r5, 15
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicl %r8, %r12, 63, 1
	subfc %r0, %r8, %r8
2271:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2271b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 15
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicl %r8, %r12, 63, 1
2272:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2272b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2265b
2245:
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 7
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2273f
	addi %r8, %r29, 0
2275:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2275b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
	b 2274f
2273:
	rldicl %r8, %r29, 63, 1
2276:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2276b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
2274:
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	lwz %r3, 140(%r31)
28:
	b 22f
21:
	li %r3, 0
22:
	ld %r14, 0(%r31)
	ld %r15, 8(%r31)
	ld %r16, 16(%r31)
	ld %r17, 24(%r31)
	ld %r18, 32(%r31)
	ld %r19, 40(%r31)
	ld %r20, 48(%r31)
	ld %r21, 56(%r31)
	ld %r22, 64(%r31)
	ld %r23, 72(%r31)
	ld %r24, 80(%r31)
	ld %r26, 88(%r31)
	ld %r29, 96(%r31)
	ld %r30, 104(%r31)
	ld %r31, 112(%r31)
	blr

vg_rsa_recover_primes_det:
	addi %r11, %r1, 112
	ld %r11, 0(%r11)
	addi %r12, %r8, 7
	rldicl %r12, %r12, 61, 3
	rldicr %r12, %r12, 1, 62
	addi %r12, %r12, 2
	addi %r0, %r12, 2
	rldicr %r0, %r0, 2, 61
	li %r12, 44
	mulld %r12, %r12, %r0
	add %r12, %r12, %r11
	addi %r12, %r12, 160
	std %r14, 0(%r12)
	std %r15, 8(%r12)
	std %r16, 16(%r12)
	std %r17, 24(%r12)
	std %r18, 32(%r12)
	std %r19, 40(%r12)
	std %r20, 48(%r12)
	std %r21, 56(%r12)
	std %r22, 64(%r12)
	std %r23, 72(%r12)
	std %r24, 80(%r12)
	std %r25, 88(%r12)
	std %r26, 96(%r12)
	std %r27, 104(%r12)
	std %r28, 112(%r12)
	std %r29, 120(%r12)
	std %r30, 128(%r12)
	std %r31, 136(%r12)
	addi %r31, %r11, 0
	addi %r29, %r8, 7
	rldicl %r29, %r29, 61, 3
	rldicr %r29, %r29, 1, 62
	addi %r29, %r29, 2
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	addi %r21, %r3, 0
	addi %r23, %r5, 0
	addi %r24, %r7, 0
	addi %r25, %r8, 0
	addi %r26, %r9, 0
	addi %r27, %r10, 0
	addi %r28, %r1, 96
	ld %r28, 0(%r28)
	addi %r22, %r1, 104
	ld %r22, 0(%r22)
	addi %r9, %r24, 0
	addi %r10, %r25, 0
	add %r11, %r9, %r10
	addi %r11, %r11, -1
	lbz %r0, 0(%r11)
	li %r12, 1
	and %r0, %r0, %r12
	xor %r0, %r0, %r12
	lbz %r11, 0(%r9)
	cmpldi %cr0, %r11, 0
	beq %cr0, 20f
	b 21f
20:
	li %r0, 1
21:
	addi %r12, %r10, -64
	cmpldi %cr0, %r12, 0
	beq %cr0, 22f
	b 23f
22:
	rldicl %r11, %r11, 57, 7
	li %r12, 1
	xor %r11, %r11, %r12
	or %r0, %r0, %r11
23:
	cmpldi %cr0, %r0, 0
	beq %cr0, 24f
	addi %r5, %r21, 0
	addi %r8, %r25, 0
	li %r0, 0
26:
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 26b
	addi %r5, %r23, 0
	addi %r8, %r25, 0
	li %r0, 0
27:
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 27b
	li %r3, 0
	b 25f
24:
	li %r8, 44
	mulld %r8, %r8, %r30
	rldicl %r8, %r8, 62, 2
	addi %r5, %r31, 160
	li %r0, 0
28:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 28b
	addi %r6, %r24, 0
	addi %r8, %r25, 0
	li %r5, 32
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
29:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 29b
	rldicr %r29, %r29, 1, 62
	addi %r29, %r29, 2
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	addi %r6, %r26, 0
	addi %r8, %r27, 0
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
210:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 210b
	addi %r6, %r28, 0
	addi %r8, %r22, 0
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
211:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 211b
	add %r26, %r27, %r22
	rldicr %r26, %r26, 3, 60
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r0, %r29, 2, 61
	add %r5, %r5, %r0
	addi %r5, %r5, -4
	li %r0, 1
	rldicr %r0, %r0, 31, 32
	stw %r0, 0(%r5)
	rldicr %r4, %r27, 3, 60
212:
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 128(%r31)
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 213f
	addi %r8, %r29, 0
215:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 215b
	b 214f
213:
	rldicl %r8, %r29, 63, 1
216:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 216b
214:
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 5
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 217f
	addi %r8, %r29, 0
	li %r9, 0
219:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 219b
	b 218f
217:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
220:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 220b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
218:
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 3
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 221f
	addi %r8, %r29, 0
	li %r9, 0
223:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 223b
	b 222f
221:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
224:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 224b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
222:
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 7
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 4
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 225f
	addi %r8, %r29, 0
	li %r9, 0
227:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 227b
	b 226f
225:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
228:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 228b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
226:
	stw %r9, 132(%r31)
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 8
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 7
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 229f
	addi %r8, %r29, 0
231:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 231b
	b 230f
229:
	rldicl %r8, %r29, 63, 1
232:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 232b
230:
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 233f
	addi %r8, %r29, 0
	li %r9, 0
235:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 235b
	b 234f
233:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
236:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 236b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
234:
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 237f
	addi %r8, %r29, 0
	li %r9, 0
239:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 239b
	b 238f
237:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
240:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 240b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
238:
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 7
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 4
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 241f
	addi %r8, %r29, 0
	li %r9, 0
243:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 243b
	b 242f
241:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
244:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 244b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
242:
	stw %r9, 132(%r31)
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 8
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 7
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 245f
	addi %r8, %r29, 0
247:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 247b
	b 246f
245:
	rldicl %r8, %r29, 63, 1
248:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 248b
246:
	li %r9, 0
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 249f
	addi %r8, %r29, 0
251:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 251b
	b 250f
249:
	rldicl %r8, %r29, 63, 1
252:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 252b
250:
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 212b
	li %r5, 9
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 253f
	addi %r8, %r29, 0
255:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 255b
	b 254f
253:
	rldicl %r8, %r29, 63, 1
256:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 256b
254:
	li %r5, 9
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	stw %r0, 0(%r5)
	li %r5, 10
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 3
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 257f
	addi %r8, %r29, 0
	li %r9, 0
259:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 259b
	b 258f
257:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
260:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 260b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
258:
	stw %r9, 0(%r31)
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 261f
	addi %r8, %r29, 0
	li %r9, 0
263:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 263b
	b 262f
261:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
264:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 264b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
262:
	stw %r9, 4(%r31)
	li %r5, 15
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 265f
	addi %r8, %r29, 0
267:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 267b
	b 266f
265:
	rldicl %r8, %r29, 63, 1
268:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 268b
266:
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 269f
	addi %r8, %r29, 0
271:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 271b
	b 270f
269:
	rldicl %r8, %r29, 63, 1
272:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 272b
270:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 15
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 273f
	addi %r8, %r29, 0
275:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 275b
	b 274f
273:
	rldicl %r8, %r29, 63, 1
276:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 276b
274:
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 15
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 277f
	addi %r8, %r29, 0
279:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 279b
	b 278f
277:
	rldicl %r8, %r29, 63, 1
280:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 280b
278:
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 15
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 281f
	addi %r8, %r29, 0
283:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 283b
	b 282f
281:
	rldicl %r8, %r29, 63, 1
284:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 284b
282:
	addi %r29, %r29, -2
	rldicl %r29, %r29, 63, 1
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	li %r5, 26
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 20
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 285f
	addi %r8, %r29, 0
287:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 287b
	b 286f
285:
	rldicl %r8, %r29, 63, 1
288:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 288b
286:
	li %r5, 42
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 30
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 289f
	addi %r8, %r29, 0
291:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 291b
	b 290f
289:
	rldicl %r8, %r29, 63, 1
292:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 292b
290:
	li %r5, 42
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	stw %r0, 0(%r5)
	li %r5, 40
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 32
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 42
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 293f
	addi %r8, %r29, 0
	li %r9, 0
295:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 295b
	b 294f
293:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
296:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 296b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
294:
	li %r5, 28
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 40
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 297f
	addi %r8, %r29, 0
299:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 299b
	b 298f
297:
	rldicl %r8, %r29, 63, 1
2100:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2100b
298:
	rldicr %r27, %r29, 5, 58
	rldicr %r29, %r29, 1, 62
	addi %r29, %r29, 2
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
2101:
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 8(%r31)
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 12(%r31)
	lwz %r0, 8(%r31)
	lwz %r3, 12(%r31)
	li %r5, 1
	xor %r0, %r0, %r5
	xor %r3, %r3, %r5
	stw %r0, 16(%r31)
	and %r3, %r3, %r0
	stw %r3, 20(%r31)
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 14
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2102f
	addi %r8, %r29, 0
2104:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2104b
	b 2103f
2102:
	rldicl %r8, %r29, 63, 1
2105:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2105b
2103:
	li %r9, 0
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2106f
	addi %r8, %r29, 0
2108:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2108b
	b 2107f
2106:
	rldicl %r8, %r29, 63, 1
2109:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2109b
2107:
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 14
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 16(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2110f
	addi %r8, %r29, 0
2112:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2112b
	b 2111f
2110:
	rldicl %r8, %r29, 63, 1
2113:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2113b
2111:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2114f
	addi %r8, %r29, 0
2116:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2116b
	b 2115f
2114:
	rldicl %r8, %r29, 63, 1
2117:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2117b
2115:
	li %r9, 0
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2118f
	addi %r8, %r29, 0
2120:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2120b
	b 2119f
2118:
	rldicl %r8, %r29, 63, 1
2121:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2121b
2119:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 20(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2122f
	addi %r8, %r29, 0
2124:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2124b
	b 2123f
2122:
	rldicl %r8, %r29, 63, 1
2125:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2125b
2123:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 12
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2126f
	addi %r8, %r29, 0
2128:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2128b
	b 2127f
2126:
	rldicl %r8, %r29, 63, 1
2129:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2129b
2127:
	li %r9, 0
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2130f
	addi %r8, %r29, 0
2132:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2132b
	b 2131f
2130:
	rldicl %r8, %r29, 63, 1
2133:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2133b
2131:
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 12
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 20(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2134f
	addi %r8, %r29, 0
2136:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2136b
	b 2135f
2134:
	rldicl %r8, %r29, 63, 1
2137:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2137b
2135:
	addi %r27, %r27, -1
	cmpldi %cr0, %r27, 0
	bne %cr0, 2101b
	addi %r29, %r29, -2
	rldicl %r29, %r29, 63, 1
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 26
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2138f
	addi %r8, %r29, 0
2140:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2140b
	b 2139f
2138:
	rldicl %r8, %r29, 63, 1
2141:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2141b
2139:
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 28
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2142f
	addi %r8, %r29, 0
2144:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2144b
	b 2143f
2142:
	rldicl %r8, %r29, 63, 1
2145:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2145b
2143:
	addi %r11, %r29, 0
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 8
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	addi %r10, %r11, 0
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
2146:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2146b
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	rldicr %r8, %r8, 2, 61
	add %r6, %r6, %r8
	li %r0, 0
	stw %r0, 0(%r6)
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
2147:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2147b
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	stw %r0, 0(%r5)
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 7
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
2148:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2148b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	rldicr %r0, %r0, 1, 62
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r3, 0(%r5)
	or %r3, %r3, %r0
	stw %r3, 0(%r5)
	li %r10, 2
	mulld %r10, %r10, %r30
	add %r10, %r10, %r31
	addi %r10, %r10, 160
	ld %r0, 0(%r10)
	ld %r12, 0(%r10)
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	li %r3, 0
	subf %r12, %r12, %r3
	rldicr %r12, %r12, 32, 31
	rldicl %r12, %r12, 32, 32
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	std %r12, 40(%r5)
	addi %r10, %r11, 0
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
2149:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2149b
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r11, 0(%r5)
	rldicr %r11, %r11, 63, 0
	rldicl %r11, %r11, 1, 63
	li %r0, 1
	xor %r11, %r11, %r0
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	li %r9, 0
2150:
	lwz %r0, 0(%r7)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r6)
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2150b
	stw %r9, 0(%r5)
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r0, 0
2151:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2151b
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	std %r0, 0(%r5)
	addi %r3, %r10, 1
	add %r0, %r3, %r3
	add %r3, %r3, %r0
	rldicr %r3, %r3, 15, 48
	add %r10, %r10, %r3
2152:
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r4, 0(%r5)
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r5, 0(%r5)
	li %r3, 14
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r3, 0(%r3)
	li %r6, 1
	li %r7, 0
	li %r8, 0
	li %r9, 1
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	li %r4, 14
	mulld %r4, %r4, %r30
	add %r4, %r4, %r31
	addi %r4, %r4, 160
	std %r3, 0(%r4)
	std %r6, 8(%r4)
	std %r7, 16(%r4)
	std %r8, 24(%r4)
	std %r9, 32(%r4)
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 5
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r11, 14
	mulld %r11, %r11, %r30
	add %r11, %r11, %r31
	addi %r11, %r11, 160
	ld %r11, 8(%r11)
	li %r12, 14
	mulld %r12, %r12, %r30
	add %r12, %r12, %r31
	addi %r12, %r12, 160
	ld %r12, 16(%r12)
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	li %r9, 0
2153:
	lwz %r0, 0(%r6)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r7)
	mulld %r3, %r12, %r3
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	rldicl %r3, %r0, 1, 63
	rldicr %r3, %r3, 32, 31
	subf %r9, %r3, %r9
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2153b
	lwz %r0, 0(%r6)
	rldicl %r4, %r0, 33, 31
	rldicr %r4, %r4, 32, 31
	subf %r0, %r4, %r0
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r7)
	rldicl %r4, %r3, 33, 31
	rldicr %r4, %r4, 32, 31
	subf %r3, %r4, %r3
	mulld %r3, %r12, %r3
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	rldicl %r3, %r0, 1, 63
	rldicr %r3, %r3, 32, 31
	subf %r9, %r3, %r9
	stw %r9, 4(%r5)
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 5
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r11, 14
	mulld %r11, %r11, %r30
	add %r11, %r11, %r31
	addi %r11, %r11, 160
	ld %r11, 24(%r11)
	li %r12, 14
	mulld %r12, %r12, %r30
	add %r12, %r12, %r31
	addi %r12, %r12, 160
	ld %r12, 32(%r12)
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	li %r9, 0
2154:
	lwz %r0, 0(%r6)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r7)
	mulld %r3, %r12, %r3
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	rldicl %r3, %r0, 1, 63
	rldicr %r3, %r3, 32, 31
	subf %r9, %r3, %r9
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2154b
	lwz %r0, 0(%r6)
	rldicl %r4, %r0, 33, 31
	rldicr %r4, %r4, 32, 31
	subf %r0, %r4, %r0
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r7)
	rldicl %r4, %r3, 33, 31
	rldicr %r4, %r4, 32, 31
	subf %r3, %r4, %r3
	mulld %r3, %r12, %r3
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	rldicl %r3, %r0, 1, 63
	rldicr %r3, %r3, 32, 31
	subf %r9, %r3, %r9
	stw %r9, 4(%r5)
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
2155:
	lwz %r0, 0(%r6)
	lwz %r3, 4(%r6)
	rldicl %r0, %r0, 34, 30
	rldicr %r3, %r3, 2, 61
	add %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2155b
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 12
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
2156:
	lwz %r0, 0(%r6)
	lwz %r3, 4(%r6)
	rldicl %r0, %r0, 34, 30
	rldicr %r3, %r3, 2, 61
	add %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2156b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 7
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r11, 14
	mulld %r11, %r11, %r30
	add %r11, %r11, %r31
	addi %r11, %r11, 160
	ld %r11, 8(%r11)
	li %r12, 14
	mulld %r12, %r12, %r30
	add %r12, %r12, %r31
	addi %r12, %r12, 160
	ld %r12, 16(%r12)
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	li %r9, 0
2157:
	lwz %r0, 0(%r6)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r7)
	mulld %r3, %r12, %r3
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	rldicl %r3, %r0, 1, 63
	rldicr %r3, %r3, 32, 31
	subf %r9, %r3, %r9
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2157b
	lwz %r0, 0(%r6)
	rldicl %r4, %r0, 33, 31
	rldicr %r4, %r4, 32, 31
	subf %r0, %r4, %r0
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r7)
	rldicl %r4, %r3, 33, 31
	rldicr %r4, %r4, 32, 31
	subf %r3, %r4, %r3
	mulld %r3, %r12, %r3
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	rldicl %r3, %r0, 1, 63
	rldicr %r3, %r3, 32, 31
	subf %r9, %r3, %r9
	stw %r9, 4(%r5)
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 7
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r11, 14
	mulld %r11, %r11, %r30
	add %r11, %r11, %r31
	addi %r11, %r11, 160
	ld %r11, 24(%r11)
	li %r12, 14
	mulld %r12, %r12, %r30
	add %r12, %r12, %r31
	addi %r12, %r12, 160
	ld %r12, 32(%r12)
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	li %r9, 0
2158:
	lwz %r0, 0(%r6)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r7)
	mulld %r3, %r12, %r3
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	rldicl %r3, %r0, 1, 63
	rldicr %r3, %r3, 32, 31
	subf %r9, %r3, %r9
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2158b
	lwz %r0, 0(%r6)
	rldicl %r4, %r0, 33, 31
	rldicr %r4, %r4, 32, 31
	subf %r0, %r4, %r0
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r7)
	rldicl %r4, %r3, 33, 31
	rldicr %r4, %r4, 32, 31
	subf %r3, %r4, %r3
	mulld %r3, %r12, %r3
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	rldicl %r3, %r0, 1, 63
	rldicr %r3, %r3, 32, 31
	subf %r9, %r3, %r9
	stw %r9, 4(%r5)
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r3, 14
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r3, 40(%r3)
	lwz %r0, 0(%r5)
	mulld %r11, %r0, %r3
	rlwinm %r11, %r11, 0, 0, 31
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
2159:
	lwz %r0, 0(%r7)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r6)
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2159b
	lwz %r0, 0(%r5)
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	addi %r6, %r6, 4
	li %r11, 1
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
2160:
	lwz %r0, 0(%r7)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r6)
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2160b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
2161:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2161b
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r0, 0
	subf %r9, %r9, %r0
2162:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2162b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
2163:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2163b
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r0, 0
	subf %r9, %r9, %r0
2164:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2164b
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r3, 14
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r3, 40(%r3)
	lwz %r0, 0(%r5)
	mulld %r11, %r0, %r3
	rlwinm %r11, %r11, 0, 0, 31
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 12
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
2165:
	lwz %r0, 0(%r7)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r6)
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2165b
	lwz %r0, 0(%r5)
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 12
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	addi %r6, %r6, 4
	li %r11, 1
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
2166:
	lwz %r0, 0(%r7)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r6)
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2166b
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
2167:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2167b
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 12
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r0, 0
	subf %r9, %r9, %r0
2168:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2168b
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
2169:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2169b
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 12
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r0, 0
	subf %r9, %r9, %r0
2170:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2170b
	addi %r10, %r10, -32768
	rldicl %r3, %r10, 49, 15
	cmpldi %cr0, %r3, 0
	bne %cr0, 2152b
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
2171:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2171b
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	rldicr %r8, %r8, 2, 61
	add %r6, %r6, %r8
	lwz %r9, 0(%r6)
	rldicl %r9, %r9, 33, 31
	li %r0, 0
	subf %r9, %r9, %r0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
2172:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2172b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
2173:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2173b
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r0, 0
	subf %r9, %r9, %r0
2174:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2174b
	addi %r3, %r10, 1
	add %r0, %r3, %r3
	add %r3, %r3, %r0
	add %r3, %r3, %r3
	rldicr %r3, %r3, 15, 48
	add %r10, %r10, %r3
2175:
	li %r11, 1
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
2176:
	lwz %r0, 0(%r7)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r6)
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2176b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
2177:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2177b
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r0, 0
	subf %r9, %r9, %r0
2178:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2178b
	addi %r10, %r10, -32768
	rldicl %r3, %r10, 49, 15
	cmpldi %cr0, %r3, 0
	bne %cr0, 2175b
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2179:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2179b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 4
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
2180:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2180b
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	rldicr %r8, %r8, 2, 61
	add %r6, %r6, %r8
	lwz %r9, 0(%r6)
	rldicl %r9, %r9, 33, 31
	li %r0, 0
	subf %r9, %r9, %r0
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
2181:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2181b
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2182:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2182b
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
2183:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2183b
	li %r6, 8
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 42
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2184f
	addi %r8, %r29, 0
2186:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2186b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 52(%r31)
	b 2185f
2184:
	rldicl %r8, %r29, 63, 1
2187:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2187b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 52(%r31)
2185:
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 42
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 52(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2188f
	addi %r8, %r29, 0
2190:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2190b
	b 2189f
2188:
	rldicl %r8, %r29, 63, 1
2191:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2191b
2189:
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2192f
	addi %r8, %r29, 0
2194:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2194b
	b 2193f
2192:
	rldicl %r8, %r29, 63, 1
2195:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2195b
2193:
	rldicr %r27, %r29, 5, 58
	rldicr %r29, %r29, 1, 62
	addi %r29, %r29, 2
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	li %r5, 17
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 15
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2196f
	addi %r8, %r29, 0
2198:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2198b
	b 2197f
2196:
	rldicl %r8, %r29, 63, 1
2199:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2199b
2197:
2200:
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 24(%r31)
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 15
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 12
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 24(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2201f
	addi %r8, %r29, 0
2203:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2203b
	b 2202f
2201:
	rldicl %r8, %r29, 63, 1
2204:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2204b
2202:
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 15
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2205f
	addi %r8, %r29, 0
	li %r9, 0
2207:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2207b
	b 2206f
2205:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2208:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2208b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2206:
	li %r5, 17
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 17
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 20
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2209f
	addi %r8, %r29, 0
	li %r9, 0
2211:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2211b
	b 2210f
2209:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2212:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2212b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2210:
	li %r9, 0
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2213f
	addi %r8, %r29, 0
2215:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2215b
	b 2214f
2213:
	rldicl %r8, %r29, 63, 1
2216:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2216b
2214:
	li %r9, 0
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2217f
	addi %r8, %r29, 0
2219:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2219b
	b 2218f
2217:
	rldicl %r8, %r29, 63, 1
2220:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2220b
2218:
	addi %r27, %r27, -1
	cmpldi %cr0, %r27, 0
	bne %cr0, 2200b
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 15
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2221f
	addi %r8, %r29, 0
2223:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2223b
	b 2222f
2221:
	rldicl %r8, %r29, 63, 1
2224:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2224b
2222:
	addi %r29, %r29, -2
	rldicl %r29, %r29, 63, 1
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	li %r5, 38
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 32
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2225f
	addi %r8, %r29, 0
2227:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2227b
	b 2226f
2225:
	rldicl %r8, %r29, 63, 1
2228:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2228b
2226:
	rldicr %r29, %r29, 1, 62
	addi %r29, %r29, 2
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r0, %r29, 2, 61
	add %r5, %r5, %r0
	li %r0, 0
	stw %r0, 0(%r5)
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2229:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2229b
	rldicr %r4, %r29, 5, 58
2230:
	li %r5, 17
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2231f
	addi %r8, %r29, 0
2233:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2233b
	b 2232f
2231:
	rldicl %r8, %r29, 63, 1
2234:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2234b
2232:
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2235f
	addi %r8, %r29, 1
2237:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2237b
	b 2236f
2235:
	rldicl %r8, %r29, 63, 1
2238:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2238b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
2236:
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 18
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 19
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2239f
	addi %r8, %r29, 1
	li %r9, 0
2241:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2241b
	b 2240f
2239:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2242:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2242b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
2240:
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 18
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2243f
	addi %r8, %r29, 1
2245:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2245b
	b 2244f
2243:
	rldicl %r8, %r29, 63, 1
2246:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2246b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
2244:
	li %r5, 17
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2230b
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 17
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 19
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2247f
	addi %r8, %r29, 0
	li %r9, 0
2249:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2249b
	b 2248f
2247:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2250:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2250b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2248:
	stw %r9, 28(%r31)
	addi %r29, %r29, -2
	rldicl %r29, %r29, 63, 1
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 30
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2251f
	addi %r8, %r29, 0
2253:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2253b
	b 2252f
2251:
	rldicl %r8, %r29, 63, 1
2254:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2254b
2252:
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	stw %r0, 0(%r5)
	li %r5, 23
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 30
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 22
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2255f
	addi %r8, %r29, 0
	li %r9, 0
2257:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2257b
	b 2256f
2255:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2258:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2258b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2256:
	li %r5, 24
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 34
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 23
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2259f
	addi %r8, %r29, 0
	li %r9, 0
2261:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2261b
	b 2260f
2259:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2262:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2262b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2260:
	li %r5, 25
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 32
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 36
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2263f
	addi %r8, %r29, 0
	li %r9, 0
2265:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2265b
	b 2264f
2263:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2266:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2266b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2264:
	li %r5, 24
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r0, %r29, 2, 61
	add %r5, %r5, %r0
	li %r0, 0
	stw %r0, 0(%r5)
	li %r5, 26
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2267:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2267b
	rldicr %r4, %r29, 5, 58
2268:
	li %r5, 25
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2269f
	addi %r8, %r29, 0
2271:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2271b
	b 2270f
2269:
	rldicl %r8, %r29, 63, 1
2272:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2272b
2270:
	li %r5, 26
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2273f
	addi %r8, %r29, 1
2275:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2275b
	b 2274f
2273:
	rldicl %r8, %r29, 63, 1
2276:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2276b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
2274:
	li %r5, 27
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 26
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 24
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2277f
	addi %r8, %r29, 1
	li %r9, 0
2279:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2279b
	b 2278f
2277:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2280:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2280b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
2278:
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 26
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 26
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 27
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2281f
	addi %r8, %r29, 1
2283:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2283b
	b 2282f
2281:
	rldicl %r8, %r29, 63, 1
2284:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2284b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
2282:
	li %r5, 25
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2268b
	li %r6, 26
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 30
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2285f
	addi %r8, %r29, 0
2287:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2287b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 32(%r31)
	b 2286f
2285:
	rldicl %r8, %r29, 63, 1
2288:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2288b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 32(%r31)
2286:
	li %r5, 25
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 25
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 23
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2289f
	addi %r8, %r29, 0
	li %r9, 0
2291:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2291b
	b 2290f
2289:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2292:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2292b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2290:
	rldicr %r29, %r29, 1, 62
	addi %r29, %r29, 2
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 15
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2293f
	addi %r8, %r29, 0
2295:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2295b
	b 2294f
2293:
	rldicl %r8, %r29, 63, 1
2296:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2296b
2294:
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 15
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2297f
	addi %r8, %r29, 0
2299:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2299b
	b 2298f
2297:
	rldicl %r8, %r29, 63, 1
2300:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2300b
2298:
	li %r5, 17
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 15
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2301f
	addi %r8, %r29, 0
2303:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2303b
	b 2302f
2301:
	rldicl %r8, %r29, 63, 1
2304:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2304b
2302:
	addi %r29, %r29, -2
	rldicl %r29, %r29, 63, 1
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	li %r5, 28
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 25
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2305f
	addi %r8, %r29, 0
2307:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2307b
	b 2306f
2305:
	rldicl %r8, %r29, 63, 1
2308:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2308b
2306:
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 25
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2309f
	addi %r8, %r29, 0
2311:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2311b
	b 2310f
2309:
	rldicl %r8, %r29, 63, 1
2312:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2312b
2310:
	rldicr %r27, %r29, 5, 58
	rldicr %r29, %r29, 1, 62
	addi %r29, %r29, 2
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
2313:
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 24(%r31)
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 15
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 24(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2314f
	addi %r8, %r29, 0
2316:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2316b
	b 2315f
2314:
	rldicl %r8, %r29, 63, 1
2317:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2317b
2315:
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 15
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2318f
	addi %r8, %r29, 0
	li %r9, 0
2320:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2320b
	b 2319f
2318:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2321:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2321b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2319:
	li %r5, 17
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 17
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 20
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2322f
	addi %r8, %r29, 0
	li %r9, 0
2324:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2324b
	b 2323f
2322:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2325:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2325b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2323:
	li %r9, 0
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2326f
	addi %r8, %r29, 0
2328:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2328b
	b 2327f
2326:
	rldicl %r8, %r29, 63, 1
2329:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2329b
2327:
	li %r9, 0
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2330f
	addi %r8, %r29, 0
2332:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2332b
	b 2331f
2330:
	rldicl %r8, %r29, 63, 1
2333:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2333b
2331:
	addi %r27, %r27, -1
	cmpldi %cr0, %r27, 0
	bne %cr0, 2313b
	li %r9, 0
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2334f
	addi %r8, %r29, 0
2336:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2336b
	b 2335f
2334:
	rldicl %r8, %r29, 63, 1
2337:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2337b
2335:
	li %r9, 0
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2338f
	addi %r8, %r29, 0
2340:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2340b
	b 2339f
2338:
	rldicl %r8, %r29, 63, 1
2341:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2341b
2339:
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 17
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 19
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2342f
	addi %r8, %r29, 0
	li %r9, 0
2344:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2344b
	b 2343f
2342:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2345:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2345b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2343:
	stw %r9, 36(%r31)
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 18
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2346f
	addi %r8, %r29, 0
	li %r9, 0
2348:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2348b
	b 2347f
2346:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2349:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2349b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2347:
	stw %r9, 40(%r31)
	addi %r29, %r29, -2
	rldicl %r29, %r29, 63, 1
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 30
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2350f
	addi %r8, %r29, 0
2352:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2352b
	b 2351f
2350:
	rldicl %r8, %r29, 63, 1
2353:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2353b
2351:
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 30
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2354f
	addi %r8, %r29, 0
2356:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2356b
	b 2355f
2354:
	rldicl %r8, %r29, 63, 1
2357:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2357b
2355:
	rldicr %r27, %r29, 5, 58
	addi %r27, %r27, 32
2358:
	rldicr %r29, %r29, 1, 62
	addi %r29, %r29, 2
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	li %r9, 0
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2359f
	addi %r8, %r29, 0
2361:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2361b
	b 2360f
2359:
	rldicl %r8, %r29, 63, 1
2362:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2362b
2360:
	addi %r29, %r29, -2
	rldicl %r29, %r29, 63, 1
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2363f
	addi %r8, %r29, 0
2365:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2365b
	b 2364f
2363:
	rldicl %r8, %r29, 63, 1
2366:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2366b
2364:
	rldicr %r29, %r29, 1, 62
	addi %r29, %r29, 2
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	li %r9, 0
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2367f
	addi %r8, %r29, 0
2369:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2369b
	b 2368f
2367:
	rldicl %r8, %r29, 63, 1
2370:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2370b
2368:
	addi %r29, %r29, -2
	rldicl %r29, %r29, 63, 1
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2371f
	addi %r8, %r29, 0
2373:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2373b
	b 2372f
2371:
	rldicl %r8, %r29, 63, 1
2374:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2374b
2372:
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2375f
	addi %r8, %r29, 0
2377:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2377b
	b 2376f
2375:
	rldicl %r8, %r29, 63, 1
2378:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2378b
2376:
	li %r9, 0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2379f
	addi %r8, %r29, 0
2381:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2381b
	b 2380f
2379:
	rldicl %r8, %r29, 63, 1
2382:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2382b
2380:
	li %r9, 1
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2383f
	addi %r8, %r29, 0
2385:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2385b
	b 2384f
2383:
	rldicl %r8, %r29, 63, 1
2386:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2386b
2384:
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2387f
	addi %r8, %r29, 0
	li %r9, 0
2389:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2389b
	b 2388f
2387:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2390:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2390b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2388:
	stw %r9, 44(%r31)
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 8
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 44(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2391f
	addi %r8, %r29, 0
2393:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2393b
	b 2392f
2391:
	rldicl %r8, %r29, 63, 1
2394:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2394b
2392:
	lwz %r9, 44(%r31)
	li %r0, 1
	xor %r9, %r9, %r0
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2395f
	addi %r8, %r29, 0
2397:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2397b
	b 2396f
2395:
	rldicl %r8, %r29, 63, 1
2398:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2398b
2396:
	addi %r27, %r27, -1
	cmpldi %cr0, %r27, 0
	bne %cr0, 2358b
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 30
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2399f
	addi %r8, %r29, 0
2401:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2401b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 48(%r31)
	b 2400f
2399:
	rldicl %r8, %r29, 63, 1
2402:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2402b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 48(%r31)
2400:
	li %r5, 9
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 30
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 4
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2403f
	addi %r8, %r29, 0
	li %r9, 0
2405:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2405b
	b 2404f
2403:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2406:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2406b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2404:
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 25
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2407f
	addi %r8, %r29, 0
	li %r9, 0
2409:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2409b
	b 2408f
2407:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2410:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2410b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2408:
	li %r9, 0
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2411f
	addi %r8, %r29, 0
2413:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2413b
	b 2412f
2411:
	rldicl %r8, %r29, 63, 1
2414:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2414b
2412:
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 25
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 4
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2415f
	addi %r8, %r29, 0
	li %r9, 0
2417:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2417b
	b 2416f
2415:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2418:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2418b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2416:
	li %r9, 0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2419f
	addi %r8, %r29, 0
2421:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2421b
	b 2420f
2419:
	rldicl %r8, %r29, 63, 1
2422:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2422b
2420:
	li %r6, 1
	lwz %r0, 0(%r31)
	xor %r0, %r0, %r6
	lwz %r3, 4(%r31)
	xor %r3, %r3, %r6
	and %r0, %r0, %r3
	lwz %r3, 28(%r31)
	and %r0, %r0, %r3
	lwz %r3, 32(%r31)
	and %r0, %r0, %r3
	lwz %r3, 36(%r31)
	xor %r3, %r3, %r6
	and %r0, %r0, %r3
	lwz %r3, 40(%r31)
	xor %r3, %r3, %r6
	and %r0, %r0, %r3
	lwz %r3, 48(%r31)
	and %r0, %r0, %r3
	stw %r0, 152(%r31)
	addi %r5, %r21, 0
	addi %r8, %r25, 0
	lwz %r9, 152(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r6, 5
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	add %r6, %r6, %r8
	addi %r6, %r6, -1
2423:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2423b
	addi %r5, %r23, 0
	addi %r8, %r25, 0
	lwz %r9, 152(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	add %r6, %r6, %r8
	addi %r6, %r6, -1
2424:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2424b
	lwz %r3, 152(%r31)
25:
	li %r11, 44
	mulld %r11, %r11, %r30
	add %r11, %r11, %r31
	addi %r11, %r11, 160
	ld %r14, 0(%r11)
	ld %r15, 8(%r11)
	ld %r16, 16(%r11)
	ld %r17, 24(%r11)
	ld %r18, 32(%r11)
	ld %r19, 40(%r11)
	ld %r20, 48(%r11)
	ld %r21, 56(%r11)
	ld %r22, 64(%r11)
	ld %r23, 72(%r11)
	ld %r24, 80(%r11)
	ld %r25, 88(%r11)
	ld %r26, 96(%r11)
	ld %r27, 104(%r11)
	ld %r28, 112(%r11)
	ld %r29, 120(%r11)
	ld %r30, 128(%r11)
	ld %r31, 136(%r11)
	blr
