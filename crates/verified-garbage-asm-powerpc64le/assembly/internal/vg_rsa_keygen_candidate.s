// The functions of `src/internal/vg_rsa_keygen_candidate.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_keygen_candidate:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -176(%r1)
	addi %r11, %r1, 0
	std %r14, 32(%r11)
	std %r15, 40(%r11)
	std %r16, 48(%r11)
	std %r17, 56(%r11)
	std %r18, 64(%r11)
	std %r19, 72(%r11)
	std %r20, 80(%r11)
	std %r21, 88(%r11)
	std %r22, 96(%r11)
	std %r23, 104(%r11)
	std %r24, 112(%r11)
	std %r25, 120(%r11)
	std %r26, 128(%r11)
	std %r27, 136(%r11)
	std %r28, 144(%r11)
	std %r29, 152(%r11)
	std %r30, 160(%r11)
	std %r31, 168(%r11)
	addi %r23, %r3, 0
	addi %r24, %r4, 0
	addi %r25, %r5, 0
	addi %r21, %r6, 0
	addi %r30, %r7, 0
	addi %r18, %r8, 0
	addi %r19, %r9, 0
	addi %r26, %r10, 0
	addi %r27, %r1, 320
	ld %r27, 0(%r27)
	addi %r31, %r1, 328
	ld %r31, 0(%r31)
	addi %r11, %r1, 336
	ld %r11, 0(%r11)
	li %r28, 0
	addi %r14, %r23, 0
	addi %r17, %r24, 0
	li %r0, 0
20:
	stb %r0, 0(%r14)
	addi %r14, %r14, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 20b
	subf %r5, %r24, %r27
	rldicl %r5, %r5, 1, 63
	li %r0, 1
	xor %r5, %r5, %r0
	rldicl %r0, %r27, 1, 63
	or %r5, %r5, %r0
	cmpldi %cr0, %r5, 0
	beq %cr0, 21f
	std %r11, 0(%r31)
	rldicl %r3, %r24, 61, 3
	std %r3, 48(%r31)
	addi %r29, %r3, 2
	rldicr %r29, %r29, 3, 60
	std %r29, 224(%r31)
	addi %r10, %r31, 256
	rldicr %r11, %r3, 1, 62
	addi %r3, %r10, 0
	std %r3, 64(%r31)
	addi %r3, %r10, 0
	add %r3, %r3, %r29
	std %r3, 72(%r31)
	addi %r3, %r10, 0
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	std %r3, 80(%r31)
	addi %r3, %r10, 0
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	std %r3, 88(%r31)
	addi %r3, %r10, 0
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	std %r3, 96(%r31)
	addi %r3, %r10, 0
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	std %r3, 104(%r31)
	addi %r3, %r10, 0
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	std %r3, 112(%r31)
	addi %r3, %r10, 0
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	std %r3, 120(%r31)
	addi %r14, %r10, 0
	li %r17, 35
	mulld %r17, %r17, %r29
	rldicl %r17, %r17, 61, 3
	li %r0, 0
23:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 23b
	addi %r12, %r26, 0
	addi %r6, %r24, 0
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
	ld %r3, 0(%r10)
	li %r4, 1
	or %r3, %r3, %r4
	std %r3, 0(%r10)
	rldicr %r5, %r11, 2, 61
	add %r5, %r5, %r10
	addi %r5, %r5, -8
	ld %r3, 0(%r5)
	lis %r4, -16384
	rldicr %r4, %r4, 32, 31
	or %r3, %r3, %r4
	std %r3, 0(%r5)
	addi %r28, %r24, 0
	cmpldi %cr0, %r19, 0
	beq %cr0, 26f
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r12, %r18, 0
	addi %r6, %r24, 0
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
	addi %r10, %r31, 256
	addi %r8, %r10, 0
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
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
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
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
210:
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
	bne %cr0, 210b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r31, 256
	addi %r22, %r20, 0
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
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r10, %r10, 0
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
211:
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
	bne %cr0, 211b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r31, 256
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
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
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
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r20, %r22, 0
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	addi %r17, %r11, 0
212:
	lwz %r0, 0(%r15)
	lwz %r3, 0(%r14)
	xor %r3, %r3, %r0
	and %r3, %r3, %r20
	xor %r3, %r3, %r0
	stw %r3, 0(%r16)
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 212b
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	rldicr %r6, %r11, 2, 61
	add %r5, %r5, %r6
	addi %r5, %r5, -16
	lis %r0, 4096
	std %r0, 0(%r5)
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
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
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
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
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
213:
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
	bne %cr0, 213b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r31, 256
	li %r0, 1
	and %r22, %r20, %r0
	xor %r22, %r22, %r0
	b 27f
26:
	li %r22, 0
27:
	cmpldi %cr0, %r22, 0
	bne %cr0, 214f
	li %r3, 0
	addi %r14, %r21, 0
	addi %r17, %r30, 0
216:
	rldicr %r3, %r3, 8, 55
	lbz %r0, 0(%r14)
	add %r3, %r3, %r0
	addi %r14, %r14, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 216b
	addi %r21, %r3, 0
	li %r0, 1
	and %r5, %r21, %r0
	cmpldi %cr0, %r5, 0
	beq %cr0, 217f
	addi %r5, %r21, -1
	cmpldi %cr0, %r5, 0
	beq %cr0, 219f
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	rldicl %r17, %r11, 63, 1
221:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 221b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	ld %r3, 0(%r14)
	addi %r3, %r3, -1
	std %r3, 0(%r14)
	rldicr %r5, %r11, 2, 61
	add %r14, %r14, %r5
	rldicl %r17, %r11, 63, 1
	li %r3, 0
222:
	addi %r14, %r14, -8
	ld %r7, 0(%r14)
	li %r6, 64
223:
	rldicl %r8, %r3, 1, 63
	rldicl %r9, %r7, 1, 63
	rldicr %r3, %r3, 1, 62
	add %r3, %r3, %r9
	rldicr %r7, %r7, 1, 62
	rldicr %r15, %r3, 1, 62
	rldicl %r15, %r15, 63, 1
	rldicr %r16, %r21, 1, 62
	rldicl %r16, %r16, 63, 1
	subf %r15, %r16, %r15
	rldicl %r15, %r15, 1, 63
	rldicl %r9, %r3, 1, 63
	rldicl %r16, %r21, 1, 63
	xor %r9, %r9, %r16
	and %r16, %r16, %r9
	li %r0, 1
	xor %r9, %r9, %r0
	and %r9, %r9, %r15
	or %r9, %r9, %r16
	li %r0, 1
	xor %r9, %r9, %r0
	or %r9, %r9, %r8
	li %r0, 0
	subf %r9, %r9, %r0
	subf %r4, %r21, %r3
	xor %r4, %r4, %r3
	and %r4, %r4, %r9
	xor %r3, %r3, %r4
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 223b
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 222b
	li %r9, 128
224:
	rldicr %r15, %r3, 1, 62
	rldicl %r15, %r15, 63, 1
	rldicr %r16, %r21, 1, 62
	rldicl %r16, %r16, 63, 1
	subf %r15, %r16, %r15
	rldicl %r15, %r15, 1, 63
	rldicl %r5, %r3, 1, 63
	rldicl %r16, %r21, 1, 63
	xor %r5, %r5, %r16
	and %r16, %r16, %r5
	li %r0, 1
	xor %r5, %r5, %r0
	and %r5, %r5, %r15
	or %r5, %r5, %r16
	li %r0, 0
	subf %r5, %r5, %r0
	li %r0, 1
	and %r4, %r3, %r0
	li %r0, 0
	subf %r4, %r4, %r0
	subf %r6, %r21, %r3
	subf %r7, %r3, %r21
	xor %r7, %r7, %r6
	and %r7, %r7, %r5
	xor %r6, %r6, %r7
	xor %r7, %r3, %r21
	and %r7, %r7, %r5
	xor %r7, %r7, %r21
	xor %r6, %r6, %r3
	and %r6, %r6, %r4
	xor %r3, %r3, %r6
	xor %r7, %r7, %r21
	and %r7, %r7, %r4
	xor %r21, %r21, %r7
	rldicl %r3, %r3, 63, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 224b
	addi %r22, %r21, -1
	b 220f
219:
	li %r22, 0
220:
	b 218f
217:
	li %r22, 1
218:
	cmpldi %cr0, %r22, 0
	bne %cr0, 225f
	std %r26, 136(%r31)
	std %r27, 144(%r31)
	std %r28, 152(%r31)
	std %r24, 216(%r31)
	ld %r3, 48(%r31)
	li %r5, 27
	addi %r4, %r3, -5
	rldicl %r4, %r4, 1, 63
	addi %r4, %r4, -1
	li %r6, 8
	xor %r6, %r6, %r5
	and %r6, %r6, %r4
	xor %r5, %r5, %r6
	addi %r4, %r3, -6
	rldicl %r4, %r4, 1, 63
	addi %r4, %r4, -1
	li %r6, 7
	xor %r6, %r6, %r5
	and %r6, %r6, %r4
	xor %r5, %r5, %r6
	addi %r4, %r3, -7
	rldicl %r4, %r4, 1, 63
	addi %r4, %r4, -1
	li %r6, 6
	xor %r6, %r6, %r5
	and %r6, %r6, %r4
	xor %r5, %r5, %r6
	addi %r4, %r3, -8
	rldicl %r4, %r4, 1, 63
	addi %r4, %r4, -1
	li %r6, 5
	xor %r6, %r6, %r5
	and %r6, %r6, %r4
	xor %r5, %r5, %r6
	addi %r4, %r3, -22
	rldicl %r4, %r4, 1, 63
	addi %r4, %r4, -1
	li %r6, 4
	xor %r6, %r6, %r5
	and %r6, %r6, %r4
	xor %r5, %r5, %r6
	addi %r4, %r3, -59
	rldicl %r4, %r4, 1, 63
	addi %r4, %r4, -1
	li %r6, 3
	xor %r6, %r6, %r5
	and %r6, %r6, %r4
	xor %r5, %r5, %r6
	std %r5, 168(%r31)
	li %r4, 16
	subf %r4, %r3, %r4
	rldicl %r4, %r4, 1, 63
	li %r5, 512
	mulld %r4, %r4, %r5
	add %r4, %r4, %r5
	std %r4, 128(%r31)
	std %r23, 24(%r31)
	std %r24, 40(%r31)
	bcl 20, 31, 2f
2:
	mflr %r23
	addis %r23, %r23, ({VG_RSA_KEYGEN_TRIAL32}
	addi %r23, %r23, ({VG_RSA_KEYGEN_TRIAL32}
	ld %r24, 128(%r31)
227:
	ld %r8, 0(%r23)
	rldicl %r9, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	rldicl %r8, %r8, 32, 32
	li %r3, 0
	addi %r5, %r10, 0
	addi %r4, %r11, 0
228:
	lwz %r0, 0(%r5)
	add %r0, %r0, %r3
	mulld %r6, %r0, %r9
	rldicr %r6, %r6, 32, 31
	rldicl %r6, %r6, 32, 32
	mulld %r6, %r6, %r8
	add %r6, %r6, %r0
	rldicl %r3, %r6, 32, 32
	addi %r5, %r5, 4
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 228b
	addi %r6, %r3, -1
	rldicl %r6, %r6, 1, 63
	xor %r7, %r3, %r8
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	or %r22, %r6, %r7
	addi %r23, %r23, 8
	addi %r24, %r24, -1
	addi %r6, %r22, -1
	and %r24, %r24, %r6
	cmpldi %cr0, %r24, 0
	bne %cr0, 227b
	ld %r23, 24(%r31)
	ld %r24, 40(%r31)
	cmpldi %cr0, %r22, 0
	bne %cr0, 229f
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
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	li %r3, 0
	subf %r3, %r12, %r3
	std %r3, 56(%r31)
	rldicr %r12, %r3, 32, 31
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
231:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 231b
	rldicr %r14, %r11, 2, 61
	add %r14, %r14, %r5
	addi %r14, %r14, -8
	li %r0, 1
	std %r0, 0(%r14)
	rldicl %r4, %r11, 63, 1
	addi %r4, %r4, 64
232:
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	addi %r17, %r11, 0
	li %r20, 0
233:
	lwz %r0, 0(%r15)
	add %r0, %r0, %r0
	add %r0, %r0, %r20
	stw %r0, 0(%r14)
	rldicl %r20, %r0, 32, 32
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 233b
	stw %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
234:
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
	bne %cr0, 234b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	addi %r17, %r11, 0
235:
	lwz %r0, 0(%r15)
	lwz %r3, 0(%r14)
	xor %r3, %r3, %r0
	and %r3, %r3, %r20
	xor %r3, %r3, %r0
	stw %r3, 0(%r16)
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 235b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 232b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
236:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 236b
237:
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
	beq %cr0, 238f
240:
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
	bne %cr0, 240b
	b 239f
238:
239:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 241f
243:
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
	bne %cr0, 243b
	b 242f
241:
242:
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
	bne %cr0, 237b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
244:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 244b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
245:
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
	bne %cr0, 245b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
246:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 246b
247:
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
	beq %cr0, 248f
250:
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
	bne %cr0, 250b
	b 249f
248:
249:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 251f
253:
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
	bne %cr0, 253b
	b 252f
251:
252:
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
	bne %cr0, 247b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
254:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 254b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
255:
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
	bne %cr0, 255b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
256:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 256b
257:
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
	beq %cr0, 258f
260:
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
	bne %cr0, 260b
	b 259f
258:
259:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 261f
263:
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
	bne %cr0, 263b
	b 262f
261:
262:
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
	bne %cr0, 257b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
264:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 264b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
265:
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
	bne %cr0, 265b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
266:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 266b
267:
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
	beq %cr0, 268f
270:
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
	bne %cr0, 270b
	b 269f
268:
269:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 271f
273:
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
	bne %cr0, 273b
	b 272f
271:
272:
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
	bne %cr0, 267b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
274:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 274b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
275:
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
	bne %cr0, 275b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
276:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 276b
277:
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
	beq %cr0, 278f
280:
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
	bne %cr0, 280b
	b 279f
278:
279:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 281f
283:
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
	bne %cr0, 283b
	b 282f
281:
282:
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
	bne %cr0, 277b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
284:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 284b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
285:
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
	bne %cr0, 285b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
286:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 286b
287:
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
	beq %cr0, 288f
290:
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
	bne %cr0, 290b
	b 289f
288:
289:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 291f
293:
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
	bne %cr0, 293b
	b 292f
291:
292:
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
	bne %cr0, 287b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
294:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 294b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
295:
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
	bne %cr0, 295b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
296:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 296b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	li %r0, 1
	stw %r0, 0(%r14)
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r6, %r10, 0
	add %r6, %r6, %r29
	addi %r7, %r10, 0
	add %r7, %r7, %r29
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
297:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 297b
298:
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
	beq %cr0, 299f
2101:
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
	bne %cr0, 2101b
	b 2100f
299:
2100:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2102f
2104:
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
	bne %cr0, 2104b
	b 2103f
2102:
2103:
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
	bne %cr0, 298b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2105:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2105b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2106:
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
	bne %cr0, 2106b
	addi %r8, %r10, 0
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
2107:
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
	bne %cr0, 2107b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r31, 256
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
2108:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2108b
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r6, 0
	li %r4, 1
2109:
	ld %r7, 0(%r14)
	xor %r7, %r7, %r4
	li %r4, 0
	addi %r3, %r6, 0
	rldicl %r5, %r3, 63, 1
	li %r0, 1
	and %r0, %r3, %r0
	or %r5, %r5, %r0
	addi %r5, %r5, -1
	rldicl %r5, %r5, 1, 63
	li %r0, 0
	subf %r5, %r5, %r0
	and %r7, %r7, %r5
	or %r6, %r6, %r7
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2109b
	li %r7, 0
	subf %r7, %r6, %r7
	and %r6, %r6, %r7
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicr %r7, %r11, 2, 61
	add %r14, %r14, %r7
	std %r6, 0(%r14)
	li %r9, 0
	addi %r9, %r9, -1
	addi %r15, %r10, 0
	addi %r16, %r10, 0
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	ld %r5, 0(%r15)
	addi %r15, %r15, 8
	rldicl %r17, %r11, 63, 1
	addi %r17, %r17, -1
2110:
	ld %r3, 0(%r15)
	rldicr %r4, %r3, 63, 0
	rldicl %r6, %r5, 63, 1
	or %r6, %r6, %r4
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r5, %r3, 0
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2110b
	rldicl %r6, %r5, 63, 1
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicr %r7, %r11, 2, 61
	add %r14, %r14, %r7
	ld %r3, 0(%r14)
	lis %r4, -8739
	ori %r4, %r4, 56797
	rldicr %r4, %r4, 32, 31
	oris %r4, %r4, 56797
	ori %r4, %r4, 56797
	and %r3, %r3, %r4
	rldicl %r5, %r3, 63, 1
	li %r0, 1
	and %r0, %r3, %r0
	or %r5, %r5, %r0
	addi %r5, %r5, -1
	rldicl %r5, %r5, 1, 63
	li %r0, 0
	subf %r5, %r5, %r0
	li %r9, 0
	addi %r9, %r9, -1
	xor %r9, %r9, %r5
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
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r16, %r10, 0
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	ld %r5, 0(%r15)
	addi %r15, %r15, 8
	rldicl %r17, %r11, 63, 1
	addi %r17, %r17, -1
2111:
	ld %r3, 0(%r15)
	rldicr %r4, %r3, 63, 0
	rldicl %r6, %r5, 63, 1
	or %r6, %r6, %r4
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r5, %r3, 0
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2111b
	rldicl %r6, %r5, 63, 1
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicr %r7, %r11, 2, 61
	add %r14, %r14, %r7
	ld %r3, 0(%r14)
	lis %r4, -26215
	ori %r4, %r4, 39321
	rldicr %r4, %r4, 32, 31
	oris %r4, %r4, 39321
	ori %r4, %r4, 39321
	and %r3, %r3, %r4
	rldicl %r5, %r3, 63, 1
	li %r0, 1
	and %r0, %r3, %r0
	or %r5, %r5, %r0
	addi %r5, %r5, -1
	rldicl %r5, %r5, 1, 63
	li %r0, 0
	subf %r5, %r5, %r0
	li %r9, 0
	addi %r9, %r9, -1
	xor %r9, %r9, %r5
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
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r16, %r10, 0
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	ld %r5, 0(%r15)
	addi %r15, %r15, 8
	rldicl %r17, %r11, 63, 1
	addi %r17, %r17, -1
2112:
	ld %r3, 0(%r15)
	rldicr %r4, %r3, 63, 0
	rldicl %r6, %r5, 63, 1
	or %r6, %r6, %r4
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r5, %r3, 0
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2112b
	rldicl %r6, %r5, 63, 1
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicr %r7, %r11, 2, 61
	add %r14, %r14, %r7
	ld %r3, 0(%r14)
	lis %r4, 4369
	ori %r4, %r4, 4369
	rldicr %r4, %r4, 32, 31
	oris %r4, %r4, 4369
	ori %r4, %r4, 4369
	and %r3, %r3, %r4
	rldicl %r5, %r3, 63, 1
	li %r0, 1
	and %r0, %r3, %r0
	or %r5, %r5, %r0
	addi %r5, %r5, -1
	rldicl %r5, %r5, 1, 63
	li %r0, 0
	subf %r5, %r5, %r0
	li %r9, 0
	addi %r9, %r9, -1
	xor %r9, %r9, %r5
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
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r16, %r10, 0
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	ld %r5, 0(%r15)
	addi %r15, %r15, 8
	rldicl %r17, %r11, 63, 1
	addi %r17, %r17, -1
2113:
	ld %r3, 0(%r15)
	rldicr %r4, %r3, 63, 0
	rldicl %r6, %r5, 63, 1
	or %r6, %r6, %r4
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r5, %r3, 0
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2113b
	rldicl %r6, %r5, 63, 1
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	li %r3, 1
	std %r3, 176(%r31)
	li %r3, 0
	std %r3, 16(%r31)
	li %r3, 4
	std %r3, 160(%r31)
2114:
	ld %r3, 144(%r31)
	ld %r4, 152(%r31)
	subf %r3, %r4, %r3
	ld %r4, 216(%r31)
	subf %r5, %r4, %r3
	rldicl %r5, %r5, 1, 63
	li %r0, 1
	xor %r5, %r5, %r0
	rldicl %r0, %r3, 1, 63
	or %r5, %r5, %r0
	cmpldi %cr0, %r5, 0
	beq %cr0, 2115f
	ld %r12, 136(%r31)
	ld %r3, 152(%r31)
	add %r12, %r12, %r3
	ld %r6, 216(%r31)
	add %r3, %r3, %r6
	std %r3, 152(%r31)
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2117:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2117b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2118:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2118b
	addi %r10, %r31, 256
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	ld %r21, 0(%r5)
	rldicl %r21, %r21, 63, 1
	addi %r5, %r5, 8
	rldicl %r6, %r11, 63, 1
	addi %r6, %r6, -1
2119:
	ld %r3, 0(%r5)
	or %r21, %r21, %r3
	addi %r5, %r5, 8
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2119b
	rldicl %r3, %r21, 63, 1
	li %r0, 1
	and %r21, %r21, %r0
	or %r21, %r21, %r3
	addi %r21, %r21, -1
	rldicl %r21, %r21, 1, 63
	xor %r21, %r21, %r0
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
2120:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2120b
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	rldicr %r6, %r11, 2, 61
	add %r5, %r5, %r6
	li %r0, 0
	std %r0, 0(%r5)
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	ld %r3, 0(%r5)
	li %r4, 1
	or %r3, %r3, %r4
	std %r3, 0(%r5)
	addi %r8, %r10, 0
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
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2121:
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
	bne %cr0, 2121b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	li %r0, 1
	and %r3, %r20, %r0
	and %r21, %r21, %r3
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
2122:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2122b
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	rldicr %r6, %r11, 2, 61
	add %r5, %r5, %r6
	li %r0, 0
	std %r0, 0(%r5)
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	ld %r3, 0(%r5)
	li %r4, 2
	or %r3, %r3, %r4
	std %r3, 0(%r5)
	rldicr %r6, %r11, 2, 61
	add %r5, %r5, %r6
	addi %r5, %r5, -8
	li %r4, 0
	addi %r4, %r4, -1
	rldicl %r4, %r4, 63, 1
	ld %r3, 0(%r5)
	and %r3, %r3, %r4
	std %r3, 0(%r5)
	li %r0, 0
	subf %r20, %r21, %r0
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2123:
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
	bne %cr0, 2123b
	li %r20, 0
	addi %r20, %r20, -1
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
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2124:
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
	bne %cr0, 2124b
	ld %r3, 16(%r31)
	add %r3, %r3, %r21
	std %r3, 16(%r31)
	ld %r12, 56(%r31)
	rldicr %r12, %r12, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r5, %r10, 0
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2125:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2125b
2126:
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
	beq %cr0, 2127f
2129:
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
	bne %cr0, 2129b
	b 2128f
2127:
2128:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2130f
2132:
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
	bne %cr0, 2132b
	b 2131f
2130:
2131:
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
	bne %cr0, 2126b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2133:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2133b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2134:
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
	bne %cr0, 2134b
	addi %r3, %r31, 0
	ld %r4, 0(%r31)
	bl {vg_miller_rabin_round}
	rldicr %r3, %r3, 32, 31
	rldicl %r3, %r3, 32, 32
	addi %r10, %r31, 256
	ld %r11, 48(%r31)
	rldicr %r11, %r11, 1, 62
	ld %r29, 224(%r31)
	ld %r12, 56(%r31)
	rldicr %r12, %r12, 32, 31
	rldicl %r12, %r12, 32, 32
	cmpldi %cr0, %r3, 0
	beq %cr0, 2135f
	ld %r3, 176(%r31)
	addi %r3, %r3, 1
	std %r3, 176(%r31)
	li %r4, 17
	subf %r5, %r4, %r3
	rldicl %r5, %r5, 1, 63
	li %r0, 1
	xor %r5, %r5, %r0
	rldicl %r0, %r3, 1, 63
	or %r5, %r5, %r0
	addi %r7, %r5, 0
	ld %r3, 16(%r31)
	ld %r4, 168(%r31)
	subf %r5, %r4, %r3
	rldicl %r5, %r5, 1, 63
	li %r0, 1
	xor %r5, %r5, %r0
	rldicl %r0, %r3, 1, 63
	or %r5, %r5, %r0
	and %r5, %r5, %r7
	li %r4, 3
	mulld %r5, %r5, %r4
	li %r4, 4
	subf %r5, %r5, %r4
	std %r5, 160(%r31)
	b 2136f
2135:
	li %r3, 2
	std %r3, 160(%r31)
2136:
	b 2116f
2115:
	li %r3, 0
	std %r3, 160(%r31)
2116:
	ld %r3, 160(%r31)
	addi %r3, %r3, -4
	cmpldi %cr0, %r3, 0
	beq %cr0, 2114b
	ld %r28, 152(%r31)
	ld %r3, 160(%r31)
	cmpldi %cr0, %r3, 0
	beq %cr0, 2137f
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	beq %cr0, 2139f
	std %r28, 0(%r25)
	li %r3, 3
	b 2140f
2139:
	addi %r10, %r31, 256
	add %r15, %r10, %r24
	addi %r15, %r15, -1
	addi %r16, %r23, 0
	addi %r17, %r24, 0
2141:
	lbz %r0, 0(%r15)
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2141b
	std %r28, 0(%r25)
	li %r3, 1
2140:
	b 2138f
2137:
	li %r28, 0
	std %r28, 0(%r25)
	li %r3, 0
2138:
	b 230f
229:
	std %r28, 0(%r25)
	li %r3, 3
230:
	b 226f
225:
	std %r28, 0(%r25)
	li %r3, 3
226:
	b 215f
214:
	std %r28, 0(%r25)
	li %r3, 2
215:
	b 22f
21:
	li %r28, 0
	std %r28, 0(%r25)
	li %r3, 0
22:
	addi %r11, %r1, 0
	ld %r14, 32(%r11)
	ld %r15, 40(%r11)
	ld %r16, 48(%r11)
	ld %r17, 56(%r11)
	ld %r18, 64(%r11)
	ld %r19, 72(%r11)
	ld %r20, 80(%r11)
	ld %r21, 88(%r11)
	ld %r22, 96(%r11)
	ld %r23, 104(%r11)
	ld %r24, 112(%r11)
	ld %r25, 120(%r11)
	ld %r26, 128(%r11)
	ld %r27, 136(%r11)
	ld %r28, 144(%r11)
	ld %r29, 152(%r11)
	ld %r30, 160(%r11)
	ld %r31, 168(%r11)
	addi %r1, %r1, 176
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr
