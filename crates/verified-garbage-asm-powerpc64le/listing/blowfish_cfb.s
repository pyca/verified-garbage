// The functions of `src/blowfish_cfb.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blowfish_cfb64_encrypt:
	stdu %r1, -128(%r1)
	addi %r7, %r1, 32
	mflr %r0
	std %r0, 64(%r7)
	std %r29, 40(%r7)
	std %r30, 48(%r7)
	std %r31, 56(%r7)
	or %r29, %r4, %r4
	or %r30, %r6, %r6
	or %r31, %r4, %r4
	or %r6, %r5, %r5
	or %r5, %r7, %r7
	lwz %r8, 0(%r31)
	stw %r8, 72(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 76(%r5)
	or %r31, %r6, %r6
	cmpldi %cr0, %r30, 0
	beq %cr0, 20f
22:
	lwz %r8, 72(%r5)
	stw %r8, 32(%r5)
	lwz %r8, 76(%r5)
	stw %r8, 36(%r5)
	or %r6, %r5, %r5
	std %r14, 0(%r6)
	std %r15, 8(%r6)
	std %r16, 16(%r6)
	std %r17, 24(%r6)
	li %r0, 0
	addi %r16, %r6, 32
	lwbrx %r4, %r16, %r0
	addi %r12, %r16, 4
	lwbrx %r5, %r12, %r0
	addi %r8, %r3, 4096
23:
	lwz %r12, 0(%r8)
	xor %r4, %r4, %r12
	rldicr %r9, %r4, 32, 31
	rldicl %r9, %r9, 8, 56
	li %r14, 255
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 8, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 16, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	li %r10, 0
	or %r15, %r3, %r3
24:
	rldicl %r11, %r9, 62, 2
	addi %r11, %r11, -1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	and %r11, %r11, %r14
	addi %r9, %r9, -4
	lwz %r12, 0(%r15)
	and %r12, %r12, %r11
	or %r10, %r10, %r12
	lwz %r12, 256(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 8, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 512(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 16, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 768(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 24, 0, 31
	or %r10, %r10, %r12
	addi %r15, %r15, 4
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 24b
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 24, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 16, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	or %r7, %r10, %r10
	rldicr %r9, %r4, 40, 23
	rldicl %r9, %r9, 8, 56
	li %r14, 255
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 8, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 16, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	li %r10, 0
	or %r15, %r3, %r3
25:
	rldicl %r11, %r9, 62, 2
	addi %r11, %r11, -1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	and %r11, %r11, %r14
	addi %r9, %r9, -4
	lwz %r12, 1024(%r15)
	and %r12, %r12, %r11
	or %r10, %r10, %r12
	lwz %r12, 1280(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 8, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 1536(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 16, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 1792(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 24, 0, 31
	or %r10, %r10, %r12
	addi %r15, %r15, 4
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 25b
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 24, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 16, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	add %r7, %r7, %r10
	rldicr %r9, %r4, 48, 15
	rldicl %r9, %r9, 8, 56
	li %r14, 255
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 8, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 16, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	li %r10, 0
	or %r15, %r3, %r3
26:
	rldicl %r11, %r9, 62, 2
	addi %r11, %r11, -1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	and %r11, %r11, %r14
	addi %r9, %r9, -4
	lwz %r12, 2048(%r15)
	and %r12, %r12, %r11
	or %r10, %r10, %r12
	lwz %r12, 2304(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 8, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 2560(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 16, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 2816(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 24, 0, 31
	or %r10, %r10, %r12
	addi %r15, %r15, 4
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 26b
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 24, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 16, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	xor %r7, %r7, %r10
	rldicr %r9, %r4, 56, 7
	rldicl %r9, %r9, 8, 56
	li %r14, 255
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 8, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 16, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	li %r10, 0
	or %r15, %r3, %r3
27:
	rldicl %r11, %r9, 62, 2
	addi %r11, %r11, -1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	and %r11, %r11, %r14
	addi %r9, %r9, -4
	lwz %r12, 3072(%r15)
	and %r12, %r12, %r11
	or %r10, %r10, %r12
	lwz %r12, 3328(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 8, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 3584(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 16, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 3840(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 24, 0, 31
	or %r10, %r10, %r12
	addi %r15, %r15, 4
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 27b
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 24, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 16, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	add %r7, %r7, %r10
	xor %r5, %r5, %r7
	or %r12, %r4, %r4
	or %r4, %r5, %r5
	or %r5, %r12, %r12
	addi %r8, %r8, 4
	subf %r12, %r3, %r8
	addi %r12, %r12, -4160
	cmpldi %cr0, %r12, 0
	bne %cr0, 23b
	lwz %r12, 0(%r8)
	xor %r12, %r4, %r12
	lwz %r4, 4(%r8)
	xor %r4, %r4, %r5
	or %r5, %r12, %r12
	stwbrx %r4, %r16, %r0
	addi %r12, %r16, 4
	stwbrx %r5, %r12, %r0
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	or %r5, %r6, %r6
	ld %r14, 0(%r6)
	ld %r15, 8(%r6)
	ld %r16, 16(%r6)
	ld %r17, 24(%r6)
	lwz %r8, 0(%r31)
	lwz %r9, 32(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 36(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 0(%r31)
	stw %r8, 72(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 76(%r5)
	addi %r31, %r31, 8
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 22b
	b 21f
20:
21:
	or %r31, %r29, %r29
	lwz %r8, 72(%r5)
	stw %r8, 0(%r31)
	lwz %r8, 76(%r5)
	stw %r8, 4(%r31)
	ld %r29, 40(%r5)
	ld %r30, 48(%r5)
	ld %r31, 56(%r5)
	ld %r0, 64(%r5)
	mtlr %r0
	addi %r12, %r1, 32
	li %r11, 0
	std %r11, 0(%r12)
	std %r11, 8(%r12)
	std %r11, 16(%r12)
	std %r11, 24(%r12)
	std %r11, 32(%r12)
	std %r11, 40(%r12)
	std %r11, 48(%r12)
	std %r11, 56(%r12)
	std %r11, 64(%r12)
	std %r11, 72(%r12)
	std %r11, 80(%r12)
	std %r11, 88(%r12)
	addi %r1, %r1, 128
	blr

vg_blowfish_cfb64_decrypt:
	stdu %r1, -128(%r1)
	addi %r7, %r1, 32
	mflr %r0
	std %r0, 64(%r7)
	std %r29, 40(%r7)
	std %r30, 48(%r7)
	std %r31, 56(%r7)
	or %r29, %r4, %r4
	or %r30, %r6, %r6
	or %r31, %r4, %r4
	or %r6, %r5, %r5
	or %r5, %r7, %r7
	lwz %r8, 0(%r31)
	stw %r8, 72(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 76(%r5)
	or %r31, %r6, %r6
	cmpldi %cr0, %r30, 0
	beq %cr0, 20f
22:
	lwz %r8, 72(%r5)
	stw %r8, 32(%r5)
	lwz %r8, 76(%r5)
	stw %r8, 36(%r5)
	or %r6, %r5, %r5
	std %r14, 0(%r6)
	std %r15, 8(%r6)
	std %r16, 16(%r6)
	std %r17, 24(%r6)
	li %r0, 0
	addi %r16, %r6, 32
	lwbrx %r4, %r16, %r0
	addi %r12, %r16, 4
	lwbrx %r5, %r12, %r0
	addi %r8, %r3, 4096
23:
	lwz %r12, 0(%r8)
	xor %r4, %r4, %r12
	rldicr %r9, %r4, 32, 31
	rldicl %r9, %r9, 8, 56
	li %r14, 255
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 8, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 16, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	li %r10, 0
	or %r15, %r3, %r3
24:
	rldicl %r11, %r9, 62, 2
	addi %r11, %r11, -1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	and %r11, %r11, %r14
	addi %r9, %r9, -4
	lwz %r12, 0(%r15)
	and %r12, %r12, %r11
	or %r10, %r10, %r12
	lwz %r12, 256(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 8, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 512(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 16, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 768(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 24, 0, 31
	or %r10, %r10, %r12
	addi %r15, %r15, 4
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 24b
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 24, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 16, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	or %r7, %r10, %r10
	rldicr %r9, %r4, 40, 23
	rldicl %r9, %r9, 8, 56
	li %r14, 255
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 8, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 16, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	li %r10, 0
	or %r15, %r3, %r3
25:
	rldicl %r11, %r9, 62, 2
	addi %r11, %r11, -1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	and %r11, %r11, %r14
	addi %r9, %r9, -4
	lwz %r12, 1024(%r15)
	and %r12, %r12, %r11
	or %r10, %r10, %r12
	lwz %r12, 1280(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 8, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 1536(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 16, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 1792(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 24, 0, 31
	or %r10, %r10, %r12
	addi %r15, %r15, 4
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 25b
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 24, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 16, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	add %r7, %r7, %r10
	rldicr %r9, %r4, 48, 15
	rldicl %r9, %r9, 8, 56
	li %r14, 255
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 8, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 16, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	li %r10, 0
	or %r15, %r3, %r3
26:
	rldicl %r11, %r9, 62, 2
	addi %r11, %r11, -1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	and %r11, %r11, %r14
	addi %r9, %r9, -4
	lwz %r12, 2048(%r15)
	and %r12, %r12, %r11
	or %r10, %r10, %r12
	lwz %r12, 2304(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 8, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 2560(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 16, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 2816(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 24, 0, 31
	or %r10, %r10, %r12
	addi %r15, %r15, 4
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 26b
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 24, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 16, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	xor %r7, %r7, %r10
	rldicr %r9, %r4, 56, 7
	rldicl %r9, %r9, 8, 56
	li %r14, 255
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 8, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 16, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	li %r10, 0
	or %r15, %r3, %r3
27:
	rldicl %r11, %r9, 62, 2
	addi %r11, %r11, -1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	and %r11, %r11, %r14
	addi %r9, %r9, -4
	lwz %r12, 3072(%r15)
	and %r12, %r12, %r11
	or %r10, %r10, %r12
	lwz %r12, 3328(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 8, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 3584(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 16, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 3840(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 24, 0, 31
	or %r10, %r10, %r12
	addi %r15, %r15, 4
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 27b
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 24, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 16, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	add %r7, %r7, %r10
	xor %r5, %r5, %r7
	or %r12, %r4, %r4
	or %r4, %r5, %r5
	or %r5, %r12, %r12
	addi %r8, %r8, 4
	subf %r12, %r3, %r8
	addi %r12, %r12, -4160
	cmpldi %cr0, %r12, 0
	bne %cr0, 23b
	lwz %r12, 0(%r8)
	xor %r12, %r4, %r12
	lwz %r4, 4(%r8)
	xor %r4, %r4, %r5
	or %r5, %r12, %r12
	stwbrx %r4, %r16, %r0
	addi %r12, %r16, 4
	stwbrx %r5, %r12, %r0
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	or %r5, %r6, %r6
	ld %r14, 0(%r6)
	ld %r15, 8(%r6)
	ld %r16, 16(%r6)
	ld %r17, 24(%r6)
	lwz %r8, 0(%r31)
	stw %r8, 72(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 76(%r5)
	lwz %r8, 0(%r31)
	lwz %r9, 32(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 36(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	addi %r31, %r31, 8
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 22b
	b 21f
20:
21:
	or %r31, %r29, %r29
	lwz %r8, 72(%r5)
	stw %r8, 0(%r31)
	lwz %r8, 76(%r5)
	stw %r8, 4(%r31)
	ld %r29, 40(%r5)
	ld %r30, 48(%r5)
	ld %r31, 56(%r5)
	ld %r0, 64(%r5)
	mtlr %r0
	addi %r12, %r1, 32
	li %r11, 0
	std %r11, 0(%r12)
	std %r11, 8(%r12)
	std %r11, 16(%r12)
	std %r11, 24(%r12)
	std %r11, 32(%r12)
	std %r11, 40(%r12)
	std %r11, 48(%r12)
	std %r11, 56(%r12)
	std %r11, 64(%r12)
	std %r11, 72(%r12)
	std %r11, 80(%r12)
	std %r11, 88(%r12)
	addi %r1, %r1, 128
	blr
