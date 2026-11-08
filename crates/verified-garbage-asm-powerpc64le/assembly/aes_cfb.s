// The functions of `src/aes_cfb.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_cfb128_encrypt:
	mflr %r0
	std %r0, 2112(%r8)
	std %r14, 2064(%r8)
	std %r15, 2072(%r8)
	std %r16, 2080(%r8)
	std %r17, 2088(%r8)
	std %r18, 2096(%r8)
	std %r19, 2104(%r8)
	or %r14, %r3, %r3
	or %r15, %r4, %r4
	or %r16, %r5, %r5
	or %r17, %r6, %r6
	or %r18, %r7, %r7
	or %r19, %r8, %r8
	cmpldi %cr0, %r18, 0
	beq %cr0, 20f
22:
	or %r3, %r14, %r14
	or %r4, %r15, %r15
	or %r5, %r16, %r16
	li %r6, 1
	or %r7, %r19, %r19
	bl {vg_aes_encrypt_blocks}
	ld %r9, 0(%r17)
	ld %r10, 0(%r16)
	xor %r9, %r9, %r10
	std %r9, 0(%r17)
	ld %r9, 8(%r17)
	ld %r10, 8(%r16)
	xor %r9, %r9, %r10
	std %r9, 8(%r17)
	ld %r9, 0(%r17)
	std %r9, 0(%r16)
	ld %r9, 8(%r17)
	std %r9, 8(%r16)
	addi %r17, %r17, 16
	addi %r18, %r18, -1
	cmpldi %cr0, %r18, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r0, 2112(%r19)
	ld %r14, 2064(%r19)
	ld %r15, 2072(%r19)
	ld %r16, 2080(%r19)
	ld %r17, 2088(%r19)
	ld %r18, 2096(%r19)
	ld %r19, 2104(%r19)
	mtlr %r0
	blr

vg_aes_cfb128_decrypt:
	mflr %r0
	std %r0, 2112(%r8)
	std %r14, 2064(%r8)
	std %r15, 2072(%r8)
	std %r16, 2080(%r8)
	std %r17, 2088(%r8)
	std %r18, 2096(%r8)
	std %r19, 2104(%r8)
	or %r14, %r3, %r3
	or %r15, %r4, %r4
	or %r16, %r5, %r5
	or %r17, %r6, %r6
	or %r18, %r7, %r7
	or %r19, %r8, %r8
	cmpldi %cr0, %r18, 0
	beq %cr0, 20f
	rldicl %r9, %r18, 61, 3
	cmpldi %cr0, %r9, 0
	beq %cr0, 22f
24:
	ld %r9, 0(%r16)
	std %r9, 0(%r19)
	ld %r9, 8(%r16)
	std %r9, 8(%r19)
	ld %r9, 0(%r17)
	std %r9, 16(%r19)
	ld %r9, 8(%r17)
	std %r9, 24(%r19)
	ld %r9, 16(%r17)
	std %r9, 32(%r19)
	ld %r9, 24(%r17)
	std %r9, 40(%r19)
	ld %r9, 32(%r17)
	std %r9, 48(%r19)
	ld %r9, 40(%r17)
	std %r9, 56(%r19)
	ld %r9, 48(%r17)
	std %r9, 64(%r19)
	ld %r9, 56(%r17)
	std %r9, 72(%r19)
	ld %r9, 64(%r17)
	std %r9, 80(%r19)
	ld %r9, 72(%r17)
	std %r9, 88(%r19)
	ld %r9, 80(%r17)
	std %r9, 96(%r19)
	ld %r9, 88(%r17)
	std %r9, 104(%r19)
	ld %r9, 96(%r17)
	std %r9, 112(%r19)
	ld %r9, 104(%r17)
	std %r9, 120(%r19)
	or %r3, %r14, %r14
	or %r4, %r15, %r15
	or %r5, %r19, %r19
	li %r6, 8
	addi %r7, %r19, 128
	bl {vg_aes_encrypt_blocks}
	ld %r9, 112(%r17)
	std %r9, 0(%r16)
	ld %r9, 120(%r17)
	std %r9, 8(%r16)
	ld %r9, 0(%r17)
	ld %r10, 0(%r19)
	xor %r9, %r9, %r10
	std %r9, 0(%r17)
	ld %r9, 8(%r17)
	ld %r10, 8(%r19)
	xor %r9, %r9, %r10
	std %r9, 8(%r17)
	ld %r9, 16(%r17)
	ld %r10, 16(%r19)
	xor %r9, %r9, %r10
	std %r9, 16(%r17)
	ld %r9, 24(%r17)
	ld %r10, 24(%r19)
	xor %r9, %r9, %r10
	std %r9, 24(%r17)
	ld %r9, 32(%r17)
	ld %r10, 32(%r19)
	xor %r9, %r9, %r10
	std %r9, 32(%r17)
	ld %r9, 40(%r17)
	ld %r10, 40(%r19)
	xor %r9, %r9, %r10
	std %r9, 40(%r17)
	ld %r9, 48(%r17)
	ld %r10, 48(%r19)
	xor %r9, %r9, %r10
	std %r9, 48(%r17)
	ld %r9, 56(%r17)
	ld %r10, 56(%r19)
	xor %r9, %r9, %r10
	std %r9, 56(%r17)
	ld %r9, 64(%r17)
	ld %r10, 64(%r19)
	xor %r9, %r9, %r10
	std %r9, 64(%r17)
	ld %r9, 72(%r17)
	ld %r10, 72(%r19)
	xor %r9, %r9, %r10
	std %r9, 72(%r17)
	ld %r9, 80(%r17)
	ld %r10, 80(%r19)
	xor %r9, %r9, %r10
	std %r9, 80(%r17)
	ld %r9, 88(%r17)
	ld %r10, 88(%r19)
	xor %r9, %r9, %r10
	std %r9, 88(%r17)
	ld %r9, 96(%r17)
	ld %r10, 96(%r19)
	xor %r9, %r9, %r10
	std %r9, 96(%r17)
	ld %r9, 104(%r17)
	ld %r10, 104(%r19)
	xor %r9, %r9, %r10
	std %r9, 104(%r17)
	ld %r9, 112(%r17)
	ld %r10, 112(%r19)
	xor %r9, %r9, %r10
	std %r9, 112(%r17)
	ld %r9, 120(%r17)
	ld %r10, 120(%r19)
	xor %r9, %r9, %r10
	std %r9, 120(%r17)
	addi %r17, %r17, 128
	addi %r18, %r18, -8
	rldicl %r9, %r18, 61, 3
	cmpldi %cr0, %r9, 0
	bne %cr0, 24b
	b 23f
22:
23:
	cmpldi %cr0, %r18, 0
	beq %cr0, 25f
27:
	or %r3, %r14, %r14
	or %r4, %r15, %r15
	or %r5, %r16, %r16
	li %r6, 1
	or %r7, %r19, %r19
	bl {vg_aes_encrypt_blocks}
	ld %r9, 0(%r17)
	ld %r10, 0(%r16)
	xor %r9, %r9, %r10
	std %r9, 0(%r17)
	ld %r9, 8(%r17)
	ld %r10, 8(%r16)
	xor %r9, %r9, %r10
	std %r9, 8(%r17)
	ld %r9, 0(%r16)
	ld %r10, 0(%r17)
	xor %r9, %r9, %r10
	std %r9, 0(%r16)
	ld %r9, 8(%r16)
	ld %r10, 8(%r17)
	xor %r9, %r9, %r10
	std %r9, 8(%r16)
	addi %r17, %r17, 16
	addi %r18, %r18, -1
	cmpldi %cr0, %r18, 0
	bne %cr0, 27b
	b 26f
25:
26:
	b 21f
20:
21:
	ld %r0, 2112(%r19)
	ld %r14, 2064(%r19)
	ld %r15, 2072(%r19)
	ld %r16, 2080(%r19)
	ld %r17, 2088(%r19)
	ld %r18, 2096(%r19)
	ld %r19, 2104(%r19)
	mtlr %r0
	blr

vg_aes_cfb128_encrypt_final:
	stdu %r1, -96(%r1)
	addi %r9, %r1, 32
	mflr %r0
	std %r0, 0(%r9)
	std %r14, 8(%r9)
	std %r15, 16(%r9)
	std %r16, 24(%r9)
	std %r19, 32(%r9)
	std %r30, 40(%r9)
	std %r31, 48(%r9)
	std %r20, 56(%r9)
	or %r14, %r3, %r3
	or %r15, %r4, %r4
	or %r16, %r5, %r5
	or %r19, %r8, %r8
	or %r20, %r9, %r9
	rldicl %r10, %r7, 60, 4
	rldicr %r11, %r10, 4, 59
	add %r31, %r6, %r11
	subf %r30, %r11, %r7
	or %r7, %r10, %r10
	bl {vg_aes_cfb128_encrypt}
	cmpldi %cr0, %r30, 0
	beq %cr0, 20f
	or %r3, %r14, %r14
	or %r4, %r15, %r15
	or %r5, %r16, %r16
	li %r6, 1
	or %r7, %r19, %r19
	bl {vg_aes_encrypt_blocks}
	or %r8, %r16, %r16
22:
	lbz %r9, 0(%r31)
	lbz %r10, 0(%r8)
	xor %r9, %r9, %r10
	stb %r9, 0(%r31)
	addi %r8, %r8, 1
	addi %r31, %r31, 1
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r0, 0(%r20)
	ld %r14, 8(%r20)
	ld %r15, 16(%r20)
	ld %r16, 24(%r20)
	ld %r19, 32(%r20)
	ld %r30, 40(%r20)
	ld %r31, 48(%r20)
	ld %r20, 56(%r20)
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
	addi %r1, %r1, 96
	blr

vg_aes_cfb128_decrypt_final:
	stdu %r1, -96(%r1)
	addi %r9, %r1, 32
	mflr %r0
	std %r0, 0(%r9)
	std %r14, 8(%r9)
	std %r15, 16(%r9)
	std %r16, 24(%r9)
	std %r19, 32(%r9)
	std %r30, 40(%r9)
	std %r31, 48(%r9)
	std %r20, 56(%r9)
	or %r14, %r3, %r3
	or %r15, %r4, %r4
	or %r16, %r5, %r5
	or %r19, %r8, %r8
	or %r20, %r9, %r9
	rldicl %r10, %r7, 60, 4
	rldicr %r11, %r10, 4, 59
	add %r31, %r6, %r11
	subf %r30, %r11, %r7
	or %r7, %r10, %r10
	bl {vg_aes_cfb128_decrypt}
	cmpldi %cr0, %r30, 0
	beq %cr0, 20f
	or %r3, %r14, %r14
	or %r4, %r15, %r15
	or %r5, %r16, %r16
	li %r6, 1
	or %r7, %r19, %r19
	bl {vg_aes_encrypt_blocks}
	or %r8, %r16, %r16
22:
	lbz %r9, 0(%r31)
	lbz %r10, 0(%r8)
	xor %r9, %r9, %r10
	stb %r9, 0(%r31)
	addi %r8, %r8, 1
	addi %r31, %r31, 1
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r0, 0(%r20)
	ld %r14, 8(%r20)
	ld %r15, 16(%r20)
	ld %r16, 24(%r20)
	ld %r19, 32(%r20)
	ld %r30, 40(%r20)
	ld %r31, 48(%r20)
	ld %r20, 56(%r20)
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
	addi %r1, %r1, 96
	blr
