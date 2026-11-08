// The functions of `src/internal/vg_aes_xts_encrypt.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_xts_encrypt:
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
	ld %r9, 0(%r17)
	ld %r10, 0(%r16)
	xor %r9, %r9, %r10
	std %r9, 0(%r17)
	ld %r9, 8(%r17)
	ld %r10, 8(%r16)
	xor %r9, %r9, %r10
	std %r9, 8(%r17)
	ld %r9, 0(%r16)
	std %r9, 0(%r19)
	ld %r9, 8(%r16)
	std %r9, 8(%r19)
	ld %r9, 0(%r16)
	ld %r10, 8(%r16)
	rldicl %r11, %r10, 1, 63
	li %r12, 0
	subf %r11, %r11, %r12
	li %r12, 135
	and %r11, %r11, %r12
	rldicl %r12, %r9, 1, 63
	rldicr %r9, %r9, 1, 62
	xor %r9, %r9, %r11
	rldicr %r10, %r10, 1, 62
	or %r10, %r10, %r12
	std %r9, 0(%r16)
	std %r10, 8(%r16)
	ld %r9, 16(%r17)
	ld %r10, 0(%r16)
	xor %r9, %r9, %r10
	std %r9, 16(%r17)
	ld %r9, 24(%r17)
	ld %r10, 8(%r16)
	xor %r9, %r9, %r10
	std %r9, 24(%r17)
	ld %r9, 0(%r16)
	std %r9, 16(%r19)
	ld %r9, 8(%r16)
	std %r9, 24(%r19)
	ld %r9, 0(%r16)
	ld %r10, 8(%r16)
	rldicl %r11, %r10, 1, 63
	li %r12, 0
	subf %r11, %r11, %r12
	li %r12, 135
	and %r11, %r11, %r12
	rldicl %r12, %r9, 1, 63
	rldicr %r9, %r9, 1, 62
	xor %r9, %r9, %r11
	rldicr %r10, %r10, 1, 62
	or %r10, %r10, %r12
	std %r9, 0(%r16)
	std %r10, 8(%r16)
	ld %r9, 32(%r17)
	ld %r10, 0(%r16)
	xor %r9, %r9, %r10
	std %r9, 32(%r17)
	ld %r9, 40(%r17)
	ld %r10, 8(%r16)
	xor %r9, %r9, %r10
	std %r9, 40(%r17)
	ld %r9, 0(%r16)
	std %r9, 32(%r19)
	ld %r9, 8(%r16)
	std %r9, 40(%r19)
	ld %r9, 0(%r16)
	ld %r10, 8(%r16)
	rldicl %r11, %r10, 1, 63
	li %r12, 0
	subf %r11, %r11, %r12
	li %r12, 135
	and %r11, %r11, %r12
	rldicl %r12, %r9, 1, 63
	rldicr %r9, %r9, 1, 62
	xor %r9, %r9, %r11
	rldicr %r10, %r10, 1, 62
	or %r10, %r10, %r12
	std %r9, 0(%r16)
	std %r10, 8(%r16)
	ld %r9, 48(%r17)
	ld %r10, 0(%r16)
	xor %r9, %r9, %r10
	std %r9, 48(%r17)
	ld %r9, 56(%r17)
	ld %r10, 8(%r16)
	xor %r9, %r9, %r10
	std %r9, 56(%r17)
	ld %r9, 0(%r16)
	std %r9, 48(%r19)
	ld %r9, 8(%r16)
	std %r9, 56(%r19)
	ld %r9, 0(%r16)
	ld %r10, 8(%r16)
	rldicl %r11, %r10, 1, 63
	li %r12, 0
	subf %r11, %r11, %r12
	li %r12, 135
	and %r11, %r11, %r12
	rldicl %r12, %r9, 1, 63
	rldicr %r9, %r9, 1, 62
	xor %r9, %r9, %r11
	rldicr %r10, %r10, 1, 62
	or %r10, %r10, %r12
	std %r9, 0(%r16)
	std %r10, 8(%r16)
	ld %r9, 64(%r17)
	ld %r10, 0(%r16)
	xor %r9, %r9, %r10
	std %r9, 64(%r17)
	ld %r9, 72(%r17)
	ld %r10, 8(%r16)
	xor %r9, %r9, %r10
	std %r9, 72(%r17)
	ld %r9, 0(%r16)
	std %r9, 64(%r19)
	ld %r9, 8(%r16)
	std %r9, 72(%r19)
	ld %r9, 0(%r16)
	ld %r10, 8(%r16)
	rldicl %r11, %r10, 1, 63
	li %r12, 0
	subf %r11, %r11, %r12
	li %r12, 135
	and %r11, %r11, %r12
	rldicl %r12, %r9, 1, 63
	rldicr %r9, %r9, 1, 62
	xor %r9, %r9, %r11
	rldicr %r10, %r10, 1, 62
	or %r10, %r10, %r12
	std %r9, 0(%r16)
	std %r10, 8(%r16)
	ld %r9, 80(%r17)
	ld %r10, 0(%r16)
	xor %r9, %r9, %r10
	std %r9, 80(%r17)
	ld %r9, 88(%r17)
	ld %r10, 8(%r16)
	xor %r9, %r9, %r10
	std %r9, 88(%r17)
	ld %r9, 0(%r16)
	std %r9, 80(%r19)
	ld %r9, 8(%r16)
	std %r9, 88(%r19)
	ld %r9, 0(%r16)
	ld %r10, 8(%r16)
	rldicl %r11, %r10, 1, 63
	li %r12, 0
	subf %r11, %r11, %r12
	li %r12, 135
	and %r11, %r11, %r12
	rldicl %r12, %r9, 1, 63
	rldicr %r9, %r9, 1, 62
	xor %r9, %r9, %r11
	rldicr %r10, %r10, 1, 62
	or %r10, %r10, %r12
	std %r9, 0(%r16)
	std %r10, 8(%r16)
	ld %r9, 96(%r17)
	ld %r10, 0(%r16)
	xor %r9, %r9, %r10
	std %r9, 96(%r17)
	ld %r9, 104(%r17)
	ld %r10, 8(%r16)
	xor %r9, %r9, %r10
	std %r9, 104(%r17)
	ld %r9, 0(%r16)
	std %r9, 96(%r19)
	ld %r9, 8(%r16)
	std %r9, 104(%r19)
	ld %r9, 0(%r16)
	ld %r10, 8(%r16)
	rldicl %r11, %r10, 1, 63
	li %r12, 0
	subf %r11, %r11, %r12
	li %r12, 135
	and %r11, %r11, %r12
	rldicl %r12, %r9, 1, 63
	rldicr %r9, %r9, 1, 62
	xor %r9, %r9, %r11
	rldicr %r10, %r10, 1, 62
	or %r10, %r10, %r12
	std %r9, 0(%r16)
	std %r10, 8(%r16)
	ld %r9, 112(%r17)
	ld %r10, 0(%r16)
	xor %r9, %r9, %r10
	std %r9, 112(%r17)
	ld %r9, 120(%r17)
	ld %r10, 8(%r16)
	xor %r9, %r9, %r10
	std %r9, 120(%r17)
	ld %r9, 0(%r16)
	std %r9, 112(%r19)
	ld %r9, 8(%r16)
	std %r9, 120(%r19)
	ld %r9, 0(%r16)
	ld %r10, 8(%r16)
	rldicl %r11, %r10, 1, 63
	li %r12, 0
	subf %r11, %r11, %r12
	li %r12, 135
	and %r11, %r11, %r12
	rldicl %r12, %r9, 1, 63
	rldicr %r9, %r9, 1, 62
	xor %r9, %r9, %r11
	rldicr %r10, %r10, 1, 62
	or %r10, %r10, %r12
	std %r9, 0(%r16)
	std %r10, 8(%r16)
	or %r3, %r14, %r14
	or %r4, %r15, %r15
	or %r5, %r17, %r17
	li %r6, 8
	or %r7, %r19, %r19
	bl {vg_aes_encrypt_blocks}
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
	ld %r9, 0(%r17)
	ld %r10, 0(%r16)
	xor %r9, %r9, %r10
	std %r9, 0(%r17)
	ld %r9, 8(%r17)
	ld %r10, 8(%r16)
	xor %r9, %r9, %r10
	std %r9, 8(%r17)
	or %r3, %r14, %r14
	or %r4, %r15, %r15
	or %r5, %r17, %r17
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
	ld %r10, 8(%r16)
	rldicl %r11, %r10, 1, 63
	li %r12, 0
	subf %r11, %r11, %r12
	li %r12, 135
	and %r11, %r11, %r12
	rldicl %r12, %r9, 1, 63
	rldicr %r9, %r9, 1, 62
	xor %r9, %r9, %r11
	rldicr %r10, %r10, 1, 62
	or %r10, %r10, %r12
	std %r9, 0(%r16)
	std %r10, 8(%r16)
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
