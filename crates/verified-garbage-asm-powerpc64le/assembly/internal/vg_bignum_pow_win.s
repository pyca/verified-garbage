// The functions of `src/internal/vg_bignum_pow_win.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_bignum_pow_win:
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
	rldicl %r11, %r29, 62, 2
	addi %r11, %r11, -4
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
20:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 20b
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
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
	li %r24, 2
22:
	mflr %r14
	addi %r3, %r12, 0
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	addi %r19, %r24, 0
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r19, 8
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
23:
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
	bne %cr0, 23b
	addi %r24, %r24, 1
	addi %r4, %r24, -16
	cmpldi %cr0, %r4, 0
	bne %cr0, 22b
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
	addi %r9, %r10, 0
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
24:
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
	bne %cr0, 24b
25:
	lbz %r24, 0(%r30)
	rldicr %r24, %r24, 56, 7
	addi %r30, %r30, 1
	mflr %r14
	addi %r3, %r12, 0
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	mflr %r14
	addi %r3, %r12, 0
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	mflr %r14
	addi %r3, %r12, 0
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	mflr %r14
	addi %r3, %r12, 0
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	rldicl %r18, %r24, 4, 60
	rldicl %r4, %r11, 61, 3
	rldicl %r0, %r11, 63, 1
	li %r9, 3
	and %r9, %r0, %r9
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	cmpldi %cr0, %r4, 0
	beq %cr0, 26f
28:
	li %r14, 0
	addi %r14, %r14, -1
	li %r15, 0
	addi %r15, %r15, -1
	li %r16, 0
	addi %r16, %r16, -1
	li %r17, 0
	addi %r17, %r17, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	std %r15, 8(%r5)
	std %r16, 16(%r5)
	std %r17, 24(%r5)
	addi %r5, %r5, 32
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 28b
	b 27f
26:
27:
	cmpldi %cr0, %r9, 0
	beq %cr0, 29f
211:
	li %r14, 0
	addi %r14, %r14, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	addi %r5, %r5, 8
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 211b
	b 210f
29:
210:
	mflr %r14
	addi %r3, %r12, 0
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	rldicr %r24, %r24, 4, 59
	mflr %r14
	addi %r3, %r12, 0
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	mflr %r14
	addi %r3, %r12, 0
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	mflr %r14
	addi %r3, %r12, 0
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	mflr %r14
	addi %r3, %r12, 0
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	rldicl %r18, %r24, 4, 60
	rldicl %r4, %r11, 61, 3
	rldicl %r0, %r11, 63, 1
	li %r9, 3
	and %r9, %r0, %r9
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	cmpldi %cr0, %r4, 0
	beq %cr0, 212f
214:
	li %r14, 0
	addi %r14, %r14, -1
	li %r15, 0
	addi %r15, %r15, -1
	li %r16, 0
	addi %r16, %r16, -1
	li %r17, 0
	addi %r17, %r17, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	std %r15, 8(%r5)
	std %r16, 16(%r5)
	std %r17, 24(%r5)
	addi %r5, %r5, 32
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 214b
	b 213f
212:
213:
	cmpldi %cr0, %r9, 0
	beq %cr0, 215f
217:
	li %r14, 0
	addi %r14, %r14, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	addi %r5, %r5, 8
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 217b
	b 216f
215:
216:
	mflr %r14
	addi %r3, %r12, 0
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	rldicr %r24, %r24, 4, 59
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 25b
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
	add %r6, %r6, %r29
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	blr
