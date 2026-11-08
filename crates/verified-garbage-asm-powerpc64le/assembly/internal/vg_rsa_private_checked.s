// The functions of `src/internal/vg_rsa_private_checked.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_private_checked:
	stdu %r1, -3328(%r1)
	addi %r12, %r1, 0
	std %r24, 176(%r12)
	std %r25, 184(%r12)
	std %r26, 192(%r12)
	std %r27, 200(%r12)
	std %r28, 208(%r12)
	std %r29, 216(%r12)
	mflr %r0
	std %r0, 224(%r12)
	or %r24, %r3, %r3
	or %r25, %r5, %r5
	or %r26, %r6, %r6
	or %r27, %r7, %r7
	or %r28, %r8, %r8
	or %r29, %r9, %r9
	addi %r3, %r12, 248
	or %r4, %r26, %r26
	or %r7, %r29, %r29
	or %r8, %r26, %r26
	ld %r9, 3424(%r12)
	ld %r10, 3432(%r12)
	ld %r0, 3440(%r12)
	std %r0, 96(%r12)
	ld %r0, 3448(%r12)
	std %r0, 104(%r12)
	ld %r0, 3456(%r12)
	std %r0, 112(%r12)
	ld %r0, 3464(%r12)
	std %r0, 120(%r12)
	ld %r0, 3472(%r12)
	std %r0, 128(%r12)
	ld %r0, 3480(%r12)
	std %r0, 136(%r12)
	ld %r0, 3488(%r12)
	std %r0, 144(%r12)
	ld %r0, 3496(%r12)
	std %r0, 152(%r12)
	ld %r0, 3504(%r12)
	std %r0, 160(%r12)
	ld %r0, 3512(%r12)
	std %r0, 168(%r12)
	bl {vg_rsa_private_crt}
	addi %r12, %r1, 0
	std %r3, 232(%r12)
	addi %r3, %r12, 1272
	addi %r4, %r26, 7
	rldicl %r4, %r4, 61, 3
	rldicr %r4, %r4, 1, 62
	or %r5, %r25, %r25
	or %r6, %r26, %r26
	ld %r7, 3504(%r12)
	ld %r8, 3512(%r12)
	bl {vg_rsa_public_precompute}
	addi %r12, %r1, 0
	or %r3, %r24, %r24
	or %r4, %r26, %r26
	addi %r5, %r12, 1272
	addi %r4, %r26, 7
	rldicl %r4, %r4, 61, 3
	rldicr %r4, %r4, 1, 62
	addi %r6, %r4, 0
	or %r4, %r26, %r26
	or %r7, %r27, %r27
	or %r8, %r28, %r28
	addi %r9, %r12, 248
	or %r10, %r26, %r26
	ld %r0, 3504(%r12)
	std %r0, 96(%r12)
	ld %r0, 3512(%r12)
	std %r0, 104(%r12)
	bl {vg_rsa_public_precomputed_checked}
	addi %r12, %r1, 0
	std %r3, 240(%r12)
	or %r3, %r24, %r24
	or %r4, %r29, %r29
	li %r5, 0
	or %r6, %r26, %r26
20:
	lbz %r7, 0(%r3)
	lbz %r8, 0(%r4)
	xor %r7, %r7, %r8
	or %r5, %r5, %r7
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 20b
	addi %r12, %r1, 0
	ld %r3, 232(%r12)
	ld %r4, 240(%r12)
	and %r3, %r3, %r4
	li %r4, 1
	and %r3, %r3, %r4
	addi %r5, %r5, -1
	rldicl %r5, %r5, 1, 63
	li %r4, 2
	subf %r4, %r5, %r4
	and %r5, %r5, %r3
	li %r9, 0
	subf %r9, %r5, %r9
	li %r7, 0
	subf %r3, %r3, %r7
	and %r3, %r3, %r4
	or %r6, %r26, %r26
	or %r7, %r24, %r24
	addi %r8, %r12, 248
21:
	lbz %r0, 0(%r8)
	and %r0, %r0, %r9
	stb %r0, 0(%r7)
	li %r0, 0
	stb %r0, 0(%r8)
	addi %r7, %r7, 1
	addi %r8, %r8, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 21b
	addi %r12, %r1, 0
	ld %r0, 224(%r12)
	mtlr %r0
	ld %r24, 176(%r12)
	ld %r25, 184(%r12)
	ld %r26, 192(%r12)
	ld %r27, 200(%r12)
	ld %r28, 208(%r12)
	ld %r29, 216(%r12)
	addi %r1, %r1, 3328
	blr
	.p2align 6
