// The functions of `src/internal/vg_scrypt_blockmix.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_scrypt_blockmix:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r24, 64(%r7)
	std %r25, 72(%r7)
	std %r26, 80(%r7)
	std %r28, 88(%r7)
	std %r29, 96(%r7)
	std %r27, 104(%r7)
	addi %r28, %r4, 0
	addi %r24, %r3, 0
	addi %r25, %r5, 0
	addi %r27, %r7, 0
	rldicr %r9, %r4, 6, 57
	add %r26, %r5, %r9
	rldicr %r9, %r4, 7, 56
	add %r29, %r3, %r9
	addi %r29, %r29, -64
20:
	ld %r9, 0(%r29)
	ld %r10, 0(%r24)
	xor %r9, %r9, %r10
	std %r9, 0(%r25)
	ld %r9, 8(%r29)
	ld %r10, 8(%r24)
	xor %r9, %r9, %r10
	std %r9, 8(%r25)
	ld %r9, 16(%r29)
	ld %r10, 16(%r24)
	xor %r9, %r9, %r10
	std %r9, 16(%r25)
	ld %r9, 24(%r29)
	ld %r10, 24(%r24)
	xor %r9, %r9, %r10
	std %r9, 24(%r25)
	ld %r9, 32(%r29)
	ld %r10, 32(%r24)
	xor %r9, %r9, %r10
	std %r9, 32(%r25)
	ld %r9, 40(%r29)
	ld %r10, 40(%r24)
	xor %r9, %r9, %r10
	std %r9, 40(%r25)
	ld %r9, 48(%r29)
	ld %r10, 48(%r24)
	xor %r9, %r9, %r10
	std %r9, 48(%r25)
	ld %r9, 56(%r29)
	ld %r10, 56(%r24)
	xor %r9, %r9, %r10
	std %r9, 56(%r25)
	addi %r3, %r25, 0
	addi %r4, %r27, 0
	bl {vg_salsa20_8}
	addi %r24, %r24, 64
	ld %r9, 0(%r25)
	ld %r10, 0(%r24)
	xor %r9, %r9, %r10
	std %r9, 0(%r26)
	ld %r9, 8(%r25)
	ld %r10, 8(%r24)
	xor %r9, %r9, %r10
	std %r9, 8(%r26)
	ld %r9, 16(%r25)
	ld %r10, 16(%r24)
	xor %r9, %r9, %r10
	std %r9, 16(%r26)
	ld %r9, 24(%r25)
	ld %r10, 24(%r24)
	xor %r9, %r9, %r10
	std %r9, 24(%r26)
	ld %r9, 32(%r25)
	ld %r10, 32(%r24)
	xor %r9, %r9, %r10
	std %r9, 32(%r26)
	ld %r9, 40(%r25)
	ld %r10, 40(%r24)
	xor %r9, %r9, %r10
	std %r9, 40(%r26)
	ld %r9, 48(%r25)
	ld %r10, 48(%r24)
	xor %r9, %r9, %r10
	std %r9, 48(%r26)
	ld %r9, 56(%r25)
	ld %r10, 56(%r24)
	xor %r9, %r9, %r10
	std %r9, 56(%r26)
	addi %r3, %r26, 0
	addi %r4, %r27, 0
	bl {vg_salsa20_8}
	addi %r29, %r26, 0
	addi %r24, %r24, 64
	addi %r25, %r25, 64
	addi %r26, %r26, 64
	addi %r28, %r28, -1
	cmpldi %cr0, %r28, 0
	bne %cr0, 20b
	ld %r24, 64(%r27)
	ld %r25, 72(%r27)
	ld %r26, 80(%r27)
	ld %r28, 88(%r27)
	ld %r29, 96(%r27)
	ld %r27, 104(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr
