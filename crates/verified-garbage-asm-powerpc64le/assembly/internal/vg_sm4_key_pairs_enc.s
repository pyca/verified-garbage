// The functions of `src/internal/vg_sm4_key_pairs_enc.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_key_pairs_enc:
	ld %r23, 0(%r3)
	lis %r30, -1
	ori %r30, %r30, 65535
	rldicl %r30, %r30, 32, 32
	and %r23, %r23, %r30
	ld %r26, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r26
	ld %r27, 384(%r8)
	and %r28, %r27, %r26
	rldicl %r24, %r26, 48, 0
	and %r27, %r27, %r24
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r27
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r28
	xor %r23, %r23, %r22
	li %r29, 1
	rldicl %r22, %r29, 16, 0
	xor %r29, %r29, %r22
	rldicl %r22, %r29, 32, 0
	xor %r29, %r29, %r22
	and %r14, %r23, %r29
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r29
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r29
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r29
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r29
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r29
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r29
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r29
	rldicl %r22, %r21, 1, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 2, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 4, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 8, 0
	xor %r21, %r21, %r22
	std %r14, 0(%r10)
	std %r15, 8(%r10)
	std %r16, 16(%r10)
	std %r17, 24(%r10)
	std %r18, 32(%r10)
	std %r19, 40(%r10)
	std %r20, 48(%r10)
	std %r21, 56(%r10)
	addi %r10, %r10, 64
	ld %r23, 0(%r3)
	rldicl %r23, %r23, 32, 32
	ld %r26, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r26
	ld %r27, 384(%r8)
	and %r28, %r27, %r26
	rldicl %r24, %r26, 48, 0
	and %r27, %r27, %r24
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r27
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r28
	xor %r23, %r23, %r22
	li %r29, 1
	rldicl %r22, %r29, 16, 0
	xor %r29, %r29, %r22
	rldicl %r22, %r29, 32, 0
	xor %r29, %r29, %r22
	and %r14, %r23, %r29
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r29
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r29
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r29
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r29
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r29
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r29
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r29
	rldicl %r22, %r21, 1, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 2, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 4, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 8, 0
	xor %r21, %r21, %r22
	std %r14, 0(%r10)
	std %r15, 8(%r10)
	std %r16, 16(%r10)
	std %r17, 24(%r10)
	std %r18, 32(%r10)
	std %r19, 40(%r10)
	std %r20, 48(%r10)
	std %r21, 56(%r10)
	addi %r10, %r10, 64
	addi %r3, %r3, 8
	ld %r23, 0(%r3)
	lis %r30, -1
	ori %r30, %r30, 65535
	rldicl %r30, %r30, 32, 32
	and %r23, %r23, %r30
	ld %r26, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r26
	ld %r27, 384(%r8)
	and %r28, %r27, %r26
	rldicl %r24, %r26, 48, 0
	and %r27, %r27, %r24
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r27
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r28
	xor %r23, %r23, %r22
	li %r29, 1
	rldicl %r22, %r29, 16, 0
	xor %r29, %r29, %r22
	rldicl %r22, %r29, 32, 0
	xor %r29, %r29, %r22
	and %r14, %r23, %r29
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r29
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r29
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r29
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r29
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r29
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r29
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r29
	rldicl %r22, %r21, 1, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 2, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 4, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 8, 0
	xor %r21, %r21, %r22
	std %r14, 0(%r10)
	std %r15, 8(%r10)
	std %r16, 16(%r10)
	std %r17, 24(%r10)
	std %r18, 32(%r10)
	std %r19, 40(%r10)
	std %r20, 48(%r10)
	std %r21, 56(%r10)
	addi %r10, %r10, 64
	ld %r23, 0(%r3)
	rldicl %r23, %r23, 32, 32
	ld %r26, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r26
	ld %r27, 384(%r8)
	and %r28, %r27, %r26
	rldicl %r24, %r26, 48, 0
	and %r27, %r27, %r24
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r27
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r28
	xor %r23, %r23, %r22
	li %r29, 1
	rldicl %r22, %r29, 16, 0
	xor %r29, %r29, %r22
	rldicl %r22, %r29, 32, 0
	xor %r29, %r29, %r22
	and %r14, %r23, %r29
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r29
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r29
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r29
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r29
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r29
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r29
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r29
	rldicl %r22, %r21, 1, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 2, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 4, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 8, 0
	xor %r21, %r21, %r22
	std %r14, 0(%r10)
	std %r15, 8(%r10)
	std %r16, 16(%r10)
	std %r17, 24(%r10)
	std %r18, 32(%r10)
	std %r19, 40(%r10)
	std %r20, 48(%r10)
	std %r21, 56(%r10)
	addi %r10, %r10, 64
	addi %r3, %r3, 8
	blr
