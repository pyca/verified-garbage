// The functions of `src/internal/vg_sm4_prepare_keys.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_prepare_keys:
	or %r8, %r5, %r5
	std %r14, 3072(%r8)
	std %r15, 3080(%r8)
	std %r16, 3088(%r8)
	std %r17, 3096(%r8)
	std %r18, 3104(%r8)
	std %r19, 3112(%r8)
	std %r20, 3120(%r8)
	std %r21, 3128(%r8)
	std %r22, 3136(%r8)
	std %r23, 3144(%r8)
	std %r24, 3152(%r8)
	std %r25, 3160(%r8)
	std %r26, 3168(%r8)
	std %r27, 3176(%r8)
	std %r28, 3184(%r8)
	std %r29, 3192(%r8)
	std %r30, 3200(%r8)
	std %r31, 3208(%r8)
	lis %r22, 255
	ori %r22, %r22, 255
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 255
	ori %r22, %r22, 255
	std %r22, 384(%r8)
	lis %r22, -256
	ori %r22, %r22, 65280
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65280
	ori %r22, %r22, 65280
	std %r22, 392(%r8)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 400(%r8)
	cmpldi %cr0, %r4, 0
	bne %cr0, 20f
	b 21f
20:
	addi %r10, %r8, 3008
	ld %r23, 0(%r3)
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	ld %r23, 0(%r3)
	rldicl %r23, %r23, 32, 32
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	addi %r3, %r3, 8
	ld %r23, 0(%r3)
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	ld %r23, 0(%r3)
	rldicl %r23, %r23, 32, 32
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	addi %r3, %r3, 8
	ld %r23, 0(%r3)
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	ld %r23, 0(%r3)
	rldicl %r23, %r23, 32, 32
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	addi %r3, %r3, 8
	ld %r23, 0(%r3)
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	ld %r23, 0(%r3)
	rldicl %r23, %r23, 32, 32
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	addi %r3, %r3, 8
	ld %r23, 0(%r3)
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	ld %r23, 0(%r3)
	rldicl %r23, %r23, 32, 32
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	addi %r3, %r3, 8
	ld %r23, 0(%r3)
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	ld %r23, 0(%r3)
	rldicl %r23, %r23, 32, 32
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	addi %r3, %r3, 8
	ld %r23, 0(%r3)
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	ld %r23, 0(%r3)
	rldicl %r23, %r23, 32, 32
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	addi %r3, %r3, 8
	ld %r23, 0(%r3)
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	ld %r23, 0(%r3)
	rldicl %r23, %r23, 32, 32
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	addi %r3, %r3, 8
	ld %r23, 0(%r3)
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	ld %r23, 0(%r3)
	rldicl %r23, %r23, 32, 32
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	addi %r3, %r3, 8
	ld %r23, 0(%r3)
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	ld %r23, 0(%r3)
	rldicl %r23, %r23, 32, 32
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	addi %r3, %r3, 8
	ld %r23, 0(%r3)
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	ld %r23, 0(%r3)
	rldicl %r23, %r23, 32, 32
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	addi %r3, %r3, 8
	ld %r23, 0(%r3)
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	ld %r23, 0(%r3)
	rldicl %r23, %r23, 32, 32
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	addi %r3, %r3, 8
	ld %r23, 0(%r3)
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	ld %r23, 0(%r3)
	rldicl %r23, %r23, 32, 32
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	addi %r3, %r3, 8
	ld %r23, 0(%r3)
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	ld %r23, 0(%r3)
	rldicl %r23, %r23, 32, 32
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	addi %r3, %r3, 8
	ld %r23, 0(%r3)
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	ld %r23, 0(%r3)
	rldicl %r23, %r23, 32, 32
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	addi %r3, %r3, 8
	ld %r23, 0(%r3)
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	ld %r23, 0(%r3)
	rldicl %r23, %r23, 32, 32
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r10, %r10, -64
	addi %r3, %r3, 8
	addi %r11, %r8, 3072
21:
	cmpldi %cr0, %r4, 0
	beq %cr0, 22f
	b 23f
22:
	addi %r10, %r8, 1024
	ld %r23, 0(%r3)
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	lis %r28, -1
	ori %r28, %r28, 65535
	rldicl %r28, %r28, 32, 32
	and %r23, %r23, %r28
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	ld %r24, 400(%r8)
	rldicl %r22, %r23, 16, 0
	xor %r23, %r23, %r22
	and %r23, %r23, %r24
	ld %r25, 384(%r8)
	and %r26, %r25, %r24
	rldicl %r30, %r24, 48, 0
	and %r25, %r25, %r30
	rldicl %r22, %r23, 48, 0
	and %r22, %r22, %r25
	rldicl %r23, %r23, 24, 0
	and %r23, %r23, %r26
	xor %r23, %r23, %r22
	li %r27, 1
	rldicl %r22, %r27, 16, 0
	xor %r27, %r27, %r22
	rldicl %r22, %r27, 32, 0
	xor %r27, %r27, %r22
	and %r14, %r23, %r27
	rldicl %r22, %r14, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	xor %r14, %r14, %r22
	rldicl %r15, %r23, 63, 0
	and %r15, %r15, %r27
	rldicl %r22, %r15, 1, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	xor %r15, %r15, %r22
	rldicl %r16, %r23, 62, 0
	and %r16, %r16, %r27
	rldicl %r22, %r16, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 2, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	xor %r16, %r16, %r22
	rldicl %r17, %r23, 61, 0
	and %r17, %r17, %r27
	rldicl %r22, %r17, 1, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 2, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	xor %r17, %r17, %r22
	rldicl %r18, %r23, 60, 0
	and %r18, %r18, %r27
	rldicl %r22, %r18, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 4, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	xor %r18, %r18, %r22
	rldicl %r19, %r23, 59, 0
	and %r19, %r19, %r27
	rldicl %r22, %r19, 1, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 4, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	xor %r19, %r19, %r22
	rldicl %r20, %r23, 58, 0
	and %r20, %r20, %r27
	rldicl %r22, %r20, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 2, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 4, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	xor %r20, %r20, %r22
	rldicl %r21, %r23, 57, 0
	and %r21, %r21, %r27
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
	addi %r11, %r8, 3072
23:
	ld %r14, 3072(%r8)
	ld %r15, 3080(%r8)
	ld %r16, 3088(%r8)
	ld %r17, 3096(%r8)
	ld %r18, 3104(%r8)
	ld %r19, 3112(%r8)
	ld %r20, 3120(%r8)
	ld %r21, 3128(%r8)
	ld %r22, 3136(%r8)
	ld %r23, 3144(%r8)
	ld %r24, 3152(%r8)
	ld %r25, 3160(%r8)
	ld %r26, 3168(%r8)
	ld %r27, 3176(%r8)
	ld %r28, 3184(%r8)
	ld %r29, 3192(%r8)
	ld %r30, 3200(%r8)
	ld %r31, 3208(%r8)
	blr
