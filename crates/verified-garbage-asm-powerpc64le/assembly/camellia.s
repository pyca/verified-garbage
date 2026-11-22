// The functions of `src/camellia.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_expand_key:
	stdu %r1, -3344(%r1)
	addi %r6, %r1, 32
	or %r8, %r6, %r6
	or %r6, %r4, %r4
	std %r14, 2944(%r8)
	std %r15, 2952(%r8)
	std %r16, 2960(%r8)
	std %r17, 2968(%r8)
	std %r18, 2976(%r8)
	std %r19, 2984(%r8)
	std %r20, 2992(%r8)
	std %r21, 3000(%r8)
	std %r22, 3008(%r8)
	std %r23, 3016(%r8)
	std %r24, 3024(%r8)
	std %r25, 3032(%r8)
	std %r26, 3040(%r8)
	std %r27, 3048(%r8)
	std %r28, 3056(%r8)
	std %r29, 3064(%r8)
	std %r30, 3072(%r8)
	std %r31, 3080(%r8)
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
	lis %r22, 255
	ori %r22, %r22, 65280
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 400(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 255
	ori %r22, %r22, 65280
	std %r22, 408(%r8)
	lis %r22, 0
	ori %r22, %r22, 255
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65280
	ori %r22, %r22, 0
	std %r22, 416(%r8)
	addi %r4, %r8, 768
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65280
	std %r22, 0(%r4)
	lis %r22, -1
	ori %r22, %r22, 255
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 255
	ori %r22, %r22, 65280
	std %r22, 8(%r4)
	lis %r22, 255
	ori %r22, %r22, 255
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 16(%r4)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65280
	std %r22, 24(%r4)
	lis %r22, 255
	ori %r22, %r22, 65280
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 255
	ori %r22, %r22, 65280
	std %r22, 32(%r4)
	lis %r22, 255
	ori %r22, %r22, 255
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 40(%r4)
	lis %r22, 255
	ori %r22, %r22, 255
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65280
	ori %r22, %r22, 0
	std %r22, 48(%r4)
	lis %r22, -256
	ori %r22, %r22, 65280
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 255
	std %r22, 56(%r4)
	addi %r4, %r4, 64
	lis %r22, 0
	ori %r22, %r22, 65280
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 0(%r4)
	lis %r22, -256
	ori %r22, %r22, 65280
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 255
	std %r22, 8(%r4)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 16(%r4)
	lis %r22, 255
	ori %r22, %r22, 255
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65280
	std %r22, 24(%r4)
	lis %r22, -1
	ori %r22, %r22, 65280
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 255
	ori %r22, %r22, 255
	std %r22, 32(%r4)
	lis %r22, -256
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 255
	std %r22, 40(%r4)
	lis %r22, 255
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 255
	ori %r22, %r22, 65280
	std %r22, 48(%r4)
	lis %r22, -256
	ori %r22, %r22, 255
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65280
	ori %r22, %r22, 255
	std %r22, 56(%r4)
	addi %r4, %r4, 64
	lis %r22, 255
	ori %r22, %r22, 255
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65280
	std %r22, 0(%r4)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 255
	std %r22, 8(%r4)
	lis %r22, -1
	ori %r22, %r22, 255
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 255
	std %r22, 16(%r4)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65280
	std %r22, 24(%r4)
	lis %r22, -256
	ori %r22, %r22, 255
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 32(%r4)
	lis %r22, -1
	ori %r22, %r22, 255
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 255
	ori %r22, %r22, 65280
	std %r22, 40(%r4)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 48(%r4)
	lis %r22, -256
	ori %r22, %r22, 65280
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 255
	ori %r22, %r22, 65535
	std %r22, 56(%r4)
	addi %r4, %r4, 64
	lis %r22, 255
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65280
	std %r22, 0(%r4)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 8(%r4)
	lis %r22, -1
	ori %r22, %r22, 65280
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 255
	ori %r22, %r22, 255
	std %r22, 16(%r4)
	lis %r22, -256
	ori %r22, %r22, 65280
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 255
	ori %r22, %r22, 0
	std %r22, 24(%r4)
	lis %r22, -256
	ori %r22, %r22, 255
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 32(%r4)
	lis %r22, 255
	ori %r22, %r22, 65280
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 255
	ori %r22, %r22, 65280
	std %r22, 40(%r4)
	lis %r22, 0
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65535
	std %r22, 48(%r4)
	lis %r22, 255
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65280
	std %r22, 56(%r4)
	addi %r4, %r4, 64
	lis %r22, -256
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 255
	ori %r22, %r22, 0
	std %r22, 0(%r4)
	lis %r22, 255
	ori %r22, %r22, 255
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65280
	std %r22, 8(%r4)
	lis %r22, -256
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 255
	ori %r22, %r22, 65280
	std %r22, 16(%r4)
	lis %r22, -1
	ori %r22, %r22, 65280
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65280
	ori %r22, %r22, 65280
	std %r22, 24(%r4)
	lis %r22, -1
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65535
	std %r22, 32(%r4)
	lis %r22, 255
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 40(%r4)
	lis %r22, 255
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65280
	std %r22, 48(%r4)
	lis %r22, 255
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 255
	ori %r22, %r22, 65280
	std %r22, 56(%r4)
	addi %r4, %r4, 64
	lis %r22, -256
	ori %r22, %r22, 65280
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 65280
	std %r22, 0(%r4)
	lis %r22, 255
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 65280
	std %r22, 8(%r4)
	lis %r22, -256
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 16(%r4)
	lis %r22, -256
	ori %r22, %r22, 255
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 24(%r4)
	lis %r22, -256
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 255
	ori %r22, %r22, 65535
	std %r22, 32(%r4)
	lis %r22, -256
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65280
	ori %r22, %r22, 65535
	std %r22, 40(%r4)
	lis %r22, -1
	ori %r22, %r22, 65280
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65535
	ori %r22, %r22, 0
	std %r22, 48(%r4)
	lis %r22, -1
	ori %r22, %r22, 65535
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65280
	ori %r22, %r22, 65535
	std %r22, 56(%r4)
	addi %r4, %r4, 64
	ld %r22, 0(%r3)
	std %r22, 3088(%r8)
	ld %r22, 8(%r3)
	std %r22, 3096(%r8)
	addi %r23, %r6, -16
	cmpldi %cr0, %r23, 0
	beq %cr0, 20f
	ld %r22, 16(%r3)
	std %r22, 3104(%r8)
	addi %r23, %r6, -24
	cmpldi %cr0, %r23, 0
	beq %cr0, 22f
	ld %r22, 24(%r3)
	std %r22, 3112(%r8)
	b 23f
22:
	li %r24, 0
	addi %r24, %r24, -1
	xor %r22, %r22, %r24
	std %r22, 3112(%r8)
23:
	b 21f
20:
	li %r22, 0
	std %r22, 3104(%r8)
	std %r22, 3112(%r8)
21:
	addi %r4, %r8, 768
	ld %r22, 3088(%r8)
	std %r22, 3120(%r8)
	ld %r22, 3096(%r8)
	std %r22, 3128(%r8)
	ld %r22, 3104(%r8)
	ld %r23, 3120(%r8)
	xor %r22, %r22, %r23
	std %r22, 3120(%r8)
	ld %r22, 3112(%r8)
	ld %r23, 3128(%r8)
	xor %r22, %r22, %r23
	std %r22, 3128(%r8)
	li %r7, 3
	addi %r3, %r8, 3120
24:
	ld %r14, 8(%r3)
	or %r15, %r14, %r14
	or %r16, %r14, %r14
	or %r17, %r14, %r14
	or %r18, %r14, %r14
	or %r19, %r14, %r14
	or %r20, %r14, %r14
	or %r21, %r14, %r14
	lis %r24, 0
	ori %r24, %r24, 0
	rldicr %r24, %r24, 32, 31
	oris %r24, %r24, 65535
	ori %r24, %r24, 0
	lis %r25, 0
	ori %r25, %r25, 65280
	rldicr %r25, %r25, 32, 31
	oris %r25, %r25, 0
	ori %r25, %r25, 65280
	lis %r27, 21845
	ori %r27, %r27, 21845
	rldicr %r27, %r27, 32, 31
	oris %r27, %r27, 21845
	ori %r27, %r27, 21845
	lis %r28, 13107
	ori %r28, %r28, 13107
	rldicr %r28, %r28, 32, 31
	oris %r28, %r28, 13107
	ori %r28, %r28, 13107
	lis %r29, 3855
	ori %r29, %r29, 3855
	rldicr %r29, %r29, 32, 31
	oris %r29, %r29, 3855
	ori %r29, %r29, 3855
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 576(%r8)
	std %r15, 584(%r8)
	std %r16, 592(%r8)
	std %r17, 600(%r8)
	std %r18, 608(%r8)
	std %r19, 616(%r8)
	std %r20, 624(%r8)
	std %r21, 632(%r8)
	ld %r14, 0(%r3)
	or %r15, %r14, %r14
	or %r16, %r14, %r14
	or %r17, %r14, %r14
	or %r18, %r14, %r14
	or %r19, %r14, %r14
	or %r20, %r14, %r14
	or %r21, %r14, %r14
	lis %r24, 0
	ori %r24, %r24, 0
	rldicr %r24, %r24, 32, 31
	oris %r24, %r24, 65535
	ori %r24, %r24, 0
	lis %r25, 0
	ori %r25, %r25, 65280
	rldicr %r25, %r25, 32, 31
	oris %r25, %r25, 0
	ori %r25, %r25, 65280
	lis %r27, 21845
	ori %r27, %r27, 21845
	rldicr %r27, %r27, 32, 31
	oris %r27, %r27, 21845
	ori %r27, %r27, 21845
	lis %r28, 13107
	ori %r28, %r28, 13107
	rldicr %r28, %r28, 32, 31
	oris %r28, %r28, 13107
	ori %r28, %r28, 13107
	lis %r29, 3855
	ori %r29, %r29, 3855
	rldicr %r29, %r29, 32, 31
	oris %r29, %r29, 3855
	ori %r29, %r29, 3855
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 512(%r8)
	std %r15, 520(%r8)
	std %r16, 528(%r8)
	std %r17, 536(%r8)
	std %r18, 544(%r8)
	std %r19, 552(%r8)
	std %r20, 560(%r8)
	std %r21, 568(%r8)
	ld %r22, 0(%r4)
	xor %r14, %r14, %r22
	ld %r22, 8(%r4)
	xor %r15, %r15, %r22
	ld %r22, 16(%r4)
	xor %r16, %r16, %r22
	ld %r22, 24(%r4)
	xor %r17, %r17, %r22
	ld %r22, 32(%r4)
	xor %r18, %r18, %r22
	ld %r22, 40(%r4)
	xor %r19, %r19, %r22
	ld %r22, 48(%r4)
	xor %r20, %r20, %r22
	ld %r22, 56(%r4)
	xor %r21, %r21, %r22
	ld %r30, 400(%r8)
	or %r23, %r21, %r21
	xor %r22, %r21, %r20
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	xor %r22, %r20, %r19
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	xor %r22, %r19, %r18
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	xor %r22, %r18, %r17
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	xor %r22, %r17, %r16
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	xor %r22, %r16, %r15
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	xor %r22, %r15, %r14
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	xor %r22, %r14, %r23
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	li %r31, 0
	addi %r31, %r31, -1
	xor %r22, %r21, %r15
	xor %r23, %r19, %r17
	xor %r24, %r16, %r22
	xor %r25, %r20, %r14
	xor %r26, %r14, %r23
	xor %r27, %r18, %r15
	xor %r28, %r18, %r24
	xor %r29, %r20, %r23
	xor %r30, %r16, %r25
	xor %r0, %r24, %r25
	xor %r9, %r21, %r20
	std %r30, 0(%r8)
	xor %r30, %r21, %r25
	std %r21, 8(%r8)
	xor %r21, %r30, %r31
	std %r30, 16(%r8)
	xor %r30, %r20, %r17
	std %r21, 24(%r8)
	xor %r21, %r19, %r15
	std %r20, 32(%r8)
	xor %r20, %r19, %r14
	xor %r19, %r19, %r24
	xor %r25, %r18, %r25
	xor %r18, %r18, %r9
	xor %r17, %r17, %r14
	xor %r17, %r17, %r31
	xor %r14, %r16, %r26
	xor %r16, %r16, %r27
	xor %r16, %r16, %r31
	xor %r9, %r15, %r29
	xor %r9, %r9, %r31
	std %r9, 40(%r8)
	xor %r9, %r22, %r26
	xor %r22, %r22, %r29
	xor %r29, %r23, %r27
	std %r9, 48(%r8)
	xor %r9, %r23, %r28
	xor %r23, %r23, %r0
	std %r23, 56(%r8)
	xor %r23, %r24, %r26
	xor %r23, %r23, %r31
	xor %r24, %r24, %r30
	xor %r24, %r24, %r31
	xor %r26, %r26, %r27
	xor %r26, %r26, %r31
	xor %r20, %r28, %r20
	xor %r20, %r20, %r31
	ld %r27, 0(%r8)
	xor %r21, %r27, %r21
	xor %r21, %r21, %r31
	xor %r27, %r27, %r29
	xor %r27, %r27, %r31
	ld %r29, 8(%r8)
	ld %r30, 32(%r8)
	std %r24, 0(%r8)
	xor %r24, %r29, %r30
	xor %r24, %r24, %r31
	xor %r24, %r24, %r30
	xor %r29, %r29, %r15
	xor %r29, %r29, %r31
	and %r15, %r16, %r18
	and %r30, %r24, %r21
	xor %r30, %r30, %r15
	std %r31, 8(%r8)
	and %r31, %r28, %r20
	xor %r31, %r31, %r15
	and %r15, %r14, %r23
	std %r14, 32(%r8)
	and %r14, %r22, %r19
	xor %r14, %r14, %r15
	std %r22, 64(%r8)
	and %r22, %r0, %r17
	xor %r22, %r22, %r15
	and %r15, %r25, %r9
	std %r25, 72(%r8)
	and %r25, %r26, %r27
	xor %r25, %r25, %r15
	std %r26, 80(%r8)
	ld %r26, 40(%r8)
	std %r0, 88(%r8)
	ld %r0, 24(%r8)
	std %r28, 96(%r8)
	and %r28, %r26, %r0
	xor %r28, %r28, %r15
	xor %r30, %r30, %r25
	xor %r31, %r31, %r28
	xor %r14, %r14, %r25
	xor %r22, %r22, %r28
	ld %r28, 56(%r8)
	xor %r30, %r30, %r28
	ld %r28, 48(%r8)
	xor %r31, %r31, %r28
	xor %r14, %r14, %r29
	ld %r29, 0(%r8)
	xor %r22, %r22, %r29
	xor %r29, %r30, %r31
	and %r30, %r30, %r14
	xor %r28, %r22, %r30
	and %r25, %r29, %r28
	xor %r25, %r25, %r31
	xor %r15, %r14, %r22
	xor %r31, %r31, %r30
	and %r31, %r31, %r15
	xor %r31, %r31, %r22
	xor %r14, %r14, %r31
	xor %r15, %r28, %r31
	and %r22, %r22, %r15
	xor %r14, %r22, %r14
	xor %r28, %r28, %r22
	and %r28, %r25, %r28
	xor %r29, %r29, %r28
	xor %r28, %r29, %r14
	xor %r22, %r25, %r31
	xor %r15, %r25, %r29
	xor %r30, %r31, %r14
	xor %r26, %r22, %r28
	and %r18, %r30, %r18
	and %r21, %r14, %r21
	and %r20, %r31, %r20
	and %r23, %r15, %r23
	and %r19, %r29, %r19
	and %r17, %r25, %r17
	and %r9, %r22, %r9
	and %r27, %r26, %r27
	and %r0, %r28, %r0
	and %r30, %r30, %r16
	and %r14, %r14, %r24
	ld %r24, 96(%r8)
	and %r31, %r31, %r24
	ld %r24, 32(%r8)
	and %r15, %r15, %r24
	ld %r24, 64(%r8)
	and %r29, %r29, %r24
	ld %r24, 88(%r8)
	and %r25, %r25, %r24
	ld %r24, 72(%r8)
	and %r22, %r22, %r24
	ld %r24, 80(%r8)
	and %r26, %r26, %r24
	ld %r24, 40(%r8)
	and %r28, %r28, %r24
	xor %r27, %r21, %r27
	xor %r23, %r23, %r17
	xor %r24, %r9, %r0
	xor %r16, %r18, %r26
	xor %r31, %r31, %r27
	std %r27, 40(%r8)
	xor %r27, %r15, %r23
	std %r23, 80(%r8)
	xor %r23, %r22, %r24
	xor %r25, %r20, %r25
	xor %r9, %r9, %r28
	xor %r0, %r0, %r30
	xor %r30, %r30, %r14
	xor %r29, %r29, %r27
	xor %r26, %r26, %r23
	std %r26, 72(%r8)
	xor %r26, %r16, %r31
	xor %r18, %r18, %r20
	xor %r21, %r21, %r19
	xor %r17, %r17, %r16
	xor %r14, %r14, %r9
	xor %r15, %r15, %r31
	ld %r31, 40(%r8)
	xor %r22, %r22, %r31
	xor %r28, %r28, %r0
	ld %r31, 80(%r8)
	xor %r31, %r31, %r30
	xor %r18, %r24, %r18
	xor %r27, %r27, %r25
	xor %r23, %r23, %r30
	xor %r25, %r25, %r0
	xor %r9, %r9, %r22
	ld %r22, 72(%r8)
	xor %r0, %r29, %r22
	xor %r29, %r29, %r26
	xor %r22, %r22, %r31
	ld %r31, 8(%r8)
	xor %r19, %r22, %r31
	xor %r26, %r26, %r14
	xor %r16, %r26, %r31
	xor %r21, %r21, %r17
	xor %r15, %r15, %r25
	xor %r17, %r15, %r31
	xor %r28, %r28, %r29
	xor %r15, %r28, %r31
	xor %r27, %r27, %r9
	xor %r23, %r23, %r21
	xor %r20, %r23, %r31
	or %r21, %r27, %r27
	or %r14, %r0, %r0
	ld %r30, 408(%r8)
	or %r23, %r21, %r21
	xor %r22, %r21, %r20
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	xor %r22, %r20, %r19
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	xor %r22, %r19, %r18
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	xor %r22, %r18, %r17
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	xor %r22, %r17, %r16
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	xor %r22, %r16, %r15
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	xor %r22, %r15, %r14
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	xor %r22, %r14, %r23
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	ld %r30, 416(%r8)
	or %r23, %r14, %r14
	xor %r22, %r14, %r15
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	xor %r22, %r15, %r16
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	xor %r22, %r16, %r17
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	xor %r22, %r17, %r18
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	xor %r22, %r18, %r19
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	xor %r22, %r19, %r20
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	xor %r22, %r20, %r21
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	xor %r22, %r21, %r23
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	ld %r30, 384(%r8)
	ld %r24, 392(%r8)
	rldicl %r22, %r14, 56, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 24, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 56, 0
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 24, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 24, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 56, 0
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 24, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 24, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 56, 0
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 24, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 24, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 56, 0
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 24, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 24, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 56, 0
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 24, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 24, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 56, 0
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 24, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 24, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 56, 0
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 24, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 24, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 8, 0
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 56, 0
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 24, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	ld %r22, 576(%r8)
	xor %r14, %r14, %r22
	std %r14, 576(%r8)
	ld %r22, 584(%r8)
	xor %r15, %r15, %r22
	std %r15, 584(%r8)
	ld %r22, 592(%r8)
	xor %r16, %r16, %r22
	std %r16, 592(%r8)
	ld %r22, 600(%r8)
	xor %r17, %r17, %r22
	std %r17, 600(%r8)
	ld %r22, 608(%r8)
	xor %r18, %r18, %r22
	std %r18, 608(%r8)
	ld %r22, 616(%r8)
	xor %r19, %r19, %r22
	std %r19, 616(%r8)
	ld %r22, 624(%r8)
	xor %r20, %r20, %r22
	std %r20, 624(%r8)
	ld %r22, 632(%r8)
	xor %r21, %r21, %r22
	std %r21, 632(%r8)
	ld %r22, 64(%r4)
	xor %r14, %r14, %r22
	ld %r22, 72(%r4)
	xor %r15, %r15, %r22
	ld %r22, 80(%r4)
	xor %r16, %r16, %r22
	ld %r22, 88(%r4)
	xor %r17, %r17, %r22
	ld %r22, 96(%r4)
	xor %r18, %r18, %r22
	ld %r22, 104(%r4)
	xor %r19, %r19, %r22
	ld %r22, 112(%r4)
	xor %r20, %r20, %r22
	ld %r22, 120(%r4)
	xor %r21, %r21, %r22
	ld %r30, 400(%r8)
	or %r23, %r21, %r21
	xor %r22, %r21, %r20
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	xor %r22, %r20, %r19
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	xor %r22, %r19, %r18
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	xor %r22, %r18, %r17
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	xor %r22, %r17, %r16
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	xor %r22, %r16, %r15
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	xor %r22, %r15, %r14
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	xor %r22, %r14, %r23
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	li %r31, 0
	addi %r31, %r31, -1
	xor %r22, %r21, %r15
	xor %r23, %r19, %r17
	xor %r24, %r16, %r22
	xor %r25, %r20, %r14
	xor %r26, %r14, %r23
	xor %r27, %r18, %r15
	xor %r28, %r18, %r24
	xor %r29, %r20, %r23
	xor %r30, %r16, %r25
	xor %r0, %r24, %r25
	xor %r9, %r21, %r20
	std %r30, 0(%r8)
	xor %r30, %r21, %r25
	std %r21, 8(%r8)
	xor %r21, %r30, %r31
	std %r30, 16(%r8)
	xor %r30, %r20, %r17
	std %r21, 24(%r8)
	xor %r21, %r19, %r15
	std %r20, 32(%r8)
	xor %r20, %r19, %r14
	xor %r19, %r19, %r24
	xor %r25, %r18, %r25
	xor %r18, %r18, %r9
	xor %r17, %r17, %r14
	xor %r17, %r17, %r31
	xor %r14, %r16, %r26
	xor %r16, %r16, %r27
	xor %r16, %r16, %r31
	xor %r9, %r15, %r29
	xor %r9, %r9, %r31
	std %r9, 40(%r8)
	xor %r9, %r22, %r26
	xor %r22, %r22, %r29
	xor %r29, %r23, %r27
	std %r9, 48(%r8)
	xor %r9, %r23, %r28
	xor %r23, %r23, %r0
	std %r23, 56(%r8)
	xor %r23, %r24, %r26
	xor %r23, %r23, %r31
	xor %r24, %r24, %r30
	xor %r24, %r24, %r31
	xor %r26, %r26, %r27
	xor %r26, %r26, %r31
	xor %r20, %r28, %r20
	xor %r20, %r20, %r31
	ld %r27, 0(%r8)
	xor %r21, %r27, %r21
	xor %r21, %r21, %r31
	xor %r27, %r27, %r29
	xor %r27, %r27, %r31
	ld %r29, 8(%r8)
	ld %r30, 32(%r8)
	std %r24, 0(%r8)
	xor %r24, %r29, %r30
	xor %r24, %r24, %r31
	xor %r24, %r24, %r30
	xor %r29, %r29, %r15
	xor %r29, %r29, %r31
	and %r15, %r16, %r18
	and %r30, %r24, %r21
	xor %r30, %r30, %r15
	std %r31, 8(%r8)
	and %r31, %r28, %r20
	xor %r31, %r31, %r15
	and %r15, %r14, %r23
	std %r14, 32(%r8)
	and %r14, %r22, %r19
	xor %r14, %r14, %r15
	std %r22, 64(%r8)
	and %r22, %r0, %r17
	xor %r22, %r22, %r15
	and %r15, %r25, %r9
	std %r25, 72(%r8)
	and %r25, %r26, %r27
	xor %r25, %r25, %r15
	std %r26, 80(%r8)
	ld %r26, 40(%r8)
	std %r0, 88(%r8)
	ld %r0, 24(%r8)
	std %r28, 96(%r8)
	and %r28, %r26, %r0
	xor %r28, %r28, %r15
	xor %r30, %r30, %r25
	xor %r31, %r31, %r28
	xor %r14, %r14, %r25
	xor %r22, %r22, %r28
	ld %r28, 56(%r8)
	xor %r30, %r30, %r28
	ld %r28, 48(%r8)
	xor %r31, %r31, %r28
	xor %r14, %r14, %r29
	ld %r29, 0(%r8)
	xor %r22, %r22, %r29
	xor %r29, %r30, %r31
	and %r30, %r30, %r14
	xor %r28, %r22, %r30
	and %r25, %r29, %r28
	xor %r25, %r25, %r31
	xor %r15, %r14, %r22
	xor %r31, %r31, %r30
	and %r31, %r31, %r15
	xor %r31, %r31, %r22
	xor %r14, %r14, %r31
	xor %r15, %r28, %r31
	and %r22, %r22, %r15
	xor %r14, %r22, %r14
	xor %r28, %r28, %r22
	and %r28, %r25, %r28
	xor %r29, %r29, %r28
	xor %r28, %r29, %r14
	xor %r22, %r25, %r31
	xor %r15, %r25, %r29
	xor %r30, %r31, %r14
	xor %r26, %r22, %r28
	and %r18, %r30, %r18
	and %r21, %r14, %r21
	and %r20, %r31, %r20
	and %r23, %r15, %r23
	and %r19, %r29, %r19
	and %r17, %r25, %r17
	and %r9, %r22, %r9
	and %r27, %r26, %r27
	and %r0, %r28, %r0
	and %r30, %r30, %r16
	and %r14, %r14, %r24
	ld %r24, 96(%r8)
	and %r31, %r31, %r24
	ld %r24, 32(%r8)
	and %r15, %r15, %r24
	ld %r24, 64(%r8)
	and %r29, %r29, %r24
	ld %r24, 88(%r8)
	and %r25, %r25, %r24
	ld %r24, 72(%r8)
	and %r22, %r22, %r24
	ld %r24, 80(%r8)
	and %r26, %r26, %r24
	ld %r24, 40(%r8)
	and %r28, %r28, %r24
	xor %r27, %r21, %r27
	xor %r23, %r23, %r17
	xor %r24, %r9, %r0
	xor %r16, %r18, %r26
	xor %r31, %r31, %r27
	std %r27, 40(%r8)
	xor %r27, %r15, %r23
	std %r23, 80(%r8)
	xor %r23, %r22, %r24
	xor %r25, %r20, %r25
	xor %r9, %r9, %r28
	xor %r0, %r0, %r30
	xor %r30, %r30, %r14
	xor %r29, %r29, %r27
	xor %r26, %r26, %r23
	std %r26, 72(%r8)
	xor %r26, %r16, %r31
	xor %r18, %r18, %r20
	xor %r21, %r21, %r19
	xor %r17, %r17, %r16
	xor %r14, %r14, %r9
	xor %r15, %r15, %r31
	ld %r31, 40(%r8)
	xor %r22, %r22, %r31
	xor %r28, %r28, %r0
	ld %r31, 80(%r8)
	xor %r31, %r31, %r30
	xor %r18, %r24, %r18
	xor %r27, %r27, %r25
	xor %r23, %r23, %r30
	xor %r25, %r25, %r0
	xor %r9, %r9, %r22
	ld %r22, 72(%r8)
	xor %r0, %r29, %r22
	xor %r29, %r29, %r26
	xor %r22, %r22, %r31
	ld %r31, 8(%r8)
	xor %r19, %r22, %r31
	xor %r26, %r26, %r14
	xor %r16, %r26, %r31
	xor %r21, %r21, %r17
	xor %r15, %r15, %r25
	xor %r17, %r15, %r31
	xor %r28, %r28, %r29
	xor %r15, %r28, %r31
	xor %r27, %r27, %r9
	xor %r23, %r23, %r21
	xor %r20, %r23, %r31
	or %r21, %r27, %r27
	or %r14, %r0, %r0
	ld %r30, 408(%r8)
	or %r23, %r21, %r21
	xor %r22, %r21, %r20
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	xor %r22, %r20, %r19
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	xor %r22, %r19, %r18
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	xor %r22, %r18, %r17
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	xor %r22, %r17, %r16
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	xor %r22, %r16, %r15
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	xor %r22, %r15, %r14
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	xor %r22, %r14, %r23
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	ld %r30, 416(%r8)
	or %r23, %r14, %r14
	xor %r22, %r14, %r15
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	xor %r22, %r15, %r16
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	xor %r22, %r16, %r17
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	xor %r22, %r17, %r18
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	xor %r22, %r18, %r19
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	xor %r22, %r19, %r20
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	xor %r22, %r20, %r21
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	xor %r22, %r21, %r23
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	ld %r30, 384(%r8)
	ld %r24, 392(%r8)
	rldicl %r22, %r14, 56, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 24, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 56, 0
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 24, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 24, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 56, 0
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 24, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 24, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 56, 0
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 24, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 24, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 56, 0
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 24, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 24, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 56, 0
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 24, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 24, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 56, 0
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 24, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 24, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 56, 0
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 24, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 24, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 8, 0
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 56, 0
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 24, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	ld %r22, 512(%r8)
	xor %r14, %r14, %r22
	std %r14, 512(%r8)
	ld %r22, 520(%r8)
	xor %r15, %r15, %r22
	std %r15, 520(%r8)
	ld %r22, 528(%r8)
	xor %r16, %r16, %r22
	std %r16, 528(%r8)
	ld %r22, 536(%r8)
	xor %r17, %r17, %r22
	std %r17, 536(%r8)
	ld %r22, 544(%r8)
	xor %r18, %r18, %r22
	std %r18, 544(%r8)
	ld %r22, 552(%r8)
	xor %r19, %r19, %r22
	std %r19, 552(%r8)
	ld %r22, 560(%r8)
	xor %r20, %r20, %r22
	std %r20, 560(%r8)
	ld %r22, 568(%r8)
	xor %r21, %r21, %r22
	std %r21, 568(%r8)
	lis %r24, 0
	ori %r24, %r24, 0
	rldicr %r24, %r24, 32, 31
	oris %r24, %r24, 65535
	ori %r24, %r24, 0
	lis %r25, 0
	ori %r25, %r25, 65280
	rldicr %r25, %r25, 32, 31
	oris %r25, %r25, 0
	ori %r25, %r25, 65280
	lis %r27, 21845
	ori %r27, %r27, 21845
	rldicr %r27, %r27, 32, 31
	oris %r27, %r27, 21845
	ori %r27, %r27, 21845
	lis %r28, 13107
	ori %r28, %r28, 13107
	rldicr %r28, %r28, 32, 31
	oris %r28, %r28, 13107
	ori %r28, %r28, 13107
	lis %r29, 3855
	ori %r29, %r29, 3855
	rldicr %r29, %r29, 32, 31
	oris %r29, %r29, 3855
	ori %r29, %r29, 3855
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	std %r14, 3120(%r8)
	ld %r14, 576(%r8)
	ld %r15, 584(%r8)
	ld %r16, 592(%r8)
	ld %r17, 600(%r8)
	ld %r18, 608(%r8)
	ld %r19, 616(%r8)
	ld %r20, 624(%r8)
	ld %r21, 632(%r8)
	lis %r24, 0
	ori %r24, %r24, 0
	rldicr %r24, %r24, 32, 31
	oris %r24, %r24, 65535
	ori %r24, %r24, 0
	lis %r25, 0
	ori %r25, %r25, 65280
	rldicr %r25, %r25, 32, 31
	oris %r25, %r25, 0
	ori %r25, %r25, 65280
	lis %r27, 21845
	ori %r27, %r27, 21845
	rldicr %r27, %r27, 32, 31
	oris %r27, %r27, 21845
	ori %r27, %r27, 21845
	lis %r28, 13107
	ori %r28, %r28, 13107
	rldicr %r28, %r28, 32, 31
	oris %r28, %r28, 13107
	ori %r28, %r28, 13107
	lis %r29, 3855
	ori %r29, %r29, 3855
	rldicr %r29, %r29, 32, 31
	oris %r29, %r29, 3855
	ori %r29, %r29, 3855
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	std %r14, 3128(%r8)
	addi %r4, %r4, 128
	rldicl %r23, %r7, 63, 1
	cmpldi %cr0, %r23, 0
	bne %cr0, 25f
	ld %r22, 3120(%r8)
	std %r22, 3152(%r8)
	ld %r22, 3128(%r8)
	std %r22, 3160(%r8)
	b 26f
25:
	addi %r23, %r7, -3
	cmpldi %cr0, %r23, 0
	beq %cr0, 27f
	ld %r22, 3120(%r8)
	std %r22, 3136(%r8)
	ld %r22, 3128(%r8)
	std %r22, 3144(%r8)
	ld %r22, 3104(%r8)
	ld %r23, 3120(%r8)
	xor %r22, %r22, %r23
	std %r22, 3120(%r8)
	ld %r22, 3112(%r8)
	ld %r23, 3128(%r8)
	xor %r22, %r22, %r23
	std %r22, 3128(%r8)
	b 28f
27:
	ld %r22, 3088(%r8)
	ld %r23, 3120(%r8)
	xor %r22, %r22, %r23
	std %r22, 3120(%r8)
	ld %r22, 3096(%r8)
	ld %r23, 3128(%r8)
	xor %r22, %r22, %r23
	std %r22, 3128(%r8)
28:
26:
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 24b
	li %r12, 3088
	ldbrx %r14, %r8, %r12
	li %r12, 3096
	ldbrx %r15, %r8, %r12
	li %r12, 3104
	ldbrx %r16, %r8, %r12
	li %r12, 3112
	ldbrx %r17, %r8, %r12
	li %r12, 3136
	ldbrx %r18, %r8, %r12
	li %r12, 3144
	ldbrx %r19, %r8, %r12
	li %r12, 3152
	ldbrx %r20, %r8, %r12
	li %r12, 3160
	ldbrx %r21, %r8, %r12
	addi %r22, %r6, -16
	cmpldi %cr0, %r22, 0
	beq %cr0, 29f
	or %r22, %r14, %r14
	li %r12, 0
	stdbrx %r22, %r5, %r12
	or %r22, %r15, %r15
	li %r12, 8
	stdbrx %r22, %r5, %r12
	or %r22, %r20, %r20
	li %r12, 16
	stdbrx %r22, %r5, %r12
	or %r22, %r21, %r21
	li %r12, 24
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r16, 15, 48
	rldicl %r23, %r17, 15, 49
	or %r22, %r22, %r23
	li %r12, 32
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r17, 15, 48
	rldicl %r23, %r16, 15, 49
	or %r22, %r22, %r23
	li %r12, 40
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r18, 15, 48
	rldicl %r23, %r19, 15, 49
	or %r22, %r22, %r23
	li %r12, 48
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r19, 15, 48
	rldicl %r23, %r18, 15, 49
	or %r22, %r22, %r23
	li %r12, 56
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r16, 30, 33
	rldicl %r23, %r17, 30, 34
	or %r22, %r22, %r23
	li %r12, 64
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r17, 30, 33
	rldicl %r23, %r16, 30, 34
	or %r22, %r22, %r23
	li %r12, 72
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r20, 30, 33
	rldicl %r23, %r21, 30, 34
	or %r22, %r22, %r23
	li %r12, 80
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r21, 30, 33
	rldicl %r23, %r20, 30, 34
	or %r22, %r22, %r23
	li %r12, 88
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r14, 45, 18
	rldicl %r23, %r15, 45, 19
	or %r22, %r22, %r23
	li %r12, 96
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r15, 45, 18
	rldicl %r23, %r14, 45, 19
	or %r22, %r22, %r23
	li %r12, 104
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r18, 45, 18
	rldicl %r23, %r19, 45, 19
	or %r22, %r22, %r23
	li %r12, 112
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r19, 45, 18
	rldicl %r23, %r18, 45, 19
	or %r22, %r22, %r23
	li %r12, 120
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r14, 60, 3
	rldicl %r23, %r15, 60, 4
	or %r22, %r22, %r23
	li %r12, 128
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r15, 60, 3
	rldicl %r23, %r14, 60, 4
	or %r22, %r22, %r23
	li %r12, 136
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r16, 60, 3
	rldicl %r23, %r17, 60, 4
	or %r22, %r22, %r23
	li %r12, 144
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r17, 60, 3
	rldicl %r23, %r16, 60, 4
	or %r22, %r22, %r23
	li %r12, 152
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r20, 60, 3
	rldicl %r23, %r21, 60, 4
	or %r22, %r22, %r23
	li %r12, 160
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r21, 60, 3
	rldicl %r23, %r20, 60, 4
	or %r22, %r22, %r23
	li %r12, 168
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r15, 13, 50
	rldicl %r23, %r14, 13, 51
	or %r22, %r22, %r23
	li %r12, 176
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r14, 13, 50
	rldicl %r23, %r15, 13, 51
	or %r22, %r22, %r23
	li %r12, 184
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r19, 13, 50
	rldicl %r23, %r18, 13, 51
	or %r22, %r22, %r23
	li %r12, 192
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r18, 13, 50
	rldicl %r23, %r19, 13, 51
	or %r22, %r22, %r23
	li %r12, 200
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r17, 30, 33
	rldicl %r23, %r16, 30, 34
	or %r22, %r22, %r23
	li %r12, 208
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r16, 30, 33
	rldicl %r23, %r17, 30, 34
	or %r22, %r22, %r23
	li %r12, 216
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r19, 30, 33
	rldicl %r23, %r18, 30, 34
	or %r22, %r22, %r23
	li %r12, 224
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r18, 30, 33
	rldicl %r23, %r19, 30, 34
	or %r22, %r22, %r23
	li %r12, 232
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r15, 47, 16
	rldicl %r23, %r14, 47, 17
	or %r22, %r22, %r23
	li %r12, 240
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r14, 47, 16
	rldicl %r23, %r15, 47, 17
	or %r22, %r22, %r23
	li %r12, 248
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r21, 47, 16
	rldicl %r23, %r20, 47, 17
	or %r22, %r22, %r23
	li %r12, 256
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r20, 47, 16
	rldicl %r23, %r21, 47, 17
	or %r22, %r22, %r23
	li %r12, 264
	stdbrx %r22, %r5, %r12
	b 210f
29:
	or %r22, %r14, %r14
	li %r12, 0
	stdbrx %r22, %r5, %r12
	or %r22, %r15, %r15
	li %r12, 8
	stdbrx %r22, %r5, %r12
	or %r22, %r18, %r18
	li %r12, 16
	stdbrx %r22, %r5, %r12
	or %r22, %r19, %r19
	li %r12, 24
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r14, 15, 48
	rldicl %r23, %r15, 15, 49
	or %r22, %r22, %r23
	li %r12, 32
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r15, 15, 48
	rldicl %r23, %r14, 15, 49
	or %r22, %r22, %r23
	li %r12, 40
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r18, 15, 48
	rldicl %r23, %r19, 15, 49
	or %r22, %r22, %r23
	li %r12, 48
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r19, 15, 48
	rldicl %r23, %r18, 15, 49
	or %r22, %r22, %r23
	li %r12, 56
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r18, 30, 33
	rldicl %r23, %r19, 30, 34
	or %r22, %r22, %r23
	li %r12, 64
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r19, 30, 33
	rldicl %r23, %r18, 30, 34
	or %r22, %r22, %r23
	li %r12, 72
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r14, 45, 18
	rldicl %r23, %r15, 45, 19
	or %r22, %r22, %r23
	li %r12, 80
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r15, 45, 18
	rldicl %r23, %r14, 45, 19
	or %r22, %r22, %r23
	li %r12, 88
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r18, 45, 18
	rldicl %r23, %r19, 45, 19
	or %r22, %r22, %r23
	li %r12, 96
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r15, 60, 3
	rldicl %r23, %r14, 60, 4
	or %r22, %r22, %r23
	li %r12, 104
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r18, 60, 3
	rldicl %r23, %r19, 60, 4
	or %r22, %r22, %r23
	li %r12, 112
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r19, 60, 3
	rldicl %r23, %r18, 60, 4
	or %r22, %r22, %r23
	li %r12, 120
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r15, 13, 50
	rldicl %r23, %r14, 13, 51
	or %r22, %r22, %r23
	li %r12, 128
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r14, 13, 50
	rldicl %r23, %r15, 13, 51
	or %r22, %r22, %r23
	li %r12, 136
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r15, 30, 33
	rldicl %r23, %r14, 30, 34
	or %r22, %r22, %r23
	li %r12, 144
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r14, 30, 33
	rldicl %r23, %r15, 30, 34
	or %r22, %r22, %r23
	li %r12, 152
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r19, 30, 33
	rldicl %r23, %r18, 30, 34
	or %r22, %r22, %r23
	li %r12, 160
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r18, 30, 33
	rldicl %r23, %r19, 30, 34
	or %r22, %r22, %r23
	li %r12, 168
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r15, 47, 16
	rldicl %r23, %r14, 47, 17
	or %r22, %r22, %r23
	li %r12, 176
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r14, 47, 16
	rldicl %r23, %r15, 47, 17
	or %r22, %r22, %r23
	li %r12, 184
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r19, 47, 16
	rldicl %r23, %r18, 47, 17
	or %r22, %r22, %r23
	li %r12, 192
	stdbrx %r22, %r5, %r12
	rldicr %r22, %r18, 47, 16
	rldicl %r23, %r19, 47, 17
	or %r22, %r22, %r23
	li %r12, 200
	stdbrx %r22, %r5, %r12
210:
	ld %r14, 2944(%r8)
	ld %r15, 2952(%r8)
	ld %r16, 2960(%r8)
	ld %r17, 2968(%r8)
	ld %r18, 2976(%r8)
	ld %r19, 2984(%r8)
	ld %r20, 2992(%r8)
	ld %r21, 3000(%r8)
	ld %r22, 3008(%r8)
	ld %r23, 3016(%r8)
	ld %r24, 3024(%r8)
	ld %r25, 3032(%r8)
	ld %r26, 3040(%r8)
	ld %r27, 3048(%r8)
	ld %r28, 3056(%r8)
	ld %r29, 3064(%r8)
	ld %r30, 3072(%r8)
	ld %r31, 3080(%r8)
	addi %r12, %r1, 32
	li %r0, 0
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	std %r0, 128(%r12)
	std %r0, 136(%r12)
	std %r0, 144(%r12)
	std %r0, 152(%r12)
	std %r0, 160(%r12)
	std %r0, 168(%r12)
	std %r0, 176(%r12)
	std %r0, 184(%r12)
	std %r0, 192(%r12)
	std %r0, 200(%r12)
	std %r0, 208(%r12)
	std %r0, 216(%r12)
	std %r0, 224(%r12)
	std %r0, 232(%r12)
	addi %r1, %r1, 3344
	li %r0, 0
	li %r3, 0
	li %r4, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r11, 0
	li %r12, 0
	blr

vg_camellia_ecb_encrypt:
	stdu %r1, -3344(%r1)
	addi %r7, %r1, 32
	or %r8, %r7, %r7
	std %r14, 2944(%r8)
	std %r15, 2952(%r8)
	std %r16, 2960(%r8)
	std %r17, 2968(%r8)
	std %r18, 2976(%r8)
	std %r19, 2984(%r8)
	std %r20, 2992(%r8)
	std %r21, 3000(%r8)
	std %r22, 3008(%r8)
	std %r23, 3016(%r8)
	std %r24, 3024(%r8)
	std %r25, 3032(%r8)
	std %r26, 3040(%r8)
	std %r27, 3048(%r8)
	std %r28, 3056(%r8)
	std %r29, 3064(%r8)
	std %r30, 3072(%r8)
	std %r31, 3080(%r8)
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
	lis %r22, 255
	ori %r22, %r22, 65280
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 400(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 255
	ori %r22, %r22, 65280
	std %r22, 408(%r8)
	lis %r22, 0
	ori %r22, %r22, 255
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65280
	ori %r22, %r22, 0
	std %r22, 416(%r8)
	addi %r22, %r4, -18
	cmpldi %cr0, %r22, 0
	beq %cr0, 20f
	addi %r7, %r8, 2816
	li %r23, 34
	b 21f
20:
	addi %r7, %r8, 2304
	li %r23, 26
21:
	addi %r4, %r8, 768
22:
	ld %r14, 0(%r3)
	or %r15, %r14, %r14
	or %r16, %r14, %r14
	or %r17, %r14, %r14
	or %r18, %r14, %r14
	or %r19, %r14, %r14
	or %r20, %r14, %r14
	or %r21, %r14, %r14
	lis %r24, 0
	ori %r24, %r24, 0
	rldicr %r24, %r24, 32, 31
	oris %r24, %r24, 65535
	ori %r24, %r24, 0
	lis %r25, 0
	ori %r25, %r25, 65280
	rldicr %r25, %r25, 32, 31
	oris %r25, %r25, 0
	ori %r25, %r25, 65280
	lis %r27, 21845
	ori %r27, %r27, 21845
	rldicr %r27, %r27, 32, 31
	oris %r27, %r27, 21845
	ori %r27, %r27, 21845
	lis %r28, 13107
	ori %r28, %r28, 13107
	rldicr %r28, %r28, 32, 31
	oris %r28, %r28, 13107
	ori %r28, %r28, 13107
	lis %r29, 3855
	ori %r29, %r29, 3855
	rldicr %r29, %r29, 32, 31
	oris %r29, %r29, 3855
	ori %r29, %r29, 3855
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 0(%r4)
	std %r15, 8(%r4)
	std %r16, 16(%r4)
	std %r17, 24(%r4)
	std %r18, 32(%r4)
	std %r19, 40(%r4)
	std %r20, 48(%r4)
	std %r21, 56(%r4)
	addi %r4, %r4, 64
	addi %r3, %r3, 8
	addi %r23, %r23, -1
	cmpldi %cr0, %r23, 0
	bne %cr0, 22b
	cmpldi %cr0, %r6, 0
	beq %cr0, 23f
25:
	rldicl %r22, %r6, 61, 3
	cmpldi %cr0, %r22, 0
	bne %cr0, 26f
	or %r12, %r6, %r6
	b 27f
26:
	li %r12, 8
27:
	or %r9, %r5, %r5
	addi %r10, %r8, 3088
	or %r11, %r12, %r12
28:
	ld %r22, 0(%r9)
	std %r22, 0(%r10)
	ld %r22, 8(%r9)
	std %r22, 8(%r10)
	addi %r9, %r9, 16
	addi %r10, %r10, 16
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 28b
	addi %r4, %r8, 768
	ld %r14, 3096(%r8)
	ld %r15, 3112(%r8)
	ld %r16, 3128(%r8)
	ld %r17, 3144(%r8)
	ld %r18, 3160(%r8)
	ld %r19, 3176(%r8)
	ld %r20, 3192(%r8)
	ld %r21, 3208(%r8)
	lis %r24, 0
	ori %r24, %r24, 0
	rldicr %r24, %r24, 32, 31
	oris %r24, %r24, 65535
	ori %r24, %r24, 0
	lis %r25, 0
	ori %r25, %r25, 65280
	rldicr %r25, %r25, 32, 31
	oris %r25, %r25, 0
	ori %r25, %r25, 65280
	lis %r27, 21845
	ori %r27, %r27, 21845
	rldicr %r27, %r27, 32, 31
	oris %r27, %r27, 21845
	ori %r27, %r27, 21845
	lis %r28, 13107
	ori %r28, %r28, 13107
	rldicr %r28, %r28, 32, 31
	oris %r28, %r28, 13107
	ori %r28, %r28, 13107
	lis %r29, 3855
	ori %r29, %r29, 3855
	rldicr %r29, %r29, 32, 31
	oris %r29, %r29, 3855
	ori %r29, %r29, 3855
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 576(%r8)
	std %r15, 584(%r8)
	std %r16, 592(%r8)
	std %r17, 600(%r8)
	std %r18, 608(%r8)
	std %r19, 616(%r8)
	std %r20, 624(%r8)
	std %r21, 632(%r8)
	ld %r14, 3088(%r8)
	ld %r15, 3104(%r8)
	ld %r16, 3120(%r8)
	ld %r17, 3136(%r8)
	ld %r18, 3152(%r8)
	ld %r19, 3168(%r8)
	ld %r20, 3184(%r8)
	ld %r21, 3200(%r8)
	lis %r24, 0
	ori %r24, %r24, 0
	rldicr %r24, %r24, 32, 31
	oris %r24, %r24, 65535
	ori %r24, %r24, 0
	lis %r25, 0
	ori %r25, %r25, 65280
	rldicr %r25, %r25, 32, 31
	oris %r25, %r25, 0
	ori %r25, %r25, 65280
	lis %r27, 21845
	ori %r27, %r27, 21845
	rldicr %r27, %r27, 32, 31
	oris %r27, %r27, 21845
	ori %r27, %r27, 21845
	lis %r28, 13107
	ori %r28, %r28, 13107
	rldicr %r28, %r28, 32, 31
	oris %r28, %r28, 13107
	ori %r28, %r28, 13107
	lis %r29, 3855
	ori %r29, %r29, 3855
	rldicr %r29, %r29, 32, 31
	oris %r29, %r29, 3855
	ori %r29, %r29, 3855
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	ld %r22, 0(%r4)
	xor %r14, %r14, %r22
	ld %r22, 8(%r4)
	xor %r15, %r15, %r22
	ld %r22, 16(%r4)
	xor %r16, %r16, %r22
	ld %r22, 24(%r4)
	xor %r17, %r17, %r22
	ld %r22, 32(%r4)
	xor %r18, %r18, %r22
	ld %r22, 40(%r4)
	xor %r19, %r19, %r22
	ld %r22, 48(%r4)
	xor %r20, %r20, %r22
	ld %r22, 56(%r4)
	xor %r21, %r21, %r22
	std %r14, 512(%r8)
	std %r15, 520(%r8)
	std %r16, 528(%r8)
	std %r17, 536(%r8)
	std %r18, 544(%r8)
	std %r19, 552(%r8)
	std %r20, 560(%r8)
	std %r21, 568(%r8)
	ld %r22, 576(%r8)
	ld %r24, 64(%r4)
	xor %r22, %r22, %r24
	std %r22, 576(%r8)
	ld %r22, 584(%r8)
	ld %r24, 72(%r4)
	xor %r22, %r22, %r24
	std %r22, 584(%r8)
	ld %r22, 592(%r8)
	ld %r24, 80(%r4)
	xor %r22, %r22, %r24
	std %r22, 592(%r8)
	ld %r22, 600(%r8)
	ld %r24, 88(%r4)
	xor %r22, %r22, %r24
	std %r22, 600(%r8)
	ld %r22, 608(%r8)
	ld %r24, 96(%r4)
	xor %r22, %r22, %r24
	std %r22, 608(%r8)
	ld %r22, 616(%r8)
	ld %r24, 104(%r4)
	xor %r22, %r22, %r24
	std %r22, 616(%r8)
	ld %r22, 624(%r8)
	ld %r24, 112(%r4)
	xor %r22, %r22, %r24
	std %r22, 624(%r8)
	ld %r22, 632(%r8)
	ld %r24, 120(%r4)
	xor %r22, %r22, %r24
	std %r22, 632(%r8)
	addi %r4, %r4, 128
29:
	addi %r3, %r4, 384
210:
	ld %r22, 0(%r4)
	xor %r14, %r14, %r22
	ld %r22, 8(%r4)
	xor %r15, %r15, %r22
	ld %r22, 16(%r4)
	xor %r16, %r16, %r22
	ld %r22, 24(%r4)
	xor %r17, %r17, %r22
	ld %r22, 32(%r4)
	xor %r18, %r18, %r22
	ld %r22, 40(%r4)
	xor %r19, %r19, %r22
	ld %r22, 48(%r4)
	xor %r20, %r20, %r22
	ld %r22, 56(%r4)
	xor %r21, %r21, %r22
	ld %r30, 400(%r8)
	or %r23, %r21, %r21
	xor %r22, %r21, %r20
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	xor %r22, %r20, %r19
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	xor %r22, %r19, %r18
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	xor %r22, %r18, %r17
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	xor %r22, %r17, %r16
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	xor %r22, %r16, %r15
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	xor %r22, %r15, %r14
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	xor %r22, %r14, %r23
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	li %r31, 0
	addi %r31, %r31, -1
	xor %r22, %r21, %r15
	xor %r23, %r19, %r17
	xor %r24, %r16, %r22
	xor %r25, %r20, %r14
	xor %r26, %r14, %r23
	xor %r27, %r18, %r15
	xor %r28, %r18, %r24
	xor %r29, %r20, %r23
	xor %r30, %r16, %r25
	xor %r0, %r24, %r25
	xor %r9, %r21, %r20
	std %r30, 0(%r8)
	xor %r30, %r21, %r25
	std %r21, 8(%r8)
	xor %r21, %r30, %r31
	std %r30, 16(%r8)
	xor %r30, %r20, %r17
	std %r21, 24(%r8)
	xor %r21, %r19, %r15
	std %r20, 32(%r8)
	xor %r20, %r19, %r14
	xor %r19, %r19, %r24
	xor %r25, %r18, %r25
	xor %r18, %r18, %r9
	xor %r17, %r17, %r14
	xor %r17, %r17, %r31
	xor %r14, %r16, %r26
	xor %r16, %r16, %r27
	xor %r16, %r16, %r31
	xor %r9, %r15, %r29
	xor %r9, %r9, %r31
	std %r9, 40(%r8)
	xor %r9, %r22, %r26
	xor %r22, %r22, %r29
	xor %r29, %r23, %r27
	std %r9, 48(%r8)
	xor %r9, %r23, %r28
	xor %r23, %r23, %r0
	std %r23, 56(%r8)
	xor %r23, %r24, %r26
	xor %r23, %r23, %r31
	xor %r24, %r24, %r30
	xor %r24, %r24, %r31
	xor %r26, %r26, %r27
	xor %r26, %r26, %r31
	xor %r20, %r28, %r20
	xor %r20, %r20, %r31
	ld %r27, 0(%r8)
	xor %r21, %r27, %r21
	xor %r21, %r21, %r31
	xor %r27, %r27, %r29
	xor %r27, %r27, %r31
	ld %r29, 8(%r8)
	ld %r30, 32(%r8)
	std %r24, 0(%r8)
	xor %r24, %r29, %r30
	xor %r24, %r24, %r31
	xor %r24, %r24, %r30
	xor %r29, %r29, %r15
	xor %r29, %r29, %r31
	and %r15, %r16, %r18
	and %r30, %r24, %r21
	xor %r30, %r30, %r15
	std %r31, 8(%r8)
	and %r31, %r28, %r20
	xor %r31, %r31, %r15
	and %r15, %r14, %r23
	std %r14, 32(%r8)
	and %r14, %r22, %r19
	xor %r14, %r14, %r15
	std %r22, 64(%r8)
	and %r22, %r0, %r17
	xor %r22, %r22, %r15
	and %r15, %r25, %r9
	std %r25, 72(%r8)
	and %r25, %r26, %r27
	xor %r25, %r25, %r15
	std %r26, 80(%r8)
	ld %r26, 40(%r8)
	std %r0, 88(%r8)
	ld %r0, 24(%r8)
	std %r28, 96(%r8)
	and %r28, %r26, %r0
	xor %r28, %r28, %r15
	xor %r30, %r30, %r25
	xor %r31, %r31, %r28
	xor %r14, %r14, %r25
	xor %r22, %r22, %r28
	ld %r28, 56(%r8)
	xor %r30, %r30, %r28
	ld %r28, 48(%r8)
	xor %r31, %r31, %r28
	xor %r14, %r14, %r29
	ld %r29, 0(%r8)
	xor %r22, %r22, %r29
	xor %r29, %r30, %r31
	and %r30, %r30, %r14
	xor %r28, %r22, %r30
	and %r25, %r29, %r28
	xor %r25, %r25, %r31
	xor %r15, %r14, %r22
	xor %r31, %r31, %r30
	and %r31, %r31, %r15
	xor %r31, %r31, %r22
	xor %r14, %r14, %r31
	xor %r15, %r28, %r31
	and %r22, %r22, %r15
	xor %r14, %r22, %r14
	xor %r28, %r28, %r22
	and %r28, %r25, %r28
	xor %r29, %r29, %r28
	xor %r28, %r29, %r14
	xor %r22, %r25, %r31
	xor %r15, %r25, %r29
	xor %r30, %r31, %r14
	xor %r26, %r22, %r28
	and %r18, %r30, %r18
	and %r21, %r14, %r21
	and %r20, %r31, %r20
	and %r23, %r15, %r23
	and %r19, %r29, %r19
	and %r17, %r25, %r17
	and %r9, %r22, %r9
	and %r27, %r26, %r27
	and %r0, %r28, %r0
	and %r30, %r30, %r16
	and %r14, %r14, %r24
	ld %r24, 96(%r8)
	and %r31, %r31, %r24
	ld %r24, 32(%r8)
	and %r15, %r15, %r24
	ld %r24, 64(%r8)
	and %r29, %r29, %r24
	ld %r24, 88(%r8)
	and %r25, %r25, %r24
	ld %r24, 72(%r8)
	and %r22, %r22, %r24
	ld %r24, 80(%r8)
	and %r26, %r26, %r24
	ld %r24, 40(%r8)
	and %r28, %r28, %r24
	xor %r27, %r21, %r27
	xor %r23, %r23, %r17
	xor %r24, %r9, %r0
	xor %r16, %r18, %r26
	xor %r31, %r31, %r27
	std %r27, 40(%r8)
	xor %r27, %r15, %r23
	std %r23, 80(%r8)
	xor %r23, %r22, %r24
	xor %r25, %r20, %r25
	xor %r9, %r9, %r28
	xor %r0, %r0, %r30
	xor %r30, %r30, %r14
	xor %r29, %r29, %r27
	xor %r26, %r26, %r23
	std %r26, 72(%r8)
	xor %r26, %r16, %r31
	xor %r18, %r18, %r20
	xor %r21, %r21, %r19
	xor %r17, %r17, %r16
	xor %r14, %r14, %r9
	xor %r15, %r15, %r31
	ld %r31, 40(%r8)
	xor %r22, %r22, %r31
	xor %r28, %r28, %r0
	ld %r31, 80(%r8)
	xor %r31, %r31, %r30
	xor %r18, %r24, %r18
	xor %r27, %r27, %r25
	xor %r23, %r23, %r30
	xor %r25, %r25, %r0
	xor %r9, %r9, %r22
	ld %r22, 72(%r8)
	xor %r0, %r29, %r22
	xor %r29, %r29, %r26
	xor %r22, %r22, %r31
	ld %r31, 8(%r8)
	xor %r19, %r22, %r31
	xor %r26, %r26, %r14
	xor %r16, %r26, %r31
	xor %r21, %r21, %r17
	xor %r15, %r15, %r25
	xor %r17, %r15, %r31
	xor %r28, %r28, %r29
	xor %r15, %r28, %r31
	xor %r27, %r27, %r9
	xor %r23, %r23, %r21
	xor %r20, %r23, %r31
	or %r21, %r27, %r27
	or %r14, %r0, %r0
	ld %r30, 408(%r8)
	or %r23, %r21, %r21
	xor %r22, %r21, %r20
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	xor %r22, %r20, %r19
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	xor %r22, %r19, %r18
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	xor %r22, %r18, %r17
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	xor %r22, %r17, %r16
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	xor %r22, %r16, %r15
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	xor %r22, %r15, %r14
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	xor %r22, %r14, %r23
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	ld %r30, 416(%r8)
	or %r23, %r14, %r14
	xor %r22, %r14, %r15
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	xor %r22, %r15, %r16
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	xor %r22, %r16, %r17
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	xor %r22, %r17, %r18
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	xor %r22, %r18, %r19
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	xor %r22, %r19, %r20
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	xor %r22, %r20, %r21
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	xor %r22, %r21, %r23
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	ld %r30, 384(%r8)
	ld %r24, 392(%r8)
	rldicl %r22, %r14, 56, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 24, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 56, 0
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 24, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 24, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 56, 0
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 24, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 24, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 56, 0
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 24, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 24, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 56, 0
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 24, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 24, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 56, 0
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 24, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 24, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 56, 0
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 24, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 24, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 56, 0
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 24, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 24, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 8, 0
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 56, 0
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 24, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	ld %r22, 576(%r8)
	xor %r14, %r14, %r22
	std %r14, 576(%r8)
	ld %r22, 584(%r8)
	xor %r15, %r15, %r22
	std %r15, 584(%r8)
	ld %r22, 592(%r8)
	xor %r16, %r16, %r22
	std %r16, 592(%r8)
	ld %r22, 600(%r8)
	xor %r17, %r17, %r22
	std %r17, 600(%r8)
	ld %r22, 608(%r8)
	xor %r18, %r18, %r22
	std %r18, 608(%r8)
	ld %r22, 616(%r8)
	xor %r19, %r19, %r22
	std %r19, 616(%r8)
	ld %r22, 624(%r8)
	xor %r20, %r20, %r22
	std %r20, 624(%r8)
	ld %r22, 632(%r8)
	xor %r21, %r21, %r22
	std %r21, 632(%r8)
	ld %r22, 64(%r4)
	xor %r14, %r14, %r22
	ld %r22, 72(%r4)
	xor %r15, %r15, %r22
	ld %r22, 80(%r4)
	xor %r16, %r16, %r22
	ld %r22, 88(%r4)
	xor %r17, %r17, %r22
	ld %r22, 96(%r4)
	xor %r18, %r18, %r22
	ld %r22, 104(%r4)
	xor %r19, %r19, %r22
	ld %r22, 112(%r4)
	xor %r20, %r20, %r22
	ld %r22, 120(%r4)
	xor %r21, %r21, %r22
	ld %r30, 400(%r8)
	or %r23, %r21, %r21
	xor %r22, %r21, %r20
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	xor %r22, %r20, %r19
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	xor %r22, %r19, %r18
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	xor %r22, %r18, %r17
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	xor %r22, %r17, %r16
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	xor %r22, %r16, %r15
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	xor %r22, %r15, %r14
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	xor %r22, %r14, %r23
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	li %r31, 0
	addi %r31, %r31, -1
	xor %r22, %r21, %r15
	xor %r23, %r19, %r17
	xor %r24, %r16, %r22
	xor %r25, %r20, %r14
	xor %r26, %r14, %r23
	xor %r27, %r18, %r15
	xor %r28, %r18, %r24
	xor %r29, %r20, %r23
	xor %r30, %r16, %r25
	xor %r0, %r24, %r25
	xor %r9, %r21, %r20
	std %r30, 0(%r8)
	xor %r30, %r21, %r25
	std %r21, 8(%r8)
	xor %r21, %r30, %r31
	std %r30, 16(%r8)
	xor %r30, %r20, %r17
	std %r21, 24(%r8)
	xor %r21, %r19, %r15
	std %r20, 32(%r8)
	xor %r20, %r19, %r14
	xor %r19, %r19, %r24
	xor %r25, %r18, %r25
	xor %r18, %r18, %r9
	xor %r17, %r17, %r14
	xor %r17, %r17, %r31
	xor %r14, %r16, %r26
	xor %r16, %r16, %r27
	xor %r16, %r16, %r31
	xor %r9, %r15, %r29
	xor %r9, %r9, %r31
	std %r9, 40(%r8)
	xor %r9, %r22, %r26
	xor %r22, %r22, %r29
	xor %r29, %r23, %r27
	std %r9, 48(%r8)
	xor %r9, %r23, %r28
	xor %r23, %r23, %r0
	std %r23, 56(%r8)
	xor %r23, %r24, %r26
	xor %r23, %r23, %r31
	xor %r24, %r24, %r30
	xor %r24, %r24, %r31
	xor %r26, %r26, %r27
	xor %r26, %r26, %r31
	xor %r20, %r28, %r20
	xor %r20, %r20, %r31
	ld %r27, 0(%r8)
	xor %r21, %r27, %r21
	xor %r21, %r21, %r31
	xor %r27, %r27, %r29
	xor %r27, %r27, %r31
	ld %r29, 8(%r8)
	ld %r30, 32(%r8)
	std %r24, 0(%r8)
	xor %r24, %r29, %r30
	xor %r24, %r24, %r31
	xor %r24, %r24, %r30
	xor %r29, %r29, %r15
	xor %r29, %r29, %r31
	and %r15, %r16, %r18
	and %r30, %r24, %r21
	xor %r30, %r30, %r15
	std %r31, 8(%r8)
	and %r31, %r28, %r20
	xor %r31, %r31, %r15
	and %r15, %r14, %r23
	std %r14, 32(%r8)
	and %r14, %r22, %r19
	xor %r14, %r14, %r15
	std %r22, 64(%r8)
	and %r22, %r0, %r17
	xor %r22, %r22, %r15
	and %r15, %r25, %r9
	std %r25, 72(%r8)
	and %r25, %r26, %r27
	xor %r25, %r25, %r15
	std %r26, 80(%r8)
	ld %r26, 40(%r8)
	std %r0, 88(%r8)
	ld %r0, 24(%r8)
	std %r28, 96(%r8)
	and %r28, %r26, %r0
	xor %r28, %r28, %r15
	xor %r30, %r30, %r25
	xor %r31, %r31, %r28
	xor %r14, %r14, %r25
	xor %r22, %r22, %r28
	ld %r28, 56(%r8)
	xor %r30, %r30, %r28
	ld %r28, 48(%r8)
	xor %r31, %r31, %r28
	xor %r14, %r14, %r29
	ld %r29, 0(%r8)
	xor %r22, %r22, %r29
	xor %r29, %r30, %r31
	and %r30, %r30, %r14
	xor %r28, %r22, %r30
	and %r25, %r29, %r28
	xor %r25, %r25, %r31
	xor %r15, %r14, %r22
	xor %r31, %r31, %r30
	and %r31, %r31, %r15
	xor %r31, %r31, %r22
	xor %r14, %r14, %r31
	xor %r15, %r28, %r31
	and %r22, %r22, %r15
	xor %r14, %r22, %r14
	xor %r28, %r28, %r22
	and %r28, %r25, %r28
	xor %r29, %r29, %r28
	xor %r28, %r29, %r14
	xor %r22, %r25, %r31
	xor %r15, %r25, %r29
	xor %r30, %r31, %r14
	xor %r26, %r22, %r28
	and %r18, %r30, %r18
	and %r21, %r14, %r21
	and %r20, %r31, %r20
	and %r23, %r15, %r23
	and %r19, %r29, %r19
	and %r17, %r25, %r17
	and %r9, %r22, %r9
	and %r27, %r26, %r27
	and %r0, %r28, %r0
	and %r30, %r30, %r16
	and %r14, %r14, %r24
	ld %r24, 96(%r8)
	and %r31, %r31, %r24
	ld %r24, 32(%r8)
	and %r15, %r15, %r24
	ld %r24, 64(%r8)
	and %r29, %r29, %r24
	ld %r24, 88(%r8)
	and %r25, %r25, %r24
	ld %r24, 72(%r8)
	and %r22, %r22, %r24
	ld %r24, 80(%r8)
	and %r26, %r26, %r24
	ld %r24, 40(%r8)
	and %r28, %r28, %r24
	xor %r27, %r21, %r27
	xor %r23, %r23, %r17
	xor %r24, %r9, %r0
	xor %r16, %r18, %r26
	xor %r31, %r31, %r27
	std %r27, 40(%r8)
	xor %r27, %r15, %r23
	std %r23, 80(%r8)
	xor %r23, %r22, %r24
	xor %r25, %r20, %r25
	xor %r9, %r9, %r28
	xor %r0, %r0, %r30
	xor %r30, %r30, %r14
	xor %r29, %r29, %r27
	xor %r26, %r26, %r23
	std %r26, 72(%r8)
	xor %r26, %r16, %r31
	xor %r18, %r18, %r20
	xor %r21, %r21, %r19
	xor %r17, %r17, %r16
	xor %r14, %r14, %r9
	xor %r15, %r15, %r31
	ld %r31, 40(%r8)
	xor %r22, %r22, %r31
	xor %r28, %r28, %r0
	ld %r31, 80(%r8)
	xor %r31, %r31, %r30
	xor %r18, %r24, %r18
	xor %r27, %r27, %r25
	xor %r23, %r23, %r30
	xor %r25, %r25, %r0
	xor %r9, %r9, %r22
	ld %r22, 72(%r8)
	xor %r0, %r29, %r22
	xor %r29, %r29, %r26
	xor %r22, %r22, %r31
	ld %r31, 8(%r8)
	xor %r19, %r22, %r31
	xor %r26, %r26, %r14
	xor %r16, %r26, %r31
	xor %r21, %r21, %r17
	xor %r15, %r15, %r25
	xor %r17, %r15, %r31
	xor %r28, %r28, %r29
	xor %r15, %r28, %r31
	xor %r27, %r27, %r9
	xor %r23, %r23, %r21
	xor %r20, %r23, %r31
	or %r21, %r27, %r27
	or %r14, %r0, %r0
	ld %r30, 408(%r8)
	or %r23, %r21, %r21
	xor %r22, %r21, %r20
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	xor %r22, %r20, %r19
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	xor %r22, %r19, %r18
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	xor %r22, %r18, %r17
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	xor %r22, %r17, %r16
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	xor %r22, %r16, %r15
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	xor %r22, %r15, %r14
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	xor %r22, %r14, %r23
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	ld %r30, 416(%r8)
	or %r23, %r14, %r14
	xor %r22, %r14, %r15
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	xor %r22, %r15, %r16
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	xor %r22, %r16, %r17
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	xor %r22, %r17, %r18
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	xor %r22, %r18, %r19
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	xor %r22, %r19, %r20
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	xor %r22, %r20, %r21
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	xor %r22, %r21, %r23
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	ld %r30, 384(%r8)
	ld %r24, 392(%r8)
	rldicl %r22, %r14, 56, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 24, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 56, 0
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 24, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 24, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 56, 0
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 24, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 24, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 56, 0
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 24, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 24, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 56, 0
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 24, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 24, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 56, 0
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 24, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 24, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 56, 0
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 24, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 24, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 56, 0
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 24, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 24, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 8, 0
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 56, 0
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 24, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	ld %r22, 512(%r8)
	xor %r14, %r14, %r22
	std %r14, 512(%r8)
	ld %r22, 520(%r8)
	xor %r15, %r15, %r22
	std %r15, 520(%r8)
	ld %r22, 528(%r8)
	xor %r16, %r16, %r22
	std %r16, 528(%r8)
	ld %r22, 536(%r8)
	xor %r17, %r17, %r22
	std %r17, 536(%r8)
	ld %r22, 544(%r8)
	xor %r18, %r18, %r22
	std %r18, 544(%r8)
	ld %r22, 552(%r8)
	xor %r19, %r19, %r22
	std %r19, 552(%r8)
	ld %r22, 560(%r8)
	xor %r20, %r20, %r22
	std %r20, 560(%r8)
	ld %r22, 568(%r8)
	xor %r21, %r21, %r22
	std %r21, 568(%r8)
	addi %r4, %r4, 128
	subf %r22, %r3, %r4
	cmpldi %cr0, %r22, 0
	bne %cr0, 210b
	subf %r22, %r7, %r4
	cmpldi %cr0, %r22, 0
	bne %cr0, 211f
	b 212f
211:
	ld %r14, 576(%r8)
	ld %r15, 584(%r8)
	ld %r16, 592(%r8)
	ld %r17, 600(%r8)
	ld %r18, 608(%r8)
	ld %r19, 616(%r8)
	ld %r20, 624(%r8)
	ld %r21, 632(%r8)
	ld %r30, 384(%r8)
	ld %r24, 120(%r4)
	or %r22, %r21, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	ld %r24, 112(%r4)
	or %r22, %r20, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	ld %r24, 104(%r4)
	or %r22, %r19, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	ld %r24, 96(%r4)
	or %r22, %r18, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	ld %r24, 88(%r4)
	or %r22, %r17, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	ld %r24, 80(%r4)
	or %r22, %r16, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	ld %r24, 72(%r4)
	or %r22, %r15, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	ld %r24, 64(%r4)
	or %r22, %r14, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	ld %r30, 392(%r8)
	or %r23, %r21, %r21
	ld %r24, 112(%r4)
	and %r22, %r20, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	ld %r24, 104(%r4)
	and %r22, %r19, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	ld %r24, 96(%r4)
	and %r22, %r18, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	ld %r24, 88(%r4)
	and %r22, %r17, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	ld %r24, 80(%r4)
	and %r22, %r16, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	ld %r24, 72(%r4)
	and %r22, %r15, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	ld %r24, 64(%r4)
	and %r22, %r14, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	ld %r24, 120(%r4)
	and %r22, %r23, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	std %r14, 576(%r8)
	std %r15, 584(%r8)
	std %r16, 592(%r8)
	std %r17, 600(%r8)
	std %r18, 608(%r8)
	std %r19, 616(%r8)
	std %r20, 624(%r8)
	std %r21, 632(%r8)
	ld %r14, 512(%r8)
	ld %r15, 520(%r8)
	ld %r16, 528(%r8)
	ld %r17, 536(%r8)
	ld %r18, 544(%r8)
	ld %r19, 552(%r8)
	ld %r20, 560(%r8)
	ld %r21, 568(%r8)
	ld %r30, 392(%r8)
	or %r23, %r21, %r21
	ld %r24, 48(%r4)
	and %r22, %r20, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	ld %r24, 40(%r4)
	and %r22, %r19, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	ld %r24, 32(%r4)
	and %r22, %r18, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	ld %r24, 24(%r4)
	and %r22, %r17, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	ld %r24, 16(%r4)
	and %r22, %r16, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	ld %r24, 8(%r4)
	and %r22, %r15, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	ld %r24, 0(%r4)
	and %r22, %r14, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	ld %r24, 56(%r4)
	and %r22, %r23, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	ld %r30, 384(%r8)
	ld %r24, 56(%r4)
	or %r22, %r21, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	ld %r24, 48(%r4)
	or %r22, %r20, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	ld %r24, 40(%r4)
	or %r22, %r19, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	ld %r24, 32(%r4)
	or %r22, %r18, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	ld %r24, 24(%r4)
	or %r22, %r17, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	ld %r24, 16(%r4)
	or %r22, %r16, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	ld %r24, 8(%r4)
	or %r22, %r15, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	ld %r24, 0(%r4)
	or %r22, %r14, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	std %r14, 512(%r8)
	std %r15, 520(%r8)
	std %r16, 528(%r8)
	std %r17, 536(%r8)
	std %r18, 544(%r8)
	std %r19, 552(%r8)
	std %r20, 560(%r8)
	std %r21, 568(%r8)
	addi %r4, %r4, 128
212:
	subf %r22, %r7, %r4
	cmpldi %cr0, %r22, 0
	bne %cr0, 29b
	ld %r22, 64(%r4)
	xor %r14, %r14, %r22
	ld %r22, 72(%r4)
	xor %r15, %r15, %r22
	ld %r22, 80(%r4)
	xor %r16, %r16, %r22
	ld %r22, 88(%r4)
	xor %r17, %r17, %r22
	ld %r22, 96(%r4)
	xor %r18, %r18, %r22
	ld %r22, 104(%r4)
	xor %r19, %r19, %r22
	ld %r22, 112(%r4)
	xor %r20, %r20, %r22
	ld %r22, 120(%r4)
	xor %r21, %r21, %r22
	lis %r24, 0
	ori %r24, %r24, 0
	rldicr %r24, %r24, 32, 31
	oris %r24, %r24, 65535
	ori %r24, %r24, 0
	lis %r25, 0
	ori %r25, %r25, 65280
	rldicr %r25, %r25, 32, 31
	oris %r25, %r25, 0
	ori %r25, %r25, 65280
	lis %r27, 21845
	ori %r27, %r27, 21845
	rldicr %r27, %r27, 32, 31
	oris %r27, %r27, 21845
	ori %r27, %r27, 21845
	lis %r28, 13107
	ori %r28, %r28, 13107
	rldicr %r28, %r28, 32, 31
	oris %r28, %r28, 13107
	ori %r28, %r28, 13107
	lis %r29, 3855
	ori %r29, %r29, 3855
	rldicr %r29, %r29, 32, 31
	oris %r29, %r29, 3855
	ori %r29, %r29, 3855
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	std %r14, 3096(%r8)
	std %r15, 3112(%r8)
	std %r16, 3128(%r8)
	std %r17, 3144(%r8)
	std %r18, 3160(%r8)
	std %r19, 3176(%r8)
	std %r20, 3192(%r8)
	std %r21, 3208(%r8)
	ld %r14, 576(%r8)
	ld %r15, 584(%r8)
	ld %r16, 592(%r8)
	ld %r17, 600(%r8)
	ld %r18, 608(%r8)
	ld %r19, 616(%r8)
	ld %r20, 624(%r8)
	ld %r21, 632(%r8)
	ld %r22, 0(%r4)
	xor %r14, %r14, %r22
	ld %r22, 8(%r4)
	xor %r15, %r15, %r22
	ld %r22, 16(%r4)
	xor %r16, %r16, %r22
	ld %r22, 24(%r4)
	xor %r17, %r17, %r22
	ld %r22, 32(%r4)
	xor %r18, %r18, %r22
	ld %r22, 40(%r4)
	xor %r19, %r19, %r22
	ld %r22, 48(%r4)
	xor %r20, %r20, %r22
	ld %r22, 56(%r4)
	xor %r21, %r21, %r22
	lis %r24, 0
	ori %r24, %r24, 0
	rldicr %r24, %r24, 32, 31
	oris %r24, %r24, 65535
	ori %r24, %r24, 0
	lis %r25, 0
	ori %r25, %r25, 65280
	rldicr %r25, %r25, 32, 31
	oris %r25, %r25, 0
	ori %r25, %r25, 65280
	lis %r27, 21845
	ori %r27, %r27, 21845
	rldicr %r27, %r27, 32, 31
	oris %r27, %r27, 21845
	ori %r27, %r27, 21845
	lis %r28, 13107
	ori %r28, %r28, 13107
	rldicr %r28, %r28, 32, 31
	oris %r28, %r28, 13107
	ori %r28, %r28, 13107
	lis %r29, 3855
	ori %r29, %r29, 3855
	rldicr %r29, %r29, 32, 31
	oris %r29, %r29, 3855
	ori %r29, %r29, 3855
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	std %r14, 3088(%r8)
	std %r15, 3104(%r8)
	std %r16, 3120(%r8)
	std %r17, 3136(%r8)
	std %r18, 3152(%r8)
	std %r19, 3168(%r8)
	std %r20, 3184(%r8)
	std %r21, 3200(%r8)
	rldicl %r22, %r6, 61, 3
	cmpldi %cr0, %r22, 0
	bne %cr0, 213f
	or %r12, %r6, %r6
	b 214f
213:
	li %r12, 8
214:
	addi %r9, %r8, 3088
	or %r10, %r5, %r5
	or %r11, %r12, %r12
215:
	ld %r22, 0(%r9)
	std %r22, 0(%r10)
	ld %r22, 8(%r9)
	std %r22, 8(%r10)
	addi %r9, %r9, 16
	addi %r10, %r10, 16
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 215b
	subf %r6, %r12, %r6
	addi %r5, %r5, 128
	cmpldi %cr0, %r6, 0
	bne %cr0, 25b
	b 24f
23:
24:
	ld %r14, 2944(%r8)
	ld %r15, 2952(%r8)
	ld %r16, 2960(%r8)
	ld %r17, 2968(%r8)
	ld %r18, 2976(%r8)
	ld %r19, 2984(%r8)
	ld %r20, 2992(%r8)
	ld %r21, 3000(%r8)
	ld %r22, 3008(%r8)
	ld %r23, 3016(%r8)
	ld %r24, 3024(%r8)
	ld %r25, 3032(%r8)
	ld %r26, 3040(%r8)
	ld %r27, 3048(%r8)
	ld %r28, 3056(%r8)
	ld %r29, 3064(%r8)
	ld %r30, 3072(%r8)
	ld %r31, 3080(%r8)
	addi %r12, %r1, 32
	li %r0, 0
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	std %r0, 128(%r12)
	std %r0, 136(%r12)
	std %r0, 144(%r12)
	std %r0, 152(%r12)
	std %r0, 160(%r12)
	std %r0, 168(%r12)
	std %r0, 176(%r12)
	std %r0, 184(%r12)
	std %r0, 192(%r12)
	std %r0, 200(%r12)
	std %r0, 208(%r12)
	std %r0, 216(%r12)
	std %r0, 224(%r12)
	std %r0, 232(%r12)
	addi %r1, %r1, 3344
	li %r0, 0
	li %r3, 0
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	blr

vg_camellia_ecb_decrypt:
	stdu %r1, -3344(%r1)
	addi %r7, %r1, 32
	or %r8, %r7, %r7
	std %r14, 2944(%r8)
	std %r15, 2952(%r8)
	std %r16, 2960(%r8)
	std %r17, 2968(%r8)
	std %r18, 2976(%r8)
	std %r19, 2984(%r8)
	std %r20, 2992(%r8)
	std %r21, 3000(%r8)
	std %r22, 3008(%r8)
	std %r23, 3016(%r8)
	std %r24, 3024(%r8)
	std %r25, 3032(%r8)
	std %r26, 3040(%r8)
	std %r27, 3048(%r8)
	std %r28, 3056(%r8)
	std %r29, 3064(%r8)
	std %r30, 3072(%r8)
	std %r31, 3080(%r8)
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
	lis %r22, 255
	ori %r22, %r22, 65280
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 0
	ori %r22, %r22, 0
	std %r22, 400(%r8)
	lis %r22, 0
	ori %r22, %r22, 0
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 255
	ori %r22, %r22, 65280
	std %r22, 408(%r8)
	lis %r22, 0
	ori %r22, %r22, 255
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 65280
	ori %r22, %r22, 0
	std %r22, 416(%r8)
	addi %r22, %r4, -18
	cmpldi %cr0, %r22, 0
	beq %cr0, 20f
	addi %r7, %r8, 2816
	addi %r3, %r3, 256
	li %r23, 30
	b 21f
20:
	addi %r7, %r8, 2304
	addi %r3, %r3, 192
	li %r23, 22
21:
	addi %r4, %r8, 768
	ld %r14, 0(%r3)
	or %r15, %r14, %r14
	or %r16, %r14, %r14
	or %r17, %r14, %r14
	or %r18, %r14, %r14
	or %r19, %r14, %r14
	or %r20, %r14, %r14
	or %r21, %r14, %r14
	lis %r24, 0
	ori %r24, %r24, 0
	rldicr %r24, %r24, 32, 31
	oris %r24, %r24, 65535
	ori %r24, %r24, 0
	lis %r25, 0
	ori %r25, %r25, 65280
	rldicr %r25, %r25, 32, 31
	oris %r25, %r25, 0
	ori %r25, %r25, 65280
	lis %r27, 21845
	ori %r27, %r27, 21845
	rldicr %r27, %r27, 32, 31
	oris %r27, %r27, 21845
	ori %r27, %r27, 21845
	lis %r28, 13107
	ori %r28, %r28, 13107
	rldicr %r28, %r28, 32, 31
	oris %r28, %r28, 13107
	ori %r28, %r28, 13107
	lis %r29, 3855
	ori %r29, %r29, 3855
	rldicr %r29, %r29, 32, 31
	oris %r29, %r29, 3855
	ori %r29, %r29, 3855
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 0(%r4)
	std %r15, 8(%r4)
	std %r16, 16(%r4)
	std %r17, 24(%r4)
	std %r18, 32(%r4)
	std %r19, 40(%r4)
	std %r20, 48(%r4)
	std %r21, 56(%r4)
	addi %r4, %r4, 64
	ld %r14, 8(%r3)
	or %r15, %r14, %r14
	or %r16, %r14, %r14
	or %r17, %r14, %r14
	or %r18, %r14, %r14
	or %r19, %r14, %r14
	or %r20, %r14, %r14
	or %r21, %r14, %r14
	lis %r24, 0
	ori %r24, %r24, 0
	rldicr %r24, %r24, 32, 31
	oris %r24, %r24, 65535
	ori %r24, %r24, 0
	lis %r25, 0
	ori %r25, %r25, 65280
	rldicr %r25, %r25, 32, 31
	oris %r25, %r25, 0
	ori %r25, %r25, 65280
	lis %r27, 21845
	ori %r27, %r27, 21845
	rldicr %r27, %r27, 32, 31
	oris %r27, %r27, 21845
	ori %r27, %r27, 21845
	lis %r28, 13107
	ori %r28, %r28, 13107
	rldicr %r28, %r28, 32, 31
	oris %r28, %r28, 13107
	ori %r28, %r28, 13107
	lis %r29, 3855
	ori %r29, %r29, 3855
	rldicr %r29, %r29, 32, 31
	oris %r29, %r29, 3855
	ori %r29, %r29, 3855
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 0(%r4)
	std %r15, 8(%r4)
	std %r16, 16(%r4)
	std %r17, 24(%r4)
	std %r18, 32(%r4)
	std %r19, 40(%r4)
	std %r20, 48(%r4)
	std %r21, 56(%r4)
	addi %r4, %r4, 64
	addi %r3, %r3, -8
22:
	ld %r14, 0(%r3)
	or %r15, %r14, %r14
	or %r16, %r14, %r14
	or %r17, %r14, %r14
	or %r18, %r14, %r14
	or %r19, %r14, %r14
	or %r20, %r14, %r14
	or %r21, %r14, %r14
	lis %r24, 0
	ori %r24, %r24, 0
	rldicr %r24, %r24, 32, 31
	oris %r24, %r24, 65535
	ori %r24, %r24, 0
	lis %r25, 0
	ori %r25, %r25, 65280
	rldicr %r25, %r25, 32, 31
	oris %r25, %r25, 0
	ori %r25, %r25, 65280
	lis %r27, 21845
	ori %r27, %r27, 21845
	rldicr %r27, %r27, 32, 31
	oris %r27, %r27, 21845
	ori %r27, %r27, 21845
	lis %r28, 13107
	ori %r28, %r28, 13107
	rldicr %r28, %r28, 32, 31
	oris %r28, %r28, 13107
	ori %r28, %r28, 13107
	lis %r29, 3855
	ori %r29, %r29, 3855
	rldicr %r29, %r29, 32, 31
	oris %r29, %r29, 3855
	ori %r29, %r29, 3855
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 0(%r4)
	std %r15, 8(%r4)
	std %r16, 16(%r4)
	std %r17, 24(%r4)
	std %r18, 32(%r4)
	std %r19, 40(%r4)
	std %r20, 48(%r4)
	std %r21, 56(%r4)
	addi %r4, %r4, 64
	addi %r3, %r3, -8
	addi %r23, %r23, -1
	cmpldi %cr0, %r23, 0
	bne %cr0, 22b
	addi %r3, %r3, -8
	ld %r14, 0(%r3)
	or %r15, %r14, %r14
	or %r16, %r14, %r14
	or %r17, %r14, %r14
	or %r18, %r14, %r14
	or %r19, %r14, %r14
	or %r20, %r14, %r14
	or %r21, %r14, %r14
	lis %r24, 0
	ori %r24, %r24, 0
	rldicr %r24, %r24, 32, 31
	oris %r24, %r24, 65535
	ori %r24, %r24, 0
	lis %r25, 0
	ori %r25, %r25, 65280
	rldicr %r25, %r25, 32, 31
	oris %r25, %r25, 0
	ori %r25, %r25, 65280
	lis %r27, 21845
	ori %r27, %r27, 21845
	rldicr %r27, %r27, 32, 31
	oris %r27, %r27, 21845
	ori %r27, %r27, 21845
	lis %r28, 13107
	ori %r28, %r28, 13107
	rldicr %r28, %r28, 32, 31
	oris %r28, %r28, 13107
	ori %r28, %r28, 13107
	lis %r29, 3855
	ori %r29, %r29, 3855
	rldicr %r29, %r29, 32, 31
	oris %r29, %r29, 3855
	ori %r29, %r29, 3855
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 0(%r4)
	std %r15, 8(%r4)
	std %r16, 16(%r4)
	std %r17, 24(%r4)
	std %r18, 32(%r4)
	std %r19, 40(%r4)
	std %r20, 48(%r4)
	std %r21, 56(%r4)
	addi %r4, %r4, 64
	ld %r14, 8(%r3)
	or %r15, %r14, %r14
	or %r16, %r14, %r14
	or %r17, %r14, %r14
	or %r18, %r14, %r14
	or %r19, %r14, %r14
	or %r20, %r14, %r14
	or %r21, %r14, %r14
	lis %r24, 0
	ori %r24, %r24, 0
	rldicr %r24, %r24, 32, 31
	oris %r24, %r24, 65535
	ori %r24, %r24, 0
	lis %r25, 0
	ori %r25, %r25, 65280
	rldicr %r25, %r25, 32, 31
	oris %r25, %r25, 0
	ori %r25, %r25, 65280
	lis %r27, 21845
	ori %r27, %r27, 21845
	rldicr %r27, %r27, 32, 31
	oris %r27, %r27, 21845
	ori %r27, %r27, 21845
	lis %r28, 13107
	ori %r28, %r28, 13107
	rldicr %r28, %r28, 32, 31
	oris %r28, %r28, 13107
	ori %r28, %r28, 13107
	lis %r29, 3855
	ori %r29, %r29, 3855
	rldicr %r29, %r29, 32, 31
	oris %r29, %r29, 3855
	ori %r29, %r29, 3855
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 0(%r4)
	std %r15, 8(%r4)
	std %r16, 16(%r4)
	std %r17, 24(%r4)
	std %r18, 32(%r4)
	std %r19, 40(%r4)
	std %r20, 48(%r4)
	std %r21, 56(%r4)
	addi %r4, %r4, 64
	cmpldi %cr0, %r6, 0
	beq %cr0, 23f
25:
	rldicl %r22, %r6, 61, 3
	cmpldi %cr0, %r22, 0
	bne %cr0, 26f
	or %r12, %r6, %r6
	b 27f
26:
	li %r12, 8
27:
	or %r9, %r5, %r5
	addi %r10, %r8, 3088
	or %r11, %r12, %r12
28:
	ld %r22, 0(%r9)
	std %r22, 0(%r10)
	ld %r22, 8(%r9)
	std %r22, 8(%r10)
	addi %r9, %r9, 16
	addi %r10, %r10, 16
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 28b
	addi %r4, %r8, 768
	ld %r14, 3096(%r8)
	ld %r15, 3112(%r8)
	ld %r16, 3128(%r8)
	ld %r17, 3144(%r8)
	ld %r18, 3160(%r8)
	ld %r19, 3176(%r8)
	ld %r20, 3192(%r8)
	ld %r21, 3208(%r8)
	lis %r24, 0
	ori %r24, %r24, 0
	rldicr %r24, %r24, 32, 31
	oris %r24, %r24, 65535
	ori %r24, %r24, 0
	lis %r25, 0
	ori %r25, %r25, 65280
	rldicr %r25, %r25, 32, 31
	oris %r25, %r25, 0
	ori %r25, %r25, 65280
	lis %r27, 21845
	ori %r27, %r27, 21845
	rldicr %r27, %r27, 32, 31
	oris %r27, %r27, 21845
	ori %r27, %r27, 21845
	lis %r28, 13107
	ori %r28, %r28, 13107
	rldicr %r28, %r28, 32, 31
	oris %r28, %r28, 13107
	ori %r28, %r28, 13107
	lis %r29, 3855
	ori %r29, %r29, 3855
	rldicr %r29, %r29, 32, 31
	oris %r29, %r29, 3855
	ori %r29, %r29, 3855
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	std %r14, 576(%r8)
	std %r15, 584(%r8)
	std %r16, 592(%r8)
	std %r17, 600(%r8)
	std %r18, 608(%r8)
	std %r19, 616(%r8)
	std %r20, 624(%r8)
	std %r21, 632(%r8)
	ld %r14, 3088(%r8)
	ld %r15, 3104(%r8)
	ld %r16, 3120(%r8)
	ld %r17, 3136(%r8)
	ld %r18, 3152(%r8)
	ld %r19, 3168(%r8)
	ld %r20, 3184(%r8)
	ld %r21, 3200(%r8)
	lis %r24, 0
	ori %r24, %r24, 0
	rldicr %r24, %r24, 32, 31
	oris %r24, %r24, 65535
	ori %r24, %r24, 0
	lis %r25, 0
	ori %r25, %r25, 65280
	rldicr %r25, %r25, 32, 31
	oris %r25, %r25, 0
	ori %r25, %r25, 65280
	lis %r27, 21845
	ori %r27, %r27, 21845
	rldicr %r27, %r27, 32, 31
	oris %r27, %r27, 21845
	ori %r27, %r27, 21845
	lis %r28, 13107
	ori %r28, %r28, 13107
	rldicr %r28, %r28, 32, 31
	oris %r28, %r28, 13107
	ori %r28, %r28, 13107
	lis %r29, 3855
	ori %r29, %r29, 3855
	rldicr %r29, %r29, 32, 31
	oris %r29, %r29, 3855
	ori %r29, %r29, 3855
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	ld %r22, 0(%r4)
	xor %r14, %r14, %r22
	ld %r22, 8(%r4)
	xor %r15, %r15, %r22
	ld %r22, 16(%r4)
	xor %r16, %r16, %r22
	ld %r22, 24(%r4)
	xor %r17, %r17, %r22
	ld %r22, 32(%r4)
	xor %r18, %r18, %r22
	ld %r22, 40(%r4)
	xor %r19, %r19, %r22
	ld %r22, 48(%r4)
	xor %r20, %r20, %r22
	ld %r22, 56(%r4)
	xor %r21, %r21, %r22
	std %r14, 512(%r8)
	std %r15, 520(%r8)
	std %r16, 528(%r8)
	std %r17, 536(%r8)
	std %r18, 544(%r8)
	std %r19, 552(%r8)
	std %r20, 560(%r8)
	std %r21, 568(%r8)
	ld %r22, 576(%r8)
	ld %r24, 64(%r4)
	xor %r22, %r22, %r24
	std %r22, 576(%r8)
	ld %r22, 584(%r8)
	ld %r24, 72(%r4)
	xor %r22, %r22, %r24
	std %r22, 584(%r8)
	ld %r22, 592(%r8)
	ld %r24, 80(%r4)
	xor %r22, %r22, %r24
	std %r22, 592(%r8)
	ld %r22, 600(%r8)
	ld %r24, 88(%r4)
	xor %r22, %r22, %r24
	std %r22, 600(%r8)
	ld %r22, 608(%r8)
	ld %r24, 96(%r4)
	xor %r22, %r22, %r24
	std %r22, 608(%r8)
	ld %r22, 616(%r8)
	ld %r24, 104(%r4)
	xor %r22, %r22, %r24
	std %r22, 616(%r8)
	ld %r22, 624(%r8)
	ld %r24, 112(%r4)
	xor %r22, %r22, %r24
	std %r22, 624(%r8)
	ld %r22, 632(%r8)
	ld %r24, 120(%r4)
	xor %r22, %r22, %r24
	std %r22, 632(%r8)
	addi %r4, %r4, 128
29:
	addi %r3, %r4, 384
210:
	ld %r22, 0(%r4)
	xor %r14, %r14, %r22
	ld %r22, 8(%r4)
	xor %r15, %r15, %r22
	ld %r22, 16(%r4)
	xor %r16, %r16, %r22
	ld %r22, 24(%r4)
	xor %r17, %r17, %r22
	ld %r22, 32(%r4)
	xor %r18, %r18, %r22
	ld %r22, 40(%r4)
	xor %r19, %r19, %r22
	ld %r22, 48(%r4)
	xor %r20, %r20, %r22
	ld %r22, 56(%r4)
	xor %r21, %r21, %r22
	ld %r30, 400(%r8)
	or %r23, %r21, %r21
	xor %r22, %r21, %r20
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	xor %r22, %r20, %r19
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	xor %r22, %r19, %r18
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	xor %r22, %r18, %r17
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	xor %r22, %r17, %r16
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	xor %r22, %r16, %r15
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	xor %r22, %r15, %r14
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	xor %r22, %r14, %r23
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	li %r31, 0
	addi %r31, %r31, -1
	xor %r22, %r21, %r15
	xor %r23, %r19, %r17
	xor %r24, %r16, %r22
	xor %r25, %r20, %r14
	xor %r26, %r14, %r23
	xor %r27, %r18, %r15
	xor %r28, %r18, %r24
	xor %r29, %r20, %r23
	xor %r30, %r16, %r25
	xor %r0, %r24, %r25
	xor %r9, %r21, %r20
	std %r30, 0(%r8)
	xor %r30, %r21, %r25
	std %r21, 8(%r8)
	xor %r21, %r30, %r31
	std %r30, 16(%r8)
	xor %r30, %r20, %r17
	std %r21, 24(%r8)
	xor %r21, %r19, %r15
	std %r20, 32(%r8)
	xor %r20, %r19, %r14
	xor %r19, %r19, %r24
	xor %r25, %r18, %r25
	xor %r18, %r18, %r9
	xor %r17, %r17, %r14
	xor %r17, %r17, %r31
	xor %r14, %r16, %r26
	xor %r16, %r16, %r27
	xor %r16, %r16, %r31
	xor %r9, %r15, %r29
	xor %r9, %r9, %r31
	std %r9, 40(%r8)
	xor %r9, %r22, %r26
	xor %r22, %r22, %r29
	xor %r29, %r23, %r27
	std %r9, 48(%r8)
	xor %r9, %r23, %r28
	xor %r23, %r23, %r0
	std %r23, 56(%r8)
	xor %r23, %r24, %r26
	xor %r23, %r23, %r31
	xor %r24, %r24, %r30
	xor %r24, %r24, %r31
	xor %r26, %r26, %r27
	xor %r26, %r26, %r31
	xor %r20, %r28, %r20
	xor %r20, %r20, %r31
	ld %r27, 0(%r8)
	xor %r21, %r27, %r21
	xor %r21, %r21, %r31
	xor %r27, %r27, %r29
	xor %r27, %r27, %r31
	ld %r29, 8(%r8)
	ld %r30, 32(%r8)
	std %r24, 0(%r8)
	xor %r24, %r29, %r30
	xor %r24, %r24, %r31
	xor %r24, %r24, %r30
	xor %r29, %r29, %r15
	xor %r29, %r29, %r31
	and %r15, %r16, %r18
	and %r30, %r24, %r21
	xor %r30, %r30, %r15
	std %r31, 8(%r8)
	and %r31, %r28, %r20
	xor %r31, %r31, %r15
	and %r15, %r14, %r23
	std %r14, 32(%r8)
	and %r14, %r22, %r19
	xor %r14, %r14, %r15
	std %r22, 64(%r8)
	and %r22, %r0, %r17
	xor %r22, %r22, %r15
	and %r15, %r25, %r9
	std %r25, 72(%r8)
	and %r25, %r26, %r27
	xor %r25, %r25, %r15
	std %r26, 80(%r8)
	ld %r26, 40(%r8)
	std %r0, 88(%r8)
	ld %r0, 24(%r8)
	std %r28, 96(%r8)
	and %r28, %r26, %r0
	xor %r28, %r28, %r15
	xor %r30, %r30, %r25
	xor %r31, %r31, %r28
	xor %r14, %r14, %r25
	xor %r22, %r22, %r28
	ld %r28, 56(%r8)
	xor %r30, %r30, %r28
	ld %r28, 48(%r8)
	xor %r31, %r31, %r28
	xor %r14, %r14, %r29
	ld %r29, 0(%r8)
	xor %r22, %r22, %r29
	xor %r29, %r30, %r31
	and %r30, %r30, %r14
	xor %r28, %r22, %r30
	and %r25, %r29, %r28
	xor %r25, %r25, %r31
	xor %r15, %r14, %r22
	xor %r31, %r31, %r30
	and %r31, %r31, %r15
	xor %r31, %r31, %r22
	xor %r14, %r14, %r31
	xor %r15, %r28, %r31
	and %r22, %r22, %r15
	xor %r14, %r22, %r14
	xor %r28, %r28, %r22
	and %r28, %r25, %r28
	xor %r29, %r29, %r28
	xor %r28, %r29, %r14
	xor %r22, %r25, %r31
	xor %r15, %r25, %r29
	xor %r30, %r31, %r14
	xor %r26, %r22, %r28
	and %r18, %r30, %r18
	and %r21, %r14, %r21
	and %r20, %r31, %r20
	and %r23, %r15, %r23
	and %r19, %r29, %r19
	and %r17, %r25, %r17
	and %r9, %r22, %r9
	and %r27, %r26, %r27
	and %r0, %r28, %r0
	and %r30, %r30, %r16
	and %r14, %r14, %r24
	ld %r24, 96(%r8)
	and %r31, %r31, %r24
	ld %r24, 32(%r8)
	and %r15, %r15, %r24
	ld %r24, 64(%r8)
	and %r29, %r29, %r24
	ld %r24, 88(%r8)
	and %r25, %r25, %r24
	ld %r24, 72(%r8)
	and %r22, %r22, %r24
	ld %r24, 80(%r8)
	and %r26, %r26, %r24
	ld %r24, 40(%r8)
	and %r28, %r28, %r24
	xor %r27, %r21, %r27
	xor %r23, %r23, %r17
	xor %r24, %r9, %r0
	xor %r16, %r18, %r26
	xor %r31, %r31, %r27
	std %r27, 40(%r8)
	xor %r27, %r15, %r23
	std %r23, 80(%r8)
	xor %r23, %r22, %r24
	xor %r25, %r20, %r25
	xor %r9, %r9, %r28
	xor %r0, %r0, %r30
	xor %r30, %r30, %r14
	xor %r29, %r29, %r27
	xor %r26, %r26, %r23
	std %r26, 72(%r8)
	xor %r26, %r16, %r31
	xor %r18, %r18, %r20
	xor %r21, %r21, %r19
	xor %r17, %r17, %r16
	xor %r14, %r14, %r9
	xor %r15, %r15, %r31
	ld %r31, 40(%r8)
	xor %r22, %r22, %r31
	xor %r28, %r28, %r0
	ld %r31, 80(%r8)
	xor %r31, %r31, %r30
	xor %r18, %r24, %r18
	xor %r27, %r27, %r25
	xor %r23, %r23, %r30
	xor %r25, %r25, %r0
	xor %r9, %r9, %r22
	ld %r22, 72(%r8)
	xor %r0, %r29, %r22
	xor %r29, %r29, %r26
	xor %r22, %r22, %r31
	ld %r31, 8(%r8)
	xor %r19, %r22, %r31
	xor %r26, %r26, %r14
	xor %r16, %r26, %r31
	xor %r21, %r21, %r17
	xor %r15, %r15, %r25
	xor %r17, %r15, %r31
	xor %r28, %r28, %r29
	xor %r15, %r28, %r31
	xor %r27, %r27, %r9
	xor %r23, %r23, %r21
	xor %r20, %r23, %r31
	or %r21, %r27, %r27
	or %r14, %r0, %r0
	ld %r30, 408(%r8)
	or %r23, %r21, %r21
	xor %r22, %r21, %r20
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	xor %r22, %r20, %r19
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	xor %r22, %r19, %r18
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	xor %r22, %r18, %r17
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	xor %r22, %r17, %r16
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	xor %r22, %r16, %r15
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	xor %r22, %r15, %r14
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	xor %r22, %r14, %r23
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	ld %r30, 416(%r8)
	or %r23, %r14, %r14
	xor %r22, %r14, %r15
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	xor %r22, %r15, %r16
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	xor %r22, %r16, %r17
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	xor %r22, %r17, %r18
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	xor %r22, %r18, %r19
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	xor %r22, %r19, %r20
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	xor %r22, %r20, %r21
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	xor %r22, %r21, %r23
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	ld %r30, 384(%r8)
	ld %r24, 392(%r8)
	rldicl %r22, %r14, 56, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 24, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 56, 0
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 24, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 24, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 56, 0
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 24, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 24, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 56, 0
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 24, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 24, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 56, 0
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 24, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 24, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 56, 0
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 24, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 24, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 56, 0
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 24, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 24, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 56, 0
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 24, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 24, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 8, 0
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 56, 0
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 24, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	ld %r22, 576(%r8)
	xor %r14, %r14, %r22
	std %r14, 576(%r8)
	ld %r22, 584(%r8)
	xor %r15, %r15, %r22
	std %r15, 584(%r8)
	ld %r22, 592(%r8)
	xor %r16, %r16, %r22
	std %r16, 592(%r8)
	ld %r22, 600(%r8)
	xor %r17, %r17, %r22
	std %r17, 600(%r8)
	ld %r22, 608(%r8)
	xor %r18, %r18, %r22
	std %r18, 608(%r8)
	ld %r22, 616(%r8)
	xor %r19, %r19, %r22
	std %r19, 616(%r8)
	ld %r22, 624(%r8)
	xor %r20, %r20, %r22
	std %r20, 624(%r8)
	ld %r22, 632(%r8)
	xor %r21, %r21, %r22
	std %r21, 632(%r8)
	ld %r22, 64(%r4)
	xor %r14, %r14, %r22
	ld %r22, 72(%r4)
	xor %r15, %r15, %r22
	ld %r22, 80(%r4)
	xor %r16, %r16, %r22
	ld %r22, 88(%r4)
	xor %r17, %r17, %r22
	ld %r22, 96(%r4)
	xor %r18, %r18, %r22
	ld %r22, 104(%r4)
	xor %r19, %r19, %r22
	ld %r22, 112(%r4)
	xor %r20, %r20, %r22
	ld %r22, 120(%r4)
	xor %r21, %r21, %r22
	ld %r30, 400(%r8)
	or %r23, %r21, %r21
	xor %r22, %r21, %r20
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	xor %r22, %r20, %r19
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	xor %r22, %r19, %r18
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	xor %r22, %r18, %r17
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	xor %r22, %r17, %r16
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	xor %r22, %r16, %r15
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	xor %r22, %r15, %r14
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	xor %r22, %r14, %r23
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	li %r31, 0
	addi %r31, %r31, -1
	xor %r22, %r21, %r15
	xor %r23, %r19, %r17
	xor %r24, %r16, %r22
	xor %r25, %r20, %r14
	xor %r26, %r14, %r23
	xor %r27, %r18, %r15
	xor %r28, %r18, %r24
	xor %r29, %r20, %r23
	xor %r30, %r16, %r25
	xor %r0, %r24, %r25
	xor %r9, %r21, %r20
	std %r30, 0(%r8)
	xor %r30, %r21, %r25
	std %r21, 8(%r8)
	xor %r21, %r30, %r31
	std %r30, 16(%r8)
	xor %r30, %r20, %r17
	std %r21, 24(%r8)
	xor %r21, %r19, %r15
	std %r20, 32(%r8)
	xor %r20, %r19, %r14
	xor %r19, %r19, %r24
	xor %r25, %r18, %r25
	xor %r18, %r18, %r9
	xor %r17, %r17, %r14
	xor %r17, %r17, %r31
	xor %r14, %r16, %r26
	xor %r16, %r16, %r27
	xor %r16, %r16, %r31
	xor %r9, %r15, %r29
	xor %r9, %r9, %r31
	std %r9, 40(%r8)
	xor %r9, %r22, %r26
	xor %r22, %r22, %r29
	xor %r29, %r23, %r27
	std %r9, 48(%r8)
	xor %r9, %r23, %r28
	xor %r23, %r23, %r0
	std %r23, 56(%r8)
	xor %r23, %r24, %r26
	xor %r23, %r23, %r31
	xor %r24, %r24, %r30
	xor %r24, %r24, %r31
	xor %r26, %r26, %r27
	xor %r26, %r26, %r31
	xor %r20, %r28, %r20
	xor %r20, %r20, %r31
	ld %r27, 0(%r8)
	xor %r21, %r27, %r21
	xor %r21, %r21, %r31
	xor %r27, %r27, %r29
	xor %r27, %r27, %r31
	ld %r29, 8(%r8)
	ld %r30, 32(%r8)
	std %r24, 0(%r8)
	xor %r24, %r29, %r30
	xor %r24, %r24, %r31
	xor %r24, %r24, %r30
	xor %r29, %r29, %r15
	xor %r29, %r29, %r31
	and %r15, %r16, %r18
	and %r30, %r24, %r21
	xor %r30, %r30, %r15
	std %r31, 8(%r8)
	and %r31, %r28, %r20
	xor %r31, %r31, %r15
	and %r15, %r14, %r23
	std %r14, 32(%r8)
	and %r14, %r22, %r19
	xor %r14, %r14, %r15
	std %r22, 64(%r8)
	and %r22, %r0, %r17
	xor %r22, %r22, %r15
	and %r15, %r25, %r9
	std %r25, 72(%r8)
	and %r25, %r26, %r27
	xor %r25, %r25, %r15
	std %r26, 80(%r8)
	ld %r26, 40(%r8)
	std %r0, 88(%r8)
	ld %r0, 24(%r8)
	std %r28, 96(%r8)
	and %r28, %r26, %r0
	xor %r28, %r28, %r15
	xor %r30, %r30, %r25
	xor %r31, %r31, %r28
	xor %r14, %r14, %r25
	xor %r22, %r22, %r28
	ld %r28, 56(%r8)
	xor %r30, %r30, %r28
	ld %r28, 48(%r8)
	xor %r31, %r31, %r28
	xor %r14, %r14, %r29
	ld %r29, 0(%r8)
	xor %r22, %r22, %r29
	xor %r29, %r30, %r31
	and %r30, %r30, %r14
	xor %r28, %r22, %r30
	and %r25, %r29, %r28
	xor %r25, %r25, %r31
	xor %r15, %r14, %r22
	xor %r31, %r31, %r30
	and %r31, %r31, %r15
	xor %r31, %r31, %r22
	xor %r14, %r14, %r31
	xor %r15, %r28, %r31
	and %r22, %r22, %r15
	xor %r14, %r22, %r14
	xor %r28, %r28, %r22
	and %r28, %r25, %r28
	xor %r29, %r29, %r28
	xor %r28, %r29, %r14
	xor %r22, %r25, %r31
	xor %r15, %r25, %r29
	xor %r30, %r31, %r14
	xor %r26, %r22, %r28
	and %r18, %r30, %r18
	and %r21, %r14, %r21
	and %r20, %r31, %r20
	and %r23, %r15, %r23
	and %r19, %r29, %r19
	and %r17, %r25, %r17
	and %r9, %r22, %r9
	and %r27, %r26, %r27
	and %r0, %r28, %r0
	and %r30, %r30, %r16
	and %r14, %r14, %r24
	ld %r24, 96(%r8)
	and %r31, %r31, %r24
	ld %r24, 32(%r8)
	and %r15, %r15, %r24
	ld %r24, 64(%r8)
	and %r29, %r29, %r24
	ld %r24, 88(%r8)
	and %r25, %r25, %r24
	ld %r24, 72(%r8)
	and %r22, %r22, %r24
	ld %r24, 80(%r8)
	and %r26, %r26, %r24
	ld %r24, 40(%r8)
	and %r28, %r28, %r24
	xor %r27, %r21, %r27
	xor %r23, %r23, %r17
	xor %r24, %r9, %r0
	xor %r16, %r18, %r26
	xor %r31, %r31, %r27
	std %r27, 40(%r8)
	xor %r27, %r15, %r23
	std %r23, 80(%r8)
	xor %r23, %r22, %r24
	xor %r25, %r20, %r25
	xor %r9, %r9, %r28
	xor %r0, %r0, %r30
	xor %r30, %r30, %r14
	xor %r29, %r29, %r27
	xor %r26, %r26, %r23
	std %r26, 72(%r8)
	xor %r26, %r16, %r31
	xor %r18, %r18, %r20
	xor %r21, %r21, %r19
	xor %r17, %r17, %r16
	xor %r14, %r14, %r9
	xor %r15, %r15, %r31
	ld %r31, 40(%r8)
	xor %r22, %r22, %r31
	xor %r28, %r28, %r0
	ld %r31, 80(%r8)
	xor %r31, %r31, %r30
	xor %r18, %r24, %r18
	xor %r27, %r27, %r25
	xor %r23, %r23, %r30
	xor %r25, %r25, %r0
	xor %r9, %r9, %r22
	ld %r22, 72(%r8)
	xor %r0, %r29, %r22
	xor %r29, %r29, %r26
	xor %r22, %r22, %r31
	ld %r31, 8(%r8)
	xor %r19, %r22, %r31
	xor %r26, %r26, %r14
	xor %r16, %r26, %r31
	xor %r21, %r21, %r17
	xor %r15, %r15, %r25
	xor %r17, %r15, %r31
	xor %r28, %r28, %r29
	xor %r15, %r28, %r31
	xor %r27, %r27, %r9
	xor %r23, %r23, %r21
	xor %r20, %r23, %r31
	or %r21, %r27, %r27
	or %r14, %r0, %r0
	ld %r30, 408(%r8)
	or %r23, %r21, %r21
	xor %r22, %r21, %r20
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	xor %r22, %r20, %r19
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	xor %r22, %r19, %r18
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	xor %r22, %r18, %r17
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	xor %r22, %r17, %r16
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	xor %r22, %r16, %r15
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	xor %r22, %r15, %r14
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	xor %r22, %r14, %r23
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	ld %r30, 416(%r8)
	or %r23, %r14, %r14
	xor %r22, %r14, %r15
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	xor %r22, %r15, %r16
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	xor %r22, %r16, %r17
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	xor %r22, %r17, %r18
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	xor %r22, %r18, %r19
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	xor %r22, %r19, %r20
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	xor %r22, %r20, %r21
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	xor %r22, %r21, %r23
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	ld %r30, 384(%r8)
	ld %r24, 392(%r8)
	rldicl %r22, %r14, 56, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 24, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 8, 0
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 56, 0
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r14, 24, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 24, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 8, 0
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 56, 0
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r15, 24, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 24, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 8, 0
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 56, 0
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r16, 24, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 24, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 8, 0
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 56, 0
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r17, 24, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 24, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 8, 0
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 56, 0
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r18, 24, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 24, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 8, 0
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 56, 0
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r19, 24, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 24, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 8, 0
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 56, 0
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r20, 24, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 24, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 8, 0
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 56, 0
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r21, 24, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	ld %r22, 512(%r8)
	xor %r14, %r14, %r22
	std %r14, 512(%r8)
	ld %r22, 520(%r8)
	xor %r15, %r15, %r22
	std %r15, 520(%r8)
	ld %r22, 528(%r8)
	xor %r16, %r16, %r22
	std %r16, 528(%r8)
	ld %r22, 536(%r8)
	xor %r17, %r17, %r22
	std %r17, 536(%r8)
	ld %r22, 544(%r8)
	xor %r18, %r18, %r22
	std %r18, 544(%r8)
	ld %r22, 552(%r8)
	xor %r19, %r19, %r22
	std %r19, 552(%r8)
	ld %r22, 560(%r8)
	xor %r20, %r20, %r22
	std %r20, 560(%r8)
	ld %r22, 568(%r8)
	xor %r21, %r21, %r22
	std %r21, 568(%r8)
	addi %r4, %r4, 128
	subf %r22, %r3, %r4
	cmpldi %cr0, %r22, 0
	bne %cr0, 210b
	subf %r22, %r7, %r4
	cmpldi %cr0, %r22, 0
	bne %cr0, 211f
	b 212f
211:
	ld %r14, 576(%r8)
	ld %r15, 584(%r8)
	ld %r16, 592(%r8)
	ld %r17, 600(%r8)
	ld %r18, 608(%r8)
	ld %r19, 616(%r8)
	ld %r20, 624(%r8)
	ld %r21, 632(%r8)
	ld %r30, 384(%r8)
	ld %r24, 120(%r4)
	or %r22, %r21, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	ld %r24, 112(%r4)
	or %r22, %r20, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	ld %r24, 104(%r4)
	or %r22, %r19, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	ld %r24, 96(%r4)
	or %r22, %r18, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	ld %r24, 88(%r4)
	or %r22, %r17, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	ld %r24, 80(%r4)
	or %r22, %r16, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	ld %r24, 72(%r4)
	or %r22, %r15, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	ld %r24, 64(%r4)
	or %r22, %r14, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	ld %r30, 392(%r8)
	or %r23, %r21, %r21
	ld %r24, 112(%r4)
	and %r22, %r20, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	ld %r24, 104(%r4)
	and %r22, %r19, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	ld %r24, 96(%r4)
	and %r22, %r18, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	ld %r24, 88(%r4)
	and %r22, %r17, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	ld %r24, 80(%r4)
	and %r22, %r16, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	ld %r24, 72(%r4)
	and %r22, %r15, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	ld %r24, 64(%r4)
	and %r22, %r14, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	ld %r24, 120(%r4)
	and %r22, %r23, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	std %r14, 576(%r8)
	std %r15, 584(%r8)
	std %r16, 592(%r8)
	std %r17, 600(%r8)
	std %r18, 608(%r8)
	std %r19, 616(%r8)
	std %r20, 624(%r8)
	std %r21, 632(%r8)
	ld %r14, 512(%r8)
	ld %r15, 520(%r8)
	ld %r16, 528(%r8)
	ld %r17, 536(%r8)
	ld %r18, 544(%r8)
	ld %r19, 552(%r8)
	ld %r20, 560(%r8)
	ld %r21, 568(%r8)
	ld %r30, 392(%r8)
	or %r23, %r21, %r21
	ld %r24, 48(%r4)
	and %r22, %r20, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	ld %r24, 40(%r4)
	and %r22, %r19, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	ld %r24, 32(%r4)
	and %r22, %r18, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	ld %r24, 24(%r4)
	and %r22, %r17, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	ld %r24, 16(%r4)
	and %r22, %r16, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	ld %r24, 8(%r4)
	and %r22, %r15, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	ld %r24, 0(%r4)
	and %r22, %r14, %r24
	rldicl %r22, %r22, 8, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	ld %r24, 56(%r4)
	and %r22, %r23, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	ld %r30, 384(%r8)
	ld %r24, 56(%r4)
	or %r22, %r21, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r21, %r21, %r22
	ld %r24, 48(%r4)
	or %r22, %r20, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r20, %r20, %r22
	ld %r24, 40(%r4)
	or %r22, %r19, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r19, %r19, %r22
	ld %r24, 32(%r4)
	or %r22, %r18, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r18, %r18, %r22
	ld %r24, 24(%r4)
	or %r22, %r17, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r17, %r17, %r22
	ld %r24, 16(%r4)
	or %r22, %r16, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r16, %r16, %r22
	ld %r24, 8(%r4)
	or %r22, %r15, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r15, %r15, %r22
	ld %r24, 0(%r4)
	or %r22, %r14, %r24
	rldicl %r22, %r22, 56, 0
	and %r22, %r22, %r30
	xor %r14, %r14, %r22
	std %r14, 512(%r8)
	std %r15, 520(%r8)
	std %r16, 528(%r8)
	std %r17, 536(%r8)
	std %r18, 544(%r8)
	std %r19, 552(%r8)
	std %r20, 560(%r8)
	std %r21, 568(%r8)
	addi %r4, %r4, 128
212:
	subf %r22, %r7, %r4
	cmpldi %cr0, %r22, 0
	bne %cr0, 29b
	ld %r22, 64(%r4)
	xor %r14, %r14, %r22
	ld %r22, 72(%r4)
	xor %r15, %r15, %r22
	ld %r22, 80(%r4)
	xor %r16, %r16, %r22
	ld %r22, 88(%r4)
	xor %r17, %r17, %r22
	ld %r22, 96(%r4)
	xor %r18, %r18, %r22
	ld %r22, 104(%r4)
	xor %r19, %r19, %r22
	ld %r22, 112(%r4)
	xor %r20, %r20, %r22
	ld %r22, 120(%r4)
	xor %r21, %r21, %r22
	lis %r24, 0
	ori %r24, %r24, 0
	rldicr %r24, %r24, 32, 31
	oris %r24, %r24, 65535
	ori %r24, %r24, 0
	lis %r25, 0
	ori %r25, %r25, 65280
	rldicr %r25, %r25, 32, 31
	oris %r25, %r25, 0
	ori %r25, %r25, 65280
	lis %r27, 21845
	ori %r27, %r27, 21845
	rldicr %r27, %r27, 32, 31
	oris %r27, %r27, 21845
	ori %r27, %r27, 21845
	lis %r28, 13107
	ori %r28, %r28, 13107
	rldicr %r28, %r28, 32, 31
	oris %r28, %r28, 13107
	ori %r28, %r28, 13107
	lis %r29, 3855
	ori %r29, %r29, 3855
	rldicr %r29, %r29, 32, 31
	oris %r29, %r29, 3855
	ori %r29, %r29, 3855
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	std %r14, 3096(%r8)
	std %r15, 3112(%r8)
	std %r16, 3128(%r8)
	std %r17, 3144(%r8)
	std %r18, 3160(%r8)
	std %r19, 3176(%r8)
	std %r20, 3192(%r8)
	std %r21, 3208(%r8)
	ld %r14, 576(%r8)
	ld %r15, 584(%r8)
	ld %r16, 592(%r8)
	ld %r17, 600(%r8)
	ld %r18, 608(%r8)
	ld %r19, 616(%r8)
	ld %r20, 624(%r8)
	ld %r21, 632(%r8)
	ld %r22, 0(%r4)
	xor %r14, %r14, %r22
	ld %r22, 8(%r4)
	xor %r15, %r15, %r22
	ld %r22, 16(%r4)
	xor %r16, %r16, %r22
	ld %r22, 24(%r4)
	xor %r17, %r17, %r22
	ld %r22, 32(%r4)
	xor %r18, %r18, %r22
	ld %r22, 40(%r4)
	xor %r19, %r19, %r22
	ld %r22, 48(%r4)
	xor %r20, %r20, %r22
	ld %r22, 56(%r4)
	xor %r21, %r21, %r22
	lis %r24, 0
	ori %r24, %r24, 0
	rldicr %r24, %r24, 32, 31
	oris %r24, %r24, 65535
	ori %r24, %r24, 0
	lis %r25, 0
	ori %r25, %r25, 65280
	rldicr %r25, %r25, 32, 31
	oris %r25, %r25, 0
	ori %r25, %r25, 65280
	lis %r27, 21845
	ori %r27, %r27, 21845
	rldicr %r27, %r27, 32, 31
	oris %r27, %r27, 21845
	ori %r27, %r27, 21845
	lis %r28, 13107
	ori %r28, %r28, 13107
	rldicr %r28, %r28, 32, 31
	oris %r28, %r28, 13107
	ori %r28, %r28, 13107
	lis %r29, 3855
	ori %r29, %r29, 3855
	rldicr %r29, %r29, 32, 31
	oris %r29, %r29, 3855
	ori %r29, %r29, 3855
	rldicl %r22, %r14, 63, 1
	xor %r22, %r22, %r15
	and %r22, %r22, %r27
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 1, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r16, 63, 1
	xor %r22, %r22, %r17
	and %r22, %r22, %r27
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 1, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r18, 63, 1
	xor %r22, %r22, %r19
	and %r22, %r22, %r27
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 1, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r20, 63, 1
	xor %r22, %r22, %r21
	and %r22, %r22, %r27
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 1, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r14, 62, 2
	xor %r22, %r22, %r16
	and %r22, %r22, %r28
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 2, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 62, 2
	xor %r22, %r22, %r17
	and %r22, %r22, %r28
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 2, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r18, 62, 2
	xor %r22, %r22, %r20
	and %r22, %r22, %r28
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 2, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 62, 2
	xor %r22, %r22, %r21
	and %r22, %r22, %r28
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 2, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r14, 60, 4
	xor %r22, %r22, %r18
	and %r22, %r22, %r29
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 4, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 60, 4
	xor %r22, %r22, %r19
	and %r22, %r22, %r29
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 4, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 60, 4
	xor %r22, %r22, %r20
	and %r22, %r22, %r29
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 4, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 60, 4
	xor %r22, %r22, %r21
	and %r22, %r22, %r29
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 4, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r14, 56, 8
	xor %r22, %r22, %r14
	and %r22, %r22, %r25
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 8, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 56, 8
	xor %r22, %r22, %r15
	and %r22, %r22, %r25
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 8, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 56, 8
	xor %r22, %r22, %r16
	and %r22, %r22, %r25
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 8, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 56, 8
	xor %r22, %r22, %r17
	and %r22, %r22, %r25
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 8, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 56, 8
	xor %r22, %r22, %r18
	and %r22, %r22, %r25
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 8, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 56, 8
	xor %r22, %r22, %r19
	and %r22, %r22, %r25
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 8, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 56, 8
	xor %r22, %r22, %r20
	and %r22, %r22, %r25
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 8, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 56, 8
	xor %r22, %r22, %r21
	and %r22, %r22, %r25
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 8, 0
	xor %r21, %r21, %r22
	rldicl %r22, %r14, 48, 16
	xor %r22, %r22, %r14
	and %r22, %r22, %r24
	xor %r14, %r14, %r22
	rldicl %r22, %r22, 16, 0
	xor %r14, %r14, %r22
	rldicl %r22, %r15, 48, 16
	xor %r22, %r22, %r15
	and %r22, %r22, %r24
	xor %r15, %r15, %r22
	rldicl %r22, %r22, 16, 0
	xor %r15, %r15, %r22
	rldicl %r22, %r16, 48, 16
	xor %r22, %r22, %r16
	and %r22, %r22, %r24
	xor %r16, %r16, %r22
	rldicl %r22, %r22, 16, 0
	xor %r16, %r16, %r22
	rldicl %r22, %r17, 48, 16
	xor %r22, %r22, %r17
	and %r22, %r22, %r24
	xor %r17, %r17, %r22
	rldicl %r22, %r22, 16, 0
	xor %r17, %r17, %r22
	rldicl %r22, %r18, 48, 16
	xor %r22, %r22, %r18
	and %r22, %r22, %r24
	xor %r18, %r18, %r22
	rldicl %r22, %r22, 16, 0
	xor %r18, %r18, %r22
	rldicl %r22, %r19, 48, 16
	xor %r22, %r22, %r19
	and %r22, %r22, %r24
	xor %r19, %r19, %r22
	rldicl %r22, %r22, 16, 0
	xor %r19, %r19, %r22
	rldicl %r22, %r20, 48, 16
	xor %r22, %r22, %r20
	and %r22, %r22, %r24
	xor %r20, %r20, %r22
	rldicl %r22, %r22, 16, 0
	xor %r20, %r20, %r22
	rldicl %r22, %r21, 48, 16
	xor %r22, %r22, %r21
	and %r22, %r22, %r24
	xor %r21, %r21, %r22
	rldicl %r22, %r22, 16, 0
	xor %r21, %r21, %r22
	std %r14, 3088(%r8)
	std %r15, 3104(%r8)
	std %r16, 3120(%r8)
	std %r17, 3136(%r8)
	std %r18, 3152(%r8)
	std %r19, 3168(%r8)
	std %r20, 3184(%r8)
	std %r21, 3200(%r8)
	rldicl %r22, %r6, 61, 3
	cmpldi %cr0, %r22, 0
	bne %cr0, 213f
	or %r12, %r6, %r6
	b 214f
213:
	li %r12, 8
214:
	addi %r9, %r8, 3088
	or %r10, %r5, %r5
	or %r11, %r12, %r12
215:
	ld %r22, 0(%r9)
	std %r22, 0(%r10)
	ld %r22, 8(%r9)
	std %r22, 8(%r10)
	addi %r9, %r9, 16
	addi %r10, %r10, 16
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 215b
	subf %r6, %r12, %r6
	addi %r5, %r5, 128
	cmpldi %cr0, %r6, 0
	bne %cr0, 25b
	b 24f
23:
24:
	ld %r14, 2944(%r8)
	ld %r15, 2952(%r8)
	ld %r16, 2960(%r8)
	ld %r17, 2968(%r8)
	ld %r18, 2976(%r8)
	ld %r19, 2984(%r8)
	ld %r20, 2992(%r8)
	ld %r21, 3000(%r8)
	ld %r22, 3008(%r8)
	ld %r23, 3016(%r8)
	ld %r24, 3024(%r8)
	ld %r25, 3032(%r8)
	ld %r26, 3040(%r8)
	ld %r27, 3048(%r8)
	ld %r28, 3056(%r8)
	ld %r29, 3064(%r8)
	ld %r30, 3072(%r8)
	ld %r31, 3080(%r8)
	addi %r12, %r1, 32
	li %r0, 0
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	std %r0, 128(%r12)
	std %r0, 136(%r12)
	std %r0, 144(%r12)
	std %r0, 152(%r12)
	std %r0, 160(%r12)
	std %r0, 168(%r12)
	std %r0, 176(%r12)
	std %r0, 184(%r12)
	std %r0, 192(%r12)
	std %r0, 200(%r12)
	std %r0, 208(%r12)
	std %r0, 216(%r12)
	std %r0, 224(%r12)
	std %r0, 232(%r12)
	addi %r1, %r1, 3344
	li %r0, 0
	li %r3, 0
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	blr
