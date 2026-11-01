// The functions of `src/camellia_ofb.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_ofb:
	stdu %r1, -3408(%r1)
	addi %r8, %r1, 32
	std %r28, 3360(%r8)
	or %r28, %r4, %r4
	or %r4, %r5, %r5
	or %r5, %r6, %r6
	or %r6, %r7, %r7
	or %r7, %r8, %r8
	mflr %r0
	std %r0, 3336(%r7)
	std %r29, 3312(%r7)
	std %r30, 3320(%r7)
	std %r31, 3328(%r7)
	or %r29, %r4, %r4
	or %r30, %r6, %r6
	or %r31, %r4, %r4
	or %r6, %r5, %r5
	or %r5, %r7, %r7
	lwz %r8, 0(%r31)
	stw %r8, 3344(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 3348(%r5)
	lwz %r8, 8(%r31)
	stw %r8, 3352(%r5)
	lwz %r8, 12(%r31)
	stw %r8, 3356(%r5)
	or %r31, %r6, %r6
	or %r6, %r5, %r5
	or %r4, %r28, %r28
	li %r5, 0
	or %r9, %r29, %r29
	or %r10, %r30, %r30
	or %r11, %r31, %r31
	or %r12, %r3, %r3
	or %r0, %r28, %r28
	or %r8, %r6, %r6
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
	cmpldi %cr0, %r5, 0
	beq %cr0, 20f
	cmpldi %cr0, %r22, 0
	beq %cr0, 22f
	addi %r7, %r8, 2816
	addi %r3, %r3, 256
	li %r23, 30
	b 23f
22:
	addi %r7, %r8, 2304
	addi %r3, %r3, 192
	li %r23, 22
23:
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
24:
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
	bne %cr0, 24b
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
	b 21f
20:
	cmpldi %cr0, %r22, 0
	beq %cr0, 25f
	addi %r7, %r8, 2816
	li %r23, 34
	b 26f
25:
	addi %r7, %r8, 2304
	li %r23, 26
26:
	addi %r4, %r8, 768
27:
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
	bne %cr0, 27b
21:
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
	or %r5, %r6, %r6
	or %r3, %r12, %r12
	or %r28, %r0, %r0
	or %r29, %r9, %r9
	or %r30, %r10, %r10
	or %r31, %r11, %r11
	cmpldi %cr0, %r30, 0
	beq %cr0, 28f
210:
	lwz %r8, 3344(%r5)
	stw %r8, 3088(%r5)
	lwz %r8, 3348(%r5)
	stw %r8, 3092(%r5)
	lwz %r8, 3352(%r5)
	stw %r8, 3096(%r5)
	lwz %r8, 3356(%r5)
	stw %r8, 3100(%r5)
	or %r10, %r3, %r3
	or %r6, %r5, %r5
	or %r3, %r28, %r28
	or %r4, %r5, %r5
	li %r5, 414
	bl {vg_camellia_crypt_prepared}
	or %r5, %r6, %r6
	or %r3, %r10, %r10
	lwz %r8, 3088(%r5)
	stw %r8, 3344(%r5)
	lwz %r8, 3092(%r5)
	stw %r8, 3348(%r5)
	lwz %r8, 3096(%r5)
	stw %r8, 3352(%r5)
	lwz %r8, 3100(%r5)
	stw %r8, 3356(%r5)
	lwz %r8, 0(%r31)
	lwz %r9, 3088(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 3092(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 3096(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 3100(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 210b
	b 29f
28:
29:
	or %r31, %r29, %r29
	lwz %r8, 3344(%r5)
	stw %r8, 0(%r31)
	lwz %r8, 3348(%r5)
	stw %r8, 4(%r31)
	lwz %r8, 3352(%r5)
	stw %r8, 8(%r31)
	lwz %r8, 3356(%r5)
	stw %r8, 12(%r31)
	ld %r29, 3312(%r5)
	ld %r30, 3320(%r5)
	ld %r31, 3328(%r5)
	ld %r0, 3336(%r5)
	mtlr %r0
	ld %r28, 3360(%r5)
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
	std %r11, 96(%r12)
	std %r11, 104(%r12)
	std %r11, 112(%r12)
	std %r11, 120(%r12)
	std %r11, 128(%r12)
	std %r11, 136(%r12)
	std %r11, 144(%r12)
	std %r11, 152(%r12)
	std %r11, 160(%r12)
	std %r11, 168(%r12)
	std %r11, 176(%r12)
	std %r11, 184(%r12)
	std %r11, 192(%r12)
	std %r11, 200(%r12)
	std %r11, 208(%r12)
	std %r11, 216(%r12)
	std %r11, 224(%r12)
	std %r11, 232(%r12)
	std %r11, 240(%r12)
	std %r11, 248(%r12)
	std %r11, 256(%r12)
	std %r11, 264(%r12)
	std %r11, 272(%r12)
	std %r11, 280(%r12)
	std %r11, 288(%r12)
	std %r11, 296(%r12)
	std %r11, 304(%r12)
	std %r11, 312(%r12)
	std %r11, 320(%r12)
	std %r11, 328(%r12)
	std %r11, 336(%r12)
	std %r11, 344(%r12)
	std %r11, 352(%r12)
	std %r11, 360(%r12)
	std %r11, 368(%r12)
	std %r11, 376(%r12)
	std %r11, 384(%r12)
	std %r11, 392(%r12)
	std %r11, 400(%r12)
	std %r11, 408(%r12)
	std %r11, 416(%r12)
	std %r11, 424(%r12)
	std %r11, 432(%r12)
	std %r11, 440(%r12)
	std %r11, 448(%r12)
	std %r11, 456(%r12)
	std %r11, 464(%r12)
	std %r11, 472(%r12)
	std %r11, 480(%r12)
	std %r11, 488(%r12)
	std %r11, 496(%r12)
	std %r11, 504(%r12)
	std %r11, 512(%r12)
	std %r11, 520(%r12)
	std %r11, 528(%r12)
	std %r11, 536(%r12)
	std %r11, 544(%r12)
	std %r11, 552(%r12)
	std %r11, 560(%r12)
	std %r11, 568(%r12)
	std %r11, 576(%r12)
	std %r11, 584(%r12)
	std %r11, 592(%r12)
	std %r11, 600(%r12)
	std %r11, 608(%r12)
	std %r11, 616(%r12)
	std %r11, 624(%r12)
	std %r11, 632(%r12)
	std %r11, 640(%r12)
	std %r11, 648(%r12)
	std %r11, 656(%r12)
	std %r11, 664(%r12)
	std %r11, 672(%r12)
	std %r11, 680(%r12)
	std %r11, 688(%r12)
	std %r11, 696(%r12)
	std %r11, 704(%r12)
	std %r11, 712(%r12)
	std %r11, 720(%r12)
	std %r11, 728(%r12)
	std %r11, 736(%r12)
	std %r11, 744(%r12)
	std %r11, 752(%r12)
	std %r11, 760(%r12)
	std %r11, 768(%r12)
	std %r11, 776(%r12)
	std %r11, 784(%r12)
	std %r11, 792(%r12)
	std %r11, 800(%r12)
	std %r11, 808(%r12)
	std %r11, 816(%r12)
	std %r11, 824(%r12)
	std %r11, 832(%r12)
	std %r11, 840(%r12)
	std %r11, 848(%r12)
	std %r11, 856(%r12)
	std %r11, 864(%r12)
	std %r11, 872(%r12)
	std %r11, 880(%r12)
	std %r11, 888(%r12)
	std %r11, 896(%r12)
	std %r11, 904(%r12)
	std %r11, 912(%r12)
	std %r11, 920(%r12)
	std %r11, 928(%r12)
	std %r11, 936(%r12)
	std %r11, 944(%r12)
	std %r11, 952(%r12)
	std %r11, 960(%r12)
	std %r11, 968(%r12)
	std %r11, 976(%r12)
	std %r11, 984(%r12)
	std %r11, 992(%r12)
	std %r11, 1000(%r12)
	std %r11, 1008(%r12)
	std %r11, 1016(%r12)
	std %r11, 1024(%r12)
	std %r11, 1032(%r12)
	std %r11, 1040(%r12)
	std %r11, 1048(%r12)
	std %r11, 1056(%r12)
	std %r11, 1064(%r12)
	std %r11, 1072(%r12)
	std %r11, 1080(%r12)
	std %r11, 1088(%r12)
	std %r11, 1096(%r12)
	std %r11, 1104(%r12)
	std %r11, 1112(%r12)
	std %r11, 1120(%r12)
	std %r11, 1128(%r12)
	std %r11, 1136(%r12)
	std %r11, 1144(%r12)
	std %r11, 1152(%r12)
	std %r11, 1160(%r12)
	std %r11, 1168(%r12)
	std %r11, 1176(%r12)
	std %r11, 1184(%r12)
	std %r11, 1192(%r12)
	std %r11, 1200(%r12)
	std %r11, 1208(%r12)
	std %r11, 1216(%r12)
	std %r11, 1224(%r12)
	std %r11, 1232(%r12)
	std %r11, 1240(%r12)
	std %r11, 1248(%r12)
	std %r11, 1256(%r12)
	std %r11, 1264(%r12)
	std %r11, 1272(%r12)
	std %r11, 1280(%r12)
	std %r11, 1288(%r12)
	std %r11, 1296(%r12)
	std %r11, 1304(%r12)
	std %r11, 1312(%r12)
	std %r11, 1320(%r12)
	std %r11, 1328(%r12)
	std %r11, 1336(%r12)
	std %r11, 1344(%r12)
	std %r11, 1352(%r12)
	std %r11, 1360(%r12)
	std %r11, 1368(%r12)
	std %r11, 1376(%r12)
	std %r11, 1384(%r12)
	std %r11, 1392(%r12)
	std %r11, 1400(%r12)
	std %r11, 1408(%r12)
	std %r11, 1416(%r12)
	std %r11, 1424(%r12)
	std %r11, 1432(%r12)
	std %r11, 1440(%r12)
	std %r11, 1448(%r12)
	std %r11, 1456(%r12)
	std %r11, 1464(%r12)
	std %r11, 1472(%r12)
	std %r11, 1480(%r12)
	std %r11, 1488(%r12)
	std %r11, 1496(%r12)
	std %r11, 1504(%r12)
	std %r11, 1512(%r12)
	std %r11, 1520(%r12)
	std %r11, 1528(%r12)
	std %r11, 1536(%r12)
	std %r11, 1544(%r12)
	std %r11, 1552(%r12)
	std %r11, 1560(%r12)
	std %r11, 1568(%r12)
	std %r11, 1576(%r12)
	std %r11, 1584(%r12)
	std %r11, 1592(%r12)
	std %r11, 1600(%r12)
	std %r11, 1608(%r12)
	std %r11, 1616(%r12)
	std %r11, 1624(%r12)
	std %r11, 1632(%r12)
	std %r11, 1640(%r12)
	std %r11, 1648(%r12)
	std %r11, 1656(%r12)
	std %r11, 1664(%r12)
	std %r11, 1672(%r12)
	std %r11, 1680(%r12)
	std %r11, 1688(%r12)
	std %r11, 1696(%r12)
	std %r11, 1704(%r12)
	std %r11, 1712(%r12)
	std %r11, 1720(%r12)
	std %r11, 1728(%r12)
	std %r11, 1736(%r12)
	std %r11, 1744(%r12)
	std %r11, 1752(%r12)
	std %r11, 1760(%r12)
	std %r11, 1768(%r12)
	std %r11, 1776(%r12)
	std %r11, 1784(%r12)
	std %r11, 1792(%r12)
	std %r11, 1800(%r12)
	std %r11, 1808(%r12)
	std %r11, 1816(%r12)
	std %r11, 1824(%r12)
	std %r11, 1832(%r12)
	std %r11, 1840(%r12)
	std %r11, 1848(%r12)
	std %r11, 1856(%r12)
	std %r11, 1864(%r12)
	std %r11, 1872(%r12)
	std %r11, 1880(%r12)
	std %r11, 1888(%r12)
	std %r11, 1896(%r12)
	std %r11, 1904(%r12)
	std %r11, 1912(%r12)
	std %r11, 1920(%r12)
	std %r11, 1928(%r12)
	std %r11, 1936(%r12)
	std %r11, 1944(%r12)
	std %r11, 1952(%r12)
	std %r11, 1960(%r12)
	std %r11, 1968(%r12)
	std %r11, 1976(%r12)
	std %r11, 1984(%r12)
	std %r11, 1992(%r12)
	std %r11, 2000(%r12)
	std %r11, 2008(%r12)
	std %r11, 2016(%r12)
	std %r11, 2024(%r12)
	std %r11, 2032(%r12)
	std %r11, 2040(%r12)
	std %r11, 2048(%r12)
	std %r11, 2056(%r12)
	std %r11, 2064(%r12)
	std %r11, 2072(%r12)
	std %r11, 2080(%r12)
	std %r11, 2088(%r12)
	std %r11, 2096(%r12)
	std %r11, 2104(%r12)
	std %r11, 2112(%r12)
	std %r11, 2120(%r12)
	std %r11, 2128(%r12)
	std %r11, 2136(%r12)
	std %r11, 2144(%r12)
	std %r11, 2152(%r12)
	std %r11, 2160(%r12)
	std %r11, 2168(%r12)
	std %r11, 2176(%r12)
	std %r11, 2184(%r12)
	std %r11, 2192(%r12)
	std %r11, 2200(%r12)
	std %r11, 2208(%r12)
	std %r11, 2216(%r12)
	std %r11, 2224(%r12)
	std %r11, 2232(%r12)
	std %r11, 2240(%r12)
	std %r11, 2248(%r12)
	std %r11, 2256(%r12)
	std %r11, 2264(%r12)
	std %r11, 2272(%r12)
	std %r11, 2280(%r12)
	std %r11, 2288(%r12)
	std %r11, 2296(%r12)
	std %r11, 2304(%r12)
	std %r11, 2312(%r12)
	std %r11, 2320(%r12)
	std %r11, 2328(%r12)
	std %r11, 2336(%r12)
	std %r11, 2344(%r12)
	std %r11, 2352(%r12)
	std %r11, 2360(%r12)
	std %r11, 2368(%r12)
	std %r11, 2376(%r12)
	std %r11, 2384(%r12)
	std %r11, 2392(%r12)
	std %r11, 2400(%r12)
	std %r11, 2408(%r12)
	std %r11, 2416(%r12)
	std %r11, 2424(%r12)
	std %r11, 2432(%r12)
	std %r11, 2440(%r12)
	std %r11, 2448(%r12)
	std %r11, 2456(%r12)
	std %r11, 2464(%r12)
	std %r11, 2472(%r12)
	std %r11, 2480(%r12)
	std %r11, 2488(%r12)
	std %r11, 2496(%r12)
	std %r11, 2504(%r12)
	std %r11, 2512(%r12)
	std %r11, 2520(%r12)
	std %r11, 2528(%r12)
	std %r11, 2536(%r12)
	std %r11, 2544(%r12)
	std %r11, 2552(%r12)
	std %r11, 2560(%r12)
	std %r11, 2568(%r12)
	std %r11, 2576(%r12)
	std %r11, 2584(%r12)
	std %r11, 2592(%r12)
	std %r11, 2600(%r12)
	std %r11, 2608(%r12)
	std %r11, 2616(%r12)
	std %r11, 2624(%r12)
	std %r11, 2632(%r12)
	std %r11, 2640(%r12)
	std %r11, 2648(%r12)
	std %r11, 2656(%r12)
	std %r11, 2664(%r12)
	std %r11, 2672(%r12)
	std %r11, 2680(%r12)
	std %r11, 2688(%r12)
	std %r11, 2696(%r12)
	std %r11, 2704(%r12)
	std %r11, 2712(%r12)
	std %r11, 2720(%r12)
	std %r11, 2728(%r12)
	std %r11, 2736(%r12)
	std %r11, 2744(%r12)
	std %r11, 2752(%r12)
	std %r11, 2760(%r12)
	std %r11, 2768(%r12)
	std %r11, 2776(%r12)
	std %r11, 2784(%r12)
	std %r11, 2792(%r12)
	std %r11, 2800(%r12)
	std %r11, 2808(%r12)
	std %r11, 2816(%r12)
	std %r11, 2824(%r12)
	std %r11, 2832(%r12)
	std %r11, 2840(%r12)
	std %r11, 2848(%r12)
	std %r11, 2856(%r12)
	std %r11, 2864(%r12)
	std %r11, 2872(%r12)
	std %r11, 2880(%r12)
	std %r11, 2888(%r12)
	std %r11, 2896(%r12)
	std %r11, 2904(%r12)
	std %r11, 2912(%r12)
	std %r11, 2920(%r12)
	std %r11, 2928(%r12)
	std %r11, 2936(%r12)
	std %r11, 2944(%r12)
	std %r11, 2952(%r12)
	std %r11, 2960(%r12)
	std %r11, 2968(%r12)
	std %r11, 2976(%r12)
	std %r11, 2984(%r12)
	std %r11, 2992(%r12)
	std %r11, 3000(%r12)
	std %r11, 3008(%r12)
	std %r11, 3016(%r12)
	std %r11, 3024(%r12)
	std %r11, 3032(%r12)
	std %r11, 3040(%r12)
	std %r11, 3048(%r12)
	std %r11, 3056(%r12)
	std %r11, 3064(%r12)
	std %r11, 3072(%r12)
	std %r11, 3080(%r12)
	std %r11, 3088(%r12)
	std %r11, 3096(%r12)
	std %r11, 3104(%r12)
	std %r11, 3112(%r12)
	std %r11, 3120(%r12)
	std %r11, 3128(%r12)
	std %r11, 3136(%r12)
	std %r11, 3144(%r12)
	std %r11, 3152(%r12)
	std %r11, 3160(%r12)
	std %r11, 3168(%r12)
	std %r11, 3176(%r12)
	std %r11, 3184(%r12)
	std %r11, 3192(%r12)
	std %r11, 3200(%r12)
	std %r11, 3208(%r12)
	std %r11, 3216(%r12)
	std %r11, 3224(%r12)
	std %r11, 3232(%r12)
	std %r11, 3240(%r12)
	std %r11, 3248(%r12)
	std %r11, 3256(%r12)
	std %r11, 3264(%r12)
	std %r11, 3272(%r12)
	std %r11, 3280(%r12)
	std %r11, 3288(%r12)
	std %r11, 3296(%r12)
	std %r11, 3304(%r12)
	std %r11, 3312(%r12)
	std %r11, 3320(%r12)
	std %r11, 3328(%r12)
	std %r11, 3336(%r12)
	std %r11, 3344(%r12)
	std %r11, 3352(%r12)
	std %r11, 3360(%r12)
	std %r11, 3368(%r12)
	addi %r1, %r1, 3408
	blr
