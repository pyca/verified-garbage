// The functions of `src/camellia_cfb.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_cfb128_encrypt:
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
	cmpldi %cr0, %r30, 0
	beq %cr0, 20f
22:
	lwz %r8, 3344(%r5)
	stw %r8, 3088(%r5)
	lwz %r8, 3348(%r5)
	stw %r8, 3092(%r5)
	lwz %r8, 3352(%r5)
	stw %r8, 3096(%r5)
	lwz %r8, 3356(%r5)
	stw %r8, 3100(%r5)
	bl {vg_camellia_serial_crypt}
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
	lwz %r8, 0(%r31)
	stw %r8, 3344(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 3348(%r5)
	lwz %r8, 8(%r31)
	stw %r8, 3352(%r5)
	lwz %r8, 12(%r31)
	stw %r8, 3356(%r5)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 22b
	b 21f
20:
21:
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
	addi %r1, %r1, 3408
	li %r0, 0
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v9, %v9, %v9
	vxor %v10, %v10, %v10
	vxor %v11, %v11, %v11
	vxor %v12, %v12, %v12
	vxor %v13, %v13, %v13
	vxor %v14, %v14, %v14
	vxor %v15, %v15, %v15
	vxor %v16, %v16, %v16
	vxor %v17, %v17, %v17
	vxor %v18, %v18, %v18
	vxor %v19, %v19, %v19
	blr

vg_camellia_cfb128_decrypt:
	stdu %r1, -3408(%r1)
	addi %r8, %r1, 32
	std %r28, 3360(%r8)
	or %r28, %r4, %r4
	or %r4, %r5, %r5
	or %r5, %r6, %r6
	or %r6, %r7, %r7
	or %r7, %r8, %r8
	rldicl %r8, %r6, 61, 3
	cmpldi %cr0, %r8, 0
	beq %cr0, 20f
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
	beq %cr0, 22f
	cmpldi %cr0, %r22, 0
	beq %cr0, 24f
	addi %r7, %r8, 2816
	addi %r3, %r3, 256
	li %r23, 30
	b 25f
24:
	addi %r7, %r8, 2304
	addi %r3, %r3, 192
	li %r23, 22
25:
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
26:
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
	bne %cr0, 26b
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
	b 23f
22:
	cmpldi %cr0, %r22, 0
	beq %cr0, 27f
	addi %r7, %r8, 2816
	li %r23, 34
	b 28f
27:
	addi %r7, %r8, 2304
	li %r23, 26
28:
	addi %r4, %r8, 768
29:
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
	bne %cr0, 29b
23:
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
	rldicl %r8, %r30, 61, 3
	cmpldi %cr0, %r8, 0
	beq %cr0, 210f
212:
	lwz %r8, 3344(%r5)
	stw %r8, 3088(%r5)
	lwz %r8, 3348(%r5)
	stw %r8, 3092(%r5)
	lwz %r8, 3352(%r5)
	stw %r8, 3096(%r5)
	lwz %r8, 3356(%r5)
	stw %r8, 3100(%r5)
	lwz %r8, 0(%r31)
	stw %r8, 3344(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 3348(%r5)
	lwz %r8, 8(%r31)
	stw %r8, 3352(%r5)
	lwz %r8, 12(%r31)
	stw %r8, 3356(%r5)
	lwz %r8, 3344(%r5)
	stw %r8, 3104(%r5)
	lwz %r8, 3348(%r5)
	stw %r8, 3108(%r5)
	lwz %r8, 3352(%r5)
	stw %r8, 3112(%r5)
	lwz %r8, 3356(%r5)
	stw %r8, 3116(%r5)
	lwz %r8, 16(%r31)
	stw %r8, 3344(%r5)
	lwz %r8, 20(%r31)
	stw %r8, 3348(%r5)
	lwz %r8, 24(%r31)
	stw %r8, 3352(%r5)
	lwz %r8, 28(%r31)
	stw %r8, 3356(%r5)
	lwz %r8, 3344(%r5)
	stw %r8, 3120(%r5)
	lwz %r8, 3348(%r5)
	stw %r8, 3124(%r5)
	lwz %r8, 3352(%r5)
	stw %r8, 3128(%r5)
	lwz %r8, 3356(%r5)
	stw %r8, 3132(%r5)
	lwz %r8, 32(%r31)
	stw %r8, 3344(%r5)
	lwz %r8, 36(%r31)
	stw %r8, 3348(%r5)
	lwz %r8, 40(%r31)
	stw %r8, 3352(%r5)
	lwz %r8, 44(%r31)
	stw %r8, 3356(%r5)
	lwz %r8, 3344(%r5)
	stw %r8, 3136(%r5)
	lwz %r8, 3348(%r5)
	stw %r8, 3140(%r5)
	lwz %r8, 3352(%r5)
	stw %r8, 3144(%r5)
	lwz %r8, 3356(%r5)
	stw %r8, 3148(%r5)
	lwz %r8, 48(%r31)
	stw %r8, 3344(%r5)
	lwz %r8, 52(%r31)
	stw %r8, 3348(%r5)
	lwz %r8, 56(%r31)
	stw %r8, 3352(%r5)
	lwz %r8, 60(%r31)
	stw %r8, 3356(%r5)
	lwz %r8, 3344(%r5)
	stw %r8, 3152(%r5)
	lwz %r8, 3348(%r5)
	stw %r8, 3156(%r5)
	lwz %r8, 3352(%r5)
	stw %r8, 3160(%r5)
	lwz %r8, 3356(%r5)
	stw %r8, 3164(%r5)
	lwz %r8, 64(%r31)
	stw %r8, 3344(%r5)
	lwz %r8, 68(%r31)
	stw %r8, 3348(%r5)
	lwz %r8, 72(%r31)
	stw %r8, 3352(%r5)
	lwz %r8, 76(%r31)
	stw %r8, 3356(%r5)
	lwz %r8, 3344(%r5)
	stw %r8, 3168(%r5)
	lwz %r8, 3348(%r5)
	stw %r8, 3172(%r5)
	lwz %r8, 3352(%r5)
	stw %r8, 3176(%r5)
	lwz %r8, 3356(%r5)
	stw %r8, 3180(%r5)
	lwz %r8, 80(%r31)
	stw %r8, 3344(%r5)
	lwz %r8, 84(%r31)
	stw %r8, 3348(%r5)
	lwz %r8, 88(%r31)
	stw %r8, 3352(%r5)
	lwz %r8, 92(%r31)
	stw %r8, 3356(%r5)
	lwz %r8, 3344(%r5)
	stw %r8, 3184(%r5)
	lwz %r8, 3348(%r5)
	stw %r8, 3188(%r5)
	lwz %r8, 3352(%r5)
	stw %r8, 3192(%r5)
	lwz %r8, 3356(%r5)
	stw %r8, 3196(%r5)
	lwz %r8, 96(%r31)
	stw %r8, 3344(%r5)
	lwz %r8, 100(%r31)
	stw %r8, 3348(%r5)
	lwz %r8, 104(%r31)
	stw %r8, 3352(%r5)
	lwz %r8, 108(%r31)
	stw %r8, 3356(%r5)
	lwz %r8, 3344(%r5)
	stw %r8, 3200(%r5)
	lwz %r8, 3348(%r5)
	stw %r8, 3204(%r5)
	lwz %r8, 3352(%r5)
	stw %r8, 3208(%r5)
	lwz %r8, 3356(%r5)
	stw %r8, 3212(%r5)
	lwz %r8, 112(%r31)
	stw %r8, 3344(%r5)
	lwz %r8, 116(%r31)
	stw %r8, 3348(%r5)
	lwz %r8, 120(%r31)
	stw %r8, 3352(%r5)
	lwz %r8, 124(%r31)
	stw %r8, 3356(%r5)
	or %r10, %r3, %r3
	or %r6, %r5, %r5
	or %r3, %r28, %r28
	or %r4, %r5, %r5
	li %r5, 414
	bl {vg_camellia_crypt_prepared}
	or %r5, %r6, %r6
	or %r3, %r10, %r10
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
	lwz %r8, 16(%r31)
	lwz %r9, 3104(%r5)
	xor %r8, %r8, %r9
	stw %r8, 16(%r31)
	lwz %r8, 20(%r31)
	lwz %r9, 3108(%r5)
	xor %r8, %r8, %r9
	stw %r8, 20(%r31)
	lwz %r8, 24(%r31)
	lwz %r9, 3112(%r5)
	xor %r8, %r8, %r9
	stw %r8, 24(%r31)
	lwz %r8, 28(%r31)
	lwz %r9, 3116(%r5)
	xor %r8, %r8, %r9
	stw %r8, 28(%r31)
	lwz %r8, 32(%r31)
	lwz %r9, 3120(%r5)
	xor %r8, %r8, %r9
	stw %r8, 32(%r31)
	lwz %r8, 36(%r31)
	lwz %r9, 3124(%r5)
	xor %r8, %r8, %r9
	stw %r8, 36(%r31)
	lwz %r8, 40(%r31)
	lwz %r9, 3128(%r5)
	xor %r8, %r8, %r9
	stw %r8, 40(%r31)
	lwz %r8, 44(%r31)
	lwz %r9, 3132(%r5)
	xor %r8, %r8, %r9
	stw %r8, 44(%r31)
	lwz %r8, 48(%r31)
	lwz %r9, 3136(%r5)
	xor %r8, %r8, %r9
	stw %r8, 48(%r31)
	lwz %r8, 52(%r31)
	lwz %r9, 3140(%r5)
	xor %r8, %r8, %r9
	stw %r8, 52(%r31)
	lwz %r8, 56(%r31)
	lwz %r9, 3144(%r5)
	xor %r8, %r8, %r9
	stw %r8, 56(%r31)
	lwz %r8, 60(%r31)
	lwz %r9, 3148(%r5)
	xor %r8, %r8, %r9
	stw %r8, 60(%r31)
	lwz %r8, 64(%r31)
	lwz %r9, 3152(%r5)
	xor %r8, %r8, %r9
	stw %r8, 64(%r31)
	lwz %r8, 68(%r31)
	lwz %r9, 3156(%r5)
	xor %r8, %r8, %r9
	stw %r8, 68(%r31)
	lwz %r8, 72(%r31)
	lwz %r9, 3160(%r5)
	xor %r8, %r8, %r9
	stw %r8, 72(%r31)
	lwz %r8, 76(%r31)
	lwz %r9, 3164(%r5)
	xor %r8, %r8, %r9
	stw %r8, 76(%r31)
	lwz %r8, 80(%r31)
	lwz %r9, 3168(%r5)
	xor %r8, %r8, %r9
	stw %r8, 80(%r31)
	lwz %r8, 84(%r31)
	lwz %r9, 3172(%r5)
	xor %r8, %r8, %r9
	stw %r8, 84(%r31)
	lwz %r8, 88(%r31)
	lwz %r9, 3176(%r5)
	xor %r8, %r8, %r9
	stw %r8, 88(%r31)
	lwz %r8, 92(%r31)
	lwz %r9, 3180(%r5)
	xor %r8, %r8, %r9
	stw %r8, 92(%r31)
	lwz %r8, 96(%r31)
	lwz %r9, 3184(%r5)
	xor %r8, %r8, %r9
	stw %r8, 96(%r31)
	lwz %r8, 100(%r31)
	lwz %r9, 3188(%r5)
	xor %r8, %r8, %r9
	stw %r8, 100(%r31)
	lwz %r8, 104(%r31)
	lwz %r9, 3192(%r5)
	xor %r8, %r8, %r9
	stw %r8, 104(%r31)
	lwz %r8, 108(%r31)
	lwz %r9, 3196(%r5)
	xor %r8, %r8, %r9
	stw %r8, 108(%r31)
	lwz %r8, 112(%r31)
	lwz %r9, 3200(%r5)
	xor %r8, %r8, %r9
	stw %r8, 112(%r31)
	lwz %r8, 116(%r31)
	lwz %r9, 3204(%r5)
	xor %r8, %r8, %r9
	stw %r8, 116(%r31)
	lwz %r8, 120(%r31)
	lwz %r9, 3208(%r5)
	xor %r8, %r8, %r9
	stw %r8, 120(%r31)
	lwz %r8, 124(%r31)
	lwz %r9, 3212(%r5)
	xor %r8, %r8, %r9
	stw %r8, 124(%r31)
	addi %r31, %r31, 128
	addi %r30, %r30, -8
	rldicl %r8, %r30, 61, 3
	cmpldi %cr0, %r8, 0
	bne %cr0, 212b
	b 211f
210:
211:
	cmpldi %cr0, %r30, 0
	beq %cr0, 213f
215:
	lwz %r8, 3344(%r5)
	stw %r8, 3088(%r5)
	lwz %r8, 3348(%r5)
	stw %r8, 3092(%r5)
	lwz %r8, 3352(%r5)
	stw %r8, 3096(%r5)
	lwz %r8, 3356(%r5)
	stw %r8, 3100(%r5)
	lwz %r8, 0(%r31)
	stw %r8, 3344(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 3348(%r5)
	lwz %r8, 8(%r31)
	stw %r8, 3352(%r5)
	lwz %r8, 12(%r31)
	stw %r8, 3356(%r5)
	or %r10, %r3, %r3
	or %r6, %r5, %r5
	or %r3, %r28, %r28
	or %r4, %r5, %r5
	li %r5, 414
	bl {vg_camellia_crypt_prepared}
	or %r5, %r6, %r6
	or %r3, %r10, %r10
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
	bne %cr0, 215b
	b 214f
213:
214:
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
	b 21f
20:
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
	cmpldi %cr0, %r30, 0
	beq %cr0, 216f
218:
	lwz %r8, 3344(%r5)
	stw %r8, 3088(%r5)
	lwz %r8, 3348(%r5)
	stw %r8, 3092(%r5)
	lwz %r8, 3352(%r5)
	stw %r8, 3096(%r5)
	lwz %r8, 3356(%r5)
	stw %r8, 3100(%r5)
	bl {vg_camellia_serial_crypt}
	lwz %r8, 0(%r31)
	stw %r8, 3344(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 3348(%r5)
	lwz %r8, 8(%r31)
	stw %r8, 3352(%r5)
	lwz %r8, 12(%r31)
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
	bne %cr0, 218b
	b 217f
216:
217:
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
21:
	ld %r28, 3360(%r5)
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
	addi %r1, %r1, 3408
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
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v9, %v9, %v9
	vxor %v10, %v10, %v10
	vxor %v11, %v11, %v11
	vxor %v12, %v12, %v12
	vxor %v13, %v13, %v13
	vxor %v14, %v14, %v14
	vxor %v15, %v15, %v15
	vxor %v16, %v16, %v16
	vxor %v17, %v17, %v17
	vxor %v18, %v18, %v18
	vxor %v19, %v19, %v19
	blr

vg_camellia_cfb128_encrypt_final:
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
	cmpldi %cr0, %r30, 0
	beq %cr0, 20f
22:
	lwz %r8, 3344(%r5)
	stw %r8, 3088(%r5)
	lwz %r8, 3348(%r5)
	stw %r8, 3092(%r5)
	lwz %r8, 3352(%r5)
	stw %r8, 3096(%r5)
	lwz %r8, 3356(%r5)
	stw %r8, 3100(%r5)
	bl {vg_camellia_serial_crypt}
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 23f
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
	lwz %r8, 0(%r31)
	stw %r8, 3344(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 3348(%r5)
	lwz %r8, 8(%r31)
	stw %r8, 3352(%r5)
	lwz %r8, 12(%r31)
	stw %r8, 3356(%r5)
	addi %r31, %r31, 16
	addi %r30, %r30, -16
	b 24f
23:
	lwz %r8, 3088(%r5)
	stw %r8, 3344(%r5)
	lwz %r8, 3092(%r5)
	stw %r8, 3348(%r5)
	lwz %r8, 3096(%r5)
	stw %r8, 3352(%r5)
	lwz %r8, 3100(%r5)
	stw %r8, 3356(%r5)
	addi %r8, %r5, 3088
25:
	lbz %r9, 0(%r31)
	lbz %r10, 0(%r8)
	xor %r9, %r9, %r10
	stb %r9, 0(%r31)
	addi %r8, %r8, 1
	addi %r31, %r31, 1
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 25b
24:
	cmpldi %cr0, %r30, 0
	bne %cr0, 22b
	b 21f
20:
21:
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
	addi %r1, %r1, 3408
	li %r0, 0
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v9, %v9, %v9
	vxor %v10, %v10, %v10
	vxor %v11, %v11, %v11
	vxor %v12, %v12, %v12
	vxor %v13, %v13, %v13
	vxor %v14, %v14, %v14
	vxor %v15, %v15, %v15
	vxor %v16, %v16, %v16
	vxor %v17, %v17, %v17
	vxor %v18, %v18, %v18
	vxor %v19, %v19, %v19
	blr

vg_camellia_cfb128_decrypt_final:
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
	cmpldi %cr0, %r30, 0
	beq %cr0, 20f
22:
	lwz %r8, 3344(%r5)
	stw %r8, 3088(%r5)
	lwz %r8, 3348(%r5)
	stw %r8, 3092(%r5)
	lwz %r8, 3352(%r5)
	stw %r8, 3096(%r5)
	lwz %r8, 3356(%r5)
	stw %r8, 3100(%r5)
	bl {vg_camellia_serial_crypt}
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 23f
	lwz %r8, 0(%r31)
	stw %r8, 3344(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 3348(%r5)
	lwz %r8, 8(%r31)
	stw %r8, 3352(%r5)
	lwz %r8, 12(%r31)
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
	addi %r30, %r30, -16
	b 24f
23:
	lwz %r8, 3088(%r5)
	stw %r8, 3344(%r5)
	lwz %r8, 3092(%r5)
	stw %r8, 3348(%r5)
	lwz %r8, 3096(%r5)
	stw %r8, 3352(%r5)
	lwz %r8, 3100(%r5)
	stw %r8, 3356(%r5)
	addi %r8, %r5, 3088
25:
	lbz %r9, 0(%r31)
	lbz %r10, 0(%r8)
	xor %r9, %r9, %r10
	stb %r9, 0(%r31)
	addi %r8, %r8, 1
	addi %r31, %r31, 1
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 25b
24:
	cmpldi %cr0, %r30, 0
	bne %cr0, 22b
	b 21f
20:
21:
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
	addi %r1, %r1, 3408
	li %r0, 0
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v9, %v9, %v9
	vxor %v10, %v10, %v10
	vxor %v11, %v11, %v11
	vxor %v12, %v12, %v12
	vxor %v13, %v13, %v13
	vxor %v14, %v14, %v14
	vxor %v15, %v15, %v15
	vxor %v16, %v16, %v16
	vxor %v17, %v17, %v17
	vxor %v18, %v18, %v18
	vxor %v19, %v19, %v19
	blr
