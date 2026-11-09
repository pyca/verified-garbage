// The functions of `src/internal/vg_camellia_crypt_prepared.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_crypt_prepared:
	or %r8, %r4, %r4
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
	addi %r22, %r3, -18
	cmpldi %cr0, %r22, 0
	beq %cr0, 20f
	addi %r7, %r8, 2816
	b 21f
20:
	addi %r7, %r8, 2304
21:
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
22:
	addi %r3, %r4, 384
23:
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
	bne %cr0, 23b
	subf %r22, %r7, %r4
	cmpldi %cr0, %r22, 0
	bne %cr0, 24f
	b 25f
24:
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
25:
	subf %r22, %r7, %r4
	cmpldi %cr0, %r22, 0
	bne %cr0, 22b
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
	blr
