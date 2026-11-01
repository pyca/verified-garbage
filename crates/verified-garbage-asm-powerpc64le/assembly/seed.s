// The functions of `src/seed.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_seed_expand_key:
	stdu %r1, -1072(%r1)
	addi %r5, %r1, 32
	or %r8, %r5, %r5
	std %r14, 896(%r8)
	std %r15, 904(%r8)
	std %r16, 912(%r8)
	std %r17, 920(%r8)
	std %r18, 928(%r8)
	std %r19, 936(%r8)
	std %r20, 944(%r8)
	std %r21, 952(%r8)
	std %r22, 960(%r8)
	std %r23, 968(%r8)
	std %r24, 976(%r8)
	std %r25, 984(%r8)
	std %r26, 992(%r8)
	std %r27, 1000(%r8)
	std %r28, 1008(%r8)
	std %r29, 1016(%r8)
	std %r30, 1024(%r8)
	std %r31, 1032(%r8)
	li %r9, 0
	lwbrx %r9, %r3, %r9
	rldicr %r9, %r9, 32, 31
	li %r6, 4
	lwbrx %r6, %r3, %r6
	or %r6, %r6, %r9
	li %r9, 8
	lwbrx %r9, %r3, %r9
	rldicr %r9, %r9, 32, 31
	li %r7, 12
	lwbrx %r7, %r3, %r7
	or %r7, %r7, %r9
	rldicl %r9, %r6, 32, 32
	rldicl %r10, %r7, 32, 32
	add %r9, %r9, %r10
	lis %r11, -25033
	ori %r11, %r11, 31161
	subf %r9, %r11, %r9
	stw %r9, 384(%r8)
	subf %r9, %r7, %r6
	add %r9, %r9, %r11
	stw %r9, 388(%r8)
	rldicl %r6, %r6, 56, 0
	rldicl %r9, %r6, 32, 32
	rldicl %r10, %r7, 32, 32
	add %r9, %r9, %r10
	lis %r11, 15470
	ori %r11, %r11, 62323
	subf %r9, %r11, %r9
	stw %r9, 392(%r8)
	subf %r9, %r7, %r6
	add %r9, %r9, %r11
	stw %r9, 396(%r8)
	rldicl %r7, %r7, 8, 0
	rldicl %r9, %r6, 32, 32
	rldicl %r10, %r7, 32, 32
	add %r9, %r9, %r10
	lis %r11, 30941
	ori %r11, %r11, 59110
	subf %r9, %r11, %r9
	stw %r9, 400(%r8)
	subf %r9, %r7, %r6
	add %r9, %r9, %r11
	stw %r9, 404(%r8)
	rldicl %r6, %r6, 56, 0
	rldicl %r9, %r6, 32, 32
	rldicl %r10, %r7, 32, 32
	add %r9, %r9, %r10
	lis %r11, -3653
	ori %r11, %r11, 52684
	subf %r9, %r11, %r9
	stw %r9, 408(%r8)
	subf %r9, %r7, %r6
	add %r9, %r9, %r11
	stw %r9, 412(%r8)
	rldicl %r7, %r7, 8, 0
	rldicl %r9, %r6, 32, 32
	rldicl %r10, %r7, 32, 32
	add %r9, %r9, %r10
	lis %r11, -7305
	ori %r11, %r11, 39833
	subf %r9, %r11, %r9
	stw %r9, 416(%r8)
	subf %r9, %r7, %r6
	add %r9, %r9, %r11
	stw %r9, 420(%r8)
	rldicl %r6, %r6, 56, 0
	rldicl %r9, %r6, 32, 32
	rldicl %r10, %r7, 32, 32
	add %r9, %r9, %r10
	lis %r11, -14609
	ori %r11, %r11, 14131
	subf %r9, %r11, %r9
	stw %r9, 424(%r8)
	subf %r9, %r7, %r6
	add %r9, %r9, %r11
	stw %r9, 428(%r8)
	rldicl %r7, %r7, 8, 0
	rldicl %r9, %r6, 32, 32
	rldicl %r10, %r7, 32, 32
	add %r9, %r9, %r10
	lis %r11, -29218
	ori %r11, %r11, 28263
	subf %r9, %r11, %r9
	stw %r9, 432(%r8)
	subf %r9, %r7, %r6
	add %r9, %r9, %r11
	stw %r9, 436(%r8)
	rldicl %r6, %r6, 56, 0
	rldicl %r9, %r6, 32, 32
	rldicl %r10, %r7, 32, 32
	add %r9, %r9, %r10
	lis %r11, 7100
	ori %r11, %r11, 56527
	subf %r9, %r11, %r9
	stw %r9, 440(%r8)
	subf %r9, %r7, %r6
	add %r9, %r9, %r11
	stw %r9, 444(%r8)
	rldicl %r7, %r7, 8, 0
	rldicl %r9, %r6, 32, 32
	rldicl %r10, %r7, 32, 32
	add %r9, %r9, %r10
	lis %r11, 14201
	ori %r11, %r11, 47518
	subf %r9, %r11, %r9
	stw %r9, 448(%r8)
	subf %r9, %r7, %r6
	add %r9, %r9, %r11
	stw %r9, 452(%r8)
	rldicl %r6, %r6, 56, 0
	rldicl %r9, %r6, 32, 32
	rldicl %r10, %r7, 32, 32
	add %r9, %r9, %r10
	lis %r11, 28403
	ori %r11, %r11, 29500
	subf %r9, %r11, %r9
	stw %r9, 456(%r8)
	subf %r9, %r7, %r6
	add %r9, %r9, %r11
	stw %r9, 460(%r8)
	rldicl %r7, %r7, 8, 0
	rldicl %r9, %r6, 32, 32
	rldicl %r10, %r7, 32, 32
	add %r9, %r9, %r10
	lis %r11, -8730
	ori %r11, %r11, 59000
	subf %r9, %r11, %r9
	stw %r9, 464(%r8)
	subf %r9, %r7, %r6
	add %r9, %r9, %r11
	stw %r9, 468(%r8)
	rldicl %r6, %r6, 56, 0
	rldicl %r9, %r6, 32, 32
	rldicl %r10, %r7, 32, 32
	add %r9, %r9, %r10
	lis %r11, -17459
	ori %r11, %r11, 52465
	subf %r9, %r11, %r9
	stw %r9, 472(%r8)
	subf %r9, %r7, %r6
	add %r9, %r9, %r11
	stw %r9, 476(%r8)
	rldicl %r7, %r7, 8, 0
	rldicl %r9, %r6, 32, 32
	rldicl %r10, %r7, 32, 32
	add %r9, %r9, %r10
	lis %r11, 30619
	ori %r11, %r11, 39395
	subf %r9, %r11, %r9
	stw %r9, 480(%r8)
	subf %r9, %r7, %r6
	add %r9, %r9, %r11
	stw %r9, 484(%r8)
	rldicl %r6, %r6, 56, 0
	rldicl %r9, %r6, 32, 32
	rldicl %r10, %r7, 32, 32
	add %r9, %r9, %r10
	lis %r11, -4297
	ori %r11, %r11, 13254
	subf %r9, %r11, %r9
	stw %r9, 488(%r8)
	subf %r9, %r7, %r6
	add %r9, %r9, %r11
	stw %r9, 492(%r8)
	rldicl %r7, %r7, 8, 0
	rldicl %r9, %r6, 32, 32
	rldicl %r10, %r7, 32, 32
	add %r9, %r9, %r10
	lis %r11, -8594
	ori %r11, %r11, 26509
	subf %r9, %r11, %r9
	stw %r9, 496(%r8)
	subf %r9, %r7, %r6
	add %r9, %r9, %r11
	stw %r9, 500(%r8)
	rldicl %r6, %r6, 56, 0
	rldicl %r9, %r6, 32, 32
	rldicl %r10, %r7, 32, 32
	add %r9, %r9, %r10
	lis %r11, -17188
	ori %r11, %r11, 53019
	subf %r9, %r11, %r9
	stw %r9, 504(%r8)
	subf %r9, %r7, %r6
	add %r9, %r9, %r11
	stw %r9, 508(%r8)
	rldicl %r7, %r7, 8, 0
	li %r6, 2
20:
	ld %r14, 384(%r8)
	ld %r15, 392(%r8)
	ld %r16, 400(%r8)
	ld %r17, 408(%r8)
	ld %r18, 416(%r8)
	ld %r19, 424(%r8)
	ld %r20, 432(%r8)
	ld %r21, 440(%r8)
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
	or %r24, %r14, %r14
	or %r25, %r15, %r15
	or %r26, %r16, %r16
	or %r27, %r17, %r17
	or %r28, %r18, %r18
	or %r29, %r19, %r19
	or %r30, %r20, %r20
	or %r31, %r21, %r21
	or %r14, %r24, %r24
	xor %r14, %r14, %r25
	xor %r14, %r14, %r27
	or %r15, %r26, %r26
	xor %r15, %r15, %r27
	xor %r15, %r15, %r30
	xor %r15, %r15, %r31
	or %r16, %r28, %r28
	xor %r16, %r16, %r29
	xor %r16, %r16, %r31
	or %r17, %r25, %r25
	xor %r17, %r17, %r26
	xor %r17, %r17, %r27
	xor %r17, %r17, %r29
	or %r18, %r25, %r25
	xor %r18, %r18, %r26
	xor %r18, %r18, %r28
	or %r19, %r27, %r27
	xor %r19, %r19, %r28
	or %r20, %r26, %r26
	xor %r20, %r20, %r27
	xor %r20, %r20, %r28
	xor %r20, %r20, %r29
	or %r21, %r28, %r28
	xor %r21, %r21, %r29
	xor %r21, %r21, %r30
	li %r31, 0
	addi %r31, %r31, -1
	xor %r22, %r18, %r16
	xor %r23, %r21, %r15
	xor %r24, %r21, %r18
	xor %r25, %r21, %r16
	xor %r19, %r20, %r19
	xor %r26, %r19, %r14
	xor %r18, %r26, %r18
	xor %r27, %r23, %r22
	xor %r28, %r26, %r21
	xor %r15, %r26, %r15
	xor %r29, %r15, %r25
	xor %r17, %r17, %r27
	xor %r16, %r17, %r16
	xor %r17, %r17, %r20
	xor %r20, %r16, %r14
	xor %r30, %r16, %r19
	xor %r0, %r17, %r24
	xor %r9, %r14, %r0
	std %r31, 0(%r8)
	xor %r31, %r30, %r0
	std %r17, 8(%r8)
	xor %r17, %r30, %r25
	xor %r19, %r19, %r0
	std %r17, 16(%r8)
	xor %r17, %r23, %r19
	xor %r21, %r21, %r19
	std %r21, 24(%r8)
	and %r21, %r27, %r16
	std %r27, 32(%r8)
	and %r27, %r29, %r20
	xor %r27, %r27, %r21
	std %r29, 40(%r8)
	and %r29, %r18, %r14
	xor %r29, %r29, %r21
	and %r21, %r23, %r19
	std %r23, 48(%r8)
	and %r23, %r15, %r26
	xor %r23, %r23, %r21
	std %r15, 56(%r8)
	and %r15, %r28, %r9
	xor %r15, %r15, %r21
	and %r21, %r24, %r0
	std %r24, 64(%r8)
	and %r24, %r22, %r31
	xor %r24, %r24, %r21
	std %r22, 72(%r8)
	and %r22, %r25, %r30
	xor %r22, %r22, %r21
	xor %r27, %r27, %r24
	xor %r29, %r29, %r22
	xor %r23, %r23, %r24
	xor %r15, %r15, %r22
	ld %r22, 8(%r8)
	xor %r27, %r27, %r22
	ld %r22, 16(%r8)
	xor %r29, %r29, %r22
	xor %r23, %r23, %r17
	ld %r17, 24(%r8)
	xor %r15, %r15, %r17
	xor %r17, %r27, %r29
	and %r27, %r27, %r23
	xor %r22, %r15, %r27
	and %r24, %r17, %r22
	xor %r24, %r24, %r29
	xor %r21, %r23, %r15
	xor %r29, %r29, %r27
	and %r29, %r29, %r21
	xor %r29, %r29, %r15
	xor %r23, %r23, %r29
	xor %r21, %r22, %r29
	and %r15, %r15, %r21
	xor %r23, %r15, %r23
	xor %r22, %r22, %r15
	and %r22, %r24, %r22
	xor %r17, %r17, %r22
	xor %r22, %r17, %r23
	xor %r15, %r24, %r29
	xor %r21, %r24, %r17
	xor %r27, %r29, %r23
	std %r25, 24(%r8)
	xor %r25, %r15, %r22
	and %r16, %r27, %r16
	and %r20, %r23, %r20
	and %r14, %r29, %r14
	and %r19, %r21, %r19
	and %r26, %r17, %r26
	and %r9, %r24, %r9
	and %r0, %r15, %r0
	and %r31, %r25, %r31
	and %r30, %r22, %r30
	std %r20, 16(%r8)
	ld %r20, 32(%r8)
	and %r27, %r27, %r20
	ld %r20, 40(%r8)
	and %r23, %r23, %r20
	and %r29, %r29, %r18
	ld %r18, 48(%r8)
	and %r21, %r21, %r18
	ld %r18, 56(%r8)
	and %r17, %r17, %r18
	and %r24, %r24, %r28
	ld %r28, 64(%r8)
	and %r15, %r15, %r28
	ld %r28, 72(%r8)
	and %r25, %r25, %r28
	ld %r28, 24(%r8)
	and %r22, %r22, %r28
	xor %r15, %r15, %r25
	xor %r29, %r23, %r29
	xor %r17, %r9, %r17
	xor %r27, %r27, %r23
	xor %r23, %r14, %r21
	xor %r14, %r14, %r9
	xor %r30, %r31, %r30
	xor %r16, %r16, %r19
	xor %r0, %r0, %r31
	xor %r25, %r25, %r22
	xor %r21, %r21, %r17
	xor %r23, %r23, %r16
	xor %r22, %r26, %r15
	xor %r19, %r19, %r0
	xor %r15, %r15, %r23
	xor %r24, %r24, %r23
	xor %r30, %r30, %r22
	xor %r27, %r27, %r22
	xor %r26, %r26, %r19
	xor %r24, %r24, %r30
	ld %r22, 16(%r8)
	xor %r22, %r22, %r27
	xor %r19, %r19, %r27
	xor %r21, %r21, %r30
	ld %r30, 0(%r8)
	xor %r21, %r21, %r30
	xor %r17, %r17, %r15
	xor %r17, %r17, %r30
	xor %r15, %r26, %r24
	xor %r18, %r16, %r22
	xor %r14, %r14, %r22
	xor %r16, %r29, %r24
	xor %r26, %r26, %r18
	xor %r20, %r26, %r30
	xor %r25, %r25, %r15
	xor %r25, %r25, %r30
	std %r21, 0(%r8)
	or %r21, %r19, %r19
	or %r19, %r25, %r25
	std %r17, 16(%r8)
	or %r17, %r14, %r14
	ld %r15, 0(%r8)
	ld %r14, 16(%r8)
	or %r24, %r14, %r14
	or %r25, %r15, %r15
	or %r26, %r16, %r16
	or %r27, %r17, %r17
	or %r28, %r18, %r18
	or %r29, %r19, %r19
	or %r30, %r20, %r20
	or %r31, %r21, %r21
	lis %r9, 255
	ori %r9, %r9, 255
	rldicr %r9, %r9, 32, 31
	oris %r9, %r9, 255
	ori %r9, %r9, 255
	lis %r10, -256
	ori %r10, %r10, 65280
	rldicr %r10, %r10, 32, 31
	oris %r10, %r10, 65280
	ori %r10, %r10, 65280
	and %r14, %r25, %r10
	and %r22, %r26, %r9
	xor %r14, %r14, %r22
	and %r22, %r27, %r10
	xor %r14, %r14, %r22
	and %r22, %r28, %r9
	xor %r14, %r14, %r22
	and %r22, %r29, %r9
	xor %r14, %r14, %r22
	and %r22, %r30, %r9
	xor %r14, %r14, %r22
	and %r15, %r25, %r10
	and %r22, %r26, %r9
	xor %r15, %r15, %r22
	xor %r15, %r15, %r28
	and %r22, %r29, %r10
	xor %r15, %r15, %r22
	xor %r15, %r15, %r30
	xor %r15, %r15, %r31
	or %r16, %r24, %r24
	and %r22, %r25, %r9
	xor %r16, %r16, %r22
	and %r22, %r26, %r10
	xor %r16, %r16, %r22
	and %r22, %r27, %r10
	xor %r16, %r16, %r22
	xor %r16, %r16, %r28
	xor %r16, %r16, %r30
	or %r17, %r24, %r24
	and %r22, %r25, %r10
	xor %r17, %r17, %r22
	and %r22, %r26, %r9
	xor %r17, %r17, %r22
	and %r22, %r27, %r10
	xor %r17, %r17, %r22
	xor %r17, %r17, %r28
	xor %r17, %r17, %r29
	xor %r17, %r17, %r30
	and %r22, %r31, %r9
	xor %r17, %r17, %r22
	and %r18, %r24, %r9
	and %r22, %r26, %r9
	xor %r18, %r18, %r22
	xor %r18, %r18, %r27
	and %r22, %r28, %r9
	xor %r18, %r18, %r22
	xor %r18, %r18, %r30
	and %r22, %r31, %r10
	xor %r18, %r18, %r22
	and %r19, %r24, %r9
	and %r22, %r25, %r9
	xor %r19, %r19, %r22
	xor %r19, %r19, %r27
	and %r22, %r28, %r10
	xor %r19, %r19, %r22
	xor %r19, %r19, %r29
	xor %r19, %r19, %r30
	and %r20, %r24, %r9
	and %r22, %r25, %r10
	xor %r20, %r20, %r22
	and %r22, %r26, %r10
	xor %r20, %r20, %r22
	and %r22, %r27, %r10
	xor %r20, %r20, %r22
	and %r22, %r28, %r9
	xor %r20, %r20, %r22
	and %r22, %r29, %r9
	xor %r20, %r20, %r22
	xor %r20, %r20, %r30
	and %r21, %r25, %r9
	xor %r21, %r21, %r27
	and %r22, %r30, %r9
	xor %r21, %r21, %r22
	and %r22, %r31, %r9
	xor %r21, %r21, %r22
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
	lis %r24, -12292
	ori %r24, %r24, 53244
	rldicr %r24, %r24, 32, 31
	oris %r24, %r24, 53244
	ori %r24, %r24, 53244
	lis %r25, 243
	ori %r25, %r25, 16371
	rldicr %r25, %r25, 32, 31
	oris %r25, %r25, 243
	ori %r25, %r25, 16371
	lis %r28, 16128
	ori %r28, %r28, 0
	rldicr %r28, %r28, 32, 31
	oris %r28, %r28, 16128
	ori %r28, %r28, 0
	lis %r26, 0
	ori %r26, %r26, 64719
	rldicr %r26, %r26, 32, 31
	oris %r26, %r26, 0
	ori %r26, %r26, 64719
	lis %r29, -817
	ori %r29, %r29, 0
	rldicr %r29, %r29, 32, 31
	oris %r29, %r29, 64719
	ori %r29, %r29, 0
	lis %r27, 0
	ori %r27, %r27, 63
	rldicr %r27, %r27, 32, 31
	oris %r27, %r27, 0
	ori %r27, %r27, 63
	lis %r30, -3265
	ori %r30, %r30, 62208
	rldicr %r30, %r30, 32, 31
	oris %r30, %r30, 62271
	ori %r30, %r30, 62208
	lis %r31, -6357
	ori %r31, %r31, 59179
	rldicr %r31, %r31, 32, 31
	oris %r31, %r31, 59179
	ori %r31, %r31, 59179
	and %r23, %r14, %r24
	rldicl %r22, %r14, 56, 0
	and %r22, %r22, %r25
	xor %r23, %r23, %r22
	rldicl %r22, %r14, 24, 0
	and %r22, %r22, %r28
	xor %r23, %r23, %r22
	rldicl %r22, %r14, 48, 0
	and %r22, %r22, %r26
	xor %r23, %r23, %r22
	rldicl %r22, %r14, 16, 0
	and %r22, %r22, %r29
	xor %r23, %r23, %r22
	rldicl %r22, %r14, 40, 0
	and %r22, %r22, %r27
	xor %r23, %r23, %r22
	rldicl %r22, %r14, 8, 0
	and %r22, %r22, %r30
	xor %r23, %r23, %r22
	xor %r23, %r23, %r31
	std %r23, 384(%r8)
	and %r23, %r15, %r24
	rldicl %r22, %r15, 56, 0
	and %r22, %r22, %r25
	xor %r23, %r23, %r22
	rldicl %r22, %r15, 24, 0
	and %r22, %r22, %r28
	xor %r23, %r23, %r22
	rldicl %r22, %r15, 48, 0
	and %r22, %r22, %r26
	xor %r23, %r23, %r22
	rldicl %r22, %r15, 16, 0
	and %r22, %r22, %r29
	xor %r23, %r23, %r22
	rldicl %r22, %r15, 40, 0
	and %r22, %r22, %r27
	xor %r23, %r23, %r22
	rldicl %r22, %r15, 8, 0
	and %r22, %r22, %r30
	xor %r23, %r23, %r22
	xor %r23, %r23, %r31
	std %r23, 392(%r8)
	and %r23, %r16, %r24
	rldicl %r22, %r16, 56, 0
	and %r22, %r22, %r25
	xor %r23, %r23, %r22
	rldicl %r22, %r16, 24, 0
	and %r22, %r22, %r28
	xor %r23, %r23, %r22
	rldicl %r22, %r16, 48, 0
	and %r22, %r22, %r26
	xor %r23, %r23, %r22
	rldicl %r22, %r16, 16, 0
	and %r22, %r22, %r29
	xor %r23, %r23, %r22
	rldicl %r22, %r16, 40, 0
	and %r22, %r22, %r27
	xor %r23, %r23, %r22
	rldicl %r22, %r16, 8, 0
	and %r22, %r22, %r30
	xor %r23, %r23, %r22
	xor %r23, %r23, %r31
	std %r23, 400(%r8)
	and %r23, %r17, %r24
	rldicl %r22, %r17, 56, 0
	and %r22, %r22, %r25
	xor %r23, %r23, %r22
	rldicl %r22, %r17, 24, 0
	and %r22, %r22, %r28
	xor %r23, %r23, %r22
	rldicl %r22, %r17, 48, 0
	and %r22, %r22, %r26
	xor %r23, %r23, %r22
	rldicl %r22, %r17, 16, 0
	and %r22, %r22, %r29
	xor %r23, %r23, %r22
	rldicl %r22, %r17, 40, 0
	and %r22, %r22, %r27
	xor %r23, %r23, %r22
	rldicl %r22, %r17, 8, 0
	and %r22, %r22, %r30
	xor %r23, %r23, %r22
	xor %r23, %r23, %r31
	std %r23, 408(%r8)
	and %r23, %r18, %r24
	rldicl %r22, %r18, 56, 0
	and %r22, %r22, %r25
	xor %r23, %r23, %r22
	rldicl %r22, %r18, 24, 0
	and %r22, %r22, %r28
	xor %r23, %r23, %r22
	rldicl %r22, %r18, 48, 0
	and %r22, %r22, %r26
	xor %r23, %r23, %r22
	rldicl %r22, %r18, 16, 0
	and %r22, %r22, %r29
	xor %r23, %r23, %r22
	rldicl %r22, %r18, 40, 0
	and %r22, %r22, %r27
	xor %r23, %r23, %r22
	rldicl %r22, %r18, 8, 0
	and %r22, %r22, %r30
	xor %r23, %r23, %r22
	xor %r23, %r23, %r31
	std %r23, 416(%r8)
	and %r23, %r19, %r24
	rldicl %r22, %r19, 56, 0
	and %r22, %r22, %r25
	xor %r23, %r23, %r22
	rldicl %r22, %r19, 24, 0
	and %r22, %r22, %r28
	xor %r23, %r23, %r22
	rldicl %r22, %r19, 48, 0
	and %r22, %r22, %r26
	xor %r23, %r23, %r22
	rldicl %r22, %r19, 16, 0
	and %r22, %r22, %r29
	xor %r23, %r23, %r22
	rldicl %r22, %r19, 40, 0
	and %r22, %r22, %r27
	xor %r23, %r23, %r22
	rldicl %r22, %r19, 8, 0
	and %r22, %r22, %r30
	xor %r23, %r23, %r22
	xor %r23, %r23, %r31
	std %r23, 424(%r8)
	and %r23, %r20, %r24
	rldicl %r22, %r20, 56, 0
	and %r22, %r22, %r25
	xor %r23, %r23, %r22
	rldicl %r22, %r20, 24, 0
	and %r22, %r22, %r28
	xor %r23, %r23, %r22
	rldicl %r22, %r20, 48, 0
	and %r22, %r22, %r26
	xor %r23, %r23, %r22
	rldicl %r22, %r20, 16, 0
	and %r22, %r22, %r29
	xor %r23, %r23, %r22
	rldicl %r22, %r20, 40, 0
	and %r22, %r22, %r27
	xor %r23, %r23, %r22
	rldicl %r22, %r20, 8, 0
	and %r22, %r22, %r30
	xor %r23, %r23, %r22
	xor %r23, %r23, %r31
	std %r23, 432(%r8)
	and %r23, %r21, %r24
	rldicl %r22, %r21, 56, 0
	and %r22, %r22, %r25
	xor %r23, %r23, %r22
	rldicl %r22, %r21, 24, 0
	and %r22, %r22, %r28
	xor %r23, %r23, %r22
	rldicl %r22, %r21, 48, 0
	and %r22, %r22, %r26
	xor %r23, %r23, %r22
	rldicl %r22, %r21, 16, 0
	and %r22, %r22, %r29
	xor %r23, %r23, %r22
	rldicl %r22, %r21, 40, 0
	and %r22, %r22, %r27
	xor %r23, %r23, %r22
	rldicl %r22, %r21, 8, 0
	and %r22, %r22, %r30
	xor %r23, %r23, %r22
	xor %r23, %r23, %r31
	std %r23, 440(%r8)
	lwz %r9, 384(%r8)
	stw %r9, 0(%r4)
	lwz %r9, 388(%r8)
	stw %r9, 4(%r4)
	lwz %r9, 392(%r8)
	stw %r9, 8(%r4)
	lwz %r9, 396(%r8)
	stw %r9, 12(%r4)
	lwz %r9, 400(%r8)
	stw %r9, 16(%r4)
	lwz %r9, 404(%r8)
	stw %r9, 20(%r4)
	lwz %r9, 408(%r8)
	stw %r9, 24(%r4)
	lwz %r9, 412(%r8)
	stw %r9, 28(%r4)
	lwz %r9, 416(%r8)
	stw %r9, 32(%r4)
	lwz %r9, 420(%r8)
	stw %r9, 36(%r4)
	lwz %r9, 424(%r8)
	stw %r9, 40(%r4)
	lwz %r9, 428(%r8)
	stw %r9, 44(%r4)
	lwz %r9, 432(%r8)
	stw %r9, 48(%r4)
	lwz %r9, 436(%r8)
	stw %r9, 52(%r4)
	lwz %r9, 440(%r8)
	stw %r9, 56(%r4)
	lwz %r9, 444(%r8)
	stw %r9, 60(%r4)
	addi %r4, %r4, 64
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 21f
	b 22f
21:
	lwz %r9, 448(%r8)
	stw %r9, 384(%r8)
	lwz %r9, 452(%r8)
	stw %r9, 388(%r8)
	lwz %r9, 456(%r8)
	stw %r9, 392(%r8)
	lwz %r9, 460(%r8)
	stw %r9, 396(%r8)
	lwz %r9, 464(%r8)
	stw %r9, 400(%r8)
	lwz %r9, 468(%r8)
	stw %r9, 404(%r8)
	lwz %r9, 472(%r8)
	stw %r9, 408(%r8)
	lwz %r9, 476(%r8)
	stw %r9, 412(%r8)
	lwz %r9, 480(%r8)
	stw %r9, 416(%r8)
	lwz %r9, 484(%r8)
	stw %r9, 420(%r8)
	lwz %r9, 488(%r8)
	stw %r9, 424(%r8)
	lwz %r9, 492(%r8)
	stw %r9, 428(%r8)
	lwz %r9, 496(%r8)
	stw %r9, 432(%r8)
	lwz %r9, 500(%r8)
	stw %r9, 436(%r8)
	lwz %r9, 504(%r8)
	stw %r9, 440(%r8)
	lwz %r9, 508(%r8)
	stw %r9, 444(%r8)
22:
	cmpldi %cr0, %r6, 0
	bne %cr0, 20b
	ld %r14, 896(%r8)
	ld %r15, 904(%r8)
	ld %r16, 912(%r8)
	ld %r17, 920(%r8)
	ld %r18, 928(%r8)
	ld %r19, 936(%r8)
	ld %r20, 944(%r8)
	ld %r21, 952(%r8)
	ld %r22, 960(%r8)
	ld %r23, 968(%r8)
	ld %r24, 976(%r8)
	ld %r25, 984(%r8)
	ld %r26, 992(%r8)
	ld %r27, 1000(%r8)
	ld %r28, 1008(%r8)
	ld %r29, 1016(%r8)
	ld %r30, 1024(%r8)
	ld %r31, 1032(%r8)
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
	addi %r1, %r1, 1072
	blr

vg_seed_ecb_encrypt:
	stdu %r1, -1120(%r1)
	addi %r6, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	bl {vg_seed_encrypt_blocks}
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
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
	addi %r1, %r1, 1120
	blr

vg_seed_ecb_decrypt:
	stdu %r1, -1120(%r1)
	addi %r6, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	bl {vg_seed_decrypt_blocks}
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
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
	addi %r1, %r1, 1120
	blr
