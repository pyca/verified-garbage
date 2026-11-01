// The functions of `src/internal/vg_seed_encrypt_blocks.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_seed_encrypt_blocks:
	or %r8, %r6, %r6
	addi %r3, %r3, 0
	cmpldi %cr0, %r5, 0
	beq %cr0, 20f
22:
	rldicl %r10, %r5, 60, 4
	cmpldi %cr0, %r10, 0
	bne %cr0, 23f
	or %r10, %r5, %r5
	b 24f
23:
	li %r10, 16
24:
	or %r6, %r4, %r4
	or %r7, %r8, %r8
25:
	li %r9, 0
	lwbrx %r9, %r6, %r9
	stw %r9, 640(%r7)
	li %r9, 4
	lwbrx %r9, %r6, %r9
	stw %r9, 704(%r7)
	li %r9, 8
	lwbrx %r9, %r6, %r9
	stw %r9, 768(%r7)
	li %r9, 12
	lwbrx %r9, %r6, %r9
	stw %r9, 832(%r7)
	addi %r6, %r6, 16
	addi %r7, %r7, 4
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 25b
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
	li %r7, 16
26:
	lwz %r11, 0(%r3)
	lwz %r12, 4(%r3)
	lwz %r9, 768(%r8)
	xor %r9, %r9, %r11
	stw %r9, 448(%r8)
	lwz %r10, 832(%r8)
	xor %r9, %r9, %r10
	xor %r9, %r9, %r12
	stw %r9, 384(%r8)
	lwz %r9, 772(%r8)
	xor %r9, %r9, %r11
	stw %r9, 452(%r8)
	lwz %r10, 836(%r8)
	xor %r9, %r9, %r10
	xor %r9, %r9, %r12
	stw %r9, 388(%r8)
	lwz %r9, 776(%r8)
	xor %r9, %r9, %r11
	stw %r9, 456(%r8)
	lwz %r10, 840(%r8)
	xor %r9, %r9, %r10
	xor %r9, %r9, %r12
	stw %r9, 392(%r8)
	lwz %r9, 780(%r8)
	xor %r9, %r9, %r11
	stw %r9, 460(%r8)
	lwz %r10, 844(%r8)
	xor %r9, %r9, %r10
	xor %r9, %r9, %r12
	stw %r9, 396(%r8)
	lwz %r9, 784(%r8)
	xor %r9, %r9, %r11
	stw %r9, 464(%r8)
	lwz %r10, 848(%r8)
	xor %r9, %r9, %r10
	xor %r9, %r9, %r12
	stw %r9, 400(%r8)
	lwz %r9, 788(%r8)
	xor %r9, %r9, %r11
	stw %r9, 468(%r8)
	lwz %r10, 852(%r8)
	xor %r9, %r9, %r10
	xor %r9, %r9, %r12
	stw %r9, 404(%r8)
	lwz %r9, 792(%r8)
	xor %r9, %r9, %r11
	stw %r9, 472(%r8)
	lwz %r10, 856(%r8)
	xor %r9, %r9, %r10
	xor %r9, %r9, %r12
	stw %r9, 408(%r8)
	lwz %r9, 796(%r8)
	xor %r9, %r9, %r11
	stw %r9, 476(%r8)
	lwz %r10, 860(%r8)
	xor %r9, %r9, %r10
	xor %r9, %r9, %r12
	stw %r9, 412(%r8)
	lwz %r9, 800(%r8)
	xor %r9, %r9, %r11
	stw %r9, 480(%r8)
	lwz %r10, 864(%r8)
	xor %r9, %r9, %r10
	xor %r9, %r9, %r12
	stw %r9, 416(%r8)
	lwz %r9, 804(%r8)
	xor %r9, %r9, %r11
	stw %r9, 484(%r8)
	lwz %r10, 868(%r8)
	xor %r9, %r9, %r10
	xor %r9, %r9, %r12
	stw %r9, 420(%r8)
	lwz %r9, 808(%r8)
	xor %r9, %r9, %r11
	stw %r9, 488(%r8)
	lwz %r10, 872(%r8)
	xor %r9, %r9, %r10
	xor %r9, %r9, %r12
	stw %r9, 424(%r8)
	lwz %r9, 812(%r8)
	xor %r9, %r9, %r11
	stw %r9, 492(%r8)
	lwz %r10, 876(%r8)
	xor %r9, %r9, %r10
	xor %r9, %r9, %r12
	stw %r9, 428(%r8)
	lwz %r9, 816(%r8)
	xor %r9, %r9, %r11
	stw %r9, 496(%r8)
	lwz %r10, 880(%r8)
	xor %r9, %r9, %r10
	xor %r9, %r9, %r12
	stw %r9, 432(%r8)
	lwz %r9, 820(%r8)
	xor %r9, %r9, %r11
	stw %r9, 500(%r8)
	lwz %r10, 884(%r8)
	xor %r9, %r9, %r10
	xor %r9, %r9, %r12
	stw %r9, 436(%r8)
	lwz %r9, 824(%r8)
	xor %r9, %r9, %r11
	stw %r9, 504(%r8)
	lwz %r10, 888(%r8)
	xor %r9, %r9, %r10
	xor %r9, %r9, %r12
	stw %r9, 440(%r8)
	lwz %r9, 828(%r8)
	xor %r9, %r9, %r11
	stw %r9, 508(%r8)
	lwz %r10, 892(%r8)
	xor %r9, %r9, %r10
	xor %r9, %r9, %r12
	stw %r9, 444(%r8)
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
	stw %r9, 512(%r8)
	lwz %r10, 448(%r8)
	add %r9, %r9, %r10
	stw %r9, 384(%r8)
	lwz %r9, 388(%r8)
	stw %r9, 516(%r8)
	lwz %r10, 452(%r8)
	add %r9, %r9, %r10
	stw %r9, 388(%r8)
	lwz %r9, 392(%r8)
	stw %r9, 520(%r8)
	lwz %r10, 456(%r8)
	add %r9, %r9, %r10
	stw %r9, 392(%r8)
	lwz %r9, 396(%r8)
	stw %r9, 524(%r8)
	lwz %r10, 460(%r8)
	add %r9, %r9, %r10
	stw %r9, 396(%r8)
	lwz %r9, 400(%r8)
	stw %r9, 528(%r8)
	lwz %r10, 464(%r8)
	add %r9, %r9, %r10
	stw %r9, 400(%r8)
	lwz %r9, 404(%r8)
	stw %r9, 532(%r8)
	lwz %r10, 468(%r8)
	add %r9, %r9, %r10
	stw %r9, 404(%r8)
	lwz %r9, 408(%r8)
	stw %r9, 536(%r8)
	lwz %r10, 472(%r8)
	add %r9, %r9, %r10
	stw %r9, 408(%r8)
	lwz %r9, 412(%r8)
	stw %r9, 540(%r8)
	lwz %r10, 476(%r8)
	add %r9, %r9, %r10
	stw %r9, 412(%r8)
	lwz %r9, 416(%r8)
	stw %r9, 544(%r8)
	lwz %r10, 480(%r8)
	add %r9, %r9, %r10
	stw %r9, 416(%r8)
	lwz %r9, 420(%r8)
	stw %r9, 548(%r8)
	lwz %r10, 484(%r8)
	add %r9, %r9, %r10
	stw %r9, 420(%r8)
	lwz %r9, 424(%r8)
	stw %r9, 552(%r8)
	lwz %r10, 488(%r8)
	add %r9, %r9, %r10
	stw %r9, 424(%r8)
	lwz %r9, 428(%r8)
	stw %r9, 556(%r8)
	lwz %r10, 492(%r8)
	add %r9, %r9, %r10
	stw %r9, 428(%r8)
	lwz %r9, 432(%r8)
	stw %r9, 560(%r8)
	lwz %r10, 496(%r8)
	add %r9, %r9, %r10
	stw %r9, 432(%r8)
	lwz %r9, 436(%r8)
	stw %r9, 564(%r8)
	lwz %r10, 500(%r8)
	add %r9, %r9, %r10
	stw %r9, 436(%r8)
	lwz %r9, 440(%r8)
	stw %r9, 568(%r8)
	lwz %r10, 504(%r8)
	add %r9, %r9, %r10
	stw %r9, 440(%r8)
	lwz %r9, 444(%r8)
	stw %r9, 572(%r8)
	lwz %r10, 508(%r8)
	add %r9, %r9, %r10
	stw %r9, 444(%r8)
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
	stw %r9, 576(%r8)
	lwz %r10, 512(%r8)
	add %r9, %r9, %r10
	stw %r9, 384(%r8)
	lwz %r9, 388(%r8)
	stw %r9, 580(%r8)
	lwz %r10, 516(%r8)
	add %r9, %r9, %r10
	stw %r9, 388(%r8)
	lwz %r9, 392(%r8)
	stw %r9, 584(%r8)
	lwz %r10, 520(%r8)
	add %r9, %r9, %r10
	stw %r9, 392(%r8)
	lwz %r9, 396(%r8)
	stw %r9, 588(%r8)
	lwz %r10, 524(%r8)
	add %r9, %r9, %r10
	stw %r9, 396(%r8)
	lwz %r9, 400(%r8)
	stw %r9, 592(%r8)
	lwz %r10, 528(%r8)
	add %r9, %r9, %r10
	stw %r9, 400(%r8)
	lwz %r9, 404(%r8)
	stw %r9, 596(%r8)
	lwz %r10, 532(%r8)
	add %r9, %r9, %r10
	stw %r9, 404(%r8)
	lwz %r9, 408(%r8)
	stw %r9, 600(%r8)
	lwz %r10, 536(%r8)
	add %r9, %r9, %r10
	stw %r9, 408(%r8)
	lwz %r9, 412(%r8)
	stw %r9, 604(%r8)
	lwz %r10, 540(%r8)
	add %r9, %r9, %r10
	stw %r9, 412(%r8)
	lwz %r9, 416(%r8)
	stw %r9, 608(%r8)
	lwz %r10, 544(%r8)
	add %r9, %r9, %r10
	stw %r9, 416(%r8)
	lwz %r9, 420(%r8)
	stw %r9, 612(%r8)
	lwz %r10, 548(%r8)
	add %r9, %r9, %r10
	stw %r9, 420(%r8)
	lwz %r9, 424(%r8)
	stw %r9, 616(%r8)
	lwz %r10, 552(%r8)
	add %r9, %r9, %r10
	stw %r9, 424(%r8)
	lwz %r9, 428(%r8)
	stw %r9, 620(%r8)
	lwz %r10, 556(%r8)
	add %r9, %r9, %r10
	stw %r9, 428(%r8)
	lwz %r9, 432(%r8)
	stw %r9, 624(%r8)
	lwz %r10, 560(%r8)
	add %r9, %r9, %r10
	stw %r9, 432(%r8)
	lwz %r9, 436(%r8)
	stw %r9, 628(%r8)
	lwz %r10, 564(%r8)
	add %r9, %r9, %r10
	stw %r9, 436(%r8)
	lwz %r9, 440(%r8)
	stw %r9, 632(%r8)
	lwz %r10, 568(%r8)
	add %r9, %r9, %r10
	stw %r9, 440(%r8)
	lwz %r9, 444(%r8)
	stw %r9, 636(%r8)
	lwz %r10, 572(%r8)
	add %r9, %r9, %r10
	stw %r9, 444(%r8)
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
	lwz %r10, 704(%r8)
	xor %r10, %r10, %r9
	stw %r10, 704(%r8)
	lwz %r10, 576(%r8)
	add %r9, %r9, %r10
	lwz %r10, 640(%r8)
	xor %r9, %r9, %r10
	stw %r9, 640(%r8)
	lwz %r9, 388(%r8)
	lwz %r10, 708(%r8)
	xor %r10, %r10, %r9
	stw %r10, 708(%r8)
	lwz %r10, 580(%r8)
	add %r9, %r9, %r10
	lwz %r10, 644(%r8)
	xor %r9, %r9, %r10
	stw %r9, 644(%r8)
	lwz %r9, 392(%r8)
	lwz %r10, 712(%r8)
	xor %r10, %r10, %r9
	stw %r10, 712(%r8)
	lwz %r10, 584(%r8)
	add %r9, %r9, %r10
	lwz %r10, 648(%r8)
	xor %r9, %r9, %r10
	stw %r9, 648(%r8)
	lwz %r9, 396(%r8)
	lwz %r10, 716(%r8)
	xor %r10, %r10, %r9
	stw %r10, 716(%r8)
	lwz %r10, 588(%r8)
	add %r9, %r9, %r10
	lwz %r10, 652(%r8)
	xor %r9, %r9, %r10
	stw %r9, 652(%r8)
	lwz %r9, 400(%r8)
	lwz %r10, 720(%r8)
	xor %r10, %r10, %r9
	stw %r10, 720(%r8)
	lwz %r10, 592(%r8)
	add %r9, %r9, %r10
	lwz %r10, 656(%r8)
	xor %r9, %r9, %r10
	stw %r9, 656(%r8)
	lwz %r9, 404(%r8)
	lwz %r10, 724(%r8)
	xor %r10, %r10, %r9
	stw %r10, 724(%r8)
	lwz %r10, 596(%r8)
	add %r9, %r9, %r10
	lwz %r10, 660(%r8)
	xor %r9, %r9, %r10
	stw %r9, 660(%r8)
	lwz %r9, 408(%r8)
	lwz %r10, 728(%r8)
	xor %r10, %r10, %r9
	stw %r10, 728(%r8)
	lwz %r10, 600(%r8)
	add %r9, %r9, %r10
	lwz %r10, 664(%r8)
	xor %r9, %r9, %r10
	stw %r9, 664(%r8)
	lwz %r9, 412(%r8)
	lwz %r10, 732(%r8)
	xor %r10, %r10, %r9
	stw %r10, 732(%r8)
	lwz %r10, 604(%r8)
	add %r9, %r9, %r10
	lwz %r10, 668(%r8)
	xor %r9, %r9, %r10
	stw %r9, 668(%r8)
	lwz %r9, 416(%r8)
	lwz %r10, 736(%r8)
	xor %r10, %r10, %r9
	stw %r10, 736(%r8)
	lwz %r10, 608(%r8)
	add %r9, %r9, %r10
	lwz %r10, 672(%r8)
	xor %r9, %r9, %r10
	stw %r9, 672(%r8)
	lwz %r9, 420(%r8)
	lwz %r10, 740(%r8)
	xor %r10, %r10, %r9
	stw %r10, 740(%r8)
	lwz %r10, 612(%r8)
	add %r9, %r9, %r10
	lwz %r10, 676(%r8)
	xor %r9, %r9, %r10
	stw %r9, 676(%r8)
	lwz %r9, 424(%r8)
	lwz %r10, 744(%r8)
	xor %r10, %r10, %r9
	stw %r10, 744(%r8)
	lwz %r10, 616(%r8)
	add %r9, %r9, %r10
	lwz %r10, 680(%r8)
	xor %r9, %r9, %r10
	stw %r9, 680(%r8)
	lwz %r9, 428(%r8)
	lwz %r10, 748(%r8)
	xor %r10, %r10, %r9
	stw %r10, 748(%r8)
	lwz %r10, 620(%r8)
	add %r9, %r9, %r10
	lwz %r10, 684(%r8)
	xor %r9, %r9, %r10
	stw %r9, 684(%r8)
	lwz %r9, 432(%r8)
	lwz %r10, 752(%r8)
	xor %r10, %r10, %r9
	stw %r10, 752(%r8)
	lwz %r10, 624(%r8)
	add %r9, %r9, %r10
	lwz %r10, 688(%r8)
	xor %r9, %r9, %r10
	stw %r9, 688(%r8)
	lwz %r9, 436(%r8)
	lwz %r10, 756(%r8)
	xor %r10, %r10, %r9
	stw %r10, 756(%r8)
	lwz %r10, 628(%r8)
	add %r9, %r9, %r10
	lwz %r10, 692(%r8)
	xor %r9, %r9, %r10
	stw %r9, 692(%r8)
	lwz %r9, 440(%r8)
	lwz %r10, 760(%r8)
	xor %r10, %r10, %r9
	stw %r10, 760(%r8)
	lwz %r10, 632(%r8)
	add %r9, %r9, %r10
	lwz %r10, 696(%r8)
	xor %r9, %r9, %r10
	stw %r9, 696(%r8)
	lwz %r9, 444(%r8)
	lwz %r10, 764(%r8)
	xor %r10, %r10, %r9
	stw %r10, 764(%r8)
	lwz %r10, 636(%r8)
	add %r9, %r9, %r10
	lwz %r10, 700(%r8)
	xor %r9, %r9, %r10
	stw %r9, 700(%r8)
	ld %r9, 640(%r8)
	ld %r10, 768(%r8)
	std %r10, 640(%r8)
	std %r9, 768(%r8)
	ld %r9, 648(%r8)
	ld %r10, 776(%r8)
	std %r10, 648(%r8)
	std %r9, 776(%r8)
	ld %r9, 656(%r8)
	ld %r10, 784(%r8)
	std %r10, 656(%r8)
	std %r9, 784(%r8)
	ld %r9, 664(%r8)
	ld %r10, 792(%r8)
	std %r10, 664(%r8)
	std %r9, 792(%r8)
	ld %r9, 672(%r8)
	ld %r10, 800(%r8)
	std %r10, 672(%r8)
	std %r9, 800(%r8)
	ld %r9, 680(%r8)
	ld %r10, 808(%r8)
	std %r10, 680(%r8)
	std %r9, 808(%r8)
	ld %r9, 688(%r8)
	ld %r10, 816(%r8)
	std %r10, 688(%r8)
	std %r9, 816(%r8)
	ld %r9, 696(%r8)
	ld %r10, 824(%r8)
	std %r10, 696(%r8)
	std %r9, 824(%r8)
	ld %r9, 704(%r8)
	ld %r10, 832(%r8)
	std %r10, 704(%r8)
	std %r9, 832(%r8)
	ld %r9, 712(%r8)
	ld %r10, 840(%r8)
	std %r10, 712(%r8)
	std %r9, 840(%r8)
	ld %r9, 720(%r8)
	ld %r10, 848(%r8)
	std %r10, 720(%r8)
	std %r9, 848(%r8)
	ld %r9, 728(%r8)
	ld %r10, 856(%r8)
	std %r10, 728(%r8)
	std %r9, 856(%r8)
	ld %r9, 736(%r8)
	ld %r10, 864(%r8)
	std %r10, 736(%r8)
	std %r9, 864(%r8)
	ld %r9, 744(%r8)
	ld %r10, 872(%r8)
	std %r10, 744(%r8)
	std %r9, 872(%r8)
	ld %r9, 752(%r8)
	ld %r10, 880(%r8)
	std %r10, 752(%r8)
	std %r9, 880(%r8)
	ld %r9, 760(%r8)
	ld %r10, 888(%r8)
	std %r10, 760(%r8)
	std %r9, 888(%r8)
	addi %r3, %r3, 8
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 26b
	addi %r3, %r3, -128
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
	rldicl %r10, %r5, 60, 4
	cmpldi %cr0, %r10, 0
	bne %cr0, 27f
	or %r10, %r5, %r5
	b 28f
27:
	li %r10, 16
28:
	or %r6, %r4, %r4
	or %r7, %r8, %r8
29:
	li %r9, 768
	lwbrx %r9, %r7, %r9
	stw %r9, 0(%r6)
	li %r9, 832
	lwbrx %r9, %r7, %r9
	stw %r9, 4(%r6)
	li %r9, 640
	lwbrx %r9, %r7, %r9
	stw %r9, 8(%r6)
	li %r9, 704
	lwbrx %r9, %r7, %r9
	stw %r9, 12(%r6)
	addi %r6, %r6, 16
	addi %r7, %r7, 4
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 29b
	rldicl %r10, %r5, 60, 4
	cmpldi %cr0, %r10, 0
	bne %cr0, 210f
	or %r10, %r5, %r5
	b 211f
210:
	li %r10, 16
211:
	or %r4, %r6, %r6
	subf %r5, %r10, %r5
	cmpldi %cr0, %r5, 0
	bne %cr0, 22b
	b 21f
20:
21:
	blr
