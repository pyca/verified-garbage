// The functions of `src/pbkdf2_sha1.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha1_iterate:
	mflr %r0
	rldicr %r5, %r5, 32, 31
	rldicl %r5, %r5, 32, 32
	std %r26, 112(%r7)
	std %r27, 120(%r7)
	std %r28, 128(%r7)
	std %r29, 136(%r7)
	std %r30, 144(%r7)
	std %r31, 152(%r7)
	std %r0, 160(%r7)
	addi %r26, %r7, 168
	addi %r27, %r7, 0
	addi %r28, %r7, 188
	addi %r30, %r6, 0
	addi %r31, %r5, 0
	lwz %r8, 0(%r4)
	stw %r8, 0(%r28)
	lwz %r8, 4(%r4)
	stw %r8, 4(%r28)
	lwz %r8, 8(%r4)
	stw %r8, 8(%r28)
	lwz %r8, 12(%r4)
	stw %r8, 12(%r28)
	lwz %r8, 16(%r4)
	stw %r8, 16(%r28)
	li %r8, 128
	stw %r8, 20(%r28)
	li %r8, 0
	stw %r8, 24(%r28)
	stw %r8, 28(%r28)
	stw %r8, 32(%r28)
	stw %r8, 36(%r28)
	stw %r8, 40(%r28)
	stw %r8, 44(%r28)
	stw %r8, 48(%r28)
	stw %r8, 52(%r28)
	li %r29, 84
	add %r8, %r29, %r29
	add %r8, %r8, %r8
	add %r8, %r8, %r8
	li %r11, 76
	stdbrx %r8, %r26, %r11
	addi %r29, %r3, 0
	cmpldi %cr0, %r31, 0
	beq %cr0, 20f
22:
	lwz %r8, 0(%r29)
	stw %r8, 0(%r26)
	lwz %r8, 4(%r29)
	stw %r8, 4(%r26)
	lwz %r8, 8(%r29)
	stw %r8, 8(%r26)
	lwz %r8, 12(%r29)
	stw %r8, 12(%r26)
	lwz %r8, 16(%r29)
	stw %r8, 16(%r26)
	addi %r4, %r28, 0
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha1_compress}
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 84(%r29)
	stw %r8, 0(%r26)
	lwz %r8, 88(%r29)
	stw %r8, 4(%r26)
	lwz %r8, 92(%r29)
	stw %r8, 8(%r26)
	lwz %r8, 96(%r29)
	stw %r8, 12(%r26)
	lwz %r8, 100(%r29)
	stw %r8, 16(%r26)
	addi %r4, %r28, 0
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha1_compress}
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 0(%r28)
	lwz %r9, 0(%r30)
	xor %r8, %r8, %r9
	stw %r8, 0(%r30)
	lwz %r8, 4(%r28)
	lwz %r9, 4(%r30)
	xor %r8, %r8, %r9
	stw %r8, 4(%r30)
	lwz %r8, 8(%r28)
	lwz %r9, 8(%r30)
	xor %r8, %r8, %r9
	stw %r8, 8(%r30)
	lwz %r8, 12(%r28)
	lwz %r9, 12(%r30)
	xor %r8, %r8, %r9
	stw %r8, 12(%r30)
	lwz %r8, 16(%r28)
	lwz %r9, 16(%r30)
	xor %r8, %r8, %r9
	stw %r8, 16(%r30)
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r0, 160(%r27)
	ld %r26, 112(%r27)
	ld %r28, 128(%r27)
	ld %r29, 136(%r27)
	ld %r30, 144(%r27)
	ld %r31, 152(%r27)
	ld %r27, 120(%r27)
	mtlr %r0
	blr

vg_pbkdf2_hmac_sha1:
	stdu %r1, -1152(%r1)
	addi %r10, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r20, 0(%r10)
	std %r21, 8(%r10)
	std %r22, 16(%r10)
	std %r23, 24(%r10)
	std %r24, 32(%r10)
	std %r25, 40(%r10)
	addi %r21, %r10, 0
	addi %r20, %r6, 0
	addi %r22, %r7, 0
	addi %r23, %r8, 0
	addi %r24, %r9, 0
	addi %r25, %r5, 0
	addi %r5, %r3, 0
	addi %r6, %r4, 0
	addi %r3, %r21, 496
	addi %r4, %r21, 580
	bl {vg_hmac_sha1_init}
	li %r12, 1
	li %r11, 788
	stwbrx %r12, %r21, %r11
	cmpldi %cr0, %r24, 0
	beq %cr0, 20f
22:
	lwz %r8, 496(%r21)
	stw %r8, 664(%r21)
	lwz %r8, 500(%r21)
	stw %r8, 668(%r21)
	lwz %r8, 504(%r21)
	stw %r8, 672(%r21)
	lwz %r8, 508(%r21)
	stw %r8, 676(%r21)
	lwz %r8, 512(%r21)
	stw %r8, 680(%r21)
	lwz %r8, 516(%r21)
	stw %r8, 684(%r21)
	lwz %r8, 520(%r21)
	stw %r8, 688(%r21)
	lwz %r8, 524(%r21)
	stw %r8, 692(%r21)
	lwz %r8, 528(%r21)
	stw %r8, 696(%r21)
	lwz %r8, 532(%r21)
	stw %r8, 700(%r21)
	lwz %r8, 536(%r21)
	stw %r8, 704(%r21)
	lwz %r8, 540(%r21)
	stw %r8, 708(%r21)
	lwz %r8, 544(%r21)
	stw %r8, 712(%r21)
	lwz %r8, 548(%r21)
	stw %r8, 716(%r21)
	lwz %r8, 552(%r21)
	stw %r8, 720(%r21)
	lwz %r8, 556(%r21)
	stw %r8, 724(%r21)
	lwz %r8, 560(%r21)
	stw %r8, 728(%r21)
	lwz %r8, 564(%r21)
	stw %r8, 732(%r21)
	lwz %r8, 568(%r21)
	stw %r8, 736(%r21)
	lwz %r8, 572(%r21)
	stw %r8, 740(%r21)
	lwz %r8, 576(%r21)
	stw %r8, 744(%r21)
	addi %r3, %r21, 664
	li %r4, 64
	addi %r5, %r25, 0
	addi %r6, %r20, 0
	addi %r7, %r21, 48
	bl {vg_sha1_update_scratch}
	addi %r3, %r21, 664
	addi %r4, %r20, 64
	addi %r5, %r21, 788
	li %r6, 4
	addi %r7, %r21, 48
	bl {vg_sha1_update_scratch}
	addi %r3, %r21, 664
	addi %r4, %r21, 580
	addi %r5, %r20, 68
	addi %r6, %r21, 748
	addi %r7, %r21, 48
	bl {vg_hmac_sha1_finalize_scratch}
	lwz %r8, 748(%r21)
	stw %r8, 768(%r21)
	lwz %r8, 752(%r21)
	stw %r8, 772(%r21)
	lwz %r8, 756(%r21)
	stw %r8, 776(%r21)
	lwz %r8, 760(%r21)
	stw %r8, 780(%r21)
	lwz %r8, 764(%r21)
	stw %r8, 784(%r21)
	addi %r3, %r21, 496
	addi %r4, %r21, 748
	addi %r5, %r22, -1
	addi %r6, %r21, 768
	addi %r7, %r21, 48
	bl {vg_pbkdf2_hmac_sha1_iterate}
	addi %r12, %r24, -20
	rldicl %r12, %r12, 1, 63
	addi %r9, %r24, 0
	cmpldi %cr0, %r12, 0
	bne %cr0, 23f
	li %r9, 20
	b 24f
23:
24:
	li %r8, 0
25:
	add %r11, %r21, %r8
	lbz %r12, 768(%r11)
	add %r11, %r23, %r8
	stb %r12, 0(%r11)
	addi %r8, %r8, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 25b
	add %r23, %r23, %r8
	subf %r24, %r8, %r24
	li %r11, 788
	lwbrx %r12, %r21, %r11
	addi %r12, %r12, 1
	stwbrx %r12, %r21, %r11
	cmpldi %cr0, %r24, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r20, 0(%r21)
	ld %r22, 16(%r21)
	ld %r23, 24(%r21)
	ld %r24, 32(%r21)
	ld %r25, 40(%r21)
	ld %r21, 8(%r21)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 1152
	blr
