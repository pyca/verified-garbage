// The functions of `src/pbkdf2_sha1.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

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
