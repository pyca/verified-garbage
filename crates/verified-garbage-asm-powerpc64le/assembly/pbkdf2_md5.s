// The functions of `src/pbkdf2_md5.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_md5:
	stdu %r1, -1056(%r1)
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
	addi %r3, %r21, 432
	addi %r4, %r21, 512
	bl {vg_hmac_md5_init}
	li %r12, 1
	li %r11, 704
	stwbrx %r12, %r21, %r11
	cmpldi %cr0, %r24, 0
	beq %cr0, 20f
22:
	lwz %r8, 432(%r21)
	stw %r8, 592(%r21)
	lwz %r8, 436(%r21)
	stw %r8, 596(%r21)
	lwz %r8, 440(%r21)
	stw %r8, 600(%r21)
	lwz %r8, 444(%r21)
	stw %r8, 604(%r21)
	lwz %r8, 448(%r21)
	stw %r8, 608(%r21)
	lwz %r8, 452(%r21)
	stw %r8, 612(%r21)
	lwz %r8, 456(%r21)
	stw %r8, 616(%r21)
	lwz %r8, 460(%r21)
	stw %r8, 620(%r21)
	lwz %r8, 464(%r21)
	stw %r8, 624(%r21)
	lwz %r8, 468(%r21)
	stw %r8, 628(%r21)
	lwz %r8, 472(%r21)
	stw %r8, 632(%r21)
	lwz %r8, 476(%r21)
	stw %r8, 636(%r21)
	lwz %r8, 480(%r21)
	stw %r8, 640(%r21)
	lwz %r8, 484(%r21)
	stw %r8, 644(%r21)
	lwz %r8, 488(%r21)
	stw %r8, 648(%r21)
	lwz %r8, 492(%r21)
	stw %r8, 652(%r21)
	lwz %r8, 496(%r21)
	stw %r8, 656(%r21)
	lwz %r8, 500(%r21)
	stw %r8, 660(%r21)
	lwz %r8, 504(%r21)
	stw %r8, 664(%r21)
	lwz %r8, 508(%r21)
	stw %r8, 668(%r21)
	addi %r3, %r21, 592
	li %r4, 64
	addi %r5, %r25, 0
	addi %r6, %r20, 0
	addi %r7, %r21, 48
	bl {vg_md5_update_scratch}
	addi %r3, %r21, 592
	addi %r4, %r20, 64
	addi %r5, %r21, 704
	li %r6, 4
	addi %r7, %r21, 48
	bl {vg_md5_update_scratch}
	addi %r3, %r21, 592
	addi %r4, %r21, 512
	addi %r5, %r20, 68
	addi %r6, %r21, 672
	addi %r7, %r21, 48
	bl {vg_hmac_md5_finalize_scratch}
	lwz %r8, 672(%r21)
	stw %r8, 688(%r21)
	lwz %r8, 676(%r21)
	stw %r8, 692(%r21)
	lwz %r8, 680(%r21)
	stw %r8, 696(%r21)
	lwz %r8, 684(%r21)
	stw %r8, 700(%r21)
	addi %r3, %r21, 432
	addi %r4, %r21, 672
	addi %r5, %r22, -1
	addi %r6, %r21, 688
	addi %r7, %r21, 48
	bl {vg_pbkdf2_hmac_md5_iterate}
	addi %r12, %r24, -16
	rldicl %r12, %r12, 1, 63
	addi %r9, %r24, 0
	cmpldi %cr0, %r12, 0
	bne %cr0, 23f
	li %r9, 16
	b 24f
23:
24:
	li %r8, 0
25:
	add %r11, %r21, %r8
	lbz %r12, 688(%r11)
	add %r11, %r23, %r8
	stb %r12, 0(%r11)
	addi %r8, %r8, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 25b
	add %r23, %r23, %r8
	subf %r24, %r8, %r24
	li %r11, 704
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
	addi %r1, %r1, 1056
	blr
