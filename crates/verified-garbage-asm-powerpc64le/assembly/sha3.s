// The functions of `src/sha3.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha3_224_update:
	addi %r8, %r7, 0
	addi %r7, %r6, 0
	addi %r6, %r5, 0
	addi %r5, %r4, 0
	li %r4, 144
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 512(%r8)
	std %r27, 520(%r8)
	std %r28, 528(%r8)
	std %r29, 536(%r8)
	std %r30, 544(%r8)
	std %r31, 552(%r8)
	addi %r26, %r3, 0
	addi %r27, %r8, 0
	addi %r28, %r4, 0
	addi %r29, %r5, 0
	addi %r30, %r6, 0
	addi %r31, %r7, 0
	cmpldi %cr0, %r31, 0
	beq %cr0, 20f
22:
	li %r10, 7
	and %r10, %r29, %r10
	addi %r11, %r31, -8
	rldicl %r11, %r11, 1, 63
	or %r10, %r10, %r11
	cmpldi %cr0, %r10, 0
	beq %cr0, 23f
	lbz %r9, 0(%r30)
	add %r10, %r26, %r29
	lbz %r11, 0(%r10)
	xor %r9, %r9, %r11
	stb %r9, 0(%r10)
	addi %r30, %r30, 1
	addi %r29, %r29, 1
	addi %r31, %r31, -1
	subf %r9, %r28, %r29
	b 24f
23:
	ld %r9, 0(%r30)
	add %r10, %r26, %r29
	ld %r11, 0(%r10)
	xor %r9, %r9, %r11
	std %r9, 0(%r10)
	addi %r30, %r30, 8
	addi %r29, %r29, 8
	addi %r31, %r31, -8
	subf %r9, %r28, %r29
24:
	cmpldi %cr0, %r9, 0
	beq %cr0, 25f
	b 26f
25:
	li %r29, 0
	addi %r3, %r26, 0
	addi %r4, %r27, 0
	bl {vg_keccak_f1600}
	addi %r26, %r3, 0
	addi %r27, %r4, 0
26:
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	b 21f
20:
21:
	addi %r3, %r29, 0
	ld %r26, 512(%r27)
	ld %r28, 528(%r27)
	ld %r29, 536(%r27)
	ld %r30, 544(%r27)
	ld %r31, 552(%r27)
	ld %r27, 520(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	li %r0, 0
	stdu %r1, -48(%r1)
	addi %r12, %r1, 32
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	addi %r1, %r1, 48
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	addc %r0, %r0, %r0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
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

vg_sha3_224_finalize:
	stdu %r1, -704(%r1)
	addi %r6, %r1, 32
	mflr %r0
	std %r0, 664(%r6)
	std %r29, 640(%r6)
	std %r30, 648(%r6)
	std %r31, 656(%r6)
	addi %r29, %r3, 0
	addi %r30, %r5, 0
	addi %r31, %r6, 0
	addi %r5, %r4, 0
	li %r4, 144
	li %r6, 6
	addi %r7, %r31, 0
	bl {vg_keccak_pad_scratch}
	addi %r3, %r29, 0
	li %r4, 144
	li %r5, 0
	addi %r6, %r30, 0
	li %r7, 28
	addi %r8, %r31, 0
	bl {vg_keccak_squeeze_scratch}
	ld %r0, 664(%r31)
	mtlr %r0
	ld %r29, 640(%r31)
	ld %r30, 648(%r31)
	ld %r31, 656(%r31)
	addi %r1, %r1, 704
	li %r0, 0
	stdu %r1, -752(%r1)
	addi %r12, %r1, 32
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
	std %r0, 240(%r12)
	std %r0, 248(%r12)
	std %r0, 256(%r12)
	std %r0, 264(%r12)
	std %r0, 272(%r12)
	std %r0, 280(%r12)
	std %r0, 288(%r12)
	std %r0, 296(%r12)
	std %r0, 304(%r12)
	std %r0, 312(%r12)
	std %r0, 320(%r12)
	std %r0, 328(%r12)
	std %r0, 336(%r12)
	std %r0, 344(%r12)
	std %r0, 352(%r12)
	std %r0, 360(%r12)
	std %r0, 368(%r12)
	std %r0, 376(%r12)
	std %r0, 384(%r12)
	std %r0, 392(%r12)
	std %r0, 400(%r12)
	std %r0, 408(%r12)
	std %r0, 416(%r12)
	std %r0, 424(%r12)
	std %r0, 432(%r12)
	std %r0, 440(%r12)
	std %r0, 448(%r12)
	std %r0, 456(%r12)
	std %r0, 464(%r12)
	std %r0, 472(%r12)
	std %r0, 480(%r12)
	std %r0, 488(%r12)
	std %r0, 496(%r12)
	std %r0, 504(%r12)
	std %r0, 512(%r12)
	std %r0, 520(%r12)
	std %r0, 528(%r12)
	std %r0, 536(%r12)
	std %r0, 544(%r12)
	std %r0, 552(%r12)
	std %r0, 560(%r12)
	std %r0, 568(%r12)
	std %r0, 576(%r12)
	std %r0, 584(%r12)
	std %r0, 592(%r12)
	std %r0, 600(%r12)
	std %r0, 608(%r12)
	std %r0, 616(%r12)
	std %r0, 624(%r12)
	std %r0, 632(%r12)
	std %r0, 640(%r12)
	std %r0, 648(%r12)
	std %r0, 656(%r12)
	std %r0, 664(%r12)
	std %r0, 672(%r12)
	std %r0, 680(%r12)
	std %r0, 688(%r12)
	std %r0, 696(%r12)
	std %r0, 704(%r12)
	std %r0, 712(%r12)
	addi %r1, %r1, 752
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
	addc %r0, %r0, %r0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
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

vg_sha3_256_update:
	addi %r8, %r7, 0
	addi %r7, %r6, 0
	addi %r6, %r5, 0
	addi %r5, %r4, 0
	li %r4, 136
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 512(%r8)
	std %r27, 520(%r8)
	std %r28, 528(%r8)
	std %r29, 536(%r8)
	std %r30, 544(%r8)
	std %r31, 552(%r8)
	addi %r26, %r3, 0
	addi %r27, %r8, 0
	addi %r28, %r4, 0
	addi %r29, %r5, 0
	addi %r30, %r6, 0
	addi %r31, %r7, 0
	cmpldi %cr0, %r31, 0
	beq %cr0, 20f
22:
	li %r10, 7
	and %r10, %r29, %r10
	addi %r11, %r31, -8
	rldicl %r11, %r11, 1, 63
	or %r10, %r10, %r11
	cmpldi %cr0, %r10, 0
	beq %cr0, 23f
	lbz %r9, 0(%r30)
	add %r10, %r26, %r29
	lbz %r11, 0(%r10)
	xor %r9, %r9, %r11
	stb %r9, 0(%r10)
	addi %r30, %r30, 1
	addi %r29, %r29, 1
	addi %r31, %r31, -1
	subf %r9, %r28, %r29
	b 24f
23:
	ld %r9, 0(%r30)
	add %r10, %r26, %r29
	ld %r11, 0(%r10)
	xor %r9, %r9, %r11
	std %r9, 0(%r10)
	addi %r30, %r30, 8
	addi %r29, %r29, 8
	addi %r31, %r31, -8
	subf %r9, %r28, %r29
24:
	cmpldi %cr0, %r9, 0
	beq %cr0, 25f
	b 26f
25:
	li %r29, 0
	addi %r3, %r26, 0
	addi %r4, %r27, 0
	bl {vg_keccak_f1600}
	addi %r26, %r3, 0
	addi %r27, %r4, 0
26:
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	b 21f
20:
21:
	addi %r3, %r29, 0
	ld %r26, 512(%r27)
	ld %r28, 528(%r27)
	ld %r29, 536(%r27)
	ld %r30, 544(%r27)
	ld %r31, 552(%r27)
	ld %r27, 520(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	li %r0, 0
	stdu %r1, -48(%r1)
	addi %r12, %r1, 32
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	addi %r1, %r1, 48
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	addc %r0, %r0, %r0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
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

vg_sha3_256_finalize:
	stdu %r1, -704(%r1)
	addi %r6, %r1, 32
	mflr %r0
	std %r0, 664(%r6)
	std %r29, 640(%r6)
	std %r30, 648(%r6)
	std %r31, 656(%r6)
	addi %r29, %r3, 0
	addi %r30, %r5, 0
	addi %r31, %r6, 0
	addi %r5, %r4, 0
	li %r4, 136
	li %r6, 6
	addi %r7, %r31, 0
	bl {vg_keccak_pad_scratch}
	addi %r3, %r29, 0
	li %r4, 136
	li %r5, 0
	addi %r6, %r30, 0
	li %r7, 32
	addi %r8, %r31, 0
	bl {vg_keccak_squeeze_scratch}
	ld %r0, 664(%r31)
	mtlr %r0
	ld %r29, 640(%r31)
	ld %r30, 648(%r31)
	ld %r31, 656(%r31)
	addi %r1, %r1, 704
	li %r0, 0
	stdu %r1, -752(%r1)
	addi %r12, %r1, 32
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
	std %r0, 240(%r12)
	std %r0, 248(%r12)
	std %r0, 256(%r12)
	std %r0, 264(%r12)
	std %r0, 272(%r12)
	std %r0, 280(%r12)
	std %r0, 288(%r12)
	std %r0, 296(%r12)
	std %r0, 304(%r12)
	std %r0, 312(%r12)
	std %r0, 320(%r12)
	std %r0, 328(%r12)
	std %r0, 336(%r12)
	std %r0, 344(%r12)
	std %r0, 352(%r12)
	std %r0, 360(%r12)
	std %r0, 368(%r12)
	std %r0, 376(%r12)
	std %r0, 384(%r12)
	std %r0, 392(%r12)
	std %r0, 400(%r12)
	std %r0, 408(%r12)
	std %r0, 416(%r12)
	std %r0, 424(%r12)
	std %r0, 432(%r12)
	std %r0, 440(%r12)
	std %r0, 448(%r12)
	std %r0, 456(%r12)
	std %r0, 464(%r12)
	std %r0, 472(%r12)
	std %r0, 480(%r12)
	std %r0, 488(%r12)
	std %r0, 496(%r12)
	std %r0, 504(%r12)
	std %r0, 512(%r12)
	std %r0, 520(%r12)
	std %r0, 528(%r12)
	std %r0, 536(%r12)
	std %r0, 544(%r12)
	std %r0, 552(%r12)
	std %r0, 560(%r12)
	std %r0, 568(%r12)
	std %r0, 576(%r12)
	std %r0, 584(%r12)
	std %r0, 592(%r12)
	std %r0, 600(%r12)
	std %r0, 608(%r12)
	std %r0, 616(%r12)
	std %r0, 624(%r12)
	std %r0, 632(%r12)
	std %r0, 640(%r12)
	std %r0, 648(%r12)
	std %r0, 656(%r12)
	std %r0, 664(%r12)
	std %r0, 672(%r12)
	std %r0, 680(%r12)
	std %r0, 688(%r12)
	std %r0, 696(%r12)
	std %r0, 704(%r12)
	std %r0, 712(%r12)
	addi %r1, %r1, 752
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
	addc %r0, %r0, %r0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
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

vg_sha3_384_update:
	addi %r8, %r7, 0
	addi %r7, %r6, 0
	addi %r6, %r5, 0
	addi %r5, %r4, 0
	li %r4, 104
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 512(%r8)
	std %r27, 520(%r8)
	std %r28, 528(%r8)
	std %r29, 536(%r8)
	std %r30, 544(%r8)
	std %r31, 552(%r8)
	addi %r26, %r3, 0
	addi %r27, %r8, 0
	addi %r28, %r4, 0
	addi %r29, %r5, 0
	addi %r30, %r6, 0
	addi %r31, %r7, 0
	cmpldi %cr0, %r31, 0
	beq %cr0, 20f
22:
	li %r10, 7
	and %r10, %r29, %r10
	addi %r11, %r31, -8
	rldicl %r11, %r11, 1, 63
	or %r10, %r10, %r11
	cmpldi %cr0, %r10, 0
	beq %cr0, 23f
	lbz %r9, 0(%r30)
	add %r10, %r26, %r29
	lbz %r11, 0(%r10)
	xor %r9, %r9, %r11
	stb %r9, 0(%r10)
	addi %r30, %r30, 1
	addi %r29, %r29, 1
	addi %r31, %r31, -1
	subf %r9, %r28, %r29
	b 24f
23:
	ld %r9, 0(%r30)
	add %r10, %r26, %r29
	ld %r11, 0(%r10)
	xor %r9, %r9, %r11
	std %r9, 0(%r10)
	addi %r30, %r30, 8
	addi %r29, %r29, 8
	addi %r31, %r31, -8
	subf %r9, %r28, %r29
24:
	cmpldi %cr0, %r9, 0
	beq %cr0, 25f
	b 26f
25:
	li %r29, 0
	addi %r3, %r26, 0
	addi %r4, %r27, 0
	bl {vg_keccak_f1600}
	addi %r26, %r3, 0
	addi %r27, %r4, 0
26:
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	b 21f
20:
21:
	addi %r3, %r29, 0
	ld %r26, 512(%r27)
	ld %r28, 528(%r27)
	ld %r29, 536(%r27)
	ld %r30, 544(%r27)
	ld %r31, 552(%r27)
	ld %r27, 520(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	li %r0, 0
	stdu %r1, -48(%r1)
	addi %r12, %r1, 32
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	addi %r1, %r1, 48
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	addc %r0, %r0, %r0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
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

vg_sha3_384_finalize:
	stdu %r1, -704(%r1)
	addi %r6, %r1, 32
	mflr %r0
	std %r0, 664(%r6)
	std %r29, 640(%r6)
	std %r30, 648(%r6)
	std %r31, 656(%r6)
	addi %r29, %r3, 0
	addi %r30, %r5, 0
	addi %r31, %r6, 0
	addi %r5, %r4, 0
	li %r4, 104
	li %r6, 6
	addi %r7, %r31, 0
	bl {vg_keccak_pad_scratch}
	addi %r3, %r29, 0
	li %r4, 104
	li %r5, 0
	addi %r6, %r30, 0
	li %r7, 48
	addi %r8, %r31, 0
	bl {vg_keccak_squeeze_scratch}
	ld %r0, 664(%r31)
	mtlr %r0
	ld %r29, 640(%r31)
	ld %r30, 648(%r31)
	ld %r31, 656(%r31)
	addi %r1, %r1, 704
	li %r0, 0
	stdu %r1, -752(%r1)
	addi %r12, %r1, 32
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
	std %r0, 240(%r12)
	std %r0, 248(%r12)
	std %r0, 256(%r12)
	std %r0, 264(%r12)
	std %r0, 272(%r12)
	std %r0, 280(%r12)
	std %r0, 288(%r12)
	std %r0, 296(%r12)
	std %r0, 304(%r12)
	std %r0, 312(%r12)
	std %r0, 320(%r12)
	std %r0, 328(%r12)
	std %r0, 336(%r12)
	std %r0, 344(%r12)
	std %r0, 352(%r12)
	std %r0, 360(%r12)
	std %r0, 368(%r12)
	std %r0, 376(%r12)
	std %r0, 384(%r12)
	std %r0, 392(%r12)
	std %r0, 400(%r12)
	std %r0, 408(%r12)
	std %r0, 416(%r12)
	std %r0, 424(%r12)
	std %r0, 432(%r12)
	std %r0, 440(%r12)
	std %r0, 448(%r12)
	std %r0, 456(%r12)
	std %r0, 464(%r12)
	std %r0, 472(%r12)
	std %r0, 480(%r12)
	std %r0, 488(%r12)
	std %r0, 496(%r12)
	std %r0, 504(%r12)
	std %r0, 512(%r12)
	std %r0, 520(%r12)
	std %r0, 528(%r12)
	std %r0, 536(%r12)
	std %r0, 544(%r12)
	std %r0, 552(%r12)
	std %r0, 560(%r12)
	std %r0, 568(%r12)
	std %r0, 576(%r12)
	std %r0, 584(%r12)
	std %r0, 592(%r12)
	std %r0, 600(%r12)
	std %r0, 608(%r12)
	std %r0, 616(%r12)
	std %r0, 624(%r12)
	std %r0, 632(%r12)
	std %r0, 640(%r12)
	std %r0, 648(%r12)
	std %r0, 656(%r12)
	std %r0, 664(%r12)
	std %r0, 672(%r12)
	std %r0, 680(%r12)
	std %r0, 688(%r12)
	std %r0, 696(%r12)
	std %r0, 704(%r12)
	std %r0, 712(%r12)
	addi %r1, %r1, 752
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
	addc %r0, %r0, %r0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
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

vg_sha3_512_update:
	addi %r8, %r7, 0
	addi %r7, %r6, 0
	addi %r6, %r5, 0
	addi %r5, %r4, 0
	li %r4, 72
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 512(%r8)
	std %r27, 520(%r8)
	std %r28, 528(%r8)
	std %r29, 536(%r8)
	std %r30, 544(%r8)
	std %r31, 552(%r8)
	addi %r26, %r3, 0
	addi %r27, %r8, 0
	addi %r28, %r4, 0
	addi %r29, %r5, 0
	addi %r30, %r6, 0
	addi %r31, %r7, 0
	cmpldi %cr0, %r31, 0
	beq %cr0, 20f
22:
	li %r10, 7
	and %r10, %r29, %r10
	addi %r11, %r31, -8
	rldicl %r11, %r11, 1, 63
	or %r10, %r10, %r11
	cmpldi %cr0, %r10, 0
	beq %cr0, 23f
	lbz %r9, 0(%r30)
	add %r10, %r26, %r29
	lbz %r11, 0(%r10)
	xor %r9, %r9, %r11
	stb %r9, 0(%r10)
	addi %r30, %r30, 1
	addi %r29, %r29, 1
	addi %r31, %r31, -1
	subf %r9, %r28, %r29
	b 24f
23:
	ld %r9, 0(%r30)
	add %r10, %r26, %r29
	ld %r11, 0(%r10)
	xor %r9, %r9, %r11
	std %r9, 0(%r10)
	addi %r30, %r30, 8
	addi %r29, %r29, 8
	addi %r31, %r31, -8
	subf %r9, %r28, %r29
24:
	cmpldi %cr0, %r9, 0
	beq %cr0, 25f
	b 26f
25:
	li %r29, 0
	addi %r3, %r26, 0
	addi %r4, %r27, 0
	bl {vg_keccak_f1600}
	addi %r26, %r3, 0
	addi %r27, %r4, 0
26:
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	b 21f
20:
21:
	addi %r3, %r29, 0
	ld %r26, 512(%r27)
	ld %r28, 528(%r27)
	ld %r29, 536(%r27)
	ld %r30, 544(%r27)
	ld %r31, 552(%r27)
	ld %r27, 520(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	li %r0, 0
	stdu %r1, -48(%r1)
	addi %r12, %r1, 32
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	addi %r1, %r1, 48
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	addc %r0, %r0, %r0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
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

vg_sha3_512_finalize:
	stdu %r1, -704(%r1)
	addi %r6, %r1, 32
	mflr %r0
	std %r0, 664(%r6)
	std %r29, 640(%r6)
	std %r30, 648(%r6)
	std %r31, 656(%r6)
	addi %r29, %r3, 0
	addi %r30, %r5, 0
	addi %r31, %r6, 0
	addi %r5, %r4, 0
	li %r4, 72
	li %r6, 6
	addi %r7, %r31, 0
	bl {vg_keccak_pad_scratch}
	addi %r3, %r29, 0
	li %r4, 72
	li %r5, 0
	addi %r6, %r30, 0
	li %r7, 64
	addi %r8, %r31, 0
	bl {vg_keccak_squeeze_scratch}
	ld %r0, 664(%r31)
	mtlr %r0
	ld %r29, 640(%r31)
	ld %r30, 648(%r31)
	ld %r31, 656(%r31)
	addi %r1, %r1, 704
	li %r0, 0
	stdu %r1, -752(%r1)
	addi %r12, %r1, 32
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
	std %r0, 240(%r12)
	std %r0, 248(%r12)
	std %r0, 256(%r12)
	std %r0, 264(%r12)
	std %r0, 272(%r12)
	std %r0, 280(%r12)
	std %r0, 288(%r12)
	std %r0, 296(%r12)
	std %r0, 304(%r12)
	std %r0, 312(%r12)
	std %r0, 320(%r12)
	std %r0, 328(%r12)
	std %r0, 336(%r12)
	std %r0, 344(%r12)
	std %r0, 352(%r12)
	std %r0, 360(%r12)
	std %r0, 368(%r12)
	std %r0, 376(%r12)
	std %r0, 384(%r12)
	std %r0, 392(%r12)
	std %r0, 400(%r12)
	std %r0, 408(%r12)
	std %r0, 416(%r12)
	std %r0, 424(%r12)
	std %r0, 432(%r12)
	std %r0, 440(%r12)
	std %r0, 448(%r12)
	std %r0, 456(%r12)
	std %r0, 464(%r12)
	std %r0, 472(%r12)
	std %r0, 480(%r12)
	std %r0, 488(%r12)
	std %r0, 496(%r12)
	std %r0, 504(%r12)
	std %r0, 512(%r12)
	std %r0, 520(%r12)
	std %r0, 528(%r12)
	std %r0, 536(%r12)
	std %r0, 544(%r12)
	std %r0, 552(%r12)
	std %r0, 560(%r12)
	std %r0, 568(%r12)
	std %r0, 576(%r12)
	std %r0, 584(%r12)
	std %r0, 592(%r12)
	std %r0, 600(%r12)
	std %r0, 608(%r12)
	std %r0, 616(%r12)
	std %r0, 624(%r12)
	std %r0, 632(%r12)
	std %r0, 640(%r12)
	std %r0, 648(%r12)
	std %r0, 656(%r12)
	std %r0, 664(%r12)
	std %r0, 672(%r12)
	std %r0, 680(%r12)
	std %r0, 688(%r12)
	std %r0, 696(%r12)
	std %r0, 704(%r12)
	std %r0, 712(%r12)
	addi %r1, %r1, 752
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
	addc %r0, %r0, %r0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
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

vg_shake128_update:
	addi %r8, %r7, 0
	addi %r7, %r6, 0
	addi %r6, %r5, 0
	addi %r5, %r4, 0
	li %r4, 168
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 512(%r8)
	std %r27, 520(%r8)
	std %r28, 528(%r8)
	std %r29, 536(%r8)
	std %r30, 544(%r8)
	std %r31, 552(%r8)
	addi %r26, %r3, 0
	addi %r27, %r8, 0
	addi %r28, %r4, 0
	addi %r29, %r5, 0
	addi %r30, %r6, 0
	addi %r31, %r7, 0
	cmpldi %cr0, %r31, 0
	beq %cr0, 20f
22:
	li %r10, 7
	and %r10, %r29, %r10
	addi %r11, %r31, -8
	rldicl %r11, %r11, 1, 63
	or %r10, %r10, %r11
	cmpldi %cr0, %r10, 0
	beq %cr0, 23f
	lbz %r9, 0(%r30)
	add %r10, %r26, %r29
	lbz %r11, 0(%r10)
	xor %r9, %r9, %r11
	stb %r9, 0(%r10)
	addi %r30, %r30, 1
	addi %r29, %r29, 1
	addi %r31, %r31, -1
	subf %r9, %r28, %r29
	b 24f
23:
	ld %r9, 0(%r30)
	add %r10, %r26, %r29
	ld %r11, 0(%r10)
	xor %r9, %r9, %r11
	std %r9, 0(%r10)
	addi %r30, %r30, 8
	addi %r29, %r29, 8
	addi %r31, %r31, -8
	subf %r9, %r28, %r29
24:
	cmpldi %cr0, %r9, 0
	beq %cr0, 25f
	b 26f
25:
	li %r29, 0
	addi %r3, %r26, 0
	addi %r4, %r27, 0
	bl {vg_keccak_f1600}
	addi %r26, %r3, 0
	addi %r27, %r4, 0
26:
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	b 21f
20:
21:
	addi %r3, %r29, 0
	ld %r26, 512(%r27)
	ld %r28, 528(%r27)
	ld %r29, 536(%r27)
	ld %r30, 544(%r27)
	ld %r31, 552(%r27)
	ld %r27, 520(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	li %r0, 0
	stdu %r1, -48(%r1)
	addi %r12, %r1, 32
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	addi %r1, %r1, 48
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	addc %r0, %r0, %r0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
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

vg_shake128_finalize:
	stdu %r1, -672(%r1)
	addi %r5, %r1, 32
	addi %r7, %r5, 0
	addi %r5, %r4, 0
	li %r4, 168
	li %r6, 31
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	add %r9, %r3, %r5
	lbz %r10, 0(%r9)
	xor %r10, %r10, %r6
	stb %r10, 0(%r9)
	add %r9, %r3, %r4
	addi %r9, %r9, -1
	lbz %r10, 0(%r9)
	li %r11, 128
	xor %r10, %r10, %r11
	stb %r10, 0(%r9)
	addi %r4, %r7, 0
	bl {vg_keccak_f1600}
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 672
	li %r0, 0
	stdu %r1, -720(%r1)
	addi %r12, %r1, 32
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
	std %r0, 240(%r12)
	std %r0, 248(%r12)
	std %r0, 256(%r12)
	std %r0, 264(%r12)
	std %r0, 272(%r12)
	std %r0, 280(%r12)
	std %r0, 288(%r12)
	std %r0, 296(%r12)
	std %r0, 304(%r12)
	std %r0, 312(%r12)
	std %r0, 320(%r12)
	std %r0, 328(%r12)
	std %r0, 336(%r12)
	std %r0, 344(%r12)
	std %r0, 352(%r12)
	std %r0, 360(%r12)
	std %r0, 368(%r12)
	std %r0, 376(%r12)
	std %r0, 384(%r12)
	std %r0, 392(%r12)
	std %r0, 400(%r12)
	std %r0, 408(%r12)
	std %r0, 416(%r12)
	std %r0, 424(%r12)
	std %r0, 432(%r12)
	std %r0, 440(%r12)
	std %r0, 448(%r12)
	std %r0, 456(%r12)
	std %r0, 464(%r12)
	std %r0, 472(%r12)
	std %r0, 480(%r12)
	std %r0, 488(%r12)
	std %r0, 496(%r12)
	std %r0, 504(%r12)
	std %r0, 512(%r12)
	std %r0, 520(%r12)
	std %r0, 528(%r12)
	std %r0, 536(%r12)
	std %r0, 544(%r12)
	std %r0, 552(%r12)
	std %r0, 560(%r12)
	std %r0, 568(%r12)
	std %r0, 576(%r12)
	std %r0, 584(%r12)
	std %r0, 592(%r12)
	std %r0, 600(%r12)
	std %r0, 608(%r12)
	std %r0, 616(%r12)
	std %r0, 624(%r12)
	std %r0, 632(%r12)
	std %r0, 640(%r12)
	std %r0, 648(%r12)
	std %r0, 656(%r12)
	std %r0, 664(%r12)
	std %r0, 672(%r12)
	std %r0, 680(%r12)
	addi %r1, %r1, 720
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
	addc %r0, %r0, %r0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
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

vg_shake128_squeeze:
	stdu %r1, -672(%r1)
	addi %r7, %r1, 32
	addi %r8, %r7, 0
	addi %r7, %r6, 0
	addi %r6, %r5, 0
	addi %r5, %r4, 0
	li %r4, 168
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 512(%r8)
	std %r27, 520(%r8)
	std %r28, 528(%r8)
	std %r29, 536(%r8)
	std %r30, 544(%r8)
	std %r31, 552(%r8)
	addi %r26, %r3, 0
	addi %r27, %r8, 0
	addi %r28, %r4, 0
	addi %r29, %r5, 0
	addi %r30, %r6, 0
	addi %r31, %r7, 0
	cmpldi %cr0, %r31, 0
	beq %cr0, 20f
22:
	subf %r9, %r28, %r29
	cmpldi %cr0, %r9, 0
	beq %cr0, 23f
	b 24f
23:
	li %r29, 0
	addi %r3, %r26, 0
	addi %r4, %r27, 0
	bl {vg_keccak_f1600}
	addi %r26, %r3, 0
	addi %r27, %r4, 0
24:
	li %r10, 7
	and %r10, %r29, %r10
	addi %r11, %r31, -8
	rldicl %r11, %r11, 1, 63
	or %r10, %r10, %r11
	cmpldi %cr0, %r10, 0
	beq %cr0, 25f
	add %r10, %r26, %r29
	lbz %r9, 0(%r10)
	stb %r9, 0(%r30)
	addi %r30, %r30, 1
	addi %r29, %r29, 1
	addi %r31, %r31, -1
	b 26f
25:
	add %r10, %r26, %r29
	ld %r9, 0(%r10)
	std %r9, 0(%r30)
	addi %r30, %r30, 8
	addi %r29, %r29, 8
	addi %r31, %r31, -8
26:
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	b 21f
20:
21:
	addi %r3, %r29, 0
	ld %r26, 512(%r27)
	ld %r28, 528(%r27)
	ld %r29, 536(%r27)
	ld %r30, 544(%r27)
	ld %r31, 552(%r27)
	ld %r27, 520(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 672
	li %r0, 0
	stdu %r1, -720(%r1)
	addi %r12, %r1, 32
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
	std %r0, 240(%r12)
	std %r0, 248(%r12)
	std %r0, 256(%r12)
	std %r0, 264(%r12)
	std %r0, 272(%r12)
	std %r0, 280(%r12)
	std %r0, 288(%r12)
	std %r0, 296(%r12)
	std %r0, 304(%r12)
	std %r0, 312(%r12)
	std %r0, 320(%r12)
	std %r0, 328(%r12)
	std %r0, 336(%r12)
	std %r0, 344(%r12)
	std %r0, 352(%r12)
	std %r0, 360(%r12)
	std %r0, 368(%r12)
	std %r0, 376(%r12)
	std %r0, 384(%r12)
	std %r0, 392(%r12)
	std %r0, 400(%r12)
	std %r0, 408(%r12)
	std %r0, 416(%r12)
	std %r0, 424(%r12)
	std %r0, 432(%r12)
	std %r0, 440(%r12)
	std %r0, 448(%r12)
	std %r0, 456(%r12)
	std %r0, 464(%r12)
	std %r0, 472(%r12)
	std %r0, 480(%r12)
	std %r0, 488(%r12)
	std %r0, 496(%r12)
	std %r0, 504(%r12)
	std %r0, 512(%r12)
	std %r0, 520(%r12)
	std %r0, 528(%r12)
	std %r0, 536(%r12)
	std %r0, 544(%r12)
	std %r0, 552(%r12)
	std %r0, 560(%r12)
	std %r0, 568(%r12)
	std %r0, 576(%r12)
	std %r0, 584(%r12)
	std %r0, 592(%r12)
	std %r0, 600(%r12)
	std %r0, 608(%r12)
	std %r0, 616(%r12)
	std %r0, 624(%r12)
	std %r0, 632(%r12)
	std %r0, 640(%r12)
	std %r0, 648(%r12)
	std %r0, 656(%r12)
	std %r0, 664(%r12)
	std %r0, 672(%r12)
	std %r0, 680(%r12)
	addi %r1, %r1, 720
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	addc %r0, %r0, %r0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
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

vg_shake256_finalize:
	stdu %r1, -672(%r1)
	addi %r5, %r1, 32
	addi %r7, %r5, 0
	addi %r5, %r4, 0
	li %r4, 136
	li %r6, 31
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	add %r9, %r3, %r5
	lbz %r10, 0(%r9)
	xor %r10, %r10, %r6
	stb %r10, 0(%r9)
	add %r9, %r3, %r4
	addi %r9, %r9, -1
	lbz %r10, 0(%r9)
	li %r11, 128
	xor %r10, %r10, %r11
	stb %r10, 0(%r9)
	addi %r4, %r7, 0
	bl {vg_keccak_f1600}
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 672
	li %r0, 0
	stdu %r1, -720(%r1)
	addi %r12, %r1, 32
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
	std %r0, 240(%r12)
	std %r0, 248(%r12)
	std %r0, 256(%r12)
	std %r0, 264(%r12)
	std %r0, 272(%r12)
	std %r0, 280(%r12)
	std %r0, 288(%r12)
	std %r0, 296(%r12)
	std %r0, 304(%r12)
	std %r0, 312(%r12)
	std %r0, 320(%r12)
	std %r0, 328(%r12)
	std %r0, 336(%r12)
	std %r0, 344(%r12)
	std %r0, 352(%r12)
	std %r0, 360(%r12)
	std %r0, 368(%r12)
	std %r0, 376(%r12)
	std %r0, 384(%r12)
	std %r0, 392(%r12)
	std %r0, 400(%r12)
	std %r0, 408(%r12)
	std %r0, 416(%r12)
	std %r0, 424(%r12)
	std %r0, 432(%r12)
	std %r0, 440(%r12)
	std %r0, 448(%r12)
	std %r0, 456(%r12)
	std %r0, 464(%r12)
	std %r0, 472(%r12)
	std %r0, 480(%r12)
	std %r0, 488(%r12)
	std %r0, 496(%r12)
	std %r0, 504(%r12)
	std %r0, 512(%r12)
	std %r0, 520(%r12)
	std %r0, 528(%r12)
	std %r0, 536(%r12)
	std %r0, 544(%r12)
	std %r0, 552(%r12)
	std %r0, 560(%r12)
	std %r0, 568(%r12)
	std %r0, 576(%r12)
	std %r0, 584(%r12)
	std %r0, 592(%r12)
	std %r0, 600(%r12)
	std %r0, 608(%r12)
	std %r0, 616(%r12)
	std %r0, 624(%r12)
	std %r0, 632(%r12)
	std %r0, 640(%r12)
	std %r0, 648(%r12)
	std %r0, 656(%r12)
	std %r0, 664(%r12)
	std %r0, 672(%r12)
	std %r0, 680(%r12)
	addi %r1, %r1, 720
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
	addc %r0, %r0, %r0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
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

vg_shake256_squeeze:
	stdu %r1, -672(%r1)
	addi %r7, %r1, 32
	addi %r8, %r7, 0
	addi %r7, %r6, 0
	addi %r6, %r5, 0
	addi %r5, %r4, 0
	li %r4, 136
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 512(%r8)
	std %r27, 520(%r8)
	std %r28, 528(%r8)
	std %r29, 536(%r8)
	std %r30, 544(%r8)
	std %r31, 552(%r8)
	addi %r26, %r3, 0
	addi %r27, %r8, 0
	addi %r28, %r4, 0
	addi %r29, %r5, 0
	addi %r30, %r6, 0
	addi %r31, %r7, 0
	cmpldi %cr0, %r31, 0
	beq %cr0, 20f
22:
	subf %r9, %r28, %r29
	cmpldi %cr0, %r9, 0
	beq %cr0, 23f
	b 24f
23:
	li %r29, 0
	addi %r3, %r26, 0
	addi %r4, %r27, 0
	bl {vg_keccak_f1600}
	addi %r26, %r3, 0
	addi %r27, %r4, 0
24:
	li %r10, 7
	and %r10, %r29, %r10
	addi %r11, %r31, -8
	rldicl %r11, %r11, 1, 63
	or %r10, %r10, %r11
	cmpldi %cr0, %r10, 0
	beq %cr0, 25f
	add %r10, %r26, %r29
	lbz %r9, 0(%r10)
	stb %r9, 0(%r30)
	addi %r30, %r30, 1
	addi %r29, %r29, 1
	addi %r31, %r31, -1
	b 26f
25:
	add %r10, %r26, %r29
	ld %r9, 0(%r10)
	std %r9, 0(%r30)
	addi %r30, %r30, 8
	addi %r29, %r29, 8
	addi %r31, %r31, -8
26:
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	b 21f
20:
21:
	addi %r3, %r29, 0
	ld %r26, 512(%r27)
	ld %r28, 528(%r27)
	ld %r29, 536(%r27)
	ld %r30, 544(%r27)
	ld %r31, 552(%r27)
	ld %r27, 520(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 672
	li %r0, 0
	stdu %r1, -720(%r1)
	addi %r12, %r1, 32
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
	std %r0, 240(%r12)
	std %r0, 248(%r12)
	std %r0, 256(%r12)
	std %r0, 264(%r12)
	std %r0, 272(%r12)
	std %r0, 280(%r12)
	std %r0, 288(%r12)
	std %r0, 296(%r12)
	std %r0, 304(%r12)
	std %r0, 312(%r12)
	std %r0, 320(%r12)
	std %r0, 328(%r12)
	std %r0, 336(%r12)
	std %r0, 344(%r12)
	std %r0, 352(%r12)
	std %r0, 360(%r12)
	std %r0, 368(%r12)
	std %r0, 376(%r12)
	std %r0, 384(%r12)
	std %r0, 392(%r12)
	std %r0, 400(%r12)
	std %r0, 408(%r12)
	std %r0, 416(%r12)
	std %r0, 424(%r12)
	std %r0, 432(%r12)
	std %r0, 440(%r12)
	std %r0, 448(%r12)
	std %r0, 456(%r12)
	std %r0, 464(%r12)
	std %r0, 472(%r12)
	std %r0, 480(%r12)
	std %r0, 488(%r12)
	std %r0, 496(%r12)
	std %r0, 504(%r12)
	std %r0, 512(%r12)
	std %r0, 520(%r12)
	std %r0, 528(%r12)
	std %r0, 536(%r12)
	std %r0, 544(%r12)
	std %r0, 552(%r12)
	std %r0, 560(%r12)
	std %r0, 568(%r12)
	std %r0, 576(%r12)
	std %r0, 584(%r12)
	std %r0, 592(%r12)
	std %r0, 600(%r12)
	std %r0, 608(%r12)
	std %r0, 616(%r12)
	std %r0, 624(%r12)
	std %r0, 632(%r12)
	std %r0, 640(%r12)
	std %r0, 648(%r12)
	std %r0, 656(%r12)
	std %r0, 664(%r12)
	std %r0, 672(%r12)
	std %r0, 680(%r12)
	addi %r1, %r1, 720
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	addc %r0, %r0, %r0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
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
