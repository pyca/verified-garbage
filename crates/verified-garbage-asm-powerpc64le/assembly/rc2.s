// The functions of `src/rc2.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_cbc_init:
	stdu %r1, -608(%r1)
	addi %r9, %r1, 32
	addi %r10, %r4, -1
	rldicl %r10, %r10, 57, 7
	cmpldi %cr0, %r10, 0
	bne %cr0, 20f
	addi %r10, %r5, -1
	rldicl %r10, %r10, 54, 10
	cmpldi %cr0, %r10, 0
	bne %cr0, 22f
	addi %r10, %r7, -8
	cmpldi %cr0, %r10, 0
	bne %cr0, 24f
	b 25f
24:
	li %r3, 3
25:
	b 23f
22:
	li %r3, 2
23:
	b 21f
20:
	li %r3, 1
21:
	cmpldi %cr0, %r10, 0
	bne %cr0, 26f
	mflr %r0
	std %r0, 512(%r9)
	std %r25, 520(%r9)
	addi %r25, %r9, 0
	ld %r10, 0(%r6)
	std %r10, 128(%r8)
	addi %r6, %r8, 0
	addi %r7, %r9, 0
	bl {vg_rc2_expand_key}
	li %r3, 0
	ld %r0, 512(%r25)
	mtlr %r0
	ld %r25, 520(%r25)
	b 27f
26:
27:
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
	addi %r1, %r1, 608
	blr

vg_rc2_cbc_encrypt_update:
	stdu %r1, -608(%r1)
	addi %r9, %r1, 32
	cmpldi %cr0, %r8, 0
	beq %cr0, 20f
	mflr %r0
	std %r0, 512(%r9)
	std %r25, 520(%r9)
	addi %r25, %r9, 0
	addi %r10, %r3, 136
	addi %r11, %r7, 0
	addi %r12, %r4, 0
	cmpldi %cr0, %r12, 0
	beq %cr0, 22f
24:
	lbz %r0, 0(%r10)
	stb %r0, 0(%r11)
	addi %r10, %r10, 1
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 24b
	b 23f
22:
23:
	subf %r12, %r4, %r8
	cmpldi %cr0, %r12, 0
	beq %cr0, 25f
27:
	lbz %r0, 0(%r5)
	stb %r0, 0(%r11)
	addi %r5, %r5, 1
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 27b
	b 26f
25:
26:
	addi %r10, %r3, 136
	subf %r12, %r8, %r6
	add %r12, %r12, %r4
	cmpldi %cr0, %r12, 0
	beq %cr0, 28f
210:
	lbz %r0, 0(%r5)
	stb %r0, 0(%r10)
	addi %r5, %r5, 1
	addi %r10, %r10, 1
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 210b
	b 29f
28:
29:
	addi %r4, %r3, 128
	addi %r5, %r7, 0
	rldicl %r6, %r8, 61, 3
	addi %r7, %r9, 0
	bl {vg_rc2_cbc_encrypt}
	ld %r0, 512(%r25)
	mtlr %r0
	ld %r25, 520(%r25)
	b 21f
20:
	add %r10, %r3, %r4
	cmpldi %cr0, %r6, 0
	beq %cr0, 211f
213:
	lbz %r0, 0(%r5)
	stb %r0, 136(%r10)
	addi %r5, %r5, 1
	addi %r10, %r10, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 213b
	b 212f
211:
212:
21:
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
	addi %r1, %r1, 608
	blr

vg_rc2_cbc_decrypt_update:
	stdu %r1, -608(%r1)
	addi %r9, %r1, 32
	cmpldi %cr0, %r8, 0
	beq %cr0, 20f
	mflr %r0
	std %r0, 512(%r9)
	std %r25, 520(%r9)
	addi %r25, %r9, 0
	addi %r10, %r3, 136
	addi %r11, %r7, 0
	addi %r12, %r4, 0
	cmpldi %cr0, %r12, 0
	beq %cr0, 22f
24:
	lbz %r0, 0(%r10)
	stb %r0, 0(%r11)
	addi %r10, %r10, 1
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 24b
	b 23f
22:
23:
	subf %r12, %r4, %r8
	cmpldi %cr0, %r12, 0
	beq %cr0, 25f
27:
	lbz %r0, 0(%r5)
	stb %r0, 0(%r11)
	addi %r5, %r5, 1
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 27b
	b 26f
25:
26:
	addi %r10, %r3, 136
	subf %r12, %r8, %r6
	add %r12, %r12, %r4
	cmpldi %cr0, %r12, 0
	beq %cr0, 28f
210:
	lbz %r0, 0(%r5)
	stb %r0, 0(%r10)
	addi %r5, %r5, 1
	addi %r10, %r10, 1
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 210b
	b 29f
28:
29:
	addi %r4, %r3, 128
	addi %r5, %r7, 0
	rldicl %r6, %r8, 61, 3
	addi %r7, %r9, 0
	bl {vg_rc2_cbc_decrypt}
	ld %r0, 512(%r25)
	mtlr %r0
	ld %r25, 520(%r25)
	b 21f
20:
	add %r10, %r3, %r4
	cmpldi %cr0, %r6, 0
	beq %cr0, 211f
213:
	lbz %r0, 0(%r5)
	stb %r0, 136(%r10)
	addi %r5, %r5, 1
	addi %r10, %r10, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 213b
	b 212f
211:
212:
21:
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
	addi %r1, %r1, 608
	blr

vg_rc2_cbc_encrypt:
	mflr %r0
	std %r26, 256(%r7)
	std %r27, 264(%r7)
	std %r28, 272(%r7)
	std %r29, 280(%r7)
	std %r31, 296(%r7)
	std %r0, 304(%r7)
	std %r30, 288(%r7)
	addi %r26, %r3, 0
	addi %r27, %r4, 0
	addi %r28, %r5, 0
	addi %r29, %r6, 0
	addi %r30, %r7, 0
	cmpldi %cr0, %r29, 0
	beq %cr0, 20f
22:
	ld %r10, 0(%r28)
	ld %r11, 0(%r27)
	xor %r10, %r10, %r11
	std %r10, 0(%r28)
	addi %r3, %r26, 0
	addi %r4, %r28, 0
	addi %r5, %r30, 0
	bl {vg_rc2_encrypt_block}
	ld %r10, 0(%r28)
	std %r10, 0(%r27)
	addi %r28, %r28, 8
	addi %r29, %r29, -1
	cmpldi %cr0, %r29, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r26, 256(%r30)
	ld %r27, 264(%r30)
	ld %r28, 272(%r30)
	ld %r29, 280(%r30)
	ld %r31, 296(%r30)
	ld %r0, 304(%r30)
	ld %r30, 288(%r30)
	mtlr %r0
	blr

vg_rc2_cbc_decrypt:
	mflr %r0
	std %r26, 256(%r7)
	std %r27, 264(%r7)
	std %r28, 272(%r7)
	std %r29, 280(%r7)
	std %r31, 296(%r7)
	std %r0, 304(%r7)
	std %r30, 288(%r7)
	addi %r26, %r3, 0
	addi %r27, %r4, 0
	addi %r28, %r5, 0
	addi %r29, %r6, 0
	addi %r30, %r7, 0
	cmpldi %cr0, %r29, 0
	beq %cr0, 20f
22:
	ld %r31, 0(%r28)
	addi %r3, %r26, 0
	addi %r4, %r28, 0
	addi %r5, %r30, 0
	bl {vg_rc2_decrypt_block}
	ld %r10, 0(%r28)
	ld %r11, 0(%r27)
	xor %r10, %r10, %r11
	std %r10, 0(%r28)
	std %r31, 0(%r27)
	addi %r28, %r28, 8
	addi %r29, %r29, -1
	cmpldi %cr0, %r29, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r26, 256(%r30)
	ld %r27, 264(%r30)
	ld %r28, 272(%r30)
	ld %r29, 280(%r30)
	ld %r31, 296(%r30)
	ld %r0, 304(%r30)
	ld %r30, 288(%r30)
	mtlr %r0
	blr

vg_rc2_expand_key:
	std %r14, 256(%r7)
	std %r15, 264(%r7)
	lis %r12, -4683
	ori %r12, %r12, 56601
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 50425
	ori %r12, %r12, 30937
	std %r12, 0(%r7)
	lis %r12, -25128
	ori %r12, %r12, 41034
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 31229
	ori %r12, %r12, 59688
	std %r12, 8(%r7)
	lis %r12, -29101
	ori %r12, %r12, 30251
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 33591
	ori %r12, %r12, 32454
	std %r12, 16(%r7)
	lis %r12, -23813
	ori %r12, %r12, 35652
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 34916
	ori %r12, %r12, 19554
	std %r12, 24(%r7)
	lis %r12, 4943
	ori %r12, %r12, 45959
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 62809
	ori %r12, %r12, 39447
	std %r12, 32(%r7)
	lis %r12, 12925
	ori %r12, %r12, 33033
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 36205
	ori %r12, %r12, 17761
	std %r12, 40(%r7)
	lis %r12, 2939
	ori %r12, %r12, 46982
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 60224
	ori %r12, %r12, 36797
	std %r12, 48(%r7)
	lis %r12, -32178
	ori %r12, %r12, 27484
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 8737
	ori %r12, %r12, 38384
	std %r12, 56(%r7)
	lis %r12, 7346
	ori %r12, %r12, 24782
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 37733
	ori %r12, %r12, 54868
	std %r12, 64(%r7)
	lis %r12, -8975
	ori %r12, %r12, 36007
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 5312
	ori %r12, %r12, 22131
	std %r12, 72(%r7)
	lis %r12, -11804
	ori %r12, %r12, 48699
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 8138
	ori %r12, %r12, 29970
	std %r12, 80(%r7)
	lis %r12, 9910
	ori %r12, %r12, 15523
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 12500
	ori %r12, %r12, 15682
	std %r12, 88(%r7)
	lis %r12, 22279
	ori %r12, %r12, 26950
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 55822
	ori %r12, %r12, 49007
	std %r12, 96(%r7)
	lis %r12, 835
	ori %r12, %r12, 38076
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 39709
	ori %r12, %r12, 61991
	std %r12, 104(%r7)
	lis %r12, -6338
	ori %r12, %r12, 61328
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 63175
	ori %r12, %r12, 4600
	std %r12, 112(%r7)
	lis %r12, -10466
	ori %r12, %r12, 26312
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 12245
	ori %r12, %r12, 49926
	std %r12, 120(%r7)
	lis %r12, -2066
	ori %r12, %r12, 21120
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 57066
	ori %r12, %r12, 59400
	std %r12, 128(%r7)
	lis %r12, 10858
	ori %r12, %r12, 19765
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 44146
	ori %r12, %r12, 43652
	std %r12, 136(%r7)
	lis %r12, 29769
	ori %r12, %r12, 5466
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 29138
	ori %r12, %r12, 6806
	std %r12, 144(%r7)
	lis %r12, -4956
	ori %r12, %r12, 6148
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 24272
	ori %r12, %r12, 40779
	std %r12, 152(%r7)
	lis %r12, -13109
	ori %r12, %r12, 20751
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 28225
	ori %r12, %r12, 57538
	std %r12, 160(%r7)
	lis %r12, 14704
	ori %r12, %r12, 62625
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 20655
	ori %r12, %r12, 37156
	std %r12, 168(%r7)
	lis %r12, 31412
	ori %r12, %r12, 47139
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 34106
	ori %r12, %r12, 31897
	std %r12, 176(%r7)
	lis %r12, 12695
	ori %r12, %r12, 21797
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 23350
	ori %r12, %r12, 764
	std %r12, 184(%r7)
	lis %r12, -20846
	ori %r12, %r12, 35555
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 39162
	ori %r12, %r12, 23853
	std %r12, 192(%r7)
	lis %r12, -13894
	ori %r12, %r12, 27751
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 4137
	ori %r12, %r12, 57093
	std %r12, 200(%r7)
	lis %r12, 11432
	ori %r12, %r12, 40673
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 53222
	ori %r12, %r12, 211
	std %r12, 208(%r7)
	lis %r12, -22135
	ori %r12, %r12, 57944
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 16129
	ori %r12, %r12, 5731
	std %r12, 216(%r7)
	lis %r12, -20225
	ori %r12, %r12, 13227
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 6964
	ori %r12, %r12, 14349
	std %r12, 224(%r7)
	lis %r12, 11981
	ori %r12, %r12, 45497
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 24332
	ori %r12, %r12, 18619
	std %r12, 232(%r7)
	lis %r12, 30620
	ori %r12, %r12, 42469
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 18395
	ori %r12, %r12, 62405
	std %r12, 240(%r7)
	lis %r12, -21055
	ori %r12, %r12, 32766
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 26656
	ori %r12, %r12, 42506
	std %r12, 248(%r7)
	li %r8, 0
20:
	add %r9, %r3, %r8
	lbz %r12, 0(%r9)
	add %r9, %r6, %r8
	stb %r12, 0(%r9)
	addi %r8, %r8, 1
	subf %r0, %r4, %r8
	cmpldi %cr0, %r0, 0
	bne %cr0, 20b
	li %r0, 128
	subf %r0, %r0, %r8
	cmpldi %cr0, %r0, 0
	beq %cr0, 21f
23:
	add %r9, %r6, %r8
	addi %r9, %r9, -1
	lbz %r10, 0(%r9)
	subf %r9, %r4, %r8
	add %r9, %r6, %r9
	lbz %r11, 0(%r9)
	add %r10, %r10, %r11
	rldicr %r10, %r10, 56, 7
	rldicl %r10, %r10, 8, 56
	li %r11, 0
	addi %r15, %r7, 248
24:
	subf %r0, %r7, %r15
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r15)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r7, %r15
	addi %r15, %r15, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 24b
	rldicr %r12, %r10, 63, 0
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 56, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 56, 7
	rldicl %r11, %r11, 8, 56
	add %r9, %r6, %r8
	stb %r11, 0(%r9)
	addi %r8, %r8, 1
	li %r0, 128
	subf %r0, %r0, %r8
	cmpldi %cr0, %r0, 0
	bne %cr0, 23b
	b 22f
21:
22:
	addi %r14, %r5, 7
	rldicl %r14, %r14, 61, 3
	li %r8, 128
	subf %r8, %r14, %r8
	rldicr %r9, %r5, 61, 2
	rldicl %r9, %r9, 3, 61
	li %r12, 255
	addi %r10, %r9, -1
	cmpldi %cr0, %r10, 0
	beq %cr0, 25f
	b 26f
25:
	li %r12, 1
26:
	addi %r10, %r9, -2
	cmpldi %cr0, %r10, 0
	beq %cr0, 27f
	b 28f
27:
	li %r12, 3
28:
	addi %r10, %r9, -3
	cmpldi %cr0, %r10, 0
	beq %cr0, 29f
	b 210f
29:
	li %r12, 7
210:
	addi %r10, %r9, -4
	cmpldi %cr0, %r10, 0
	beq %cr0, 211f
	b 212f
211:
	li %r12, 15
212:
	addi %r10, %r9, -5
	cmpldi %cr0, %r10, 0
	beq %cr0, 213f
	b 214f
213:
	li %r12, 31
214:
	addi %r10, %r9, -6
	cmpldi %cr0, %r10, 0
	beq %cr0, 215f
	b 216f
215:
	li %r12, 63
216:
	addi %r10, %r9, -7
	cmpldi %cr0, %r10, 0
	beq %cr0, 217f
	b 218f
217:
	li %r12, 127
218:
	add %r9, %r6, %r8
	lbz %r10, 0(%r9)
	and %r10, %r10, %r12
	li %r11, 0
	addi %r15, %r7, 248
219:
	subf %r0, %r7, %r15
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r15)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r7, %r15
	addi %r15, %r15, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 219b
	rldicr %r12, %r10, 63, 0
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 56, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 56, 7
	rldicl %r11, %r11, 8, 56
	add %r9, %r6, %r8
	stb %r11, 0(%r9)
	cmpldi %cr0, %r8, 0
	beq %cr0, 220f
222:
	addi %r8, %r8, -1
	add %r9, %r6, %r8
	lbz %r10, 1(%r9)
	add %r9, %r8, %r14
	add %r9, %r6, %r9
	lbz %r11, 0(%r9)
	xor %r10, %r10, %r11
	li %r11, 0
	addi %r15, %r7, 248
223:
	subf %r0, %r7, %r15
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r15)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r7, %r15
	addi %r15, %r15, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 223b
	rldicr %r12, %r10, 63, 0
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 56, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 56, 7
	rldicl %r11, %r11, 8, 56
	add %r9, %r6, %r8
	stb %r11, 0(%r9)
	cmpldi %cr0, %r8, 0
	bne %cr0, 222b
	b 221f
220:
221:
	ld %r14, 256(%r7)
	ld %r15, 264(%r7)
	blr

vg_rc2_encrypt_block:
	ld %r11, 0(%r4)
	rldicr %r6, %r11, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r7, %r11, 32, 31
	rldicl %r7, %r7, 16, 48
	rldicr %r8, %r11, 16, 47
	rldicl %r8, %r8, 16, 48
	rldicl %r9, %r11, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 0(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 2(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 4(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 6(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 8(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 10(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 12(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 14(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 16(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 18(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 20(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 22(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 24(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 26(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 28(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 30(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 32(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 34(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 36(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 38(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r10, %r9, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r11, 0
	addi %r5, %r3, 120
20:
	subf %r0, %r3, %r5
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r5)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r3, %r5
	addi %r5, %r5, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 20b
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 48, 15
	rldicl %r11, %r11, 16, 48
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r10, %r6, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r11, 0
	addi %r5, %r3, 120
21:
	subf %r0, %r3, %r5
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r5)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r3, %r5
	addi %r5, %r5, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 21b
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 48, 15
	rldicl %r11, %r11, 16, 48
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r10, %r7, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r11, 0
	addi %r5, %r3, 120
22:
	subf %r0, %r3, %r5
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r5)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r3, %r5
	addi %r5, %r5, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 22b
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 48, 15
	rldicl %r11, %r11, 16, 48
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r10, %r8, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r11, 0
	addi %r5, %r3, 120
23:
	subf %r0, %r3, %r5
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r5)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r3, %r5
	addi %r5, %r5, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 23b
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 48, 15
	rldicl %r11, %r11, 16, 48
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 40(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 42(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 44(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 46(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 48(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 50(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 52(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 54(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 56(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 58(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 60(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 62(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 64(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 66(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 68(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 70(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 72(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 74(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 76(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 78(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 80(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 82(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 84(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 86(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r10, %r9, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r11, 0
	addi %r5, %r3, 120
24:
	subf %r0, %r3, %r5
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r5)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r3, %r5
	addi %r5, %r5, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 24b
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 48, 15
	rldicl %r11, %r11, 16, 48
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r10, %r6, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r11, 0
	addi %r5, %r3, 120
25:
	subf %r0, %r3, %r5
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r5)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r3, %r5
	addi %r5, %r5, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 25b
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 48, 15
	rldicl %r11, %r11, 16, 48
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r10, %r7, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r11, 0
	addi %r5, %r3, 120
26:
	subf %r0, %r3, %r5
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r5)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r3, %r5
	addi %r5, %r5, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 26b
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 48, 15
	rldicl %r11, %r11, 16, 48
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r10, %r8, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r11, 0
	addi %r5, %r3, 120
27:
	subf %r0, %r3, %r5
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r5)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r3, %r5
	addi %r5, %r5, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 27b
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 48, 15
	rldicl %r11, %r11, 16, 48
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 88(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 90(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 92(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 94(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 96(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 98(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 100(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 102(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 104(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 106(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 108(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 110(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 112(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 114(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 116(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 118(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 120(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 122(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 124(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 124(%r3)
	rlwinm %r12, %r12, 16, 16, 31
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r11, %r7, 16, 47
	or %r11, %r11, %r6
	rldicr %r12, %r8, 32, 31
	or %r11, %r11, %r12
	rldicr %r12, %r9, 48, 15
	or %r11, %r11, %r12
	std %r11, 0(%r4)
	blr

vg_rc2_decrypt_block:
	ld %r11, 0(%r4)
	rldicr %r6, %r11, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r7, %r11, 32, 31
	rldicl %r7, %r7, 16, 48
	rldicr %r8, %r11, 16, 47
	rldicl %r8, %r8, 16, 48
	rldicl %r9, %r11, 16, 48
	rldicr %r0, %r9, 11, 52
	rldicl %r9, %r9, 59, 5
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 124(%r3)
	rlwinm %r12, %r12, 16, 16, 31
	subf %r9, %r12, %r9
	subf %r9, %r10, %r9
	subf %r9, %r11, %r9
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r8, 13, 50
	rldicl %r8, %r8, 61, 3
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 124(%r3)
	subf %r8, %r12, %r8
	subf %r8, %r10, %r8
	subf %r8, %r11, %r8
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r7, 14, 49
	rldicl %r7, %r7, 62, 2
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 122(%r3)
	subf %r7, %r12, %r7
	subf %r7, %r10, %r7
	subf %r7, %r11, %r7
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r6, 15, 48
	rldicl %r6, %r6, 63, 1
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 120(%r3)
	subf %r6, %r12, %r6
	subf %r6, %r10, %r6
	subf %r6, %r11, %r6
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r9, 11, 52
	rldicl %r9, %r9, 59, 5
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 118(%r3)
	subf %r9, %r12, %r9
	subf %r9, %r10, %r9
	subf %r9, %r11, %r9
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r8, 13, 50
	rldicl %r8, %r8, 61, 3
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 116(%r3)
	subf %r8, %r12, %r8
	subf %r8, %r10, %r8
	subf %r8, %r11, %r8
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r7, 14, 49
	rldicl %r7, %r7, 62, 2
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 114(%r3)
	subf %r7, %r12, %r7
	subf %r7, %r10, %r7
	subf %r7, %r11, %r7
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r6, 15, 48
	rldicl %r6, %r6, 63, 1
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 112(%r3)
	subf %r6, %r12, %r6
	subf %r6, %r10, %r6
	subf %r6, %r11, %r6
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r9, 11, 52
	rldicl %r9, %r9, 59, 5
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 110(%r3)
	subf %r9, %r12, %r9
	subf %r9, %r10, %r9
	subf %r9, %r11, %r9
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r8, 13, 50
	rldicl %r8, %r8, 61, 3
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 108(%r3)
	subf %r8, %r12, %r8
	subf %r8, %r10, %r8
	subf %r8, %r11, %r8
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r7, 14, 49
	rldicl %r7, %r7, 62, 2
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 106(%r3)
	subf %r7, %r12, %r7
	subf %r7, %r10, %r7
	subf %r7, %r11, %r7
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r6, 15, 48
	rldicl %r6, %r6, 63, 1
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 104(%r3)
	subf %r6, %r12, %r6
	subf %r6, %r10, %r6
	subf %r6, %r11, %r6
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r9, 11, 52
	rldicl %r9, %r9, 59, 5
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 102(%r3)
	subf %r9, %r12, %r9
	subf %r9, %r10, %r9
	subf %r9, %r11, %r9
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r8, 13, 50
	rldicl %r8, %r8, 61, 3
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 100(%r3)
	subf %r8, %r12, %r8
	subf %r8, %r10, %r8
	subf %r8, %r11, %r8
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r7, 14, 49
	rldicl %r7, %r7, 62, 2
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 98(%r3)
	subf %r7, %r12, %r7
	subf %r7, %r10, %r7
	subf %r7, %r11, %r7
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r6, 15, 48
	rldicl %r6, %r6, 63, 1
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 96(%r3)
	subf %r6, %r12, %r6
	subf %r6, %r10, %r6
	subf %r6, %r11, %r6
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r9, 11, 52
	rldicl %r9, %r9, 59, 5
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 94(%r3)
	subf %r9, %r12, %r9
	subf %r9, %r10, %r9
	subf %r9, %r11, %r9
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r8, 13, 50
	rldicl %r8, %r8, 61, 3
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 92(%r3)
	subf %r8, %r12, %r8
	subf %r8, %r10, %r8
	subf %r8, %r11, %r8
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r7, 14, 49
	rldicl %r7, %r7, 62, 2
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 90(%r3)
	subf %r7, %r12, %r7
	subf %r7, %r10, %r7
	subf %r7, %r11, %r7
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r6, 15, 48
	rldicl %r6, %r6, 63, 1
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 88(%r3)
	subf %r6, %r12, %r6
	subf %r6, %r10, %r6
	subf %r6, %r11, %r6
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r10, %r8, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r11, 0
	addi %r5, %r3, 120
20:
	subf %r0, %r3, %r5
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r5)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r3, %r5
	addi %r5, %r5, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 20b
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 48, 15
	rldicl %r11, %r11, 16, 48
	subf %r9, %r11, %r9
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r10, %r7, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r11, 0
	addi %r5, %r3, 120
21:
	subf %r0, %r3, %r5
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r5)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r3, %r5
	addi %r5, %r5, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 21b
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 48, 15
	rldicl %r11, %r11, 16, 48
	subf %r8, %r11, %r8
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r10, %r6, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r11, 0
	addi %r5, %r3, 120
22:
	subf %r0, %r3, %r5
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r5)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r3, %r5
	addi %r5, %r5, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 22b
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 48, 15
	rldicl %r11, %r11, 16, 48
	subf %r7, %r11, %r7
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r10, %r9, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r11, 0
	addi %r5, %r3, 120
23:
	subf %r0, %r3, %r5
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r5)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r3, %r5
	addi %r5, %r5, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 23b
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 48, 15
	rldicl %r11, %r11, 16, 48
	subf %r6, %r11, %r6
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r9, 11, 52
	rldicl %r9, %r9, 59, 5
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 86(%r3)
	subf %r9, %r12, %r9
	subf %r9, %r10, %r9
	subf %r9, %r11, %r9
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r8, 13, 50
	rldicl %r8, %r8, 61, 3
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 84(%r3)
	subf %r8, %r12, %r8
	subf %r8, %r10, %r8
	subf %r8, %r11, %r8
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r7, 14, 49
	rldicl %r7, %r7, 62, 2
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 82(%r3)
	subf %r7, %r12, %r7
	subf %r7, %r10, %r7
	subf %r7, %r11, %r7
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r6, 15, 48
	rldicl %r6, %r6, 63, 1
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 80(%r3)
	subf %r6, %r12, %r6
	subf %r6, %r10, %r6
	subf %r6, %r11, %r6
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r9, 11, 52
	rldicl %r9, %r9, 59, 5
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 78(%r3)
	subf %r9, %r12, %r9
	subf %r9, %r10, %r9
	subf %r9, %r11, %r9
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r8, 13, 50
	rldicl %r8, %r8, 61, 3
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 76(%r3)
	subf %r8, %r12, %r8
	subf %r8, %r10, %r8
	subf %r8, %r11, %r8
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r7, 14, 49
	rldicl %r7, %r7, 62, 2
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 74(%r3)
	subf %r7, %r12, %r7
	subf %r7, %r10, %r7
	subf %r7, %r11, %r7
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r6, 15, 48
	rldicl %r6, %r6, 63, 1
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 72(%r3)
	subf %r6, %r12, %r6
	subf %r6, %r10, %r6
	subf %r6, %r11, %r6
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r9, 11, 52
	rldicl %r9, %r9, 59, 5
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 70(%r3)
	subf %r9, %r12, %r9
	subf %r9, %r10, %r9
	subf %r9, %r11, %r9
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r8, 13, 50
	rldicl %r8, %r8, 61, 3
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 68(%r3)
	subf %r8, %r12, %r8
	subf %r8, %r10, %r8
	subf %r8, %r11, %r8
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r7, 14, 49
	rldicl %r7, %r7, 62, 2
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 66(%r3)
	subf %r7, %r12, %r7
	subf %r7, %r10, %r7
	subf %r7, %r11, %r7
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r6, 15, 48
	rldicl %r6, %r6, 63, 1
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 64(%r3)
	subf %r6, %r12, %r6
	subf %r6, %r10, %r6
	subf %r6, %r11, %r6
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r9, 11, 52
	rldicl %r9, %r9, 59, 5
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 62(%r3)
	subf %r9, %r12, %r9
	subf %r9, %r10, %r9
	subf %r9, %r11, %r9
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r8, 13, 50
	rldicl %r8, %r8, 61, 3
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 60(%r3)
	subf %r8, %r12, %r8
	subf %r8, %r10, %r8
	subf %r8, %r11, %r8
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r7, 14, 49
	rldicl %r7, %r7, 62, 2
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 58(%r3)
	subf %r7, %r12, %r7
	subf %r7, %r10, %r7
	subf %r7, %r11, %r7
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r6, 15, 48
	rldicl %r6, %r6, 63, 1
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 56(%r3)
	subf %r6, %r12, %r6
	subf %r6, %r10, %r6
	subf %r6, %r11, %r6
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r9, 11, 52
	rldicl %r9, %r9, 59, 5
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 54(%r3)
	subf %r9, %r12, %r9
	subf %r9, %r10, %r9
	subf %r9, %r11, %r9
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r8, 13, 50
	rldicl %r8, %r8, 61, 3
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 52(%r3)
	subf %r8, %r12, %r8
	subf %r8, %r10, %r8
	subf %r8, %r11, %r8
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r7, 14, 49
	rldicl %r7, %r7, 62, 2
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 50(%r3)
	subf %r7, %r12, %r7
	subf %r7, %r10, %r7
	subf %r7, %r11, %r7
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r6, 15, 48
	rldicl %r6, %r6, 63, 1
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 48(%r3)
	subf %r6, %r12, %r6
	subf %r6, %r10, %r6
	subf %r6, %r11, %r6
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r9, 11, 52
	rldicl %r9, %r9, 59, 5
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 46(%r3)
	subf %r9, %r12, %r9
	subf %r9, %r10, %r9
	subf %r9, %r11, %r9
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r8, 13, 50
	rldicl %r8, %r8, 61, 3
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 44(%r3)
	subf %r8, %r12, %r8
	subf %r8, %r10, %r8
	subf %r8, %r11, %r8
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r7, 14, 49
	rldicl %r7, %r7, 62, 2
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 42(%r3)
	subf %r7, %r12, %r7
	subf %r7, %r10, %r7
	subf %r7, %r11, %r7
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r6, 15, 48
	rldicl %r6, %r6, 63, 1
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 40(%r3)
	subf %r6, %r12, %r6
	subf %r6, %r10, %r6
	subf %r6, %r11, %r6
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r10, %r8, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r11, 0
	addi %r5, %r3, 120
24:
	subf %r0, %r3, %r5
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r5)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r3, %r5
	addi %r5, %r5, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 24b
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 48, 15
	rldicl %r11, %r11, 16, 48
	subf %r9, %r11, %r9
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r10, %r7, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r11, 0
	addi %r5, %r3, 120
25:
	subf %r0, %r3, %r5
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r5)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r3, %r5
	addi %r5, %r5, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 25b
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 48, 15
	rldicl %r11, %r11, 16, 48
	subf %r8, %r11, %r8
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r10, %r6, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r11, 0
	addi %r5, %r3, 120
26:
	subf %r0, %r3, %r5
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r5)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r3, %r5
	addi %r5, %r5, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 26b
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 48, 15
	rldicl %r11, %r11, 16, 48
	subf %r7, %r11, %r7
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r10, %r9, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r11, 0
	addi %r5, %r3, 120
27:
	subf %r0, %r3, %r5
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r5)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r3, %r5
	addi %r5, %r5, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 27b
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 48, 15
	rldicl %r11, %r11, 16, 48
	subf %r6, %r11, %r6
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r9, 11, 52
	rldicl %r9, %r9, 59, 5
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 38(%r3)
	subf %r9, %r12, %r9
	subf %r9, %r10, %r9
	subf %r9, %r11, %r9
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r8, 13, 50
	rldicl %r8, %r8, 61, 3
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 36(%r3)
	subf %r8, %r12, %r8
	subf %r8, %r10, %r8
	subf %r8, %r11, %r8
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r7, 14, 49
	rldicl %r7, %r7, 62, 2
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 34(%r3)
	subf %r7, %r12, %r7
	subf %r7, %r10, %r7
	subf %r7, %r11, %r7
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r6, 15, 48
	rldicl %r6, %r6, 63, 1
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 32(%r3)
	subf %r6, %r12, %r6
	subf %r6, %r10, %r6
	subf %r6, %r11, %r6
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r9, 11, 52
	rldicl %r9, %r9, 59, 5
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 30(%r3)
	subf %r9, %r12, %r9
	subf %r9, %r10, %r9
	subf %r9, %r11, %r9
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r8, 13, 50
	rldicl %r8, %r8, 61, 3
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 28(%r3)
	subf %r8, %r12, %r8
	subf %r8, %r10, %r8
	subf %r8, %r11, %r8
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r7, 14, 49
	rldicl %r7, %r7, 62, 2
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 26(%r3)
	subf %r7, %r12, %r7
	subf %r7, %r10, %r7
	subf %r7, %r11, %r7
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r6, 15, 48
	rldicl %r6, %r6, 63, 1
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 24(%r3)
	subf %r6, %r12, %r6
	subf %r6, %r10, %r6
	subf %r6, %r11, %r6
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r9, 11, 52
	rldicl %r9, %r9, 59, 5
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 22(%r3)
	subf %r9, %r12, %r9
	subf %r9, %r10, %r9
	subf %r9, %r11, %r9
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r8, 13, 50
	rldicl %r8, %r8, 61, 3
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 20(%r3)
	subf %r8, %r12, %r8
	subf %r8, %r10, %r8
	subf %r8, %r11, %r8
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r7, 14, 49
	rldicl %r7, %r7, 62, 2
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 18(%r3)
	subf %r7, %r12, %r7
	subf %r7, %r10, %r7
	subf %r7, %r11, %r7
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r6, 15, 48
	rldicl %r6, %r6, 63, 1
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 16(%r3)
	subf %r6, %r12, %r6
	subf %r6, %r10, %r6
	subf %r6, %r11, %r6
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r9, 11, 52
	rldicl %r9, %r9, 59, 5
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 14(%r3)
	subf %r9, %r12, %r9
	subf %r9, %r10, %r9
	subf %r9, %r11, %r9
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r8, 13, 50
	rldicl %r8, %r8, 61, 3
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 12(%r3)
	subf %r8, %r12, %r8
	subf %r8, %r10, %r8
	subf %r8, %r11, %r8
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r7, 14, 49
	rldicl %r7, %r7, 62, 2
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 10(%r3)
	subf %r7, %r12, %r7
	subf %r7, %r10, %r7
	subf %r7, %r11, %r7
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r6, 15, 48
	rldicl %r6, %r6, 63, 1
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 8(%r3)
	subf %r6, %r12, %r6
	subf %r6, %r10, %r6
	subf %r6, %r11, %r6
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r9, 11, 52
	rldicl %r9, %r9, 59, 5
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 6(%r3)
	subf %r9, %r12, %r9
	subf %r9, %r10, %r9
	subf %r9, %r11, %r9
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r8, 13, 50
	rldicl %r8, %r8, 61, 3
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 4(%r3)
	subf %r8, %r12, %r8
	subf %r8, %r10, %r8
	subf %r8, %r11, %r8
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r7, 14, 49
	rldicl %r7, %r7, 62, 2
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 2(%r3)
	subf %r7, %r12, %r7
	subf %r7, %r10, %r7
	subf %r7, %r11, %r7
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r6, 15, 48
	rldicl %r6, %r6, 63, 1
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 0(%r3)
	subf %r6, %r12, %r6
	subf %r6, %r10, %r6
	subf %r6, %r11, %r6
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r11, %r7, 16, 47
	or %r11, %r11, %r6
	rldicr %r12, %r8, 32, 31
	or %r11, %r11, %r12
	rldicr %r12, %r9, 48, 15
	or %r11, %r11, %r12
	std %r11, 0(%r4)
	blr
