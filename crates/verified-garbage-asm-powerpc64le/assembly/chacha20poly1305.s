// The functions of `src/chacha20poly1305.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_poly1305_seal:
	stdu %r1, -688(%r1)
	addi %r10, %r1, 32
	std %r24, 464(%r10)
	std %r25, 472(%r10)
	std %r26, 480(%r10)
	std %r27, 488(%r10)
	std %r28, 496(%r10)
	std %r29, 504(%r10)
	mflr %r0
	std %r0, 512(%r10)
	addi %r24, %r10, 0
	addi %r25, %r5, 0
	addi %r26, %r6, 0
	addi %r27, %r7, 0
	addi %r28, %r8, 0
	addi %r29, %r9, 0
	lis %r12, 24944
	ori %r12, %r12, 30821
	stw %r12, 320(%r24)
	lis %r12, 13088
	ori %r12, %r12, 25710
	stw %r12, 324(%r24)
	lis %r12, 31074
	ori %r12, %r12, 11570
	stw %r12, 328(%r24)
	lis %r12, 27424
	ori %r12, %r12, 25972
	stw %r12, 332(%r24)
	lwz %r12, 0(%r3)
	stw %r12, 336(%r24)
	lwz %r12, 4(%r3)
	stw %r12, 340(%r24)
	lwz %r12, 8(%r3)
	stw %r12, 344(%r24)
	lwz %r12, 12(%r3)
	stw %r12, 348(%r24)
	lwz %r12, 16(%r3)
	stw %r12, 352(%r24)
	lwz %r12, 20(%r3)
	stw %r12, 356(%r24)
	lwz %r12, 24(%r3)
	stw %r12, 360(%r24)
	lwz %r12, 28(%r3)
	stw %r12, 364(%r24)
	li %r12, 0
	stw %r12, 368(%r24)
	lwz %r12, 0(%r4)
	stw %r12, 372(%r24)
	lwz %r12, 4(%r4)
	stw %r12, 376(%r24)
	lwz %r12, 8(%r4)
	stw %r12, 380(%r24)
	addi %r3, %r24, 320
	addi %r4, %r24, 0
	bl {vg_chacha20_block}
	ld %r12, 0(%r24)
	std %r12, 384(%r24)
	ld %r12, 8(%r24)
	std %r12, 392(%r24)
	ld %r12, 16(%r24)
	std %r12, 400(%r24)
	ld %r12, 24(%r24)
	std %r12, 408(%r24)
	li %r12, 1
	stw %r12, 368(%r24)
	addi %r3, %r24, 320
	addi %r4, %r27, 0
	addi %r5, %r28, 0
	addi %r6, %r24, 0
	bl {vg_chacha20_xor}
	addi %r3, %r24, 0
	addi %r4, %r24, 384
	bl {vg_poly1305_init}
	addi %r4, %r25, 0
	rldicl %r5, %r26, 60, 4
	addi %r3, %r24, 0
	bl {vg_poly1305_blocks}
	li %r12, 15
	and %r12, %r26, %r12
	cmpldi %cr0, %r12, 0
	beq %cr0, 20f
	subf %r4, %r12, %r26
	add %r4, %r25, %r4
	li %r11, 0
	std %r11, 416(%r24)
	std %r11, 424(%r24)
	addi %r6, %r24, 416
22:
	lbz %r11, 0(%r4)
	stb %r11, 0(%r6)
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 22b
	addi %r4, %r24, 416
	li %r5, 1
	addi %r3, %r24, 0
	bl {vg_poly1305_blocks}
	b 21f
20:
21:
	addi %r4, %r27, 0
	rldicl %r5, %r28, 60, 4
	addi %r3, %r24, 0
	bl {vg_poly1305_blocks}
	li %r12, 15
	and %r12, %r28, %r12
	cmpldi %cr0, %r12, 0
	beq %cr0, 23f
	subf %r4, %r12, %r28
	add %r4, %r27, %r4
	li %r11, 0
	std %r11, 416(%r24)
	std %r11, 424(%r24)
	addi %r6, %r24, 416
25:
	lbz %r11, 0(%r4)
	stb %r11, 0(%r6)
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 25b
	addi %r4, %r24, 416
	li %r5, 1
	addi %r3, %r24, 0
	bl {vg_poly1305_blocks}
	b 24f
23:
24:
	std %r26, 432(%r24)
	std %r28, 440(%r24)
	addi %r4, %r24, 432
	li %r5, 1
	addi %r3, %r24, 0
	bl {vg_poly1305_blocks}
	rldicl %r4, %r26, 60, 4
	li %r12, 15
	and %r12, %r26, %r12
	addi %r12, %r12, 15
	rldicl %r12, %r12, 60, 4
	add %r4, %r4, %r12
	rldicl %r5, %r28, 60, 4
	li %r12, 15
	and %r12, %r28, %r12
	addi %r12, %r12, 15
	rldicl %r12, %r12, 60, 4
	add %r5, %r5, %r12
	add %r4, %r4, %r5
	addi %r4, %r4, 1
	rldicr %r4, %r4, 4, 59
	addi %r3, %r24, 0
	addi %r5, %r29, 0
	addi %r6, %r24, 520
	bl {vg_poly1305_finalize_scratch}
	addi %r12, %r24, 0
	ld %r0, 512(%r12)
	mtlr %r0
	ld %r24, 464(%r12)
	ld %r25, 472(%r12)
	ld %r26, 480(%r12)
	ld %r27, 488(%r12)
	ld %r28, 496(%r12)
	ld %r29, 504(%r12)
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
	addi %r1, %r1, 688
	blr

vg_chacha20_poly1305_open:
	stdu %r1, -688(%r1)
	addi %r10, %r1, 32
	std %r24, 464(%r10)
	std %r25, 472(%r10)
	std %r26, 480(%r10)
	std %r27, 488(%r10)
	std %r28, 496(%r10)
	std %r29, 504(%r10)
	mflr %r0
	std %r0, 512(%r10)
	addi %r24, %r10, 0
	addi %r25, %r5, 0
	addi %r26, %r6, 0
	addi %r27, %r7, 0
	addi %r28, %r8, 0
	addi %r29, %r9, 0
	lis %r12, 24944
	ori %r12, %r12, 30821
	stw %r12, 320(%r24)
	lis %r12, 13088
	ori %r12, %r12, 25710
	stw %r12, 324(%r24)
	lis %r12, 31074
	ori %r12, %r12, 11570
	stw %r12, 328(%r24)
	lis %r12, 27424
	ori %r12, %r12, 25972
	stw %r12, 332(%r24)
	lwz %r12, 0(%r3)
	stw %r12, 336(%r24)
	lwz %r12, 4(%r3)
	stw %r12, 340(%r24)
	lwz %r12, 8(%r3)
	stw %r12, 344(%r24)
	lwz %r12, 12(%r3)
	stw %r12, 348(%r24)
	lwz %r12, 16(%r3)
	stw %r12, 352(%r24)
	lwz %r12, 20(%r3)
	stw %r12, 356(%r24)
	lwz %r12, 24(%r3)
	stw %r12, 360(%r24)
	lwz %r12, 28(%r3)
	stw %r12, 364(%r24)
	li %r12, 0
	stw %r12, 368(%r24)
	lwz %r12, 0(%r4)
	stw %r12, 372(%r24)
	lwz %r12, 4(%r4)
	stw %r12, 376(%r24)
	lwz %r12, 8(%r4)
	stw %r12, 380(%r24)
	addi %r3, %r24, 320
	addi %r4, %r24, 0
	bl {vg_chacha20_block}
	ld %r12, 0(%r24)
	std %r12, 384(%r24)
	ld %r12, 8(%r24)
	std %r12, 392(%r24)
	ld %r12, 16(%r24)
	std %r12, 400(%r24)
	ld %r12, 24(%r24)
	std %r12, 408(%r24)
	addi %r3, %r24, 0
	addi %r4, %r24, 384
	bl {vg_poly1305_init}
	addi %r4, %r25, 0
	rldicl %r5, %r26, 60, 4
	addi %r3, %r24, 0
	bl {vg_poly1305_blocks}
	li %r12, 15
	and %r12, %r26, %r12
	cmpldi %cr0, %r12, 0
	beq %cr0, 20f
	subf %r4, %r12, %r26
	add %r4, %r25, %r4
	li %r11, 0
	std %r11, 416(%r24)
	std %r11, 424(%r24)
	addi %r6, %r24, 416
22:
	lbz %r11, 0(%r4)
	stb %r11, 0(%r6)
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 22b
	addi %r4, %r24, 416
	li %r5, 1
	addi %r3, %r24, 0
	bl {vg_poly1305_blocks}
	b 21f
20:
21:
	addi %r4, %r27, 0
	rldicl %r5, %r28, 60, 4
	addi %r3, %r24, 0
	bl {vg_poly1305_blocks}
	li %r12, 15
	and %r12, %r28, %r12
	cmpldi %cr0, %r12, 0
	beq %cr0, 23f
	subf %r4, %r12, %r28
	add %r4, %r27, %r4
	li %r11, 0
	std %r11, 416(%r24)
	std %r11, 424(%r24)
	addi %r6, %r24, 416
25:
	lbz %r11, 0(%r4)
	stb %r11, 0(%r6)
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 25b
	addi %r4, %r24, 416
	li %r5, 1
	addi %r3, %r24, 0
	bl {vg_poly1305_blocks}
	b 24f
23:
24:
	std %r26, 432(%r24)
	std %r28, 440(%r24)
	addi %r4, %r24, 432
	li %r5, 1
	addi %r3, %r24, 0
	bl {vg_poly1305_blocks}
	rldicl %r4, %r26, 60, 4
	li %r12, 15
	and %r12, %r26, %r12
	addi %r12, %r12, 15
	rldicl %r12, %r12, 60, 4
	add %r4, %r4, %r12
	rldicl %r5, %r28, 60, 4
	li %r12, 15
	and %r12, %r28, %r12
	addi %r12, %r12, 15
	rldicl %r12, %r12, 60, 4
	add %r5, %r5, %r12
	add %r4, %r4, %r5
	addi %r4, %r4, 1
	rldicr %r4, %r4, 4, 59
	addi %r3, %r24, 0
	addi %r5, %r24, 448
	addi %r6, %r24, 520
	bl {vg_poly1305_finalize_scratch}
	li %r12, 1
	stw %r12, 368(%r24)
	addi %r3, %r24, 320
	addi %r4, %r27, 0
	addi %r5, %r28, 0
	addi %r6, %r24, 0
	bl {vg_chacha20_xor}
	ld %r3, 448(%r24)
	ld %r4, 0(%r29)
	xor %r3, %r3, %r4
	ld %r4, 456(%r24)
	ld %r5, 8(%r29)
	xor %r4, %r4, %r5
	or %r3, %r3, %r4
	li %r4, 0
	subf %r4, %r3, %r4
	or %r3, %r3, %r4
	rldicl %r3, %r3, 1, 63
	li %r4, 1
	subf %r3, %r3, %r4
	addi %r12, %r24, 0
	ld %r0, 512(%r12)
	mtlr %r0
	ld %r24, 464(%r12)
	ld %r25, 472(%r12)
	ld %r26, 480(%r12)
	ld %r27, 488(%r12)
	ld %r28, 496(%r12)
	ld %r29, 504(%r12)
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
	addi %r1, %r1, 688
	blr

vg_chacha20_poly1305_seal_gather:
	stdu %r1, -80(%r1)
	addi %r12, %r1, 0
	std %r3, 32(%r12)
	std %r4, 40(%r12)
	std %r5, 48(%r12)
	std %r6, 56(%r12)
	std %r9, 64(%r12)
	mflr %r0
	std %r0, 72(%r12)
	ld %r11, 176(%r12)
	cmpldi %cr0, %r8, 0
	beq %cr0, 20f
22:
	ld %r3, 0(%r7)
	ld %r4, 8(%r7)
	addi %r7, %r7, 16
	rldicl %r5, %r4, 61, 3
	cmpldi %cr0, %r5, 0
	beq %cr0, 23f
25:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 25b
	b 24f
23:
24:
	li %r6, 7
	and %r4, %r4, %r6
	cmpldi %cr0, %r4, 0
	beq %cr0, 26f
28:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r9)
	addi %r3, %r3, 1
	addi %r9, %r9, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 28b
	b 27f
26:
27:
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r3, 32(%r12)
	ld %r4, 40(%r12)
	ld %r5, 48(%r12)
	ld %r6, 56(%r12)
	ld %r7, 64(%r12)
	addi %r8, %r10, 0
	addi %r9, %r11, 0
	bl {vg_chacha20_poly1305_seal}
	addi %r12, %r1, 0
	ld %r0, 72(%r12)
	mtlr %r0
	addi %r1, %r1, 80
	blr
