// The functions of `src/internal/vg_chacha20_poly1305_seal_core.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_poly1305_seal_core:
	stdu %r1, -688(%r1)
	addi %r10, %r1, 32
	addi %r11, %r7, 0
	std %r24, 464(%r10)
	std %r25, 472(%r10)
	std %r26, 480(%r10)
	std %r27, 488(%r10)
	std %r28, 496(%r10)
	std %r29, 504(%r10)
	std %r31, 512(%r10)
	mflr %r0
	std %r0, 520(%r10)
	addi %r24, %r10, 0
	addi %r25, %r5, 0
	addi %r26, %r6, 0
	addi %r27, %r7, 0
	addi %r28, %r8, 0
	addi %r29, %r9, 0
	addi %r31, %r11, 0
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
	addi %r7, %r31, 0
	bl {vg_chacha20_xor}
	addi %r3, %r24, 0
	addi %r4, %r24, 384
	bl {vg_poly1305_init_core}
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
	addi %r6, %r24, 528
	bl {vg_poly1305_finalize_scratch}
	addi %r12, %r24, 0
	ld %r0, 520(%r12)
	mtlr %r0
	ld %r24, 464(%r12)
	ld %r25, 472(%r12)
	ld %r26, 480(%r12)
	ld %r27, 488(%r12)
	ld %r28, 496(%r12)
	ld %r29, 504(%r12)
	ld %r31, 512(%r12)
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
	addi %r1, %r1, 688
	blr
