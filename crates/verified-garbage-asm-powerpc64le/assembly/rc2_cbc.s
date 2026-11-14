// The functions of `src/rc2_cbc.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_cbc_encrypt_chained:
	stdu %r1, -544(%r1)
	addi %r7, %r1, 32
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
	addi %r1, %r1, 544
	blr

vg_rc2_cbc_decrypt_chained:
	stdu %r1, -544(%r1)
	addi %r7, %r1, 32
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
	addi %r1, %r1, 544
	blr
