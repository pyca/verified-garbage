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
