// The functions of `src/triple_des_cfb8.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_cfb8_encrypt:
	stdu %r1, -608(%r1)
	addi %r7, %r1, 32
	mflr %r0
	std %r0, 544(%r7)
	std %r29, 520(%r7)
	std %r30, 528(%r7)
	std %r31, 536(%r7)
	or %r29, %r4, %r4
	or %r30, %r6, %r6
	or %r31, %r4, %r4
	or %r6, %r5, %r5
	or %r5, %r7, %r7
	lwz %r8, 0(%r31)
	stw %r8, 552(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 556(%r5)
	or %r31, %r6, %r6
	cmpldi %cr0, %r30, 0
	beq %cr0, 20f
22:
	lwz %r8, 552(%r5)
	stw %r8, 512(%r5)
	lwz %r8, 556(%r5)
	stw %r8, 516(%r5)
	addi %r4, %r5, 512
	bl {vg_triple_des_encrypt_block}
	lbz %r8, 0(%r31)
	lbz %r9, 512(%r5)
	xor %r8, %r8, %r9
	stb %r8, 0(%r31)
	lbz %r8, 553(%r5)
	stb %r8, 552(%r5)
	lbz %r8, 554(%r5)
	stb %r8, 553(%r5)
	lbz %r8, 555(%r5)
	stb %r8, 554(%r5)
	lbz %r8, 556(%r5)
	stb %r8, 555(%r5)
	lbz %r8, 557(%r5)
	stb %r8, 556(%r5)
	lbz %r8, 558(%r5)
	stb %r8, 557(%r5)
	lbz %r8, 559(%r5)
	stb %r8, 558(%r5)
	lbz %r8, 0(%r31)
	stb %r8, 559(%r5)
	addi %r31, %r31, 1
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 22b
	b 21f
20:
21:
	or %r31, %r29, %r29
	lwz %r8, 552(%r5)
	stw %r8, 0(%r31)
	lwz %r8, 556(%r5)
	stw %r8, 4(%r31)
	ld %r29, 520(%r5)
	ld %r30, 528(%r5)
	ld %r31, 536(%r5)
	ld %r0, 544(%r5)
	mtlr %r0
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
	addi %r1, %r1, 608
	li %r0, 0
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	blr

vg_triple_des_cfb8_decrypt:
	stdu %r1, -608(%r1)
	addi %r7, %r1, 32
	mflr %r0
	std %r0, 544(%r7)
	std %r29, 520(%r7)
	std %r30, 528(%r7)
	std %r31, 536(%r7)
	or %r29, %r4, %r4
	or %r30, %r6, %r6
	or %r31, %r4, %r4
	or %r6, %r5, %r5
	or %r5, %r7, %r7
	lwz %r8, 0(%r31)
	stw %r8, 552(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 556(%r5)
	or %r31, %r6, %r6
	cmpldi %cr0, %r30, 0
	beq %cr0, 20f
22:
	lwz %r8, 552(%r5)
	stw %r8, 512(%r5)
	lwz %r8, 556(%r5)
	stw %r8, 516(%r5)
	addi %r4, %r5, 512
	bl {vg_triple_des_encrypt_block}
	lbz %r8, 553(%r5)
	stb %r8, 552(%r5)
	lbz %r8, 554(%r5)
	stb %r8, 553(%r5)
	lbz %r8, 555(%r5)
	stb %r8, 554(%r5)
	lbz %r8, 556(%r5)
	stb %r8, 555(%r5)
	lbz %r8, 557(%r5)
	stb %r8, 556(%r5)
	lbz %r8, 558(%r5)
	stb %r8, 557(%r5)
	lbz %r8, 559(%r5)
	stb %r8, 558(%r5)
	lbz %r8, 0(%r31)
	stb %r8, 559(%r5)
	lbz %r8, 0(%r31)
	lbz %r9, 512(%r5)
	xor %r8, %r8, %r9
	stb %r8, 0(%r31)
	addi %r31, %r31, 1
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 22b
	b 21f
20:
21:
	or %r31, %r29, %r29
	lwz %r8, 552(%r5)
	stw %r8, 0(%r31)
	lwz %r8, 556(%r5)
	stw %r8, 4(%r31)
	ld %r29, 520(%r5)
	ld %r30, 528(%r5)
	ld %r31, 536(%r5)
	ld %r0, 544(%r5)
	mtlr %r0
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
	addi %r1, %r1, 608
	li %r0, 0
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	blr
