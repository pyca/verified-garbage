// The functions of `src/sm4_ofb.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_ofb:
	stdu %r1, -3296(%r1)
	addi %r7, %r1, 32
	mflr %r0
	std %r0, 3240(%r7)
	std %r29, 3216(%r7)
	std %r30, 3224(%r7)
	std %r31, 3232(%r7)
	or %r29, %r4, %r4
	or %r30, %r6, %r6
	or %r31, %r4, %r4
	or %r6, %r5, %r5
	or %r5, %r7, %r7
	lwz %r8, 0(%r31)
	stw %r8, 3248(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 3252(%r5)
	lwz %r8, 8(%r31)
	stw %r8, 3256(%r5)
	lwz %r8, 12(%r31)
	stw %r8, 3260(%r5)
	or %r31, %r6, %r6
	cmpldi %cr0, %r30, 0
	beq %cr0, 20f
22:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	bl {vg_sm4_serial_encrypt}
	lwz %r8, 768(%r5)
	stw %r8, 3248(%r5)
	lwz %r8, 772(%r5)
	stw %r8, 3252(%r5)
	lwz %r8, 776(%r5)
	stw %r8, 3256(%r5)
	lwz %r8, 780(%r5)
	stw %r8, 3260(%r5)
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 22b
	b 21f
20:
21:
	or %r31, %r29, %r29
	lwz %r8, 3248(%r5)
	stw %r8, 0(%r31)
	lwz %r8, 3252(%r5)
	stw %r8, 4(%r31)
	lwz %r8, 3256(%r5)
	stw %r8, 8(%r31)
	lwz %r8, 3260(%r5)
	stw %r8, 12(%r31)
	ld %r29, 3216(%r5)
	ld %r30, 3224(%r5)
	ld %r31, 3232(%r5)
	ld %r0, 3240(%r5)
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
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
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
	std %r0, 144(%r12)
	std %r0, 152(%r12)
	std %r0, 160(%r12)
	std %r0, 168(%r12)
	std %r0, 176(%r12)
	std %r0, 184(%r12)
	addi %r1, %r1, 3296
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
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v12, %v12, %v12
	vxor %v13, %v13, %v13
	vxor %v14, %v14, %v14
	vxor %v15, %v15, %v15
	blr

vg_sm4_ofb_final:
	stdu %r1, -3296(%r1)
	addi %r7, %r1, 32
	mflr %r0
	std %r0, 3240(%r7)
	std %r29, 3216(%r7)
	std %r30, 3224(%r7)
	std %r31, 3232(%r7)
	or %r29, %r4, %r4
	or %r30, %r6, %r6
	or %r31, %r4, %r4
	or %r6, %r5, %r5
	or %r5, %r7, %r7
	lwz %r8, 0(%r31)
	stw %r8, 3248(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 3252(%r5)
	lwz %r8, 8(%r31)
	stw %r8, 3256(%r5)
	lwz %r8, 12(%r31)
	stw %r8, 3260(%r5)
	or %r31, %r6, %r6
	cmpldi %cr0, %r30, 0
	beq %cr0, 20f
22:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	bl {vg_sm4_serial_encrypt}
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 23f
	lwz %r8, 768(%r5)
	stw %r8, 3248(%r5)
	lwz %r8, 772(%r5)
	stw %r8, 3252(%r5)
	lwz %r8, 776(%r5)
	stw %r8, 3256(%r5)
	lwz %r8, 780(%r5)
	stw %r8, 3260(%r5)
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -16
	b 24f
23:
	lwz %r8, 768(%r5)
	stw %r8, 3248(%r5)
	lwz %r8, 772(%r5)
	stw %r8, 3252(%r5)
	lwz %r8, 776(%r5)
	stw %r8, 3256(%r5)
	lwz %r8, 780(%r5)
	stw %r8, 3260(%r5)
	addi %r8, %r5, 768
25:
	lbz %r9, 0(%r31)
	lbz %r10, 0(%r8)
	xor %r9, %r9, %r10
	stb %r9, 0(%r31)
	addi %r8, %r8, 1
	addi %r31, %r31, 1
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 25b
24:
	cmpldi %cr0, %r30, 0
	bne %cr0, 22b
	b 21f
20:
21:
	or %r31, %r29, %r29
	lwz %r8, 3248(%r5)
	stw %r8, 0(%r31)
	lwz %r8, 3252(%r5)
	stw %r8, 4(%r31)
	lwz %r8, 3256(%r5)
	stw %r8, 8(%r31)
	lwz %r8, 3260(%r5)
	stw %r8, 12(%r31)
	ld %r29, 3216(%r5)
	ld %r30, 3224(%r5)
	ld %r31, 3232(%r5)
	ld %r0, 3240(%r5)
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
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
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
	std %r0, 144(%r12)
	std %r0, 152(%r12)
	std %r0, 160(%r12)
	std %r0, 168(%r12)
	std %r0, 176(%r12)
	std %r0, 184(%r12)
	addi %r1, %r1, 3296
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
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v12, %v12, %v12
	vxor %v13, %v13, %v13
	vxor %v14, %v14, %v14
	vxor %v15, %v15, %v15
	blr
