// The functions of `src/internal/vg_x25519.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x25519:
	lwz %r7, 0(%r5)
	stw %r7, 0(%r6)
	stw %r7, 96(%r6)
	lwz %r7, 4(%r5)
	stw %r7, 4(%r6)
	stw %r7, 100(%r6)
	lwz %r7, 8(%r5)
	stw %r7, 8(%r6)
	stw %r7, 104(%r6)
	lwz %r7, 12(%r5)
	stw %r7, 12(%r6)
	stw %r7, 108(%r6)
	lwz %r7, 16(%r5)
	stw %r7, 16(%r6)
	stw %r7, 112(%r6)
	lwz %r7, 20(%r5)
	stw %r7, 20(%r6)
	stw %r7, 116(%r6)
	lwz %r7, 24(%r5)
	stw %r7, 24(%r6)
	stw %r7, 120(%r6)
	lwz %r7, 28(%r5)
	rldicr %r7, %r7, 33, 30
	rldicl %r7, %r7, 31, 33
	stw %r7, 28(%r6)
	stw %r7, 124(%r6)
	li %r7, 1
	li %r8, 0
	stw %r7, 32(%r6)
	stw %r8, 64(%r6)
	stw %r7, 128(%r6)
	stw %r8, 36(%r6)
	stw %r8, 40(%r6)
	stw %r8, 44(%r6)
	stw %r8, 48(%r6)
	stw %r8, 52(%r6)
	stw %r8, 56(%r6)
	stw %r8, 60(%r6)
	stw %r8, 68(%r6)
	stw %r8, 72(%r6)
	stw %r8, 76(%r6)
	stw %r8, 80(%r6)
	stw %r8, 84(%r6)
	stw %r8, 88(%r6)
	stw %r8, 92(%r6)
	stw %r8, 132(%r6)
	stw %r8, 136(%r6)
	stw %r8, 140(%r6)
	stw %r8, 144(%r6)
	stw %r8, 148(%r6)
	stw %r8, 152(%r6)
	stw %r8, 156(%r6)
	addi %r9, %r6, 0
	li %r11, 32
20:
	lbz %r7, 0(%r4)
	rldicr %r8, %r7, 63, 0
	rldicl %r8, %r8, 1, 63
	stb %r8, 608(%r9)
	rldicr %r8, %r7, 62, 1
	rldicl %r8, %r8, 1, 63
	stb %r8, 609(%r9)
	rldicr %r8, %r7, 61, 2
	rldicl %r8, %r8, 1, 63
	stb %r8, 610(%r9)
	rldicr %r8, %r7, 60, 3
	rldicl %r8, %r8, 1, 63
	stb %r8, 611(%r9)
	rldicr %r8, %r7, 59, 4
	rldicl %r8, %r8, 1, 63
	stb %r8, 612(%r9)
	rldicr %r8, %r7, 58, 5
	rldicl %r8, %r8, 1, 63
	stb %r8, 613(%r9)
	rldicr %r8, %r7, 57, 6
	rldicl %r8, %r8, 1, 63
	stb %r8, 614(%r9)
	rldicr %r8, %r7, 56, 7
	rldicl %r8, %r8, 1, 63
	stb %r8, 615(%r9)
	addi %r4, %r4, 1
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 20b
	li %r7, 0
	stb %r7, 608(%r6)
	stb %r7, 609(%r6)
	stb %r7, 610(%r6)
	li %r7, 1
	stb %r7, 862(%r6)
	li %r12, 255
	li %r0, 0
21:
	addi %r12, %r12, -1
	add %r4, %r6, %r12
	lbz %r4, 608(%r4)
	xor %r0, %r0, %r4
	li %r11, 0
	subf %r11, %r0, %r11
	lwz %r5, 32(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 108(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 112(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 112(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 116(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 116(%r6)
	lwz %r5, 56(%r6)
	lwz %r7, 120(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 56(%r6)
	stw %r7, 120(%r6)
	lwz %r5, 60(%r6)
	lwz %r7, 124(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 60(%r6)
	stw %r7, 124(%r6)
	lwz %r5, 64(%r6)
	lwz %r7, 128(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 64(%r6)
	stw %r7, 128(%r6)
	lwz %r5, 68(%r6)
	lwz %r7, 132(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 68(%r6)
	stw %r7, 132(%r6)
	lwz %r5, 72(%r6)
	lwz %r7, 136(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 72(%r6)
	stw %r7, 136(%r6)
	lwz %r5, 76(%r6)
	lwz %r7, 140(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 76(%r6)
	stw %r7, 140(%r6)
	lwz %r5, 80(%r6)
	lwz %r7, 144(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 80(%r6)
	stw %r7, 144(%r6)
	lwz %r5, 84(%r6)
	lwz %r7, 148(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 84(%r6)
	stw %r7, 148(%r6)
	lwz %r5, 88(%r6)
	lwz %r7, 152(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 88(%r6)
	stw %r7, 152(%r6)
	lwz %r5, 92(%r6)
	lwz %r7, 156(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 92(%r6)
	stw %r7, 156(%r6)
	addi %r0, %r4, 0
	ld %r8, 32(%r6)
	ld %r4, 64(%r6)
	addc %r8, %r8, %r4
	ld %r9, 40(%r6)
	ld %r4, 72(%r6)
	adde %r9, %r9, %r4
	ld %r10, 48(%r6)
	ld %r4, 80(%r6)
	adde %r10, %r10, %r4
	ld %r11, 56(%r6)
	ld %r4, 88(%r6)
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	li %r5, 38
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 160(%r6)
	std %r9, 168(%r6)
	std %r10, 176(%r6)
	std %r11, 184(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 160(%r6)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 168(%r6)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 160(%r6)
	ld %r5, 168(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 176(%r6)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 168(%r6)
	ld %r5, 168(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 160(%r6)
	ld %r5, 176(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 184(%r6)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 176(%r6)
	ld %r5, 168(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 168(%r6)
	ld %r5, 176(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 160(%r6)
	ld %r5, 184(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 184(%r6)
	ld %r5, 168(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 176(%r6)
	ld %r5, 176(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 168(%r6)
	ld %r5, 184(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 184(%r6)
	ld %r5, 176(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 176(%r6)
	ld %r5, 184(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 184(%r6)
	ld %r5, 184(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 288(%r6)
	std %r9, 296(%r6)
	std %r10, 304(%r6)
	std %r11, 312(%r6)
	ld %r8, 32(%r6)
	ld %r4, 64(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 40(%r6)
	ld %r4, 72(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 48(%r6)
	ld %r4, 80(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 56(%r6)
	ld %r4, 88(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 192(%r6)
	std %r9, 200(%r6)
	std %r10, 208(%r6)
	std %r11, 216(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 192(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 200(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 192(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 208(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 200(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 192(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 216(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 208(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 200(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 192(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 216(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 208(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 200(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 216(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 208(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 216(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 320(%r6)
	std %r9, 328(%r6)
	std %r10, 336(%r6)
	std %r11, 344(%r6)
	ld %r8, 288(%r6)
	ld %r4, 320(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 296(%r6)
	ld %r4, 328(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 304(%r6)
	ld %r4, 336(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 312(%r6)
	ld %r4, 344(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 352(%r6)
	std %r9, 360(%r6)
	std %r10, 368(%r6)
	std %r11, 376(%r6)
	ld %r8, 96(%r6)
	ld %r4, 128(%r6)
	addc %r8, %r8, %r4
	ld %r9, 104(%r6)
	ld %r4, 136(%r6)
	adde %r9, %r9, %r4
	ld %r10, 112(%r6)
	ld %r4, 144(%r6)
	adde %r10, %r10, %r4
	ld %r11, 120(%r6)
	ld %r4, 152(%r6)
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	li %r5, 38
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 224(%r6)
	std %r9, 232(%r6)
	std %r10, 240(%r6)
	std %r11, 248(%r6)
	ld %r8, 96(%r6)
	ld %r4, 128(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 104(%r6)
	ld %r4, 136(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 112(%r6)
	ld %r4, 144(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 120(%r6)
	ld %r4, 152(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 256(%r6)
	std %r9, 264(%r6)
	std %r10, 272(%r6)
	std %r11, 280(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 256(%r6)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 264(%r6)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 256(%r6)
	ld %r5, 168(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 272(%r6)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 264(%r6)
	ld %r5, 168(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 256(%r6)
	ld %r5, 176(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 280(%r6)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 272(%r6)
	ld %r5, 168(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 264(%r6)
	ld %r5, 176(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 256(%r6)
	ld %r5, 184(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 280(%r6)
	ld %r5, 168(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 272(%r6)
	ld %r5, 176(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 264(%r6)
	ld %r5, 184(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 280(%r6)
	ld %r5, 176(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 272(%r6)
	ld %r5, 184(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 280(%r6)
	ld %r5, 184(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 384(%r6)
	std %r9, 392(%r6)
	std %r10, 400(%r6)
	std %r11, 408(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 224(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 232(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 224(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 240(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 232(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 224(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 240(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 232(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 224(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 248(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 240(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 232(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 248(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 240(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 416(%r6)
	std %r9, 424(%r6)
	std %r10, 432(%r6)
	std %r11, 440(%r6)
	ld %r8, 384(%r6)
	ld %r4, 416(%r6)
	addc %r8, %r8, %r4
	ld %r9, 392(%r6)
	ld %r4, 424(%r6)
	adde %r9, %r9, %r4
	ld %r10, 400(%r6)
	ld %r4, 432(%r6)
	adde %r10, %r10, %r4
	ld %r11, 408(%r6)
	ld %r4, 440(%r6)
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	li %r5, 38
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 96(%r6)
	std %r9, 104(%r6)
	std %r10, 112(%r6)
	std %r11, 120(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 96(%r6)
	ld %r5, 96(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 104(%r6)
	ld %r5, 96(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 96(%r6)
	ld %r5, 104(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 112(%r6)
	ld %r5, 96(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 104(%r6)
	ld %r5, 104(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 96(%r6)
	ld %r5, 112(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 120(%r6)
	ld %r5, 96(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 112(%r6)
	ld %r5, 104(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 104(%r6)
	ld %r5, 112(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 96(%r6)
	ld %r5, 120(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 120(%r6)
	ld %r5, 104(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 112(%r6)
	ld %r5, 112(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 104(%r6)
	ld %r5, 120(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 120(%r6)
	ld %r5, 112(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 112(%r6)
	ld %r5, 120(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 120(%r6)
	ld %r5, 120(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 96(%r6)
	std %r9, 104(%r6)
	std %r10, 112(%r6)
	std %r11, 120(%r6)
	ld %r8, 384(%r6)
	ld %r4, 416(%r6)
	subfc %r8, %r4, %r8
	ld %r9, 392(%r6)
	ld %r4, 424(%r6)
	subfe %r9, %r4, %r9
	ld %r10, 400(%r6)
	ld %r4, 432(%r6)
	subfe %r10, %r4, %r10
	ld %r11, 408(%r6)
	ld %r4, 440(%r6)
	subfe %r11, %r4, %r11
	li %r5, 38
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	subfe %r7, %r7, %r7
	and %r4, %r7, %r5
	li %r7, 0
	subfc %r8, %r4, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r7, %r10
	subfe %r11, %r7, %r11
	std %r8, 128(%r6)
	std %r9, 136(%r6)
	std %r10, 144(%r6)
	std %r11, 152(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 128(%r6)
	ld %r5, 128(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 136(%r6)
	ld %r5, 128(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 128(%r6)
	ld %r5, 136(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 144(%r6)
	ld %r5, 128(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 136(%r6)
	ld %r5, 136(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 128(%r6)
	ld %r5, 144(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 152(%r6)
	ld %r5, 128(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 144(%r6)
	ld %r5, 136(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 136(%r6)
	ld %r5, 144(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 128(%r6)
	ld %r5, 152(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 152(%r6)
	ld %r5, 136(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 144(%r6)
	ld %r5, 144(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 136(%r6)
	ld %r5, 152(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 152(%r6)
	ld %r5, 144(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 144(%r6)
	ld %r5, 152(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 152(%r6)
	ld %r5, 152(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 128(%r6)
	std %r9, 136(%r6)
	std %r10, 144(%r6)
	std %r11, 152(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 0(%r6)
	ld %r5, 128(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 8(%r6)
	ld %r5, 128(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 0(%r6)
	ld %r5, 136(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 16(%r6)
	ld %r5, 128(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 8(%r6)
	ld %r5, 136(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 0(%r6)
	ld %r5, 144(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 24(%r6)
	ld %r5, 128(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 16(%r6)
	ld %r5, 136(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 8(%r6)
	ld %r5, 144(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 0(%r6)
	ld %r5, 152(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 24(%r6)
	ld %r5, 136(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 16(%r6)
	ld %r5, 144(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 8(%r6)
	ld %r5, 152(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 24(%r6)
	ld %r5, 144(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 16(%r6)
	ld %r5, 152(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 24(%r6)
	ld %r5, 152(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 128(%r6)
	std %r9, 136(%r6)
	std %r10, 144(%r6)
	std %r11, 152(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 288(%r6)
	ld %r5, 320(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 296(%r6)
	ld %r5, 320(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 288(%r6)
	ld %r5, 328(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 304(%r6)
	ld %r5, 320(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 296(%r6)
	ld %r5, 328(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 288(%r6)
	ld %r5, 336(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 312(%r6)
	ld %r5, 320(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 304(%r6)
	ld %r5, 328(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 296(%r6)
	ld %r5, 336(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 288(%r6)
	ld %r5, 344(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 312(%r6)
	ld %r5, 328(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 304(%r6)
	ld %r5, 336(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 296(%r6)
	ld %r5, 344(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 312(%r6)
	ld %r5, 336(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 304(%r6)
	ld %r5, 344(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 312(%r6)
	ld %r5, 344(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 32(%r6)
	std %r9, 40(%r6)
	std %r10, 48(%r6)
	std %r11, 56(%r6)
	lis %r5, 1
	ori %r5, %r5, 56129
	ld %r8, 352(%r6)
	mulhdu %r7, %r8, %r5
	mulld %r8, %r8, %r5
	ld %r9, 360(%r6)
	mulhdu %r4, %r9, %r5
	mulld %r9, %r9, %r5
	addc %r9, %r9, %r7
	ld %r10, 368(%r6)
	mulhdu %r7, %r10, %r5
	mulld %r10, %r10, %r5
	adde %r10, %r10, %r4
	ld %r11, 376(%r6)
	mulhdu %r4, %r11, %r5
	mulld %r11, %r11, %r5
	adde %r11, %r11, %r7
	addze %r7, %r4
	li %r5, 38
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 64(%r6)
	std %r9, 72(%r6)
	std %r10, 80(%r6)
	std %r11, 88(%r6)
	ld %r8, 288(%r6)
	ld %r4, 64(%r6)
	addc %r8, %r8, %r4
	ld %r9, 296(%r6)
	ld %r4, 72(%r6)
	adde %r9, %r9, %r4
	ld %r10, 304(%r6)
	ld %r4, 80(%r6)
	adde %r10, %r10, %r4
	ld %r11, 312(%r6)
	ld %r4, 88(%r6)
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	li %r5, 38
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 64(%r6)
	std %r9, 72(%r6)
	std %r10, 80(%r6)
	std %r11, 88(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 352(%r6)
	ld %r5, 64(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 360(%r6)
	ld %r5, 64(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 352(%r6)
	ld %r5, 72(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 368(%r6)
	ld %r5, 64(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 360(%r6)
	ld %r5, 72(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 352(%r6)
	ld %r5, 80(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 376(%r6)
	ld %r5, 64(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 368(%r6)
	ld %r5, 72(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 360(%r6)
	ld %r5, 80(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 352(%r6)
	ld %r5, 88(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 376(%r6)
	ld %r5, 72(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 368(%r6)
	ld %r5, 80(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 360(%r6)
	ld %r5, 88(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 376(%r6)
	ld %r5, 80(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 368(%r6)
	ld %r5, 88(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 376(%r6)
	ld %r5, 88(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 64(%r6)
	std %r9, 72(%r6)
	std %r10, 80(%r6)
	std %r11, 88(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 21b
	li %r11, 0
	subf %r11, %r0, %r11
	lwz %r5, 32(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 108(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 112(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 112(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 116(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 116(%r6)
	lwz %r5, 56(%r6)
	lwz %r7, 120(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 56(%r6)
	stw %r7, 120(%r6)
	lwz %r5, 60(%r6)
	lwz %r7, 124(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 60(%r6)
	stw %r7, 124(%r6)
	lwz %r5, 64(%r6)
	lwz %r7, 128(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 64(%r6)
	stw %r7, 128(%r6)
	lwz %r5, 68(%r6)
	lwz %r7, 132(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 68(%r6)
	stw %r7, 132(%r6)
	lwz %r5, 72(%r6)
	lwz %r7, 136(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 72(%r6)
	stw %r7, 136(%r6)
	lwz %r5, 76(%r6)
	lwz %r7, 140(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 76(%r6)
	stw %r7, 140(%r6)
	lwz %r5, 80(%r6)
	lwz %r7, 144(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 80(%r6)
	stw %r7, 144(%r6)
	lwz %r5, 84(%r6)
	lwz %r7, 148(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 84(%r6)
	stw %r7, 148(%r6)
	lwz %r5, 88(%r6)
	lwz %r7, 152(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 88(%r6)
	stw %r7, 152(%r6)
	lwz %r5, 92(%r6)
	lwz %r7, 156(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 92(%r6)
	stw %r7, 156(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 64(%r6)
	ld %r5, 64(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 72(%r6)
	ld %r5, 64(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 64(%r6)
	ld %r5, 72(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 80(%r6)
	ld %r5, 64(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 72(%r6)
	ld %r5, 72(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 64(%r6)
	ld %r5, 80(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 88(%r6)
	ld %r5, 64(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 80(%r6)
	ld %r5, 72(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 72(%r6)
	ld %r5, 80(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 64(%r6)
	ld %r5, 88(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 88(%r6)
	ld %r5, 72(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 80(%r6)
	ld %r5, 80(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 72(%r6)
	ld %r5, 88(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 88(%r6)
	ld %r5, 80(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 80(%r6)
	ld %r5, 88(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 88(%r6)
	ld %r5, 88(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 160(%r6)
	std %r9, 168(%r6)
	std %r10, 176(%r6)
	std %r11, 184(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 160(%r6)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 168(%r6)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 160(%r6)
	ld %r5, 168(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 176(%r6)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 168(%r6)
	ld %r5, 168(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 160(%r6)
	ld %r5, 176(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 184(%r6)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 176(%r6)
	ld %r5, 168(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 168(%r6)
	ld %r5, 176(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 160(%r6)
	ld %r5, 184(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 184(%r6)
	ld %r5, 168(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 176(%r6)
	ld %r5, 176(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 168(%r6)
	ld %r5, 184(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 184(%r6)
	ld %r5, 176(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 176(%r6)
	ld %r5, 184(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 184(%r6)
	ld %r5, 184(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 192(%r6)
	std %r9, 200(%r6)
	std %r10, 208(%r6)
	std %r11, 216(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 192(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 200(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 192(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 208(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 200(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 192(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 216(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 208(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 200(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 192(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 216(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 208(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 200(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 216(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 208(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 216(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 192(%r6)
	std %r9, 200(%r6)
	std %r10, 208(%r6)
	std %r11, 216(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 64(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 72(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 64(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 80(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 72(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 64(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 88(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 80(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 72(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 64(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 88(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 80(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 72(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 88(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 80(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 88(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 192(%r6)
	std %r9, 200(%r6)
	std %r10, 208(%r6)
	std %r11, 216(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 160(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 168(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 160(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 176(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 168(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 160(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 184(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 176(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 168(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 160(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 184(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 176(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 168(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 184(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 176(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 184(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 160(%r6)
	std %r9, 168(%r6)
	std %r10, 176(%r6)
	std %r11, 184(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 160(%r6)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 168(%r6)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 160(%r6)
	ld %r5, 168(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 176(%r6)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 168(%r6)
	ld %r5, 168(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 160(%r6)
	ld %r5, 176(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 184(%r6)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 176(%r6)
	ld %r5, 168(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 168(%r6)
	ld %r5, 176(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 160(%r6)
	ld %r5, 184(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 184(%r6)
	ld %r5, 168(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 176(%r6)
	ld %r5, 176(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 168(%r6)
	ld %r5, 184(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 184(%r6)
	ld %r5, 176(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 176(%r6)
	ld %r5, 184(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 184(%r6)
	ld %r5, 184(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 224(%r6)
	std %r9, 232(%r6)
	std %r10, 240(%r6)
	std %r11, 248(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 192(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 200(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 192(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 208(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 200(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 192(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 216(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 208(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 200(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 192(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 216(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 208(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 200(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 216(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 208(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 216(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 192(%r6)
	std %r9, 200(%r6)
	std %r10, 208(%r6)
	std %r11, 216(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 192(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 200(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 192(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 208(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 200(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 192(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 216(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 208(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 200(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 192(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 216(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 208(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 200(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 216(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 208(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 216(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 224(%r6)
	std %r9, 232(%r6)
	std %r10, 240(%r6)
	std %r11, 248(%r6)
	li %r12, 4
22:
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 224(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 232(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 224(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 240(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 232(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 224(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 240(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 232(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 224(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 248(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 240(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 232(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 248(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 240(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 224(%r6)
	std %r9, 232(%r6)
	std %r10, 240(%r6)
	std %r11, 248(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 22b
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 224(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 232(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 224(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 240(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 232(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 224(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 240(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 232(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 224(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 248(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 240(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 232(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 248(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 240(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 192(%r6)
	std %r9, 200(%r6)
	std %r10, 208(%r6)
	std %r11, 216(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 192(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 200(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 192(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 208(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 200(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 192(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 216(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 208(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 200(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 192(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 216(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 208(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 200(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 216(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 208(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 216(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 224(%r6)
	std %r9, 232(%r6)
	std %r10, 240(%r6)
	std %r11, 248(%r6)
	li %r12, 9
23:
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 224(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 232(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 224(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 240(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 232(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 224(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 240(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 232(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 224(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 248(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 240(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 232(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 248(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 240(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 224(%r6)
	std %r9, 232(%r6)
	std %r10, 240(%r6)
	std %r11, 248(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 23b
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 224(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 232(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 224(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 240(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 232(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 224(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 240(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 232(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 224(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 248(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 240(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 232(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 248(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 240(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 224(%r6)
	std %r9, 232(%r6)
	std %r10, 240(%r6)
	std %r11, 248(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 224(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 232(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 224(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 240(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 232(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 224(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 240(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 232(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 224(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 248(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 240(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 232(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 248(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 240(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 256(%r6)
	std %r9, 264(%r6)
	std %r10, 272(%r6)
	std %r11, 280(%r6)
	li %r12, 19
24:
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 256(%r6)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 264(%r6)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 256(%r6)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 272(%r6)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 264(%r6)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 256(%r6)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 280(%r6)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 272(%r6)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 264(%r6)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 256(%r6)
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 280(%r6)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 272(%r6)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 264(%r6)
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 280(%r6)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 272(%r6)
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 280(%r6)
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 256(%r6)
	std %r9, 264(%r6)
	std %r10, 272(%r6)
	std %r11, 280(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 24b
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 256(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 264(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 256(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 272(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 264(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 256(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 280(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 272(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 264(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 256(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 280(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 272(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 264(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 280(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 272(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 280(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 224(%r6)
	std %r9, 232(%r6)
	std %r10, 240(%r6)
	std %r11, 248(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 224(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 232(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 224(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 240(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 232(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 224(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 240(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 232(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 224(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 248(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 240(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 232(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 248(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 240(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 224(%r6)
	std %r9, 232(%r6)
	std %r10, 240(%r6)
	std %r11, 248(%r6)
	li %r12, 9
25:
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 224(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 232(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 224(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 240(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 232(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 224(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 240(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 232(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 224(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 248(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 240(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 232(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 248(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 240(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 224(%r6)
	std %r9, 232(%r6)
	std %r10, 240(%r6)
	std %r11, 248(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 25b
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 224(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 232(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 224(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 240(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 232(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 224(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 240(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 232(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 224(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 248(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 240(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 232(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 248(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 240(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 192(%r6)
	std %r9, 200(%r6)
	std %r10, 208(%r6)
	std %r11, 216(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 192(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 200(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 192(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 208(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 200(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 192(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 216(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 208(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 200(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 192(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 216(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 208(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 200(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 216(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 208(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 216(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 224(%r6)
	std %r9, 232(%r6)
	std %r10, 240(%r6)
	std %r11, 248(%r6)
	li %r12, 49
26:
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 224(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 232(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 224(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 240(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 232(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 224(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 240(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 232(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 224(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 248(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 240(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 232(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 248(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 240(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 224(%r6)
	std %r9, 232(%r6)
	std %r10, 240(%r6)
	std %r11, 248(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 26b
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 224(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 232(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 224(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 240(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 232(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 224(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 240(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 232(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 224(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 248(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 240(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 232(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 248(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 240(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 224(%r6)
	std %r9, 232(%r6)
	std %r10, 240(%r6)
	std %r11, 248(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 224(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 232(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 224(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 240(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 232(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 224(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 240(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 232(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 224(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 248(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 240(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 232(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 248(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 240(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 256(%r6)
	std %r9, 264(%r6)
	std %r10, 272(%r6)
	std %r11, 280(%r6)
	li %r12, 99
27:
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 256(%r6)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 264(%r6)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 256(%r6)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 272(%r6)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 264(%r6)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 256(%r6)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 280(%r6)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 272(%r6)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 264(%r6)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 256(%r6)
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 280(%r6)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 272(%r6)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 264(%r6)
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 280(%r6)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 272(%r6)
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 280(%r6)
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 256(%r6)
	std %r9, 264(%r6)
	std %r10, 272(%r6)
	std %r11, 280(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 27b
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 256(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 264(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 256(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 272(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 264(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 256(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 280(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 272(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 264(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 256(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 280(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 272(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 264(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 280(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 272(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 280(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 224(%r6)
	std %r9, 232(%r6)
	std %r10, 240(%r6)
	std %r11, 248(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 224(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 232(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 224(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 240(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 232(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 224(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 240(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 232(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 224(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 248(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 240(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 232(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 248(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 240(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 224(%r6)
	std %r9, 232(%r6)
	std %r10, 240(%r6)
	std %r11, 248(%r6)
	li %r12, 49
28:
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 224(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 232(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 224(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 240(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 232(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 224(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 240(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 232(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 224(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 248(%r6)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 240(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 232(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 248(%r6)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 240(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 224(%r6)
	std %r9, 232(%r6)
	std %r10, 240(%r6)
	std %r11, 248(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 28b
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 224(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 232(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 224(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 240(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 232(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 224(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 240(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 232(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 224(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 248(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 240(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 232(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 248(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 240(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 248(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 192(%r6)
	std %r9, 200(%r6)
	std %r10, 208(%r6)
	std %r11, 216(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 192(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 200(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 192(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 208(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 200(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 192(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 216(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 208(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 200(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 192(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 216(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 208(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 200(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 216(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 208(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 216(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 192(%r6)
	std %r9, 200(%r6)
	std %r10, 208(%r6)
	std %r11, 216(%r6)
	li %r12, 4
29:
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 192(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 200(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 192(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 208(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 200(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 192(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 216(%r6)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 208(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 200(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 192(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 216(%r6)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 208(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 200(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 216(%r6)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 208(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 216(%r6)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 192(%r6)
	std %r9, 200(%r6)
	std %r10, 208(%r6)
	std %r11, 216(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 29b
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 192(%r6)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 200(%r6)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 192(%r6)
	ld %r5, 168(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 208(%r6)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 200(%r6)
	ld %r5, 168(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 192(%r6)
	ld %r5, 176(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 216(%r6)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 208(%r6)
	ld %r5, 168(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 200(%r6)
	ld %r5, 176(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 192(%r6)
	ld %r5, 184(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 216(%r6)
	ld %r5, 168(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 208(%r6)
	ld %r5, 176(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 200(%r6)
	ld %r5, 184(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 216(%r6)
	ld %r5, 176(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 208(%r6)
	ld %r5, 184(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 216(%r6)
	ld %r5, 184(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 480(%r6)
	std %r9, 488(%r6)
	std %r10, 496(%r6)
	std %r11, 504(%r6)
	li %r8, 0
	li %r9, 0
	li %r10, 0
	ld %r4, 32(%r6)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 544(%r6)
	li %r8, 0
	ld %r4, 40(%r6)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 32(%r6)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 552(%r6)
	li %r9, 0
	ld %r4, 48(%r6)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 40(%r6)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 32(%r6)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 560(%r6)
	li %r10, 0
	ld %r4, 56(%r6)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 48(%r6)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 40(%r6)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	ld %r4, 32(%r6)
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 568(%r6)
	li %r8, 0
	ld %r4, 56(%r6)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 48(%r6)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	ld %r4, 40(%r6)
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r7
	adde %r10, %r10, %r4
	addze %r8, %r8
	std %r9, 576(%r6)
	li %r9, 0
	ld %r4, 56(%r6)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	ld %r4, 48(%r6)
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r10, %r10, %r7
	adde %r8, %r8, %r4
	addze %r9, %r9
	std %r10, 584(%r6)
	li %r10, 0
	ld %r4, 56(%r6)
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r4, %r4, %r5
	addc %r8, %r8, %r7
	adde %r9, %r9, %r4
	addze %r10, %r10
	std %r8, 592(%r6)
	li %r8, 0
	std %r9, 600(%r6)
	li %r9, 0
	li %r5, 38
	ld %r8, 544(%r6)
	ld %r4, 576(%r6)
	mulld %r4, %r4, %r5
	addc %r8, %r8, %r4
	ld %r9, 552(%r6)
	ld %r4, 584(%r6)
	mulld %r4, %r4, %r5
	adde %r9, %r9, %r4
	ld %r10, 560(%r6)
	ld %r4, 592(%r6)
	mulld %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r11, 568(%r6)
	ld %r4, 600(%r6)
	mulld %r4, %r4, %r5
	adde %r11, %r11, %r4
	li %r7, 0
	addze %r7, %r7
	ld %r4, 576(%r6)
	mulhdu %r4, %r4, %r5
	addc %r9, %r9, %r4
	ld %r4, 584(%r6)
	mulhdu %r4, %r4, %r5
	adde %r10, %r10, %r4
	ld %r4, 592(%r6)
	mulhdu %r4, %r4, %r5
	adde %r11, %r11, %r4
	ld %r4, 600(%r6)
	mulhdu %r4, %r4, %r5
	adde %r7, %r7, %r4
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	mulld %r4, %r7, %r5
	addc %r8, %r8, %r4
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	li %r7, 0
	addze %r7, %r7
	std %r8, 32(%r6)
	std %r9, 40(%r6)
	std %r10, 48(%r6)
	std %r11, 56(%r6)
	lwz %r7, 60(%r6)
	rldicl %r8, %r7, 33, 31
	rldicr %r7, %r7, 33, 30
	rldicl %r7, %r7, 31, 33
	stw %r7, 60(%r6)
	li %r5, 19
	mulld %r8, %r8, %r5
	lwz %r7, 32(%r6)
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 19
	lwz %r7, 32(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	rldicl %r11, %r7, 33, 31
	li %r4, 0
	subf %r11, %r11, %r4
	rldicr %r7, %r7, 33, 30
	rldicl %r7, %r7, 31, 33
	stw %r7, 540(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 512(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 0(%r3)
	lwz %r5, 36(%r6)
	lwz %r7, 516(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 4(%r3)
	lwz %r5, 40(%r6)
	lwz %r7, 520(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 8(%r3)
	lwz %r5, 44(%r6)
	lwz %r7, 524(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 12(%r3)
	lwz %r5, 48(%r6)
	lwz %r7, 528(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 16(%r3)
	lwz %r5, 52(%r6)
	lwz %r7, 532(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 20(%r3)
	lwz %r5, 56(%r6)
	lwz %r7, 536(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 24(%r3)
	lwz %r5, 60(%r6)
	lwz %r7, 540(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 28(%r3)
	blr
