// The functions of `src/x448.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x448_exchange:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	addi %r12, %r1, 0
	std %r3, 40(%r12)
	bl {vg_x448}
	addi %r12, %r1, 0
	ld %r12, 40(%r12)
	li %r11, 0
	lbz %r10, 0(%r12)
	or %r11, %r11, %r10
	lbz %r10, 1(%r12)
	or %r11, %r11, %r10
	lbz %r10, 2(%r12)
	or %r11, %r11, %r10
	lbz %r10, 3(%r12)
	or %r11, %r11, %r10
	lbz %r10, 4(%r12)
	or %r11, %r11, %r10
	lbz %r10, 5(%r12)
	or %r11, %r11, %r10
	lbz %r10, 6(%r12)
	or %r11, %r11, %r10
	lbz %r10, 7(%r12)
	or %r11, %r11, %r10
	lbz %r10, 8(%r12)
	or %r11, %r11, %r10
	lbz %r10, 9(%r12)
	or %r11, %r11, %r10
	lbz %r10, 10(%r12)
	or %r11, %r11, %r10
	lbz %r10, 11(%r12)
	or %r11, %r11, %r10
	lbz %r10, 12(%r12)
	or %r11, %r11, %r10
	lbz %r10, 13(%r12)
	or %r11, %r11, %r10
	lbz %r10, 14(%r12)
	or %r11, %r11, %r10
	lbz %r10, 15(%r12)
	or %r11, %r11, %r10
	lbz %r10, 16(%r12)
	or %r11, %r11, %r10
	lbz %r10, 17(%r12)
	or %r11, %r11, %r10
	lbz %r10, 18(%r12)
	or %r11, %r11, %r10
	lbz %r10, 19(%r12)
	or %r11, %r11, %r10
	lbz %r10, 20(%r12)
	or %r11, %r11, %r10
	lbz %r10, 21(%r12)
	or %r11, %r11, %r10
	lbz %r10, 22(%r12)
	or %r11, %r11, %r10
	lbz %r10, 23(%r12)
	or %r11, %r11, %r10
	lbz %r10, 24(%r12)
	or %r11, %r11, %r10
	lbz %r10, 25(%r12)
	or %r11, %r11, %r10
	lbz %r10, 26(%r12)
	or %r11, %r11, %r10
	lbz %r10, 27(%r12)
	or %r11, %r11, %r10
	lbz %r10, 28(%r12)
	or %r11, %r11, %r10
	lbz %r10, 29(%r12)
	or %r11, %r11, %r10
	lbz %r10, 30(%r12)
	or %r11, %r11, %r10
	lbz %r10, 31(%r12)
	or %r11, %r11, %r10
	lbz %r10, 32(%r12)
	or %r11, %r11, %r10
	lbz %r10, 33(%r12)
	or %r11, %r11, %r10
	lbz %r10, 34(%r12)
	or %r11, %r11, %r10
	lbz %r10, 35(%r12)
	or %r11, %r11, %r10
	lbz %r10, 36(%r12)
	or %r11, %r11, %r10
	lbz %r10, 37(%r12)
	or %r11, %r11, %r10
	lbz %r10, 38(%r12)
	or %r11, %r11, %r10
	lbz %r10, 39(%r12)
	or %r11, %r11, %r10
	lbz %r10, 40(%r12)
	or %r11, %r11, %r10
	lbz %r10, 41(%r12)
	or %r11, %r11, %r10
	lbz %r10, 42(%r12)
	or %r11, %r11, %r10
	lbz %r10, 43(%r12)
	or %r11, %r11, %r10
	lbz %r10, 44(%r12)
	or %r11, %r11, %r10
	lbz %r10, 45(%r12)
	or %r11, %r11, %r10
	lbz %r10, 46(%r12)
	or %r11, %r11, %r10
	lbz %r10, 47(%r12)
	or %r11, %r11, %r10
	lbz %r10, 48(%r12)
	or %r11, %r11, %r10
	lbz %r10, 49(%r12)
	or %r11, %r11, %r10
	lbz %r10, 50(%r12)
	or %r11, %r11, %r10
	lbz %r10, 51(%r12)
	or %r11, %r11, %r10
	lbz %r10, 52(%r12)
	or %r11, %r11, %r10
	lbz %r10, 53(%r12)
	or %r11, %r11, %r10
	lbz %r10, 54(%r12)
	or %r11, %r11, %r10
	lbz %r10, 55(%r12)
	or %r11, %r11, %r10
	addi %r11, %r11, -1
	rldicl %r3, %r11, 1, 63
	li %r10, 1
	xor %r3, %r3, %r10
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr

vg_x448_base:
	addi %r6, %r5, 0
	li %r7, 5
	li %r8, 0
	stw %r7, 0(%r6)
	stw %r7, 168(%r6)
	stw %r8, 4(%r6)
	stw %r8, 8(%r6)
	stw %r8, 12(%r6)
	stw %r8, 16(%r6)
	stw %r8, 20(%r6)
	stw %r8, 24(%r6)
	stw %r8, 28(%r6)
	stw %r8, 32(%r6)
	stw %r8, 36(%r6)
	stw %r8, 40(%r6)
	stw %r8, 44(%r6)
	stw %r8, 48(%r6)
	stw %r8, 52(%r6)
	stw %r8, 172(%r6)
	stw %r8, 176(%r6)
	stw %r8, 180(%r6)
	stw %r8, 184(%r6)
	stw %r8, 188(%r6)
	stw %r8, 192(%r6)
	stw %r8, 196(%r6)
	stw %r8, 200(%r6)
	stw %r8, 204(%r6)
	stw %r8, 208(%r6)
	stw %r8, 212(%r6)
	stw %r8, 216(%r6)
	stw %r8, 220(%r6)
	li %r7, 1
	li %r8, 0
	stw %r7, 56(%r6)
	stw %r8, 112(%r6)
	stw %r7, 224(%r6)
	stw %r8, 60(%r6)
	stw %r8, 64(%r6)
	stw %r8, 68(%r6)
	stw %r8, 72(%r6)
	stw %r8, 76(%r6)
	stw %r8, 80(%r6)
	stw %r8, 84(%r6)
	stw %r8, 88(%r6)
	stw %r8, 92(%r6)
	stw %r8, 96(%r6)
	stw %r8, 100(%r6)
	stw %r8, 104(%r6)
	stw %r8, 108(%r6)
	stw %r8, 116(%r6)
	stw %r8, 120(%r6)
	stw %r8, 124(%r6)
	stw %r8, 128(%r6)
	stw %r8, 132(%r6)
	stw %r8, 136(%r6)
	stw %r8, 140(%r6)
	stw %r8, 144(%r6)
	stw %r8, 148(%r6)
	stw %r8, 152(%r6)
	stw %r8, 156(%r6)
	stw %r8, 160(%r6)
	stw %r8, 164(%r6)
	stw %r8, 228(%r6)
	stw %r8, 232(%r6)
	stw %r8, 236(%r6)
	stw %r8, 240(%r6)
	stw %r8, 244(%r6)
	stw %r8, 248(%r6)
	stw %r8, 252(%r6)
	stw %r8, 256(%r6)
	stw %r8, 260(%r6)
	stw %r8, 264(%r6)
	stw %r8, 268(%r6)
	stw %r8, 272(%r6)
	stw %r8, 276(%r6)
	std %r15, 1512(%r6)
	std %r16, 1520(%r6)
	std %r17, 1528(%r6)
	std %r18, 1536(%r6)
	std %r19, 1544(%r6)
	std %r20, 1552(%r6)
	std %r21, 1560(%r6)
	std %r22, 1568(%r6)
	std %r23, 1576(%r6)
	std %r24, 1584(%r6)
	std %r25, 1592(%r6)
	std %r26, 1600(%r6)
	std %r27, 1608(%r6)
	std %r28, 1616(%r6)
	std %r29, 1624(%r6)
	std %r30, 1632(%r6)
	std %r31, 1640(%r6)
	addi %r9, %r6, 0
	li %r11, 56
20:
	lbz %r7, 0(%r4)
	rldicr %r8, %r7, 63, 0
	rldicl %r8, %r8, 1, 63
	stb %r8, 1064(%r9)
	rldicr %r8, %r7, 62, 1
	rldicl %r8, %r8, 1, 63
	stb %r8, 1065(%r9)
	rldicr %r8, %r7, 61, 2
	rldicl %r8, %r8, 1, 63
	stb %r8, 1066(%r9)
	rldicr %r8, %r7, 60, 3
	rldicl %r8, %r8, 1, 63
	stb %r8, 1067(%r9)
	rldicr %r8, %r7, 59, 4
	rldicl %r8, %r8, 1, 63
	stb %r8, 1068(%r9)
	rldicr %r8, %r7, 58, 5
	rldicl %r8, %r8, 1, 63
	stb %r8, 1069(%r9)
	rldicr %r8, %r7, 57, 6
	rldicl %r8, %r8, 1, 63
	stb %r8, 1070(%r9)
	rldicr %r8, %r7, 56, 7
	rldicl %r8, %r8, 1, 63
	stb %r8, 1071(%r9)
	addi %r4, %r4, 1
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 20b
	li %r7, 0
	stb %r7, 1064(%r6)
	stb %r7, 1065(%r6)
	li %r7, 1
	stb %r7, 1511(%r6)
	li %r12, 448
	li %r0, 0
21:
	addi %r12, %r12, -1
	add %r4, %r6, %r12
	lbz %r4, 1064(%r4)
	xor %r0, %r0, %r4
	li %r11, 0
	subf %r11, %r0, %r11
	lwz %r5, 56(%r6)
	lwz %r7, 168(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 56(%r6)
	stw %r7, 168(%r6)
	lwz %r5, 60(%r6)
	lwz %r7, 172(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 60(%r6)
	stw %r7, 172(%r6)
	lwz %r5, 64(%r6)
	lwz %r7, 176(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 64(%r6)
	stw %r7, 176(%r6)
	lwz %r5, 68(%r6)
	lwz %r7, 180(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 68(%r6)
	stw %r7, 180(%r6)
	lwz %r5, 72(%r6)
	lwz %r7, 184(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 72(%r6)
	stw %r7, 184(%r6)
	lwz %r5, 76(%r6)
	lwz %r7, 188(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 76(%r6)
	stw %r7, 188(%r6)
	lwz %r5, 80(%r6)
	lwz %r7, 192(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 80(%r6)
	stw %r7, 192(%r6)
	lwz %r5, 84(%r6)
	lwz %r7, 196(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 84(%r6)
	stw %r7, 196(%r6)
	lwz %r5, 88(%r6)
	lwz %r7, 200(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 88(%r6)
	stw %r7, 200(%r6)
	lwz %r5, 92(%r6)
	lwz %r7, 204(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 92(%r6)
	stw %r7, 204(%r6)
	lwz %r5, 96(%r6)
	lwz %r7, 208(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 96(%r6)
	stw %r7, 208(%r6)
	lwz %r5, 100(%r6)
	lwz %r7, 212(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 100(%r6)
	stw %r7, 212(%r6)
	lwz %r5, 104(%r6)
	lwz %r7, 216(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 104(%r6)
	stw %r7, 216(%r6)
	lwz %r5, 108(%r6)
	lwz %r7, 220(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 108(%r6)
	stw %r7, 220(%r6)
	lwz %r5, 112(%r6)
	lwz %r7, 224(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 224(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 228(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 228(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 232(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 232(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 236(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 236(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 240(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 240(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 244(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 244(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 248(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 248(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 252(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 252(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 256(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 256(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 260(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 260(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 264(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 264(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 268(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 268(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 272(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 272(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 276(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 276(%r6)
	addi %r0, %r4, 0
	ld %r7, 56(%r6)
	ld %r8, 112(%r6)
	addc %r7, %r7, %r8
	std %r7, 280(%r6)
	ld %r7, 64(%r6)
	ld %r8, 120(%r6)
	adde %r7, %r7, %r8
	std %r7, 288(%r6)
	ld %r7, 72(%r6)
	ld %r8, 128(%r6)
	adde %r7, %r7, %r8
	std %r7, 296(%r6)
	ld %r7, 80(%r6)
	ld %r8, 136(%r6)
	adde %r7, %r7, %r8
	std %r7, 304(%r6)
	ld %r7, 88(%r6)
	ld %r8, 144(%r6)
	adde %r7, %r7, %r8
	std %r7, 312(%r6)
	ld %r7, 96(%r6)
	ld %r8, 152(%r6)
	adde %r7, %r7, %r8
	std %r7, 320(%r6)
	ld %r7, 104(%r6)
	ld %r8, 160(%r6)
	adde %r7, %r7, %r8
	std %r7, 328(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 280(%r6)
	addc %r7, %r7, %r4
	std %r7, 280(%r6)
	ld %r7, 288(%r6)
	adde %r7, %r7, %r8
	std %r7, 288(%r6)
	ld %r7, 296(%r6)
	adde %r7, %r7, %r8
	std %r7, 296(%r6)
	ld %r7, 304(%r6)
	adde %r7, %r7, %r5
	std %r7, 304(%r6)
	ld %r7, 312(%r6)
	adde %r7, %r7, %r8
	std %r7, 312(%r6)
	ld %r7, 320(%r6)
	adde %r7, %r7, %r8
	std %r7, 320(%r6)
	ld %r7, 328(%r6)
	adde %r7, %r7, %r8
	std %r7, 328(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 280(%r6)
	addc %r7, %r7, %r4
	std %r7, 280(%r6)
	ld %r7, 288(%r6)
	adde %r7, %r7, %r8
	std %r7, 288(%r6)
	ld %r7, 296(%r6)
	adde %r7, %r7, %r8
	std %r7, 296(%r6)
	ld %r7, 304(%r6)
	adde %r7, %r7, %r5
	std %r7, 304(%r6)
	ld %r7, 312(%r6)
	adde %r7, %r7, %r8
	std %r7, 312(%r6)
	ld %r7, 320(%r6)
	adde %r7, %r7, %r8
	std %r7, 320(%r6)
	ld %r7, 328(%r6)
	adde %r7, %r7, %r8
	std %r7, 328(%r6)
	ld %r15, 280(%r6)
	ld %r16, 288(%r6)
	ld %r17, 296(%r6)
	ld %r18, 304(%r6)
	ld %r19, 312(%r6)
	ld %r20, 320(%r6)
	ld %r21, 328(%r6)
	ld %r22, 280(%r6)
	ld %r23, 288(%r6)
	ld %r24, 296(%r6)
	ld %r25, 304(%r6)
	ld %r26, 312(%r6)
	ld %r27, 320(%r6)
	ld %r28, 328(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 504(%r6)
	std %r8, 512(%r6)
	std %r9, 520(%r6)
	std %r10, 528(%r6)
	std %r11, 536(%r6)
	std %r29, 544(%r6)
	std %r30, 552(%r6)
	ld %r7, 56(%r6)
	ld %r8, 112(%r6)
	subfc %r7, %r8, %r7
	std %r7, 336(%r6)
	ld %r7, 64(%r6)
	ld %r8, 120(%r6)
	subfe %r7, %r8, %r7
	std %r7, 344(%r6)
	ld %r7, 72(%r6)
	ld %r8, 128(%r6)
	subfe %r7, %r8, %r7
	std %r7, 352(%r6)
	ld %r7, 80(%r6)
	ld %r8, 136(%r6)
	subfe %r7, %r8, %r7
	std %r7, 360(%r6)
	ld %r7, 88(%r6)
	ld %r8, 144(%r6)
	subfe %r7, %r8, %r7
	std %r7, 368(%r6)
	ld %r7, 96(%r6)
	ld %r8, 152(%r6)
	subfe %r7, %r8, %r7
	std %r7, 376(%r6)
	ld %r7, 104(%r6)
	ld %r8, 160(%r6)
	subfe %r7, %r8, %r7
	std %r7, 384(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 336(%r6)
	subfc %r7, %r4, %r7
	std %r7, 336(%r6)
	ld %r7, 344(%r6)
	subfe %r7, %r8, %r7
	std %r7, 344(%r6)
	ld %r7, 352(%r6)
	subfe %r7, %r8, %r7
	std %r7, 352(%r6)
	ld %r7, 360(%r6)
	subfe %r7, %r5, %r7
	std %r7, 360(%r6)
	ld %r7, 368(%r6)
	subfe %r7, %r8, %r7
	std %r7, 368(%r6)
	ld %r7, 376(%r6)
	subfe %r7, %r8, %r7
	std %r7, 376(%r6)
	ld %r7, 384(%r6)
	subfe %r7, %r8, %r7
	std %r7, 384(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 336(%r6)
	subfc %r7, %r4, %r7
	std %r7, 336(%r6)
	ld %r7, 344(%r6)
	subfe %r7, %r8, %r7
	std %r7, 344(%r6)
	ld %r7, 352(%r6)
	subfe %r7, %r8, %r7
	std %r7, 352(%r6)
	ld %r7, 360(%r6)
	subfe %r7, %r5, %r7
	std %r7, 360(%r6)
	ld %r7, 368(%r6)
	subfe %r7, %r8, %r7
	std %r7, 368(%r6)
	ld %r7, 376(%r6)
	subfe %r7, %r8, %r7
	std %r7, 376(%r6)
	ld %r7, 384(%r6)
	subfe %r7, %r8, %r7
	std %r7, 384(%r6)
	ld %r15, 336(%r6)
	ld %r16, 344(%r6)
	ld %r17, 352(%r6)
	ld %r18, 360(%r6)
	ld %r19, 368(%r6)
	ld %r20, 376(%r6)
	ld %r21, 384(%r6)
	ld %r22, 336(%r6)
	ld %r23, 344(%r6)
	ld %r24, 352(%r6)
	ld %r25, 360(%r6)
	ld %r26, 368(%r6)
	ld %r27, 376(%r6)
	ld %r28, 384(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 560(%r6)
	std %r8, 568(%r6)
	std %r9, 576(%r6)
	std %r10, 584(%r6)
	std %r11, 592(%r6)
	std %r29, 600(%r6)
	std %r30, 608(%r6)
	ld %r7, 504(%r6)
	ld %r8, 560(%r6)
	subfc %r7, %r8, %r7
	std %r7, 616(%r6)
	ld %r7, 512(%r6)
	ld %r8, 568(%r6)
	subfe %r7, %r8, %r7
	std %r7, 624(%r6)
	ld %r7, 520(%r6)
	ld %r8, 576(%r6)
	subfe %r7, %r8, %r7
	std %r7, 632(%r6)
	ld %r7, 528(%r6)
	ld %r8, 584(%r6)
	subfe %r7, %r8, %r7
	std %r7, 640(%r6)
	ld %r7, 536(%r6)
	ld %r8, 592(%r6)
	subfe %r7, %r8, %r7
	std %r7, 648(%r6)
	ld %r7, 544(%r6)
	ld %r8, 600(%r6)
	subfe %r7, %r8, %r7
	std %r7, 656(%r6)
	ld %r7, 552(%r6)
	ld %r8, 608(%r6)
	subfe %r7, %r8, %r7
	std %r7, 664(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 616(%r6)
	subfc %r7, %r4, %r7
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	subfe %r7, %r8, %r7
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	subfe %r7, %r8, %r7
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	subfe %r7, %r5, %r7
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	subfe %r7, %r8, %r7
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	subfe %r7, %r8, %r7
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	subfe %r7, %r8, %r7
	std %r7, 664(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 616(%r6)
	subfc %r7, %r4, %r7
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	subfe %r7, %r8, %r7
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	subfe %r7, %r8, %r7
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	subfe %r7, %r5, %r7
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	subfe %r7, %r8, %r7
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	subfe %r7, %r8, %r7
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	subfe %r7, %r8, %r7
	std %r7, 664(%r6)
	ld %r7, 168(%r6)
	ld %r8, 224(%r6)
	addc %r7, %r7, %r8
	std %r7, 392(%r6)
	ld %r7, 176(%r6)
	ld %r8, 232(%r6)
	adde %r7, %r7, %r8
	std %r7, 400(%r6)
	ld %r7, 184(%r6)
	ld %r8, 240(%r6)
	adde %r7, %r7, %r8
	std %r7, 408(%r6)
	ld %r7, 192(%r6)
	ld %r8, 248(%r6)
	adde %r7, %r7, %r8
	std %r7, 416(%r6)
	ld %r7, 200(%r6)
	ld %r8, 256(%r6)
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 208(%r6)
	ld %r8, 264(%r6)
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 216(%r6)
	ld %r8, 272(%r6)
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 392(%r6)
	addc %r7, %r7, %r4
	std %r7, 392(%r6)
	ld %r7, 400(%r6)
	adde %r7, %r7, %r8
	std %r7, 400(%r6)
	ld %r7, 408(%r6)
	adde %r7, %r7, %r8
	std %r7, 408(%r6)
	ld %r7, 416(%r6)
	adde %r7, %r7, %r5
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 392(%r6)
	addc %r7, %r7, %r4
	std %r7, 392(%r6)
	ld %r7, 400(%r6)
	adde %r7, %r7, %r8
	std %r7, 400(%r6)
	ld %r7, 408(%r6)
	adde %r7, %r7, %r8
	std %r7, 408(%r6)
	ld %r7, 416(%r6)
	adde %r7, %r7, %r5
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
	ld %r7, 168(%r6)
	ld %r8, 224(%r6)
	subfc %r7, %r8, %r7
	std %r7, 448(%r6)
	ld %r7, 176(%r6)
	ld %r8, 232(%r6)
	subfe %r7, %r8, %r7
	std %r7, 456(%r6)
	ld %r7, 184(%r6)
	ld %r8, 240(%r6)
	subfe %r7, %r8, %r7
	std %r7, 464(%r6)
	ld %r7, 192(%r6)
	ld %r8, 248(%r6)
	subfe %r7, %r8, %r7
	std %r7, 472(%r6)
	ld %r7, 200(%r6)
	ld %r8, 256(%r6)
	subfe %r7, %r8, %r7
	std %r7, 480(%r6)
	ld %r7, 208(%r6)
	ld %r8, 264(%r6)
	subfe %r7, %r8, %r7
	std %r7, 488(%r6)
	ld %r7, 216(%r6)
	ld %r8, 272(%r6)
	subfe %r7, %r8, %r7
	std %r7, 496(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 448(%r6)
	subfc %r7, %r4, %r7
	std %r7, 448(%r6)
	ld %r7, 456(%r6)
	subfe %r7, %r8, %r7
	std %r7, 456(%r6)
	ld %r7, 464(%r6)
	subfe %r7, %r8, %r7
	std %r7, 464(%r6)
	ld %r7, 472(%r6)
	subfe %r7, %r5, %r7
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	subfe %r7, %r8, %r7
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	subfe %r7, %r8, %r7
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	subfe %r7, %r8, %r7
	std %r7, 496(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 448(%r6)
	subfc %r7, %r4, %r7
	std %r7, 448(%r6)
	ld %r7, 456(%r6)
	subfe %r7, %r8, %r7
	std %r7, 456(%r6)
	ld %r7, 464(%r6)
	subfe %r7, %r8, %r7
	std %r7, 464(%r6)
	ld %r7, 472(%r6)
	subfe %r7, %r5, %r7
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	subfe %r7, %r8, %r7
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	subfe %r7, %r8, %r7
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	subfe %r7, %r8, %r7
	std %r7, 496(%r6)
	ld %r15, 448(%r6)
	ld %r16, 456(%r6)
	ld %r17, 464(%r6)
	ld %r18, 472(%r6)
	ld %r19, 480(%r6)
	ld %r20, 488(%r6)
	ld %r21, 496(%r6)
	ld %r22, 280(%r6)
	ld %r23, 288(%r6)
	ld %r24, 296(%r6)
	ld %r25, 304(%r6)
	ld %r26, 312(%r6)
	ld %r27, 320(%r6)
	ld %r28, 328(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 672(%r6)
	std %r8, 680(%r6)
	std %r9, 688(%r6)
	std %r10, 696(%r6)
	std %r11, 704(%r6)
	std %r29, 712(%r6)
	std %r30, 720(%r6)
	ld %r15, 392(%r6)
	ld %r16, 400(%r6)
	ld %r17, 408(%r6)
	ld %r18, 416(%r6)
	ld %r19, 424(%r6)
	ld %r20, 432(%r6)
	ld %r21, 440(%r6)
	ld %r22, 336(%r6)
	ld %r23, 344(%r6)
	ld %r24, 352(%r6)
	ld %r25, 360(%r6)
	ld %r26, 368(%r6)
	ld %r27, 376(%r6)
	ld %r28, 384(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 728(%r6)
	std %r8, 736(%r6)
	std %r9, 744(%r6)
	std %r10, 752(%r6)
	std %r11, 760(%r6)
	std %r29, 768(%r6)
	std %r30, 776(%r6)
	ld %r7, 672(%r6)
	ld %r8, 728(%r6)
	addc %r7, %r7, %r8
	std %r7, 168(%r6)
	ld %r7, 680(%r6)
	ld %r8, 736(%r6)
	adde %r7, %r7, %r8
	std %r7, 176(%r6)
	ld %r7, 688(%r6)
	ld %r8, 744(%r6)
	adde %r7, %r7, %r8
	std %r7, 184(%r6)
	ld %r7, 696(%r6)
	ld %r8, 752(%r6)
	adde %r7, %r7, %r8
	std %r7, 192(%r6)
	ld %r7, 704(%r6)
	ld %r8, 760(%r6)
	adde %r7, %r7, %r8
	std %r7, 200(%r6)
	ld %r7, 712(%r6)
	ld %r8, 768(%r6)
	adde %r7, %r7, %r8
	std %r7, 208(%r6)
	ld %r7, 720(%r6)
	ld %r8, 776(%r6)
	adde %r7, %r7, %r8
	std %r7, 216(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 168(%r6)
	addc %r7, %r7, %r4
	std %r7, 168(%r6)
	ld %r7, 176(%r6)
	adde %r7, %r7, %r8
	std %r7, 176(%r6)
	ld %r7, 184(%r6)
	adde %r7, %r7, %r8
	std %r7, 184(%r6)
	ld %r7, 192(%r6)
	adde %r7, %r7, %r5
	std %r7, 192(%r6)
	ld %r7, 200(%r6)
	adde %r7, %r7, %r8
	std %r7, 200(%r6)
	ld %r7, 208(%r6)
	adde %r7, %r7, %r8
	std %r7, 208(%r6)
	ld %r7, 216(%r6)
	adde %r7, %r7, %r8
	std %r7, 216(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 168(%r6)
	addc %r7, %r7, %r4
	std %r7, 168(%r6)
	ld %r7, 176(%r6)
	adde %r7, %r7, %r8
	std %r7, 176(%r6)
	ld %r7, 184(%r6)
	adde %r7, %r7, %r8
	std %r7, 184(%r6)
	ld %r7, 192(%r6)
	adde %r7, %r7, %r5
	std %r7, 192(%r6)
	ld %r7, 200(%r6)
	adde %r7, %r7, %r8
	std %r7, 200(%r6)
	ld %r7, 208(%r6)
	adde %r7, %r7, %r8
	std %r7, 208(%r6)
	ld %r7, 216(%r6)
	adde %r7, %r7, %r8
	std %r7, 216(%r6)
	ld %r15, 168(%r6)
	ld %r16, 176(%r6)
	ld %r17, 184(%r6)
	ld %r18, 192(%r6)
	ld %r19, 200(%r6)
	ld %r20, 208(%r6)
	ld %r21, 216(%r6)
	ld %r22, 168(%r6)
	ld %r23, 176(%r6)
	ld %r24, 184(%r6)
	ld %r25, 192(%r6)
	ld %r26, 200(%r6)
	ld %r27, 208(%r6)
	ld %r28, 216(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 168(%r6)
	std %r8, 176(%r6)
	std %r9, 184(%r6)
	std %r10, 192(%r6)
	std %r11, 200(%r6)
	std %r29, 208(%r6)
	std %r30, 216(%r6)
	ld %r7, 672(%r6)
	ld %r8, 728(%r6)
	subfc %r7, %r8, %r7
	std %r7, 224(%r6)
	ld %r7, 680(%r6)
	ld %r8, 736(%r6)
	subfe %r7, %r8, %r7
	std %r7, 232(%r6)
	ld %r7, 688(%r6)
	ld %r8, 744(%r6)
	subfe %r7, %r8, %r7
	std %r7, 240(%r6)
	ld %r7, 696(%r6)
	ld %r8, 752(%r6)
	subfe %r7, %r8, %r7
	std %r7, 248(%r6)
	ld %r7, 704(%r6)
	ld %r8, 760(%r6)
	subfe %r7, %r8, %r7
	std %r7, 256(%r6)
	ld %r7, 712(%r6)
	ld %r8, 768(%r6)
	subfe %r7, %r8, %r7
	std %r7, 264(%r6)
	ld %r7, 720(%r6)
	ld %r8, 776(%r6)
	subfe %r7, %r8, %r7
	std %r7, 272(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 224(%r6)
	subfc %r7, %r4, %r7
	std %r7, 224(%r6)
	ld %r7, 232(%r6)
	subfe %r7, %r8, %r7
	std %r7, 232(%r6)
	ld %r7, 240(%r6)
	subfe %r7, %r8, %r7
	std %r7, 240(%r6)
	ld %r7, 248(%r6)
	subfe %r7, %r5, %r7
	std %r7, 248(%r6)
	ld %r7, 256(%r6)
	subfe %r7, %r8, %r7
	std %r7, 256(%r6)
	ld %r7, 264(%r6)
	subfe %r7, %r8, %r7
	std %r7, 264(%r6)
	ld %r7, 272(%r6)
	subfe %r7, %r8, %r7
	std %r7, 272(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 224(%r6)
	subfc %r7, %r4, %r7
	std %r7, 224(%r6)
	ld %r7, 232(%r6)
	subfe %r7, %r8, %r7
	std %r7, 232(%r6)
	ld %r7, 240(%r6)
	subfe %r7, %r8, %r7
	std %r7, 240(%r6)
	ld %r7, 248(%r6)
	subfe %r7, %r5, %r7
	std %r7, 248(%r6)
	ld %r7, 256(%r6)
	subfe %r7, %r8, %r7
	std %r7, 256(%r6)
	ld %r7, 264(%r6)
	subfe %r7, %r8, %r7
	std %r7, 264(%r6)
	ld %r7, 272(%r6)
	subfe %r7, %r8, %r7
	std %r7, 272(%r6)
	ld %r15, 224(%r6)
	ld %r16, 232(%r6)
	ld %r17, 240(%r6)
	ld %r18, 248(%r6)
	ld %r19, 256(%r6)
	ld %r20, 264(%r6)
	ld %r21, 272(%r6)
	ld %r22, 224(%r6)
	ld %r23, 232(%r6)
	ld %r24, 240(%r6)
	ld %r25, 248(%r6)
	ld %r26, 256(%r6)
	ld %r27, 264(%r6)
	ld %r28, 272(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 224(%r6)
	std %r8, 232(%r6)
	std %r9, 240(%r6)
	std %r10, 248(%r6)
	std %r11, 256(%r6)
	std %r29, 264(%r6)
	std %r30, 272(%r6)
	ld %r15, 0(%r6)
	ld %r16, 8(%r6)
	ld %r17, 16(%r6)
	ld %r18, 24(%r6)
	ld %r19, 32(%r6)
	ld %r20, 40(%r6)
	ld %r21, 48(%r6)
	ld %r22, 224(%r6)
	ld %r23, 232(%r6)
	ld %r24, 240(%r6)
	ld %r25, 248(%r6)
	ld %r26, 256(%r6)
	ld %r27, 264(%r6)
	ld %r28, 272(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 224(%r6)
	std %r8, 232(%r6)
	std %r9, 240(%r6)
	std %r10, 248(%r6)
	std %r11, 256(%r6)
	std %r29, 264(%r6)
	std %r30, 272(%r6)
	ld %r15, 504(%r6)
	ld %r16, 512(%r6)
	ld %r17, 520(%r6)
	ld %r18, 528(%r6)
	ld %r19, 536(%r6)
	ld %r20, 544(%r6)
	ld %r21, 552(%r6)
	ld %r22, 560(%r6)
	ld %r23, 568(%r6)
	ld %r24, 576(%r6)
	ld %r25, 584(%r6)
	ld %r26, 592(%r6)
	ld %r27, 600(%r6)
	ld %r28, 608(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 56(%r6)
	std %r8, 64(%r6)
	std %r9, 72(%r6)
	std %r10, 80(%r6)
	std %r11, 88(%r6)
	std %r29, 96(%r6)
	std %r30, 104(%r6)
	li %r5, 0
	ori %r5, %r5, 39081
	li %r7, 0
	ld %r8, 616(%r6)
	mulld %r9, %r8, %r5
	addc %r9, %r9, %r7
	mulhdu %r7, %r8, %r5
	std %r9, 112(%r6)
	ld %r8, 624(%r6)
	mulld %r9, %r8, %r5
	adde %r9, %r9, %r7
	mulhdu %r7, %r8, %r5
	std %r9, 120(%r6)
	ld %r8, 632(%r6)
	mulld %r9, %r8, %r5
	adde %r9, %r9, %r7
	mulhdu %r7, %r8, %r5
	std %r9, 128(%r6)
	ld %r8, 640(%r6)
	mulld %r9, %r8, %r5
	adde %r9, %r9, %r7
	mulhdu %r7, %r8, %r5
	std %r9, 136(%r6)
	ld %r8, 648(%r6)
	mulld %r9, %r8, %r5
	adde %r9, %r9, %r7
	mulhdu %r7, %r8, %r5
	std %r9, 144(%r6)
	ld %r8, 656(%r6)
	mulld %r9, %r8, %r5
	adde %r9, %r9, %r7
	mulhdu %r7, %r8, %r5
	std %r9, 152(%r6)
	ld %r8, 664(%r6)
	mulld %r9, %r8, %r5
	adde %r9, %r9, %r7
	mulhdu %r7, %r8, %r5
	std %r9, 160(%r6)
	addze %r4, %r7
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 112(%r6)
	addc %r7, %r7, %r4
	std %r7, 112(%r6)
	ld %r7, 120(%r6)
	adde %r7, %r7, %r8
	std %r7, 120(%r6)
	ld %r7, 128(%r6)
	adde %r7, %r7, %r8
	std %r7, 128(%r6)
	ld %r7, 136(%r6)
	adde %r7, %r7, %r5
	std %r7, 136(%r6)
	ld %r7, 144(%r6)
	adde %r7, %r7, %r8
	std %r7, 144(%r6)
	ld %r7, 152(%r6)
	adde %r7, %r7, %r8
	std %r7, 152(%r6)
	ld %r7, 160(%r6)
	adde %r7, %r7, %r8
	std %r7, 160(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 112(%r6)
	addc %r7, %r7, %r4
	std %r7, 112(%r6)
	ld %r7, 120(%r6)
	adde %r7, %r7, %r8
	std %r7, 120(%r6)
	ld %r7, 128(%r6)
	adde %r7, %r7, %r8
	std %r7, 128(%r6)
	ld %r7, 136(%r6)
	adde %r7, %r7, %r5
	std %r7, 136(%r6)
	ld %r7, 144(%r6)
	adde %r7, %r7, %r8
	std %r7, 144(%r6)
	ld %r7, 152(%r6)
	adde %r7, %r7, %r8
	std %r7, 152(%r6)
	ld %r7, 160(%r6)
	adde %r7, %r7, %r8
	std %r7, 160(%r6)
	ld %r7, 504(%r6)
	ld %r8, 112(%r6)
	addc %r7, %r7, %r8
	std %r7, 112(%r6)
	ld %r7, 512(%r6)
	ld %r8, 120(%r6)
	adde %r7, %r7, %r8
	std %r7, 120(%r6)
	ld %r7, 520(%r6)
	ld %r8, 128(%r6)
	adde %r7, %r7, %r8
	std %r7, 128(%r6)
	ld %r7, 528(%r6)
	ld %r8, 136(%r6)
	adde %r7, %r7, %r8
	std %r7, 136(%r6)
	ld %r7, 536(%r6)
	ld %r8, 144(%r6)
	adde %r7, %r7, %r8
	std %r7, 144(%r6)
	ld %r7, 544(%r6)
	ld %r8, 152(%r6)
	adde %r7, %r7, %r8
	std %r7, 152(%r6)
	ld %r7, 552(%r6)
	ld %r8, 160(%r6)
	adde %r7, %r7, %r8
	std %r7, 160(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 112(%r6)
	addc %r7, %r7, %r4
	std %r7, 112(%r6)
	ld %r7, 120(%r6)
	adde %r7, %r7, %r8
	std %r7, 120(%r6)
	ld %r7, 128(%r6)
	adde %r7, %r7, %r8
	std %r7, 128(%r6)
	ld %r7, 136(%r6)
	adde %r7, %r7, %r5
	std %r7, 136(%r6)
	ld %r7, 144(%r6)
	adde %r7, %r7, %r8
	std %r7, 144(%r6)
	ld %r7, 152(%r6)
	adde %r7, %r7, %r8
	std %r7, 152(%r6)
	ld %r7, 160(%r6)
	adde %r7, %r7, %r8
	std %r7, 160(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 112(%r6)
	addc %r7, %r7, %r4
	std %r7, 112(%r6)
	ld %r7, 120(%r6)
	adde %r7, %r7, %r8
	std %r7, 120(%r6)
	ld %r7, 128(%r6)
	adde %r7, %r7, %r8
	std %r7, 128(%r6)
	ld %r7, 136(%r6)
	adde %r7, %r7, %r5
	std %r7, 136(%r6)
	ld %r7, 144(%r6)
	adde %r7, %r7, %r8
	std %r7, 144(%r6)
	ld %r7, 152(%r6)
	adde %r7, %r7, %r8
	std %r7, 152(%r6)
	ld %r7, 160(%r6)
	adde %r7, %r7, %r8
	std %r7, 160(%r6)
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 112(%r6)
	ld %r23, 120(%r6)
	ld %r24, 128(%r6)
	ld %r25, 136(%r6)
	ld %r26, 144(%r6)
	ld %r27, 152(%r6)
	ld %r28, 160(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 112(%r6)
	std %r8, 120(%r6)
	std %r9, 128(%r6)
	std %r10, 136(%r6)
	std %r11, 144(%r6)
	std %r29, 152(%r6)
	std %r30, 160(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 21b
	li %r11, 0
	subf %r11, %r0, %r11
	lwz %r5, 56(%r6)
	lwz %r7, 168(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 56(%r6)
	stw %r7, 168(%r6)
	lwz %r5, 60(%r6)
	lwz %r7, 172(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 60(%r6)
	stw %r7, 172(%r6)
	lwz %r5, 64(%r6)
	lwz %r7, 176(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 64(%r6)
	stw %r7, 176(%r6)
	lwz %r5, 68(%r6)
	lwz %r7, 180(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 68(%r6)
	stw %r7, 180(%r6)
	lwz %r5, 72(%r6)
	lwz %r7, 184(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 72(%r6)
	stw %r7, 184(%r6)
	lwz %r5, 76(%r6)
	lwz %r7, 188(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 76(%r6)
	stw %r7, 188(%r6)
	lwz %r5, 80(%r6)
	lwz %r7, 192(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 80(%r6)
	stw %r7, 192(%r6)
	lwz %r5, 84(%r6)
	lwz %r7, 196(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 84(%r6)
	stw %r7, 196(%r6)
	lwz %r5, 88(%r6)
	lwz %r7, 200(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 88(%r6)
	stw %r7, 200(%r6)
	lwz %r5, 92(%r6)
	lwz %r7, 204(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 92(%r6)
	stw %r7, 204(%r6)
	lwz %r5, 96(%r6)
	lwz %r7, 208(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 96(%r6)
	stw %r7, 208(%r6)
	lwz %r5, 100(%r6)
	lwz %r7, 212(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 100(%r6)
	stw %r7, 212(%r6)
	lwz %r5, 104(%r6)
	lwz %r7, 216(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 104(%r6)
	stw %r7, 216(%r6)
	lwz %r5, 108(%r6)
	lwz %r7, 220(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 108(%r6)
	stw %r7, 220(%r6)
	lwz %r5, 112(%r6)
	lwz %r7, 224(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 224(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 228(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 228(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 232(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 232(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 236(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 236(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 240(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 240(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 244(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 244(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 248(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 248(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 252(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 252(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 256(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 256(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 260(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 260(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 264(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 264(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 268(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 268(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 272(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 272(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 276(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 276(%r6)
	ld %r15, 112(%r6)
	ld %r16, 120(%r6)
	ld %r17, 128(%r6)
	ld %r18, 136(%r6)
	ld %r19, 144(%r6)
	ld %r20, 152(%r6)
	ld %r21, 160(%r6)
	ld %r22, 112(%r6)
	ld %r23, 120(%r6)
	ld %r24, 128(%r6)
	ld %r25, 136(%r6)
	ld %r26, 144(%r6)
	ld %r27, 152(%r6)
	ld %r28, 160(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 280(%r6)
	std %r8, 288(%r6)
	std %r9, 296(%r6)
	std %r10, 304(%r6)
	std %r11, 312(%r6)
	std %r29, 320(%r6)
	std %r30, 328(%r6)
	ld %r15, 280(%r6)
	ld %r16, 288(%r6)
	ld %r17, 296(%r6)
	ld %r18, 304(%r6)
	ld %r19, 312(%r6)
	ld %r20, 320(%r6)
	ld %r21, 328(%r6)
	ld %r22, 112(%r6)
	ld %r23, 120(%r6)
	ld %r24, 128(%r6)
	ld %r25, 136(%r6)
	ld %r26, 144(%r6)
	ld %r27, 152(%r6)
	ld %r28, 160(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 280(%r6)
	std %r8, 288(%r6)
	std %r9, 296(%r6)
	std %r10, 304(%r6)
	std %r11, 312(%r6)
	std %r29, 320(%r6)
	std %r30, 328(%r6)
	ld %r15, 280(%r6)
	ld %r16, 288(%r6)
	ld %r17, 296(%r6)
	ld %r18, 304(%r6)
	ld %r19, 312(%r6)
	ld %r20, 320(%r6)
	ld %r21, 328(%r6)
	ld %r22, 280(%r6)
	ld %r23, 288(%r6)
	ld %r24, 296(%r6)
	ld %r25, 304(%r6)
	ld %r26, 312(%r6)
	ld %r27, 320(%r6)
	ld %r28, 328(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 336(%r6)
	std %r8, 344(%r6)
	std %r9, 352(%r6)
	std %r10, 360(%r6)
	std %r11, 368(%r6)
	std %r29, 376(%r6)
	std %r30, 384(%r6)
	li %r12, 1
22:
	addi %r12, %r12, -1
	ld %r15, 336(%r6)
	ld %r16, 344(%r6)
	ld %r17, 352(%r6)
	ld %r18, 360(%r6)
	ld %r19, 368(%r6)
	ld %r20, 376(%r6)
	ld %r21, 384(%r6)
	ld %r22, 336(%r6)
	ld %r23, 344(%r6)
	ld %r24, 352(%r6)
	ld %r25, 360(%r6)
	ld %r26, 368(%r6)
	ld %r27, 376(%r6)
	ld %r28, 384(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 336(%r6)
	std %r8, 344(%r6)
	std %r9, 352(%r6)
	std %r10, 360(%r6)
	std %r11, 368(%r6)
	std %r29, 376(%r6)
	std %r30, 384(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 22b
	ld %r15, 336(%r6)
	ld %r16, 344(%r6)
	ld %r17, 352(%r6)
	ld %r18, 360(%r6)
	ld %r19, 368(%r6)
	ld %r20, 376(%r6)
	ld %r21, 384(%r6)
	ld %r22, 280(%r6)
	ld %r23, 288(%r6)
	ld %r24, 296(%r6)
	ld %r25, 304(%r6)
	ld %r26, 312(%r6)
	ld %r27, 320(%r6)
	ld %r28, 328(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 336(%r6)
	std %r8, 344(%r6)
	std %r9, 352(%r6)
	std %r10, 360(%r6)
	std %r11, 368(%r6)
	std %r29, 376(%r6)
	std %r30, 384(%r6)
	ld %r15, 336(%r6)
	ld %r16, 344(%r6)
	ld %r17, 352(%r6)
	ld %r18, 360(%r6)
	ld %r19, 368(%r6)
	ld %r20, 376(%r6)
	ld %r21, 384(%r6)
	ld %r22, 336(%r6)
	ld %r23, 344(%r6)
	ld %r24, 352(%r6)
	ld %r25, 360(%r6)
	ld %r26, 368(%r6)
	ld %r27, 376(%r6)
	ld %r28, 384(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 392(%r6)
	std %r8, 400(%r6)
	std %r9, 408(%r6)
	std %r10, 416(%r6)
	std %r11, 424(%r6)
	std %r29, 432(%r6)
	std %r30, 440(%r6)
	li %r12, 3
23:
	addi %r12, %r12, -1
	ld %r15, 392(%r6)
	ld %r16, 400(%r6)
	ld %r17, 408(%r6)
	ld %r18, 416(%r6)
	ld %r19, 424(%r6)
	ld %r20, 432(%r6)
	ld %r21, 440(%r6)
	ld %r22, 392(%r6)
	ld %r23, 400(%r6)
	ld %r24, 408(%r6)
	ld %r25, 416(%r6)
	ld %r26, 424(%r6)
	ld %r27, 432(%r6)
	ld %r28, 440(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 392(%r6)
	std %r8, 400(%r6)
	std %r9, 408(%r6)
	std %r10, 416(%r6)
	std %r11, 424(%r6)
	std %r29, 432(%r6)
	std %r30, 440(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 23b
	ld %r15, 392(%r6)
	ld %r16, 400(%r6)
	ld %r17, 408(%r6)
	ld %r18, 416(%r6)
	ld %r19, 424(%r6)
	ld %r20, 432(%r6)
	ld %r21, 440(%r6)
	ld %r22, 336(%r6)
	ld %r23, 344(%r6)
	ld %r24, 352(%r6)
	ld %r25, 360(%r6)
	ld %r26, 368(%r6)
	ld %r27, 376(%r6)
	ld %r28, 384(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 392(%r6)
	std %r8, 400(%r6)
	std %r9, 408(%r6)
	std %r10, 416(%r6)
	std %r11, 424(%r6)
	std %r29, 432(%r6)
	std %r30, 440(%r6)
	ld %r15, 392(%r6)
	ld %r16, 400(%r6)
	ld %r17, 408(%r6)
	ld %r18, 416(%r6)
	ld %r19, 424(%r6)
	ld %r20, 432(%r6)
	ld %r21, 440(%r6)
	ld %r22, 392(%r6)
	ld %r23, 400(%r6)
	ld %r24, 408(%r6)
	ld %r25, 416(%r6)
	ld %r26, 424(%r6)
	ld %r27, 432(%r6)
	ld %r28, 440(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 448(%r6)
	std %r8, 456(%r6)
	std %r9, 464(%r6)
	std %r10, 472(%r6)
	std %r11, 480(%r6)
	std %r29, 488(%r6)
	std %r30, 496(%r6)
	li %r12, 7
24:
	addi %r12, %r12, -1
	ld %r15, 448(%r6)
	ld %r16, 456(%r6)
	ld %r17, 464(%r6)
	ld %r18, 472(%r6)
	ld %r19, 480(%r6)
	ld %r20, 488(%r6)
	ld %r21, 496(%r6)
	ld %r22, 448(%r6)
	ld %r23, 456(%r6)
	ld %r24, 464(%r6)
	ld %r25, 472(%r6)
	ld %r26, 480(%r6)
	ld %r27, 488(%r6)
	ld %r28, 496(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 448(%r6)
	std %r8, 456(%r6)
	std %r9, 464(%r6)
	std %r10, 472(%r6)
	std %r11, 480(%r6)
	std %r29, 488(%r6)
	std %r30, 496(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 24b
	ld %r15, 448(%r6)
	ld %r16, 456(%r6)
	ld %r17, 464(%r6)
	ld %r18, 472(%r6)
	ld %r19, 480(%r6)
	ld %r20, 488(%r6)
	ld %r21, 496(%r6)
	ld %r22, 392(%r6)
	ld %r23, 400(%r6)
	ld %r24, 408(%r6)
	ld %r25, 416(%r6)
	ld %r26, 424(%r6)
	ld %r27, 432(%r6)
	ld %r28, 440(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 448(%r6)
	std %r8, 456(%r6)
	std %r9, 464(%r6)
	std %r10, 472(%r6)
	std %r11, 480(%r6)
	std %r29, 488(%r6)
	std %r30, 496(%r6)
	ld %r15, 448(%r6)
	ld %r16, 456(%r6)
	ld %r17, 464(%r6)
	ld %r18, 472(%r6)
	ld %r19, 480(%r6)
	ld %r20, 488(%r6)
	ld %r21, 496(%r6)
	ld %r22, 448(%r6)
	ld %r23, 456(%r6)
	ld %r24, 464(%r6)
	ld %r25, 472(%r6)
	ld %r26, 480(%r6)
	ld %r27, 488(%r6)
	ld %r28, 496(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 504(%r6)
	std %r8, 512(%r6)
	std %r9, 520(%r6)
	std %r10, 528(%r6)
	std %r11, 536(%r6)
	std %r29, 544(%r6)
	std %r30, 552(%r6)
	li %r12, 15
25:
	addi %r12, %r12, -1
	ld %r15, 504(%r6)
	ld %r16, 512(%r6)
	ld %r17, 520(%r6)
	ld %r18, 528(%r6)
	ld %r19, 536(%r6)
	ld %r20, 544(%r6)
	ld %r21, 552(%r6)
	ld %r22, 504(%r6)
	ld %r23, 512(%r6)
	ld %r24, 520(%r6)
	ld %r25, 528(%r6)
	ld %r26, 536(%r6)
	ld %r27, 544(%r6)
	ld %r28, 552(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 504(%r6)
	std %r8, 512(%r6)
	std %r9, 520(%r6)
	std %r10, 528(%r6)
	std %r11, 536(%r6)
	std %r29, 544(%r6)
	std %r30, 552(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 25b
	ld %r15, 504(%r6)
	ld %r16, 512(%r6)
	ld %r17, 520(%r6)
	ld %r18, 528(%r6)
	ld %r19, 536(%r6)
	ld %r20, 544(%r6)
	ld %r21, 552(%r6)
	ld %r22, 448(%r6)
	ld %r23, 456(%r6)
	ld %r24, 464(%r6)
	ld %r25, 472(%r6)
	ld %r26, 480(%r6)
	ld %r27, 488(%r6)
	ld %r28, 496(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 504(%r6)
	std %r8, 512(%r6)
	std %r9, 520(%r6)
	std %r10, 528(%r6)
	std %r11, 536(%r6)
	std %r29, 544(%r6)
	std %r30, 552(%r6)
	ld %r15, 504(%r6)
	ld %r16, 512(%r6)
	ld %r17, 520(%r6)
	ld %r18, 528(%r6)
	ld %r19, 536(%r6)
	ld %r20, 544(%r6)
	ld %r21, 552(%r6)
	ld %r22, 504(%r6)
	ld %r23, 512(%r6)
	ld %r24, 520(%r6)
	ld %r25, 528(%r6)
	ld %r26, 536(%r6)
	ld %r27, 544(%r6)
	ld %r28, 552(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 560(%r6)
	std %r8, 568(%r6)
	std %r9, 576(%r6)
	std %r10, 584(%r6)
	std %r11, 592(%r6)
	std %r29, 600(%r6)
	std %r30, 608(%r6)
	li %r12, 31
26:
	addi %r12, %r12, -1
	ld %r15, 560(%r6)
	ld %r16, 568(%r6)
	ld %r17, 576(%r6)
	ld %r18, 584(%r6)
	ld %r19, 592(%r6)
	ld %r20, 600(%r6)
	ld %r21, 608(%r6)
	ld %r22, 560(%r6)
	ld %r23, 568(%r6)
	ld %r24, 576(%r6)
	ld %r25, 584(%r6)
	ld %r26, 592(%r6)
	ld %r27, 600(%r6)
	ld %r28, 608(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 560(%r6)
	std %r8, 568(%r6)
	std %r9, 576(%r6)
	std %r10, 584(%r6)
	std %r11, 592(%r6)
	std %r29, 600(%r6)
	std %r30, 608(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 26b
	ld %r15, 560(%r6)
	ld %r16, 568(%r6)
	ld %r17, 576(%r6)
	ld %r18, 584(%r6)
	ld %r19, 592(%r6)
	ld %r20, 600(%r6)
	ld %r21, 608(%r6)
	ld %r22, 504(%r6)
	ld %r23, 512(%r6)
	ld %r24, 520(%r6)
	ld %r25, 528(%r6)
	ld %r26, 536(%r6)
	ld %r27, 544(%r6)
	ld %r28, 552(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 560(%r6)
	std %r8, 568(%r6)
	std %r9, 576(%r6)
	std %r10, 584(%r6)
	std %r11, 592(%r6)
	std %r29, 600(%r6)
	std %r30, 608(%r6)
	ld %r15, 560(%r6)
	ld %r16, 568(%r6)
	ld %r17, 576(%r6)
	ld %r18, 584(%r6)
	ld %r19, 592(%r6)
	ld %r20, 600(%r6)
	ld %r21, 608(%r6)
	ld %r22, 560(%r6)
	ld %r23, 568(%r6)
	ld %r24, 576(%r6)
	ld %r25, 584(%r6)
	ld %r26, 592(%r6)
	ld %r27, 600(%r6)
	ld %r28, 608(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	li %r12, 63
27:
	addi %r12, %r12, -1
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 616(%r6)
	ld %r23, 624(%r6)
	ld %r24, 632(%r6)
	ld %r25, 640(%r6)
	ld %r26, 648(%r6)
	ld %r27, 656(%r6)
	ld %r28, 664(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 27b
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 560(%r6)
	ld %r23, 568(%r6)
	ld %r24, 576(%r6)
	ld %r25, 584(%r6)
	ld %r26, 592(%r6)
	ld %r27, 600(%r6)
	ld %r28, 608(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 616(%r6)
	ld %r23, 624(%r6)
	ld %r24, 632(%r6)
	ld %r25, 640(%r6)
	ld %r26, 648(%r6)
	ld %r27, 656(%r6)
	ld %r28, 664(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	li %r12, 63
28:
	addi %r12, %r12, -1
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 616(%r6)
	ld %r23, 624(%r6)
	ld %r24, 632(%r6)
	ld %r25, 640(%r6)
	ld %r26, 648(%r6)
	ld %r27, 656(%r6)
	ld %r28, 664(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 28b
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 560(%r6)
	ld %r23, 568(%r6)
	ld %r24, 576(%r6)
	ld %r25, 584(%r6)
	ld %r26, 592(%r6)
	ld %r27, 600(%r6)
	ld %r28, 608(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 616(%r6)
	ld %r23, 624(%r6)
	ld %r24, 632(%r6)
	ld %r25, 640(%r6)
	ld %r26, 648(%r6)
	ld %r27, 656(%r6)
	ld %r28, 664(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	li %r12, 15
29:
	addi %r12, %r12, -1
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 616(%r6)
	ld %r23, 624(%r6)
	ld %r24, 632(%r6)
	ld %r25, 640(%r6)
	ld %r26, 648(%r6)
	ld %r27, 656(%r6)
	ld %r28, 664(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 29b
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 448(%r6)
	ld %r23, 456(%r6)
	ld %r24, 464(%r6)
	ld %r25, 472(%r6)
	ld %r26, 480(%r6)
	ld %r27, 488(%r6)
	ld %r28, 496(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 616(%r6)
	ld %r23, 624(%r6)
	ld %r24, 632(%r6)
	ld %r25, 640(%r6)
	ld %r26, 648(%r6)
	ld %r27, 656(%r6)
	ld %r28, 664(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	li %r12, 7
210:
	addi %r12, %r12, -1
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 616(%r6)
	ld %r23, 624(%r6)
	ld %r24, 632(%r6)
	ld %r25, 640(%r6)
	ld %r26, 648(%r6)
	ld %r27, 656(%r6)
	ld %r28, 664(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 210b
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 392(%r6)
	ld %r23, 400(%r6)
	ld %r24, 408(%r6)
	ld %r25, 416(%r6)
	ld %r26, 424(%r6)
	ld %r27, 432(%r6)
	ld %r28, 440(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 616(%r6)
	ld %r23, 624(%r6)
	ld %r24, 632(%r6)
	ld %r25, 640(%r6)
	ld %r26, 648(%r6)
	ld %r27, 656(%r6)
	ld %r28, 664(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	li %r12, 3
211:
	addi %r12, %r12, -1
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 616(%r6)
	ld %r23, 624(%r6)
	ld %r24, 632(%r6)
	ld %r25, 640(%r6)
	ld %r26, 648(%r6)
	ld %r27, 656(%r6)
	ld %r28, 664(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 211b
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 336(%r6)
	ld %r23, 344(%r6)
	ld %r24, 352(%r6)
	ld %r25, 360(%r6)
	ld %r26, 368(%r6)
	ld %r27, 376(%r6)
	ld %r28, 384(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 616(%r6)
	ld %r23, 624(%r6)
	ld %r24, 632(%r6)
	ld %r25, 640(%r6)
	ld %r26, 648(%r6)
	ld %r27, 656(%r6)
	ld %r28, 664(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	li %r12, 1
212:
	addi %r12, %r12, -1
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 616(%r6)
	ld %r23, 624(%r6)
	ld %r24, 632(%r6)
	ld %r25, 640(%r6)
	ld %r26, 648(%r6)
	ld %r27, 656(%r6)
	ld %r28, 664(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 212b
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 280(%r6)
	ld %r23, 288(%r6)
	ld %r24, 296(%r6)
	ld %r25, 304(%r6)
	ld %r26, 312(%r6)
	ld %r27, 320(%r6)
	ld %r28, 328(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 616(%r6)
	ld %r23, 624(%r6)
	ld %r24, 632(%r6)
	ld %r25, 640(%r6)
	ld %r26, 648(%r6)
	ld %r27, 656(%r6)
	ld %r28, 664(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 840(%r6)
	std %r8, 848(%r6)
	std %r9, 856(%r6)
	std %r10, 864(%r6)
	std %r11, 872(%r6)
	std %r29, 880(%r6)
	std %r30, 888(%r6)
	ld %r15, 840(%r6)
	ld %r16, 848(%r6)
	ld %r17, 856(%r6)
	ld %r18, 864(%r6)
	ld %r19, 872(%r6)
	ld %r20, 880(%r6)
	ld %r21, 888(%r6)
	ld %r22, 112(%r6)
	ld %r23, 120(%r6)
	ld %r24, 128(%r6)
	ld %r25, 136(%r6)
	ld %r26, 144(%r6)
	ld %r27, 152(%r6)
	ld %r28, 160(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 840(%r6)
	std %r8, 848(%r6)
	std %r9, 856(%r6)
	std %r10, 864(%r6)
	std %r11, 872(%r6)
	std %r29, 880(%r6)
	std %r30, 888(%r6)
	ld %r15, 840(%r6)
	ld %r16, 848(%r6)
	ld %r17, 856(%r6)
	ld %r18, 864(%r6)
	ld %r19, 872(%r6)
	ld %r20, 880(%r6)
	ld %r21, 888(%r6)
	ld %r22, 840(%r6)
	ld %r23, 848(%r6)
	ld %r24, 856(%r6)
	ld %r25, 864(%r6)
	ld %r26, 872(%r6)
	ld %r27, 880(%r6)
	ld %r28, 888(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 840(%r6)
	std %r8, 848(%r6)
	std %r9, 856(%r6)
	std %r10, 864(%r6)
	std %r11, 872(%r6)
	std %r29, 880(%r6)
	std %r30, 888(%r6)
	li %r12, 224
213:
	addi %r12, %r12, -1
	ld %r15, 840(%r6)
	ld %r16, 848(%r6)
	ld %r17, 856(%r6)
	ld %r18, 864(%r6)
	ld %r19, 872(%r6)
	ld %r20, 880(%r6)
	ld %r21, 888(%r6)
	ld %r22, 840(%r6)
	ld %r23, 848(%r6)
	ld %r24, 856(%r6)
	ld %r25, 864(%r6)
	ld %r26, 872(%r6)
	ld %r27, 880(%r6)
	ld %r28, 888(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 840(%r6)
	std %r8, 848(%r6)
	std %r9, 856(%r6)
	std %r10, 864(%r6)
	std %r11, 872(%r6)
	std %r29, 880(%r6)
	std %r30, 888(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 213b
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 616(%r6)
	ld %r23, 624(%r6)
	ld %r24, 632(%r6)
	ld %r25, 640(%r6)
	ld %r26, 648(%r6)
	ld %r27, 656(%r6)
	ld %r28, 664(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	li %r12, 1
214:
	addi %r12, %r12, -1
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 616(%r6)
	ld %r23, 624(%r6)
	ld %r24, 632(%r6)
	ld %r25, 640(%r6)
	ld %r26, 648(%r6)
	ld %r27, 656(%r6)
	ld %r28, 664(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 214b
	ld %r15, 616(%r6)
	ld %r16, 624(%r6)
	ld %r17, 632(%r6)
	ld %r18, 640(%r6)
	ld %r19, 648(%r6)
	ld %r20, 656(%r6)
	ld %r21, 664(%r6)
	ld %r22, 112(%r6)
	ld %r23, 120(%r6)
	ld %r24, 128(%r6)
	ld %r25, 136(%r6)
	ld %r26, 144(%r6)
	ld %r27, 152(%r6)
	ld %r28, 160(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	ld %r15, 840(%r6)
	ld %r16, 848(%r6)
	ld %r17, 856(%r6)
	ld %r18, 864(%r6)
	ld %r19, 872(%r6)
	ld %r20, 880(%r6)
	ld %r21, 888(%r6)
	ld %r22, 616(%r6)
	ld %r23, 624(%r6)
	ld %r24, 632(%r6)
	ld %r25, 640(%r6)
	ld %r26, 648(%r6)
	ld %r27, 656(%r6)
	ld %r28, 664(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 840(%r6)
	std %r8, 848(%r6)
	std %r9, 856(%r6)
	std %r10, 864(%r6)
	std %r11, 872(%r6)
	std %r29, 880(%r6)
	std %r30, 888(%r6)
	ld %r15, 56(%r6)
	ld %r16, 64(%r6)
	ld %r17, 72(%r6)
	ld %r18, 80(%r6)
	ld %r19, 88(%r6)
	ld %r20, 96(%r6)
	ld %r21, 104(%r6)
	ld %r22, 840(%r6)
	ld %r23, 848(%r6)
	ld %r24, 856(%r6)
	ld %r25, 864(%r6)
	ld %r26, 872(%r6)
	ld %r27, 880(%r6)
	ld %r28, 888(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 56(%r6)
	std %r8, 64(%r6)
	std %r9, 72(%r6)
	std %r10, 80(%r6)
	std %r11, 88(%r6)
	std %r29, 96(%r6)
	std %r30, 104(%r6)
	ld %r15, 1512(%r6)
	ld %r16, 1520(%r6)
	ld %r17, 1528(%r6)
	ld %r18, 1536(%r6)
	ld %r19, 1544(%r6)
	ld %r20, 1552(%r6)
	ld %r21, 1560(%r6)
	ld %r22, 1568(%r6)
	ld %r23, 1576(%r6)
	ld %r24, 1584(%r6)
	ld %r25, 1592(%r6)
	ld %r26, 1600(%r6)
	ld %r27, 1608(%r6)
	ld %r28, 1616(%r6)
	ld %r29, 1624(%r6)
	ld %r30, 1632(%r6)
	ld %r31, 1640(%r6)
	li %r8, 1
	li %r10, 1
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 896(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 900(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 904(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 908(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 912(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 916(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 920(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 924(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 928(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 932(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 936(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 940(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 944(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 948(%r6)
	rldicl %r8, %r7, 32, 32
	li %r4, 0
	subf %r11, %r8, %r4
	lwz %r5, 56(%r6)
	lwz %r7, 896(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 0(%r3)
	lwz %r5, 60(%r6)
	lwz %r7, 900(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 4(%r3)
	lwz %r5, 64(%r6)
	lwz %r7, 904(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 8(%r3)
	lwz %r5, 68(%r6)
	lwz %r7, 908(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 12(%r3)
	lwz %r5, 72(%r6)
	lwz %r7, 912(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 16(%r3)
	lwz %r5, 76(%r6)
	lwz %r7, 916(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 20(%r3)
	lwz %r5, 80(%r6)
	lwz %r7, 920(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 24(%r3)
	lwz %r5, 84(%r6)
	lwz %r7, 924(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 28(%r3)
	lwz %r5, 88(%r6)
	lwz %r7, 928(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 32(%r3)
	lwz %r5, 92(%r6)
	lwz %r7, 932(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 36(%r3)
	lwz %r5, 96(%r6)
	lwz %r7, 936(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 40(%r3)
	lwz %r5, 100(%r6)
	lwz %r7, 940(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 44(%r3)
	lwz %r5, 104(%r6)
	lwz %r7, 944(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 48(%r3)
	lwz %r5, 108(%r6)
	lwz %r7, 948(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 52(%r3)
	blr
