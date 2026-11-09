// The functions of `src/internal/vg_x448.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x448:
	lwz %r7, 0(%r5)
	stw %r7, 0(%r6)
	stw %r7, 168(%r6)
	lwz %r7, 4(%r5)
	stw %r7, 4(%r6)
	stw %r7, 172(%r6)
	lwz %r7, 8(%r5)
	stw %r7, 8(%r6)
	stw %r7, 176(%r6)
	lwz %r7, 12(%r5)
	stw %r7, 12(%r6)
	stw %r7, 180(%r6)
	lwz %r7, 16(%r5)
	stw %r7, 16(%r6)
	stw %r7, 184(%r6)
	lwz %r7, 20(%r5)
	stw %r7, 20(%r6)
	stw %r7, 188(%r6)
	lwz %r7, 24(%r5)
	stw %r7, 24(%r6)
	stw %r7, 192(%r6)
	lwz %r7, 28(%r5)
	stw %r7, 28(%r6)
	stw %r7, 196(%r6)
	lwz %r7, 32(%r5)
	stw %r7, 32(%r6)
	stw %r7, 200(%r6)
	lwz %r7, 36(%r5)
	stw %r7, 36(%r6)
	stw %r7, 204(%r6)
	lwz %r7, 40(%r5)
	stw %r7, 40(%r6)
	stw %r7, 208(%r6)
	lwz %r7, 44(%r5)
	stw %r7, 44(%r6)
	stw %r7, 212(%r6)
	lwz %r7, 48(%r5)
	stw %r7, 48(%r6)
	stw %r7, 216(%r6)
	lwz %r7, 52(%r5)
	stw %r7, 52(%r6)
	stw %r7, 220(%r6)
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
	std %r14, 1512(%r6)
	std %r15, 1520(%r6)
	std %r16, 1528(%r6)
	std %r17, 1536(%r6)
	std %r18, 1544(%r6)
	std %r19, 1552(%r6)
	std %r20, 1560(%r6)
	std %r21, 1568(%r6)
	std %r22, 1576(%r6)
	std %r23, 1584(%r6)
	std %r24, 1592(%r6)
	std %r25, 1600(%r6)
	std %r26, 1608(%r6)
	std %r27, 1616(%r6)
	std %r28, 1624(%r6)
	std %r29, 1632(%r6)
	std %r30, 1640(%r6)
	std %r31, 1648(%r6)
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
	ld %r14, 280(%r6)
	ld %r15, 288(%r6)
	ld %r16, 296(%r6)
	ld %r17, 304(%r6)
	ld %r18, 312(%r6)
	ld %r19, 320(%r6)
	ld %r20, 328(%r6)
	ld %r21, 280(%r6)
	ld %r22, 288(%r6)
	ld %r23, 296(%r6)
	ld %r24, 304(%r6)
	ld %r25, 312(%r6)
	ld %r26, 320(%r6)
	ld %r27, 328(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 504(%r6)
	std %r8, 512(%r6)
	std %r9, 520(%r6)
	std %r10, 528(%r6)
	std %r11, 536(%r6)
	std %r28, 544(%r6)
	std %r29, 552(%r6)
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
	ld %r14, 336(%r6)
	ld %r15, 344(%r6)
	ld %r16, 352(%r6)
	ld %r17, 360(%r6)
	ld %r18, 368(%r6)
	ld %r19, 376(%r6)
	ld %r20, 384(%r6)
	ld %r21, 336(%r6)
	ld %r22, 344(%r6)
	ld %r23, 352(%r6)
	ld %r24, 360(%r6)
	ld %r25, 368(%r6)
	ld %r26, 376(%r6)
	ld %r27, 384(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 560(%r6)
	std %r8, 568(%r6)
	std %r9, 576(%r6)
	std %r10, 584(%r6)
	std %r11, 592(%r6)
	std %r28, 600(%r6)
	std %r29, 608(%r6)
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
	ld %r14, 448(%r6)
	ld %r15, 456(%r6)
	ld %r16, 464(%r6)
	ld %r17, 472(%r6)
	ld %r18, 480(%r6)
	ld %r19, 488(%r6)
	ld %r20, 496(%r6)
	ld %r21, 280(%r6)
	ld %r22, 288(%r6)
	ld %r23, 296(%r6)
	ld %r24, 304(%r6)
	ld %r25, 312(%r6)
	ld %r26, 320(%r6)
	ld %r27, 328(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 672(%r6)
	std %r8, 680(%r6)
	std %r9, 688(%r6)
	std %r10, 696(%r6)
	std %r11, 704(%r6)
	std %r28, 712(%r6)
	std %r29, 720(%r6)
	ld %r14, 392(%r6)
	ld %r15, 400(%r6)
	ld %r16, 408(%r6)
	ld %r17, 416(%r6)
	ld %r18, 424(%r6)
	ld %r19, 432(%r6)
	ld %r20, 440(%r6)
	ld %r21, 336(%r6)
	ld %r22, 344(%r6)
	ld %r23, 352(%r6)
	ld %r24, 360(%r6)
	ld %r25, 368(%r6)
	ld %r26, 376(%r6)
	ld %r27, 384(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 728(%r6)
	std %r8, 736(%r6)
	std %r9, 744(%r6)
	std %r10, 752(%r6)
	std %r11, 760(%r6)
	std %r28, 768(%r6)
	std %r29, 776(%r6)
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
	ld %r14, 168(%r6)
	ld %r15, 176(%r6)
	ld %r16, 184(%r6)
	ld %r17, 192(%r6)
	ld %r18, 200(%r6)
	ld %r19, 208(%r6)
	ld %r20, 216(%r6)
	ld %r21, 168(%r6)
	ld %r22, 176(%r6)
	ld %r23, 184(%r6)
	ld %r24, 192(%r6)
	ld %r25, 200(%r6)
	ld %r26, 208(%r6)
	ld %r27, 216(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 168(%r6)
	std %r8, 176(%r6)
	std %r9, 184(%r6)
	std %r10, 192(%r6)
	std %r11, 200(%r6)
	std %r28, 208(%r6)
	std %r29, 216(%r6)
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
	ld %r14, 224(%r6)
	ld %r15, 232(%r6)
	ld %r16, 240(%r6)
	ld %r17, 248(%r6)
	ld %r18, 256(%r6)
	ld %r19, 264(%r6)
	ld %r20, 272(%r6)
	ld %r21, 224(%r6)
	ld %r22, 232(%r6)
	ld %r23, 240(%r6)
	ld %r24, 248(%r6)
	ld %r25, 256(%r6)
	ld %r26, 264(%r6)
	ld %r27, 272(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 224(%r6)
	std %r8, 232(%r6)
	std %r9, 240(%r6)
	std %r10, 248(%r6)
	std %r11, 256(%r6)
	std %r28, 264(%r6)
	std %r29, 272(%r6)
	ld %r14, 0(%r6)
	ld %r15, 8(%r6)
	ld %r16, 16(%r6)
	ld %r17, 24(%r6)
	ld %r18, 32(%r6)
	ld %r19, 40(%r6)
	ld %r20, 48(%r6)
	ld %r21, 224(%r6)
	ld %r22, 232(%r6)
	ld %r23, 240(%r6)
	ld %r24, 248(%r6)
	ld %r25, 256(%r6)
	ld %r26, 264(%r6)
	ld %r27, 272(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 224(%r6)
	std %r8, 232(%r6)
	std %r9, 240(%r6)
	std %r10, 248(%r6)
	std %r11, 256(%r6)
	std %r28, 264(%r6)
	std %r29, 272(%r6)
	ld %r14, 504(%r6)
	ld %r15, 512(%r6)
	ld %r16, 520(%r6)
	ld %r17, 528(%r6)
	ld %r18, 536(%r6)
	ld %r19, 544(%r6)
	ld %r20, 552(%r6)
	ld %r21, 560(%r6)
	ld %r22, 568(%r6)
	ld %r23, 576(%r6)
	ld %r24, 584(%r6)
	ld %r25, 592(%r6)
	ld %r26, 600(%r6)
	ld %r27, 608(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 56(%r6)
	std %r8, 64(%r6)
	std %r9, 72(%r6)
	std %r10, 80(%r6)
	std %r11, 88(%r6)
	std %r28, 96(%r6)
	std %r29, 104(%r6)
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
	ld %r14, 616(%r6)
	ld %r15, 624(%r6)
	ld %r16, 632(%r6)
	ld %r17, 640(%r6)
	ld %r18, 648(%r6)
	ld %r19, 656(%r6)
	ld %r20, 664(%r6)
	ld %r21, 112(%r6)
	ld %r22, 120(%r6)
	ld %r23, 128(%r6)
	ld %r24, 136(%r6)
	ld %r25, 144(%r6)
	ld %r26, 152(%r6)
	ld %r27, 160(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 112(%r6)
	std %r8, 120(%r6)
	std %r9, 128(%r6)
	std %r10, 136(%r6)
	std %r11, 144(%r6)
	std %r28, 152(%r6)
	std %r29, 160(%r6)
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
	ld %r14, 112(%r6)
	ld %r15, 120(%r6)
	ld %r16, 128(%r6)
	ld %r17, 136(%r6)
	ld %r18, 144(%r6)
	ld %r19, 152(%r6)
	ld %r20, 160(%r6)
	ld %r21, 112(%r6)
	ld %r22, 120(%r6)
	ld %r23, 128(%r6)
	ld %r24, 136(%r6)
	ld %r25, 144(%r6)
	ld %r26, 152(%r6)
	ld %r27, 160(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 280(%r6)
	std %r8, 288(%r6)
	std %r9, 296(%r6)
	std %r10, 304(%r6)
	std %r11, 312(%r6)
	std %r28, 320(%r6)
	std %r29, 328(%r6)
	ld %r14, 280(%r6)
	ld %r15, 288(%r6)
	ld %r16, 296(%r6)
	ld %r17, 304(%r6)
	ld %r18, 312(%r6)
	ld %r19, 320(%r6)
	ld %r20, 328(%r6)
	ld %r21, 112(%r6)
	ld %r22, 120(%r6)
	ld %r23, 128(%r6)
	ld %r24, 136(%r6)
	ld %r25, 144(%r6)
	ld %r26, 152(%r6)
	ld %r27, 160(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 280(%r6)
	std %r8, 288(%r6)
	std %r9, 296(%r6)
	std %r10, 304(%r6)
	std %r11, 312(%r6)
	std %r28, 320(%r6)
	std %r29, 328(%r6)
	ld %r14, 280(%r6)
	ld %r15, 288(%r6)
	ld %r16, 296(%r6)
	ld %r17, 304(%r6)
	ld %r18, 312(%r6)
	ld %r19, 320(%r6)
	ld %r20, 328(%r6)
	ld %r21, 280(%r6)
	ld %r22, 288(%r6)
	ld %r23, 296(%r6)
	ld %r24, 304(%r6)
	ld %r25, 312(%r6)
	ld %r26, 320(%r6)
	ld %r27, 328(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 336(%r6)
	std %r8, 344(%r6)
	std %r9, 352(%r6)
	std %r10, 360(%r6)
	std %r11, 368(%r6)
	std %r28, 376(%r6)
	std %r29, 384(%r6)
	li %r12, 1
22:
	addi %r12, %r12, -1
	ld %r14, 336(%r6)
	ld %r15, 344(%r6)
	ld %r16, 352(%r6)
	ld %r17, 360(%r6)
	ld %r18, 368(%r6)
	ld %r19, 376(%r6)
	ld %r20, 384(%r6)
	ld %r21, 336(%r6)
	ld %r22, 344(%r6)
	ld %r23, 352(%r6)
	ld %r24, 360(%r6)
	ld %r25, 368(%r6)
	ld %r26, 376(%r6)
	ld %r27, 384(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 336(%r6)
	std %r8, 344(%r6)
	std %r9, 352(%r6)
	std %r10, 360(%r6)
	std %r11, 368(%r6)
	std %r28, 376(%r6)
	std %r29, 384(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 22b
	ld %r14, 336(%r6)
	ld %r15, 344(%r6)
	ld %r16, 352(%r6)
	ld %r17, 360(%r6)
	ld %r18, 368(%r6)
	ld %r19, 376(%r6)
	ld %r20, 384(%r6)
	ld %r21, 280(%r6)
	ld %r22, 288(%r6)
	ld %r23, 296(%r6)
	ld %r24, 304(%r6)
	ld %r25, 312(%r6)
	ld %r26, 320(%r6)
	ld %r27, 328(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 336(%r6)
	std %r8, 344(%r6)
	std %r9, 352(%r6)
	std %r10, 360(%r6)
	std %r11, 368(%r6)
	std %r28, 376(%r6)
	std %r29, 384(%r6)
	ld %r14, 336(%r6)
	ld %r15, 344(%r6)
	ld %r16, 352(%r6)
	ld %r17, 360(%r6)
	ld %r18, 368(%r6)
	ld %r19, 376(%r6)
	ld %r20, 384(%r6)
	ld %r21, 336(%r6)
	ld %r22, 344(%r6)
	ld %r23, 352(%r6)
	ld %r24, 360(%r6)
	ld %r25, 368(%r6)
	ld %r26, 376(%r6)
	ld %r27, 384(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 392(%r6)
	std %r8, 400(%r6)
	std %r9, 408(%r6)
	std %r10, 416(%r6)
	std %r11, 424(%r6)
	std %r28, 432(%r6)
	std %r29, 440(%r6)
	li %r12, 3
23:
	addi %r12, %r12, -1
	ld %r14, 392(%r6)
	ld %r15, 400(%r6)
	ld %r16, 408(%r6)
	ld %r17, 416(%r6)
	ld %r18, 424(%r6)
	ld %r19, 432(%r6)
	ld %r20, 440(%r6)
	ld %r21, 392(%r6)
	ld %r22, 400(%r6)
	ld %r23, 408(%r6)
	ld %r24, 416(%r6)
	ld %r25, 424(%r6)
	ld %r26, 432(%r6)
	ld %r27, 440(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 392(%r6)
	std %r8, 400(%r6)
	std %r9, 408(%r6)
	std %r10, 416(%r6)
	std %r11, 424(%r6)
	std %r28, 432(%r6)
	std %r29, 440(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 23b
	ld %r14, 392(%r6)
	ld %r15, 400(%r6)
	ld %r16, 408(%r6)
	ld %r17, 416(%r6)
	ld %r18, 424(%r6)
	ld %r19, 432(%r6)
	ld %r20, 440(%r6)
	ld %r21, 336(%r6)
	ld %r22, 344(%r6)
	ld %r23, 352(%r6)
	ld %r24, 360(%r6)
	ld %r25, 368(%r6)
	ld %r26, 376(%r6)
	ld %r27, 384(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 392(%r6)
	std %r8, 400(%r6)
	std %r9, 408(%r6)
	std %r10, 416(%r6)
	std %r11, 424(%r6)
	std %r28, 432(%r6)
	std %r29, 440(%r6)
	ld %r14, 392(%r6)
	ld %r15, 400(%r6)
	ld %r16, 408(%r6)
	ld %r17, 416(%r6)
	ld %r18, 424(%r6)
	ld %r19, 432(%r6)
	ld %r20, 440(%r6)
	ld %r21, 392(%r6)
	ld %r22, 400(%r6)
	ld %r23, 408(%r6)
	ld %r24, 416(%r6)
	ld %r25, 424(%r6)
	ld %r26, 432(%r6)
	ld %r27, 440(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 448(%r6)
	std %r8, 456(%r6)
	std %r9, 464(%r6)
	std %r10, 472(%r6)
	std %r11, 480(%r6)
	std %r28, 488(%r6)
	std %r29, 496(%r6)
	li %r12, 7
24:
	addi %r12, %r12, -1
	ld %r14, 448(%r6)
	ld %r15, 456(%r6)
	ld %r16, 464(%r6)
	ld %r17, 472(%r6)
	ld %r18, 480(%r6)
	ld %r19, 488(%r6)
	ld %r20, 496(%r6)
	ld %r21, 448(%r6)
	ld %r22, 456(%r6)
	ld %r23, 464(%r6)
	ld %r24, 472(%r6)
	ld %r25, 480(%r6)
	ld %r26, 488(%r6)
	ld %r27, 496(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 448(%r6)
	std %r8, 456(%r6)
	std %r9, 464(%r6)
	std %r10, 472(%r6)
	std %r11, 480(%r6)
	std %r28, 488(%r6)
	std %r29, 496(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 24b
	ld %r14, 448(%r6)
	ld %r15, 456(%r6)
	ld %r16, 464(%r6)
	ld %r17, 472(%r6)
	ld %r18, 480(%r6)
	ld %r19, 488(%r6)
	ld %r20, 496(%r6)
	ld %r21, 392(%r6)
	ld %r22, 400(%r6)
	ld %r23, 408(%r6)
	ld %r24, 416(%r6)
	ld %r25, 424(%r6)
	ld %r26, 432(%r6)
	ld %r27, 440(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 448(%r6)
	std %r8, 456(%r6)
	std %r9, 464(%r6)
	std %r10, 472(%r6)
	std %r11, 480(%r6)
	std %r28, 488(%r6)
	std %r29, 496(%r6)
	ld %r14, 448(%r6)
	ld %r15, 456(%r6)
	ld %r16, 464(%r6)
	ld %r17, 472(%r6)
	ld %r18, 480(%r6)
	ld %r19, 488(%r6)
	ld %r20, 496(%r6)
	ld %r21, 448(%r6)
	ld %r22, 456(%r6)
	ld %r23, 464(%r6)
	ld %r24, 472(%r6)
	ld %r25, 480(%r6)
	ld %r26, 488(%r6)
	ld %r27, 496(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 504(%r6)
	std %r8, 512(%r6)
	std %r9, 520(%r6)
	std %r10, 528(%r6)
	std %r11, 536(%r6)
	std %r28, 544(%r6)
	std %r29, 552(%r6)
	li %r12, 15
25:
	addi %r12, %r12, -1
	ld %r14, 504(%r6)
	ld %r15, 512(%r6)
	ld %r16, 520(%r6)
	ld %r17, 528(%r6)
	ld %r18, 536(%r6)
	ld %r19, 544(%r6)
	ld %r20, 552(%r6)
	ld %r21, 504(%r6)
	ld %r22, 512(%r6)
	ld %r23, 520(%r6)
	ld %r24, 528(%r6)
	ld %r25, 536(%r6)
	ld %r26, 544(%r6)
	ld %r27, 552(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 504(%r6)
	std %r8, 512(%r6)
	std %r9, 520(%r6)
	std %r10, 528(%r6)
	std %r11, 536(%r6)
	std %r28, 544(%r6)
	std %r29, 552(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 25b
	ld %r14, 504(%r6)
	ld %r15, 512(%r6)
	ld %r16, 520(%r6)
	ld %r17, 528(%r6)
	ld %r18, 536(%r6)
	ld %r19, 544(%r6)
	ld %r20, 552(%r6)
	ld %r21, 448(%r6)
	ld %r22, 456(%r6)
	ld %r23, 464(%r6)
	ld %r24, 472(%r6)
	ld %r25, 480(%r6)
	ld %r26, 488(%r6)
	ld %r27, 496(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 504(%r6)
	std %r8, 512(%r6)
	std %r9, 520(%r6)
	std %r10, 528(%r6)
	std %r11, 536(%r6)
	std %r28, 544(%r6)
	std %r29, 552(%r6)
	ld %r14, 504(%r6)
	ld %r15, 512(%r6)
	ld %r16, 520(%r6)
	ld %r17, 528(%r6)
	ld %r18, 536(%r6)
	ld %r19, 544(%r6)
	ld %r20, 552(%r6)
	ld %r21, 504(%r6)
	ld %r22, 512(%r6)
	ld %r23, 520(%r6)
	ld %r24, 528(%r6)
	ld %r25, 536(%r6)
	ld %r26, 544(%r6)
	ld %r27, 552(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 560(%r6)
	std %r8, 568(%r6)
	std %r9, 576(%r6)
	std %r10, 584(%r6)
	std %r11, 592(%r6)
	std %r28, 600(%r6)
	std %r29, 608(%r6)
	li %r12, 31
26:
	addi %r12, %r12, -1
	ld %r14, 560(%r6)
	ld %r15, 568(%r6)
	ld %r16, 576(%r6)
	ld %r17, 584(%r6)
	ld %r18, 592(%r6)
	ld %r19, 600(%r6)
	ld %r20, 608(%r6)
	ld %r21, 560(%r6)
	ld %r22, 568(%r6)
	ld %r23, 576(%r6)
	ld %r24, 584(%r6)
	ld %r25, 592(%r6)
	ld %r26, 600(%r6)
	ld %r27, 608(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 560(%r6)
	std %r8, 568(%r6)
	std %r9, 576(%r6)
	std %r10, 584(%r6)
	std %r11, 592(%r6)
	std %r28, 600(%r6)
	std %r29, 608(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 26b
	ld %r14, 560(%r6)
	ld %r15, 568(%r6)
	ld %r16, 576(%r6)
	ld %r17, 584(%r6)
	ld %r18, 592(%r6)
	ld %r19, 600(%r6)
	ld %r20, 608(%r6)
	ld %r21, 504(%r6)
	ld %r22, 512(%r6)
	ld %r23, 520(%r6)
	ld %r24, 528(%r6)
	ld %r25, 536(%r6)
	ld %r26, 544(%r6)
	ld %r27, 552(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 560(%r6)
	std %r8, 568(%r6)
	std %r9, 576(%r6)
	std %r10, 584(%r6)
	std %r11, 592(%r6)
	std %r28, 600(%r6)
	std %r29, 608(%r6)
	ld %r14, 560(%r6)
	ld %r15, 568(%r6)
	ld %r16, 576(%r6)
	ld %r17, 584(%r6)
	ld %r18, 592(%r6)
	ld %r19, 600(%r6)
	ld %r20, 608(%r6)
	ld %r21, 560(%r6)
	ld %r22, 568(%r6)
	ld %r23, 576(%r6)
	ld %r24, 584(%r6)
	ld %r25, 592(%r6)
	ld %r26, 600(%r6)
	ld %r27, 608(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r28, 656(%r6)
	std %r29, 664(%r6)
	li %r12, 63
27:
	addi %r12, %r12, -1
	ld %r14, 616(%r6)
	ld %r15, 624(%r6)
	ld %r16, 632(%r6)
	ld %r17, 640(%r6)
	ld %r18, 648(%r6)
	ld %r19, 656(%r6)
	ld %r20, 664(%r6)
	ld %r21, 616(%r6)
	ld %r22, 624(%r6)
	ld %r23, 632(%r6)
	ld %r24, 640(%r6)
	ld %r25, 648(%r6)
	ld %r26, 656(%r6)
	ld %r27, 664(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r28, 656(%r6)
	std %r29, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 27b
	ld %r14, 616(%r6)
	ld %r15, 624(%r6)
	ld %r16, 632(%r6)
	ld %r17, 640(%r6)
	ld %r18, 648(%r6)
	ld %r19, 656(%r6)
	ld %r20, 664(%r6)
	ld %r21, 560(%r6)
	ld %r22, 568(%r6)
	ld %r23, 576(%r6)
	ld %r24, 584(%r6)
	ld %r25, 592(%r6)
	ld %r26, 600(%r6)
	ld %r27, 608(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r28, 656(%r6)
	std %r29, 664(%r6)
	ld %r14, 616(%r6)
	ld %r15, 624(%r6)
	ld %r16, 632(%r6)
	ld %r17, 640(%r6)
	ld %r18, 648(%r6)
	ld %r19, 656(%r6)
	ld %r20, 664(%r6)
	ld %r21, 616(%r6)
	ld %r22, 624(%r6)
	ld %r23, 632(%r6)
	ld %r24, 640(%r6)
	ld %r25, 648(%r6)
	ld %r26, 656(%r6)
	ld %r27, 664(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r28, 656(%r6)
	std %r29, 664(%r6)
	li %r12, 63
28:
	addi %r12, %r12, -1
	ld %r14, 616(%r6)
	ld %r15, 624(%r6)
	ld %r16, 632(%r6)
	ld %r17, 640(%r6)
	ld %r18, 648(%r6)
	ld %r19, 656(%r6)
	ld %r20, 664(%r6)
	ld %r21, 616(%r6)
	ld %r22, 624(%r6)
	ld %r23, 632(%r6)
	ld %r24, 640(%r6)
	ld %r25, 648(%r6)
	ld %r26, 656(%r6)
	ld %r27, 664(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r28, 656(%r6)
	std %r29, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 28b
	ld %r14, 616(%r6)
	ld %r15, 624(%r6)
	ld %r16, 632(%r6)
	ld %r17, 640(%r6)
	ld %r18, 648(%r6)
	ld %r19, 656(%r6)
	ld %r20, 664(%r6)
	ld %r21, 560(%r6)
	ld %r22, 568(%r6)
	ld %r23, 576(%r6)
	ld %r24, 584(%r6)
	ld %r25, 592(%r6)
	ld %r26, 600(%r6)
	ld %r27, 608(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r28, 656(%r6)
	std %r29, 664(%r6)
	ld %r14, 616(%r6)
	ld %r15, 624(%r6)
	ld %r16, 632(%r6)
	ld %r17, 640(%r6)
	ld %r18, 648(%r6)
	ld %r19, 656(%r6)
	ld %r20, 664(%r6)
	ld %r21, 616(%r6)
	ld %r22, 624(%r6)
	ld %r23, 632(%r6)
	ld %r24, 640(%r6)
	ld %r25, 648(%r6)
	ld %r26, 656(%r6)
	ld %r27, 664(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r28, 656(%r6)
	std %r29, 664(%r6)
	li %r12, 15
29:
	addi %r12, %r12, -1
	ld %r14, 616(%r6)
	ld %r15, 624(%r6)
	ld %r16, 632(%r6)
	ld %r17, 640(%r6)
	ld %r18, 648(%r6)
	ld %r19, 656(%r6)
	ld %r20, 664(%r6)
	ld %r21, 616(%r6)
	ld %r22, 624(%r6)
	ld %r23, 632(%r6)
	ld %r24, 640(%r6)
	ld %r25, 648(%r6)
	ld %r26, 656(%r6)
	ld %r27, 664(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r28, 656(%r6)
	std %r29, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 29b
	ld %r14, 616(%r6)
	ld %r15, 624(%r6)
	ld %r16, 632(%r6)
	ld %r17, 640(%r6)
	ld %r18, 648(%r6)
	ld %r19, 656(%r6)
	ld %r20, 664(%r6)
	ld %r21, 448(%r6)
	ld %r22, 456(%r6)
	ld %r23, 464(%r6)
	ld %r24, 472(%r6)
	ld %r25, 480(%r6)
	ld %r26, 488(%r6)
	ld %r27, 496(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r28, 656(%r6)
	std %r29, 664(%r6)
	ld %r14, 616(%r6)
	ld %r15, 624(%r6)
	ld %r16, 632(%r6)
	ld %r17, 640(%r6)
	ld %r18, 648(%r6)
	ld %r19, 656(%r6)
	ld %r20, 664(%r6)
	ld %r21, 616(%r6)
	ld %r22, 624(%r6)
	ld %r23, 632(%r6)
	ld %r24, 640(%r6)
	ld %r25, 648(%r6)
	ld %r26, 656(%r6)
	ld %r27, 664(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r28, 656(%r6)
	std %r29, 664(%r6)
	li %r12, 7
210:
	addi %r12, %r12, -1
	ld %r14, 616(%r6)
	ld %r15, 624(%r6)
	ld %r16, 632(%r6)
	ld %r17, 640(%r6)
	ld %r18, 648(%r6)
	ld %r19, 656(%r6)
	ld %r20, 664(%r6)
	ld %r21, 616(%r6)
	ld %r22, 624(%r6)
	ld %r23, 632(%r6)
	ld %r24, 640(%r6)
	ld %r25, 648(%r6)
	ld %r26, 656(%r6)
	ld %r27, 664(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r28, 656(%r6)
	std %r29, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 210b
	ld %r14, 616(%r6)
	ld %r15, 624(%r6)
	ld %r16, 632(%r6)
	ld %r17, 640(%r6)
	ld %r18, 648(%r6)
	ld %r19, 656(%r6)
	ld %r20, 664(%r6)
	ld %r21, 392(%r6)
	ld %r22, 400(%r6)
	ld %r23, 408(%r6)
	ld %r24, 416(%r6)
	ld %r25, 424(%r6)
	ld %r26, 432(%r6)
	ld %r27, 440(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r28, 656(%r6)
	std %r29, 664(%r6)
	ld %r14, 616(%r6)
	ld %r15, 624(%r6)
	ld %r16, 632(%r6)
	ld %r17, 640(%r6)
	ld %r18, 648(%r6)
	ld %r19, 656(%r6)
	ld %r20, 664(%r6)
	ld %r21, 616(%r6)
	ld %r22, 624(%r6)
	ld %r23, 632(%r6)
	ld %r24, 640(%r6)
	ld %r25, 648(%r6)
	ld %r26, 656(%r6)
	ld %r27, 664(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r28, 656(%r6)
	std %r29, 664(%r6)
	li %r12, 3
211:
	addi %r12, %r12, -1
	ld %r14, 616(%r6)
	ld %r15, 624(%r6)
	ld %r16, 632(%r6)
	ld %r17, 640(%r6)
	ld %r18, 648(%r6)
	ld %r19, 656(%r6)
	ld %r20, 664(%r6)
	ld %r21, 616(%r6)
	ld %r22, 624(%r6)
	ld %r23, 632(%r6)
	ld %r24, 640(%r6)
	ld %r25, 648(%r6)
	ld %r26, 656(%r6)
	ld %r27, 664(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r28, 656(%r6)
	std %r29, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 211b
	ld %r14, 616(%r6)
	ld %r15, 624(%r6)
	ld %r16, 632(%r6)
	ld %r17, 640(%r6)
	ld %r18, 648(%r6)
	ld %r19, 656(%r6)
	ld %r20, 664(%r6)
	ld %r21, 336(%r6)
	ld %r22, 344(%r6)
	ld %r23, 352(%r6)
	ld %r24, 360(%r6)
	ld %r25, 368(%r6)
	ld %r26, 376(%r6)
	ld %r27, 384(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r28, 656(%r6)
	std %r29, 664(%r6)
	ld %r14, 616(%r6)
	ld %r15, 624(%r6)
	ld %r16, 632(%r6)
	ld %r17, 640(%r6)
	ld %r18, 648(%r6)
	ld %r19, 656(%r6)
	ld %r20, 664(%r6)
	ld %r21, 616(%r6)
	ld %r22, 624(%r6)
	ld %r23, 632(%r6)
	ld %r24, 640(%r6)
	ld %r25, 648(%r6)
	ld %r26, 656(%r6)
	ld %r27, 664(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r28, 656(%r6)
	std %r29, 664(%r6)
	li %r12, 1
212:
	addi %r12, %r12, -1
	ld %r14, 616(%r6)
	ld %r15, 624(%r6)
	ld %r16, 632(%r6)
	ld %r17, 640(%r6)
	ld %r18, 648(%r6)
	ld %r19, 656(%r6)
	ld %r20, 664(%r6)
	ld %r21, 616(%r6)
	ld %r22, 624(%r6)
	ld %r23, 632(%r6)
	ld %r24, 640(%r6)
	ld %r25, 648(%r6)
	ld %r26, 656(%r6)
	ld %r27, 664(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r28, 656(%r6)
	std %r29, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 212b
	ld %r14, 616(%r6)
	ld %r15, 624(%r6)
	ld %r16, 632(%r6)
	ld %r17, 640(%r6)
	ld %r18, 648(%r6)
	ld %r19, 656(%r6)
	ld %r20, 664(%r6)
	ld %r21, 280(%r6)
	ld %r22, 288(%r6)
	ld %r23, 296(%r6)
	ld %r24, 304(%r6)
	ld %r25, 312(%r6)
	ld %r26, 320(%r6)
	ld %r27, 328(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r28, 656(%r6)
	std %r29, 664(%r6)
	ld %r14, 616(%r6)
	ld %r15, 624(%r6)
	ld %r16, 632(%r6)
	ld %r17, 640(%r6)
	ld %r18, 648(%r6)
	ld %r19, 656(%r6)
	ld %r20, 664(%r6)
	ld %r21, 616(%r6)
	ld %r22, 624(%r6)
	ld %r23, 632(%r6)
	ld %r24, 640(%r6)
	ld %r25, 648(%r6)
	ld %r26, 656(%r6)
	ld %r27, 664(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 840(%r6)
	std %r8, 848(%r6)
	std %r9, 856(%r6)
	std %r10, 864(%r6)
	std %r11, 872(%r6)
	std %r28, 880(%r6)
	std %r29, 888(%r6)
	ld %r14, 840(%r6)
	ld %r15, 848(%r6)
	ld %r16, 856(%r6)
	ld %r17, 864(%r6)
	ld %r18, 872(%r6)
	ld %r19, 880(%r6)
	ld %r20, 888(%r6)
	ld %r21, 112(%r6)
	ld %r22, 120(%r6)
	ld %r23, 128(%r6)
	ld %r24, 136(%r6)
	ld %r25, 144(%r6)
	ld %r26, 152(%r6)
	ld %r27, 160(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 840(%r6)
	std %r8, 848(%r6)
	std %r9, 856(%r6)
	std %r10, 864(%r6)
	std %r11, 872(%r6)
	std %r28, 880(%r6)
	std %r29, 888(%r6)
	ld %r14, 840(%r6)
	ld %r15, 848(%r6)
	ld %r16, 856(%r6)
	ld %r17, 864(%r6)
	ld %r18, 872(%r6)
	ld %r19, 880(%r6)
	ld %r20, 888(%r6)
	ld %r21, 840(%r6)
	ld %r22, 848(%r6)
	ld %r23, 856(%r6)
	ld %r24, 864(%r6)
	ld %r25, 872(%r6)
	ld %r26, 880(%r6)
	ld %r27, 888(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 840(%r6)
	std %r8, 848(%r6)
	std %r9, 856(%r6)
	std %r10, 864(%r6)
	std %r11, 872(%r6)
	std %r28, 880(%r6)
	std %r29, 888(%r6)
	li %r12, 224
213:
	addi %r12, %r12, -1
	ld %r14, 840(%r6)
	ld %r15, 848(%r6)
	ld %r16, 856(%r6)
	ld %r17, 864(%r6)
	ld %r18, 872(%r6)
	ld %r19, 880(%r6)
	ld %r20, 888(%r6)
	ld %r21, 840(%r6)
	ld %r22, 848(%r6)
	ld %r23, 856(%r6)
	ld %r24, 864(%r6)
	ld %r25, 872(%r6)
	ld %r26, 880(%r6)
	ld %r27, 888(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 840(%r6)
	std %r8, 848(%r6)
	std %r9, 856(%r6)
	std %r10, 864(%r6)
	std %r11, 872(%r6)
	std %r28, 880(%r6)
	std %r29, 888(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 213b
	ld %r14, 616(%r6)
	ld %r15, 624(%r6)
	ld %r16, 632(%r6)
	ld %r17, 640(%r6)
	ld %r18, 648(%r6)
	ld %r19, 656(%r6)
	ld %r20, 664(%r6)
	ld %r21, 616(%r6)
	ld %r22, 624(%r6)
	ld %r23, 632(%r6)
	ld %r24, 640(%r6)
	ld %r25, 648(%r6)
	ld %r26, 656(%r6)
	ld %r27, 664(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r28, 656(%r6)
	std %r29, 664(%r6)
	li %r12, 1
214:
	addi %r12, %r12, -1
	ld %r14, 616(%r6)
	ld %r15, 624(%r6)
	ld %r16, 632(%r6)
	ld %r17, 640(%r6)
	ld %r18, 648(%r6)
	ld %r19, 656(%r6)
	ld %r20, 664(%r6)
	ld %r21, 616(%r6)
	ld %r22, 624(%r6)
	ld %r23, 632(%r6)
	ld %r24, 640(%r6)
	ld %r25, 648(%r6)
	ld %r26, 656(%r6)
	ld %r27, 664(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r28, 656(%r6)
	std %r29, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 214b
	ld %r14, 616(%r6)
	ld %r15, 624(%r6)
	ld %r16, 632(%r6)
	ld %r17, 640(%r6)
	ld %r18, 648(%r6)
	ld %r19, 656(%r6)
	ld %r20, 664(%r6)
	ld %r21, 112(%r6)
	ld %r22, 120(%r6)
	ld %r23, 128(%r6)
	ld %r24, 136(%r6)
	ld %r25, 144(%r6)
	ld %r26, 152(%r6)
	ld %r27, 160(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r28, 656(%r6)
	std %r29, 664(%r6)
	ld %r14, 840(%r6)
	ld %r15, 848(%r6)
	ld %r16, 856(%r6)
	ld %r17, 864(%r6)
	ld %r18, 872(%r6)
	ld %r19, 880(%r6)
	ld %r20, 888(%r6)
	ld %r21, 616(%r6)
	ld %r22, 624(%r6)
	ld %r23, 632(%r6)
	ld %r24, 640(%r6)
	ld %r25, 648(%r6)
	ld %r26, 656(%r6)
	ld %r27, 664(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 840(%r6)
	std %r8, 848(%r6)
	std %r9, 856(%r6)
	std %r10, 864(%r6)
	std %r11, 872(%r6)
	std %r28, 880(%r6)
	std %r29, 888(%r6)
	ld %r14, 56(%r6)
	ld %r15, 64(%r6)
	ld %r16, 72(%r6)
	ld %r17, 80(%r6)
	ld %r18, 88(%r6)
	ld %r19, 96(%r6)
	ld %r20, 104(%r6)
	ld %r21, 840(%r6)
	ld %r22, 848(%r6)
	ld %r23, 856(%r6)
	ld %r24, 864(%r6)
	ld %r25, 872(%r6)
	ld %r26, 880(%r6)
	ld %r27, 888(%r6)
	li %r7, 0
	li %r8, 0
	li %r9, 0
	mulld %r4, %r14, %r21
	mulhdu %r5, %r14, %r21
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	li %r10, 0
	mulld %r4, %r14, %r22
	mulhdu %r5, %r14, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r21
	mulhdu %r5, %r15, %r21
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	li %r11, 0
	mulld %r4, %r14, %r23
	mulhdu %r5, %r14, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r21
	mulhdu %r5, %r16, %r21
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	li %r28, 0
	mulld %r4, %r14, %r24
	mulhdu %r5, %r14, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	mulld %r4, %r17, %r21
	mulhdu %r5, %r17, %r21
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r28, %r28
	li %r29, 0
	mulld %r4, %r14, %r25
	mulhdu %r5, %r14, %r25
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r21
	mulhdu %r5, %r18, %r21
	addc %r11, %r11, %r4
	adde %r28, %r28, %r5
	addze %r29, %r29
	li %r30, 0
	mulld %r4, %r14, %r26
	mulhdu %r5, %r14, %r26
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r21
	mulhdu %r5, %r19, %r21
	addc %r28, %r28, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	li %r31, 0
	mulld %r4, %r14, %r27
	mulhdu %r5, %r14, %r27
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r21
	mulhdu %r5, %r20, %r21
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	li %r14, 0
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r14, %r14
	li %r21, 0
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r31, %r31, %r4
	adde %r14, %r14, %r5
	addze %r21, %r21
	li %r15, 0
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r14, %r14, %r4
	adde %r21, %r21, %r5
	addze %r15, %r15
	li %r22, 0
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r21, %r21, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	li %r16, 0
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	li %r17, 0
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r17, %r17
	addc %r7, %r7, %r30
	adde %r8, %r8, %r31
	adde %r9, %r9, %r14
	adde %r10, %r10, %r21
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	li %r4, 0
	addze %r4, %r4
	rldicl %r18, %r21, 32, 32
	rldicr %r27, %r15, 32, 31
	add %r18, %r18, %r27
	rldicl %r19, %r15, 32, 32
	rldicr %r27, %r22, 32, 31
	add %r19, %r19, %r27
	rldicl %r20, %r22, 32, 32
	rldicr %r27, %r16, 32, 31
	add %r20, %r20, %r27
	rldicl %r23, %r16, 32, 32
	rldicr %r27, %r30, 32, 31
	add %r23, %r23, %r27
	rldicl %r24, %r30, 32, 32
	rldicr %r27, %r31, 32, 31
	add %r24, %r24, %r27
	rldicl %r25, %r31, 32, 32
	rldicr %r27, %r14, 32, 31
	add %r25, %r25, %r27
	rldicl %r26, %r14, 32, 32
	rldicr %r27, %r21, 32, 31
	add %r26, %r26, %r27
	addc %r7, %r7, %r18
	adde %r8, %r8, %r19
	adde %r9, %r9, %r20
	adde %r10, %r10, %r23
	adde %r11, %r11, %r24
	adde %r28, %r28, %r25
	adde %r29, %r29, %r26
	addze %r4, %r4
	li %r18, 0
	rldicl %r19, %r21, 32, 32
	rldicr %r19, %r19, 32, 31
	addc %r7, %r7, %r18
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r19
	adde %r11, %r11, %r15
	adde %r28, %r28, %r22
	adde %r29, %r29, %r16
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r18
	adde %r9, %r9, %r18
	adde %r10, %r10, %r5
	adde %r11, %r11, %r18
	adde %r28, %r28, %r18
	adde %r29, %r29, %r18
	std %r7, 56(%r6)
	std %r8, 64(%r6)
	std %r9, 72(%r6)
	std %r10, 80(%r6)
	std %r11, 88(%r6)
	std %r28, 96(%r6)
	std %r29, 104(%r6)
	ld %r14, 1512(%r6)
	ld %r15, 1520(%r6)
	ld %r16, 1528(%r6)
	ld %r17, 1536(%r6)
	ld %r18, 1544(%r6)
	ld %r19, 1552(%r6)
	ld %r20, 1560(%r6)
	ld %r21, 1568(%r6)
	ld %r22, 1576(%r6)
	ld %r23, 1584(%r6)
	ld %r24, 1592(%r6)
	ld %r25, 1600(%r6)
	ld %r26, 1608(%r6)
	ld %r27, 1616(%r6)
	ld %r28, 1624(%r6)
	ld %r29, 1632(%r6)
	ld %r30, 1640(%r6)
	ld %r31, 1648(%r6)
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
