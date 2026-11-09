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
	std %r14, 896(%r6)
	std %r15, 904(%r6)
	std %r16, 912(%r6)
	std %r17, 920(%r6)
	std %r18, 928(%r6)
	std %r19, 936(%r6)
	std %r20, 944(%r6)
	std %r21, 952(%r6)
	std %r22, 960(%r6)
	std %r23, 968(%r6)
	std %r24, 976(%r6)
	std %r25, 984(%r6)
	std %r26, 992(%r6)
	std %r27, 1000(%r6)
	std %r28, 1008(%r6)
	std %r29, 1016(%r6)
	std %r30, 1024(%r6)
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
	ld %r14, 160(%r6)
	ld %r15, 168(%r6)
	ld %r16, 176(%r6)
	ld %r17, 184(%r6)
	ld %r18, 160(%r6)
	ld %r19, 168(%r6)
	ld %r20, 176(%r6)
	ld %r21, 184(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 192(%r6)
	ld %r15, 200(%r6)
	ld %r16, 208(%r6)
	ld %r17, 216(%r6)
	ld %r18, 192(%r6)
	ld %r19, 200(%r6)
	ld %r20, 208(%r6)
	ld %r21, 216(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 256(%r6)
	ld %r15, 264(%r6)
	ld %r16, 272(%r6)
	ld %r17, 280(%r6)
	ld %r18, 160(%r6)
	ld %r19, 168(%r6)
	ld %r20, 176(%r6)
	ld %r21, 184(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 224(%r6)
	ld %r15, 232(%r6)
	ld %r16, 240(%r6)
	ld %r17, 248(%r6)
	ld %r18, 192(%r6)
	ld %r19, 200(%r6)
	ld %r20, 208(%r6)
	ld %r21, 216(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 96(%r6)
	ld %r15, 104(%r6)
	ld %r16, 112(%r6)
	ld %r17, 120(%r6)
	ld %r18, 96(%r6)
	ld %r19, 104(%r6)
	ld %r20, 112(%r6)
	ld %r21, 120(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 128(%r6)
	ld %r15, 136(%r6)
	ld %r16, 144(%r6)
	ld %r17, 152(%r6)
	ld %r18, 128(%r6)
	ld %r19, 136(%r6)
	ld %r20, 144(%r6)
	ld %r21, 152(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 0(%r6)
	ld %r15, 8(%r6)
	ld %r16, 16(%r6)
	ld %r17, 24(%r6)
	ld %r18, 128(%r6)
	ld %r19, 136(%r6)
	ld %r20, 144(%r6)
	ld %r21, 152(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 288(%r6)
	ld %r15, 296(%r6)
	ld %r16, 304(%r6)
	ld %r17, 312(%r6)
	ld %r18, 320(%r6)
	ld %r19, 328(%r6)
	ld %r20, 336(%r6)
	ld %r21, 344(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 352(%r6)
	ld %r15, 360(%r6)
	ld %r16, 368(%r6)
	ld %r17, 376(%r6)
	ld %r18, 64(%r6)
	ld %r19, 72(%r6)
	ld %r20, 80(%r6)
	ld %r21, 88(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 64(%r6)
	ld %r15, 72(%r6)
	ld %r16, 80(%r6)
	ld %r17, 88(%r6)
	ld %r18, 64(%r6)
	ld %r19, 72(%r6)
	ld %r20, 80(%r6)
	ld %r21, 88(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 160(%r6)
	ld %r15, 168(%r6)
	ld %r16, 176(%r6)
	ld %r17, 184(%r6)
	ld %r18, 160(%r6)
	ld %r19, 168(%r6)
	ld %r20, 176(%r6)
	ld %r21, 184(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 192(%r6)
	ld %r15, 200(%r6)
	ld %r16, 208(%r6)
	ld %r17, 216(%r6)
	ld %r18, 192(%r6)
	ld %r19, 200(%r6)
	ld %r20, 208(%r6)
	ld %r21, 216(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 64(%r6)
	ld %r15, 72(%r6)
	ld %r16, 80(%r6)
	ld %r17, 88(%r6)
	ld %r18, 192(%r6)
	ld %r19, 200(%r6)
	ld %r20, 208(%r6)
	ld %r21, 216(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 160(%r6)
	ld %r15, 168(%r6)
	ld %r16, 176(%r6)
	ld %r17, 184(%r6)
	ld %r18, 192(%r6)
	ld %r19, 200(%r6)
	ld %r20, 208(%r6)
	ld %r21, 216(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 160(%r6)
	ld %r15, 168(%r6)
	ld %r16, 176(%r6)
	ld %r17, 184(%r6)
	ld %r18, 160(%r6)
	ld %r19, 168(%r6)
	ld %r20, 176(%r6)
	ld %r21, 184(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 192(%r6)
	ld %r15, 200(%r6)
	ld %r16, 208(%r6)
	ld %r17, 216(%r6)
	ld %r18, 224(%r6)
	ld %r19, 232(%r6)
	ld %r20, 240(%r6)
	ld %r21, 248(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 192(%r6)
	ld %r15, 200(%r6)
	ld %r16, 208(%r6)
	ld %r17, 216(%r6)
	ld %r18, 192(%r6)
	ld %r19, 200(%r6)
	ld %r20, 208(%r6)
	ld %r21, 216(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 224(%r6)
	ld %r15, 232(%r6)
	ld %r16, 240(%r6)
	ld %r17, 248(%r6)
	ld %r18, 224(%r6)
	ld %r19, 232(%r6)
	ld %r20, 240(%r6)
	ld %r21, 248(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 224(%r6)
	ld %r15, 232(%r6)
	ld %r16, 240(%r6)
	ld %r17, 248(%r6)
	ld %r18, 192(%r6)
	ld %r19, 200(%r6)
	ld %r20, 208(%r6)
	ld %r21, 216(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 192(%r6)
	ld %r15, 200(%r6)
	ld %r16, 208(%r6)
	ld %r17, 216(%r6)
	ld %r18, 192(%r6)
	ld %r19, 200(%r6)
	ld %r20, 208(%r6)
	ld %r21, 216(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 224(%r6)
	ld %r15, 232(%r6)
	ld %r16, 240(%r6)
	ld %r17, 248(%r6)
	ld %r18, 224(%r6)
	ld %r19, 232(%r6)
	ld %r20, 240(%r6)
	ld %r21, 248(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 224(%r6)
	ld %r15, 232(%r6)
	ld %r16, 240(%r6)
	ld %r17, 248(%r6)
	ld %r18, 192(%r6)
	ld %r19, 200(%r6)
	ld %r20, 208(%r6)
	ld %r21, 216(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 224(%r6)
	ld %r15, 232(%r6)
	ld %r16, 240(%r6)
	ld %r17, 248(%r6)
	ld %r18, 224(%r6)
	ld %r19, 232(%r6)
	ld %r20, 240(%r6)
	ld %r21, 248(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 256(%r6)
	ld %r15, 264(%r6)
	ld %r16, 272(%r6)
	ld %r17, 280(%r6)
	ld %r18, 256(%r6)
	ld %r19, 264(%r6)
	ld %r20, 272(%r6)
	ld %r21, 280(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 256(%r6)
	ld %r15, 264(%r6)
	ld %r16, 272(%r6)
	ld %r17, 280(%r6)
	ld %r18, 224(%r6)
	ld %r19, 232(%r6)
	ld %r20, 240(%r6)
	ld %r21, 248(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 224(%r6)
	ld %r15, 232(%r6)
	ld %r16, 240(%r6)
	ld %r17, 248(%r6)
	ld %r18, 224(%r6)
	ld %r19, 232(%r6)
	ld %r20, 240(%r6)
	ld %r21, 248(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 224(%r6)
	ld %r15, 232(%r6)
	ld %r16, 240(%r6)
	ld %r17, 248(%r6)
	ld %r18, 224(%r6)
	ld %r19, 232(%r6)
	ld %r20, 240(%r6)
	ld %r21, 248(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 224(%r6)
	ld %r15, 232(%r6)
	ld %r16, 240(%r6)
	ld %r17, 248(%r6)
	ld %r18, 192(%r6)
	ld %r19, 200(%r6)
	ld %r20, 208(%r6)
	ld %r21, 216(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 192(%r6)
	ld %r15, 200(%r6)
	ld %r16, 208(%r6)
	ld %r17, 216(%r6)
	ld %r18, 192(%r6)
	ld %r19, 200(%r6)
	ld %r20, 208(%r6)
	ld %r21, 216(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 224(%r6)
	ld %r15, 232(%r6)
	ld %r16, 240(%r6)
	ld %r17, 248(%r6)
	ld %r18, 224(%r6)
	ld %r19, 232(%r6)
	ld %r20, 240(%r6)
	ld %r21, 248(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 224(%r6)
	ld %r15, 232(%r6)
	ld %r16, 240(%r6)
	ld %r17, 248(%r6)
	ld %r18, 192(%r6)
	ld %r19, 200(%r6)
	ld %r20, 208(%r6)
	ld %r21, 216(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 224(%r6)
	ld %r15, 232(%r6)
	ld %r16, 240(%r6)
	ld %r17, 248(%r6)
	ld %r18, 224(%r6)
	ld %r19, 232(%r6)
	ld %r20, 240(%r6)
	ld %r21, 248(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 256(%r6)
	ld %r15, 264(%r6)
	ld %r16, 272(%r6)
	ld %r17, 280(%r6)
	ld %r18, 256(%r6)
	ld %r19, 264(%r6)
	ld %r20, 272(%r6)
	ld %r21, 280(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 256(%r6)
	ld %r15, 264(%r6)
	ld %r16, 272(%r6)
	ld %r17, 280(%r6)
	ld %r18, 224(%r6)
	ld %r19, 232(%r6)
	ld %r20, 240(%r6)
	ld %r21, 248(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 224(%r6)
	ld %r15, 232(%r6)
	ld %r16, 240(%r6)
	ld %r17, 248(%r6)
	ld %r18, 224(%r6)
	ld %r19, 232(%r6)
	ld %r20, 240(%r6)
	ld %r21, 248(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 224(%r6)
	ld %r15, 232(%r6)
	ld %r16, 240(%r6)
	ld %r17, 248(%r6)
	ld %r18, 224(%r6)
	ld %r19, 232(%r6)
	ld %r20, 240(%r6)
	ld %r21, 248(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 224(%r6)
	ld %r15, 232(%r6)
	ld %r16, 240(%r6)
	ld %r17, 248(%r6)
	ld %r18, 192(%r6)
	ld %r19, 200(%r6)
	ld %r20, 208(%r6)
	ld %r21, 216(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 192(%r6)
	ld %r15, 200(%r6)
	ld %r16, 208(%r6)
	ld %r17, 216(%r6)
	ld %r18, 192(%r6)
	ld %r19, 200(%r6)
	ld %r20, 208(%r6)
	ld %r21, 216(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 192(%r6)
	ld %r15, 200(%r6)
	ld %r16, 208(%r6)
	ld %r17, 216(%r6)
	ld %r18, 192(%r6)
	ld %r19, 200(%r6)
	ld %r20, 208(%r6)
	ld %r21, 216(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 192(%r6)
	ld %r15, 200(%r6)
	ld %r16, 208(%r6)
	ld %r17, 216(%r6)
	ld %r18, 160(%r6)
	ld %r19, 168(%r6)
	ld %r20, 176(%r6)
	ld %r21, 184(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 32(%r6)
	ld %r15, 40(%r6)
	ld %r16, 48(%r6)
	ld %r17, 56(%r6)
	ld %r18, 480(%r6)
	ld %r19, 488(%r6)
	ld %r20, 496(%r6)
	ld %r21, 504(%r6)
	li %r22, 0
	li %r23, 0
	li %r24, 0
	mulld %r7, %r14, %r18
	mulhdu %r4, %r14, %r18
	addc %r22, %r22, %r7
	adde %r23, %r23, %r4
	addze %r24, %r24
	li %r25, 0
	mulld %r7, %r15, %r18
	mulhdu %r4, %r15, %r18
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	mulld %r7, %r14, %r19
	mulhdu %r4, %r14, %r19
	addc %r23, %r23, %r7
	adde %r24, %r24, %r4
	addze %r25, %r25
	li %r26, 0
	mulld %r7, %r16, %r18
	mulhdu %r4, %r16, %r18
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r15, %r19
	mulhdu %r4, %r15, %r19
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	mulld %r7, %r14, %r20
	mulhdu %r4, %r14, %r20
	addc %r24, %r24, %r7
	adde %r25, %r25, %r4
	addze %r26, %r26
	li %r27, 0
	mulld %r7, %r17, %r18
	mulhdu %r4, %r17, %r18
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r16, %r19
	mulhdu %r4, %r16, %r19
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r15, %r20
	mulhdu %r4, %r15, %r20
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	mulld %r7, %r14, %r21
	mulhdu %r4, %r14, %r21
	addc %r25, %r25, %r7
	adde %r26, %r26, %r4
	addze %r27, %r27
	li %r28, 0
	mulld %r7, %r17, %r19
	mulhdu %r4, %r17, %r19
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r16, %r20
	mulhdu %r4, %r16, %r20
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	mulld %r7, %r15, %r21
	mulhdu %r4, %r15, %r21
	addc %r26, %r26, %r7
	adde %r27, %r27, %r4
	addze %r28, %r28
	li %r29, 0
	mulld %r7, %r17, %r20
	mulhdu %r4, %r17, %r20
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	mulld %r7, %r16, %r21
	mulhdu %r4, %r16, %r21
	addc %r27, %r27, %r7
	adde %r28, %r28, %r4
	addze %r29, %r29
	li %r30, 0
	mulld %r7, %r17, %r21
	mulhdu %r4, %r17, %r21
	addc %r28, %r28, %r7
	adde %r29, %r29, %r4
	addze %r30, %r30
	li %r5, 38
	mulld %r4, %r26, %r5
	addc %r8, %r22, %r4
	mulld %r4, %r27, %r5
	adde %r9, %r23, %r4
	mulld %r4, %r28, %r5
	adde %r10, %r24, %r4
	mulld %r4, %r29, %r5
	adde %r11, %r25, %r4
	li %r7, 0
	addze %r7, %r7
	mulhdu %r4, %r26, %r5
	addc %r9, %r9, %r4
	mulhdu %r4, %r27, %r5
	adde %r10, %r10, %r4
	mulhdu %r4, %r28, %r5
	adde %r11, %r11, %r4
	mulhdu %r4, %r29, %r5
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
	ld %r14, 896(%r6)
	ld %r15, 904(%r6)
	ld %r16, 912(%r6)
	ld %r17, 920(%r6)
	ld %r18, 928(%r6)
	ld %r19, 936(%r6)
	ld %r20, 944(%r6)
	ld %r21, 952(%r6)
	ld %r22, 960(%r6)
	ld %r23, 968(%r6)
	ld %r24, 976(%r6)
	ld %r25, 984(%r6)
	ld %r26, 992(%r6)
	ld %r27, 1000(%r6)
	ld %r28, 1008(%r6)
	ld %r29, 1016(%r6)
	ld %r30, 1024(%r6)
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
