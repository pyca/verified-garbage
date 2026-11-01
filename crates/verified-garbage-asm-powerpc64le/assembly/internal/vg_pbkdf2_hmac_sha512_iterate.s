// The functions of `src/internal/vg_pbkdf2_hmac_sha512_iterate.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha512_iterate:
	mflr %r0
	rldicr %r5, %r5, 32, 31
	rldicl %r5, %r5, 32, 32
	std %r26, 176(%r7)
	std %r27, 184(%r7)
	std %r28, 192(%r7)
	std %r29, 200(%r7)
	std %r30, 208(%r7)
	std %r31, 216(%r7)
	std %r0, 224(%r7)
	addi %r26, %r7, 232
	addi %r27, %r7, 0
	addi %r28, %r7, 296
	addi %r30, %r6, 0
	addi %r31, %r5, 0
	lwz %r8, 0(%r4)
	stw %r8, 0(%r28)
	lwz %r8, 4(%r4)
	stw %r8, 4(%r28)
	lwz %r8, 8(%r4)
	stw %r8, 8(%r28)
	lwz %r8, 12(%r4)
	stw %r8, 12(%r28)
	lwz %r8, 16(%r4)
	stw %r8, 16(%r28)
	lwz %r8, 20(%r4)
	stw %r8, 20(%r28)
	lwz %r8, 24(%r4)
	stw %r8, 24(%r28)
	lwz %r8, 28(%r4)
	stw %r8, 28(%r28)
	lwz %r8, 32(%r4)
	stw %r8, 32(%r28)
	lwz %r8, 36(%r4)
	stw %r8, 36(%r28)
	lwz %r8, 40(%r4)
	stw %r8, 40(%r28)
	lwz %r8, 44(%r4)
	stw %r8, 44(%r28)
	lwz %r8, 48(%r4)
	stw %r8, 48(%r28)
	lwz %r8, 52(%r4)
	stw %r8, 52(%r28)
	lwz %r8, 56(%r4)
	stw %r8, 56(%r28)
	lwz %r8, 60(%r4)
	stw %r8, 60(%r28)
	li %r8, 128
	stw %r8, 64(%r28)
	li %r8, 0
	stw %r8, 68(%r28)
	stw %r8, 72(%r28)
	stw %r8, 76(%r28)
	stw %r8, 80(%r28)
	stw %r8, 84(%r28)
	stw %r8, 88(%r28)
	stw %r8, 92(%r28)
	stw %r8, 96(%r28)
	stw %r8, 100(%r28)
	stw %r8, 104(%r28)
	stw %r8, 108(%r28)
	li %r29, 192
	rldicl %r8, %r29, 3, 61
	li %r11, 176
	stdbrx %r8, %r26, %r11
	add %r8, %r29, %r29
	add %r8, %r8, %r8
	add %r8, %r8, %r8
	li %r11, 184
	stdbrx %r8, %r26, %r11
	addi %r29, %r3, 0
	cmpldi %cr0, %r31, 0
	beq %cr0, 20f
22:
	lwz %r8, 0(%r29)
	stw %r8, 0(%r26)
	lwz %r8, 4(%r29)
	stw %r8, 4(%r26)
	lwz %r8, 8(%r29)
	stw %r8, 8(%r26)
	lwz %r8, 12(%r29)
	stw %r8, 12(%r26)
	lwz %r8, 16(%r29)
	stw %r8, 16(%r26)
	lwz %r8, 20(%r29)
	stw %r8, 20(%r26)
	lwz %r8, 24(%r29)
	stw %r8, 24(%r26)
	lwz %r8, 28(%r29)
	stw %r8, 28(%r26)
	lwz %r8, 32(%r29)
	stw %r8, 32(%r26)
	lwz %r8, 36(%r29)
	stw %r8, 36(%r26)
	lwz %r8, 40(%r29)
	stw %r8, 40(%r26)
	lwz %r8, 44(%r29)
	stw %r8, 44(%r26)
	lwz %r8, 48(%r29)
	stw %r8, 48(%r26)
	lwz %r8, 52(%r29)
	stw %r8, 52(%r26)
	lwz %r8, 56(%r29)
	stw %r8, 56(%r26)
	lwz %r8, 60(%r29)
	stw %r8, 60(%r26)
	addi %r4, %r28, 0
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha512_compress}
	ld %r8, 0(%r26)
	li %r11, 0
	stdbrx %r8, %r28, %r11
	ld %r8, 8(%r26)
	li %r11, 8
	stdbrx %r8, %r28, %r11
	ld %r8, 16(%r26)
	li %r11, 16
	stdbrx %r8, %r28, %r11
	ld %r8, 24(%r26)
	li %r11, 24
	stdbrx %r8, %r28, %r11
	ld %r8, 32(%r26)
	li %r11, 32
	stdbrx %r8, %r28, %r11
	ld %r8, 40(%r26)
	li %r11, 40
	stdbrx %r8, %r28, %r11
	ld %r8, 48(%r26)
	li %r11, 48
	stdbrx %r8, %r28, %r11
	ld %r8, 56(%r26)
	li %r11, 56
	stdbrx %r8, %r28, %r11
	lwz %r8, 192(%r29)
	stw %r8, 0(%r26)
	lwz %r8, 196(%r29)
	stw %r8, 4(%r26)
	lwz %r8, 200(%r29)
	stw %r8, 8(%r26)
	lwz %r8, 204(%r29)
	stw %r8, 12(%r26)
	lwz %r8, 208(%r29)
	stw %r8, 16(%r26)
	lwz %r8, 212(%r29)
	stw %r8, 20(%r26)
	lwz %r8, 216(%r29)
	stw %r8, 24(%r26)
	lwz %r8, 220(%r29)
	stw %r8, 28(%r26)
	lwz %r8, 224(%r29)
	stw %r8, 32(%r26)
	lwz %r8, 228(%r29)
	stw %r8, 36(%r26)
	lwz %r8, 232(%r29)
	stw %r8, 40(%r26)
	lwz %r8, 236(%r29)
	stw %r8, 44(%r26)
	lwz %r8, 240(%r29)
	stw %r8, 48(%r26)
	lwz %r8, 244(%r29)
	stw %r8, 52(%r26)
	lwz %r8, 248(%r29)
	stw %r8, 56(%r26)
	lwz %r8, 252(%r29)
	stw %r8, 60(%r26)
	addi %r4, %r28, 0
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha512_compress}
	ld %r8, 0(%r26)
	li %r11, 0
	stdbrx %r8, %r28, %r11
	ld %r8, 8(%r26)
	li %r11, 8
	stdbrx %r8, %r28, %r11
	ld %r8, 16(%r26)
	li %r11, 16
	stdbrx %r8, %r28, %r11
	ld %r8, 24(%r26)
	li %r11, 24
	stdbrx %r8, %r28, %r11
	ld %r8, 32(%r26)
	li %r11, 32
	stdbrx %r8, %r28, %r11
	ld %r8, 40(%r26)
	li %r11, 40
	stdbrx %r8, %r28, %r11
	ld %r8, 48(%r26)
	li %r11, 48
	stdbrx %r8, %r28, %r11
	ld %r8, 56(%r26)
	li %r11, 56
	stdbrx %r8, %r28, %r11
	lwz %r8, 0(%r28)
	lwz %r9, 0(%r30)
	xor %r8, %r8, %r9
	stw %r8, 0(%r30)
	lwz %r8, 4(%r28)
	lwz %r9, 4(%r30)
	xor %r8, %r8, %r9
	stw %r8, 4(%r30)
	lwz %r8, 8(%r28)
	lwz %r9, 8(%r30)
	xor %r8, %r8, %r9
	stw %r8, 8(%r30)
	lwz %r8, 12(%r28)
	lwz %r9, 12(%r30)
	xor %r8, %r8, %r9
	stw %r8, 12(%r30)
	lwz %r8, 16(%r28)
	lwz %r9, 16(%r30)
	xor %r8, %r8, %r9
	stw %r8, 16(%r30)
	lwz %r8, 20(%r28)
	lwz %r9, 20(%r30)
	xor %r8, %r8, %r9
	stw %r8, 20(%r30)
	lwz %r8, 24(%r28)
	lwz %r9, 24(%r30)
	xor %r8, %r8, %r9
	stw %r8, 24(%r30)
	lwz %r8, 28(%r28)
	lwz %r9, 28(%r30)
	xor %r8, %r8, %r9
	stw %r8, 28(%r30)
	lwz %r8, 32(%r28)
	lwz %r9, 32(%r30)
	xor %r8, %r8, %r9
	stw %r8, 32(%r30)
	lwz %r8, 36(%r28)
	lwz %r9, 36(%r30)
	xor %r8, %r8, %r9
	stw %r8, 36(%r30)
	lwz %r8, 40(%r28)
	lwz %r9, 40(%r30)
	xor %r8, %r8, %r9
	stw %r8, 40(%r30)
	lwz %r8, 44(%r28)
	lwz %r9, 44(%r30)
	xor %r8, %r8, %r9
	stw %r8, 44(%r30)
	lwz %r8, 48(%r28)
	lwz %r9, 48(%r30)
	xor %r8, %r8, %r9
	stw %r8, 48(%r30)
	lwz %r8, 52(%r28)
	lwz %r9, 52(%r30)
	xor %r8, %r8, %r9
	stw %r8, 52(%r30)
	lwz %r8, 56(%r28)
	lwz %r9, 56(%r30)
	xor %r8, %r8, %r9
	stw %r8, 56(%r30)
	lwz %r8, 60(%r28)
	lwz %r9, 60(%r30)
	xor %r8, %r8, %r9
	stw %r8, 60(%r30)
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r0, 224(%r27)
	ld %r26, 176(%r27)
	ld %r28, 192(%r27)
	ld %r29, 200(%r27)
	ld %r30, 208(%r27)
	ld %r31, 216(%r27)
	ld %r27, 184(%r27)
	mtlr %r0
	blr
