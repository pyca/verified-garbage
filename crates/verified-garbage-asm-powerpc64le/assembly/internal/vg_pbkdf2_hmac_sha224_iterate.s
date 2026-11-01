// The functions of `src/internal/vg_pbkdf2_hmac_sha224_iterate.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha224_iterate:
	mflr %r0
	rldicr %r5, %r5, 32, 31
	rldicl %r5, %r5, 32, 32
	std %r26, 112(%r7)
	std %r27, 120(%r7)
	std %r28, 128(%r7)
	std %r29, 136(%r7)
	std %r30, 144(%r7)
	std %r31, 152(%r7)
	std %r0, 160(%r7)
	addi %r26, %r7, 168
	addi %r27, %r7, 0
	addi %r28, %r7, 200
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
	li %r8, 128
	stw %r8, 28(%r28)
	li %r8, 0
	stw %r8, 32(%r28)
	stw %r8, 36(%r28)
	stw %r8, 40(%r28)
	stw %r8, 44(%r28)
	stw %r8, 48(%r28)
	stw %r8, 52(%r28)
	li %r29, 92
	add %r8, %r29, %r29
	add %r8, %r8, %r8
	add %r8, %r8, %r8
	li %r11, 88
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
	addi %r4, %r28, 0
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 96(%r29)
	stw %r8, 0(%r26)
	lwz %r8, 100(%r29)
	stw %r8, 4(%r26)
	lwz %r8, 104(%r29)
	stw %r8, 8(%r26)
	lwz %r8, 108(%r29)
	stw %r8, 12(%r26)
	lwz %r8, 112(%r29)
	stw %r8, 16(%r26)
	lwz %r8, 116(%r29)
	stw %r8, 20(%r26)
	lwz %r8, 120(%r29)
	stw %r8, 24(%r26)
	lwz %r8, 124(%r29)
	stw %r8, 28(%r26)
	addi %r4, %r28, 0
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
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
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r0, 160(%r27)
	ld %r26, 112(%r27)
	ld %r28, 128(%r27)
	ld %r29, 136(%r27)
	ld %r30, 144(%r27)
	ld %r31, 152(%r27)
	ld %r27, 120(%r27)
	mtlr %r0
	blr
