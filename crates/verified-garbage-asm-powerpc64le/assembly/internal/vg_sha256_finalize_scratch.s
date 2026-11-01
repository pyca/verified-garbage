// The functions of `src/internal/vg_sha256_finalize_scratch.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha256_finalize_scratch:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 112(%r6)
	std %r27, 120(%r6)
	std %r28, 128(%r6)
	std %r29, 136(%r6)
	std %r30, 144(%r6)
	std %r31, 152(%r6)
	addi %r26, %r3, 0
	addi %r27, %r6, 0
	addi %r28, %r5, 0
	addi %r29, %r4, 0
	li %r8, 63
	and %r30, %r29, %r8
	li %r8, 128
	add %r11, %r26, %r30
	stb %r8, 32(%r11)
	addi %r30, %r30, 1
	addi %r31, %r30, 7
	rldicl %r31, %r31, 58, 6
20:
	li %r10, 64
	cmpldi %cr0, %r31, 0
	beq %cr0, 21f
	b 22f
21:
	li %r10, 56
22:
	li %r8, 0
	subf %r10, %r30, %r10
	cmpldi %cr0, %r10, 0
	beq %cr0, 23f
25:
	add %r11, %r26, %r30
	stb %r8, 32(%r11)
	addi %r30, %r30, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 25b
	b 24f
23:
24:
	cmpldi %cr0, %r31, 0
	beq %cr0, 26f
	b 27f
26:
	add %r8, %r29, %r29
	add %r8, %r8, %r8
	add %r8, %r8, %r8
	li %r11, 88
	stdbrx %r8, %r26, %r11
27:
	addi %r4, %r26, 32
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	li %r30, 0
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	beq %cr0, 20b
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
	lwz %r8, 28(%r26)
	li %r11, 28
	stwbrx %r8, %r28, %r11
	ld %r26, 112(%r27)
	ld %r28, 128(%r27)
	ld %r29, 136(%r27)
	ld %r30, 144(%r27)
	ld %r31, 152(%r27)
	ld %r27, 120(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr
