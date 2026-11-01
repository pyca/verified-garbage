// The functions of `src/internal/vg_blake2b_finalize_scratch.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2b_finalize_scratch:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 512(%r6)
	std %r27, 520(%r6)
	std %r28, 528(%r6)
	std %r29, 536(%r6)
	std %r30, 544(%r6)
	std %r31, 552(%r6)
	addi %r26, %r3, 0
	addi %r27, %r6, 0
	addi %r28, %r5, 0
	addi %r31, %r4, 0
	addi %r30, %r31, -1
	li %r9, 127
	and %r30, %r30, %r9
	addi %r30, %r30, 1
	cmpldi %cr0, %r31, 0
	beq %cr0, 20f
	b 21f
20:
	li %r30, 0
21:
	li %r9, 0
	li %r11, 128
	subf %r11, %r30, %r11
	cmpldi %cr0, %r11, 0
	beq %cr0, 22f
24:
	add %r12, %r26, %r30
	stb %r9, 64(%r12)
	addi %r30, %r30, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 24b
	b 23f
22:
23:
	addi %r3, %r26, 0
	addi %r4, %r26, 64
	li %r5, 1
	addi %r6, %r31, 0
	li %r7, 1
	addi %r8, %r27, 0
	bl {vg_blake2b_compress}
	ld %r9, 0(%r26)
	std %r9, 0(%r28)
	ld %r9, 8(%r26)
	std %r9, 8(%r28)
	ld %r9, 16(%r26)
	std %r9, 16(%r28)
	ld %r9, 24(%r26)
	std %r9, 24(%r28)
	ld %r9, 32(%r26)
	std %r9, 32(%r28)
	ld %r9, 40(%r26)
	std %r9, 40(%r28)
	ld %r9, 48(%r26)
	std %r9, 48(%r28)
	ld %r9, 56(%r26)
	std %r9, 56(%r28)
	ld %r26, 512(%r27)
	ld %r28, 528(%r27)
	ld %r29, 536(%r27)
	ld %r30, 544(%r27)
	ld %r31, 552(%r27)
	ld %r27, 520(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr
