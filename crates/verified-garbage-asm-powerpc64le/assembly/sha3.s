// The functions of `src/sha3.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_absorb:
	stdu %r1, -672(%r1)
	addi %r8, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 512(%r8)
	std %r27, 520(%r8)
	std %r28, 528(%r8)
	std %r29, 536(%r8)
	std %r30, 544(%r8)
	std %r31, 552(%r8)
	addi %r26, %r3, 0
	addi %r27, %r8, 0
	addi %r28, %r4, 0
	addi %r29, %r5, 0
	addi %r30, %r6, 0
	addi %r31, %r7, 0
	cmpldi %cr0, %r31, 0
	beq %cr0, 20f
22:
	li %r10, 7
	and %r10, %r29, %r10
	addi %r11, %r31, -8
	rldicl %r11, %r11, 1, 63
	or %r10, %r10, %r11
	cmpldi %cr0, %r10, 0
	beq %cr0, 23f
	lbz %r9, 0(%r30)
	add %r10, %r26, %r29
	lbz %r11, 0(%r10)
	xor %r9, %r9, %r11
	stb %r9, 0(%r10)
	addi %r30, %r30, 1
	addi %r29, %r29, 1
	addi %r31, %r31, -1
	subf %r9, %r28, %r29
	b 24f
23:
	ld %r9, 0(%r30)
	add %r10, %r26, %r29
	ld %r11, 0(%r10)
	xor %r9, %r9, %r11
	std %r9, 0(%r10)
	addi %r30, %r30, 8
	addi %r29, %r29, 8
	addi %r31, %r31, -8
	subf %r9, %r28, %r29
24:
	cmpldi %cr0, %r9, 0
	beq %cr0, 25f
	b 26f
25:
	li %r29, 0
	addi %r3, %r26, 0
	addi %r4, %r27, 0
	bl {vg_keccak_f1600}
26:
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	b 21f
20:
21:
	addi %r3, %r29, 0
	ld %r26, 512(%r27)
	ld %r28, 528(%r27)
	ld %r29, 536(%r27)
	ld %r30, 544(%r27)
	ld %r31, 552(%r27)
	ld %r27, 520(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 672
	blr

vg_keccak_absorb_scratch:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 512(%r8)
	std %r27, 520(%r8)
	std %r28, 528(%r8)
	std %r29, 536(%r8)
	std %r30, 544(%r8)
	std %r31, 552(%r8)
	addi %r26, %r3, 0
	addi %r27, %r8, 0
	addi %r28, %r4, 0
	addi %r29, %r5, 0
	addi %r30, %r6, 0
	addi %r31, %r7, 0
	cmpldi %cr0, %r31, 0
	beq %cr0, 20f
22:
	li %r10, 7
	and %r10, %r29, %r10
	addi %r11, %r31, -8
	rldicl %r11, %r11, 1, 63
	or %r10, %r10, %r11
	cmpldi %cr0, %r10, 0
	beq %cr0, 23f
	lbz %r9, 0(%r30)
	add %r10, %r26, %r29
	lbz %r11, 0(%r10)
	xor %r9, %r9, %r11
	stb %r9, 0(%r10)
	addi %r30, %r30, 1
	addi %r29, %r29, 1
	addi %r31, %r31, -1
	subf %r9, %r28, %r29
	b 24f
23:
	ld %r9, 0(%r30)
	add %r10, %r26, %r29
	ld %r11, 0(%r10)
	xor %r9, %r9, %r11
	std %r9, 0(%r10)
	addi %r30, %r30, 8
	addi %r29, %r29, 8
	addi %r31, %r31, -8
	subf %r9, %r28, %r29
24:
	cmpldi %cr0, %r9, 0
	beq %cr0, 25f
	b 26f
25:
	li %r29, 0
	addi %r3, %r26, 0
	addi %r4, %r27, 0
	bl {vg_keccak_f1600}
26:
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	b 21f
20:
21:
	addi %r3, %r29, 0
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

vg_keccak_pad:
	stdu %r1, -672(%r1)
	addi %r7, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	add %r9, %r3, %r5
	lbz %r10, 0(%r9)
	xor %r10, %r10, %r6
	stb %r10, 0(%r9)
	add %r9, %r3, %r4
	addi %r9, %r9, -1
	lbz %r10, 0(%r9)
	li %r11, 128
	xor %r10, %r10, %r11
	stb %r10, 0(%r9)
	addi %r4, %r7, 0
	bl {vg_keccak_f1600}
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 672
	blr

vg_keccak_squeeze:
	stdu %r1, -672(%r1)
	addi %r8, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 512(%r8)
	std %r27, 520(%r8)
	std %r28, 528(%r8)
	std %r29, 536(%r8)
	std %r30, 544(%r8)
	std %r31, 552(%r8)
	addi %r26, %r3, 0
	addi %r27, %r8, 0
	addi %r28, %r4, 0
	addi %r29, %r5, 0
	addi %r30, %r6, 0
	addi %r31, %r7, 0
	cmpldi %cr0, %r31, 0
	beq %cr0, 20f
22:
	subf %r9, %r28, %r29
	cmpldi %cr0, %r9, 0
	beq %cr0, 23f
	b 24f
23:
	li %r29, 0
	addi %r3, %r26, 0
	addi %r4, %r27, 0
	bl {vg_keccak_f1600}
24:
	li %r10, 7
	and %r10, %r29, %r10
	addi %r11, %r31, -8
	rldicl %r11, %r11, 1, 63
	or %r10, %r10, %r11
	cmpldi %cr0, %r10, 0
	beq %cr0, 25f
	add %r10, %r26, %r29
	lbz %r9, 0(%r10)
	stb %r9, 0(%r30)
	addi %r30, %r30, 1
	addi %r29, %r29, 1
	addi %r31, %r31, -1
	b 26f
25:
	add %r10, %r26, %r29
	ld %r9, 0(%r10)
	std %r9, 0(%r30)
	addi %r30, %r30, 8
	addi %r29, %r29, 8
	addi %r31, %r31, -8
26:
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	b 21f
20:
21:
	addi %r3, %r29, 0
	ld %r26, 512(%r27)
	ld %r28, 528(%r27)
	ld %r29, 536(%r27)
	ld %r30, 544(%r27)
	ld %r31, 552(%r27)
	ld %r27, 520(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 672
	blr
