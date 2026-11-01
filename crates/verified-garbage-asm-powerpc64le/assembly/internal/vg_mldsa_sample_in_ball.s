// The functions of `src/internal/vg_mldsa_sample_in_ball.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_sample_in_ball:
	mflr %r0
	std %r27, 2000(%r7)
	std %r28, 2008(%r7)
	std %r29, 2016(%r7)
	std %r30, 2024(%r7)
	std %r31, 2032(%r7)
	std %r0, 2040(%r7)
	addi %r31, %r7, 0
	addi %r30, %r6, 0
	addi %r29, %r3, 0
	addi %r28, %r4, 0
	rldicr %r27, %r5, 32, 31
	rldicl %r27, %r27, 32, 32
	li %r0, 0
	std %r0, 0(%r31)
	std %r0, 8(%r31)
	std %r0, 16(%r31)
	std %r0, 24(%r31)
	std %r0, 32(%r31)
	std %r0, 40(%r31)
	std %r0, 48(%r31)
	std %r0, 56(%r31)
	std %r0, 64(%r31)
	std %r0, 72(%r31)
	std %r0, 80(%r31)
	std %r0, 88(%r31)
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	std %r0, 112(%r31)
	std %r0, 120(%r31)
	std %r0, 128(%r31)
	std %r0, 136(%r31)
	std %r0, 144(%r31)
	std %r0, 152(%r31)
	std %r0, 160(%r31)
	std %r0, 168(%r31)
	std %r0, 176(%r31)
	std %r0, 184(%r31)
	std %r0, 192(%r31)
	addi %r3, %r31, 0
	li %r4, 136
	li %r5, 0
	addi %r6, %r29, 0
	addi %r7, %r28, 0
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 136
	li %r6, 31
	addi %r7, %r31, 200
	bl {vg_keccak_pad_scratch}
	addi %r3, %r31, 0
	li %r4, 136
	li %r5, 0
	addi %r6, %r31, 840
	li %r7, 272
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	li %r12, 0
	addi %r4, %r30, 0
	li %r6, 256
20:
	stw %r12, 0(%r4)
	addi %r4, %r4, 4
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 20b
	ld %r9, 840(%r31)
	li %r5, 256
	subf %r5, %r27, %r5
	rldicr %r4, %r5, 2, 61
	add %r4, %r30, %r4
	addi %r3, %r31, 848
	li %r6, 264
	lis %r7, 127
	ori %r7, %r7, 57343
21:
	addi %r12, %r5, -256
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	beq %cr0, 22f
	lbz %r8, 0(%r3)
	subf %r11, %r8, %r5
	rldicl %r11, %r11, 1, 63
	cmpldi %cr0, %r11, 0
	beq %cr0, 24f
	b 25f
24:
	rldicr %r10, %r8, 2, 61
	add %r10, %r30, %r10
	lwz %r11, 0(%r10)
	stw %r11, 0(%r4)
	rldicr %r12, %r9, 63, 0
	rldicl %r12, %r12, 1, 63
	mulld %r12, %r12, %r7
	addi %r12, %r12, 1
	stw %r12, 0(%r10)
	rldicl %r9, %r9, 63, 1
	addi %r4, %r4, 4
	addi %r5, %r5, 1
25:
	b 23f
22:
23:
	addi %r3, %r3, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 21b
	rldicl %r3, %r5, 56, 8
	ld %r0, 2040(%r31)
	mtlr %r0
	ld %r27, 2000(%r31)
	ld %r28, 2008(%r31)
	ld %r29, 2016(%r31)
	ld %r30, 2024(%r31)
	ld %r31, 2032(%r31)
	blr
