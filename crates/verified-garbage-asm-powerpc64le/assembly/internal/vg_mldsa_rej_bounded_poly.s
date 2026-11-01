// The functions of `src/internal/vg_mldsa_rej_bounded_poly.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_rej_bounded_poly:
	mflr %r0
	std %r27, 2000(%r6)
	std %r28, 2008(%r6)
	std %r29, 2016(%r6)
	std %r30, 2024(%r6)
	std %r31, 2032(%r6)
	std %r0, 2040(%r6)
	addi %r31, %r6, 0
	addi %r30, %r5, 0
	addi %r29, %r3, 0
	li %r28, 66
	rldicr %r27, %r4, 32, 31
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
	li %r7, 544
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	addi %r12, %r27, -2
	cmpldi %cr0, %r12, 0
	beq %cr0, 20f
	addi %r3, %r31, 840
	addi %r4, %r30, 0
	li %r5, 0
	li %r6, 544
	lis %r7, 127
	ori %r7, %r7, 57345
22:
	lbz %r8, 0(%r3)
	rldicr %r9, %r8, 60, 3
	rldicl %r9, %r9, 4, 60
	addi %r12, %r9, -9
	rldicl %r12, %r12, 1, 63
	addi %r11, %r5, -256
	rldicl %r11, %r11, 1, 63
	and %r12, %r12, %r11
	li %r10, 4
	subf %r10, %r9, %r10
	rldicl %r11, %r10, 1, 63
	mulld %r11, %r11, %r7
	add %r10, %r10, %r11
	cmpldi %cr0, %r12, 0
	beq %cr0, 23f
	stw %r10, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, 1
	b 24f
23:
24:
	rldicl %r9, %r8, 60, 4
	addi %r12, %r9, -9
	rldicl %r12, %r12, 1, 63
	addi %r11, %r5, -256
	rldicl %r11, %r11, 1, 63
	and %r12, %r12, %r11
	li %r10, 4
	subf %r10, %r9, %r10
	rldicl %r11, %r10, 1, 63
	mulld %r11, %r11, %r7
	add %r10, %r10, %r11
	cmpldi %cr0, %r12, 0
	beq %cr0, 25f
	stw %r10, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, 1
	b 26f
25:
26:
	addi %r3, %r3, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 22b
	b 21f
20:
	addi %r3, %r31, 840
	addi %r4, %r30, 0
	li %r5, 0
	li %r6, 544
	lis %r7, 127
	ori %r7, %r7, 57345
27:
	lbz %r8, 0(%r3)
	rldicr %r9, %r8, 60, 3
	rldicl %r9, %r9, 4, 60
	addi %r12, %r9, -15
	rldicl %r12, %r12, 1, 63
	addi %r11, %r5, -256
	rldicl %r11, %r11, 1, 63
	and %r12, %r12, %r11
	addi %r9, %r9, -10
	rldicl %r11, %r9, 1, 63
	rldicr %r10, %r11, 3, 60
	add %r9, %r9, %r10
	rldicr %r10, %r11, 1, 62
	add %r9, %r9, %r10
	addi %r9, %r9, -5
	rldicl %r11, %r9, 1, 63
	rldicr %r10, %r11, 2, 61
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	li %r10, 2
	subf %r10, %r9, %r10
	rldicl %r11, %r10, 1, 63
	mulld %r11, %r11, %r7
	add %r10, %r10, %r11
	cmpldi %cr0, %r12, 0
	beq %cr0, 28f
	stw %r10, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, 1
	b 29f
28:
29:
	rldicl %r9, %r8, 60, 4
	addi %r12, %r9, -15
	rldicl %r12, %r12, 1, 63
	addi %r11, %r5, -256
	rldicl %r11, %r11, 1, 63
	and %r12, %r12, %r11
	addi %r9, %r9, -10
	rldicl %r11, %r9, 1, 63
	rldicr %r10, %r11, 3, 60
	add %r9, %r9, %r10
	rldicr %r10, %r11, 1, 62
	add %r9, %r9, %r10
	addi %r9, %r9, -5
	rldicl %r11, %r9, 1, 63
	rldicr %r10, %r11, 2, 61
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	li %r10, 2
	subf %r10, %r9, %r10
	rldicl %r11, %r10, 1, 63
	mulld %r11, %r11, %r7
	add %r10, %r10, %r11
	cmpldi %cr0, %r12, 0
	beq %cr0, 210f
	stw %r10, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, 1
	b 211f
210:
211:
	addi %r3, %r3, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 27b
21:
	rldicl %r3, %r5, 56, 8
	ld %r0, 2040(%r31)
	mtlr %r0
	ld %r27, 2000(%r31)
	ld %r28, 2008(%r31)
	ld %r29, 2016(%r31)
	ld %r30, 2024(%r31)
	ld %r31, 2032(%r31)
	blr
