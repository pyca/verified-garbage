// The functions of `src/internal/vg_mldsa_expand_mask_poly.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_expand_mask_poly:
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
	li %r7, 640
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	lis %r12, 2
	subf %r12, %r12, %r27
	cmpldi %cr0, %r12, 0
	beq %cr0, 20f
	addi %r10, %r31, 840
	addi %r11, %r30, 0
	lis %r7, 127
	ori %r7, %r7, 57345
	lis %r4, 8
	li %r12, 128
22:
	li %r8, 0
	lbz %r9, 0(%r10)
	add %r8, %r8, %r9
	lbz %r9, 1(%r10)
	rldicr %r9, %r9, 8, 55
	add %r8, %r8, %r9
	lbz %r9, 2(%r10)
	rldicr %r9, %r9, 16, 47
	add %r8, %r8, %r9
	rldicr %r9, %r8, 44, 19
	rldicl %r9, %r9, 20, 44
	rldicl %r8, %r8, 44, 20
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 0(%r11)
	lbz %r9, 3(%r10)
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	lbz %r9, 4(%r10)
	rldicr %r9, %r9, 12, 51
	add %r8, %r8, %r9
	rldicr %r9, %r8, 44, 19
	rldicl %r9, %r9, 20, 44
	rldicl %r8, %r8, 44, 20
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 4(%r11)
	addi %r10, %r10, 5
	addi %r11, %r11, 8
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 22b
	b 21f
20:
	addi %r10, %r31, 840
	addi %r11, %r30, 0
	lis %r7, 127
	ori %r7, %r7, 57345
	lis %r4, 2
	li %r12, 64
23:
	li %r8, 0
	lbz %r9, 0(%r10)
	add %r8, %r8, %r9
	lbz %r9, 1(%r10)
	rldicr %r9, %r9, 8, 55
	add %r8, %r8, %r9
	lbz %r9, 2(%r10)
	rldicr %r9, %r9, 16, 47
	add %r8, %r8, %r9
	rldicr %r9, %r8, 46, 17
	rldicl %r9, %r9, 18, 46
	rldicl %r8, %r8, 46, 18
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 0(%r11)
	lbz %r9, 3(%r10)
	rldicr %r9, %r9, 6, 57
	add %r8, %r8, %r9
	lbz %r9, 4(%r10)
	rldicr %r9, %r9, 14, 49
	add %r8, %r8, %r9
	rldicr %r9, %r8, 46, 17
	rldicl %r9, %r9, 18, 46
	rldicl %r8, %r8, 46, 18
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 4(%r11)
	lbz %r9, 5(%r10)
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	lbz %r9, 6(%r10)
	rldicr %r9, %r9, 12, 51
	add %r8, %r8, %r9
	rldicr %r9, %r8, 46, 17
	rldicl %r9, %r9, 18, 46
	rldicl %r8, %r8, 46, 18
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 8(%r11)
	lbz %r9, 7(%r10)
	rldicr %r9, %r9, 2, 61
	add %r8, %r8, %r9
	lbz %r9, 8(%r10)
	rldicr %r9, %r9, 10, 53
	add %r8, %r8, %r9
	rldicr %r9, %r8, 46, 17
	rldicl %r9, %r9, 18, 46
	rldicl %r8, %r8, 46, 18
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 12(%r11)
	addi %r10, %r10, 9
	addi %r11, %r11, 16
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 23b
21:
	ld %r0, 2040(%r31)
	mtlr %r0
	ld %r27, 2000(%r31)
	ld %r28, 2008(%r31)
	ld %r29, 2016(%r31)
	ld %r30, 2024(%r31)
	ld %r31, 2032(%r31)
	blr
