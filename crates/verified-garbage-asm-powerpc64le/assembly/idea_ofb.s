// The functions of `src/idea_ofb.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_idea_ofb:
	stdu %r1, -96(%r1)
	addi %r7, %r1, 32
	mflr %r0
	std %r0, 32(%r7)
	std %r29, 8(%r7)
	std %r30, 16(%r7)
	std %r31, 24(%r7)
	or %r29, %r4, %r4
	or %r30, %r6, %r6
	or %r31, %r4, %r4
	or %r6, %r5, %r5
	or %r5, %r7, %r7
	lwz %r8, 0(%r31)
	stw %r8, 40(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 44(%r5)
	or %r31, %r6, %r6
	cmpldi %cr0, %r30, 0
	beq %cr0, 20f
22:
	lwz %r8, 40(%r5)
	stw %r8, 0(%r5)
	lwz %r8, 44(%r5)
	stw %r8, 4(%r5)
	li %r0, 0
	ori %r0, %r0, 65535
	addi %r4, %r5, 0
	lbz %r6, 0(%r4)
	rldicr %r6, %r6, 8, 55
	lbz %r11, 1(%r4)
	or %r6, %r6, %r11
	lbz %r7, 2(%r4)
	rldicr %r7, %r7, 8, 55
	lbz %r11, 3(%r4)
	or %r7, %r7, %r11
	lbz %r8, 4(%r4)
	rldicr %r8, %r8, 8, 55
	lbz %r11, 5(%r4)
	or %r8, %r8, %r11
	lbz %r9, 6(%r4)
	rldicr %r9, %r9, 8, 55
	lbz %r11, 7(%r4)
	or %r9, %r9, %r11
	or %r11, %r6, %r6
	lwz %r12, 0(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r6, %r12, %r12
	or %r11, %r9, %r9
	lwz %r12, 6(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r9, %r12, %r12
	lwz %r12, 2(%r3)
	add %r7, %r7, %r12
	and %r7, %r7, %r0
	lwz %r12, 4(%r3)
	add %r8, %r8, %r12
	and %r8, %r8, %r0
	xor %r11, %r6, %r8
	lwz %r12, 8(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r10, %r12, %r12
	xor %r11, %r7, %r9
	add %r11, %r11, %r10
	lwz %r12, 10(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	add %r10, %r10, %r12
	and %r10, %r10, %r0
	xor %r6, %r6, %r12
	xor %r8, %r8, %r12
	xor %r7, %r7, %r10
	xor %r9, %r9, %r10
	or %r11, %r7, %r7
	or %r7, %r8, %r8
	or %r8, %r11, %r11
	or %r11, %r6, %r6
	lwz %r12, 12(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r6, %r12, %r12
	or %r11, %r9, %r9
	lwz %r12, 18(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r9, %r12, %r12
	lwz %r12, 14(%r3)
	add %r7, %r7, %r12
	and %r7, %r7, %r0
	lwz %r12, 16(%r3)
	add %r8, %r8, %r12
	and %r8, %r8, %r0
	xor %r11, %r6, %r8
	lwz %r12, 20(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r10, %r12, %r12
	xor %r11, %r7, %r9
	add %r11, %r11, %r10
	lwz %r12, 22(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	add %r10, %r10, %r12
	and %r10, %r10, %r0
	xor %r6, %r6, %r12
	xor %r8, %r8, %r12
	xor %r7, %r7, %r10
	xor %r9, %r9, %r10
	or %r11, %r7, %r7
	or %r7, %r8, %r8
	or %r8, %r11, %r11
	or %r11, %r6, %r6
	lwz %r12, 24(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r6, %r12, %r12
	or %r11, %r9, %r9
	lwz %r12, 30(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r9, %r12, %r12
	lwz %r12, 26(%r3)
	add %r7, %r7, %r12
	and %r7, %r7, %r0
	lwz %r12, 28(%r3)
	add %r8, %r8, %r12
	and %r8, %r8, %r0
	xor %r11, %r6, %r8
	lwz %r12, 32(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r10, %r12, %r12
	xor %r11, %r7, %r9
	add %r11, %r11, %r10
	lwz %r12, 34(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	add %r10, %r10, %r12
	and %r10, %r10, %r0
	xor %r6, %r6, %r12
	xor %r8, %r8, %r12
	xor %r7, %r7, %r10
	xor %r9, %r9, %r10
	or %r11, %r7, %r7
	or %r7, %r8, %r8
	or %r8, %r11, %r11
	or %r11, %r6, %r6
	lwz %r12, 36(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r6, %r12, %r12
	or %r11, %r9, %r9
	lwz %r12, 42(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r9, %r12, %r12
	lwz %r12, 38(%r3)
	add %r7, %r7, %r12
	and %r7, %r7, %r0
	lwz %r12, 40(%r3)
	add %r8, %r8, %r12
	and %r8, %r8, %r0
	xor %r11, %r6, %r8
	lwz %r12, 44(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r10, %r12, %r12
	xor %r11, %r7, %r9
	add %r11, %r11, %r10
	lwz %r12, 46(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	add %r10, %r10, %r12
	and %r10, %r10, %r0
	xor %r6, %r6, %r12
	xor %r8, %r8, %r12
	xor %r7, %r7, %r10
	xor %r9, %r9, %r10
	or %r11, %r7, %r7
	or %r7, %r8, %r8
	or %r8, %r11, %r11
	or %r11, %r6, %r6
	lwz %r12, 48(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r6, %r12, %r12
	or %r11, %r9, %r9
	lwz %r12, 54(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r9, %r12, %r12
	lwz %r12, 50(%r3)
	add %r7, %r7, %r12
	and %r7, %r7, %r0
	lwz %r12, 52(%r3)
	add %r8, %r8, %r12
	and %r8, %r8, %r0
	xor %r11, %r6, %r8
	lwz %r12, 56(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r10, %r12, %r12
	xor %r11, %r7, %r9
	add %r11, %r11, %r10
	lwz %r12, 58(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	add %r10, %r10, %r12
	and %r10, %r10, %r0
	xor %r6, %r6, %r12
	xor %r8, %r8, %r12
	xor %r7, %r7, %r10
	xor %r9, %r9, %r10
	or %r11, %r7, %r7
	or %r7, %r8, %r8
	or %r8, %r11, %r11
	or %r11, %r6, %r6
	lwz %r12, 60(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r6, %r12, %r12
	or %r11, %r9, %r9
	lwz %r12, 66(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r9, %r12, %r12
	lwz %r12, 62(%r3)
	add %r7, %r7, %r12
	and %r7, %r7, %r0
	lwz %r12, 64(%r3)
	add %r8, %r8, %r12
	and %r8, %r8, %r0
	xor %r11, %r6, %r8
	lwz %r12, 68(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r10, %r12, %r12
	xor %r11, %r7, %r9
	add %r11, %r11, %r10
	lwz %r12, 70(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	add %r10, %r10, %r12
	and %r10, %r10, %r0
	xor %r6, %r6, %r12
	xor %r8, %r8, %r12
	xor %r7, %r7, %r10
	xor %r9, %r9, %r10
	or %r11, %r7, %r7
	or %r7, %r8, %r8
	or %r8, %r11, %r11
	or %r11, %r6, %r6
	lwz %r12, 72(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r6, %r12, %r12
	or %r11, %r9, %r9
	lwz %r12, 78(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r9, %r12, %r12
	lwz %r12, 74(%r3)
	add %r7, %r7, %r12
	and %r7, %r7, %r0
	lwz %r12, 76(%r3)
	add %r8, %r8, %r12
	and %r8, %r8, %r0
	xor %r11, %r6, %r8
	lwz %r12, 80(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r10, %r12, %r12
	xor %r11, %r7, %r9
	add %r11, %r11, %r10
	lwz %r12, 82(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	add %r10, %r10, %r12
	and %r10, %r10, %r0
	xor %r6, %r6, %r12
	xor %r8, %r8, %r12
	xor %r7, %r7, %r10
	xor %r9, %r9, %r10
	or %r11, %r7, %r7
	or %r7, %r8, %r8
	or %r8, %r11, %r11
	or %r11, %r6, %r6
	lwz %r12, 84(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r6, %r12, %r12
	or %r11, %r9, %r9
	lwz %r12, 90(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r9, %r12, %r12
	lwz %r12, 86(%r3)
	add %r7, %r7, %r12
	and %r7, %r7, %r0
	lwz %r12, 88(%r3)
	add %r8, %r8, %r12
	and %r8, %r8, %r0
	xor %r11, %r6, %r8
	lwz %r12, 92(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r10, %r12, %r12
	xor %r11, %r7, %r9
	add %r11, %r11, %r10
	lwz %r12, 94(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	add %r10, %r10, %r12
	and %r10, %r10, %r0
	xor %r6, %r6, %r12
	xor %r8, %r8, %r12
	xor %r7, %r7, %r10
	xor %r9, %r9, %r10
	or %r11, %r7, %r7
	or %r7, %r8, %r8
	or %r8, %r11, %r11
	or %r11, %r6, %r6
	lwz %r12, 96(%r3)
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r6, %r12, %r12
	or %r11, %r9, %r9
	lwz %r12, 100(%r3)
	rldicl %r12, %r12, 48, 16
	addi %r11, %r11, -1
	and %r11, %r11, %r0
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	and %r12, %r12, %r0
	addi %r12, %r12, 1
	mulld %r11, %r11, %r12
	and %r12, %r11, %r0
	rldicl %r11, %r11, 48, 16
	subf %r12, %r11, %r12
	rldicl %r11, %r12, 1, 63
	add %r12, %r12, %r11
	rldicr %r11, %r11, 16, 47
	add %r12, %r12, %r11
	and %r12, %r12, %r0
	or %r9, %r12, %r12
	lwz %r12, 98(%r3)
	add %r8, %r8, %r12
	and %r8, %r8, %r0
	lwz %r12, 100(%r3)
	add %r7, %r7, %r12
	and %r7, %r7, %r0
	stb %r6, 1(%r4)
	rldicl %r11, %r6, 56, 8
	stb %r11, 0(%r4)
	stb %r8, 3(%r4)
	rldicl %r11, %r8, 56, 8
	stb %r11, 2(%r4)
	stb %r7, 5(%r4)
	rldicl %r11, %r7, 56, 8
	stb %r11, 4(%r4)
	stb %r9, 7(%r4)
	rldicl %r11, %r9, 56, 8
	stb %r11, 6(%r4)
	lwz %r8, 0(%r5)
	stw %r8, 40(%r5)
	lwz %r8, 4(%r5)
	stw %r8, 44(%r5)
	lwz %r8, 0(%r31)
	lwz %r9, 0(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 4(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	addi %r31, %r31, 8
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 22b
	b 21f
20:
21:
	or %r31, %r29, %r29
	lwz %r8, 40(%r5)
	stw %r8, 0(%r31)
	lwz %r8, 44(%r5)
	stw %r8, 4(%r31)
	ld %r29, 8(%r5)
	ld %r30, 16(%r5)
	ld %r31, 24(%r5)
	ld %r0, 32(%r5)
	mtlr %r0
	addi %r12, %r1, 32
	li %r11, 0
	std %r11, 0(%r12)
	std %r11, 8(%r12)
	std %r11, 16(%r12)
	std %r11, 24(%r12)
	std %r11, 32(%r12)
	std %r11, 40(%r12)
	std %r11, 48(%r12)
	std %r11, 56(%r12)
	addi %r1, %r1, 96
	blr
