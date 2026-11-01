// The functions of `src/internal/vg_rc2_encrypt_block.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_encrypt_block:
	ld %r11, 0(%r4)
	rldicr %r6, %r11, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r7, %r11, 32, 31
	rldicl %r7, %r7, 16, 48
	rldicr %r8, %r11, 16, 47
	rldicl %r8, %r8, 16, 48
	rldicl %r9, %r11, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 0(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 2(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 4(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 6(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 8(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 10(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 12(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 14(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 16(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 18(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 20(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 22(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 24(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 26(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 28(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 30(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 32(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 34(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 36(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 38(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r10, %r9, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r11, 0
	addi %r5, %r3, 120
20:
	subf %r0, %r3, %r5
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r5)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r3, %r5
	addi %r5, %r5, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 20b
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 48, 15
	rldicl %r11, %r11, 16, 48
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r10, %r6, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r11, 0
	addi %r5, %r3, 120
21:
	subf %r0, %r3, %r5
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r5)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r3, %r5
	addi %r5, %r5, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 21b
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 48, 15
	rldicl %r11, %r11, 16, 48
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r10, %r7, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r11, 0
	addi %r5, %r3, 120
22:
	subf %r0, %r3, %r5
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r5)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r3, %r5
	addi %r5, %r5, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 22b
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 48, 15
	rldicl %r11, %r11, 16, 48
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r10, %r8, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r11, 0
	addi %r5, %r3, 120
23:
	subf %r0, %r3, %r5
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r5)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r3, %r5
	addi %r5, %r5, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 23b
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 48, 15
	rldicl %r11, %r11, 16, 48
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 40(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 42(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 44(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 46(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 48(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 50(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 52(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 54(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 56(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 58(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 60(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 62(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 64(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 66(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 68(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 70(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 72(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 74(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 76(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 78(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 80(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 82(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 84(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 86(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r10, %r9, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r11, 0
	addi %r5, %r3, 120
24:
	subf %r0, %r3, %r5
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r5)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r3, %r5
	addi %r5, %r5, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 24b
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 48, 15
	rldicl %r11, %r11, 16, 48
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r10, %r6, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r11, 0
	addi %r5, %r3, 120
25:
	subf %r0, %r3, %r5
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r5)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r3, %r5
	addi %r5, %r5, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 25b
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 48, 15
	rldicl %r11, %r11, 16, 48
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r10, %r7, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r11, 0
	addi %r5, %r3, 120
26:
	subf %r0, %r3, %r5
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r5)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r3, %r5
	addi %r5, %r5, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 26b
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 48, 15
	rldicl %r11, %r11, 16, 48
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r10, %r8, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r11, 0
	addi %r5, %r3, 120
27:
	subf %r0, %r3, %r5
	xor %r12, %r10, %r0
	rldicl %r12, %r12, 61, 3
	addi %r12, %r12, -1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 0(%r5)
	and %r12, %r0, %r12
	xor %r0, %r0, %r12
	or %r11, %r11, %r0
	subf %r0, %r3, %r5
	addi %r5, %r5, -8
	cmpldi %cr0, %r0, 0
	bne %cr0, 27b
	rldicr %r12, %r10, 62, 1
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 48, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r12, %r10, 61, 2
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	rldicl %r0, %r11, 32, 0
	xor %r11, %r11, %r0
	and %r11, %r11, %r12
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 48, 15
	rldicl %r11, %r11, 16, 48
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 88(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 90(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 92(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 94(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 96(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 98(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 100(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 102(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 104(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 106(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 108(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 110(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 112(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 114(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 116(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 118(%r3)
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	and %r10, %r9, %r8
	and %r11, %r9, %r7
	xor %r11, %r7, %r11
	lwz %r12, 120(%r3)
	add %r6, %r6, %r12
	add %r6, %r6, %r10
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r6, 1, 62
	rldicl %r6, %r6, 49, 15
	or %r6, %r6, %r0
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	and %r10, %r6, %r9
	and %r11, %r6, %r8
	xor %r11, %r8, %r11
	lwz %r12, 122(%r3)
	add %r7, %r7, %r12
	add %r7, %r7, %r10
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r0, %r7, 2, 61
	rldicl %r7, %r7, 50, 14
	or %r7, %r7, %r0
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	and %r10, %r7, %r6
	and %r11, %r7, %r9
	xor %r11, %r9, %r11
	lwz %r12, 124(%r3)
	add %r8, %r8, %r12
	add %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r0, %r8, 3, 60
	rldicl %r8, %r8, 51, 13
	or %r8, %r8, %r0
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	and %r10, %r8, %r7
	and %r11, %r8, %r6
	xor %r11, %r6, %r11
	lwz %r12, 124(%r3)
	rlwinm %r12, %r12, 16, 16, 31
	add %r9, %r9, %r12
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r0, %r9, 5, 58
	rldicl %r9, %r9, 53, 11
	or %r9, %r9, %r0
	rldicr %r9, %r9, 48, 15
	rldicl %r9, %r9, 16, 48
	rldicr %r11, %r7, 16, 47
	or %r11, %r11, %r6
	rldicr %r12, %r8, 32, 31
	or %r11, %r11, %r12
	rldicr %r12, %r9, 48, 15
	or %r11, %r11, %r12
	std %r11, 0(%r4)
	blr
