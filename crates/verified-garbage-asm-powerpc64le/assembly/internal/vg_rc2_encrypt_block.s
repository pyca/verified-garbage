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
	li %r0, 7
	xor %r12, %r10, %r0
	rldicr %r12, %r12, 56, 7
	addi %r11, %r10, 1
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 56, 7
	rldicl %r11, %r11, 56, 8
	or %r12, %r12, %r11
	mtvsrd 32, %r12
	rldicr %r12, %r10, 58, 5
	rldicl %r12, %r12, 1, 63
	li %r0, 0
	subf %r12, %r12, %r0
	mtvsrd 33, %r12
	rldicr %r12, %r10, 57, 6
	rldicl %r12, %r12, 1, 63
	li %r0, 0
	subf %r12, %r12, %r0
	mtvsrd 34, %r12
	li %r0, 0
	li %r12, 16
	or %r5, %r3, %r3
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v6, %v4, %v5, %v0
	addi %r5, %r5, 32
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v7, %v4, %v5, %v0
	addi %r5, %r5, 32
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v8, %v4, %v5, %v0
	addi %r5, %r5, 32
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v9, %v4, %v5, %v0
	addi %r5, %r5, 32
	vsel %v6, %v6, %v7, %v1
	vsel %v8, %v8, %v9, %v1
	vsel %v6, %v6, %v8, %v2
	mfvsrd %r11, 38
	rldicr %r12, %r11, 8, 55
	rldicl %r12, %r12, 8, 56
	rldicl %r11, %r11, 8, 56
	rldicr %r12, %r12, 8, 55
	or %r11, %r11, %r12
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r10, %r6, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r0, 7
	xor %r12, %r10, %r0
	rldicr %r12, %r12, 56, 7
	addi %r11, %r10, 1
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 56, 7
	rldicl %r11, %r11, 56, 8
	or %r12, %r12, %r11
	mtvsrd 32, %r12
	rldicr %r12, %r10, 58, 5
	rldicl %r12, %r12, 1, 63
	li %r0, 0
	subf %r12, %r12, %r0
	mtvsrd 33, %r12
	rldicr %r12, %r10, 57, 6
	rldicl %r12, %r12, 1, 63
	li %r0, 0
	subf %r12, %r12, %r0
	mtvsrd 34, %r12
	li %r0, 0
	li %r12, 16
	or %r5, %r3, %r3
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v6, %v4, %v5, %v0
	addi %r5, %r5, 32
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v7, %v4, %v5, %v0
	addi %r5, %r5, 32
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v8, %v4, %v5, %v0
	addi %r5, %r5, 32
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v9, %v4, %v5, %v0
	addi %r5, %r5, 32
	vsel %v6, %v6, %v7, %v1
	vsel %v8, %v8, %v9, %v1
	vsel %v6, %v6, %v8, %v2
	mfvsrd %r11, 38
	rldicr %r12, %r11, 8, 55
	rldicl %r12, %r12, 8, 56
	rldicl %r11, %r11, 8, 56
	rldicr %r12, %r12, 8, 55
	or %r11, %r11, %r12
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r10, %r7, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r0, 7
	xor %r12, %r10, %r0
	rldicr %r12, %r12, 56, 7
	addi %r11, %r10, 1
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 56, 7
	rldicl %r11, %r11, 56, 8
	or %r12, %r12, %r11
	mtvsrd 32, %r12
	rldicr %r12, %r10, 58, 5
	rldicl %r12, %r12, 1, 63
	li %r0, 0
	subf %r12, %r12, %r0
	mtvsrd 33, %r12
	rldicr %r12, %r10, 57, 6
	rldicl %r12, %r12, 1, 63
	li %r0, 0
	subf %r12, %r12, %r0
	mtvsrd 34, %r12
	li %r0, 0
	li %r12, 16
	or %r5, %r3, %r3
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v6, %v4, %v5, %v0
	addi %r5, %r5, 32
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v7, %v4, %v5, %v0
	addi %r5, %r5, 32
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v8, %v4, %v5, %v0
	addi %r5, %r5, 32
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v9, %v4, %v5, %v0
	addi %r5, %r5, 32
	vsel %v6, %v6, %v7, %v1
	vsel %v8, %v8, %v9, %v1
	vsel %v6, %v6, %v8, %v2
	mfvsrd %r11, 38
	rldicr %r12, %r11, 8, 55
	rldicl %r12, %r12, 8, 56
	rldicl %r11, %r11, 8, 56
	rldicr %r12, %r12, 8, 55
	or %r11, %r11, %r12
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r10, %r8, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r0, 7
	xor %r12, %r10, %r0
	rldicr %r12, %r12, 56, 7
	addi %r11, %r10, 1
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 56, 7
	rldicl %r11, %r11, 56, 8
	or %r12, %r12, %r11
	mtvsrd 32, %r12
	rldicr %r12, %r10, 58, 5
	rldicl %r12, %r12, 1, 63
	li %r0, 0
	subf %r12, %r12, %r0
	mtvsrd 33, %r12
	rldicr %r12, %r10, 57, 6
	rldicl %r12, %r12, 1, 63
	li %r0, 0
	subf %r12, %r12, %r0
	mtvsrd 34, %r12
	li %r0, 0
	li %r12, 16
	or %r5, %r3, %r3
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v6, %v4, %v5, %v0
	addi %r5, %r5, 32
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v7, %v4, %v5, %v0
	addi %r5, %r5, 32
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v8, %v4, %v5, %v0
	addi %r5, %r5, 32
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v9, %v4, %v5, %v0
	addi %r5, %r5, 32
	vsel %v6, %v6, %v7, %v1
	vsel %v8, %v8, %v9, %v1
	vsel %v6, %v6, %v8, %v2
	mfvsrd %r11, 38
	rldicr %r12, %r11, 8, 55
	rldicl %r12, %r12, 8, 56
	rldicl %r11, %r11, 8, 56
	rldicr %r12, %r12, 8, 55
	or %r11, %r11, %r12
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
	li %r0, 7
	xor %r12, %r10, %r0
	rldicr %r12, %r12, 56, 7
	addi %r11, %r10, 1
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 56, 7
	rldicl %r11, %r11, 56, 8
	or %r12, %r12, %r11
	mtvsrd 32, %r12
	rldicr %r12, %r10, 58, 5
	rldicl %r12, %r12, 1, 63
	li %r0, 0
	subf %r12, %r12, %r0
	mtvsrd 33, %r12
	rldicr %r12, %r10, 57, 6
	rldicl %r12, %r12, 1, 63
	li %r0, 0
	subf %r12, %r12, %r0
	mtvsrd 34, %r12
	li %r0, 0
	li %r12, 16
	or %r5, %r3, %r3
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v6, %v4, %v5, %v0
	addi %r5, %r5, 32
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v7, %v4, %v5, %v0
	addi %r5, %r5, 32
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v8, %v4, %v5, %v0
	addi %r5, %r5, 32
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v9, %v4, %v5, %v0
	addi %r5, %r5, 32
	vsel %v6, %v6, %v7, %v1
	vsel %v8, %v8, %v9, %v1
	vsel %v6, %v6, %v8, %v2
	mfvsrd %r11, 38
	rldicr %r12, %r11, 8, 55
	rldicl %r12, %r12, 8, 56
	rldicl %r11, %r11, 8, 56
	rldicr %r12, %r12, 8, 55
	or %r11, %r11, %r12
	add %r6, %r6, %r11
	rldicr %r6, %r6, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r10, %r6, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r0, 7
	xor %r12, %r10, %r0
	rldicr %r12, %r12, 56, 7
	addi %r11, %r10, 1
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 56, 7
	rldicl %r11, %r11, 56, 8
	or %r12, %r12, %r11
	mtvsrd 32, %r12
	rldicr %r12, %r10, 58, 5
	rldicl %r12, %r12, 1, 63
	li %r0, 0
	subf %r12, %r12, %r0
	mtvsrd 33, %r12
	rldicr %r12, %r10, 57, 6
	rldicl %r12, %r12, 1, 63
	li %r0, 0
	subf %r12, %r12, %r0
	mtvsrd 34, %r12
	li %r0, 0
	li %r12, 16
	or %r5, %r3, %r3
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v6, %v4, %v5, %v0
	addi %r5, %r5, 32
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v7, %v4, %v5, %v0
	addi %r5, %r5, 32
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v8, %v4, %v5, %v0
	addi %r5, %r5, 32
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v9, %v4, %v5, %v0
	addi %r5, %r5, 32
	vsel %v6, %v6, %v7, %v1
	vsel %v8, %v8, %v9, %v1
	vsel %v6, %v6, %v8, %v2
	mfvsrd %r11, 38
	rldicr %r12, %r11, 8, 55
	rldicl %r12, %r12, 8, 56
	rldicl %r11, %r11, 8, 56
	rldicr %r12, %r12, 8, 55
	or %r11, %r11, %r12
	add %r7, %r7, %r11
	rldicr %r7, %r7, 48, 15
	rldicl %r7, %r7, 16, 48
	rldicr %r10, %r7, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r0, 7
	xor %r12, %r10, %r0
	rldicr %r12, %r12, 56, 7
	addi %r11, %r10, 1
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 56, 7
	rldicl %r11, %r11, 56, 8
	or %r12, %r12, %r11
	mtvsrd 32, %r12
	rldicr %r12, %r10, 58, 5
	rldicl %r12, %r12, 1, 63
	li %r0, 0
	subf %r12, %r12, %r0
	mtvsrd 33, %r12
	rldicr %r12, %r10, 57, 6
	rldicl %r12, %r12, 1, 63
	li %r0, 0
	subf %r12, %r12, %r0
	mtvsrd 34, %r12
	li %r0, 0
	li %r12, 16
	or %r5, %r3, %r3
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v6, %v4, %v5, %v0
	addi %r5, %r5, 32
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v7, %v4, %v5, %v0
	addi %r5, %r5, 32
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v8, %v4, %v5, %v0
	addi %r5, %r5, 32
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v9, %v4, %v5, %v0
	addi %r5, %r5, 32
	vsel %v6, %v6, %v7, %v1
	vsel %v8, %v8, %v9, %v1
	vsel %v6, %v6, %v8, %v2
	mfvsrd %r11, 38
	rldicr %r12, %r11, 8, 55
	rldicl %r12, %r12, 8, 56
	rldicl %r11, %r11, 8, 56
	rldicr %r12, %r12, 8, 55
	or %r11, %r11, %r12
	add %r8, %r8, %r11
	rldicr %r8, %r8, 48, 15
	rldicl %r8, %r8, 16, 48
	rldicr %r10, %r8, 58, 5
	rldicl %r10, %r10, 7, 57
	li %r0, 7
	xor %r12, %r10, %r0
	rldicr %r12, %r12, 56, 7
	addi %r11, %r10, 1
	xor %r11, %r11, %r0
	rldicr %r11, %r11, 56, 7
	rldicl %r11, %r11, 56, 8
	or %r12, %r12, %r11
	mtvsrd 32, %r12
	rldicr %r12, %r10, 58, 5
	rldicl %r12, %r12, 1, 63
	li %r0, 0
	subf %r12, %r12, %r0
	mtvsrd 33, %r12
	rldicr %r12, %r10, 57, 6
	rldicl %r12, %r12, 1, 63
	li %r0, 0
	subf %r12, %r12, %r0
	mtvsrd 34, %r12
	li %r0, 0
	li %r12, 16
	or %r5, %r3, %r3
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v6, %v4, %v5, %v0
	addi %r5, %r5, 32
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v7, %v4, %v5, %v0
	addi %r5, %r5, 32
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v8, %v4, %v5, %v0
	addi %r5, %r5, 32
	lxvd2x 36, %r5, %r0
	lxvd2x 37, %r5, %r12
	vperm %v9, %v4, %v5, %v0
	addi %r5, %r5, 32
	vsel %v6, %v6, %v7, %v1
	vsel %v8, %v8, %v9, %v1
	vsel %v6, %v6, %v8, %v2
	mfvsrd %r11, 38
	rldicr %r12, %r11, 8, 55
	rldicl %r12, %r12, 8, 56
	rldicl %r11, %r11, 8, 56
	rldicr %r12, %r12, 8, 55
	or %r11, %r11, %r12
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
