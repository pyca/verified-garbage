// The functions of `src/x448.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x448_exchange:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	addi %r12, %r1, 0
	std %r3, 40(%r12)
	bl {vg_x448}
	addi %r12, %r1, 0
	ld %r12, 40(%r12)
	li %r11, 0
	lbz %r10, 0(%r12)
	or %r11, %r11, %r10
	lbz %r10, 1(%r12)
	or %r11, %r11, %r10
	lbz %r10, 2(%r12)
	or %r11, %r11, %r10
	lbz %r10, 3(%r12)
	or %r11, %r11, %r10
	lbz %r10, 4(%r12)
	or %r11, %r11, %r10
	lbz %r10, 5(%r12)
	or %r11, %r11, %r10
	lbz %r10, 6(%r12)
	or %r11, %r11, %r10
	lbz %r10, 7(%r12)
	or %r11, %r11, %r10
	lbz %r10, 8(%r12)
	or %r11, %r11, %r10
	lbz %r10, 9(%r12)
	or %r11, %r11, %r10
	lbz %r10, 10(%r12)
	or %r11, %r11, %r10
	lbz %r10, 11(%r12)
	or %r11, %r11, %r10
	lbz %r10, 12(%r12)
	or %r11, %r11, %r10
	lbz %r10, 13(%r12)
	or %r11, %r11, %r10
	lbz %r10, 14(%r12)
	or %r11, %r11, %r10
	lbz %r10, 15(%r12)
	or %r11, %r11, %r10
	lbz %r10, 16(%r12)
	or %r11, %r11, %r10
	lbz %r10, 17(%r12)
	or %r11, %r11, %r10
	lbz %r10, 18(%r12)
	or %r11, %r11, %r10
	lbz %r10, 19(%r12)
	or %r11, %r11, %r10
	lbz %r10, 20(%r12)
	or %r11, %r11, %r10
	lbz %r10, 21(%r12)
	or %r11, %r11, %r10
	lbz %r10, 22(%r12)
	or %r11, %r11, %r10
	lbz %r10, 23(%r12)
	or %r11, %r11, %r10
	lbz %r10, 24(%r12)
	or %r11, %r11, %r10
	lbz %r10, 25(%r12)
	or %r11, %r11, %r10
	lbz %r10, 26(%r12)
	or %r11, %r11, %r10
	lbz %r10, 27(%r12)
	or %r11, %r11, %r10
	lbz %r10, 28(%r12)
	or %r11, %r11, %r10
	lbz %r10, 29(%r12)
	or %r11, %r11, %r10
	lbz %r10, 30(%r12)
	or %r11, %r11, %r10
	lbz %r10, 31(%r12)
	or %r11, %r11, %r10
	lbz %r10, 32(%r12)
	or %r11, %r11, %r10
	lbz %r10, 33(%r12)
	or %r11, %r11, %r10
	lbz %r10, 34(%r12)
	or %r11, %r11, %r10
	lbz %r10, 35(%r12)
	or %r11, %r11, %r10
	lbz %r10, 36(%r12)
	or %r11, %r11, %r10
	lbz %r10, 37(%r12)
	or %r11, %r11, %r10
	lbz %r10, 38(%r12)
	or %r11, %r11, %r10
	lbz %r10, 39(%r12)
	or %r11, %r11, %r10
	lbz %r10, 40(%r12)
	or %r11, %r11, %r10
	lbz %r10, 41(%r12)
	or %r11, %r11, %r10
	lbz %r10, 42(%r12)
	or %r11, %r11, %r10
	lbz %r10, 43(%r12)
	or %r11, %r11, %r10
	lbz %r10, 44(%r12)
	or %r11, %r11, %r10
	lbz %r10, 45(%r12)
	or %r11, %r11, %r10
	lbz %r10, 46(%r12)
	or %r11, %r11, %r10
	lbz %r10, 47(%r12)
	or %r11, %r11, %r10
	lbz %r10, 48(%r12)
	or %r11, %r11, %r10
	lbz %r10, 49(%r12)
	or %r11, %r11, %r10
	lbz %r10, 50(%r12)
	or %r11, %r11, %r10
	lbz %r10, 51(%r12)
	or %r11, %r11, %r10
	lbz %r10, 52(%r12)
	or %r11, %r11, %r10
	lbz %r10, 53(%r12)
	or %r11, %r11, %r10
	lbz %r10, 54(%r12)
	or %r11, %r11, %r10
	lbz %r10, 55(%r12)
	or %r11, %r11, %r10
	addi %r11, %r11, -1
	rldicl %r3, %r11, 1, 63
	li %r10, 1
	xor %r3, %r3, %r10
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	li %r0, 0
	stdu %r1, -48(%r1)
	addi %r12, %r1, 32
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	addi %r1, %r1, 48
	rldicr %r3, %r3, 32, 31
	rldicl %r3, %r3, 32, 32
	li %r4, 0
	li %r5, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	addc %r0, %r0, %r0
	blr

vg_x448_base:
	stdu %r1, -96(%r1)
	mflr %r0
	addi %r12, %r1, 32
	std %r0, 0(%r12)
	li %r7, 5
	std %r7, 8(%r12)
	li %r7, 0
	std %r7, 16(%r12)
	std %r7, 24(%r12)
	std %r7, 32(%r12)
	std %r7, 40(%r12)
	std %r7, 48(%r12)
	std %r7, 56(%r12)
	addi %r6, %r5, 0
	addi %r5, %r12, 8
	bl {vg_x448}
	addi %r12, %r1, 32
	ld %r0, 0(%r12)
	mtlr %r0
	addi %r1, %r1, 96
	li %r0, 0
	stdu %r1, -96(%r1)
	addi %r12, %r1, 32
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	addi %r1, %r1, 96
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	addc %r0, %r0, %r0
	blr
