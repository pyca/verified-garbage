// The functions of `src/internal/vg_rsa_inv_batch.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_inv_batch:
	addi %r11, %r10, 0
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 8
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	addi %r10, %r11, 0
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
20:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 20b
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	rldicr %r8, %r8, 3, 60
	add %r6, %r6, %r8
	li %r0, 0
	std %r0, 0(%r6)
	li %r4, 2
	mulld %r4, %r4, %r30
	add %r4, %r4, %r31
	addi %r4, %r4, 160
	ld %r5, 0(%r4)
	addi %r6, %r5, 0
	mulld %r3, %r5, %r6
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r6, %r6, %r3
	mulld %r3, %r5, %r6
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r6, %r6, %r3
	mulld %r3, %r5, %r6
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r6, %r6, %r3
	mulld %r3, %r5, %r6
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r6, %r6, %r3
	mulld %r3, %r5, %r6
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r6, %r6, %r3
	li %r3, 0
	subf %r12, %r6, %r3
	li %r4, 14
	mulld %r4, %r4, %r30
	add %r4, %r4, %r31
	addi %r4, %r4, 160
	std %r12, 40(%r4)
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
21:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21b
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	ld %r11, 0(%r5)
	li %r0, 1
	and %r11, %r11, %r0
	xor %r11, %r11, %r0
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	li %r9, 0
22:
	ld %r0, 0(%r7)
	mulld %r3, %r11, %r0
	mulhdu %r0, %r11, %r0
	ld %r12, 0(%r6)
	addc %r3, %r3, %r12
	addze %r0, %r0
	addc %r3, %r3, %r9
	addze %r9, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 22b
	std %r9, 0(%r5)
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	li %r0, 0
23:
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 23b
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	li %r0, 0
24:
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 24b
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	std %r0, 0(%r5)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	std %r0, 0(%r5)
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	add %r3, %r8, %r8
	add %r3, %r3, %r8
	addi %r3, %r3, 2
	rldicr %r3, %r3, 15, 48
	add %r10, %r10, %r3
25:
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	ld %r4, 0(%r5)
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	ld %r5, 0(%r5)
	li %r3, 14
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r3, 0(%r3)
	li %r6, 1
	li %r7, 0
	li %r8, 0
	li %r9, 1
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	li %r4, 14
	mulld %r4, %r4, %r30
	add %r4, %r4, %r31
	addi %r4, %r4, 160
	std %r3, 0(%r4)
	std %r6, 8(%r4)
	std %r7, 16(%r4)
	std %r8, 24(%r4)
	std %r9, 32(%r4)
	li %r3, 11
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	std %r14, 0(%r3)
	std %r15, 8(%r3)
	std %r16, 16(%r3)
	std %r17, 24(%r3)
	std %r18, 32(%r3)
	std %r19, 40(%r3)
	li %r3, 12
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	std %r20, 0(%r3)
	std %r21, 8(%r3)
	std %r22, 16(%r3)
	std %r23, 24(%r3)
	std %r24, 32(%r3)
	std %r25, 40(%r3)
	li %r3, 13
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	std %r26, 0(%r3)
	std %r27, 8(%r3)
	std %r28, 16(%r3)
	li %r14, 14
	mulld %r14, %r14, %r30
	add %r14, %r14, %r31
	addi %r14, %r14, 160
	ld %r14, 8(%r14)
	li %r15, 14
	mulld %r15, %r15, %r30
	add %r15, %r15, %r31
	addi %r15, %r15, 160
	ld %r15, 16(%r15)
	li %r16, 14
	mulld %r16, %r16, %r30
	add %r16, %r16, %r31
	addi %r16, %r16, 160
	ld %r16, 24(%r16)
	li %r17, 14
	mulld %r17, %r17, %r30
	add %r17, %r17, %r31
	addi %r17, %r17, 160
	ld %r17, 32(%r17)
	li %r0, 0
	rldicl %r18, %r14, 1, 63
	subf %r18, %r18, %r0
	rldicl %r19, %r15, 1, 63
	subf %r19, %r19, %r0
	rldicl %r20, %r16, 1, 63
	subf %r20, %r20, %r0
	rldicl %r21, %r17, 1, 63
	subf %r21, %r21, %r0
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 5
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r22, 0
	li %r23, 0
	li %r24, 0
	li %r25, 0
	ld %r26, 0(%r5)
	ld %r27, 0(%r6)
	mulld %r3, %r14, %r26
	addc %r22, %r22, %r3
	mulhdu %r3, %r14, %r26
	adde %r23, %r23, %r3
	and %r3, %r18, %r26
	subf %r23, %r3, %r23
	mulld %r3, %r15, %r27
	addc %r22, %r22, %r3
	mulhdu %r3, %r15, %r27
	adde %r23, %r23, %r3
	and %r3, %r19, %r27
	subf %r23, %r3, %r23
	mulld %r3, %r16, %r26
	addc %r24, %r24, %r3
	mulhdu %r3, %r16, %r26
	adde %r25, %r25, %r3
	and %r3, %r20, %r26
	subf %r25, %r3, %r25
	mulld %r3, %r17, %r27
	addc %r24, %r24, %r3
	mulhdu %r3, %r17, %r27
	adde %r25, %r25, %r3
	and %r3, %r21, %r27
	subf %r25, %r3, %r25
	rldicl %r28, %r22, 5, 59
	rldicl %r12, %r24, 5, 59
	addi %r22, %r23, 0
	rldicl %r0, %r23, 1, 63
	li %r23, 0
	subf %r23, %r0, %r23
	addi %r24, %r25, 0
	rldicl %r0, %r25, 1, 63
	li %r25, 0
	subf %r25, %r0, %r25
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
26:
	ld %r26, 8(%r5)
	ld %r27, 8(%r6)
	mulld %r3, %r14, %r26
	addc %r22, %r22, %r3
	mulhdu %r3, %r14, %r26
	adde %r23, %r23, %r3
	and %r3, %r18, %r26
	subf %r23, %r3, %r23
	mulld %r3, %r15, %r27
	addc %r22, %r22, %r3
	mulhdu %r3, %r15, %r27
	adde %r23, %r23, %r3
	and %r3, %r19, %r27
	subf %r23, %r3, %r23
	mulld %r3, %r16, %r26
	addc %r24, %r24, %r3
	mulhdu %r3, %r16, %r26
	adde %r25, %r25, %r3
	and %r3, %r20, %r26
	subf %r25, %r3, %r25
	mulld %r3, %r17, %r27
	addc %r24, %r24, %r3
	mulhdu %r3, %r17, %r27
	adde %r25, %r25, %r3
	and %r3, %r21, %r27
	subf %r25, %r3, %r25
	rldicr %r3, %r22, 5, 58
	add %r3, %r3, %r28
	std %r3, 0(%r5)
	rldicl %r28, %r22, 5, 59
	rldicr %r3, %r24, 5, 58
	add %r3, %r3, %r12
	std %r3, 0(%r6)
	rldicl %r12, %r24, 5, 59
	addi %r22, %r23, 0
	rldicl %r0, %r23, 1, 63
	li %r23, 0
	subf %r23, %r0, %r23
	addi %r24, %r25, 0
	rldicl %r0, %r25, 1, 63
	li %r25, 0
	subf %r25, %r0, %r25
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 26b
	rldicl %r0, %r28, 60, 4
	rldicr %r0, %r0, 5, 58
	subf %r0, %r0, %r28
	std %r0, 0(%r5)
	rldicl %r0, %r12, 60, 4
	rldicr %r0, %r0, 5, 58
	subf %r0, %r0, %r12
	std %r0, 0(%r6)
	li %r14, 14
	mulld %r14, %r14, %r30
	add %r14, %r14, %r31
	addi %r14, %r14, 160
	ld %r14, 8(%r14)
	li %r15, 14
	mulld %r15, %r15, %r30
	add %r15, %r15, %r31
	addi %r15, %r15, 160
	ld %r15, 16(%r15)
	li %r16, 14
	mulld %r16, %r16, %r30
	add %r16, %r16, %r31
	addi %r16, %r16, 160
	ld %r16, 24(%r16)
	li %r17, 14
	mulld %r17, %r17, %r30
	add %r17, %r17, %r31
	addi %r17, %r17, 160
	ld %r17, 32(%r17)
	li %r0, 0
	rldicl %r18, %r14, 1, 63
	subf %r18, %r18, %r0
	rldicl %r19, %r15, 1, 63
	subf %r19, %r19, %r0
	rldicl %r20, %r16, 1, 63
	subf %r20, %r20, %r0
	rldicl %r21, %r17, 1, 63
	subf %r21, %r21, %r0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 7
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r22, 0
	li %r23, 0
	li %r24, 0
	li %r25, 0
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r4, 14
	mulld %r4, %r4, %r30
	add %r4, %r4, %r31
	addi %r4, %r4, 160
	ld %r4, 40(%r4)
	li %r9, 0
	li %r11, 0
	ld %r26, 0(%r5)
	ld %r27, 0(%r6)
	mulld %r3, %r14, %r26
	addc %r22, %r22, %r3
	mulhdu %r3, %r14, %r26
	adde %r23, %r23, %r3
	and %r3, %r18, %r26
	subf %r23, %r3, %r23
	mulld %r3, %r15, %r27
	addc %r22, %r22, %r3
	mulhdu %r3, %r15, %r27
	adde %r23, %r23, %r3
	and %r3, %r19, %r27
	subf %r23, %r3, %r23
	mulld %r3, %r16, %r26
	addc %r24, %r24, %r3
	mulhdu %r3, %r16, %r26
	adde %r25, %r25, %r3
	and %r3, %r20, %r26
	subf %r25, %r3, %r25
	mulld %r3, %r17, %r27
	addc %r24, %r24, %r3
	mulhdu %r3, %r17, %r27
	adde %r25, %r25, %r3
	and %r3, %r21, %r27
	subf %r25, %r3, %r25
	mulld %r28, %r22, %r4
	mulld %r12, %r24, %r4
	ld %r4, 0(%r7)
	mulld %r3, %r28, %r4
	addc %r3, %r3, %r22
	mulhdu %r0, %r28, %r4
	addze %r0, %r0
	addc %r22, %r3, %r9
	addze %r9, %r0
	mulld %r3, %r12, %r4
	addc %r3, %r3, %r24
	mulhdu %r0, %r12, %r4
	addze %r0, %r0
	addc %r24, %r3, %r11
	addze %r11, %r0
	addi %r22, %r23, 0
	rldicl %r0, %r23, 1, 63
	li %r23, 0
	subf %r23, %r0, %r23
	addi %r24, %r25, 0
	rldicl %r0, %r25, 1, 63
	li %r25, 0
	subf %r25, %r0, %r25
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	beq %cr0, 27f
29:
	ld %r26, 8(%r5)
	ld %r27, 8(%r6)
	mulld %r3, %r14, %r26
	addc %r22, %r22, %r3
	mulhdu %r3, %r14, %r26
	adde %r23, %r23, %r3
	and %r3, %r18, %r26
	subf %r23, %r3, %r23
	mulld %r3, %r15, %r27
	addc %r22, %r22, %r3
	mulhdu %r3, %r15, %r27
	adde %r23, %r23, %r3
	and %r3, %r19, %r27
	subf %r23, %r3, %r23
	mulld %r3, %r16, %r26
	addc %r24, %r24, %r3
	mulhdu %r3, %r16, %r26
	adde %r25, %r25, %r3
	and %r3, %r20, %r26
	subf %r25, %r3, %r25
	mulld %r3, %r17, %r27
	addc %r24, %r24, %r3
	mulhdu %r3, %r17, %r27
	adde %r25, %r25, %r3
	and %r3, %r21, %r27
	subf %r25, %r3, %r25
	ld %r4, 8(%r7)
	mulld %r3, %r28, %r4
	addc %r3, %r3, %r22
	mulhdu %r0, %r28, %r4
	addze %r0, %r0
	addc %r22, %r3, %r9
	addze %r9, %r0
	std %r22, 0(%r5)
	mulld %r3, %r12, %r4
	addc %r3, %r3, %r24
	mulhdu %r0, %r12, %r4
	addze %r0, %r0
	addc %r24, %r3, %r11
	addze %r11, %r0
	std %r24, 0(%r6)
	addi %r22, %r23, 0
	rldicl %r0, %r23, 1, 63
	li %r23, 0
	subf %r23, %r0, %r23
	addi %r24, %r25, 0
	rldicl %r0, %r25, 1, 63
	li %r25, 0
	subf %r25, %r0, %r25
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 29b
	b 28f
27:
28:
	ld %r26, 8(%r5)
	ld %r27, 8(%r6)
	mulld %r3, %r14, %r26
	addc %r22, %r22, %r3
	mulhdu %r3, %r14, %r26
	adde %r23, %r23, %r3
	and %r3, %r18, %r26
	subf %r23, %r3, %r23
	mulld %r3, %r15, %r27
	addc %r22, %r22, %r3
	mulhdu %r3, %r15, %r27
	adde %r23, %r23, %r3
	and %r3, %r19, %r27
	subf %r23, %r3, %r23
	mulld %r3, %r16, %r26
	addc %r24, %r24, %r3
	mulhdu %r3, %r16, %r26
	adde %r25, %r25, %r3
	and %r3, %r20, %r26
	subf %r25, %r3, %r25
	mulld %r3, %r17, %r27
	addc %r24, %r24, %r3
	mulhdu %r3, %r17, %r27
	adde %r25, %r25, %r3
	and %r3, %r21, %r27
	subf %r25, %r3, %r25
	rldicl %r3, %r22, 1, 63
	li %r4, 0
	subf %r3, %r3, %r4
	addc %r22, %r22, %r9
	addze %r3, %r3
	std %r22, 0(%r5)
	std %r3, 8(%r5)
	rldicl %r3, %r24, 1, 63
	subf %r3, %r3, %r4
	addc %r24, %r24, %r11
	addze %r3, %r3
	std %r24, 0(%r6)
	std %r3, 8(%r6)
	li %r3, 11
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r14, 0(%r3)
	ld %r15, 8(%r3)
	ld %r16, 16(%r3)
	ld %r17, 24(%r3)
	ld %r18, 32(%r3)
	ld %r19, 40(%r3)
	li %r3, 12
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r20, 0(%r3)
	ld %r21, 8(%r3)
	ld %r22, 16(%r3)
	ld %r23, 24(%r3)
	ld %r24, 32(%r3)
	ld %r25, 40(%r3)
	li %r3, 13
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r26, 0(%r3)
	ld %r27, 8(%r3)
	ld %r28, 16(%r3)
	addi %r10, %r10, -32768
	rldicl %r3, %r10, 49, 15
	cmpldi %cr0, %r3, 0
	bne %cr0, 25b
	li %r11, 1
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	li %r9, 0
210:
	ld %r0, 0(%r7)
	mulld %r3, %r11, %r0
	mulhdu %r0, %r11, %r0
	ld %r12, 0(%r6)
	addc %r3, %r3, %r12
	addze %r0, %r0
	addc %r3, %r3, %r9
	addze %r9, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 210b
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	rldicr %r8, %r8, 3, 60
	add %r6, %r6, %r8
	ld %r9, 0(%r6)
	rldicl %r9, %r9, 1, 63
	li %r0, 0
	subf %r9, %r9, %r0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
211:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 211b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	subfc %r0, %r8, %r8
212:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 212b
	li %r9, 0
	adde %r9, %r9, %r9
	addi %r9, %r9, -1
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
213:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 213b
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	subfc %r0, %r8, %r8
214:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 214b
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	rldicr %r8, %r8, 3, 60
	add %r6, %r6, %r8
	ld %r9, 0(%r6)
	rldicl %r9, %r9, 1, 63
	li %r0, 0
	subf %r9, %r9, %r0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
215:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 215b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	subfc %r0, %r8, %r8
216:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 216b
	li %r9, 0
	adde %r9, %r9, %r9
	addi %r9, %r9, -1
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
217:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 217b
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	rldicr %r3, %r8, 4, 59
	subf %r3, %r8, %r3
	addi %r3, %r3, 10
	rldicr %r3, %r3, 15, 48
	add %r10, %r10, %r3
218:
	li %r11, 1
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	li %r9, 0
219:
	ld %r0, 0(%r7)
	mulld %r3, %r11, %r0
	mulhdu %r0, %r11, %r0
	ld %r12, 0(%r6)
	addc %r3, %r3, %r12
	addze %r0, %r0
	addc %r3, %r3, %r9
	addze %r9, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 219b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	subfc %r0, %r8, %r8
220:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 220b
	li %r9, 0
	adde %r9, %r9, %r9
	addi %r9, %r9, -1
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
221:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 221b
	addi %r10, %r10, -32768
	rldicl %r3, %r10, 49, 15
	cmpldi %cr0, %r3, 0
	bne %cr0, 218b
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 2
	li %r0, 0
222:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 222b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 4
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	subfc %r0, %r8, %r8
223:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 223b
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	rldicr %r8, %r8, 3, 60
	add %r6, %r6, %r8
	ld %r9, 0(%r6)
	rldicl %r9, %r9, 1, 63
	li %r0, 0
	subf %r9, %r9, %r0
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
224:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 224b
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 2
	li %r0, 0
225:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 225b
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
226:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 226b
	blr
