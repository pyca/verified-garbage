// The functions of `src/rsa_keygen.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_generate_init:
	li %r9, 0
	li %r10, 0
	cmpldi %cr0, %r6, 0
	beq %cr0, 20f
22:
	lbz %r11, 0(%r5)
	rldicr %r9, %r9, 8, 55
	add %r9, %r9, %r11
	rldicl %r7, %r9, 32, 32
	or %r10, %r10, %r7
	rlwinm %r9, %r9, 0, 0, 31
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 22b
	b 21f
20:
21:
	li %r12, 1
	subf %r7, %r12, %r10
	rldicl %r7, %r7, 1, 63
	li %r8, 1
	and %r8, %r9, %r8
	and %r7, %r7, %r8
	li %r12, 3
	subf %r8, %r12, %r9
	rldicl %r8, %r8, 1, 63
	li %r12, 1
	subf %r8, %r8, %r12
	and %r7, %r7, %r8
	rldicl %r8, %r4, 50, 14
	li %r12, 1
	subf %r8, %r12, %r8
	rldicl %r8, %r8, 1, 63
	li %r12, 16383
	and %r11, %r4, %r12
	li %r12, 8193
	subf %r0, %r12, %r11
	rldicl %r0, %r0, 1, 63
	li %r12, 512
	subf %r11, %r12, %r11
	rldicl %r11, %r11, 1, 63
	subf %r0, %r11, %r0
	mulld %r8, %r8, %r0
	li %r12, 2
	subf %r12, %r8, %r12
	mulld %r12, %r12, %r7
	mulld %r11, %r7, %r8
	rldicl %r4, %r4, 57, 7
	rldicr %r4, %r4, 3, 60
	li %r10, 3
	xor %r0, %r9, %r10
	li %r10, 1
	subf %r0, %r10, %r0
	rldicl %r0, %r0, 1, 63
	rldicr %r5, %r4, 3, 60
	rldicr %r6, %r4, 5, 58
	add %r5, %r5, %r6
	rldicr %r6, %r4, 4, 59
	rldicr %r7, %r4, 3, 60
	add %r6, %r6, %r7
	mulld %r6, %r6, %r0
	add %r5, %r5, %r6
	mulld %r5, %r5, %r11
	std %r5, 0(%r3)
	mulld %r6, %r4, %r11
	std %r6, 8(%r3)
	rldicr %r6, %r4, 15, 48
	add %r6, %r6, %r4
	mulld %r6, %r6, %r11
	std %r6, 16(%r3)
	rldicr %r6, %r4, 5, 58
	mulld %r6, %r6, %r11
	std %r6, 24(%r3)
	li %r6, 0
	std %r6, 32(%r3)
	rldicr %r6, %r11, 2, 61
	std %r6, 40(%r3)
	mulld %r6, %r9, %r11
	li %r7, 48
	stdbrx %r6, %r3, %r7
	addi %r3, %r12, 0
	blr
	.p2align 6

vg_rsa_generate:
	stdu %r1, -144(%r1)
	addi %r11, %r1, 32
	std %r31, 72(%r11)
	addi %r31, %r11, 0
	std %r3, 0(%r31)
	std %r5, 16(%r31)
	std %r6, 24(%r31)
	std %r7, 32(%r31)
	std %r8, 40(%r31)
	std %r9, 48(%r31)
	std %r10, 56(%r31)
	ld %r4, 8(%r10)
	ld %r9, 48(%r10)
	std %r4, 8(%r31)
	li %r0, 0
	std %r0, 64(%r31)
	rldicr %r5, %r4, 3, 60
	rldicr %r6, %r4, 5, 58
	add %r5, %r5, %r6
	rldicr %r6, %r4, 4, 59
	rldicr %r7, %r4, 3, 60
	add %r6, %r6, %r7
	li %r7, 3
	rldicr %r7, %r7, 56, 7
	xor %r8, %r9, %r7
	rldicl %r7, %r8, 32, 32
	rlwinm %r8, %r8, 0, 0, 31
	or %r7, %r7, %r8
	li %r8, 1
	subf %r7, %r8, %r7
	rldicl %r7, %r7, 1, 63
	mulld %r6, %r6, %r7
	add %r5, %r5, %r6
	std %r5, 88(%r31)
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	ld %r3, 0(%r31)
	std %r3, 96(%r31)
	ld %r4, 8(%r31)
	rldicr %r4, %r4, 2, 61
	std %r4, 104(%r31)
	ld %r3, 96(%r31)
	ld %r4, 104(%r31)
	li %r5, 0
20:
	stb %r5, 0(%r3)
	addi %r3, %r3, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 20b
	ld %r4, 8(%r31)
	rldicr %r5, %r4, 2, 61
	add %r4, %r4, %r5
	ld %r3, 0(%r31)
	add %r3, %r3, %r4
	std %r3, 96(%r31)
	ld %r4, 8(%r31)
	rldicr %r4, %r4, 2, 61
	std %r4, 104(%r31)
	ld %r3, 96(%r31)
	ld %r4, 104(%r31)
	li %r5, 0
21:
	stb %r5, 0(%r3)
	addi %r3, %r3, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 21b
22:
	stdu %r1, -128(%r1)
	ld %r12, 56(%r31)
	ld %r3, 32(%r31)
	ld %r4, 64(%r31)
	ld %r5, 40(%r31)
	ld %r6, 48(%r31)
	subf %r3, %r4, %r3
	addi %r11, %r1, 96
	std %r3, 0(%r11)
	std %r5, 8(%r11)
	std %r6, 16(%r11)
	std %r12, 24(%r11)
	ld %r12, 56(%r31)
	ld %r11, 32(%r12)
	ld %r4, 8(%r31)
	rldicr %r8, %r4, 2, 61
	ld %r3, 0(%r31)
	add %r8, %r8, %r3
	mulld %r9, %r4, %r11
	add %r3, %r8, %r9
	ld %r5, 16(%r31)
	addi %r6, %r12, 48
	li %r7, 8
	ld %r10, 24(%r31)
	ld %r0, 64(%r31)
	add %r10, %r10, %r0
	bl {vg_rsa_prime_search}
	addi %r1, %r1, 128
	rlwinm %r3, %r3, 0, 0, 31
	ld %r11, 16(%r31)
	ld %r11, 0(%r11)
	ld %r12, 64(%r31)
	add %r12, %r12, %r11
	std %r12, 64(%r31)
	cmpldi %cr0, %r3, 0
	beq %cr0, 23f
	addi %r12, %r3, -3
	cmpldi %cr0, %r12, 0
	beq %cr0, 25f
	cmpldi %cr0, %r11, 0
	beq %cr0, 27f
	ld %r12, 56(%r31)
	ld %r11, 32(%r12)
	cmpldi %cr0, %r11, 0
	beq %cr0, 29f
	stdu %r1, -176(%r1)
	ld %r3, 0(%r31)
	ld %r4, 8(%r31)
	ld %r12, 56(%r31)
	ld %r5, 40(%r31)
	ld %r6, 48(%r31)
	rldicr %r7, %r4, 2, 61
	rldicr %r8, %r4, 1, 62
	add %r7, %r7, %r8
	add %r7, %r3, %r7
	add %r8, %r7, %r4
	add %r9, %r8, %r4
	addi %r10, %r12, 48
	li %r0, 8
	addi %r11, %r1, 96
	std %r7, 0(%r11)
	std %r4, 8(%r11)
	std %r8, 16(%r11)
	std %r4, 24(%r11)
	std %r9, 32(%r11)
	std %r4, 40(%r11)
	std %r10, 48(%r11)
	std %r0, 56(%r11)
	std %r5, 64(%r11)
	std %r6, 72(%r11)
	ld %r8, 8(%r31)
	ld %r3, 0(%r31)
	rldicr %r4, %r8, 1, 62
	add %r5, %r3, %r4
	addi %r6, %r4, 0
	add %r7, %r5, %r4
	add %r9, %r7, %r8
	addi %r10, %r8, 0
	bl {vg_rsa_keygen_key}
	addi %r1, %r1, 176
	rlwinm %r3, %r3, 0, 0, 31
	addi %r11, %r3, -1
	cmpldi %cr0, %r11, 0
	beq %cr0, 211f
	addi %r11, %r3, -2
	cmpldi %cr0, %r11, 0
	beq %cr0, 213f
	ld %r3, 0(%r31)
	std %r3, 96(%r31)
	ld %r4, 8(%r31)
	rldicr %r5, %r4, 3, 60
	add %r5, %r5, %r4
	std %r5, 104(%r31)
	ld %r3, 96(%r31)
	ld %r4, 104(%r31)
	li %r5, 0
215:
	stb %r5, 0(%r3)
	addi %r3, %r3, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 215b
	ld %r12, 56(%r31)
	li %r11, 0
	std %r11, 32(%r12)
	std %r11, 40(%r12)
	li %r11, 2
	std %r11, 80(%r31)
	b 214f
213:
	ld %r12, 56(%r31)
	ld %r11, 88(%r31)
	std %r11, 0(%r12)
	li %r11, 0
	std %r11, 32(%r12)
	li %r11, 4
	std %r11, 80(%r31)
214:
	b 212f
211:
	ld %r12, 56(%r31)
	li %r11, 0
	std %r11, 32(%r12)
	std %r11, 40(%r12)
	li %r11, 1
	std %r11, 80(%r31)
212:
	b 210f
29:
	ld %r12, 56(%r31)
	ld %r11, 88(%r31)
	std %r11, 0(%r12)
	li %r11, 1
	std %r11, 32(%r12)
	li %r11, 4
	std %r11, 80(%r31)
210:
	b 28f
27:
	ld %r3, 0(%r31)
	std %r3, 96(%r31)
	ld %r4, 8(%r31)
	rldicr %r5, %r4, 3, 60
	add %r5, %r5, %r4
	std %r5, 104(%r31)
	ld %r3, 96(%r31)
	ld %r4, 104(%r31)
	li %r5, 0
216:
	stb %r5, 0(%r3)
	addi %r3, %r3, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 216b
	ld %r12, 56(%r31)
	li %r11, 0
	std %r11, 32(%r12)
	std %r11, 40(%r12)
	li %r11, 3
	std %r11, 80(%r31)
28:
	b 26f
25:
	ld %r12, 56(%r31)
	ld %r11, 40(%r12)
	rldicl %r10, %r11, 63, 1
	cmpldi %cr0, %r10, 0
	beq %cr0, 217f
	addi %r11, %r11, -1
	std %r11, 40(%r12)
	ld %r12, 56(%r31)
	ld %r11, 88(%r31)
	std %r11, 0(%r12)
	li %r11, 0
	std %r11, 32(%r12)
	li %r11, 4
	std %r11, 80(%r31)
	b 218f
217:
	ld %r3, 0(%r31)
	std %r3, 96(%r31)
	ld %r4, 8(%r31)
	rldicr %r5, %r4, 3, 60
	add %r5, %r5, %r4
	std %r5, 104(%r31)
	ld %r3, 96(%r31)
	ld %r4, 104(%r31)
	li %r5, 0
219:
	stb %r5, 0(%r3)
	addi %r3, %r3, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 219b
	ld %r12, 56(%r31)
	li %r11, 0
	std %r11, 32(%r12)
	std %r11, 40(%r12)
	li %r11, 3
	std %r11, 80(%r31)
218:
26:
	b 24f
23:
	std %r3, 80(%r31)
24:
	ld %r9, 80(%r31)
	addi %r9, %r9, -4
	cmpldi %cr0, %r9, 0
	beq %cr0, 22b
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	ld %r5, 16(%r31)
	ld %r6, 64(%r31)
	std %r6, 0(%r5)
	ld %r3, 80(%r31)
	ld %r31, 72(%r31)
	addi %r1, %r1, 144
	blr
	.p2align 6
