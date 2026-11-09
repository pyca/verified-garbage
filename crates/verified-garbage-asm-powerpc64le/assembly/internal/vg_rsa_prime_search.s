// The functions of `src/internal/vg_rsa_prime_search.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_prime_search:
	stdu %r1, -192(%r1)
	addi %r11, %r1, 32
	std %r31, 32(%r11)
	addi %r31, %r11, 0
	std %r3, 40(%r31)
	std %r4, 48(%r31)
	std %r5, 56(%r31)
	std %r6, 64(%r31)
	std %r7, 72(%r31)
	std %r8, 80(%r31)
	std %r9, 88(%r31)
	std %r10, 96(%r31)
	ld %r8, 256(%r31)
	ld %r9, 264(%r31)
	ld %r10, 272(%r31)
	ld %r11, 280(%r31)
	ld %r12, 0(%r11)
	std %r8, 104(%r31)
	std %r9, 112(%r31)
	std %r10, 120(%r31)
	std %r11, 144(%r31)
	std %r12, 0(%r31)
	std %r4, 8(%r31)
	rldicr %r12, %r4, 15, 48
	add %r12, %r12, %r4
	std %r12, 16(%r31)
	li %r12, 0
	std %r12, 24(%r31)
	std %r12, 128(%r31)
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
20:
	ld %r9, 0(%r31)
	cmpldi %cr0, %r9, 0
	beq %cr0, 21f
	stdu %r1, -128(%r1)
	addi %r12, %r1, 96
	ld %r9, 104(%r31)
	ld %r10, 112(%r31)
	ld %r11, 120(%r31)
	std %r9, 0(%r12)
	std %r10, 8(%r12)
	std %r11, 16(%r12)
	ld %r3, 40(%r31)
	ld %r4, 48(%r31)
	ld %r5, 56(%r31)
	ld %r6, 64(%r31)
	ld %r7, 72(%r31)
	ld %r8, 80(%r31)
	ld %r9, 88(%r31)
	ld %r10, 96(%r31)
	bl {vg_rsa_keygen_candidate}
	addi %r1, %r1, 128
	rlwinm %r9, %r3, 0, 0, 31
	ld %r11, 56(%r31)
	ld %r10, 0(%r11)
	addi %r12, %r9, -1
	cmpldi %cr0, %r12, 0
	beq %cr0, 23f
	cmpldi %cr0, %r9, 0
	beq %cr0, 25f
	cmpldi %cr0, %r10, 0
	beq %cr0, 27f
	ld %r11, 96(%r31)
	ld %r12, 104(%r31)
	ld %r6, 128(%r31)
	add %r11, %r11, %r10
	subf %r12, %r10, %r12
	add %r6, %r6, %r10
	li %r7, 4
	std %r11, 96(%r31)
	std %r12, 104(%r31)
	std %r6, 128(%r31)
	std %r7, 136(%r31)
	addi %r8, %r9, -2
	cmpldi %cr0, %r8, 0
	beq %cr0, 29f
	ld %r11, 0(%r31)
	addi %r11, %r11, -1
	std %r11, 0(%r31)
	b 210f
29:
210:
	b 28f
27:
	li %r10, 0
	li %r11, 3
	std %r10, 0(%r31)
	std %r10, 24(%r31)
	std %r11, 136(%r31)
	ld %r3, 40(%r31)
	ld %r4, 48(%r31)
	li %r5, 0
211:
	stb %r5, 0(%r3)
	addi %r3, %r3, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 211b
28:
	b 26f
25:
	ld %r10, 104(%r31)
	ld %r11, 16(%r31)
	subf %r12, %r11, %r10
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	beq %cr0, 212f
	ld %r12, 8(%r31)
	rldicr %r12, %r12, 4, 59
	subf %r0, %r12, %r10
	rldicl %r0, %r0, 1, 63
	li %r6, 0
	subf %r0, %r0, %r6
	xor %r6, %r10, %r12
	and %r6, %r6, %r0
	xor %r6, %r6, %r10
	add %r6, %r6, %r6
	subf %r0, %r11, %r6
	rldicl %r0, %r0, 1, 63
	li %r7, 0
	subf %r0, %r0, %r7
	xor %r7, %r6, %r11
	and %r7, %r7, %r0
	xor %r7, %r7, %r11
	li %r8, 0
	std %r7, 24(%r31)
	std %r8, 136(%r31)
	b 213f
212:
	li %r10, 0
	li %r11, 3
	std %r10, 0(%r31)
	std %r10, 24(%r31)
	std %r11, 136(%r31)
	ld %r3, 40(%r31)
	ld %r4, 48(%r31)
	li %r5, 0
214:
	stb %r5, 0(%r3)
	addi %r3, %r3, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 214b
213:
26:
	b 24f
23:
	ld %r11, 128(%r31)
	add %r11, %r11, %r10
	std %r11, 128(%r31)
	li %r10, 0
	li %r11, 1
	std %r10, 0(%r31)
	std %r10, 24(%r31)
	std %r11, 136(%r31)
24:
	b 22f
21:
	li %r10, 0
	li %r11, 3
	std %r10, 0(%r31)
	std %r10, 24(%r31)
	std %r11, 136(%r31)
	ld %r3, 40(%r31)
	ld %r4, 48(%r31)
	li %r5, 0
215:
	stb %r5, 0(%r3)
	addi %r3, %r3, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 215b
22:
	ld %r9, 136(%r31)
	addi %r9, %r9, -4
	cmpldi %cr0, %r9, 0
	beq %cr0, 20b
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	ld %r8, 144(%r31)
	ld %r9, 0(%r31)
	ld %r10, 8(%r31)
	ld %r11, 16(%r31)
	ld %r12, 24(%r31)
	ld %r7, 56(%r31)
	ld %r6, 128(%r31)
	ld %r3, 136(%r31)
	ld %r31, 32(%r31)
	std %r9, 0(%r8)
	std %r10, 8(%r8)
	std %r11, 16(%r8)
	std %r12, 24(%r8)
	std %r6, 0(%r7)
	addi %r1, %r1, 192
	blr
