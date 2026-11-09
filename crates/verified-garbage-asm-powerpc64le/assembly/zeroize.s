// The functions of `src/zeroize.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_zeroize:
	li %r5, 0
	rldicl %r6, %r4, 58, 6
	cmpldi %cr0, %r6, 0
	beq %cr0, 20f
22:
	std %r5, 0(%r3)
	std %r5, 8(%r3)
	std %r5, 16(%r3)
	std %r5, 24(%r3)
	std %r5, 32(%r3)
	std %r5, 40(%r3)
	std %r5, 48(%r3)
	std %r5, 56(%r3)
	addi %r3, %r3, 64
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 22b
	b 21f
20:
21:
	li %r7, 63
	and %r6, %r4, %r7
	rldicl %r6, %r6, 61, 3
	cmpldi %cr0, %r6, 0
	beq %cr0, 23f
25:
	std %r5, 0(%r3)
	addi %r3, %r3, 8
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 25b
	b 24f
23:
24:
	li %r7, 7
	and %r6, %r4, %r7
	cmpldi %cr0, %r6, 0
	beq %cr0, 26f
28:
	stb %r5, 0(%r3)
	addi %r3, %r3, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 28b
	b 27f
26:
27:
	blr
