// The functions of `src/zeroize.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_zeroize:
	li %r5, 0
	rldicl %r6, %r4, 61, 3
	li %r7, 7
	and %r4, %r4, %r7
	cmpldi %cr0, %r6, 0
	beq %cr0, 20f
22:
	std %r5, 0(%r3)
	addi %r3, %r3, 8
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 22b
	b 21f
20:
21:
	addi %r6, %r4, 0
	cmpldi %cr0, %r6, 0
	beq %cr0, 23f
25:
	stb %r5, 0(%r3)
	addi %r3, %r3, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 25b
	b 24f
23:
24:
	blr
