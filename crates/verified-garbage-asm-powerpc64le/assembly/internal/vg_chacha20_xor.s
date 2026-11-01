// The functions of `src/internal/vg_chacha20_xor.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_xor:
	std %r22, 256(%r6)
	std %r23, 264(%r6)
	mflr %r0
	std %r0, 272(%r6)
	addi %r22, %r4, 0
	addi %r23, %r5, 0
	addi %r4, %r6, 0
	cmpldi %cr0, %r23, 0
	beq %cr0, 20f
22:
	bl {vg_chacha20_block}
	rldicl %r9, %r23, 58, 6
	addi %r5, %r23, 0
	cmpldi %cr0, %r9, 0
	beq %cr0, 23f
	li %r5, 64
	b 24f
23:
24:
	subf %r23, %r5, %r23
	addi %r7, %r4, 0
	rldicl %r9, %r5, 58, 6
	cmpldi %cr0, %r9, 0
	beq %cr0, 25f
27:
	ld %r6, 0(%r22)
	ld %r8, 0(%r7)
	xor %r6, %r6, %r8
	std %r6, 0(%r22)
	addi %r22, %r22, 8
	addi %r7, %r7, 8
	addi %r5, %r5, -8
	cmpldi %cr0, %r5, 0
	bne %cr0, 27b
	b 26f
25:
28:
	lbz %r6, 0(%r22)
	lbz %r8, 0(%r7)
	xor %r6, %r6, %r8
	stb %r6, 0(%r22)
	addi %r22, %r22, 1
	addi %r7, %r7, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 28b
26:
	lwz %r8, 48(%r3)
	addi %r8, %r8, 1
	stw %r8, 48(%r3)
	cmpldi %cr0, %r23, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r0, 272(%r4)
	mtlr %r0
	ld %r22, 256(%r4)
	ld %r23, 264(%r4)
	blr
