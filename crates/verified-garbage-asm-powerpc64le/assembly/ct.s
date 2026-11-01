// The functions of `src/ct.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ct_eq:
	li %r7, 0
	subf %r9, %r6, %r4
	cmpldi %cr0, %r9, 0
	beq %cr0, 20f
	li %r3, 0
	b 21f
20:
	li %r8, 0
	cmpldi %cr0, %r4, 0
	beq %cr0, 22f
24:
	add %r10, %r3, %r8
	lbz %r11, 0(%r10)
	add %r10, %r5, %r8
	lbz %r12, 0(%r10)
	xor %r11, %r11, %r12
	or %r7, %r7, %r11
	addi %r8, %r8, 1
	subf %r9, %r4, %r8
	cmpldi %cr0, %r9, 0
	bne %cr0, 24b
	b 23f
22:
23:
	addi %r7, %r7, -1
	rldicl %r3, %r7, 1, 63
21:
	blr
