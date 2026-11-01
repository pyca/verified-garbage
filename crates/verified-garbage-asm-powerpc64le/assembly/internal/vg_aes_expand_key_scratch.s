// The functions of `src/internal/vg_aes_expand_key_scratch.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_expand_key_scratch:
	or %r7, %r4, %r4
20:
	ld %r8, 0(%r3)
	std %r8, 0(%r5)
	addi %r3, %r3, 8
	addi %r5, %r5, 8
	addi %r4, %r4, -8
	cmpldi %cr0, %r4, 0
	bne %cr0, 20b
	subf %r10, %r7, %r5
	addi %r11, %r5, -4
	li %r12, 0
	rldicl %r4, %r7, 62, 2
	add %r8, %r4, %r4
	add %r4, %r4, %r8
	addi %r4, %r4, 28
	li %r6, 1
21:
	lwz %r9, 0(%r11)
	cmpldi %cr0, %r12, 0
	beq %cr0, 22f
	addi %r0, %r12, -16
	cmpldi %cr0, %r0, 0
	beq %cr0, 24f
	b 25f
24:
	addi %r0, %r7, -32
	cmpldi %cr0, %r0, 0
	beq %cr0, 26f
	b 27f
26:
	mtvsrd 32, %r9
	vsbox %v0, %v0
	mfvsrd %r9, 32
	rlwinm %r9, %r9, 0, 0, 31
27:
25:
	b 23f
22:
	mtvsrd 32, %r9
	vsbox %v0, %v0
	mfvsrd %r9, 32
	rlwinm %r9, %r9, 0, 0, 31
	rlwinm %r9, %r9, 24, 0, 31
	xor %r9, %r9, %r6
	rldicl %r0, %r6, 57, 7
	li %r8, 0
	subf %r0, %r0, %r8
	li %r8, 27
	and %r0, %r0, %r8
	add %r6, %r6, %r6
	xor %r6, %r6, %r0
	li %r8, 255
	and %r6, %r6, %r8
23:
	lwz %r8, 0(%r10)
	xor %r9, %r9, %r8
	stw %r9, 4(%r11)
	addi %r11, %r11, 4
	addi %r10, %r10, 4
	addi %r12, %r12, 4
	subf %r0, %r7, %r12
	cmpldi %cr0, %r0, 0
	beq %cr0, 28f
	b 29f
28:
	li %r12, 0
29:
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 21b
	blr
