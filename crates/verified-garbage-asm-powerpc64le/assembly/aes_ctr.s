// The functions of `src/aes_ctr.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ctr:
	mflr %r0
	std %r0, 2112(%r8)
	std %r14, 2064(%r8)
	std %r15, 2072(%r8)
	std %r16, 2080(%r8)
	std %r17, 2088(%r8)
	std %r18, 2096(%r8)
	std %r19, 2104(%r8)
	or %r14, %r3, %r3
	or %r15, %r4, %r4
	or %r16, %r5, %r5
	or %r17, %r6, %r6
	or %r18, %r7, %r7
	or %r19, %r8, %r8
	cmpldi %cr0, %r18, 0
	beq %cr0, 20f
22:
	li %r10, 12
	lwbrx %r9, %r16, %r10
	li %r10, 1
	rldicr %r10, %r10, 32, 31
	subf %r10, %r9, %r10
	subf %r11, %r10, %r18
	rldicl %r11, %r11, 1, 63
	li %r12, 0
	subf %r11, %r11, %r12
	xor %r12, %r18, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	std %r10, 2048(%r19)
	or %r3, %r14, %r14
	or %r4, %r15, %r15
	or %r5, %r16, %r16
	or %r6, %r17, %r17
	or %r7, %r10, %r10
	or %r8, %r19, %r19
	bl {vg_aes_ctr32}
	ld %r9, 2048(%r19)
	subf %r18, %r9, %r18
	rldicr %r9, %r9, 4, 59
	add %r17, %r17, %r9
	li %r10, 12
	lwbrx %r9, %r16, %r10
	cmpldi %cr0, %r9, 0
	beq %cr0, 23f
	b 24f
23:
	li %r10, 8
	ldbrx %r9, %r16, %r10
	li %r11, 1
	rldicr %r11, %r11, 32, 31
	add %r9, %r9, %r11
	stdbrx %r9, %r16, %r10
	rldicl %r9, %r9, 32, 32
	addi %r9, %r9, -1
	rldicl %r9, %r9, 1, 63
	li %r10, 0
	ldbrx %r11, %r16, %r10
	add %r11, %r11, %r9
	stdbrx %r11, %r16, %r10
24:
	cmpldi %cr0, %r18, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r0, 2112(%r19)
	ld %r14, 2064(%r19)
	ld %r15, 2072(%r19)
	ld %r16, 2080(%r19)
	ld %r17, 2088(%r19)
	ld %r18, 2096(%r19)
	ld %r19, 2104(%r19)
	mtlr %r0
	blr
