// The functions of `src/cmac_aes.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cmac_aes_init:
	stdu %r1, -2336(%r1)
	addi %r6, %r1, 32
	mflr %r0
	std %r0, 2200(%r6)
	std %r14, 2176(%r6)
	std %r16, 2192(%r6)
	std %r15, 2184(%r6)
	or %r14, %r3, %r3
	or %r15, %r6, %r6
	rldicl %r16, %r5, 62, 2
	addi %r16, %r16, 6
	or %r3, %r4, %r4
	or %r4, %r5, %r5
	or %r5, %r14, %r14
	bl {vg_aes_expand_key_scratch}
	or %r3, %r14, %r14
	or %r4, %r16, %r16
	addi %r5, %r14, 240
	or %r6, %r15, %r15
	bl {vg_cmac_aes_subkeys}
	li %r9, 0
	std %r9, 272(%r14)
	std %r9, 280(%r14)
	ld %r0, 2200(%r15)
	ld %r14, 2176(%r15)
	ld %r16, 2192(%r15)
	ld %r15, 2184(%r15)
	mtlr %r0
	addi %r1, %r1, 2336
	blr

vg_cmac_aes_absorb:
	stdu %r1, -2336(%r1)
	addi %r8, %r1, 32
	mflr %r0
	std %r0, 2176(%r8)
	std %r14, 2184(%r8)
	std %r15, 2192(%r8)
	std %r16, 2200(%r8)
	std %r17, 2208(%r8)
	std %r18, 2216(%r8)
	std %r19, 2224(%r8)
	or %r14, %r3, %r3
	or %r15, %r4, %r4
	or %r16, %r6, %r6
	or %r17, %r7, %r7
	or %r19, %r8, %r8
	cmpldi %cr0, %r5, 0
	beq %cr0, 20f
	addi %r9, %r5, -1
	li %r10, 15
	and %r9, %r9, %r10
	addi %r9, %r9, 1
	b 21f
20:
	li %r9, 0
21:
	rldicl %r10, %r17, 60, 4
	cmpldi %cr0, %r10, 0
	beq %cr0, 22f
	li %r10, 16
	b 23f
22:
	or %r10, %r17, %r17
23:
	li %r12, 16
	subf %r12, %r9, %r12
	subf %r11, %r12, %r10
	rldicl %r11, %r11, 1, 63
	cmpldi %cr0, %r11, 0
	beq %cr0, 24f
	or %r12, %r10, %r10
	b 25f
24:
25:
	or %r8, %r12, %r12
	add %r10, %r14, %r9
	addi %r10, %r10, 288
	or %r11, %r16, %r16
	cmpldi %cr0, %r12, 0
	beq %cr0, 26f
28:
	lbz %r9, 0(%r11)
	stb %r9, 0(%r10)
	addi %r11, %r11, 1
	addi %r10, %r10, 1
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 28b
	b 27f
26:
27:
	add %r16, %r16, %r8
	subf %r17, %r8, %r17
	li %r7, 0
	cmpldi %cr0, %r17, 0
	beq %cr0, 29f
	li %r7, 1
	b 210f
29:
210:
	or %r3, %r14, %r14
	or %r4, %r15, %r15
	addi %r5, %r14, 272
	addi %r6, %r14, 288
	or %r8, %r19, %r19
	bl {vg_cmac_aes_update}
	li %r18, 0
	cmpldi %cr0, %r17, 0
	beq %cr0, 211f
	addi %r18, %r17, -1
	li %r9, 15
	and %r9, %r18, %r9
	subf %r18, %r9, %r18
	b 212f
211:
212:
	rldicl %r7, %r18, 60, 4
	or %r3, %r14, %r14
	or %r4, %r15, %r15
	addi %r5, %r14, 272
	or %r6, %r16, %r16
	or %r8, %r19, %r19
	bl {vg_cmac_aes_update}
	add %r16, %r16, %r18
	subf %r17, %r18, %r17
	addi %r10, %r14, 288
	or %r11, %r16, %r16
	or %r12, %r17, %r17
	cmpldi %cr0, %r12, 0
	beq %cr0, 213f
215:
	lbz %r9, 0(%r11)
	stb %r9, 0(%r10)
	addi %r11, %r11, 1
	addi %r10, %r10, 1
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 215b
	b 214f
213:
214:
	ld %r0, 2176(%r19)
	ld %r14, 2184(%r19)
	ld %r15, 2192(%r19)
	ld %r16, 2200(%r19)
	ld %r17, 2208(%r19)
	ld %r18, 2216(%r19)
	ld %r19, 2224(%r19)
	mtlr %r0
	addi %r1, %r1, 2336
	blr

vg_cmac_aes_finish:
	stdu %r1, -2336(%r1)
	addi %r7, %r1, 32
	mflr %r0
	ld %r9, 272(%r3)
	std %r9, 0(%r6)
	ld %r9, 280(%r3)
	std %r9, 8(%r6)
	std %r0, 2184(%r7)
	std %r14, 2176(%r7)
	or %r14, %r7, %r7
	or %r8, %r7, %r7
	or %r7, %r5, %r5
	or %r5, %r6, %r6
	addi %r6, %r3, 288
	cmpldi %cr0, %r7, 0
	beq %cr0, 20f
	addi %r7, %r7, -1
	li %r9, 15
	and %r7, %r7, %r9
	addi %r7, %r7, 1
	b 21f
20:
21:
	bl {vg_cmac_aes_finalize}
	ld %r0, 2184(%r14)
	ld %r14, 2176(%r14)
	mtlr %r0
	addi %r1, %r1, 2336
	blr
