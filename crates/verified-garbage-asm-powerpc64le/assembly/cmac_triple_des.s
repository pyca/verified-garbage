// The functions of `src/cmac_triple_des.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cmac_triple_des_stream_init:
	stdu %r1, -672(%r1)
	addi %r6, %r1, 32
	mflr %r0
	std %r0, 528(%r6)
	std %r30, 544(%r6)
	std %r31, 552(%r6)
	or %r31, %r3, %r3
	or %r30, %r6, %r6
	or %r3, %r4, %r4
	or %r4, %r5, %r5
	or %r5, %r31, %r31
	bl {vg_triple_des_expand_key}
	or %r3, %r31, %r31
	or %r5, %r30, %r30
	addi %r4, %r30, 512
	li %r0, 0
	std %r0, 0(%r4)
	bl {vg_triple_des_encrypt_block}
	li %r6, 0
	ldbrx %r7, %r4, %r6
	rldicl %r8, %r7, 1, 63
	subf %r9, %r8, %r6
	li %r10, 27
	and %r9, %r9, %r10
	rldicr %r7, %r7, 1, 62
	xor %r7, %r7, %r9
	li %r11, 384
	stdbrx %r7, %r3, %r11
	rldicl %r8, %r7, 1, 63
	subf %r9, %r8, %r6
	li %r10, 27
	and %r9, %r9, %r10
	rldicr %r7, %r7, 1, 62
	xor %r7, %r7, %r9
	li %r11, 392
	stdbrx %r7, %r3, %r11
	li %r0, 0
	std %r0, 400(%r3)
	ld %r0, 528(%r30)
	ld %r31, 552(%r30)
	ld %r30, 544(%r30)
	mtlr %r0
	addi %r1, %r1, 672
	blr

vg_cmac_triple_des_absorb:
	stdu %r1, -720(%r1)
	addi %r7, %r1, 32
	mflr %r0
	std %r0, 528(%r7)
	std %r29, 536(%r7)
	std %r30, 544(%r7)
	std %r31, 552(%r7)
	or %r29, %r5, %r5
	or %r5, %r7, %r7
	cmpldi %cr0, %r4, 0
	beq %cr0, 20f
	addi %r8, %r4, -1
	li %r9, 7
	and %r8, %r8, %r9
	addi %r8, %r8, 1
	b 21f
20:
	li %r8, 0
21:
	li %r9, 8
	subf %r9, %r8, %r9
	rldicl %r10, %r6, 60, 4
	subf %r11, %r6, %r9
	rldicl %r11, %r11, 1, 63
	or %r10, %r10, %r11
	cmpldi %cr0, %r10, 0
	bne %cr0, 22f
	addi %r11, %r3, 408
	add %r11, %r11, %r8
	or %r10, %r29, %r29
	or %r12, %r6, %r6
	cmpldi %cr0, %r12, 0
	beq %cr0, 24f
26:
	lbz %r0, 0(%r10)
	stb %r0, 0(%r11)
	addi %r10, %r10, 1
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 26b
	b 25f
24:
25:
	b 23f
22:
	addi %r11, %r3, 408
	add %r11, %r11, %r8
	or %r10, %r29, %r29
	or %r12, %r9, %r9
	cmpldi %cr0, %r12, 0
	beq %cr0, 27f
29:
	lbz %r0, 0(%r10)
	stb %r0, 0(%r11)
	addi %r10, %r10, 1
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 29b
	b 28f
27:
28:
	or %r29, %r10, %r10
	subf %r30, %r9, %r6
	addi %r30, %r30, -1
	rldicl %r30, %r30, 61, 3
	subf %r31, %r9, %r6
	rldicr %r12, %r30, 3, 60
	subf %r31, %r12, %r31
	ld %r7, 400(%r3)
	ld %r9, 408(%r3)
	xor %r7, %r7, %r9
	std %r7, 512(%r5)
	addi %r4, %r5, 512
	bl {vg_triple_des_encrypt_block}
	cmpldi %cr0, %r30, 0
	beq %cr0, 210f
212:
	ld %r7, 512(%r5)
	ld %r9, 0(%r29)
	xor %r7, %r7, %r9
	std %r7, 512(%r5)
	addi %r29, %r29, 8
	addi %r30, %r30, -1
	bl {vg_triple_des_encrypt_block}
	cmpldi %cr0, %r30, 0
	bne %cr0, 212b
	b 211f
210:
211:
	ld %r7, 512(%r5)
	std %r7, 400(%r3)
	addi %r11, %r3, 408
	or %r10, %r29, %r29
	or %r12, %r31, %r31
	cmpldi %cr0, %r12, 0
	beq %cr0, 213f
215:
	lbz %r0, 0(%r10)
	stb %r0, 0(%r11)
	addi %r10, %r10, 1
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 215b
	b 214f
213:
214:
23:
	ld %r0, 528(%r5)
	ld %r29, 536(%r5)
	ld %r30, 544(%r5)
	ld %r31, 552(%r5)
	mtlr %r0
	addi %r1, %r1, 720
	blr

vg_cmac_triple_des_finish:
	stdu %r1, -672(%r1)
	addi %r6, %r1, 32
	mflr %r0
	std %r0, 528(%r6)
	std %r31, 552(%r6)
	or %r31, %r5, %r5
	or %r5, %r6, %r6
	cmpldi %cr0, %r4, 0
	beq %cr0, 20f
	addi %r8, %r4, -1
	li %r9, 7
	and %r8, %r8, %r9
	addi %r8, %r8, 1
	b 21f
20:
	li %r8, 0
21:
	addi %r9, %r8, -8
	cmpldi %cr0, %r9, 0
	beq %cr0, 22f
	li %r0, 0
	std %r0, 520(%r5)
	addi %r10, %r3, 408
	addi %r11, %r5, 520
	or %r12, %r8, %r8
	cmpldi %cr0, %r12, 0
	beq %cr0, 24f
26:
	lbz %r0, 0(%r10)
	stb %r0, 0(%r11)
	addi %r10, %r10, 1
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 26b
	b 25f
24:
25:
	li %r9, 128
	stb %r9, 0(%r11)
	ld %r7, 520(%r5)
	ld %r9, 392(%r3)
	xor %r7, %r7, %r9
	ld %r9, 400(%r3)
	xor %r7, %r7, %r9
	std %r7, 512(%r5)
	b 23f
22:
	ld %r7, 408(%r3)
	ld %r9, 384(%r3)
	xor %r7, %r7, %r9
	ld %r9, 400(%r3)
	xor %r7, %r7, %r9
	std %r7, 512(%r5)
23:
	addi %r4, %r5, 512
	bl {vg_triple_des_encrypt_block}
	ld %r7, 512(%r5)
	std %r7, 0(%r31)
	ld %r0, 528(%r5)
	ld %r31, 552(%r5)
	mtlr %r0
	addi %r1, %r1, 672
	blr
