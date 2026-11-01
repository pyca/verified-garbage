// The functions of `src/chacha20.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_init:
	ld %r9, 0(%r4)
	ld %r10, 8(%r4)
	ld %r11, 16(%r4)
	ld %r12, 24(%r4)
	std %r9, 16(%r3)
	std %r10, 24(%r3)
	std %r11, 32(%r3)
	std %r12, 40(%r3)
	addi %r4, %r5, 0
	lwz %r9, 0(%r4)
	lwz %r10, 4(%r4)
	lwz %r11, 8(%r4)
	lwz %r12, 12(%r4)
	stw %r9, 48(%r3)
	stw %r10, 52(%r3)
	stw %r11, 56(%r3)
	stw %r12, 60(%r3)
	lis %r10, 24944
	ori %r10, %r10, 30821
	stw %r10, 0(%r3)
	lis %r10, 13088
	ori %r10, %r10, 25710
	stw %r10, 4(%r3)
	lis %r10, 31074
	ori %r10, %r10, 11570
	stw %r10, 8(%r3)
	lis %r10, 27424
	ori %r10, %r10, 25972
	stw %r10, 12(%r3)
	li %r12, 1
	rldicr %r12, %r12, 32, 31
	subf %r12, %r9, %r12
	rldicr %r12, %r12, 6, 57
	std %r12, 128(%r3)
	blr

vg_chacha20_set_nonce:
	lwz %r9, 0(%r4)
	lwz %r10, 4(%r4)
	lwz %r11, 8(%r4)
	lwz %r12, 12(%r4)
	stw %r9, 48(%r3)
	stw %r10, 52(%r3)
	stw %r11, 56(%r3)
	stw %r12, 60(%r3)
	lis %r10, 24944
	ori %r10, %r10, 30821
	stw %r10, 0(%r3)
	lis %r10, 13088
	ori %r10, %r10, 25710
	stw %r10, 4(%r3)
	lis %r10, 31074
	ori %r10, %r10, 11570
	stw %r10, 8(%r3)
	lis %r10, 27424
	ori %r10, %r10, 25972
	stw %r10, 12(%r3)
	li %r12, 1
	rldicr %r12, %r12, 32, 31
	subf %r12, %r9, %r12
	rldicr %r12, %r12, 6, 57
	std %r12, 128(%r3)
	blr

vg_chacha20_apply:
	ld %r9, 128(%r3)
	li %r12, 1
	li %r7, 63
	and %r7, %r9, %r7
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r5, 63, 1
	subf %r10, %r11, %r10
	and %r11, %r9, %r12
	and %r6, %r5, %r12
	subf %r11, %r6, %r11
	rldicl %r11, %r11, 1, 63
	subf %r10, %r11, %r10
	rldicl %r10, %r10, 1, 63
	rldicl %r8, %r7, 63, 1
	rldicl %r11, %r5, 63, 1
	subf %r8, %r11, %r8
	and %r11, %r7, %r12
	and %r6, %r5, %r12
	subf %r11, %r6, %r11
	rldicl %r11, %r11, 1, 63
	subf %r8, %r11, %r8
	rldicl %r8, %r8, 1, 63
	cmpldi %cr0, %r10, 0
	bne %cr0, 20f
	std %r24, 576(%r3)
	std %r25, 584(%r3)
	std %r26, 592(%r3)
	mflr %r0
	std %r0, 600(%r3)
	addi %r24, %r3, 0
	addi %r25, %r4, 0
	addi %r26, %r5, 0
	subf %r9, %r5, %r9
	std %r9, 608(%r24)
	cmpldi %cr0, %r8, 0
	bne %cr0, 22f
	b 23f
22:
	addi %r5, %r7, 0
23:
	addi %r4, %r24, 128
	subf %r4, %r7, %r4
	cmpldi %cr0, %r5, 0
	beq %cr0, 24f
26:
	lbz %r9, 0(%r25)
	lbz %r10, 0(%r4)
	xor %r9, %r9, %r10
	stb %r9, 0(%r25)
	addi %r25, %r25, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	addi %r26, %r26, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 26b
	b 25f
24:
25:
	rldicl %r5, %r26, 58, 6
	rldicr %r5, %r5, 6, 57
	cmpldi %cr0, %r5, 0
	beq %cr0, 27f
	ld %r9, 0(%r24)
	ld %r10, 8(%r24)
	ld %r11, 16(%r24)
	ld %r12, 24(%r24)
	std %r9, 192(%r24)
	std %r10, 200(%r24)
	std %r11, 208(%r24)
	std %r12, 216(%r24)
	ld %r9, 32(%r24)
	ld %r10, 40(%r24)
	ld %r11, 48(%r24)
	ld %r12, 56(%r24)
	std %r9, 224(%r24)
	std %r10, 232(%r24)
	std %r11, 240(%r24)
	std %r12, 248(%r24)
	rldicl %r9, %r5, 58, 6
	lwz %r10, 48(%r24)
	add %r10, %r10, %r9
	stw %r10, 48(%r24)
	addi %r3, %r24, 192
	addi %r4, %r25, 0
	addi %r6, %r24, 256
	add %r25, %r25, %r5
	subf %r26, %r5, %r26
	bl {vg_chacha20_xor}
	b 28f
27:
28:
	cmpldi %cr0, %r26, 0
	beq %cr0, 29f
	addi %r3, %r24, 0
	addi %r4, %r24, 64
	bl {vg_chacha20_block}
	lwz %r9, 48(%r24)
	addi %r9, %r9, 1
	stw %r9, 48(%r24)
	addi %r4, %r24, 64
	addi %r5, %r26, 0
	cmpldi %cr0, %r5, 0
	beq %cr0, 211f
213:
	lbz %r9, 0(%r25)
	lbz %r10, 0(%r4)
	xor %r9, %r9, %r10
	stb %r9, 0(%r25)
	addi %r25, %r25, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	addi %r26, %r26, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 213b
	b 212f
211:
212:
	b 210f
29:
210:
	ld %r9, 608(%r24)
	std %r9, 128(%r24)
	ld %r0, 600(%r24)
	mtlr %r0
	ld %r25, 584(%r24)
	ld %r26, 592(%r24)
	ld %r24, 576(%r24)
	li %r3, 1
	b 21f
20:
	li %r3, 0
21:
	blr
