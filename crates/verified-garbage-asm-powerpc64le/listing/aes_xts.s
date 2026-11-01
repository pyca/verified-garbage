// The functions of `src/aes_xts.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_xts_encrypt:
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
	ld %r9, 0(%r17)
	ld %r10, 0(%r16)
	xor %r9, %r9, %r10
	std %r9, 0(%r17)
	ld %r9, 8(%r17)
	ld %r10, 8(%r16)
	xor %r9, %r9, %r10
	std %r9, 8(%r17)
	or %r3, %r14, %r14
	or %r4, %r15, %r15
	or %r5, %r17, %r17
	li %r6, 1
	or %r7, %r19, %r19
	bl {vg_aes_encrypt_blocks}
	ld %r9, 0(%r17)
	ld %r10, 0(%r16)
	xor %r9, %r9, %r10
	std %r9, 0(%r17)
	ld %r9, 8(%r17)
	ld %r10, 8(%r16)
	xor %r9, %r9, %r10
	std %r9, 8(%r17)
	ld %r9, 0(%r16)
	ld %r10, 8(%r16)
	rldicl %r11, %r10, 1, 63
	li %r12, 0
	subf %r11, %r11, %r12
	li %r12, 135
	and %r11, %r11, %r12
	rldicl %r12, %r9, 1, 63
	rldicr %r9, %r9, 1, 62
	xor %r9, %r9, %r11
	rldicr %r10, %r10, 1, 62
	or %r10, %r10, %r12
	std %r9, 0(%r16)
	std %r10, 8(%r16)
	addi %r17, %r17, 16
	addi %r18, %r18, -1
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

vg_aes_xts_decrypt:
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
	ld %r9, 0(%r17)
	ld %r10, 0(%r16)
	xor %r9, %r9, %r10
	std %r9, 0(%r17)
	ld %r9, 8(%r17)
	ld %r10, 8(%r16)
	xor %r9, %r9, %r10
	std %r9, 8(%r17)
	or %r3, %r14, %r14
	or %r4, %r15, %r15
	or %r5, %r17, %r17
	li %r6, 1
	or %r7, %r19, %r19
	bl {vg_aes_decrypt_blocks}
	ld %r9, 0(%r17)
	ld %r10, 0(%r16)
	xor %r9, %r9, %r10
	std %r9, 0(%r17)
	ld %r9, 8(%r17)
	ld %r10, 8(%r16)
	xor %r9, %r9, %r10
	std %r9, 8(%r17)
	ld %r9, 0(%r16)
	ld %r10, 8(%r16)
	rldicl %r11, %r10, 1, 63
	li %r12, 0
	subf %r11, %r11, %r12
	li %r12, 135
	and %r11, %r11, %r12
	rldicl %r12, %r9, 1, 63
	rldicr %r9, %r9, 1, 62
	xor %r9, %r9, %r11
	rldicr %r10, %r10, 1, 62
	or %r10, %r10, %r12
	std %r9, 0(%r16)
	std %r10, 8(%r16)
	addi %r17, %r17, 16
	addi %r18, %r18, -1
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

vg_aes_xts_encrypt_unit:
	mflr %r0
	std %r0, 2256(%r9)
	std %r14, 2208(%r9)
	std %r15, 2216(%r9)
	std %r16, 2224(%r9)
	std %r17, 2232(%r9)
	std %r18, 2240(%r9)
	std %r19, 2248(%r9)
	or %r14, %r3, %r3
	or %r15, %r5, %r5
	or %r17, %r7, %r7
	or %r18, %r8, %r8
	or %r19, %r9, %r9
	ld %r9, 0(%r6)
	std %r9, 2176(%r19)
	ld %r9, 8(%r6)
	std %r9, 2184(%r19)
	li %r9, 0
	std %r9, 2192(%r19)
	std %r9, 2200(%r19)
	or %r3, %r4, %r4
	or %r4, %r15, %r15
	addi %r5, %r19, 2192
	addi %r6, %r19, 2176
	li %r7, 1
	or %r8, %r19, %r19
	bl {vg_aes_xts_encrypt}
	or %r3, %r14, %r14
	or %r4, %r15, %r15
	addi %r5, %r19, 2176
	or %r6, %r17, %r17
	rldicl %r7, %r18, 60, 4
	or %r8, %r19, %r19
	bl {vg_aes_xts_encrypt}
	rldicl %r10, %r18, 60, 4
	rldicr %r10, %r10, 4, 59
	subf %r11, %r10, %r18
	cmpldi %cr0, %r11, 0
	beq %cr0, 20f
	add %r12, %r17, %r10
	addi %r12, %r12, -16
22:
	lbz %r8, 0(%r12)
	lbz %r9, 16(%r12)
	stb %r9, 0(%r12)
	stb %r8, 16(%r12)
	addi %r12, %r12, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 22b
	add %r6, %r17, %r10
	addi %r6, %r6, -16
	or %r3, %r14, %r14
	or %r4, %r15, %r15
	addi %r5, %r19, 2176
	li %r7, 1
	or %r8, %r19, %r19
	bl {vg_aes_xts_encrypt}
	b 21f
20:
21:
	ld %r0, 2256(%r19)
	ld %r14, 2208(%r19)
	ld %r15, 2216(%r19)
	ld %r16, 2224(%r19)
	ld %r17, 2232(%r19)
	ld %r18, 2240(%r19)
	ld %r19, 2248(%r19)
	mtlr %r0
	blr

vg_aes_xts_decrypt_unit:
	mflr %r0
	std %r0, 2256(%r9)
	std %r14, 2208(%r9)
	std %r15, 2216(%r9)
	std %r16, 2224(%r9)
	std %r17, 2232(%r9)
	std %r18, 2240(%r9)
	std %r19, 2248(%r9)
	or %r14, %r3, %r3
	or %r15, %r5, %r5
	or %r17, %r7, %r7
	or %r18, %r8, %r8
	or %r19, %r9, %r9
	ld %r9, 0(%r6)
	std %r9, 2176(%r19)
	ld %r9, 8(%r6)
	std %r9, 2184(%r19)
	li %r9, 0
	std %r9, 2192(%r19)
	std %r9, 2200(%r19)
	or %r3, %r4, %r4
	or %r4, %r15, %r15
	addi %r5, %r19, 2192
	addi %r6, %r19, 2176
	li %r7, 1
	or %r8, %r19, %r19
	bl {vg_aes_xts_encrypt}
	rldicl %r10, %r18, 60, 4
	rldicr %r10, %r10, 4, 59
	subf %r11, %r10, %r18
	cmpldi %cr0, %r11, 0
	beq %cr0, 20f
	or %r3, %r14, %r14
	or %r4, %r15, %r15
	addi %r5, %r19, 2176
	or %r6, %r17, %r17
	rldicl %r7, %r18, 60, 4
	or %r8, %r19, %r19
	addi %r7, %r7, -1
	bl {vg_aes_xts_decrypt}
	addi %r16, %r19, 2192
	ld %r9, 2176(%r19)
	std %r9, 2192(%r19)
	ld %r9, 2184(%r19)
	std %r9, 2200(%r19)
	ld %r9, 0(%r16)
	ld %r10, 8(%r16)
	rldicl %r11, %r10, 1, 63
	li %r12, 0
	subf %r11, %r11, %r12
	li %r12, 135
	and %r11, %r11, %r12
	rldicl %r12, %r9, 1, 63
	rldicr %r9, %r9, 1, 62
	xor %r9, %r9, %r11
	rldicr %r10, %r10, 1, 62
	or %r10, %r10, %r12
	std %r9, 0(%r16)
	std %r10, 8(%r16)
	rldicl %r10, %r18, 60, 4
	rldicr %r10, %r10, 4, 59
	subf %r11, %r10, %r18
	add %r6, %r17, %r10
	addi %r6, %r6, -16
	or %r3, %r14, %r14
	or %r4, %r15, %r15
	addi %r5, %r19, 2192
	li %r7, 1
	or %r8, %r19, %r19
	bl {vg_aes_xts_decrypt}
	rldicl %r10, %r18, 60, 4
	rldicr %r10, %r10, 4, 59
	subf %r11, %r10, %r18
	add %r12, %r17, %r10
	addi %r12, %r12, -16
22:
	lbz %r8, 0(%r12)
	lbz %r9, 16(%r12)
	stb %r9, 0(%r12)
	stb %r8, 16(%r12)
	addi %r12, %r12, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 22b
	add %r6, %r17, %r10
	addi %r6, %r6, -16
	or %r3, %r14, %r14
	or %r4, %r15, %r15
	addi %r5, %r19, 2176
	li %r7, 1
	or %r8, %r19, %r19
	bl {vg_aes_xts_decrypt}
	b 21f
20:
	or %r3, %r14, %r14
	or %r4, %r15, %r15
	addi %r5, %r19, 2176
	or %r6, %r17, %r17
	rldicl %r7, %r18, 60, 4
	or %r8, %r19, %r19
	bl {vg_aes_xts_decrypt}
21:
	ld %r0, 2256(%r19)
	ld %r14, 2208(%r19)
	ld %r15, 2216(%r19)
	ld %r16, 2224(%r19)
	ld %r17, 2232(%r19)
	ld %r18, 2240(%r19)
	ld %r19, 2248(%r19)
	mtlr %r0
	blr
