// The functions of `src/aes_xts.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

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
	li %r0, 0
	li %r3, 0
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v9, %v9, %v9
	vxor %v10, %v10, %v10
	vxor %v11, %v11, %v11
	vxor %v12, %v12, %v12
	vxor %v13, %v13, %v13
	vxor %v14, %v14, %v14
	vxor %v15, %v15, %v15
	vxor %v16, %v16, %v16
	vxor %v17, %v17, %v17
	vxor %v18, %v18, %v18
	vxor %v19, %v19, %v19
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
	li %r0, 0
	li %r3, 0
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v9, %v9, %v9
	vxor %v10, %v10, %v10
	vxor %v11, %v11, %v11
	vxor %v12, %v12, %v12
	vxor %v13, %v13, %v13
	vxor %v14, %v14, %v14
	vxor %v15, %v15, %v15
	vxor %v16, %v16, %v16
	vxor %v17, %v17, %v17
	vxor %v18, %v18, %v18
	vxor %v19, %v19, %v19
	blr
