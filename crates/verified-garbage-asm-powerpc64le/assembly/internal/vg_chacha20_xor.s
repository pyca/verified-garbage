// The functions of `src/internal/vg_chacha20_xor.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_xor:
	rldicl %r9, %r5, 56, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 20f
	mflr %r11
	bcl 20, 31, 2f
2:
	mflr %r10
	addis %r10, %r10, ({VG_CHACHA20_VMX4_CONSTS}
	addi %r10, %r10, ({VG_CHACHA20_VMX4_CONSTS}
22:
	li %r8, 0
	lxvd2x 48, %r3, %r8
	li %r8, 16
	lxvd2x 49, %r10, %r8
	vperm %v0, %v16, %v16, %v17
	li %r8, 0
	lxvd2x 48, %r3, %r8
	li %r8, 0
	lxvd2x 49, %r10, %r8
	vperm %v1, %v16, %v16, %v17
	li %r8, 0
	lxvd2x 48, %r3, %r8
	li %r8, 48
	lxvd2x 49, %r10, %r8
	vperm %v2, %v16, %v16, %v17
	li %r8, 0
	lxvd2x 48, %r3, %r8
	li %r8, 32
	lxvd2x 49, %r10, %r8
	vperm %v3, %v16, %v16, %v17
	li %r8, 16
	lxvd2x 48, %r3, %r8
	li %r8, 16
	lxvd2x 49, %r10, %r8
	vperm %v4, %v16, %v16, %v17
	li %r8, 16
	lxvd2x 48, %r3, %r8
	li %r8, 0
	lxvd2x 49, %r10, %r8
	vperm %v5, %v16, %v16, %v17
	li %r8, 16
	lxvd2x 48, %r3, %r8
	li %r8, 48
	lxvd2x 49, %r10, %r8
	vperm %v6, %v16, %v16, %v17
	li %r8, 16
	lxvd2x 48, %r3, %r8
	li %r8, 32
	lxvd2x 49, %r10, %r8
	vperm %v7, %v16, %v16, %v17
	li %r8, 32
	lxvd2x 48, %r3, %r8
	li %r8, 16
	lxvd2x 49, %r10, %r8
	vperm %v8, %v16, %v16, %v17
	li %r8, 32
	lxvd2x 48, %r3, %r8
	li %r8, 0
	lxvd2x 49, %r10, %r8
	vperm %v9, %v16, %v16, %v17
	li %r8, 32
	lxvd2x 48, %r3, %r8
	li %r8, 48
	lxvd2x 49, %r10, %r8
	vperm %v10, %v16, %v16, %v17
	li %r8, 32
	lxvd2x 48, %r3, %r8
	li %r8, 32
	lxvd2x 49, %r10, %r8
	vperm %v11, %v16, %v16, %v17
	li %r8, 48
	lxvd2x 48, %r3, %r8
	li %r8, 16
	lxvd2x 49, %r10, %r8
	vperm %v12, %v16, %v16, %v17
	li %r8, 48
	lxvd2x 48, %r3, %r8
	li %r8, 0
	lxvd2x 49, %r10, %r8
	vperm %v13, %v16, %v16, %v17
	li %r8, 48
	lxvd2x 48, %r3, %r8
	li %r8, 48
	lxvd2x 49, %r10, %r8
	vperm %v14, %v16, %v16, %v17
	li %r8, 48
	lxvd2x 48, %r3, %r8
	li %r8, 32
	lxvd2x 49, %r10, %r8
	vperm %v15, %v16, %v16, %v17
	li %r8, 64
	lxvd2x 48, %r10, %r8
	vadduwm %v12, %v12, %v16
	li %r8, 80
	lxvd2x 48, %r10, %r8
	li %r8, 96
	lxvd2x 49, %r10, %r8
	li %r8, 112
	lxvd2x 50, %r10, %r8
	li %r8, 128
	lxvd2x 51, %r10, %r8
	li %r12, 10
23:
	vadduwm %v0, %v0, %v4
	vadduwm %v1, %v1, %v5
	vadduwm %v2, %v2, %v6
	vadduwm %v3, %v3, %v7
	vxor %v12, %v12, %v0
	vrlw %v12, %v12, %v16
	vxor %v13, %v13, %v1
	vrlw %v13, %v13, %v16
	vxor %v14, %v14, %v2
	vrlw %v14, %v14, %v16
	vxor %v15, %v15, %v3
	vrlw %v15, %v15, %v16
	vadduwm %v8, %v8, %v12
	vadduwm %v9, %v9, %v13
	vadduwm %v10, %v10, %v14
	vadduwm %v11, %v11, %v15
	vxor %v4, %v4, %v8
	vrlw %v4, %v4, %v17
	vxor %v5, %v5, %v9
	vrlw %v5, %v5, %v17
	vxor %v6, %v6, %v10
	vrlw %v6, %v6, %v17
	vxor %v7, %v7, %v11
	vrlw %v7, %v7, %v17
	vadduwm %v0, %v0, %v4
	vadduwm %v1, %v1, %v5
	vadduwm %v2, %v2, %v6
	vadduwm %v3, %v3, %v7
	vxor %v12, %v12, %v0
	vrlw %v12, %v12, %v18
	vxor %v13, %v13, %v1
	vrlw %v13, %v13, %v18
	vxor %v14, %v14, %v2
	vrlw %v14, %v14, %v18
	vxor %v15, %v15, %v3
	vrlw %v15, %v15, %v18
	vadduwm %v8, %v8, %v12
	vadduwm %v9, %v9, %v13
	vadduwm %v10, %v10, %v14
	vadduwm %v11, %v11, %v15
	vxor %v4, %v4, %v8
	vrlw %v4, %v4, %v19
	vxor %v5, %v5, %v9
	vrlw %v5, %v5, %v19
	vxor %v6, %v6, %v10
	vrlw %v6, %v6, %v19
	vxor %v7, %v7, %v11
	vrlw %v7, %v7, %v19
	vadduwm %v0, %v0, %v5
	vadduwm %v1, %v1, %v6
	vadduwm %v2, %v2, %v7
	vadduwm %v3, %v3, %v4
	vxor %v15, %v15, %v0
	vrlw %v15, %v15, %v16
	vxor %v12, %v12, %v1
	vrlw %v12, %v12, %v16
	vxor %v13, %v13, %v2
	vrlw %v13, %v13, %v16
	vxor %v14, %v14, %v3
	vrlw %v14, %v14, %v16
	vadduwm %v10, %v10, %v15
	vadduwm %v11, %v11, %v12
	vadduwm %v8, %v8, %v13
	vadduwm %v9, %v9, %v14
	vxor %v5, %v5, %v10
	vrlw %v5, %v5, %v17
	vxor %v6, %v6, %v11
	vrlw %v6, %v6, %v17
	vxor %v7, %v7, %v8
	vrlw %v7, %v7, %v17
	vxor %v4, %v4, %v9
	vrlw %v4, %v4, %v17
	vadduwm %v0, %v0, %v5
	vadduwm %v1, %v1, %v6
	vadduwm %v2, %v2, %v7
	vadduwm %v3, %v3, %v4
	vxor %v15, %v15, %v0
	vrlw %v15, %v15, %v18
	vxor %v12, %v12, %v1
	vrlw %v12, %v12, %v18
	vxor %v13, %v13, %v2
	vrlw %v13, %v13, %v18
	vxor %v14, %v14, %v3
	vrlw %v14, %v14, %v18
	vadduwm %v10, %v10, %v15
	vadduwm %v11, %v11, %v12
	vadduwm %v8, %v8, %v13
	vadduwm %v9, %v9, %v14
	vxor %v5, %v5, %v10
	vrlw %v5, %v5, %v19
	vxor %v6, %v6, %v11
	vrlw %v6, %v6, %v19
	vxor %v7, %v7, %v8
	vrlw %v7, %v7, %v19
	vxor %v4, %v4, %v9
	vrlw %v4, %v4, %v19
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 23b
	li %r8, 0
	lxvd2x 48, %r3, %r8
	li %r8, 16
	lxvd2x 49, %r10, %r8
	vperm %v18, %v16, %v16, %v17
	vadduwm %v0, %v0, %v18
	li %r8, 0
	lxvd2x 48, %r3, %r8
	li %r8, 0
	lxvd2x 49, %r10, %r8
	vperm %v18, %v16, %v16, %v17
	vadduwm %v1, %v1, %v18
	li %r8, 0
	lxvd2x 48, %r3, %r8
	li %r8, 48
	lxvd2x 49, %r10, %r8
	vperm %v18, %v16, %v16, %v17
	vadduwm %v2, %v2, %v18
	li %r8, 0
	lxvd2x 48, %r3, %r8
	li %r8, 32
	lxvd2x 49, %r10, %r8
	vperm %v18, %v16, %v16, %v17
	vadduwm %v3, %v3, %v18
	li %r8, 16
	lxvd2x 48, %r3, %r8
	li %r8, 16
	lxvd2x 49, %r10, %r8
	vperm %v18, %v16, %v16, %v17
	vadduwm %v4, %v4, %v18
	li %r8, 16
	lxvd2x 48, %r3, %r8
	li %r8, 0
	lxvd2x 49, %r10, %r8
	vperm %v18, %v16, %v16, %v17
	vadduwm %v5, %v5, %v18
	li %r8, 16
	lxvd2x 48, %r3, %r8
	li %r8, 48
	lxvd2x 49, %r10, %r8
	vperm %v18, %v16, %v16, %v17
	vadduwm %v6, %v6, %v18
	li %r8, 16
	lxvd2x 48, %r3, %r8
	li %r8, 32
	lxvd2x 49, %r10, %r8
	vperm %v18, %v16, %v16, %v17
	vadduwm %v7, %v7, %v18
	li %r8, 32
	lxvd2x 48, %r3, %r8
	li %r8, 16
	lxvd2x 49, %r10, %r8
	vperm %v18, %v16, %v16, %v17
	vadduwm %v8, %v8, %v18
	li %r8, 32
	lxvd2x 48, %r3, %r8
	li %r8, 0
	lxvd2x 49, %r10, %r8
	vperm %v18, %v16, %v16, %v17
	vadduwm %v9, %v9, %v18
	li %r8, 32
	lxvd2x 48, %r3, %r8
	li %r8, 48
	lxvd2x 49, %r10, %r8
	vperm %v18, %v16, %v16, %v17
	vadduwm %v10, %v10, %v18
	li %r8, 32
	lxvd2x 48, %r3, %r8
	li %r8, 32
	lxvd2x 49, %r10, %r8
	vperm %v18, %v16, %v16, %v17
	vadduwm %v11, %v11, %v18
	li %r8, 48
	lxvd2x 48, %r3, %r8
	li %r8, 16
	lxvd2x 49, %r10, %r8
	vperm %v18, %v16, %v16, %v17
	vadduwm %v12, %v12, %v18
	li %r8, 64
	lxvd2x 49, %r10, %r8
	vadduwm %v12, %v12, %v17
	li %r8, 48
	lxvd2x 48, %r3, %r8
	li %r8, 0
	lxvd2x 49, %r10, %r8
	vperm %v18, %v16, %v16, %v17
	vadduwm %v13, %v13, %v18
	li %r8, 48
	lxvd2x 48, %r3, %r8
	li %r8, 48
	lxvd2x 49, %r10, %r8
	vperm %v18, %v16, %v16, %v17
	vadduwm %v14, %v14, %v18
	li %r8, 48
	lxvd2x 48, %r3, %r8
	li %r8, 32
	lxvd2x 49, %r10, %r8
	vperm %v18, %v16, %v16, %v17
	vadduwm %v15, %v15, %v18
	li %r8, 144
	lxvd2x 51, %r10, %r8
	vperm %v16, %v0, %v1, %v19
	vperm %v17, %v2, %v3, %v19
	li %r8, 160
	lxvd2x 51, %r10, %r8
	vperm %v18, %v0, %v1, %v19
	vperm %v0, %v2, %v3, %v19
	li %r8, 176
	lxvd2x 51, %r10, %r8
	vperm %v1, %v16, %v17, %v19
	vperm %v2, %v18, %v0, %v19
	li %r8, 192
	lxvd2x 51, %r10, %r8
	vperm %v3, %v16, %v17, %v19
	vperm %v16, %v18, %v0, %v19
	li %r8, 0
	lxvd2x 51, %r4, %r8
	vxor %v19, %v19, %v1
	stxvd2x 51, %r7, %r8
	li %r8, 64
	lxvd2x 51, %r4, %r8
	vxor %v19, %v19, %v3
	stxvd2x 51, %r7, %r8
	li %r8, 128
	lxvd2x 51, %r4, %r8
	vxor %v19, %v19, %v2
	stxvd2x 51, %r7, %r8
	li %r8, 192
	lxvd2x 51, %r4, %r8
	vxor %v19, %v19, %v16
	stxvd2x 51, %r7, %r8
	li %r8, 144
	lxvd2x 51, %r10, %r8
	vperm %v16, %v4, %v5, %v19
	vperm %v17, %v6, %v7, %v19
	li %r8, 160
	lxvd2x 51, %r10, %r8
	vperm %v18, %v4, %v5, %v19
	vperm %v4, %v6, %v7, %v19
	li %r8, 176
	lxvd2x 51, %r10, %r8
	vperm %v5, %v16, %v17, %v19
	vperm %v6, %v18, %v4, %v19
	li %r8, 192
	lxvd2x 51, %r10, %r8
	vperm %v7, %v16, %v17, %v19
	vperm %v16, %v18, %v4, %v19
	li %r8, 16
	lxvd2x 51, %r4, %r8
	vxor %v19, %v19, %v5
	stxvd2x 51, %r7, %r8
	li %r8, 80
	lxvd2x 51, %r4, %r8
	vxor %v19, %v19, %v7
	stxvd2x 51, %r7, %r8
	li %r8, 144
	lxvd2x 51, %r4, %r8
	vxor %v19, %v19, %v6
	stxvd2x 51, %r7, %r8
	li %r8, 208
	lxvd2x 51, %r4, %r8
	vxor %v19, %v19, %v16
	stxvd2x 51, %r7, %r8
	li %r8, 144
	lxvd2x 51, %r10, %r8
	vperm %v16, %v8, %v9, %v19
	vperm %v17, %v10, %v11, %v19
	li %r8, 160
	lxvd2x 51, %r10, %r8
	vperm %v18, %v8, %v9, %v19
	vperm %v8, %v10, %v11, %v19
	li %r8, 176
	lxvd2x 51, %r10, %r8
	vperm %v9, %v16, %v17, %v19
	vperm %v10, %v18, %v8, %v19
	li %r8, 192
	lxvd2x 51, %r10, %r8
	vperm %v11, %v16, %v17, %v19
	vperm %v16, %v18, %v8, %v19
	li %r8, 32
	lxvd2x 51, %r4, %r8
	vxor %v19, %v19, %v9
	stxvd2x 51, %r7, %r8
	li %r8, 96
	lxvd2x 51, %r4, %r8
	vxor %v19, %v19, %v11
	stxvd2x 51, %r7, %r8
	li %r8, 160
	lxvd2x 51, %r4, %r8
	vxor %v19, %v19, %v10
	stxvd2x 51, %r7, %r8
	li %r8, 224
	lxvd2x 51, %r4, %r8
	vxor %v19, %v19, %v16
	stxvd2x 51, %r7, %r8
	li %r8, 144
	lxvd2x 51, %r10, %r8
	vperm %v16, %v12, %v13, %v19
	vperm %v17, %v14, %v15, %v19
	li %r8, 160
	lxvd2x 51, %r10, %r8
	vperm %v18, %v12, %v13, %v19
	vperm %v12, %v14, %v15, %v19
	li %r8, 176
	lxvd2x 51, %r10, %r8
	vperm %v13, %v16, %v17, %v19
	vperm %v14, %v18, %v12, %v19
	li %r8, 192
	lxvd2x 51, %r10, %r8
	vperm %v15, %v16, %v17, %v19
	vperm %v16, %v18, %v12, %v19
	li %r8, 48
	lxvd2x 51, %r4, %r8
	vxor %v19, %v19, %v13
	stxvd2x 51, %r7, %r8
	li %r8, 112
	lxvd2x 51, %r4, %r8
	vxor %v19, %v19, %v15
	stxvd2x 51, %r7, %r8
	li %r8, 176
	lxvd2x 51, %r4, %r8
	vxor %v19, %v19, %v14
	stxvd2x 51, %r7, %r8
	li %r8, 240
	lxvd2x 51, %r4, %r8
	vxor %v19, %v19, %v16
	stxvd2x 51, %r7, %r8
	lwz %r8, 48(%r3)
	addi %r8, %r8, 4
	stw %r8, 48(%r3)
	addi %r4, %r4, 256
	addi %r7, %r7, 256
	addi %r5, %r5, -256
	rldicl %r9, %r5, 56, 8
	cmpldi %cr0, %r9, 0
	bne %cr0, 22b
	mtlr %r11
	b 21f
20:
21:
	std %r22, 256(%r6)
	std %r23, 264(%r6)
	mflr %r0
	std %r0, 272(%r6)
	std %r30, 280(%r6)
	addi %r22, %r4, 0
	addi %r23, %r5, 0
	addi %r30, %r7, 0
	addi %r4, %r6, 0
	cmpldi %cr0, %r23, 0
	beq %cr0, 24f
26:
	bl {vg_chacha20_block}
	rldicl %r9, %r23, 58, 6
	addi %r5, %r23, 0
	cmpldi %cr0, %r9, 0
	beq %cr0, 27f
	li %r5, 64
	b 28f
27:
28:
	subf %r23, %r5, %r23
	addi %r7, %r4, 0
	rldicl %r9, %r5, 58, 6
	cmpldi %cr0, %r9, 0
	beq %cr0, 29f
211:
	ld %r6, 0(%r22)
	ld %r8, 0(%r7)
	xor %r6, %r6, %r8
	std %r6, 0(%r30)
	addi %r22, %r22, 8
	addi %r30, %r30, 8
	addi %r7, %r7, 8
	addi %r5, %r5, -8
	cmpldi %cr0, %r5, 0
	bne %cr0, 211b
	b 210f
29:
212:
	lbz %r6, 0(%r22)
	lbz %r8, 0(%r7)
	xor %r6, %r6, %r8
	stb %r6, 0(%r30)
	addi %r22, %r22, 1
	addi %r30, %r30, 1
	addi %r7, %r7, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 212b
210:
	lwz %r8, 48(%r3)
	addi %r8, %r8, 1
	stw %r8, 48(%r3)
	cmpldi %cr0, %r23, 0
	bne %cr0, 26b
	b 25f
24:
25:
	ld %r0, 272(%r4)
	mtlr %r0
	ld %r22, 256(%r4)
	ld %r23, 264(%r4)
	ld %r30, 280(%r4)
	blr
