// The functions of `src/internal/vg_sha512_finalize_scratch.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_finalize_scratch:
	std %r26, 176(%r6)
	std %r27, 184(%r6)
	std %r28, 192(%r6)
	std %r29, 200(%r6)
	std %r30, 208(%r6)
	std %r31, 216(%r6)
	addi %r26, %r3, 0
	addi %r27, %r6, 0
	addi %r28, %r5, 0
	addi %r29, %r4, 0
	li %r8, 127
	and %r30, %r29, %r8
	li %r8, 128
	add %r11, %r26, %r30
	stb %r8, 64(%r11)
	addi %r30, %r30, 1
	addi %r31, %r30, 15
	rldicl %r31, %r31, 57, 7
20:
	li %r10, 128
	cmpldi %cr0, %r31, 0
	beq %cr0, 21f
	b 22f
21:
	li %r10, 112
22:
	li %r8, 0
	subf %r10, %r30, %r10
	cmpldi %cr0, %r10, 0
	beq %cr0, 23f
25:
	add %r11, %r26, %r30
	stb %r8, 64(%r11)
	addi %r30, %r30, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 25b
	b 24f
23:
24:
	cmpldi %cr0, %r31, 0
	beq %cr0, 26f
	b 27f
26:
	rldicl %r8, %r29, 3, 61
	li %r11, 176
	stdbrx %r8, %r26, %r11
	add %r8, %r29, %r29
	add %r8, %r8, %r8
	add %r8, %r8, %r8
	li %r11, 184
	stdbrx %r8, %r26, %r11
27:
	addi %r4, %r26, 64
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	std %r18, 8(%r6)
	mflr %r0
	bcl 20, 31, 2f
2:
	mflr %r18
	addis %r18, %r18, ({VG_SHA512_PPC64LE_K}
	addi %r18, %r18, ({VG_SHA512_PPC64LE_K}
	mtlr %r0
	std %r14, 128(%r6)
	std %r15, 136(%r6)
	std %r16, 144(%r6)
	std %r17, 152(%r6)
	std %r19, 160(%r6)
	cmpldi %cr0, %r5, 0
	beq %cr0, 28f
210:
	ld %r17, 0(%r3)
	mtvsrd 36, %r17
	ld %r17, 8(%r3)
	mtvsrd 37, %r17
	ld %r17, 16(%r3)
	mtvsrd 38, %r17
	ld %r17, 24(%r3)
	mtvsrd 39, %r17
	ld %r17, 32(%r3)
	mtvsrd 40, %r17
	ld %r17, 40(%r3)
	mtvsrd 41, %r17
	ld %r17, 48(%r3)
	mtvsrd 42, %r17
	ld %r17, 56(%r3)
	mtvsrd 43, %r17
	lis %r16, 17034
	ori %r16, %r16, 12184
	rldicr %r16, %r16, 32, 31
	oris %r16, %r16, 55080
	ori %r16, %r16, 44578
	mtvsrd 44, %r16
	vaddudm %v11, %v11, %v12
	li %r19, 8
	li %r0, 0
	ldbrx %r16, %r4, %r0
	li %r0, 8
	ldbrx %r17, %r4, %r0
	mtvsrd 32, %r16
	mtvsrd 44, %r17
	vsldoi %v0, %v0, %v0, 8
	vsldoi %v0, %v0, %v12, 8
	vor %v15, %v0, %v0
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v8, 1, 8
	vsel %v13, %v10, %v9, %v8
	vaddudm %v10, %v10, %v14
	vshasigmad %v14, %v4, 1, 0
	vaddudm %v15, %v11, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v7, %v7, %v15
	vxor %v12, %v4, %v5
	vsel %v12, %v5, %v6, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v11, %v15, %v14
	vsldoi %v15, %v0, %v0, 8
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v7, 1, 8
	vsel %v13, %v9, %v8, %v7
	vaddudm %v9, %v9, %v14
	vshasigmad %v14, %v11, 1, 0
	vaddudm %v15, %v10, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v6, %v6, %v15
	vxor %v12, %v11, %v4
	vsel %v12, %v4, %v5, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v10, %v15, %v14
	li %r0, 16
	ldbrx %r16, %r4, %r0
	li %r0, 24
	ldbrx %r17, %r4, %r0
	mtvsrd 33, %r16
	mtvsrd 44, %r17
	vsldoi %v1, %v1, %v1, 8
	vsldoi %v1, %v1, %v12, 8
	vor %v15, %v1, %v1
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v6, 1, 8
	vsel %v13, %v8, %v7, %v6
	vaddudm %v8, %v8, %v14
	vshasigmad %v14, %v10, 1, 0
	vaddudm %v15, %v9, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v5, %v5, %v15
	vxor %v12, %v10, %v11
	vsel %v12, %v11, %v4, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v9, %v15, %v14
	vsldoi %v15, %v1, %v1, 8
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v5, 1, 8
	vsel %v13, %v7, %v6, %v5
	vaddudm %v7, %v7, %v14
	vshasigmad %v14, %v9, 1, 0
	vaddudm %v15, %v8, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v4, %v4, %v15
	vxor %v12, %v9, %v10
	vsel %v12, %v10, %v11, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v8, %v15, %v14
	li %r0, 32
	ldbrx %r16, %r4, %r0
	li %r0, 40
	ldbrx %r17, %r4, %r0
	mtvsrd 34, %r16
	mtvsrd 44, %r17
	vsldoi %v2, %v2, %v2, 8
	vsldoi %v2, %v2, %v12, 8
	vor %v15, %v2, %v2
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v4, 1, 8
	vsel %v13, %v6, %v5, %v4
	vaddudm %v6, %v6, %v14
	vshasigmad %v14, %v8, 1, 0
	vaddudm %v15, %v7, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v11, %v11, %v15
	vxor %v12, %v8, %v9
	vsel %v12, %v9, %v10, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v7, %v15, %v14
	vsldoi %v15, %v2, %v2, 8
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v11, 1, 8
	vsel %v13, %v5, %v4, %v11
	vaddudm %v5, %v5, %v14
	vshasigmad %v14, %v7, 1, 0
	vaddudm %v15, %v6, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v10, %v10, %v15
	vxor %v12, %v7, %v8
	vsel %v12, %v8, %v9, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v6, %v15, %v14
	li %r0, 48
	ldbrx %r16, %r4, %r0
	li %r0, 56
	ldbrx %r17, %r4, %r0
	mtvsrd 35, %r16
	mtvsrd 44, %r17
	vsldoi %v3, %v3, %v3, 8
	vsldoi %v3, %v3, %v12, 8
	vor %v15, %v3, %v3
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v10, 1, 8
	vsel %v13, %v4, %v11, %v10
	vaddudm %v4, %v4, %v14
	vshasigmad %v14, %v6, 1, 0
	vaddudm %v15, %v5, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v9, %v9, %v15
	vxor %v12, %v6, %v7
	vsel %v12, %v7, %v8, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v5, %v15, %v14
	vsldoi %v15, %v3, %v3, 8
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v9, 1, 8
	vsel %v13, %v11, %v10, %v9
	vaddudm %v11, %v11, %v14
	vshasigmad %v14, %v5, 1, 0
	vaddudm %v15, %v4, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v8, %v8, %v15
	vxor %v12, %v5, %v6
	vsel %v12, %v6, %v7, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v4, %v15, %v14
	li %r0, 64
	ldbrx %r16, %r4, %r0
	li %r0, 72
	ldbrx %r17, %r4, %r0
	mtvsrd 48, %r16
	mtvsrd 44, %r17
	vsldoi %v16, %v16, %v16, 8
	vsldoi %v16, %v16, %v12, 8
	vor %v15, %v16, %v16
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v8, 1, 8
	vsel %v13, %v10, %v9, %v8
	vaddudm %v10, %v10, %v14
	vshasigmad %v14, %v4, 1, 0
	vaddudm %v15, %v11, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v7, %v7, %v15
	vxor %v12, %v4, %v5
	vsel %v12, %v5, %v6, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v11, %v15, %v14
	vsldoi %v15, %v16, %v16, 8
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v7, 1, 8
	vsel %v13, %v9, %v8, %v7
	vaddudm %v9, %v9, %v14
	vshasigmad %v14, %v11, 1, 0
	vaddudm %v15, %v10, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v6, %v6, %v15
	vxor %v12, %v11, %v4
	vsel %v12, %v4, %v5, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v10, %v15, %v14
	li %r0, 80
	ldbrx %r16, %r4, %r0
	li %r0, 88
	ldbrx %r17, %r4, %r0
	mtvsrd 49, %r16
	mtvsrd 44, %r17
	vsldoi %v17, %v17, %v17, 8
	vsldoi %v17, %v17, %v12, 8
	vor %v15, %v17, %v17
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v6, 1, 8
	vsel %v13, %v8, %v7, %v6
	vaddudm %v8, %v8, %v14
	vshasigmad %v14, %v10, 1, 0
	vaddudm %v15, %v9, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v5, %v5, %v15
	vxor %v12, %v10, %v11
	vsel %v12, %v11, %v4, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v9, %v15, %v14
	vsldoi %v15, %v17, %v17, 8
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v5, 1, 8
	vsel %v13, %v7, %v6, %v5
	vaddudm %v7, %v7, %v14
	vshasigmad %v14, %v9, 1, 0
	vaddudm %v15, %v8, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v4, %v4, %v15
	vxor %v12, %v9, %v10
	vsel %v12, %v10, %v11, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v8, %v15, %v14
	li %r0, 96
	ldbrx %r16, %r4, %r0
	li %r0, 104
	ldbrx %r17, %r4, %r0
	mtvsrd 50, %r16
	mtvsrd 44, %r17
	vsldoi %v18, %v18, %v18, 8
	vsldoi %v18, %v18, %v12, 8
	vor %v15, %v18, %v18
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v4, 1, 8
	vsel %v13, %v6, %v5, %v4
	vaddudm %v6, %v6, %v14
	vshasigmad %v14, %v8, 1, 0
	vaddudm %v15, %v7, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v11, %v11, %v15
	vxor %v12, %v8, %v9
	vsel %v12, %v9, %v10, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v7, %v15, %v14
	vsldoi %v15, %v18, %v18, 8
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v11, 1, 8
	vsel %v13, %v5, %v4, %v11
	vaddudm %v5, %v5, %v14
	vshasigmad %v14, %v7, 1, 0
	vaddudm %v15, %v6, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v10, %v10, %v15
	vxor %v12, %v7, %v8
	vsel %v12, %v8, %v9, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v6, %v15, %v14
	li %r0, 112
	ldbrx %r16, %r4, %r0
	li %r0, 120
	ldbrx %r17, %r4, %r0
	mtvsrd 51, %r16
	mtvsrd 44, %r17
	vsldoi %v19, %v19, %v19, 8
	vsldoi %v19, %v19, %v12, 8
	vor %v15, %v19, %v19
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v10, 1, 8
	vsel %v13, %v4, %v11, %v10
	vaddudm %v4, %v4, %v14
	vshasigmad %v14, %v6, 1, 0
	vaddudm %v15, %v5, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v9, %v9, %v15
	vxor %v12, %v6, %v7
	vsel %v12, %v7, %v8, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v5, %v15, %v14
	vsldoi %v15, %v19, %v19, 8
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v9, 1, 8
	vsel %v13, %v11, %v10, %v9
	vaddudm %v11, %v11, %v14
	vshasigmad %v14, %v5, 1, 0
	vaddudm %v15, %v4, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v8, %v8, %v15
	vxor %v12, %v5, %v6
	vsel %v12, %v6, %v7, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v4, %v15, %v14
	li %r14, 4
211:
	vshasigmad %v12, %v19, 0, 10
	vsldoi %v13, %v0, %v1, 8
	vshasigmad %v13, %v13, 0, 0
	vsldoi %v14, %v16, %v17, 8
	vaddudm %v12, %v12, %v0
	vaddudm %v12, %v12, %v13
	vaddudm %v0, %v12, %v14
	vor %v15, %v0, %v0
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v8, 1, 8
	vsel %v13, %v10, %v9, %v8
	vaddudm %v10, %v10, %v14
	vshasigmad %v14, %v4, 1, 0
	vaddudm %v15, %v11, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v7, %v7, %v15
	vxor %v12, %v4, %v5
	vsel %v12, %v5, %v6, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v11, %v15, %v14
	vsldoi %v15, %v0, %v0, 8
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v7, 1, 8
	vsel %v13, %v9, %v8, %v7
	vaddudm %v9, %v9, %v14
	vshasigmad %v14, %v11, 1, 0
	vaddudm %v15, %v10, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v6, %v6, %v15
	vxor %v12, %v11, %v4
	vsel %v12, %v4, %v5, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v10, %v15, %v14
	vshasigmad %v12, %v0, 0, 10
	vsldoi %v13, %v1, %v2, 8
	vshasigmad %v13, %v13, 0, 0
	vsldoi %v14, %v17, %v18, 8
	vaddudm %v12, %v12, %v1
	vaddudm %v12, %v12, %v13
	vaddudm %v1, %v12, %v14
	vor %v15, %v1, %v1
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v6, 1, 8
	vsel %v13, %v8, %v7, %v6
	vaddudm %v8, %v8, %v14
	vshasigmad %v14, %v10, 1, 0
	vaddudm %v15, %v9, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v5, %v5, %v15
	vxor %v12, %v10, %v11
	vsel %v12, %v11, %v4, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v9, %v15, %v14
	vsldoi %v15, %v1, %v1, 8
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v5, 1, 8
	vsel %v13, %v7, %v6, %v5
	vaddudm %v7, %v7, %v14
	vshasigmad %v14, %v9, 1, 0
	vaddudm %v15, %v8, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v4, %v4, %v15
	vxor %v12, %v9, %v10
	vsel %v12, %v10, %v11, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v8, %v15, %v14
	vshasigmad %v12, %v1, 0, 10
	vsldoi %v13, %v2, %v3, 8
	vshasigmad %v13, %v13, 0, 0
	vsldoi %v14, %v18, %v19, 8
	vaddudm %v12, %v12, %v2
	vaddudm %v12, %v12, %v13
	vaddudm %v2, %v12, %v14
	vor %v15, %v2, %v2
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v4, 1, 8
	vsel %v13, %v6, %v5, %v4
	vaddudm %v6, %v6, %v14
	vshasigmad %v14, %v8, 1, 0
	vaddudm %v15, %v7, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v11, %v11, %v15
	vxor %v12, %v8, %v9
	vsel %v12, %v9, %v10, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v7, %v15, %v14
	vsldoi %v15, %v2, %v2, 8
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v11, 1, 8
	vsel %v13, %v5, %v4, %v11
	vaddudm %v5, %v5, %v14
	vshasigmad %v14, %v7, 1, 0
	vaddudm %v15, %v6, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v10, %v10, %v15
	vxor %v12, %v7, %v8
	vsel %v12, %v8, %v9, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v6, %v15, %v14
	vshasigmad %v12, %v2, 0, 10
	vsldoi %v13, %v3, %v16, 8
	vshasigmad %v13, %v13, 0, 0
	vsldoi %v14, %v19, %v0, 8
	vaddudm %v12, %v12, %v3
	vaddudm %v12, %v12, %v13
	vaddudm %v3, %v12, %v14
	vor %v15, %v3, %v3
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v10, 1, 8
	vsel %v13, %v4, %v11, %v10
	vaddudm %v4, %v4, %v14
	vshasigmad %v14, %v6, 1, 0
	vaddudm %v15, %v5, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v9, %v9, %v15
	vxor %v12, %v6, %v7
	vsel %v12, %v7, %v8, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v5, %v15, %v14
	vsldoi %v15, %v3, %v3, 8
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v9, 1, 8
	vsel %v13, %v11, %v10, %v9
	vaddudm %v11, %v11, %v14
	vshasigmad %v14, %v5, 1, 0
	vaddudm %v15, %v4, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v8, %v8, %v15
	vxor %v12, %v5, %v6
	vsel %v12, %v6, %v7, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v4, %v15, %v14
	vshasigmad %v12, %v3, 0, 10
	vsldoi %v13, %v16, %v17, 8
	vshasigmad %v13, %v13, 0, 0
	vsldoi %v14, %v0, %v1, 8
	vaddudm %v12, %v12, %v16
	vaddudm %v12, %v12, %v13
	vaddudm %v16, %v12, %v14
	vor %v15, %v16, %v16
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v8, 1, 8
	vsel %v13, %v10, %v9, %v8
	vaddudm %v10, %v10, %v14
	vshasigmad %v14, %v4, 1, 0
	vaddudm %v15, %v11, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v7, %v7, %v15
	vxor %v12, %v4, %v5
	vsel %v12, %v5, %v6, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v11, %v15, %v14
	vsldoi %v15, %v16, %v16, 8
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v7, 1, 8
	vsel %v13, %v9, %v8, %v7
	vaddudm %v9, %v9, %v14
	vshasigmad %v14, %v11, 1, 0
	vaddudm %v15, %v10, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v6, %v6, %v15
	vxor %v12, %v11, %v4
	vsel %v12, %v4, %v5, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v10, %v15, %v14
	vshasigmad %v12, %v16, 0, 10
	vsldoi %v13, %v17, %v18, 8
	vshasigmad %v13, %v13, 0, 0
	vsldoi %v14, %v1, %v2, 8
	vaddudm %v12, %v12, %v17
	vaddudm %v12, %v12, %v13
	vaddudm %v17, %v12, %v14
	vor %v15, %v17, %v17
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v6, 1, 8
	vsel %v13, %v8, %v7, %v6
	vaddudm %v8, %v8, %v14
	vshasigmad %v14, %v10, 1, 0
	vaddudm %v15, %v9, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v5, %v5, %v15
	vxor %v12, %v10, %v11
	vsel %v12, %v11, %v4, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v9, %v15, %v14
	vsldoi %v15, %v17, %v17, 8
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v5, 1, 8
	vsel %v13, %v7, %v6, %v5
	vaddudm %v7, %v7, %v14
	vshasigmad %v14, %v9, 1, 0
	vaddudm %v15, %v8, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v4, %v4, %v15
	vxor %v12, %v9, %v10
	vsel %v12, %v10, %v11, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v8, %v15, %v14
	vshasigmad %v12, %v17, 0, 10
	vsldoi %v13, %v18, %v19, 8
	vshasigmad %v13, %v13, 0, 0
	vsldoi %v14, %v2, %v3, 8
	vaddudm %v12, %v12, %v18
	vaddudm %v12, %v12, %v13
	vaddudm %v18, %v12, %v14
	vor %v15, %v18, %v18
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v4, 1, 8
	vsel %v13, %v6, %v5, %v4
	vaddudm %v6, %v6, %v14
	vshasigmad %v14, %v8, 1, 0
	vaddudm %v15, %v7, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v11, %v11, %v15
	vxor %v12, %v8, %v9
	vsel %v12, %v9, %v10, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v7, %v15, %v14
	vsldoi %v15, %v18, %v18, 8
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v11, 1, 8
	vsel %v13, %v5, %v4, %v11
	vaddudm %v5, %v5, %v14
	vshasigmad %v14, %v7, 1, 0
	vaddudm %v15, %v6, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v10, %v10, %v15
	vxor %v12, %v7, %v8
	vsel %v12, %v8, %v9, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v6, %v15, %v14
	vshasigmad %v12, %v18, 0, 10
	vsldoi %v13, %v19, %v0, 8
	vshasigmad %v13, %v13, 0, 0
	vsldoi %v14, %v3, %v16, 8
	vaddudm %v12, %v12, %v19
	vaddudm %v12, %v12, %v13
	vaddudm %v19, %v12, %v14
	vor %v15, %v19, %v19
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v10, 1, 8
	vsel %v13, %v4, %v11, %v10
	vaddudm %v4, %v4, %v14
	vshasigmad %v14, %v6, 1, 0
	vaddudm %v15, %v5, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v9, %v9, %v15
	vxor %v12, %v6, %v7
	vsel %v12, %v7, %v8, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v5, %v15, %v14
	vsldoi %v15, %v19, %v19, 8
	lxvd2x 46, %r18, %r19
	addi %r19, %r19, 8
	vshasigmad %v12, %v9, 1, 8
	vsel %v13, %v11, %v10, %v9
	vaddudm %v11, %v11, %v14
	vshasigmad %v14, %v5, 1, 0
	vaddudm %v15, %v4, %v15
	vaddudm %v15, %v15, %v13
	vaddudm %v15, %v15, %v12
	vaddudm %v8, %v8, %v15
	vxor %v12, %v5, %v6
	vsel %v12, %v6, %v7, %v12
	vaddudm %v14, %v14, %v12
	vaddudm %v4, %v15, %v14
	addi %r14, %r14, -1
	cmpldi %cr0, %r14, 0
	bne %cr0, 211b
	mfvsrd %r7, 36
	mfvsrd %r8, 37
	mfvsrd %r9, 38
	mfvsrd %r10, 39
	mfvsrd %r11, 40
	mfvsrd %r12, 41
	mfvsrd %r14, 42
	mfvsrd %r15, 43
	ld %r16, 0(%r3)
	ld %r17, 8(%r3)
	ld %r0, 16(%r3)
	ld %r19, 24(%r3)
	add %r7, %r7, %r16
	add %r8, %r8, %r17
	add %r9, %r9, %r0
	add %r10, %r10, %r19
	ld %r16, 32(%r3)
	ld %r17, 40(%r3)
	ld %r0, 48(%r3)
	ld %r19, 56(%r3)
	add %r11, %r11, %r16
	add %r12, %r12, %r17
	add %r14, %r14, %r0
	add %r15, %r15, %r19
	std %r7, 0(%r3)
	std %r8, 8(%r3)
	std %r9, 16(%r3)
	std %r10, 24(%r3)
	std %r11, 32(%r3)
	std %r12, 40(%r3)
	std %r14, 48(%r3)
	std %r15, 56(%r3)
	addi %r4, %r4, 128
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 210b
	b 29f
28:
29:
	ld %r14, 128(%r6)
	ld %r15, 136(%r6)
	ld %r16, 144(%r6)
	ld %r17, 152(%r6)
	ld %r19, 160(%r6)
	ld %r18, 8(%r6)
	li %r30, 0
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	beq %cr0, 20b
	ld %r8, 0(%r26)
	li %r11, 0
	stdbrx %r8, %r28, %r11
	ld %r8, 8(%r26)
	li %r11, 8
	stdbrx %r8, %r28, %r11
	ld %r8, 16(%r26)
	li %r11, 16
	stdbrx %r8, %r28, %r11
	ld %r8, 24(%r26)
	li %r11, 24
	stdbrx %r8, %r28, %r11
	ld %r8, 32(%r26)
	li %r11, 32
	stdbrx %r8, %r28, %r11
	ld %r8, 40(%r26)
	li %r11, 40
	stdbrx %r8, %r28, %r11
	ld %r8, 48(%r26)
	li %r11, 48
	stdbrx %r8, %r28, %r11
	ld %r8, 56(%r26)
	li %r11, 56
	stdbrx %r8, %r28, %r11
	ld %r26, 176(%r27)
	ld %r28, 192(%r27)
	ld %r29, 200(%r27)
	ld %r30, 208(%r27)
	ld %r31, 216(%r27)
	ld %r27, 184(%r27)
	blr
