// The functions of `src/sha512.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_compress:
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
	beq %cr0, 20f
22:
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
23:
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
	bne %cr0, 23b
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
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r14, 128(%r6)
	ld %r15, 136(%r6)
	ld %r16, 144(%r6)
	ld %r17, 152(%r6)
	ld %r19, 160(%r6)
	ld %r18, 8(%r6)
	blr

vg_sha384_init:
	lis %r8, -13381
	ori %r8, %r8, 40285
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 49413
	ori %r8, %r8, 40664
	std %r8, 0(%r3)
	lis %r8, 25242
	ori %r8, %r8, 10538
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 13948
	ori %r8, %r8, 54535
	std %r8, 8(%r3)
	lis %r8, -28327
	ori %r8, %r8, 346
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 12400
	ori %r8, %r8, 56599
	std %r8, 16(%r3)
	lis %r8, 5423
	ori %r8, %r8, 60632
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 63246
	ori %r8, %r8, 22841
	std %r8, 24(%r3)
	lis %r8, 26419
	ori %r8, %r8, 9831
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 65472
	ori %r8, %r8, 2865
	std %r8, 32(%r3)
	lis %r8, -29004
	ori %r8, %r8, 19079
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 26712
	ori %r8, %r8, 5393
	std %r8, 40(%r3)
	lis %r8, -9460
	ori %r8, %r8, 11789
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 25849
	ori %r8, %r8, 36775
	std %r8, 48(%r3)
	lis %r8, 18357
	ori %r8, %r8, 18461
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 48890
	ori %r8, %r8, 20388
	std %r8, 56(%r3)
	blr

vg_sha512_init:
	lis %r8, 27145
	ori %r8, %r8, 58983
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 62396
	ori %r8, %r8, 51464
	std %r8, 0(%r3)
	lis %r8, -17561
	ori %r8, %r8, 44677
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 33994
	ori %r8, %r8, 42811
	std %r8, 8(%r3)
	lis %r8, 15470
	ori %r8, %r8, 62322
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 65172
	ori %r8, %r8, 63531
	std %r8, 16(%r3)
	lis %r8, -23217
	ori %r8, %r8, 62778
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 24349
	ori %r8, %r8, 14065
	std %r8, 24(%r3)
	lis %r8, 20750
	ori %r8, %r8, 21119
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 44518
	ori %r8, %r8, 33489
	std %r8, 32(%r3)
	lis %r8, -25851
	ori %r8, %r8, 26764
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 11070
	ori %r8, %r8, 27679
	std %r8, 40(%r3)
	lis %r8, 8067
	ori %r8, %r8, 55723
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 64321
	ori %r8, %r8, 48491
	std %r8, 48(%r3)
	lis %r8, 23520
	ori %r8, %r8, 52505
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 4990
	ori %r8, %r8, 8569
	std %r8, 56(%r3)
	blr

vg_sha512_224_init:
	lis %r8, -29635
	ori %r8, %r8, 14280
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 6484
	ori %r8, %r8, 19874
	std %r8, 0(%r3)
	lis %r8, 29665
	ori %r8, %r8, 39270
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 35292
	ori %r8, %r8, 54486
	std %r8, 8(%r3)
	lis %r8, 7674
	ori %r8, %r8, 47022
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 13055
	ori %r8, %r8, 40066
	std %r8, 16(%r3)
	lis %r8, 26525
	ori %r8, %r8, 54548
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 22575
	ori %r8, %r8, 40911
	std %r8, 24(%r3)
	lis %r8, 3949
	ori %r8, %r8, 11113
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 31700
	ori %r8, %r8, 19880
	std %r8, 32(%r3)
	lis %r8, 30691
	ori %r8, %r8, 28531
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 1220
	ori %r8, %r8, 35138
	std %r8, 40(%r3)
	lis %r8, 16285
	ori %r8, %r8, 34216
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 27165
	ori %r8, %r8, 14024
	std %r8, 48(%r3)
	lis %r8, 4370
	ori %r8, %r8, 59053
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 37334
	ori %r8, %r8, 37537
	std %r8, 56(%r3)
	blr

vg_sha512_256_init:
	lis %r8, 8753
	ori %r8, %r8, 8596
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 64555
	ori %r8, %r8, 63276
	std %r8, 0(%r3)
	lis %r8, -24747
	ori %r8, %r8, 24483
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 51276
	ori %r8, %r8, 25794
	std %r8, 8(%r3)
	lis %r8, 9107
	ori %r8, %r8, 47211
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 28499
	ori %r8, %r8, 45393
	std %r8, 16(%r3)
	lis %r8, -27080
	ori %r8, %r8, 30489
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 22848
	ori %r8, %r8, 60093
	std %r8, 24(%r3)
	lis %r8, -27096
	ori %r8, %r8, 16098
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 43150
	ori %r8, %r8, 65507
	std %r8, 32(%r3)
	lis %r8, -16802
	ori %r8, %r8, 7717
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 21382
	ori %r8, %r8, 14738
	std %r8, 40(%r3)
	lis %r8, 11009
	ori %r8, %r8, 39420
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 11397
	ori %r8, %r8, 47274
	std %r8, 48(%r3)
	lis %r8, 3767
	ori %r8, %r8, 11740
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 33221
	ori %r8, %r8, 11426
	std %r8, 56(%r3)
	blr

vg_sha512_update:
	stdu %r1, -1408(%r1)
	addi %r7, %r1, 32
	std %r26, 176(%r7)
	std %r27, 184(%r7)
	std %r28, 192(%r7)
	std %r29, 200(%r7)
	std %r30, 208(%r7)
	std %r31, 216(%r7)
	addi %r26, %r3, 0
	addi %r27, %r7, 0
	addi %r28, %r5, 0
	addi %r29, %r6, 0
	li %r8, 127
	and %r30, %r4, %r8
	cmpldi %cr0, %r29, 0
	beq %cr0, 20f
22:
	li %r9, 0
	cmpldi %cr0, %r30, 0
	beq %cr0, 23f
	li %r10, 128
	subf %r10, %r30, %r10
	rldicl %r8, %r29, 57, 7
	cmpldi %cr0, %r8, 0
	beq %cr0, 25f
	b 26f
25:
	add %r8, %r29, %r30
	rldicl %r8, %r8, 57, 7
	cmpldi %cr0, %r8, 0
	beq %cr0, 27f
	b 28f
27:
	addi %r10, %r29, 0
28:
26:
	subf %r29, %r10, %r29
29:
	lbz %r8, 0(%r28)
	add %r11, %r26, %r30
	stb %r8, 64(%r11)
	addi %r28, %r28, 1
	addi %r30, %r30, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 29b
	addi %r8, %r30, -128
	cmpldi %cr0, %r8, 0
	beq %cr0, 210f
	b 211f
210:
	addi %r4, %r26, 64
	li %r30, 0
	li %r9, 1
211:
	b 24f
23:
	rldicl %r8, %r29, 57, 7
	cmpldi %cr0, %r8, 0
	beq %cr0, 212f
	addi %r4, %r28, 0
	addi %r28, %r28, 128
	addi %r29, %r29, -128
	li %r9, 1
	b 213f
212:
	li %r10, 128
	subf %r10, %r30, %r10
	rldicl %r8, %r29, 57, 7
	cmpldi %cr0, %r8, 0
	beq %cr0, 214f
	b 215f
214:
	add %r8, %r29, %r30
	rldicl %r8, %r8, 57, 7
	cmpldi %cr0, %r8, 0
	beq %cr0, 216f
	b 217f
216:
	addi %r10, %r29, 0
217:
215:
	subf %r29, %r10, %r29
218:
	lbz %r8, 0(%r28)
	add %r11, %r26, %r30
	stb %r8, 64(%r11)
	addi %r28, %r28, 1
	addi %r30, %r30, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 218b
	addi %r8, %r30, -128
	cmpldi %cr0, %r8, 0
	beq %cr0, 219f
	b 220f
219:
	addi %r4, %r26, 64
	li %r30, 0
	li %r9, 1
220:
213:
24:
	cmpldi %cr0, %r9, 0
	beq %cr0, 221f
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
	beq %cr0, 223f
225:
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
226:
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
	bne %cr0, 226b
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
	bne %cr0, 225b
	b 224f
223:
224:
	ld %r14, 128(%r6)
	ld %r15, 136(%r6)
	ld %r16, 144(%r6)
	ld %r17, 152(%r6)
	ld %r19, 160(%r6)
	ld %r18, 8(%r6)
	b 222f
221:
222:
	cmpldi %cr0, %r29, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r26, 176(%r27)
	ld %r28, 192(%r27)
	ld %r29, 200(%r27)
	ld %r30, 208(%r27)
	ld %r31, 216(%r27)
	ld %r27, 184(%r27)
	addi %r1, %r1, 1408
	blr

vg_sha512_finalize:
	stdu %r1, -1408(%r1)
	addi %r6, %r1, 32
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
	addi %r1, %r1, 1408
	blr

vg_sha512_update_scratch:
	std %r26, 176(%r7)
	std %r27, 184(%r7)
	std %r28, 192(%r7)
	std %r29, 200(%r7)
	std %r30, 208(%r7)
	std %r31, 216(%r7)
	addi %r26, %r3, 0
	addi %r27, %r7, 0
	addi %r28, %r5, 0
	addi %r29, %r6, 0
	li %r8, 127
	and %r30, %r4, %r8
	cmpldi %cr0, %r29, 0
	beq %cr0, 20f
22:
	li %r9, 0
	cmpldi %cr0, %r30, 0
	beq %cr0, 23f
	li %r10, 128
	subf %r10, %r30, %r10
	rldicl %r8, %r29, 57, 7
	cmpldi %cr0, %r8, 0
	beq %cr0, 25f
	b 26f
25:
	add %r8, %r29, %r30
	rldicl %r8, %r8, 57, 7
	cmpldi %cr0, %r8, 0
	beq %cr0, 27f
	b 28f
27:
	addi %r10, %r29, 0
28:
26:
	subf %r29, %r10, %r29
29:
	lbz %r8, 0(%r28)
	add %r11, %r26, %r30
	stb %r8, 64(%r11)
	addi %r28, %r28, 1
	addi %r30, %r30, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 29b
	addi %r8, %r30, -128
	cmpldi %cr0, %r8, 0
	beq %cr0, 210f
	b 211f
210:
	addi %r4, %r26, 64
	li %r30, 0
	li %r9, 1
211:
	b 24f
23:
	rldicl %r8, %r29, 57, 7
	cmpldi %cr0, %r8, 0
	beq %cr0, 212f
	addi %r4, %r28, 0
	addi %r28, %r28, 128
	addi %r29, %r29, -128
	li %r9, 1
	b 213f
212:
	li %r10, 128
	subf %r10, %r30, %r10
	rldicl %r8, %r29, 57, 7
	cmpldi %cr0, %r8, 0
	beq %cr0, 214f
	b 215f
214:
	add %r8, %r29, %r30
	rldicl %r8, %r8, 57, 7
	cmpldi %cr0, %r8, 0
	beq %cr0, 216f
	b 217f
216:
	addi %r10, %r29, 0
217:
215:
	subf %r29, %r10, %r29
218:
	lbz %r8, 0(%r28)
	add %r11, %r26, %r30
	stb %r8, 64(%r11)
	addi %r28, %r28, 1
	addi %r30, %r30, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 218b
	addi %r8, %r30, -128
	cmpldi %cr0, %r8, 0
	beq %cr0, 219f
	b 220f
219:
	addi %r4, %r26, 64
	li %r30, 0
	li %r9, 1
220:
213:
24:
	cmpldi %cr0, %r9, 0
	beq %cr0, 221f
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
	beq %cr0, 223f
225:
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
226:
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
	bne %cr0, 226b
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
	bne %cr0, 225b
	b 224f
223:
224:
	ld %r14, 128(%r6)
	ld %r15, 136(%r6)
	ld %r16, 144(%r6)
	ld %r17, 152(%r6)
	ld %r19, 160(%r6)
	ld %r18, 8(%r6)
	b 222f
221:
222:
	cmpldi %cr0, %r29, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r26, 176(%r27)
	ld %r28, 192(%r27)
	ld %r29, 200(%r27)
	ld %r30, 208(%r27)
	ld %r31, 216(%r27)
	ld %r27, 184(%r27)
	blr

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

vg_sha384_finalize:
	stdu %r1, -1408(%r1)
	addi %r6, %r1, 32
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
	ld %r26, 176(%r27)
	ld %r28, 192(%r27)
	ld %r29, 200(%r27)
	ld %r30, 208(%r27)
	ld %r31, 216(%r27)
	ld %r27, 184(%r27)
	addi %r1, %r1, 1408
	blr

vg_sha512_256_finalize:
	stdu %r1, -1408(%r1)
	addi %r6, %r1, 32
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
	ld %r26, 176(%r27)
	ld %r28, 192(%r27)
	ld %r29, 200(%r27)
	ld %r30, 208(%r27)
	ld %r31, 216(%r27)
	ld %r27, 184(%r27)
	addi %r1, %r1, 1408
	blr

vg_sha512_224_finalize:
	stdu %r1, -1408(%r1)
	addi %r6, %r1, 32
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
	lwz %r8, 28(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	ld %r26, 176(%r27)
	ld %r28, 192(%r27)
	ld %r29, 200(%r27)
	ld %r30, 208(%r27)
	ld %r31, 216(%r27)
	ld %r27, 184(%r27)
	addi %r1, %r1, 1408
	blr
