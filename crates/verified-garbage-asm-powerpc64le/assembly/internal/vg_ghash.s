// The functions of `src/internal/vg_ghash.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ghash:
	cmpldi %cr0, %r6, 0
	beq %cr0, 20f
	li %r0, 0
	vxor %v19, %v19, %v19
	lis %r8, -15872
	ori %r8, %r8, 0
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 0
	ori %r8, %r8, 0
	mtvsrd 33, %r8
	mtvsrd 39, %r8
	vsldoi %v1, %v19, %v1, 8
	vsldoi %v1, %v1, %v7, 8
	lis %r8, 3854
	ori %r8, %r8, 3340
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 2826
	ori %r8, %r8, 2312
	lis %r9, 1798
	ori %r9, %r9, 1284
	rldicr %r9, %r9, 32, 31
	oris %r9, %r9, 770
	ori %r9, %r9, 256
	mtvsrd 50, %r8
	mtvsrd 39, %r9
	vsldoi %v18, %v19, %v18, 8
	vsldoi %v18, %v18, %v7, 8
	lis %r8, 17920
	ori %r8, %r8, 0
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 0
	ori %r8, %r8, 0
	li %r9, 3
	mtvsrd 48, %r8
	mtvsrd 39, %r9
	vsldoi %v16, %v19, %v16, 8
	vsldoi %v16, %v16, %v7, 8
	lxvd2x 38, %r3, %r0
	vperm %v6, %v6, %v6, %v18
	vsldoi %v2, %v6, %v19, 8
	vpmsumd %v5, %v2, %v16
	vsldoi %v2, %v19, %v6, 8
	vpmsumd %v3, %v2, %v16
	vpmsumd %v4, %v6, %v16
	vsldoi %v7, %v3, %v19, 8
	vpmsumd %v7, %v7, %v1
	vsldoi %v3, %v3, %v3, 8
	vxor %v4, %v4, %v3
	vxor %v4, %v4, %v7
	vsldoi %v7, %v4, %v19, 8
	vpmsumd %v7, %v7, %v1
	vsldoi %v5, %v5, %v5, 8
	vxor %v5, %v5, %v4
	vsldoi %v7, %v7, %v7, 8
	vxor %v16, %v5, %v7
	vsldoi %v16, %v16, %v16, 8
	lxvd2x 32, %r4, %r0
	vperm %v0, %v0, %v0, %v18
	rldicl %r10, %r6, 60, 4
	cmpldi %cr0, %r10, 0
	beq %cr0, 22f
	vsldoi %v6, %v16, %v16, 8
	vsldoi %v2, %v6, %v19, 8
	vpmsumd %v5, %v2, %v16
	vsldoi %v2, %v19, %v6, 8
	vpmsumd %v3, %v2, %v16
	vpmsumd %v4, %v6, %v16
	vsldoi %v7, %v3, %v19, 8
	vpmsumd %v7, %v7, %v1
	vsldoi %v3, %v3, %v3, 8
	vxor %v4, %v4, %v3
	vxor %v4, %v4, %v7
	vsldoi %v7, %v4, %v19, 8
	vpmsumd %v7, %v7, %v1
	vsldoi %v5, %v5, %v5, 8
	vxor %v5, %v5, %v4
	vsldoi %v7, %v7, %v7, 8
	vxor %v8, %v5, %v7
	vsldoi %v8, %v8, %v8, 8
	vsldoi %v6, %v8, %v8, 8
	vsldoi %v2, %v6, %v19, 8
	vpmsumd %v5, %v2, %v16
	vsldoi %v2, %v19, %v6, 8
	vpmsumd %v3, %v2, %v16
	vpmsumd %v4, %v6, %v16
	vsldoi %v7, %v3, %v19, 8
	vpmsumd %v7, %v7, %v1
	vsldoi %v3, %v3, %v3, 8
	vxor %v4, %v4, %v3
	vxor %v4, %v4, %v7
	vsldoi %v7, %v4, %v19, 8
	vpmsumd %v7, %v7, %v1
	vsldoi %v5, %v5, %v5, 8
	vxor %v5, %v5, %v4
	vsldoi %v7, %v7, %v7, 8
	vxor %v9, %v5, %v7
	vsldoi %v9, %v9, %v9, 8
	vsldoi %v6, %v9, %v9, 8
	vsldoi %v2, %v6, %v19, 8
	vpmsumd %v5, %v2, %v16
	vsldoi %v2, %v19, %v6, 8
	vpmsumd %v3, %v2, %v16
	vpmsumd %v4, %v6, %v16
	vsldoi %v7, %v3, %v19, 8
	vpmsumd %v7, %v7, %v1
	vsldoi %v3, %v3, %v3, 8
	vxor %v4, %v4, %v3
	vxor %v4, %v4, %v7
	vsldoi %v7, %v4, %v19, 8
	vpmsumd %v7, %v7, %v1
	vsldoi %v5, %v5, %v5, 8
	vxor %v5, %v5, %v4
	vsldoi %v7, %v7, %v7, 8
	vxor %v10, %v5, %v7
	vsldoi %v10, %v10, %v10, 8
	vsldoi %v6, %v10, %v10, 8
	vsldoi %v2, %v6, %v19, 8
	vpmsumd %v5, %v2, %v16
	vsldoi %v2, %v19, %v6, 8
	vpmsumd %v3, %v2, %v16
	vpmsumd %v4, %v6, %v16
	vsldoi %v7, %v3, %v19, 8
	vpmsumd %v7, %v7, %v1
	vsldoi %v3, %v3, %v3, 8
	vxor %v4, %v4, %v3
	vxor %v4, %v4, %v7
	vsldoi %v7, %v4, %v19, 8
	vpmsumd %v7, %v7, %v1
	vsldoi %v5, %v5, %v5, 8
	vxor %v5, %v5, %v4
	vsldoi %v7, %v7, %v7, 8
	vxor %v11, %v5, %v7
	vsldoi %v11, %v11, %v11, 8
	vsldoi %v6, %v11, %v11, 8
	vsldoi %v2, %v6, %v19, 8
	vpmsumd %v5, %v2, %v16
	vsldoi %v2, %v19, %v6, 8
	vpmsumd %v3, %v2, %v16
	vpmsumd %v4, %v6, %v16
	vsldoi %v7, %v3, %v19, 8
	vpmsumd %v7, %v7, %v1
	vsldoi %v3, %v3, %v3, 8
	vxor %v4, %v4, %v3
	vxor %v4, %v4, %v7
	vsldoi %v7, %v4, %v19, 8
	vpmsumd %v7, %v7, %v1
	vsldoi %v5, %v5, %v5, 8
	vxor %v5, %v5, %v4
	vsldoi %v7, %v7, %v7, 8
	vxor %v12, %v5, %v7
	vsldoi %v12, %v12, %v12, 8
	vsldoi %v6, %v12, %v12, 8
	vsldoi %v2, %v6, %v19, 8
	vpmsumd %v5, %v2, %v16
	vsldoi %v2, %v19, %v6, 8
	vpmsumd %v3, %v2, %v16
	vpmsumd %v4, %v6, %v16
	vsldoi %v7, %v3, %v19, 8
	vpmsumd %v7, %v7, %v1
	vsldoi %v3, %v3, %v3, 8
	vxor %v4, %v4, %v3
	vxor %v4, %v4, %v7
	vsldoi %v7, %v4, %v19, 8
	vpmsumd %v7, %v7, %v1
	vsldoi %v5, %v5, %v5, 8
	vxor %v5, %v5, %v4
	vsldoi %v7, %v7, %v7, 8
	vxor %v13, %v5, %v7
	vsldoi %v13, %v13, %v13, 8
	vsldoi %v6, %v13, %v13, 8
	vsldoi %v2, %v6, %v19, 8
	vpmsumd %v5, %v2, %v16
	vsldoi %v2, %v19, %v6, 8
	vpmsumd %v3, %v2, %v16
	vpmsumd %v4, %v6, %v16
	vsldoi %v7, %v3, %v19, 8
	vpmsumd %v7, %v7, %v1
	vsldoi %v3, %v3, %v3, 8
	vxor %v4, %v4, %v3
	vxor %v4, %v4, %v7
	vsldoi %v7, %v4, %v19, 8
	vpmsumd %v7, %v7, %v1
	vsldoi %v5, %v5, %v5, 8
	vxor %v5, %v5, %v4
	vsldoi %v7, %v7, %v7, 8
	vxor %v14, %v5, %v7
	vsldoi %v14, %v14, %v14, 8
	vsldoi %v6, %v13, %v13, 8
	vsldoi %v7, %v6, %v14, 8
	vsldoi %v7, %v7, %v7, 8
	vsldoi %v14, %v14, %v6, 8
	vor %v13, %v7, %v7
	vsldoi %v6, %v11, %v11, 8
	vsldoi %v7, %v6, %v12, 8
	vsldoi %v7, %v7, %v7, 8
	vsldoi %v12, %v12, %v6, 8
	vor %v11, %v7, %v7
	vsldoi %v6, %v9, %v9, 8
	vsldoi %v7, %v6, %v10, 8
	vsldoi %v7, %v7, %v7, 8
	vsldoi %v10, %v10, %v6, 8
	vor %v9, %v7, %v7
	vsldoi %v6, %v16, %v16, 8
	vsldoi %v7, %v6, %v8, 8
	vsldoi %v7, %v7, %v7, 8
	vsldoi %v8, %v8, %v6, 8
	vor %v15, %v7, %v7
24:
	lxvd2x 38, %r5, %r0
	vperm %v6, %v6, %v6, %v18
	addi %r5, %r5, 16
	vxor %v6, %v6, %v0
	lxvd2x 37, %r5, %r0
	vperm %v5, %v5, %v5, %v18
	addi %r5, %r5, 16
	vsldoi %v5, %v5, %v5, 8
	vsldoi %v2, %v6, %v5, 8
	vsldoi %v7, %v5, %v6, 8
	vsldoi %v7, %v7, %v7, 8
	vpmsumd %v5, %v2, %v13
	vpmsumd %v3, %v7, %v14
	vpmsumd %v4, %v2, %v14
	vpmsumd %v2, %v7, %v13
	vxor %v4, %v4, %v2
	vor %v0, %v3, %v3
	vor %v16, %v4, %v4
	vor %v17, %v5, %v5
	lxvd2x 38, %r5, %r0
	vperm %v6, %v6, %v6, %v18
	addi %r5, %r5, 16
	lxvd2x 37, %r5, %r0
	vperm %v5, %v5, %v5, %v18
	addi %r5, %r5, 16
	vsldoi %v5, %v5, %v5, 8
	vsldoi %v2, %v6, %v5, 8
	vsldoi %v7, %v5, %v6, 8
	vsldoi %v7, %v7, %v7, 8
	vpmsumd %v5, %v2, %v11
	vpmsumd %v3, %v7, %v12
	vpmsumd %v4, %v2, %v12
	vpmsumd %v2, %v7, %v11
	vxor %v4, %v4, %v2
	vxor %v0, %v0, %v3
	vxor %v16, %v16, %v4
	vxor %v17, %v17, %v5
	lxvd2x 38, %r5, %r0
	vperm %v6, %v6, %v6, %v18
	addi %r5, %r5, 16
	lxvd2x 37, %r5, %r0
	vperm %v5, %v5, %v5, %v18
	addi %r5, %r5, 16
	vsldoi %v5, %v5, %v5, 8
	vsldoi %v2, %v6, %v5, 8
	vsldoi %v7, %v5, %v6, 8
	vsldoi %v7, %v7, %v7, 8
	vpmsumd %v5, %v2, %v9
	vpmsumd %v3, %v7, %v10
	vpmsumd %v4, %v2, %v10
	vpmsumd %v2, %v7, %v9
	vxor %v4, %v4, %v2
	vxor %v0, %v0, %v3
	vxor %v16, %v16, %v4
	vxor %v17, %v17, %v5
	lxvd2x 38, %r5, %r0
	vperm %v6, %v6, %v6, %v18
	addi %r5, %r5, 16
	lxvd2x 37, %r5, %r0
	vperm %v5, %v5, %v5, %v18
	addi %r5, %r5, 16
	vsldoi %v5, %v5, %v5, 8
	vsldoi %v2, %v6, %v5, 8
	vsldoi %v7, %v5, %v6, 8
	vsldoi %v7, %v7, %v7, 8
	vpmsumd %v5, %v2, %v15
	vpmsumd %v3, %v7, %v8
	vpmsumd %v4, %v2, %v8
	vpmsumd %v2, %v7, %v15
	vxor %v4, %v4, %v2
	vxor %v3, %v3, %v0
	vxor %v4, %v4, %v16
	vxor %v5, %v5, %v17
	vsldoi %v7, %v3, %v19, 8
	vpmsumd %v7, %v7, %v1
	vsldoi %v3, %v3, %v3, 8
	vxor %v4, %v4, %v3
	vxor %v4, %v4, %v7
	vsldoi %v7, %v4, %v19, 8
	vpmsumd %v7, %v7, %v1
	vsldoi %v5, %v5, %v5, 8
	vxor %v5, %v5, %v4
	vsldoi %v7, %v7, %v7, 8
	vxor %v0, %v5, %v7
	addi %r6, %r6, -8
	rldicl %r10, %r6, 61, 3
	cmpldi %cr0, %r10, 0
	bne %cr0, 24b
	vsldoi %v6, %v8, %v8, 8
	vsldoi %v16, %v15, %v6, 8
	cmpldi %cr0, %r6, 0
	beq %cr0, 25f
27:
	lxvd2x 38, %r5, %r0
	vperm %v6, %v6, %v6, %v18
	vxor %v6, %v6, %v0
	vsldoi %v2, %v6, %v19, 8
	vpmsumd %v5, %v2, %v16
	vsldoi %v2, %v19, %v6, 8
	vpmsumd %v3, %v2, %v16
	vpmsumd %v4, %v6, %v16
	vsldoi %v7, %v3, %v19, 8
	vpmsumd %v7, %v7, %v1
	vsldoi %v3, %v3, %v3, 8
	vxor %v4, %v4, %v3
	vxor %v4, %v4, %v7
	vsldoi %v7, %v4, %v19, 8
	vpmsumd %v7, %v7, %v1
	vsldoi %v5, %v5, %v5, 8
	vxor %v5, %v5, %v4
	vsldoi %v7, %v7, %v7, 8
	vxor %v0, %v5, %v7
	addi %r5, %r5, 16
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 27b
	b 26f
25:
26:
	vperm %v7, %v0, %v0, %v18
	stxvd2x 39, %r4, %r0
	b 23f
22:
28:
	lxvd2x 38, %r5, %r0
	vperm %v6, %v6, %v6, %v18
	vxor %v6, %v6, %v0
	vsldoi %v2, %v6, %v19, 8
	vpmsumd %v5, %v2, %v16
	vsldoi %v2, %v19, %v6, 8
	vpmsumd %v3, %v2, %v16
	vpmsumd %v4, %v6, %v16
	vsldoi %v7, %v3, %v19, 8
	vpmsumd %v7, %v7, %v1
	vsldoi %v3, %v3, %v3, 8
	vxor %v4, %v4, %v3
	vxor %v4, %v4, %v7
	vsldoi %v7, %v4, %v19, 8
	vpmsumd %v7, %v7, %v1
	vsldoi %v5, %v5, %v5, 8
	vxor %v5, %v5, %v4
	vsldoi %v7, %v7, %v7, 8
	vxor %v0, %v5, %v7
	addi %r5, %r5, 16
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 28b
	vperm %v7, %v0, %v0, %v18
	stxvd2x 39, %r4, %r0
23:
	b 21f
20:
21:
	blr
