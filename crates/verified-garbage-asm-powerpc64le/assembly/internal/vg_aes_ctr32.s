// The functions of `src/internal/vg_aes_ctr32.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ctr32:
	cmpldi %cr0, %r7, 0
	beq %cr0, 20f
	li %r0, 0
	vxor %v0, %v0, %v0
	lis %r11, 1798
	ori %r11, %r11, 1284
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 770
	ori %r11, %r11, 256
	lis %r12, 3854
	ori %r12, %r12, 3340
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 2826
	ori %r12, %r12, 2312
	mtvsrd 51, %r11
	mtvsrd 33, %r12
	vsldoi %v19, %v0, %v19, 8
	vsldoi %v19, %v19, %v1, 8
	lis %r11, 1
	ori %r11, %r11, 515
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 1029
	ori %r11, %r11, 1543
	lis %r12, 2057
	ori %r12, %r12, 2571
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 5141
	ori %r12, %r12, 5655
	mtvsrd 50, %r11
	mtvsrd 33, %r12
	vsldoi %v18, %v0, %v18, 8
	vsldoi %v18, %v18, %v1, 8
	li %r11, 12
	lwbrx %r8, %r5, %r11
	lxvd2x 42, %r5, %r0
	vperm %v10, %v10, %v10, %v19
	rldicl %r12, %r7, 61, 3
	cmpldi %cr0, %r12, 0
	beq %cr0, 22f
24:
	mtvsrd 43, %r8
	vperm %v0, %v10, %v11, %v18
	addi %r8, %r8, 1
	mtvsrd 43, %r8
	vperm %v1, %v10, %v11, %v18
	addi %r8, %r8, 1
	mtvsrd 43, %r8
	vperm %v2, %v10, %v11, %v18
	addi %r8, %r8, 1
	mtvsrd 43, %r8
	vperm %v3, %v10, %v11, %v18
	addi %r8, %r8, 1
	mtvsrd 43, %r8
	vperm %v4, %v10, %v11, %v18
	addi %r8, %r8, 1
	mtvsrd 43, %r8
	vperm %v5, %v10, %v11, %v18
	addi %r8, %r8, 1
	mtvsrd 43, %r8
	vperm %v6, %v10, %v11, %v18
	addi %r8, %r8, 1
	mtvsrd 43, %r8
	vperm %v7, %v10, %v11, %v18
	addi %r8, %r8, 1
	or %r9, %r3, %r3
	lxvd2x 40, %r9, %r0
	vperm %v8, %v8, %v8, %v19
	vxor %v0, %v0, %v8
	vxor %v1, %v1, %v8
	vxor %v2, %v2, %v8
	vxor %v3, %v3, %v8
	vxor %v4, %v4, %v8
	vxor %v5, %v5, %v8
	vxor %v6, %v6, %v8
	vxor %v7, %v7, %v8
	addi %r9, %r9, 16
	addi %r10, %r4, -1
25:
	lxvd2x 40, %r9, %r0
	vperm %v8, %v8, %v8, %v19
	vcipher %v0, %v0, %v8
	vcipher %v1, %v1, %v8
	vcipher %v2, %v2, %v8
	vcipher %v3, %v3, %v8
	vcipher %v4, %v4, %v8
	vcipher %v5, %v5, %v8
	vcipher %v6, %v6, %v8
	vcipher %v7, %v7, %v8
	addi %r9, %r9, 16
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 25b
	lxvd2x 40, %r9, %r0
	vperm %v8, %v8, %v8, %v19
	vcipherlast %v0, %v0, %v8
	vcipherlast %v1, %v1, %v8
	vcipherlast %v2, %v2, %v8
	vcipherlast %v3, %v3, %v8
	vcipherlast %v4, %v4, %v8
	vcipherlast %v5, %v5, %v8
	vcipherlast %v6, %v6, %v8
	vcipherlast %v7, %v7, %v8
	lxvd2x 41, %r6, %r0
	vperm %v9, %v9, %v9, %v19
	vxor %v0, %v0, %v9
	vperm %v0, %v0, %v0, %v19
	stxvd2x 32, %r6, %r0
	addi %r6, %r6, 16
	lxvd2x 41, %r6, %r0
	vperm %v9, %v9, %v9, %v19
	vxor %v1, %v1, %v9
	vperm %v1, %v1, %v1, %v19
	stxvd2x 33, %r6, %r0
	addi %r6, %r6, 16
	lxvd2x 41, %r6, %r0
	vperm %v9, %v9, %v9, %v19
	vxor %v2, %v2, %v9
	vperm %v2, %v2, %v2, %v19
	stxvd2x 34, %r6, %r0
	addi %r6, %r6, 16
	lxvd2x 41, %r6, %r0
	vperm %v9, %v9, %v9, %v19
	vxor %v3, %v3, %v9
	vperm %v3, %v3, %v3, %v19
	stxvd2x 35, %r6, %r0
	addi %r6, %r6, 16
	lxvd2x 41, %r6, %r0
	vperm %v9, %v9, %v9, %v19
	vxor %v4, %v4, %v9
	vperm %v4, %v4, %v4, %v19
	stxvd2x 36, %r6, %r0
	addi %r6, %r6, 16
	lxvd2x 41, %r6, %r0
	vperm %v9, %v9, %v9, %v19
	vxor %v5, %v5, %v9
	vperm %v5, %v5, %v5, %v19
	stxvd2x 37, %r6, %r0
	addi %r6, %r6, 16
	lxvd2x 41, %r6, %r0
	vperm %v9, %v9, %v9, %v19
	vxor %v6, %v6, %v9
	vperm %v6, %v6, %v6, %v19
	stxvd2x 38, %r6, %r0
	addi %r6, %r6, 16
	lxvd2x 41, %r6, %r0
	vperm %v9, %v9, %v9, %v19
	vxor %v7, %v7, %v9
	vperm %v7, %v7, %v7, %v19
	stxvd2x 39, %r6, %r0
	addi %r6, %r6, 16
	addi %r7, %r7, -8
	rldicl %r12, %r7, 61, 3
	cmpldi %cr0, %r12, 0
	bne %cr0, 24b
	b 23f
22:
23:
	cmpldi %cr0, %r7, 0
	beq %cr0, 26f
28:
	mtvsrd 43, %r8
	vperm %v0, %v10, %v11, %v18
	addi %r8, %r8, 1
	or %r9, %r3, %r3
	lxvd2x 40, %r9, %r0
	vperm %v8, %v8, %v8, %v19
	vxor %v0, %v0, %v8
	addi %r9, %r9, 16
	addi %r10, %r4, -1
29:
	lxvd2x 40, %r9, %r0
	vperm %v8, %v8, %v8, %v19
	vcipher %v0, %v0, %v8
	addi %r9, %r9, 16
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 29b
	lxvd2x 40, %r9, %r0
	vperm %v8, %v8, %v8, %v19
	vcipherlast %v0, %v0, %v8
	lxvd2x 41, %r6, %r0
	vperm %v9, %v9, %v9, %v19
	vxor %v0, %v0, %v9
	vperm %v0, %v0, %v0, %v19
	stxvd2x 32, %r6, %r0
	addi %r6, %r6, 16
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 28b
	b 27f
26:
27:
	stwbrx %r8, %r5, %r11
	b 21f
20:
21:
	blr
