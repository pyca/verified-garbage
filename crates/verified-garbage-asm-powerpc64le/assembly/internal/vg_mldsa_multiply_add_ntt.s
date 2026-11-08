// The functions of `src/internal/vg_mldsa_multiply_add_ntt.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_multiply_add_ntt:
	lis %r12, 127
	ori %r12, %r12, 57345
	mtvsrd 36, %r12
	vspltw %v4, %v4, 1
	lis %r12, 1
	ori %r12, %r12, 515
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 4113
	ori %r12, %r12, 4627
	lis %r11, 2057
	ori %r11, %r11, 2571
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 6169
	ori %r11, %r11, 6683
	mtvsrd 38, %r12
	mtvsrd 39, %r11
	vsldoi %v5, %v6, %v6, 8
	vsldoi %v5, %v5, %v7, 8
	lis %r12, 1
	ori %r12, %r12, 515
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 4113
	ori %r12, %r12, 4627
	lis %r11, 1029
	ori %r11, %r11, 1543
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 5141
	ori %r11, %r11, 5655
	mtvsrd 38, %r12
	mtvsrd 39, %r11
	vsldoi %v16, %v6, %v6, 8
	vsldoi %v16, %v16, %v7, 8
	lis %r12, 2057
	ori %r12, %r12, 2571
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 6169
	ori %r12, %r12, 6683
	lis %r11, 3085
	ori %r11, %r11, 3599
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 7197
	ori %r11, %r11, 7711
	mtvsrd 38, %r12
	mtvsrd 39, %r11
	vsldoi %v17, %v6, %v6, 8
	vsldoi %v17, %v17, %v7, 8
	lis %r12, 1
	ori %r12, %r12, 515
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 1029
	ori %r12, %r12, 1543
	lis %r11, 4113
	ori %r11, %r11, 4627
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 5141
	ori %r11, %r11, 5655
	mtvsrd 38, %r12
	mtvsrd 39, %r11
	vsldoi %v18, %v6, %v6, 8
	vsldoi %v18, %v18, %v7, 8
	lis %r12, 2057
	ori %r12, %r12, 2571
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 3085
	ori %r12, %r12, 3599
	lis %r11, 6169
	ori %r11, %r11, 6683
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 7197
	ori %r11, %r11, 7711
	mtvsrd 38, %r12
	mtvsrd 39, %r11
	vsldoi %v19, %v6, %v6, 8
	vsldoi %v19, %v19, %v7, 8
	lis %r12, 896
	ori %r12, %r12, 8193
	mtvsrd 45, %r12
	vspltw %v13, %v13, 1
	lis %r12, 63
	ori %r12, %r12, 65024
	mtvsrd 34, %r12
	vspltw %v2, %v2, 1
	lis %r12, -32740
	ori %r12, %r12, 1537
	mtvsrd 35, %r12
	vspltw %v3, %v3, 1
	li %r9, 0
	li %r10, 64
20:
	lxvd2x 40, %r4, %r9
	lxvd2x 41, %r5, %r9
	vmuluwm %v10, %v8, %v9
	vmuluwm %v10, %v10, %v13
	vmuleuw %v6, %v8, %v9
	vmulouw %v7, %v8, %v9
	vperm %v11, %v6, %v7, %v5
	vmuleuw %v6, %v10, %v4
	vmulouw %v7, %v10, %v4
	vperm %v6, %v6, %v7, %v5
	vsubuwm %v8, %v11, %v6
	vadduwm %v7, %v8, %v4
	vminuw %v8, %v8, %v7
	vmuleuw %v6, %v8, %v3
	vmulouw %v7, %v8, %v3
	vperm %v6, %v6, %v7, %v5
	vmuluwm %v7, %v8, %v2
	vmuluwm %v6, %v6, %v4
	vsubuwm %v7, %v7, %v6
	vsubuwm %v6, %v7, %v4
	vminuw %v8, %v7, %v6
	lxvd2x 41, %r3, %r9
	vadduwm %v6, %v8, %v9
	vsubuwm %v7, %v6, %v4
	vminuw %v8, %v6, %v7
	stxvd2x 40, %r3, %r9
	addi %r3, %r3, 16
	addi %r4, %r4, 16
	addi %r5, %r5, 16
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 20b
	blr
