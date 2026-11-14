// The functions of `src/internal/vg_aes_xts_decrypt.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

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
	rldicl %r9, %r18, 61, 3
	cmpldi %cr0, %r9, 0
	beq %cr0, 22f
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
	addi %r9, %r14, 16
	lxvd2x 42, %r9, %r0
	vperm %v10, %v10, %v10, %v19
	addi %r9, %r14, 32
	lxvd2x 43, %r9, %r0
	vperm %v11, %v11, %v11, %v19
	addi %r9, %r14, 48
	lxvd2x 44, %r9, %r0
	vperm %v12, %v12, %v12, %v19
	addi %r9, %r14, 64
	lxvd2x 45, %r9, %r0
	vperm %v13, %v13, %v13, %v19
	addi %r9, %r14, 80
	lxvd2x 46, %r9, %r0
	vperm %v14, %v14, %v14, %v19
	addi %r9, %r14, 96
	lxvd2x 47, %r9, %r0
	vperm %v15, %v15, %v15, %v19
	addi %r9, %r14, 112
	lxvd2x 48, %r9, %r0
	vperm %v16, %v16, %v16, %v19
	addi %r9, %r14, 128
	lxvd2x 49, %r9, %r0
	vperm %v17, %v17, %v17, %v19
	addi %r9, %r14, 144
	lxvd2x 50, %r9, %r0
	vperm %v18, %v18, %v18, %v19
24:
	ld %r9, 0(%r16)
	ld %r10, 8(%r16)
	std %r9, 0(%r19)
	std %r10, 8(%r19)
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
	std %r9, 16(%r19)
	std %r10, 24(%r19)
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
	std %r9, 32(%r19)
	std %r10, 40(%r19)
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
	std %r9, 48(%r19)
	std %r10, 56(%r19)
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
	std %r9, 64(%r19)
	std %r10, 72(%r19)
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
	std %r9, 80(%r19)
	std %r10, 88(%r19)
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
	std %r9, 96(%r19)
	std %r10, 104(%r19)
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
	std %r9, 112(%r19)
	std %r10, 120(%r19)
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
	or %r3, %r14, %r14
	or %r4, %r15, %r15
	or %r6, %r17, %r17
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
	lxvd2x 32, %r6, %r0
	vperm %v0, %v0, %v0, %v19
	addi %r6, %r6, 16
	lxvd2x 33, %r6, %r0
	vperm %v1, %v1, %v1, %v19
	addi %r6, %r6, 16
	lxvd2x 34, %r6, %r0
	vperm %v2, %v2, %v2, %v19
	addi %r6, %r6, 16
	lxvd2x 35, %r6, %r0
	vperm %v3, %v3, %v3, %v19
	addi %r6, %r6, 16
	lxvd2x 36, %r6, %r0
	vperm %v4, %v4, %v4, %v19
	addi %r6, %r6, 16
	lxvd2x 37, %r6, %r0
	vperm %v5, %v5, %v5, %v19
	addi %r6, %r6, 16
	lxvd2x 38, %r6, %r0
	vperm %v6, %v6, %v6, %v19
	addi %r6, %r6, 16
	lxvd2x 39, %r6, %r0
	vperm %v7, %v7, %v7, %v19
	addi %r6, %r6, 16
	addi %r6, %r6, -128
	addi %r7, %r19, 0
	lxvd2x 41, %r7, %r0
	vperm %v9, %v9, %v9, %v19
	vxor %v0, %v0, %v9
	addi %r7, %r19, 16
	lxvd2x 41, %r7, %r0
	vperm %v9, %v9, %v9, %v19
	vxor %v1, %v1, %v9
	addi %r7, %r19, 32
	lxvd2x 41, %r7, %r0
	vperm %v9, %v9, %v9, %v19
	vxor %v2, %v2, %v9
	addi %r7, %r19, 48
	lxvd2x 41, %r7, %r0
	vperm %v9, %v9, %v9, %v19
	vxor %v3, %v3, %v9
	addi %r7, %r19, 64
	lxvd2x 41, %r7, %r0
	vperm %v9, %v9, %v9, %v19
	vxor %v4, %v4, %v9
	addi %r7, %r19, 80
	lxvd2x 41, %r7, %r0
	vperm %v9, %v9, %v9, %v19
	vxor %v5, %v5, %v9
	addi %r7, %r19, 96
	lxvd2x 41, %r7, %r0
	vperm %v9, %v9, %v9, %v19
	vxor %v6, %v6, %v9
	addi %r7, %r19, 112
	lxvd2x 41, %r7, %r0
	vperm %v9, %v9, %v9, %v19
	vxor %v7, %v7, %v9
	rldicr %r9, %r4, 4, 59
	add %r9, %r3, %r9
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
	addi %r9, %r9, -16
	addi %r10, %r4, -1
	addi %r12, %r4, -10
	cmpldi %cr0, %r12, 0
	beq %cr0, 25f
	addi %r12, %r4, -12
	cmpldi %cr0, %r12, 0
	beq %cr0, 27f
	addi %r9, %r3, 208
	lxvd2x 40, %r9, %r0
	vperm %v8, %v8, %v8, %v19
	vncipher %v0, %v0, %v8
	vncipher %v1, %v1, %v8
	vncipher %v2, %v2, %v8
	vncipher %v3, %v3, %v8
	vncipher %v4, %v4, %v8
	vncipher %v5, %v5, %v8
	vncipher %v6, %v6, %v8
	vncipher %v7, %v7, %v8
	addi %r9, %r3, 192
	lxvd2x 40, %r9, %r0
	vperm %v8, %v8, %v8, %v19
	vncipher %v0, %v0, %v8
	vncipher %v1, %v1, %v8
	vncipher %v2, %v2, %v8
	vncipher %v3, %v3, %v8
	vncipher %v4, %v4, %v8
	vncipher %v5, %v5, %v8
	vncipher %v6, %v6, %v8
	vncipher %v7, %v7, %v8
	b 28f
27:
28:
	addi %r9, %r3, 176
	lxvd2x 40, %r9, %r0
	vperm %v8, %v8, %v8, %v19
	vncipher %v0, %v0, %v8
	vncipher %v1, %v1, %v8
	vncipher %v2, %v2, %v8
	vncipher %v3, %v3, %v8
	vncipher %v4, %v4, %v8
	vncipher %v5, %v5, %v8
	vncipher %v6, %v6, %v8
	vncipher %v7, %v7, %v8
	addi %r9, %r3, 160
	lxvd2x 40, %r9, %r0
	vperm %v8, %v8, %v8, %v19
	vncipher %v0, %v0, %v8
	vncipher %v1, %v1, %v8
	vncipher %v2, %v2, %v8
	vncipher %v3, %v3, %v8
	vncipher %v4, %v4, %v8
	vncipher %v5, %v5, %v8
	vncipher %v6, %v6, %v8
	vncipher %v7, %v7, %v8
	b 26f
25:
26:
	vncipher %v0, %v0, %v18
	vncipher %v1, %v1, %v18
	vncipher %v2, %v2, %v18
	vncipher %v3, %v3, %v18
	vncipher %v4, %v4, %v18
	vncipher %v5, %v5, %v18
	vncipher %v6, %v6, %v18
	vncipher %v7, %v7, %v18
	vncipher %v0, %v0, %v17
	vncipher %v1, %v1, %v17
	vncipher %v2, %v2, %v17
	vncipher %v3, %v3, %v17
	vncipher %v4, %v4, %v17
	vncipher %v5, %v5, %v17
	vncipher %v6, %v6, %v17
	vncipher %v7, %v7, %v17
	vncipher %v0, %v0, %v16
	vncipher %v1, %v1, %v16
	vncipher %v2, %v2, %v16
	vncipher %v3, %v3, %v16
	vncipher %v4, %v4, %v16
	vncipher %v5, %v5, %v16
	vncipher %v6, %v6, %v16
	vncipher %v7, %v7, %v16
	vncipher %v0, %v0, %v15
	vncipher %v1, %v1, %v15
	vncipher %v2, %v2, %v15
	vncipher %v3, %v3, %v15
	vncipher %v4, %v4, %v15
	vncipher %v5, %v5, %v15
	vncipher %v6, %v6, %v15
	vncipher %v7, %v7, %v15
	vncipher %v0, %v0, %v14
	vncipher %v1, %v1, %v14
	vncipher %v2, %v2, %v14
	vncipher %v3, %v3, %v14
	vncipher %v4, %v4, %v14
	vncipher %v5, %v5, %v14
	vncipher %v6, %v6, %v14
	vncipher %v7, %v7, %v14
	vncipher %v0, %v0, %v13
	vncipher %v1, %v1, %v13
	vncipher %v2, %v2, %v13
	vncipher %v3, %v3, %v13
	vncipher %v4, %v4, %v13
	vncipher %v5, %v5, %v13
	vncipher %v6, %v6, %v13
	vncipher %v7, %v7, %v13
	vncipher %v0, %v0, %v12
	vncipher %v1, %v1, %v12
	vncipher %v2, %v2, %v12
	vncipher %v3, %v3, %v12
	vncipher %v4, %v4, %v12
	vncipher %v5, %v5, %v12
	vncipher %v6, %v6, %v12
	vncipher %v7, %v7, %v12
	vncipher %v0, %v0, %v11
	vncipher %v1, %v1, %v11
	vncipher %v2, %v2, %v11
	vncipher %v3, %v3, %v11
	vncipher %v4, %v4, %v11
	vncipher %v5, %v5, %v11
	vncipher %v6, %v6, %v11
	vncipher %v7, %v7, %v11
	vncipher %v0, %v0, %v10
	vncipher %v1, %v1, %v10
	vncipher %v2, %v2, %v10
	vncipher %v3, %v3, %v10
	vncipher %v4, %v4, %v10
	vncipher %v5, %v5, %v10
	vncipher %v6, %v6, %v10
	vncipher %v7, %v7, %v10
	or %r9, %r3, %r3
	lxvd2x 40, %r9, %r0
	vperm %v8, %v8, %v8, %v19
	vncipherlast %v0, %v0, %v8
	vncipherlast %v1, %v1, %v8
	vncipherlast %v2, %v2, %v8
	vncipherlast %v3, %v3, %v8
	vncipherlast %v4, %v4, %v8
	vncipherlast %v5, %v5, %v8
	vncipherlast %v6, %v6, %v8
	vncipherlast %v7, %v7, %v8
	addi %r7, %r19, 0
	lxvd2x 41, %r7, %r0
	vperm %v9, %v9, %v9, %v19
	vxor %v0, %v0, %v9
	addi %r7, %r19, 16
	lxvd2x 41, %r7, %r0
	vperm %v9, %v9, %v9, %v19
	vxor %v1, %v1, %v9
	addi %r7, %r19, 32
	lxvd2x 41, %r7, %r0
	vperm %v9, %v9, %v9, %v19
	vxor %v2, %v2, %v9
	addi %r7, %r19, 48
	lxvd2x 41, %r7, %r0
	vperm %v9, %v9, %v9, %v19
	vxor %v3, %v3, %v9
	addi %r7, %r19, 64
	lxvd2x 41, %r7, %r0
	vperm %v9, %v9, %v9, %v19
	vxor %v4, %v4, %v9
	addi %r7, %r19, 80
	lxvd2x 41, %r7, %r0
	vperm %v9, %v9, %v9, %v19
	vxor %v5, %v5, %v9
	addi %r7, %r19, 96
	lxvd2x 41, %r7, %r0
	vperm %v9, %v9, %v9, %v19
	vxor %v6, %v6, %v9
	addi %r7, %r19, 112
	lxvd2x 41, %r7, %r0
	vperm %v9, %v9, %v9, %v19
	vxor %v7, %v7, %v9
	vperm %v0, %v0, %v0, %v19
	stxvd2x 32, %r6, %r0
	addi %r6, %r6, 16
	vperm %v1, %v1, %v1, %v19
	stxvd2x 33, %r6, %r0
	addi %r6, %r6, 16
	vperm %v2, %v2, %v2, %v19
	stxvd2x 34, %r6, %r0
	addi %r6, %r6, 16
	vperm %v3, %v3, %v3, %v19
	stxvd2x 35, %r6, %r0
	addi %r6, %r6, 16
	vperm %v4, %v4, %v4, %v19
	stxvd2x 36, %r6, %r0
	addi %r6, %r6, 16
	vperm %v5, %v5, %v5, %v19
	stxvd2x 37, %r6, %r0
	addi %r6, %r6, 16
	vperm %v6, %v6, %v6, %v19
	stxvd2x 38, %r6, %r0
	addi %r6, %r6, 16
	vperm %v7, %v7, %v7, %v19
	stxvd2x 39, %r6, %r0
	addi %r6, %r6, 16
	addi %r17, %r17, 128
	addi %r18, %r18, -8
	rldicl %r9, %r18, 61, 3
	cmpldi %cr0, %r9, 0
	bne %cr0, 24b
	b 23f
22:
23:
	cmpldi %cr0, %r18, 0
	beq %cr0, 29f
211:
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
	bne %cr0, 211b
	b 210f
29:
210:
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
