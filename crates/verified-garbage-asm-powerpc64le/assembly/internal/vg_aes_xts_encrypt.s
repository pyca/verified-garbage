// The functions of `src/internal/vg_aes_xts_encrypt.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
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
	rldicl %r9, %r18, 61, 3
	cmpldi %cr0, %r9, 0
	beq %cr0, 22f
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
	beq %cr0, 26f
28:
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
	bne %cr0, 28b
	b 27f
26:
27:
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
