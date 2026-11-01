// The functions of `src/aes.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_expand_key:
	or %r7, %r4, %r4
20:
	ld %r8, 0(%r3)
	std %r8, 0(%r5)
	addi %r3, %r3, 8
	addi %r5, %r5, 8
	addi %r4, %r4, -8
	cmpldi %cr0, %r4, 0
	bne %cr0, 20b
	subf %r10, %r7, %r5
	addi %r11, %r5, -4
	li %r12, 0
	rldicl %r4, %r7, 62, 2
	add %r8, %r4, %r4
	add %r4, %r4, %r8
	addi %r4, %r4, 28
	li %r6, 1
21:
	lwz %r9, 0(%r11)
	cmpldi %cr0, %r12, 0
	beq %cr0, 22f
	addi %r0, %r12, -16
	cmpldi %cr0, %r0, 0
	beq %cr0, 24f
	b 25f
24:
	addi %r0, %r7, -32
	cmpldi %cr0, %r0, 0
	beq %cr0, 26f
	b 27f
26:
	mtvsrd 32, %r9
	vsbox %v0, %v0
	mfvsrd %r9, 32
	rlwinm %r9, %r9, 0, 0, 31
27:
25:
	b 23f
22:
	mtvsrd 32, %r9
	vsbox %v0, %v0
	mfvsrd %r9, 32
	rlwinm %r9, %r9, 0, 0, 31
	rlwinm %r9, %r9, 24, 0, 31
	xor %r9, %r9, %r6
	rldicl %r0, %r6, 57, 7
	li %r8, 0
	subf %r0, %r0, %r8
	li %r8, 27
	and %r0, %r0, %r8
	add %r6, %r6, %r6
	xor %r6, %r6, %r0
	li %r8, 255
	and %r6, %r6, %r8
23:
	lwz %r8, 0(%r10)
	xor %r9, %r9, %r8
	stw %r9, 4(%r11)
	addi %r11, %r11, 4
	addi %r10, %r10, 4
	addi %r12, %r12, 4
	subf %r0, %r7, %r12
	cmpldi %cr0, %r0, 0
	beq %cr0, 28f
	b 29f
28:
	li %r12, 0
29:
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 21b
	blr

vg_aes_encrypt_blocks:
	cmpldi %cr0, %r6, 0
	beq %cr0, 20f
	or %r7, %r6, %r6
	or %r6, %r5, %r5
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
	rldicl %r12, %r7, 61, 3
	cmpldi %cr0, %r12, 0
	beq %cr0, 22f
24:
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
	lxvd2x 32, %r6, %r0
	vperm %v0, %v0, %v0, %v19
	addi %r6, %r6, 16
	addi %r6, %r6, -16
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
	vperm %v0, %v0, %v0, %v19
	stxvd2x 32, %r6, %r0
	addi %r6, %r6, 16
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 28b
	b 27f
26:
27:
	b 21f
20:
21:
	blr

vg_aes_decrypt_blocks:
	cmpldi %cr0, %r6, 0
	beq %cr0, 20f
	or %r7, %r6, %r6
	or %r6, %r5, %r5
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
	rldicl %r12, %r7, 61, 3
	cmpldi %cr0, %r12, 0
	beq %cr0, 22f
24:
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
25:
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
	addi %r9, %r9, -16
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 25b
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
	lxvd2x 32, %r6, %r0
	vperm %v0, %v0, %v0, %v19
	addi %r6, %r6, 16
	addi %r6, %r6, -16
	rldicr %r9, %r4, 4, 59
	add %r9, %r3, %r9
	lxvd2x 40, %r9, %r0
	vperm %v8, %v8, %v8, %v19
	vxor %v0, %v0, %v8
	addi %r9, %r9, -16
	addi %r10, %r4, -1
29:
	lxvd2x 40, %r9, %r0
	vperm %v8, %v8, %v8, %v19
	vncipher %v0, %v0, %v8
	addi %r9, %r9, -16
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 29b
	lxvd2x 40, %r9, %r0
	vperm %v8, %v8, %v8, %v19
	vncipherlast %v0, %v0, %v8
	vperm %v0, %v0, %v0, %v19
	stxvd2x 32, %r6, %r0
	addi %r6, %r6, 16
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 28b
	b 27f
26:
27:
	b 21f
20:
21:
	blr
