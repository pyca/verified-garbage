// The functions of `src/blowfish_cbc.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blowfish_cbc_encrypt_chained:
	stdu %r1, -128(%r1)
	addi %r7, %r1, 32
	mflr %r0
	std %r0, 64(%r7)
	std %r29, 40(%r7)
	std %r30, 48(%r7)
	std %r31, 56(%r7)
	or %r29, %r4, %r4
	or %r30, %r6, %r6
	or %r31, %r4, %r4
	or %r6, %r5, %r5
	or %r5, %r7, %r7
	lwz %r8, 0(%r31)
	stw %r8, 72(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 76(%r5)
	or %r31, %r6, %r6
	cmpldi %cr0, %r30, 0
	beq %cr0, 20f
22:
	lwz %r8, 0(%r31)
	lwz %r9, 72(%r5)
	xor %r8, %r8, %r9
	stw %r8, 32(%r5)
	lwz %r8, 4(%r31)
	lwz %r9, 76(%r5)
	xor %r8, %r8, %r9
	stw %r8, 36(%r5)
	or %r6, %r5, %r5
	std %r14, 0(%r6)
	std %r15, 8(%r6)
	std %r16, 16(%r6)
	std %r17, 24(%r6)
	li %r0, 0
	addi %r16, %r6, 32
	lwbrx %r4, %r16, %r0
	addi %r12, %r16, 4
	lwbrx %r5, %r12, %r0
	addi %r8, %r3, 4096
23:
	lwz %r12, 0(%r8)
	xor %r4, %r4, %r12
	rldicr %r9, %r4, 32, 31
	rldicl %r9, %r9, 8, 56
	vxor %v0, %v0, %v0
	li %r12, 7
	xor %r12, %r9, %r12
	rldicr %r12, %r12, 56, 7
	mtvsrd 33, %r12
	vperm %v1, %v1, %v1, %v0
	rldicl %r12, %r9, 59, 5
	rldicr %r12, %r12, 56, 7
	mtvsrd 34, %r12
	vperm %v2, %v2, %v2, %v0
	li %r12, 255
	rldicr %r12, %r12, 56, 7
	mtvsrd 35, %r12
	addi %r15, %r3, 0
	li %r11, 16
	li %r14, 256
	li %r9, 272
24:
	vperm %v4, %v3, %v3, %v2
	vsldoi %v3, %v0, %v3, 15
	lxvd2x 37, %r15, %r0
	vsel %v6, %v6, %v5, %v4
	lxvd2x 37, %r15, %r11
	vsel %v7, %v7, %v5, %v4
	lxvd2x 37, %r15, %r14
	vsel %v8, %v8, %v5, %v4
	lxvd2x 37, %r15, %r9
	vsel %v9, %v9, %v5, %v4
	addi %r15, %r15, 512
	lxvd2x 37, %r15, %r0
	vsel %v10, %v10, %v5, %v4
	lxvd2x 37, %r15, %r11
	vsel %v11, %v11, %v5, %v4
	lxvd2x 37, %r15, %r14
	vsel %v12, %v12, %v5, %v4
	lxvd2x 37, %r15, %r9
	vsel %v13, %v13, %v5, %v4
	addi %r15, %r15, -480
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 24b
	vperm %v14, %v6, %v7, %v1
	vperm %v15, %v8, %v9, %v1
	vperm %v16, %v10, %v11, %v1
	vperm %v17, %v12, %v13, %v1
	mfvsrd %r10, 46
	rldicl %r10, %r10, 8, 56
	mfvsrd %r12, 47
	rldicl %r12, %r12, 8, 56
	rldicr %r12, %r12, 8, 55
	or %r10, %r10, %r12
	mfvsrd %r12, 48
	rldicl %r12, %r12, 8, 56
	rldicr %r12, %r12, 16, 47
	or %r10, %r10, %r12
	mfvsrd %r12, 49
	rldicl %r12, %r12, 8, 56
	rldicr %r12, %r12, 24, 39
	or %r10, %r10, %r12
	or %r7, %r10, %r10
	rldicr %r9, %r4, 40, 23
	rldicl %r9, %r9, 8, 56
	vxor %v0, %v0, %v0
	li %r12, 7
	xor %r12, %r9, %r12
	rldicr %r12, %r12, 56, 7
	mtvsrd 33, %r12
	vperm %v1, %v1, %v1, %v0
	rldicl %r12, %r9, 59, 5
	rldicr %r12, %r12, 56, 7
	mtvsrd 34, %r12
	vperm %v2, %v2, %v2, %v0
	li %r12, 255
	rldicr %r12, %r12, 56, 7
	mtvsrd 35, %r12
	addi %r15, %r3, 1024
	li %r11, 16
	li %r14, 256
	li %r9, 272
25:
	vperm %v4, %v3, %v3, %v2
	vsldoi %v3, %v0, %v3, 15
	lxvd2x 37, %r15, %r0
	vsel %v6, %v6, %v5, %v4
	lxvd2x 37, %r15, %r11
	vsel %v7, %v7, %v5, %v4
	lxvd2x 37, %r15, %r14
	vsel %v8, %v8, %v5, %v4
	lxvd2x 37, %r15, %r9
	vsel %v9, %v9, %v5, %v4
	addi %r15, %r15, 512
	lxvd2x 37, %r15, %r0
	vsel %v10, %v10, %v5, %v4
	lxvd2x 37, %r15, %r11
	vsel %v11, %v11, %v5, %v4
	lxvd2x 37, %r15, %r14
	vsel %v12, %v12, %v5, %v4
	lxvd2x 37, %r15, %r9
	vsel %v13, %v13, %v5, %v4
	addi %r15, %r15, -480
	subf %r12, %r3, %r15
	addi %r12, %r12, -1280
	cmpldi %cr0, %r12, 0
	bne %cr0, 25b
	vperm %v14, %v6, %v7, %v1
	vperm %v15, %v8, %v9, %v1
	vperm %v16, %v10, %v11, %v1
	vperm %v17, %v12, %v13, %v1
	mfvsrd %r10, 46
	rldicl %r10, %r10, 8, 56
	mfvsrd %r12, 47
	rldicl %r12, %r12, 8, 56
	rldicr %r12, %r12, 8, 55
	or %r10, %r10, %r12
	mfvsrd %r12, 48
	rldicl %r12, %r12, 8, 56
	rldicr %r12, %r12, 16, 47
	or %r10, %r10, %r12
	mfvsrd %r12, 49
	rldicl %r12, %r12, 8, 56
	rldicr %r12, %r12, 24, 39
	or %r10, %r10, %r12
	add %r7, %r7, %r10
	rldicr %r9, %r4, 48, 15
	rldicl %r9, %r9, 8, 56
	vxor %v0, %v0, %v0
	li %r12, 7
	xor %r12, %r9, %r12
	rldicr %r12, %r12, 56, 7
	mtvsrd 33, %r12
	vperm %v1, %v1, %v1, %v0
	rldicl %r12, %r9, 59, 5
	rldicr %r12, %r12, 56, 7
	mtvsrd 34, %r12
	vperm %v2, %v2, %v2, %v0
	li %r12, 255
	rldicr %r12, %r12, 56, 7
	mtvsrd 35, %r12
	addi %r15, %r3, 2048
	li %r11, 16
	li %r14, 256
	li %r9, 272
26:
	vperm %v4, %v3, %v3, %v2
	vsldoi %v3, %v0, %v3, 15
	lxvd2x 37, %r15, %r0
	vsel %v6, %v6, %v5, %v4
	lxvd2x 37, %r15, %r11
	vsel %v7, %v7, %v5, %v4
	lxvd2x 37, %r15, %r14
	vsel %v8, %v8, %v5, %v4
	lxvd2x 37, %r15, %r9
	vsel %v9, %v9, %v5, %v4
	addi %r15, %r15, 512
	lxvd2x 37, %r15, %r0
	vsel %v10, %v10, %v5, %v4
	lxvd2x 37, %r15, %r11
	vsel %v11, %v11, %v5, %v4
	lxvd2x 37, %r15, %r14
	vsel %v12, %v12, %v5, %v4
	lxvd2x 37, %r15, %r9
	vsel %v13, %v13, %v5, %v4
	addi %r15, %r15, -480
	subf %r12, %r3, %r15
	addi %r12, %r12, -2304
	cmpldi %cr0, %r12, 0
	bne %cr0, 26b
	vperm %v14, %v6, %v7, %v1
	vperm %v15, %v8, %v9, %v1
	vperm %v16, %v10, %v11, %v1
	vperm %v17, %v12, %v13, %v1
	mfvsrd %r10, 46
	rldicl %r10, %r10, 8, 56
	mfvsrd %r12, 47
	rldicl %r12, %r12, 8, 56
	rldicr %r12, %r12, 8, 55
	or %r10, %r10, %r12
	mfvsrd %r12, 48
	rldicl %r12, %r12, 8, 56
	rldicr %r12, %r12, 16, 47
	or %r10, %r10, %r12
	mfvsrd %r12, 49
	rldicl %r12, %r12, 8, 56
	rldicr %r12, %r12, 24, 39
	or %r10, %r10, %r12
	xor %r7, %r7, %r10
	rldicr %r9, %r4, 56, 7
	rldicl %r9, %r9, 8, 56
	vxor %v0, %v0, %v0
	li %r12, 7
	xor %r12, %r9, %r12
	rldicr %r12, %r12, 56, 7
	mtvsrd 33, %r12
	vperm %v1, %v1, %v1, %v0
	rldicl %r12, %r9, 59, 5
	rldicr %r12, %r12, 56, 7
	mtvsrd 34, %r12
	vperm %v2, %v2, %v2, %v0
	li %r12, 255
	rldicr %r12, %r12, 56, 7
	mtvsrd 35, %r12
	addi %r15, %r3, 3072
	li %r11, 16
	li %r14, 256
	li %r9, 272
27:
	vperm %v4, %v3, %v3, %v2
	vsldoi %v3, %v0, %v3, 15
	lxvd2x 37, %r15, %r0
	vsel %v6, %v6, %v5, %v4
	lxvd2x 37, %r15, %r11
	vsel %v7, %v7, %v5, %v4
	lxvd2x 37, %r15, %r14
	vsel %v8, %v8, %v5, %v4
	lxvd2x 37, %r15, %r9
	vsel %v9, %v9, %v5, %v4
	addi %r15, %r15, 512
	lxvd2x 37, %r15, %r0
	vsel %v10, %v10, %v5, %v4
	lxvd2x 37, %r15, %r11
	vsel %v11, %v11, %v5, %v4
	lxvd2x 37, %r15, %r14
	vsel %v12, %v12, %v5, %v4
	lxvd2x 37, %r15, %r9
	vsel %v13, %v13, %v5, %v4
	addi %r15, %r15, -480
	subf %r12, %r3, %r15
	addi %r12, %r12, -3328
	cmpldi %cr0, %r12, 0
	bne %cr0, 27b
	vperm %v14, %v6, %v7, %v1
	vperm %v15, %v8, %v9, %v1
	vperm %v16, %v10, %v11, %v1
	vperm %v17, %v12, %v13, %v1
	mfvsrd %r10, 46
	rldicl %r10, %r10, 8, 56
	mfvsrd %r12, 47
	rldicl %r12, %r12, 8, 56
	rldicr %r12, %r12, 8, 55
	or %r10, %r10, %r12
	mfvsrd %r12, 48
	rldicl %r12, %r12, 8, 56
	rldicr %r12, %r12, 16, 47
	or %r10, %r10, %r12
	mfvsrd %r12, 49
	rldicl %r12, %r12, 8, 56
	rldicr %r12, %r12, 24, 39
	or %r10, %r10, %r12
	add %r7, %r7, %r10
	xor %r5, %r5, %r7
	or %r12, %r4, %r4
	or %r4, %r5, %r5
	or %r5, %r12, %r12
	addi %r8, %r8, 4
	subf %r12, %r3, %r8
	addi %r12, %r12, -4160
	cmpldi %cr0, %r12, 0
	bne %cr0, 23b
	lwz %r12, 0(%r8)
	xor %r12, %r4, %r12
	lwz %r4, 4(%r8)
	xor %r4, %r4, %r5
	or %r5, %r12, %r12
	stwbrx %r4, %r16, %r0
	addi %r12, %r16, 4
	stwbrx %r5, %r12, %r0
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	or %r5, %r6, %r6
	ld %r14, 0(%r6)
	ld %r15, 8(%r6)
	ld %r16, 16(%r6)
	ld %r17, 24(%r6)
	lwz %r8, 32(%r5)
	stw %r8, 72(%r5)
	lwz %r8, 36(%r5)
	stw %r8, 76(%r5)
	lwz %r8, 32(%r5)
	stw %r8, 0(%r31)
	lwz %r8, 36(%r5)
	stw %r8, 4(%r31)
	addi %r31, %r31, 8
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 22b
	b 21f
20:
21:
	or %r31, %r29, %r29
	lwz %r8, 72(%r5)
	stw %r8, 0(%r31)
	lwz %r8, 76(%r5)
	stw %r8, 4(%r31)
	ld %r29, 40(%r5)
	ld %r30, 48(%r5)
	ld %r31, 56(%r5)
	ld %r0, 64(%r5)
	mtlr %r0
	addi %r12, %r1, 32
	li %r11, 0
	std %r11, 0(%r12)
	std %r11, 8(%r12)
	std %r11, 16(%r12)
	std %r11, 24(%r12)
	std %r11, 32(%r12)
	std %r11, 40(%r12)
	std %r11, 48(%r12)
	std %r11, 56(%r12)
	std %r11, 64(%r12)
	std %r11, 72(%r12)
	std %r11, 80(%r12)
	std %r11, 88(%r12)
	addi %r1, %r1, 128
	blr

vg_blowfish_cbc_decrypt_chained:
	stdu %r1, -128(%r1)
	addi %r7, %r1, 32
	mflr %r0
	std %r0, 64(%r7)
	std %r29, 40(%r7)
	std %r30, 48(%r7)
	std %r31, 56(%r7)
	or %r29, %r4, %r4
	or %r30, %r6, %r6
	or %r31, %r4, %r4
	or %r6, %r5, %r5
	or %r5, %r7, %r7
	lwz %r8, 0(%r31)
	stw %r8, 72(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 76(%r5)
	or %r31, %r6, %r6
	cmpldi %cr0, %r30, 0
	beq %cr0, 20f
22:
	lwz %r8, 0(%r31)
	stw %r8, 32(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 36(%r5)
	or %r6, %r5, %r5
	std %r14, 0(%r6)
	std %r15, 8(%r6)
	std %r16, 16(%r6)
	std %r17, 24(%r6)
	li %r0, 0
	addi %r16, %r6, 32
	lwbrx %r4, %r16, %r0
	addi %r12, %r16, 4
	lwbrx %r5, %r12, %r0
	addi %r8, %r3, 4160
23:
	lwz %r12, 4(%r8)
	xor %r4, %r4, %r12
	rldicr %r9, %r4, 32, 31
	rldicl %r9, %r9, 8, 56
	vxor %v0, %v0, %v0
	li %r12, 7
	xor %r12, %r9, %r12
	rldicr %r12, %r12, 56, 7
	mtvsrd 33, %r12
	vperm %v1, %v1, %v1, %v0
	rldicl %r12, %r9, 59, 5
	rldicr %r12, %r12, 56, 7
	mtvsrd 34, %r12
	vperm %v2, %v2, %v2, %v0
	li %r12, 255
	rldicr %r12, %r12, 56, 7
	mtvsrd 35, %r12
	addi %r15, %r3, 0
	li %r11, 16
	li %r14, 256
	li %r9, 272
24:
	vperm %v4, %v3, %v3, %v2
	vsldoi %v3, %v0, %v3, 15
	lxvd2x 37, %r15, %r0
	vsel %v6, %v6, %v5, %v4
	lxvd2x 37, %r15, %r11
	vsel %v7, %v7, %v5, %v4
	lxvd2x 37, %r15, %r14
	vsel %v8, %v8, %v5, %v4
	lxvd2x 37, %r15, %r9
	vsel %v9, %v9, %v5, %v4
	addi %r15, %r15, 512
	lxvd2x 37, %r15, %r0
	vsel %v10, %v10, %v5, %v4
	lxvd2x 37, %r15, %r11
	vsel %v11, %v11, %v5, %v4
	lxvd2x 37, %r15, %r14
	vsel %v12, %v12, %v5, %v4
	lxvd2x 37, %r15, %r9
	vsel %v13, %v13, %v5, %v4
	addi %r15, %r15, -480
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 24b
	vperm %v14, %v6, %v7, %v1
	vperm %v15, %v8, %v9, %v1
	vperm %v16, %v10, %v11, %v1
	vperm %v17, %v12, %v13, %v1
	mfvsrd %r10, 46
	rldicl %r10, %r10, 8, 56
	mfvsrd %r12, 47
	rldicl %r12, %r12, 8, 56
	rldicr %r12, %r12, 8, 55
	or %r10, %r10, %r12
	mfvsrd %r12, 48
	rldicl %r12, %r12, 8, 56
	rldicr %r12, %r12, 16, 47
	or %r10, %r10, %r12
	mfvsrd %r12, 49
	rldicl %r12, %r12, 8, 56
	rldicr %r12, %r12, 24, 39
	or %r10, %r10, %r12
	or %r7, %r10, %r10
	rldicr %r9, %r4, 40, 23
	rldicl %r9, %r9, 8, 56
	vxor %v0, %v0, %v0
	li %r12, 7
	xor %r12, %r9, %r12
	rldicr %r12, %r12, 56, 7
	mtvsrd 33, %r12
	vperm %v1, %v1, %v1, %v0
	rldicl %r12, %r9, 59, 5
	rldicr %r12, %r12, 56, 7
	mtvsrd 34, %r12
	vperm %v2, %v2, %v2, %v0
	li %r12, 255
	rldicr %r12, %r12, 56, 7
	mtvsrd 35, %r12
	addi %r15, %r3, 1024
	li %r11, 16
	li %r14, 256
	li %r9, 272
25:
	vperm %v4, %v3, %v3, %v2
	vsldoi %v3, %v0, %v3, 15
	lxvd2x 37, %r15, %r0
	vsel %v6, %v6, %v5, %v4
	lxvd2x 37, %r15, %r11
	vsel %v7, %v7, %v5, %v4
	lxvd2x 37, %r15, %r14
	vsel %v8, %v8, %v5, %v4
	lxvd2x 37, %r15, %r9
	vsel %v9, %v9, %v5, %v4
	addi %r15, %r15, 512
	lxvd2x 37, %r15, %r0
	vsel %v10, %v10, %v5, %v4
	lxvd2x 37, %r15, %r11
	vsel %v11, %v11, %v5, %v4
	lxvd2x 37, %r15, %r14
	vsel %v12, %v12, %v5, %v4
	lxvd2x 37, %r15, %r9
	vsel %v13, %v13, %v5, %v4
	addi %r15, %r15, -480
	subf %r12, %r3, %r15
	addi %r12, %r12, -1280
	cmpldi %cr0, %r12, 0
	bne %cr0, 25b
	vperm %v14, %v6, %v7, %v1
	vperm %v15, %v8, %v9, %v1
	vperm %v16, %v10, %v11, %v1
	vperm %v17, %v12, %v13, %v1
	mfvsrd %r10, 46
	rldicl %r10, %r10, 8, 56
	mfvsrd %r12, 47
	rldicl %r12, %r12, 8, 56
	rldicr %r12, %r12, 8, 55
	or %r10, %r10, %r12
	mfvsrd %r12, 48
	rldicl %r12, %r12, 8, 56
	rldicr %r12, %r12, 16, 47
	or %r10, %r10, %r12
	mfvsrd %r12, 49
	rldicl %r12, %r12, 8, 56
	rldicr %r12, %r12, 24, 39
	or %r10, %r10, %r12
	add %r7, %r7, %r10
	rldicr %r9, %r4, 48, 15
	rldicl %r9, %r9, 8, 56
	vxor %v0, %v0, %v0
	li %r12, 7
	xor %r12, %r9, %r12
	rldicr %r12, %r12, 56, 7
	mtvsrd 33, %r12
	vperm %v1, %v1, %v1, %v0
	rldicl %r12, %r9, 59, 5
	rldicr %r12, %r12, 56, 7
	mtvsrd 34, %r12
	vperm %v2, %v2, %v2, %v0
	li %r12, 255
	rldicr %r12, %r12, 56, 7
	mtvsrd 35, %r12
	addi %r15, %r3, 2048
	li %r11, 16
	li %r14, 256
	li %r9, 272
26:
	vperm %v4, %v3, %v3, %v2
	vsldoi %v3, %v0, %v3, 15
	lxvd2x 37, %r15, %r0
	vsel %v6, %v6, %v5, %v4
	lxvd2x 37, %r15, %r11
	vsel %v7, %v7, %v5, %v4
	lxvd2x 37, %r15, %r14
	vsel %v8, %v8, %v5, %v4
	lxvd2x 37, %r15, %r9
	vsel %v9, %v9, %v5, %v4
	addi %r15, %r15, 512
	lxvd2x 37, %r15, %r0
	vsel %v10, %v10, %v5, %v4
	lxvd2x 37, %r15, %r11
	vsel %v11, %v11, %v5, %v4
	lxvd2x 37, %r15, %r14
	vsel %v12, %v12, %v5, %v4
	lxvd2x 37, %r15, %r9
	vsel %v13, %v13, %v5, %v4
	addi %r15, %r15, -480
	subf %r12, %r3, %r15
	addi %r12, %r12, -2304
	cmpldi %cr0, %r12, 0
	bne %cr0, 26b
	vperm %v14, %v6, %v7, %v1
	vperm %v15, %v8, %v9, %v1
	vperm %v16, %v10, %v11, %v1
	vperm %v17, %v12, %v13, %v1
	mfvsrd %r10, 46
	rldicl %r10, %r10, 8, 56
	mfvsrd %r12, 47
	rldicl %r12, %r12, 8, 56
	rldicr %r12, %r12, 8, 55
	or %r10, %r10, %r12
	mfvsrd %r12, 48
	rldicl %r12, %r12, 8, 56
	rldicr %r12, %r12, 16, 47
	or %r10, %r10, %r12
	mfvsrd %r12, 49
	rldicl %r12, %r12, 8, 56
	rldicr %r12, %r12, 24, 39
	or %r10, %r10, %r12
	xor %r7, %r7, %r10
	rldicr %r9, %r4, 56, 7
	rldicl %r9, %r9, 8, 56
	vxor %v0, %v0, %v0
	li %r12, 7
	xor %r12, %r9, %r12
	rldicr %r12, %r12, 56, 7
	mtvsrd 33, %r12
	vperm %v1, %v1, %v1, %v0
	rldicl %r12, %r9, 59, 5
	rldicr %r12, %r12, 56, 7
	mtvsrd 34, %r12
	vperm %v2, %v2, %v2, %v0
	li %r12, 255
	rldicr %r12, %r12, 56, 7
	mtvsrd 35, %r12
	addi %r15, %r3, 3072
	li %r11, 16
	li %r14, 256
	li %r9, 272
27:
	vperm %v4, %v3, %v3, %v2
	vsldoi %v3, %v0, %v3, 15
	lxvd2x 37, %r15, %r0
	vsel %v6, %v6, %v5, %v4
	lxvd2x 37, %r15, %r11
	vsel %v7, %v7, %v5, %v4
	lxvd2x 37, %r15, %r14
	vsel %v8, %v8, %v5, %v4
	lxvd2x 37, %r15, %r9
	vsel %v9, %v9, %v5, %v4
	addi %r15, %r15, 512
	lxvd2x 37, %r15, %r0
	vsel %v10, %v10, %v5, %v4
	lxvd2x 37, %r15, %r11
	vsel %v11, %v11, %v5, %v4
	lxvd2x 37, %r15, %r14
	vsel %v12, %v12, %v5, %v4
	lxvd2x 37, %r15, %r9
	vsel %v13, %v13, %v5, %v4
	addi %r15, %r15, -480
	subf %r12, %r3, %r15
	addi %r12, %r12, -3328
	cmpldi %cr0, %r12, 0
	bne %cr0, 27b
	vperm %v14, %v6, %v7, %v1
	vperm %v15, %v8, %v9, %v1
	vperm %v16, %v10, %v11, %v1
	vperm %v17, %v12, %v13, %v1
	mfvsrd %r10, 46
	rldicl %r10, %r10, 8, 56
	mfvsrd %r12, 47
	rldicl %r12, %r12, 8, 56
	rldicr %r12, %r12, 8, 55
	or %r10, %r10, %r12
	mfvsrd %r12, 48
	rldicl %r12, %r12, 8, 56
	rldicr %r12, %r12, 16, 47
	or %r10, %r10, %r12
	mfvsrd %r12, 49
	rldicl %r12, %r12, 8, 56
	rldicr %r12, %r12, 24, 39
	or %r10, %r10, %r12
	add %r7, %r7, %r10
	xor %r5, %r5, %r7
	or %r12, %r4, %r4
	or %r4, %r5, %r5
	or %r5, %r12, %r12
	addi %r8, %r8, -4
	subf %r12, %r3, %r8
	addi %r12, %r12, -4096
	cmpldi %cr0, %r12, 0
	bne %cr0, 23b
	lwz %r12, 4(%r8)
	xor %r12, %r4, %r12
	lwz %r4, 0(%r8)
	xor %r4, %r4, %r5
	or %r5, %r12, %r12
	stwbrx %r4, %r16, %r0
	addi %r12, %r16, 4
	stwbrx %r5, %r12, %r0
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	or %r5, %r6, %r6
	ld %r14, 0(%r6)
	ld %r15, 8(%r6)
	ld %r16, 16(%r6)
	ld %r17, 24(%r6)
	lwz %r8, 32(%r5)
	lwz %r9, 72(%r5)
	xor %r8, %r8, %r9
	stw %r8, 32(%r5)
	lwz %r8, 36(%r5)
	lwz %r9, 76(%r5)
	xor %r8, %r8, %r9
	stw %r8, 36(%r5)
	lwz %r8, 0(%r31)
	stw %r8, 72(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 76(%r5)
	lwz %r8, 32(%r5)
	stw %r8, 0(%r31)
	lwz %r8, 36(%r5)
	stw %r8, 4(%r31)
	addi %r31, %r31, 8
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 22b
	b 21f
20:
21:
	or %r31, %r29, %r29
	lwz %r8, 72(%r5)
	stw %r8, 0(%r31)
	lwz %r8, 76(%r5)
	stw %r8, 4(%r31)
	ld %r29, 40(%r5)
	ld %r30, 48(%r5)
	ld %r31, 56(%r5)
	ld %r0, 64(%r5)
	mtlr %r0
	addi %r12, %r1, 32
	li %r11, 0
	std %r11, 0(%r12)
	std %r11, 8(%r12)
	std %r11, 16(%r12)
	std %r11, 24(%r12)
	std %r11, 32(%r12)
	std %r11, 40(%r12)
	std %r11, 48(%r12)
	std %r11, 56(%r12)
	std %r11, 64(%r12)
	std %r11, 72(%r12)
	std %r11, 80(%r12)
	std %r11, 88(%r12)
	addi %r1, %r1, 128
	blr
