// The functions of `src/scrypt.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_scrypt:
	stdu %r1, -112(%r1)
	addi %r12, %r1, 0
	mflr %r0
	std %r0, 32(%r12)
	std %r30, 40(%r12)
	std %r3, 48(%r12)
	std %r4, 56(%r12)
	std %r7, 64(%r12)
	std %r8, 72(%r12)
	std %r9, 80(%r12)
	std %r10, 88(%r12)
	addi %r30, %r12, 0
	li %r7, 1
	rldicr %r9, %r9, 7, 56
	ld %r10, 216(%r30)
	bl {vg_pbkdf2_hmac_sha256_scratch}
	ld %r3, 72(%r30)
	std %r3, 96(%r30)
20:
	ld %r3, 96(%r30)
	ld %r4, 64(%r30)
	ld %r5, 88(%r30)
	ld %r6, 208(%r30)
	ld %r7, 216(%r30)
	addi %r8, %r4, 2
	bl {vg_scrypt_romix}
	ld %r3, 96(%r30)
	ld %r4, 64(%r30)
	rldicr %r4, %r4, 7, 56
	add %r3, %r3, %r4
	std %r3, 96(%r30)
	ld %r5, 72(%r30)
	ld %r6, 80(%r30)
	rldicr %r6, %r6, 7, 56
	add %r5, %r5, %r6
	subf %r5, %r3, %r5
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	ld %r3, 48(%r30)
	ld %r4, 56(%r30)
	ld %r5, 72(%r30)
	ld %r6, 80(%r30)
	rldicr %r6, %r6, 7, 56
	li %r7, 1
	ld %r8, 232(%r30)
	ld %r9, 240(%r30)
	ld %r10, 216(%r30)
	bl {vg_pbkdf2_hmac_sha256_scratch}
	ld %r0, 32(%r30)
	mtlr %r0
	ld %r30, 40(%r30)
	addi %r1, %r1, 112
	li %r0, 0
	stdu %r1, -1120(%r1)
	addi %r12, %r1, 32
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	std %r0, 128(%r12)
	std %r0, 136(%r12)
	std %r0, 144(%r12)
	std %r0, 152(%r12)
	std %r0, 160(%r12)
	std %r0, 168(%r12)
	std %r0, 176(%r12)
	std %r0, 184(%r12)
	addi %r1, %r1, 1120
	li %r3, 0
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v9, %v9, %v9
	vxor %v10, %v10, %v10
	vxor %v11, %v11, %v11
	vxor %v12, %v12, %v12
	vxor %v13, %v13, %v13
	vxor %v14, %v14, %v14
	vxor %v15, %v15, %v15
	vxor %v16, %v16, %v16
	vxor %v17, %v17, %v17
	vxor %v18, %v18, %v18
	vxor %v19, %v19, %v19
	blr
