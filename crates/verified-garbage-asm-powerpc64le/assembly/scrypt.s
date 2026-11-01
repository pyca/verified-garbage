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
	blr
