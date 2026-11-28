// The functions of `src/internal/vg_ed448_scalar_reduce.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_scalar_reduce:
	std %r14, 1064(%r5)
	std %r15, 1072(%r5)
	std %r16, 1080(%r5)
	std %r17, 1088(%r5)
	std %r18, 1096(%r5)
	std %r19, 1104(%r5)
	std %r26, 1112(%r5)
	std %r27, 1120(%r5)
	std %r28, 1128(%r5)
	std %r29, 1136(%r5)
	std %r30, 1144(%r5)
	std %r31, 1152(%r5)
	addi %r6, %r5, 0
	addi %r27, %r3, 0
	addi %r14, %r4, 0
	mflr %r9
	li %r15, 114
	bl {vg_ed448_scalar_engine}
	mtlr %r9
	addi %r14, %r27, 0
	lwz %r7, 0(%r6)
	stw %r7, 0(%r14)
	lwz %r7, 4(%r6)
	stw %r7, 4(%r14)
	lwz %r7, 8(%r6)
	stw %r7, 8(%r14)
	lwz %r7, 12(%r6)
	stw %r7, 12(%r14)
	lwz %r7, 16(%r6)
	stw %r7, 16(%r14)
	lwz %r7, 20(%r6)
	stw %r7, 20(%r14)
	lwz %r7, 24(%r6)
	stw %r7, 24(%r14)
	lwz %r7, 28(%r6)
	stw %r7, 28(%r14)
	lwz %r7, 32(%r6)
	stw %r7, 32(%r14)
	lwz %r7, 36(%r6)
	stw %r7, 36(%r14)
	lwz %r7, 40(%r6)
	stw %r7, 40(%r14)
	lwz %r7, 44(%r6)
	stw %r7, 44(%r14)
	lwz %r7, 48(%r6)
	stw %r7, 48(%r14)
	lwz %r7, 52(%r6)
	stw %r7, 52(%r14)
	li %r7, 0
	stb %r7, 56(%r14)
	ld %r14, 1064(%r6)
	ld %r15, 1072(%r6)
	ld %r16, 1080(%r6)
	ld %r17, 1088(%r6)
	ld %r18, 1096(%r6)
	ld %r19, 1104(%r6)
	ld %r26, 1112(%r6)
	ld %r27, 1120(%r6)
	ld %r28, 1128(%r6)
	ld %r29, 1136(%r6)
	ld %r30, 1144(%r6)
	ld %r31, 1152(%r6)
	blr
