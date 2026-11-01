// The functions of `src/internal/vg_hmac_sha512_finalize_scratch.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha512_finalize_scratch:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r20, 224(%r7)
	std %r21, 232(%r7)
	std %r22, 240(%r7)
	std %r23, 248(%r7)
	std %r24, 256(%r7)
	std %r25, 264(%r7)
	addi %r20, %r3, 0
	addi %r21, %r7, 0
	addi %r22, %r4, 0
	addi %r23, %r6, 0
	addi %r4, %r5, 0
	addi %r5, %r7, 272
	addi %r6, %r7, 0
	bl {vg_sha512_finalize_scratch}
	lwz %r8, 0(%r22)
	stw %r8, 0(%r20)
	lwz %r8, 4(%r22)
	stw %r8, 4(%r20)
	lwz %r8, 8(%r22)
	stw %r8, 8(%r20)
	lwz %r8, 12(%r22)
	stw %r8, 12(%r20)
	lwz %r8, 16(%r22)
	stw %r8, 16(%r20)
	lwz %r8, 20(%r22)
	stw %r8, 20(%r20)
	lwz %r8, 24(%r22)
	stw %r8, 24(%r20)
	lwz %r8, 28(%r22)
	stw %r8, 28(%r20)
	lwz %r8, 32(%r22)
	stw %r8, 32(%r20)
	lwz %r8, 36(%r22)
	stw %r8, 36(%r20)
	lwz %r8, 40(%r22)
	stw %r8, 40(%r20)
	lwz %r8, 44(%r22)
	stw %r8, 44(%r20)
	lwz %r8, 48(%r22)
	stw %r8, 48(%r20)
	lwz %r8, 52(%r22)
	stw %r8, 52(%r20)
	lwz %r8, 56(%r22)
	stw %r8, 56(%r20)
	lwz %r8, 60(%r22)
	stw %r8, 60(%r20)
	addi %r3, %r20, 0
	li %r4, 128
	addi %r5, %r21, 272
	li %r6, 64
	addi %r7, %r21, 0
	bl {vg_sha512_update_scratch}
	addi %r3, %r20, 0
	li %r4, 192
	addi %r5, %r21, 272
	addi %r6, %r21, 0
	bl {vg_sha512_finalize_scratch}
	lwz %r8, 272(%r21)
	stw %r8, 0(%r23)
	lwz %r8, 276(%r21)
	stw %r8, 4(%r23)
	lwz %r8, 280(%r21)
	stw %r8, 8(%r23)
	lwz %r8, 284(%r21)
	stw %r8, 12(%r23)
	lwz %r8, 288(%r21)
	stw %r8, 16(%r23)
	lwz %r8, 292(%r21)
	stw %r8, 20(%r23)
	lwz %r8, 296(%r21)
	stw %r8, 24(%r23)
	lwz %r8, 300(%r21)
	stw %r8, 28(%r23)
	lwz %r8, 304(%r21)
	stw %r8, 32(%r23)
	lwz %r8, 308(%r21)
	stw %r8, 36(%r23)
	lwz %r8, 312(%r21)
	stw %r8, 40(%r23)
	lwz %r8, 316(%r21)
	stw %r8, 44(%r23)
	lwz %r8, 320(%r21)
	stw %r8, 48(%r23)
	lwz %r8, 324(%r21)
	stw %r8, 52(%r23)
	lwz %r8, 328(%r21)
	stw %r8, 56(%r23)
	lwz %r8, 332(%r21)
	stw %r8, 60(%r23)
	ld %r20, 224(%r21)
	ld %r22, 240(%r21)
	ld %r23, 248(%r21)
	ld %r24, 256(%r21)
	ld %r25, 264(%r21)
	ld %r21, 232(%r21)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr
