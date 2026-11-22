// The functions of `src/internal/vg_sha512_digest_core.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_digest_core:
	stdu %r1, -608(%r1)
	addi %r6, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r20, 528(%r6)
	std %r21, 536(%r6)
	std %r22, 544(%r6)
	std %r23, 552(%r6)
	std %r24, 560(%r6)
	std %r25, 568(%r6)
	addi %r21, %r6, 0
	addi %r22, %r5, 0
	addi %r23, %r3, 0
	addi %r24, %r4, 0
	addi %r20, %r6, 272
	addi %r3, %r20, 0
	bl {vg_sha512_init}
	addi %r3, %r20, 0
	li %r4, 0
	addi %r5, %r23, 0
	addi %r6, %r24, 0
	addi %r7, %r21, 0
	bl {vg_sha512_update_scratch}
	addi %r3, %r20, 0
	addi %r4, %r24, 0
	addi %r5, %r21, 464
	addi %r6, %r21, 0
	bl {vg_sha512_finalize_scratch}
	lwz %r8, 464(%r21)
	stw %r8, 0(%r22)
	lwz %r8, 468(%r21)
	stw %r8, 4(%r22)
	lwz %r8, 472(%r21)
	stw %r8, 8(%r22)
	lwz %r8, 476(%r21)
	stw %r8, 12(%r22)
	lwz %r8, 480(%r21)
	stw %r8, 16(%r22)
	lwz %r8, 484(%r21)
	stw %r8, 20(%r22)
	lwz %r8, 488(%r21)
	stw %r8, 24(%r22)
	lwz %r8, 492(%r21)
	stw %r8, 28(%r22)
	lwz %r8, 496(%r21)
	stw %r8, 32(%r22)
	lwz %r8, 500(%r21)
	stw %r8, 36(%r22)
	lwz %r8, 504(%r21)
	stw %r8, 40(%r22)
	lwz %r8, 508(%r21)
	stw %r8, 44(%r22)
	lwz %r8, 512(%r21)
	stw %r8, 48(%r22)
	lwz %r8, 516(%r21)
	stw %r8, 52(%r22)
	lwz %r8, 520(%r21)
	stw %r8, 56(%r22)
	lwz %r8, 524(%r21)
	stw %r8, 60(%r22)
	ld %r20, 528(%r21)
	ld %r22, 544(%r21)
	ld %r23, 552(%r21)
	ld %r24, 560(%r21)
	ld %r25, 568(%r21)
	ld %r21, 536(%r21)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r12, %r1, 32
	li %r0, 0
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
	addi %r1, %r1, 608
	blr
