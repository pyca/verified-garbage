// The functions of `src/internal/vg_hmac_sha1_finalize_scratch.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha1_finalize_scratch:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r20, 160(%r7)
	std %r21, 168(%r7)
	std %r22, 176(%r7)
	std %r23, 184(%r7)
	std %r24, 192(%r7)
	std %r25, 200(%r7)
	addi %r20, %r3, 0
	addi %r21, %r7, 0
	addi %r22, %r4, 0
	addi %r23, %r6, 0
	addi %r4, %r5, 0
	addi %r5, %r7, 208
	addi %r6, %r7, 0
	bl {vg_sha1_finalize_scratch}
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
	addi %r3, %r20, 0
	li %r4, 64
	addi %r5, %r21, 208
	li %r6, 20
	addi %r7, %r21, 0
	bl {vg_sha1_update_scratch}
	addi %r3, %r20, 0
	li %r4, 84
	addi %r5, %r21, 208
	addi %r6, %r21, 0
	bl {vg_sha1_finalize_scratch}
	lwz %r8, 208(%r21)
	stw %r8, 0(%r23)
	lwz %r8, 212(%r21)
	stw %r8, 4(%r23)
	lwz %r8, 216(%r21)
	stw %r8, 8(%r23)
	lwz %r8, 220(%r21)
	stw %r8, 12(%r23)
	lwz %r8, 224(%r21)
	stw %r8, 16(%r23)
	ld %r20, 160(%r21)
	ld %r22, 176(%r21)
	ld %r23, 184(%r21)
	ld %r24, 192(%r21)
	ld %r25, 200(%r21)
	ld %r21, 168(%r21)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr
