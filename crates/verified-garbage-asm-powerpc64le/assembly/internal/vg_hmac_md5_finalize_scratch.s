// The functions of `src/internal/vg_hmac_md5_finalize_scratch.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_md5_finalize_scratch:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r20, 112(%r7)
	std %r21, 120(%r7)
	std %r22, 128(%r7)
	std %r23, 136(%r7)
	std %r24, 144(%r7)
	std %r25, 152(%r7)
	addi %r20, %r3, 0
	addi %r21, %r7, 0
	addi %r22, %r4, 0
	addi %r23, %r6, 0
	addi %r4, %r5, 0
	addi %r5, %r7, 160
	addi %r6, %r7, 0
	bl {vg_md5_finalize_scratch}
	lwz %r8, 0(%r22)
	stw %r8, 0(%r20)
	lwz %r8, 4(%r22)
	stw %r8, 4(%r20)
	lwz %r8, 8(%r22)
	stw %r8, 8(%r20)
	lwz %r8, 12(%r22)
	stw %r8, 12(%r20)
	addi %r3, %r20, 0
	li %r4, 64
	addi %r5, %r21, 160
	li %r6, 16
	addi %r7, %r21, 0
	bl {vg_md5_update_scratch}
	addi %r3, %r20, 0
	li %r4, 80
	addi %r5, %r21, 160
	addi %r6, %r21, 0
	bl {vg_md5_finalize_scratch}
	lwz %r8, 160(%r21)
	stw %r8, 0(%r23)
	lwz %r8, 164(%r21)
	stw %r8, 4(%r23)
	lwz %r8, 168(%r21)
	stw %r8, 8(%r23)
	lwz %r8, 172(%r21)
	stw %r8, 12(%r23)
	ld %r20, 112(%r21)
	ld %r22, 128(%r21)
	ld %r23, 136(%r21)
	ld %r24, 144(%r21)
	ld %r25, 152(%r21)
	ld %r21, 120(%r21)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr
