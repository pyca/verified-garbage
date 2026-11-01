// The functions of `src/ed25519.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_public_key:
	stdu %r1, -176(%r1)
	addi %r6, %r1, 32
	mflr %r0
	std %r20, 96(%r6)
	std %r21, 104(%r6)
	std %r22, 112(%r6)
	std %r23, 120(%r6)
	std %r0, 128(%r6)
	addi %r20, %r3, 0
	addi %r21, %r4, 0
	addi %r22, %r5, 0
	addi %r23, %r6, 0
	addi %r3, %r22, 0
	bl {vg_sha512_init}
	addi %r3, %r22, 0
	li %r4, 0
	addi %r5, %r21, 0
	li %r6, 32
	addi %r7, %r22, 192
	bl {vg_sha512_update_scratch}
	addi %r3, %r22, 0
	li %r4, 32
	addi %r5, %r23, 0
	addi %r6, %r22, 192
	bl {vg_sha512_finalize_scratch}
	ld %r8, 0(%r23)
	rldicl %r8, %r8, 61, 3
	rldicr %r8, %r8, 3, 60
	std %r8, 64(%r23)
	ld %r8, 8(%r23)
	std %r8, 72(%r23)
	ld %r8, 16(%r23)
	std %r8, 80(%r23)
	ld %r8, 24(%r23)
	rldicr %r8, %r8, 2, 61
	rldicl %r8, %r8, 62, 2
	lis %r9, 16384
	rldicr %r9, %r9, 32, 31
	or %r8, %r8, %r9
	std %r8, 88(%r23)
	addi %r3, %r20, 0
	addi %r4, %r23, 64
	addi %r5, %r22, 0
	bl {vg_ed25519_scalar_base}
	ld %r0, 128(%r23)
	ld %r20, 96(%r23)
	ld %r21, 104(%r23)
	ld %r22, 112(%r23)
	ld %r23, 120(%r23)
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
	std %r11, 96(%r12)
	std %r11, 104(%r12)
	std %r11, 112(%r12)
	std %r11, 120(%r12)
	std %r11, 128(%r12)
	addi %r1, %r1, 176
	blr

vg_ed25519_sign_cached:
	stdu %r1, -320(%r1)
	addi %r9, %r1, 32
	mflr %r0
	std %r20, 224(%r9)
	std %r21, 232(%r9)
	std %r22, 240(%r9)
	std %r23, 248(%r9)
	std %r24, 256(%r9)
	std %r25, 264(%r9)
	std %r0, 272(%r9)
	addi %r20, %r3, 0
	addi %r21, %r4, 0
	addi %r22, %r6, 0
	addi %r23, %r7, 0
	addi %r24, %r8, 0
	addi %r25, %r9, 0
	ld %r8, 0(%r5)
	std %r8, 192(%r25)
	ld %r8, 8(%r5)
	std %r8, 200(%r25)
	ld %r8, 16(%r5)
	std %r8, 208(%r25)
	ld %r8, 24(%r5)
	std %r8, 216(%r25)
	addi %r3, %r24, 0
	bl {vg_sha512_init}
	addi %r3, %r24, 0
	li %r4, 0
	addi %r5, %r21, 0
	li %r6, 32
	addi %r7, %r24, 192
	bl {vg_sha512_update_scratch}
	addi %r3, %r24, 0
	li %r4, 32
	addi %r5, %r25, 128
	addi %r6, %r24, 192
	bl {vg_sha512_finalize_scratch}
	ld %r8, 128(%r25)
	rldicl %r8, %r8, 61, 3
	rldicr %r8, %r8, 3, 60
	std %r8, 0(%r25)
	ld %r8, 136(%r25)
	std %r8, 8(%r25)
	ld %r8, 144(%r25)
	std %r8, 16(%r25)
	ld %r8, 152(%r25)
	rldicr %r8, %r8, 2, 61
	rldicl %r8, %r8, 62, 2
	lis %r9, 16384
	rldicr %r9, %r9, 32, 31
	or %r8, %r8, %r9
	std %r8, 24(%r25)
	ld %r8, 160(%r25)
	std %r8, 32(%r25)
	ld %r8, 168(%r25)
	std %r8, 40(%r25)
	ld %r8, 176(%r25)
	std %r8, 48(%r25)
	ld %r8, 184(%r25)
	std %r8, 56(%r25)
	addi %r3, %r24, 0
	bl {vg_sha512_init}
	addi %r3, %r24, 0
	li %r4, 0
	addi %r5, %r25, 32
	li %r6, 32
	addi %r7, %r24, 192
	bl {vg_sha512_update_scratch}
	addi %r3, %r24, 0
	li %r4, 32
	addi %r5, %r22, 0
	addi %r6, %r23, 0
	addi %r7, %r24, 192
	bl {vg_sha512_update_scratch}
	addi %r3, %r24, 0
	addi %r4, %r23, 32
	addi %r5, %r25, 128
	addi %r6, %r24, 192
	bl {vg_sha512_finalize_scratch}
	addi %r3, %r25, 64
	addi %r4, %r25, 128
	addi %r5, %r24, 0
	bl {vg_ed25519_scalar_reduce}
	addi %r3, %r20, 0
	addi %r4, %r25, 64
	addi %r5, %r24, 0
	bl {vg_ed25519_scalar_base}
	addi %r3, %r24, 0
	bl {vg_sha512_init}
	addi %r3, %r24, 0
	li %r4, 0
	addi %r5, %r20, 0
	li %r6, 32
	addi %r7, %r24, 192
	bl {vg_sha512_update_scratch}
	addi %r3, %r24, 0
	li %r4, 32
	addi %r5, %r25, 192
	li %r6, 32
	addi %r7, %r24, 192
	bl {vg_sha512_update_scratch}
	addi %r3, %r24, 0
	li %r4, 64
	addi %r5, %r22, 0
	addi %r6, %r23, 0
	addi %r7, %r24, 192
	bl {vg_sha512_update_scratch}
	addi %r3, %r24, 0
	addi %r4, %r23, 64
	addi %r5, %r25, 128
	addi %r6, %r24, 192
	bl {vg_sha512_finalize_scratch}
	addi %r3, %r25, 96
	addi %r4, %r25, 128
	addi %r5, %r24, 0
	bl {vg_ed25519_scalar_reduce}
	addi %r3, %r20, 32
	addi %r4, %r25, 64
	addi %r5, %r25, 96
	addi %r6, %r25, 0
	addi %r7, %r24, 0
	bl {vg_ed25519_scalar_mul_add}
	ld %r0, 272(%r25)
	ld %r20, 224(%r25)
	ld %r21, 232(%r25)
	ld %r22, 240(%r25)
	ld %r23, 248(%r25)
	ld %r24, 256(%r25)
	ld %r25, 264(%r25)
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
	std %r11, 96(%r12)
	std %r11, 104(%r12)
	std %r11, 112(%r12)
	std %r11, 120(%r12)
	std %r11, 128(%r12)
	std %r11, 136(%r12)
	std %r11, 144(%r12)
	std %r11, 152(%r12)
	std %r11, 160(%r12)
	std %r11, 168(%r12)
	std %r11, 176(%r12)
	std %r11, 184(%r12)
	std %r11, 192(%r12)
	std %r11, 200(%r12)
	std %r11, 208(%r12)
	std %r11, 216(%r12)
	addi %r1, %r1, 320
	blr

vg_ed25519_verify:
	stdu %r1, -224(%r1)
	addi %r8, %r1, 32
	mflr %r0
	std %r20, 128(%r8)
	std %r21, 136(%r8)
	std %r22, 144(%r8)
	std %r23, 152(%r8)
	std %r24, 160(%r8)
	std %r25, 168(%r8)
	std %r0, 176(%r8)
	addi %r20, %r3, 0
	addi %r21, %r4, 0
	addi %r22, %r5, 0
	addi %r23, %r6, 0
	addi %r24, %r7, 0
	addi %r25, %r8, 0
	addi %r3, %r24, 0
	bl {vg_sha512_init}
	addi %r3, %r24, 0
	li %r4, 0
	addi %r5, %r23, 0
	li %r6, 32
	addi %r7, %r24, 192
	bl {vg_sha512_update_scratch}
	addi %r3, %r24, 0
	li %r4, 32
	addi %r5, %r20, 0
	li %r6, 32
	addi %r7, %r24, 192
	bl {vg_sha512_update_scratch}
	addi %r3, %r24, 0
	li %r4, 64
	addi %r5, %r21, 0
	addi %r6, %r22, 0
	addi %r7, %r24, 192
	bl {vg_sha512_update_scratch}
	addi %r3, %r24, 0
	addi %r4, %r22, 64
	addi %r5, %r25, 64
	addi %r6, %r24, 192
	bl {vg_sha512_finalize_scratch}
	addi %r3, %r25, 0
	addi %r4, %r25, 64
	addi %r5, %r24, 0
	bl {vg_ed25519_scalar_reduce}
	li %r8, 0
	std %r8, 32(%r25)
	std %r8, 40(%r25)
	std %r8, 48(%r25)
	std %r8, 56(%r25)
	addi %r3, %r20, 0
	addi %r4, %r23, 0
	addi %r5, %r25, 0
	addi %r6, %r24, 0
	bl {vg_ed25519_verify_equation}
	ld %r0, 176(%r25)
	ld %r20, 128(%r25)
	ld %r21, 136(%r25)
	ld %r22, 144(%r25)
	ld %r23, 152(%r25)
	ld %r24, 160(%r25)
	ld %r25, 168(%r25)
	mtlr %r0
	addi %r1, %r1, 224
	blr
