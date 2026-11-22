// The functions of `src/ed25519.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_key_pair:
	stdu %r1, -64(%r1)
	mflr %r0
	addi %r12, %r1, 32
	std %r0, 0(%r12)
	std %r3, 8(%r12)
	std %r4, 16(%r12)
	std %r6, 24(%r12)
	addi %r3, %r5, 0
	addi %r5, %r4, 0
	li %r4, 32
	bl {vg_sha512_digest_core}
	addi %r12, %r1, 32
	ld %r3, 8(%r12)
	ld %r4, 16(%r12)
	ld %r5, 24(%r12)
	bl {vg_ed25519_public_key_expanded}
	addi %r12, %r1, 32
	ld %r0, 0(%r12)
	mtlr %r0
	addi %r1, %r1, 64
	li %r0, 0
	stdu %r1, -720(%r1)
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
	addi %r1, %r1, 720
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
	addc %r0, %r0, %r0
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

vg_ed25519_sign_expanded:
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
	ld %r8, 0(%r21)
	std %r8, 128(%r25)
	ld %r8, 8(%r21)
	std %r8, 136(%r25)
	ld %r8, 16(%r21)
	std %r8, 144(%r25)
	ld %r8, 24(%r21)
	std %r8, 152(%r25)
	ld %r8, 32(%r21)
	std %r8, 160(%r25)
	ld %r8, 40(%r21)
	std %r8, 168(%r25)
	ld %r8, 48(%r21)
	std %r8, 176(%r25)
	ld %r8, 56(%r21)
	std %r8, 184(%r25)
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
	std %r0, 128(%r12)
	std %r0, 136(%r12)
	std %r0, 144(%r12)
	std %r0, 152(%r12)
	std %r0, 160(%r12)
	std %r0, 168(%r12)
	std %r0, 176(%r12)
	std %r0, 184(%r12)
	std %r0, 192(%r12)
	std %r0, 200(%r12)
	std %r0, 208(%r12)
	std %r0, 216(%r12)
	addi %r1, %r1, 320
	li %r0, 0
	stdu %r1, -320(%r1)
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
	std %r0, 128(%r12)
	std %r0, 136(%r12)
	std %r0, 144(%r12)
	std %r0, 152(%r12)
	std %r0, 160(%r12)
	std %r0, 168(%r12)
	std %r0, 176(%r12)
	std %r0, 184(%r12)
	std %r0, 192(%r12)
	std %r0, 200(%r12)
	std %r0, 208(%r12)
	std %r0, 216(%r12)
	std %r0, 224(%r12)
	std %r0, 232(%r12)
	std %r0, 240(%r12)
	std %r0, 248(%r12)
	std %r0, 256(%r12)
	std %r0, 264(%r12)
	std %r0, 272(%r12)
	std %r0, 280(%r12)
	addi %r1, %r1, 320
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
	addc %r0, %r0, %r0
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
	li %r0, 0
	stdu %r1, -224(%r1)
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
	std %r0, 128(%r12)
	std %r0, 136(%r12)
	std %r0, 144(%r12)
	std %r0, 152(%r12)
	std %r0, 160(%r12)
	std %r0, 168(%r12)
	std %r0, 176(%r12)
	std %r0, 184(%r12)
	addi %r1, %r1, 224
	rldicr %r3, %r3, 32, 31
	rldicl %r3, %r3, 32, 32
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	addc %r0, %r0, %r0
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
