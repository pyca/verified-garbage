// The functions of `src/ed448.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_public_key:
	stdu %r1, -192(%r1)
	addi %r6, %r1, 32
	mflr %r0
	std %r21, 120(%r6)
	std %r22, 128(%r6)
	std %r23, 136(%r6)
	std %r24, 144(%r6)
	std %r0, 152(%r6)
	addi %r21, %r3, 0
	addi %r22, %r4, 0
	addi %r23, %r5, 0
	addi %r24, %r6, 0
	li %r0, 0
	std %r0, 0(%r23)
	std %r0, 8(%r23)
	std %r0, 16(%r23)
	std %r0, 24(%r23)
	std %r0, 32(%r23)
	std %r0, 40(%r23)
	std %r0, 48(%r23)
	std %r0, 56(%r23)
	std %r0, 64(%r23)
	std %r0, 72(%r23)
	std %r0, 80(%r23)
	std %r0, 88(%r23)
	std %r0, 96(%r23)
	std %r0, 104(%r23)
	std %r0, 112(%r23)
	std %r0, 120(%r23)
	std %r0, 128(%r23)
	std %r0, 136(%r23)
	std %r0, 144(%r23)
	std %r0, 152(%r23)
	std %r0, 160(%r23)
	std %r0, 168(%r23)
	std %r0, 176(%r23)
	std %r0, 184(%r23)
	std %r0, 192(%r23)
	li %r5, 0
	addi %r3, %r23, 0
	li %r4, 136
	addi %r6, %r22, 0
	li %r7, 57
	addi %r8, %r23, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r23, 0
	li %r4, 136
	li %r6, 31
	addi %r7, %r23, 200
	bl {vg_keccak_pad_scratch}
	addi %r3, %r23, 0
	li %r4, 136
	li %r5, 0
	addi %r6, %r24, 0
	li %r7, 114
	addi %r8, %r23, 200
	bl {vg_keccak_squeeze_scratch}
	lbz %r8, 0(%r24)
	rldicl %r8, %r8, 62, 2
	rldicr %r8, %r8, 2, 61
	stb %r8, 0(%r24)
	lbz %r8, 55(%r24)
	ori %r8, %r8, 128
	stb %r8, 55(%r24)
	li %r8, 0
	stb %r8, 56(%r24)
	addi %r3, %r21, 0
	addi %r4, %r24, 0
	addi %r5, %r23, 0
	bl {vg_ed448_scalar_base}
	ld %r0, 152(%r24)
	ld %r21, 120(%r24)
	ld %r22, 128(%r24)
	ld %r23, 136(%r24)
	ld %r24, 144(%r24)
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
	addi %r1, %r1, 192
	blr

vg_ed448_sign_cached:
	stdu %r1, -576(%r1)
	addi %r12, %r1, 0
	addi %r0, %r12, 104
	std %r0, 96(%r12)
	addi %r12, %r1, 0
	ld %r12, 96(%r12)
	mflr %r0
	std %r20, 384(%r12)
	std %r22, 392(%r12)
	std %r23, 400(%r12)
	std %r24, 408(%r12)
	std %r25, 416(%r12)
	std %r28, 424(%r12)
	std %r29, 432(%r12)
	std %r30, 440(%r12)
	std %r21, 448(%r12)
	std %r0, 456(%r12)
	addi %r20, %r3, 0
	addi %r22, %r10, 0
	addi %r23, %r4, 0
	addi %r24, %r5, 0
	addi %r25, %r6, 0
	addi %r28, %r7, 0
	addi %r29, %r8, 0
	addi %r30, %r9, 0
	addi %r21, %r12, 0
	lis %r8, 14388
	ori %r8, %r8, 13412
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 17767
	ori %r8, %r8, 26963
	std %r8, 0(%r21)
	li %r8, 0
	stb %r8, 8(%r21)
	stb %r28, 9(%r21)
	li %r0, 0
	std %r0, 0(%r22)
	std %r0, 8(%r22)
	std %r0, 16(%r22)
	std %r0, 24(%r22)
	std %r0, 32(%r22)
	std %r0, 40(%r22)
	std %r0, 48(%r22)
	std %r0, 56(%r22)
	std %r0, 64(%r22)
	std %r0, 72(%r22)
	std %r0, 80(%r22)
	std %r0, 88(%r22)
	std %r0, 96(%r22)
	std %r0, 104(%r22)
	std %r0, 112(%r22)
	std %r0, 120(%r22)
	std %r0, 128(%r22)
	std %r0, 136(%r22)
	std %r0, 144(%r22)
	std %r0, 152(%r22)
	std %r0, 160(%r22)
	std %r0, 168(%r22)
	std %r0, 176(%r22)
	std %r0, 184(%r22)
	std %r0, 192(%r22)
	li %r5, 0
	addi %r3, %r22, 0
	li %r4, 136
	addi %r6, %r23, 0
	li %r7, 57
	addi %r8, %r22, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r22, 0
	li %r4, 136
	li %r6, 31
	addi %r7, %r22, 200
	bl {vg_keccak_pad_scratch}
	addi %r3, %r22, 0
	li %r4, 136
	li %r5, 0
	addi %r6, %r21, 136
	li %r7, 114
	addi %r8, %r22, 200
	bl {vg_keccak_squeeze_scratch}
	lbz %r8, 136(%r21)
	rldicl %r8, %r8, 62, 2
	rldicr %r8, %r8, 2, 61
	stb %r8, 136(%r21)
	lbz %r8, 191(%r21)
	ori %r8, %r8, 128
	stb %r8, 191(%r21)
	li %r8, 0
	stb %r8, 192(%r21)
	li %r0, 0
	std %r0, 0(%r22)
	std %r0, 8(%r22)
	std %r0, 16(%r22)
	std %r0, 24(%r22)
	std %r0, 32(%r22)
	std %r0, 40(%r22)
	std %r0, 48(%r22)
	std %r0, 56(%r22)
	std %r0, 64(%r22)
	std %r0, 72(%r22)
	std %r0, 80(%r22)
	std %r0, 88(%r22)
	std %r0, 96(%r22)
	std %r0, 104(%r22)
	std %r0, 112(%r22)
	std %r0, 120(%r22)
	std %r0, 128(%r22)
	std %r0, 136(%r22)
	std %r0, 144(%r22)
	std %r0, 152(%r22)
	std %r0, 160(%r22)
	std %r0, 168(%r22)
	std %r0, 176(%r22)
	std %r0, 184(%r22)
	std %r0, 192(%r22)
	li %r5, 0
	addi %r3, %r22, 0
	li %r4, 136
	addi %r6, %r21, 0
	li %r7, 10
	addi %r8, %r22, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r22, 0
	li %r4, 136
	addi %r6, %r25, 0
	addi %r7, %r28, 0
	addi %r8, %r22, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r22, 0
	li %r4, 136
	addi %r6, %r21, 193
	li %r7, 57
	addi %r8, %r22, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r22, 0
	li %r4, 136
	addi %r6, %r29, 0
	addi %r7, %r30, 0
	addi %r8, %r22, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r22, 0
	li %r4, 136
	li %r6, 31
	addi %r7, %r22, 200
	bl {vg_keccak_pad_scratch}
	addi %r3, %r22, 0
	li %r4, 136
	li %r5, 0
	addi %r6, %r21, 16
	li %r7, 114
	addi %r8, %r22, 200
	bl {vg_keccak_squeeze_scratch}
	addi %r3, %r21, 256
	addi %r4, %r21, 16
	addi %r5, %r22, 0
	bl {vg_ed448_scalar_reduce}
	addi %r3, %r20, 0
	addi %r4, %r21, 256
	addi %r5, %r22, 0
	bl {vg_ed448_scalar_base}
	li %r0, 0
	std %r0, 0(%r22)
	std %r0, 8(%r22)
	std %r0, 16(%r22)
	std %r0, 24(%r22)
	std %r0, 32(%r22)
	std %r0, 40(%r22)
	std %r0, 48(%r22)
	std %r0, 56(%r22)
	std %r0, 64(%r22)
	std %r0, 72(%r22)
	std %r0, 80(%r22)
	std %r0, 88(%r22)
	std %r0, 96(%r22)
	std %r0, 104(%r22)
	std %r0, 112(%r22)
	std %r0, 120(%r22)
	std %r0, 128(%r22)
	std %r0, 136(%r22)
	std %r0, 144(%r22)
	std %r0, 152(%r22)
	std %r0, 160(%r22)
	std %r0, 168(%r22)
	std %r0, 176(%r22)
	std %r0, 184(%r22)
	std %r0, 192(%r22)
	li %r5, 0
	addi %r3, %r22, 0
	li %r4, 136
	addi %r6, %r21, 0
	li %r7, 10
	addi %r8, %r22, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r22, 0
	li %r4, 136
	addi %r6, %r25, 0
	addi %r7, %r28, 0
	addi %r8, %r22, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r22, 0
	li %r4, 136
	addi %r6, %r20, 0
	li %r7, 57
	addi %r8, %r22, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r22, 0
	li %r4, 136
	addi %r6, %r24, 0
	li %r7, 57
	addi %r8, %r22, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r22, 0
	li %r4, 136
	addi %r6, %r29, 0
	addi %r7, %r30, 0
	addi %r8, %r22, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r22, 0
	li %r4, 136
	li %r6, 31
	addi %r7, %r22, 200
	bl {vg_keccak_pad_scratch}
	addi %r3, %r22, 0
	li %r4, 136
	li %r5, 0
	addi %r6, %r21, 16
	li %r7, 114
	addi %r8, %r22, 200
	bl {vg_keccak_squeeze_scratch}
	addi %r3, %r21, 320
	addi %r4, %r21, 16
	addi %r5, %r22, 0
	bl {vg_ed448_scalar_reduce}
	addi %r3, %r20, 57
	addi %r4, %r21, 256
	addi %r5, %r21, 320
	addi %r6, %r21, 136
	addi %r7, %r22, 0
	bl {vg_ed448_scalar_mul_add}
	li %r8, 0
	std %r8, 16(%r21)
	std %r8, 24(%r21)
	std %r8, 32(%r21)
	std %r8, 40(%r21)
	std %r8, 48(%r21)
	std %r8, 56(%r21)
	std %r8, 64(%r21)
	std %r8, 72(%r21)
	std %r8, 80(%r21)
	std %r8, 88(%r21)
	std %r8, 96(%r21)
	std %r8, 104(%r21)
	std %r8, 112(%r21)
	std %r8, 120(%r21)
	std %r8, 128(%r21)
	std %r8, 136(%r21)
	std %r8, 144(%r21)
	std %r8, 152(%r21)
	std %r8, 160(%r21)
	std %r8, 168(%r21)
	std %r8, 176(%r21)
	std %r8, 184(%r21)
	std %r8, 192(%r21)
	std %r8, 200(%r21)
	std %r8, 208(%r21)
	std %r8, 216(%r21)
	std %r8, 224(%r21)
	std %r8, 232(%r21)
	std %r8, 240(%r21)
	std %r8, 248(%r21)
	std %r8, 256(%r21)
	std %r8, 264(%r21)
	std %r8, 272(%r21)
	std %r8, 280(%r21)
	std %r8, 288(%r21)
	std %r8, 296(%r21)
	std %r8, 304(%r21)
	std %r8, 312(%r21)
	std %r8, 320(%r21)
	std %r8, 328(%r21)
	std %r8, 336(%r21)
	std %r8, 344(%r21)
	std %r8, 352(%r21)
	std %r8, 360(%r21)
	std %r8, 368(%r21)
	std %r8, 376(%r21)
	ld %r0, 456(%r21)
	ld %r20, 384(%r21)
	ld %r22, 392(%r21)
	ld %r23, 400(%r21)
	ld %r24, 408(%r21)
	ld %r25, 416(%r21)
	ld %r28, 424(%r21)
	ld %r29, 432(%r21)
	ld %r30, 440(%r21)
	ld %r21, 448(%r21)
	mtlr %r0
	addi %r1, %r1, 576
	blr

vg_ed448_verify:
	stdu %r1, -304(%r1)
	addi %r10, %r1, 32
	rldicl %r11, %r5, 56, 8
	cmpldi %cr0, %r11, 0
	beq %cr0, 20f
	li %r3, 0
	b 21f
20:
	mflr %r0
	std %r20, 200(%r10)
	std %r21, 208(%r10)
	std %r22, 216(%r10)
	std %r24, 224(%r10)
	std %r25, 232(%r10)
	std %r28, 240(%r10)
	std %r29, 248(%r10)
	std %r23, 256(%r10)
	std %r0, 264(%r10)
	addi %r20, %r3, 0
	addi %r21, %r8, 0
	addi %r22, %r9, 0
	addi %r24, %r4, 0
	addi %r25, %r5, 0
	addi %r28, %r6, 0
	addi %r29, %r7, 0
	addi %r23, %r10, 0
	lis %r8, 14388
	ori %r8, %r8, 13412
	rldicr %r8, %r8, 32, 31
	oris %r8, %r8, 17767
	ori %r8, %r8, 26963
	std %r8, 0(%r23)
	li %r8, 0
	stb %r8, 8(%r23)
	stb %r25, 9(%r23)
	li %r0, 0
	std %r0, 0(%r22)
	std %r0, 8(%r22)
	std %r0, 16(%r22)
	std %r0, 24(%r22)
	std %r0, 32(%r22)
	std %r0, 40(%r22)
	std %r0, 48(%r22)
	std %r0, 56(%r22)
	std %r0, 64(%r22)
	std %r0, 72(%r22)
	std %r0, 80(%r22)
	std %r0, 88(%r22)
	std %r0, 96(%r22)
	std %r0, 104(%r22)
	std %r0, 112(%r22)
	std %r0, 120(%r22)
	std %r0, 128(%r22)
	std %r0, 136(%r22)
	std %r0, 144(%r22)
	std %r0, 152(%r22)
	std %r0, 160(%r22)
	std %r0, 168(%r22)
	std %r0, 176(%r22)
	std %r0, 184(%r22)
	std %r0, 192(%r22)
	li %r5, 0
	addi %r3, %r22, 0
	li %r4, 136
	addi %r6, %r23, 0
	li %r7, 10
	addi %r8, %r22, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r22, 0
	li %r4, 136
	addi %r6, %r24, 0
	addi %r7, %r25, 0
	addi %r8, %r22, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r22, 0
	li %r4, 136
	addi %r6, %r21, 0
	li %r7, 57
	addi %r8, %r22, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r22, 0
	li %r4, 136
	addi %r6, %r20, 0
	li %r7, 57
	addi %r8, %r22, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r22, 0
	li %r4, 136
	addi %r6, %r28, 0
	addi %r7, %r29, 0
	addi %r8, %r22, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r22, 0
	li %r4, 136
	li %r6, 31
	addi %r7, %r22, 200
	bl {vg_keccak_pad_scratch}
	addi %r3, %r22, 0
	li %r4, 136
	li %r5, 0
	addi %r6, %r23, 16
	li %r7, 114
	addi %r8, %r22, 200
	bl {vg_keccak_squeeze_scratch}
	addi %r3, %r23, 136
	addi %r4, %r23, 16
	addi %r5, %r22, 0
	bl {vg_ed448_scalar_reduce}
	addi %r3, %r20, 0
	addi %r4, %r21, 0
	addi %r5, %r23, 136
	addi %r6, %r22, 0
	bl {vg_ed448_verify_equation}
	ld %r0, 264(%r23)
	ld %r20, 200(%r23)
	ld %r21, 208(%r23)
	ld %r22, 216(%r23)
	ld %r24, 224(%r23)
	ld %r25, 232(%r23)
	ld %r28, 240(%r23)
	ld %r29, 248(%r23)
	ld %r23, 256(%r23)
	mtlr %r0
21:
	addi %r1, %r1, 304
	blr
