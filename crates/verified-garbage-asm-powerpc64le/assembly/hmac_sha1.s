// The functions of `src/hmac_sha1.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha1_init:
	rldicl %r12, %r6, 57, 7
	li %r11, 127
	and %r11, %r6, %r11
	addi %r11, %r11, 63
	rldicl %r11, %r11, 57, 7
	add %r12, %r12, %r11
	cmpldi %cr0, %r12, 0
	bne %cr0, 20f
	stdu %r1, -480(%r1)
	addi %r7, %r1, 32
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
	addi %r23, %r5, 0
	addi %r24, %r6, 0
	bl {vg_sha1_init}
	addi %r3, %r22, 0
	bl {vg_sha1_init}
	li %r12, 54
	li %r25, 0
	addi %r9, %r23, 0
	addi %r10, %r24, 0
	cmpldi %cr0, %r10, 0
	beq %cr0, 22f
24:
	lbz %r8, 0(%r9)
	xor %r8, %r8, %r12
	add %r11, %r22, %r25
	stb %r8, 20(%r11)
	addi %r9, %r9, 1
	addi %r25, %r25, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 24b
	b 23f
22:
23:
	li %r10, 64
	subf %r10, %r25, %r10
	cmpldi %cr0, %r10, 0
	beq %cr0, 25f
27:
	add %r11, %r22, %r25
	stb %r12, 20(%r11)
	addi %r25, %r25, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 27b
	b 26f
25:
26:
	addi %r3, %r20, 0
	li %r4, 0
	addi %r5, %r22, 20
	li %r6, 64
	addi %r7, %r21, 0
	bl {vg_sha1_update_scratch}
	li %r12, 92
	li %r25, 0
	addi %r9, %r23, 0
	addi %r10, %r24, 0
	cmpldi %cr0, %r10, 0
	beq %cr0, 28f
210:
	lbz %r8, 0(%r9)
	xor %r8, %r8, %r12
	add %r11, %r20, %r25
	stb %r8, 20(%r11)
	addi %r9, %r9, 1
	addi %r25, %r25, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 210b
	b 29f
28:
29:
	li %r10, 64
	subf %r10, %r25, %r10
	cmpldi %cr0, %r10, 0
	beq %cr0, 211f
213:
	add %r11, %r20, %r25
	stb %r12, 20(%r11)
	addi %r25, %r25, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 213b
	b 212f
211:
212:
	addi %r3, %r22, 0
	li %r4, 0
	addi %r5, %r20, 20
	li %r6, 64
	addi %r7, %r21, 0
	bl {vg_sha1_update_scratch}
	ld %r20, 160(%r21)
	ld %r22, 176(%r21)
	ld %r23, 184(%r21)
	ld %r24, 192(%r21)
	ld %r25, 200(%r21)
	ld %r21, 168(%r21)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 480
21:
	blr
20:
	stdu %r1, -432(%r1)
	addi %r7, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r20, 312(%r7)
	std %r21, 320(%r7)
	std %r22, 328(%r7)
	std %r23, 336(%r7)
	std %r24, 344(%r7)
	std %r25, 352(%r7)
	addi %r21, %r7, 0
	addi %r22, %r3, 0
	addi %r23, %r4, 0
	addi %r24, %r6, 0
	addi %r25, %r5, 0
	addi %r20, %r7, 208
	addi %r3, %r20, 0
	bl {vg_sha1_init}
	addi %r3, %r20, 0
	li %r4, 0
	addi %r5, %r25, 0
	addi %r6, %r24, 0
	addi %r7, %r21, 0
	bl {vg_sha1_update_scratch}
	addi %r3, %r20, 0
	addi %r4, %r24, 0
	addi %r5, %r21, 292
	addi %r6, %r21, 0
	bl {vg_sha1_finalize_scratch}
	addi %r3, %r22, 0
	addi %r4, %r23, 0
	addi %r5, %r21, 292
	li %r6, 20
	addi %r7, %r21, 0
	ld %r20, 312(%r21)
	ld %r22, 328(%r21)
	ld %r23, 336(%r21)
	ld %r24, 344(%r21)
	ld %r25, 352(%r21)
	ld %r21, 320(%r21)
	bl {vg_hmac_sha1_init_scratch}
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
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
	std %r11, 224(%r12)
	std %r11, 232(%r12)
	std %r11, 240(%r12)
	std %r11, 248(%r12)
	std %r11, 256(%r12)
	std %r11, 264(%r12)
	std %r11, 272(%r12)
	std %r11, 280(%r12)
	std %r11, 288(%r12)
	std %r11, 296(%r12)
	std %r11, 304(%r12)
	std %r11, 312(%r12)
	std %r11, 320(%r12)
	std %r11, 328(%r12)
	std %r11, 336(%r12)
	std %r11, 344(%r12)
	std %r11, 352(%r12)
	addi %r1, %r1, 432
	b 21b

vg_hmac_sha1_finalize:
	stdu %r1, -480(%r1)
	addi %r7, %r1, 32
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
	addi %r1, %r1, 480
	blr

vg_hmac_sha1_init_scratch:
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
	addi %r23, %r5, 0
	addi %r24, %r6, 0
	bl {vg_sha1_init}
	addi %r3, %r22, 0
	bl {vg_sha1_init}
	li %r12, 54
	li %r25, 0
	addi %r9, %r23, 0
	addi %r10, %r24, 0
	cmpldi %cr0, %r10, 0
	beq %cr0, 20f
22:
	lbz %r8, 0(%r9)
	xor %r8, %r8, %r12
	add %r11, %r22, %r25
	stb %r8, 20(%r11)
	addi %r9, %r9, 1
	addi %r25, %r25, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 22b
	b 21f
20:
21:
	li %r10, 64
	subf %r10, %r25, %r10
	cmpldi %cr0, %r10, 0
	beq %cr0, 23f
25:
	add %r11, %r22, %r25
	stb %r12, 20(%r11)
	addi %r25, %r25, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 25b
	b 24f
23:
24:
	addi %r3, %r20, 0
	li %r4, 0
	addi %r5, %r22, 20
	li %r6, 64
	addi %r7, %r21, 0
	bl {vg_sha1_update_scratch}
	li %r12, 92
	li %r25, 0
	addi %r9, %r23, 0
	addi %r10, %r24, 0
	cmpldi %cr0, %r10, 0
	beq %cr0, 26f
28:
	lbz %r8, 0(%r9)
	xor %r8, %r8, %r12
	add %r11, %r20, %r25
	stb %r8, 20(%r11)
	addi %r9, %r9, 1
	addi %r25, %r25, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 28b
	b 27f
26:
27:
	li %r10, 64
	subf %r10, %r25, %r10
	cmpldi %cr0, %r10, 0
	beq %cr0, 29f
211:
	add %r11, %r20, %r25
	stb %r12, 20(%r11)
	addi %r25, %r25, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 211b
	b 210f
29:
210:
	addi %r3, %r22, 0
	li %r4, 0
	addi %r5, %r20, 20
	li %r6, 64
	addi %r7, %r21, 0
	bl {vg_sha1_update_scratch}
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
