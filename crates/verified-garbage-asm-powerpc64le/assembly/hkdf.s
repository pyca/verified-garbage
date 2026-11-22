// The functions of `src/hkdf.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hkdf_extract:
	stdu %r1, -2336(%r1)
	mflr %r0
	addi %r11, %r1, 0
	std %r0, 32(%r11)
	std %r14, 40(%r11)
	std %r15, 48(%r11)
	std %r16, 56(%r11)
	std %r17, 64(%r11)
	or %r14, %r5, %r5
	or %r15, %r6, %r6
	or %r16, %r7, %r7
	or %r17, %r9, %r9
	or %r5, %r3, %r3
	or %r6, %r4, %r4
	addi %r3, %r1, 80
	addi %r4, %r1, 272
	addi %r7, %r1, 464
	ld %r12, 0(%r17)
	mtctr %r12
	bctrl
	addi %r3, %r1, 80
	ld %r4, 40(%r17)
	or %r5, %r14, %r14
	or %r6, %r15, %r15
	addi %r7, %r1, 464
	ld %r12, 8(%r17)
	mtctr %r12
	bctrl
	addi %r3, %r1, 80
	addi %r4, %r1, 272
	ld %r5, 40(%r17)
	add %r5, %r5, %r15
	or %r6, %r16, %r16
	addi %r7, %r1, 464
	ld %r12, 16(%r17)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r0, 32(%r11)
	mtlr %r0
	ld %r14, 40(%r11)
	ld %r15, 48(%r11)
	ld %r16, 56(%r11)
	ld %r17, 64(%r11)
	addi %r1, %r1, 2336
	li %r0, 0
	stdu %r1, -2480(%r1)
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
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
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
	addi %r1, %r1, 2480
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

vg_hkdf_key:
	stdu %r1, -1920(%r1)
	mflr %r0
	addi %r11, %r1, 0
	std %r0, 32(%r11)
	or %r8, %r6, %r6
	or %r9, %r3, %r3
	or %r10, %r4, %r4
	or %r3, %r5, %r5
	addi %r4, %r5, 192
	or %r5, %r9, %r9
	or %r6, %r10, %r10
	addi %r7, %r1, 48
	ld %r12, 0(%r8)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r0, 32(%r11)
	mtlr %r0
	addi %r1, %r1, 1920
	li %r0, 0
	stdu %r1, -2064(%r1)
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
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
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
	std %r0, 176(%r12)
	std %r0, 184(%r12)
	std %r0, 192(%r12)
	std %r0, 200(%r12)
	std %r0, 208(%r12)
	std %r0, 216(%r12)
	std %r0, 224(%r12)
	std %r0, 232(%r12)
	addi %r1, %r1, 2064
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

vg_hkdf_expand:
	stdu %r1, -2256(%r1)
	mflr %r0
	addi %r11, %r1, 0
	std %r0, 32(%r11)
	std %r14, 40(%r11)
	std %r15, 48(%r11)
	std %r16, 56(%r11)
	std %r17, 64(%r11)
	std %r18, 72(%r11)
	std %r19, 80(%r11)
	std %r20, 88(%r11)
	std %r21, 96(%r11)
	std %r22, 104(%r11)
	std %r23, 112(%r11)
	or %r14, %r8, %r8
	or %r15, %r3, %r3
	or %r16, %r4, %r4
	or %r17, %r5, %r5
	or %r18, %r6, %r6
	or %r19, %r7, %r7
	ld %r20, 32(%r14)
	ld %r21, 40(%r14)
	li %r22, 0
	li %r23, 1
	cmpldi %cr0, %r19, 0
	bne %cr0, 20f
	b 21f
20:
22:
	or %r4, %r15, %r15
	addi %r5, %r1, 120
	li %r6, 64
23:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 23b
	addi %r3, %r1, 120
	or %r4, %r21, %r21
	addi %r5, %r1, 312
	or %r6, %r22, %r22
	addi %r7, %r1, 384
	ld %r12, 8(%r14)
	mtctr %r12
	bctrl
	addi %r3, %r1, 120
	add %r4, %r21, %r22
	or %r5, %r16, %r16
	or %r6, %r17, %r17
	addi %r7, %r1, 384
	ld %r12, 8(%r14)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	stb %r23, 376(%r11)
	addi %r3, %r1, 120
	add %r4, %r21, %r22
	add %r4, %r4, %r17
	addi %r5, %r1, 376
	li %r6, 1
	addi %r7, %r1, 384
	ld %r12, 8(%r14)
	mtctr %r12
	bctrl
	addi %r3, %r1, 120
	addi %r4, %r15, 192
	add %r5, %r21, %r22
	add %r5, %r5, %r17
	addi %r5, %r5, 1
	addi %r6, %r1, 312
	addi %r7, %r1, 384
	ld %r12, 16(%r14)
	mtctr %r12
	bctrl
	subf %r10, %r20, %r19
	rldicl %r6, %r10, 1, 63
	li %r7, 0
	subf %r6, %r6, %r7
	and %r10, %r10, %r6
	add %r6, %r20, %r10
	or %r9, %r6, %r6
	addi %r4, %r1, 312
	or %r5, %r18, %r18
	subf %r19, %r6, %r19
24:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 24b
	add %r18, %r18, %r9
	or %r22, %r20, %r20
	addi %r23, %r23, 1
	cmpldi %cr0, %r19, 0
	bne %cr0, 22b
21:
	addi %r11, %r1, 0
	ld %r0, 32(%r11)
	mtlr %r0
	ld %r14, 40(%r11)
	ld %r15, 48(%r11)
	ld %r16, 56(%r11)
	ld %r17, 64(%r11)
	ld %r18, 72(%r11)
	ld %r19, 80(%r11)
	ld %r20, 88(%r11)
	ld %r21, 96(%r11)
	ld %r22, 104(%r11)
	ld %r23, 112(%r11)
	addi %r1, %r1, 2256
	li %r0, 0
	stdu %r1, -2352(%r1)
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
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
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
	addi %r1, %r1, 2352
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
