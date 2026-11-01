// The functions of `src/scrypt.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_salsa20_8:
	std %r14, 0(%r4)
	std %r15, 8(%r4)
	std %r16, 16(%r4)
	std %r17, 24(%r4)
	std %r18, 32(%r4)
	std %r19, 40(%r4)
	std %r20, 48(%r4)
	std %r21, 56(%r4)
	lwz %r5, 0(%r3)
	lwz %r6, 4(%r3)
	lwz %r7, 8(%r3)
	lwz %r8, 12(%r3)
	lwz %r9, 16(%r3)
	lwz %r10, 20(%r3)
	lwz %r11, 24(%r3)
	lwz %r12, 28(%r3)
	lwz %r14, 32(%r3)
	lwz %r15, 36(%r3)
	lwz %r16, 40(%r3)
	lwz %r17, 44(%r3)
	lwz %r18, 48(%r3)
	lwz %r19, 52(%r3)
	lwz %r20, 56(%r3)
	lwz %r21, 60(%r3)
	add %r0, %r5, %r18
	rlwinm %r0, %r0, 7, 0, 31
	xor %r9, %r9, %r0
	add %r0, %r9, %r5
	rlwinm %r0, %r0, 9, 0, 31
	xor %r14, %r14, %r0
	add %r0, %r14, %r9
	rlwinm %r0, %r0, 13, 0, 31
	xor %r18, %r18, %r0
	add %r0, %r18, %r14
	rlwinm %r0, %r0, 18, 0, 31
	xor %r5, %r5, %r0
	add %r0, %r10, %r6
	rlwinm %r0, %r0, 7, 0, 31
	xor %r15, %r15, %r0
	add %r0, %r15, %r10
	rlwinm %r0, %r0, 9, 0, 31
	xor %r19, %r19, %r0
	add %r0, %r19, %r15
	rlwinm %r0, %r0, 13, 0, 31
	xor %r6, %r6, %r0
	add %r0, %r6, %r19
	rlwinm %r0, %r0, 18, 0, 31
	xor %r10, %r10, %r0
	add %r0, %r16, %r11
	rlwinm %r0, %r0, 7, 0, 31
	xor %r20, %r20, %r0
	add %r0, %r20, %r16
	rlwinm %r0, %r0, 9, 0, 31
	xor %r7, %r7, %r0
	add %r0, %r7, %r20
	rlwinm %r0, %r0, 13, 0, 31
	xor %r11, %r11, %r0
	add %r0, %r11, %r7
	rlwinm %r0, %r0, 18, 0, 31
	xor %r16, %r16, %r0
	add %r0, %r21, %r17
	rlwinm %r0, %r0, 7, 0, 31
	xor %r8, %r8, %r0
	add %r0, %r8, %r21
	rlwinm %r0, %r0, 9, 0, 31
	xor %r12, %r12, %r0
	add %r0, %r12, %r8
	rlwinm %r0, %r0, 13, 0, 31
	xor %r17, %r17, %r0
	add %r0, %r17, %r12
	rlwinm %r0, %r0, 18, 0, 31
	xor %r21, %r21, %r0
	add %r0, %r5, %r8
	rlwinm %r0, %r0, 7, 0, 31
	xor %r6, %r6, %r0
	add %r0, %r6, %r5
	rlwinm %r0, %r0, 9, 0, 31
	xor %r7, %r7, %r0
	add %r0, %r7, %r6
	rlwinm %r0, %r0, 13, 0, 31
	xor %r8, %r8, %r0
	add %r0, %r8, %r7
	rlwinm %r0, %r0, 18, 0, 31
	xor %r5, %r5, %r0
	add %r0, %r10, %r9
	rlwinm %r0, %r0, 7, 0, 31
	xor %r11, %r11, %r0
	add %r0, %r11, %r10
	rlwinm %r0, %r0, 9, 0, 31
	xor %r12, %r12, %r0
	add %r0, %r12, %r11
	rlwinm %r0, %r0, 13, 0, 31
	xor %r9, %r9, %r0
	add %r0, %r9, %r12
	rlwinm %r0, %r0, 18, 0, 31
	xor %r10, %r10, %r0
	add %r0, %r16, %r15
	rlwinm %r0, %r0, 7, 0, 31
	xor %r17, %r17, %r0
	add %r0, %r17, %r16
	rlwinm %r0, %r0, 9, 0, 31
	xor %r14, %r14, %r0
	add %r0, %r14, %r17
	rlwinm %r0, %r0, 13, 0, 31
	xor %r15, %r15, %r0
	add %r0, %r15, %r14
	rlwinm %r0, %r0, 18, 0, 31
	xor %r16, %r16, %r0
	add %r0, %r21, %r20
	rlwinm %r0, %r0, 7, 0, 31
	xor %r18, %r18, %r0
	add %r0, %r18, %r21
	rlwinm %r0, %r0, 9, 0, 31
	xor %r19, %r19, %r0
	add %r0, %r19, %r18
	rlwinm %r0, %r0, 13, 0, 31
	xor %r20, %r20, %r0
	add %r0, %r20, %r19
	rlwinm %r0, %r0, 18, 0, 31
	xor %r21, %r21, %r0
	add %r0, %r5, %r18
	rlwinm %r0, %r0, 7, 0, 31
	xor %r9, %r9, %r0
	add %r0, %r9, %r5
	rlwinm %r0, %r0, 9, 0, 31
	xor %r14, %r14, %r0
	add %r0, %r14, %r9
	rlwinm %r0, %r0, 13, 0, 31
	xor %r18, %r18, %r0
	add %r0, %r18, %r14
	rlwinm %r0, %r0, 18, 0, 31
	xor %r5, %r5, %r0
	add %r0, %r10, %r6
	rlwinm %r0, %r0, 7, 0, 31
	xor %r15, %r15, %r0
	add %r0, %r15, %r10
	rlwinm %r0, %r0, 9, 0, 31
	xor %r19, %r19, %r0
	add %r0, %r19, %r15
	rlwinm %r0, %r0, 13, 0, 31
	xor %r6, %r6, %r0
	add %r0, %r6, %r19
	rlwinm %r0, %r0, 18, 0, 31
	xor %r10, %r10, %r0
	add %r0, %r16, %r11
	rlwinm %r0, %r0, 7, 0, 31
	xor %r20, %r20, %r0
	add %r0, %r20, %r16
	rlwinm %r0, %r0, 9, 0, 31
	xor %r7, %r7, %r0
	add %r0, %r7, %r20
	rlwinm %r0, %r0, 13, 0, 31
	xor %r11, %r11, %r0
	add %r0, %r11, %r7
	rlwinm %r0, %r0, 18, 0, 31
	xor %r16, %r16, %r0
	add %r0, %r21, %r17
	rlwinm %r0, %r0, 7, 0, 31
	xor %r8, %r8, %r0
	add %r0, %r8, %r21
	rlwinm %r0, %r0, 9, 0, 31
	xor %r12, %r12, %r0
	add %r0, %r12, %r8
	rlwinm %r0, %r0, 13, 0, 31
	xor %r17, %r17, %r0
	add %r0, %r17, %r12
	rlwinm %r0, %r0, 18, 0, 31
	xor %r21, %r21, %r0
	add %r0, %r5, %r8
	rlwinm %r0, %r0, 7, 0, 31
	xor %r6, %r6, %r0
	add %r0, %r6, %r5
	rlwinm %r0, %r0, 9, 0, 31
	xor %r7, %r7, %r0
	add %r0, %r7, %r6
	rlwinm %r0, %r0, 13, 0, 31
	xor %r8, %r8, %r0
	add %r0, %r8, %r7
	rlwinm %r0, %r0, 18, 0, 31
	xor %r5, %r5, %r0
	add %r0, %r10, %r9
	rlwinm %r0, %r0, 7, 0, 31
	xor %r11, %r11, %r0
	add %r0, %r11, %r10
	rlwinm %r0, %r0, 9, 0, 31
	xor %r12, %r12, %r0
	add %r0, %r12, %r11
	rlwinm %r0, %r0, 13, 0, 31
	xor %r9, %r9, %r0
	add %r0, %r9, %r12
	rlwinm %r0, %r0, 18, 0, 31
	xor %r10, %r10, %r0
	add %r0, %r16, %r15
	rlwinm %r0, %r0, 7, 0, 31
	xor %r17, %r17, %r0
	add %r0, %r17, %r16
	rlwinm %r0, %r0, 9, 0, 31
	xor %r14, %r14, %r0
	add %r0, %r14, %r17
	rlwinm %r0, %r0, 13, 0, 31
	xor %r15, %r15, %r0
	add %r0, %r15, %r14
	rlwinm %r0, %r0, 18, 0, 31
	xor %r16, %r16, %r0
	add %r0, %r21, %r20
	rlwinm %r0, %r0, 7, 0, 31
	xor %r18, %r18, %r0
	add %r0, %r18, %r21
	rlwinm %r0, %r0, 9, 0, 31
	xor %r19, %r19, %r0
	add %r0, %r19, %r18
	rlwinm %r0, %r0, 13, 0, 31
	xor %r20, %r20, %r0
	add %r0, %r20, %r19
	rlwinm %r0, %r0, 18, 0, 31
	xor %r21, %r21, %r0
	add %r0, %r5, %r18
	rlwinm %r0, %r0, 7, 0, 31
	xor %r9, %r9, %r0
	add %r0, %r9, %r5
	rlwinm %r0, %r0, 9, 0, 31
	xor %r14, %r14, %r0
	add %r0, %r14, %r9
	rlwinm %r0, %r0, 13, 0, 31
	xor %r18, %r18, %r0
	add %r0, %r18, %r14
	rlwinm %r0, %r0, 18, 0, 31
	xor %r5, %r5, %r0
	add %r0, %r10, %r6
	rlwinm %r0, %r0, 7, 0, 31
	xor %r15, %r15, %r0
	add %r0, %r15, %r10
	rlwinm %r0, %r0, 9, 0, 31
	xor %r19, %r19, %r0
	add %r0, %r19, %r15
	rlwinm %r0, %r0, 13, 0, 31
	xor %r6, %r6, %r0
	add %r0, %r6, %r19
	rlwinm %r0, %r0, 18, 0, 31
	xor %r10, %r10, %r0
	add %r0, %r16, %r11
	rlwinm %r0, %r0, 7, 0, 31
	xor %r20, %r20, %r0
	add %r0, %r20, %r16
	rlwinm %r0, %r0, 9, 0, 31
	xor %r7, %r7, %r0
	add %r0, %r7, %r20
	rlwinm %r0, %r0, 13, 0, 31
	xor %r11, %r11, %r0
	add %r0, %r11, %r7
	rlwinm %r0, %r0, 18, 0, 31
	xor %r16, %r16, %r0
	add %r0, %r21, %r17
	rlwinm %r0, %r0, 7, 0, 31
	xor %r8, %r8, %r0
	add %r0, %r8, %r21
	rlwinm %r0, %r0, 9, 0, 31
	xor %r12, %r12, %r0
	add %r0, %r12, %r8
	rlwinm %r0, %r0, 13, 0, 31
	xor %r17, %r17, %r0
	add %r0, %r17, %r12
	rlwinm %r0, %r0, 18, 0, 31
	xor %r21, %r21, %r0
	add %r0, %r5, %r8
	rlwinm %r0, %r0, 7, 0, 31
	xor %r6, %r6, %r0
	add %r0, %r6, %r5
	rlwinm %r0, %r0, 9, 0, 31
	xor %r7, %r7, %r0
	add %r0, %r7, %r6
	rlwinm %r0, %r0, 13, 0, 31
	xor %r8, %r8, %r0
	add %r0, %r8, %r7
	rlwinm %r0, %r0, 18, 0, 31
	xor %r5, %r5, %r0
	add %r0, %r10, %r9
	rlwinm %r0, %r0, 7, 0, 31
	xor %r11, %r11, %r0
	add %r0, %r11, %r10
	rlwinm %r0, %r0, 9, 0, 31
	xor %r12, %r12, %r0
	add %r0, %r12, %r11
	rlwinm %r0, %r0, 13, 0, 31
	xor %r9, %r9, %r0
	add %r0, %r9, %r12
	rlwinm %r0, %r0, 18, 0, 31
	xor %r10, %r10, %r0
	add %r0, %r16, %r15
	rlwinm %r0, %r0, 7, 0, 31
	xor %r17, %r17, %r0
	add %r0, %r17, %r16
	rlwinm %r0, %r0, 9, 0, 31
	xor %r14, %r14, %r0
	add %r0, %r14, %r17
	rlwinm %r0, %r0, 13, 0, 31
	xor %r15, %r15, %r0
	add %r0, %r15, %r14
	rlwinm %r0, %r0, 18, 0, 31
	xor %r16, %r16, %r0
	add %r0, %r21, %r20
	rlwinm %r0, %r0, 7, 0, 31
	xor %r18, %r18, %r0
	add %r0, %r18, %r21
	rlwinm %r0, %r0, 9, 0, 31
	xor %r19, %r19, %r0
	add %r0, %r19, %r18
	rlwinm %r0, %r0, 13, 0, 31
	xor %r20, %r20, %r0
	add %r0, %r20, %r19
	rlwinm %r0, %r0, 18, 0, 31
	xor %r21, %r21, %r0
	add %r0, %r5, %r18
	rlwinm %r0, %r0, 7, 0, 31
	xor %r9, %r9, %r0
	add %r0, %r9, %r5
	rlwinm %r0, %r0, 9, 0, 31
	xor %r14, %r14, %r0
	add %r0, %r14, %r9
	rlwinm %r0, %r0, 13, 0, 31
	xor %r18, %r18, %r0
	add %r0, %r18, %r14
	rlwinm %r0, %r0, 18, 0, 31
	xor %r5, %r5, %r0
	add %r0, %r10, %r6
	rlwinm %r0, %r0, 7, 0, 31
	xor %r15, %r15, %r0
	add %r0, %r15, %r10
	rlwinm %r0, %r0, 9, 0, 31
	xor %r19, %r19, %r0
	add %r0, %r19, %r15
	rlwinm %r0, %r0, 13, 0, 31
	xor %r6, %r6, %r0
	add %r0, %r6, %r19
	rlwinm %r0, %r0, 18, 0, 31
	xor %r10, %r10, %r0
	add %r0, %r16, %r11
	rlwinm %r0, %r0, 7, 0, 31
	xor %r20, %r20, %r0
	add %r0, %r20, %r16
	rlwinm %r0, %r0, 9, 0, 31
	xor %r7, %r7, %r0
	add %r0, %r7, %r20
	rlwinm %r0, %r0, 13, 0, 31
	xor %r11, %r11, %r0
	add %r0, %r11, %r7
	rlwinm %r0, %r0, 18, 0, 31
	xor %r16, %r16, %r0
	add %r0, %r21, %r17
	rlwinm %r0, %r0, 7, 0, 31
	xor %r8, %r8, %r0
	add %r0, %r8, %r21
	rlwinm %r0, %r0, 9, 0, 31
	xor %r12, %r12, %r0
	add %r0, %r12, %r8
	rlwinm %r0, %r0, 13, 0, 31
	xor %r17, %r17, %r0
	add %r0, %r17, %r12
	rlwinm %r0, %r0, 18, 0, 31
	xor %r21, %r21, %r0
	add %r0, %r5, %r8
	rlwinm %r0, %r0, 7, 0, 31
	xor %r6, %r6, %r0
	add %r0, %r6, %r5
	rlwinm %r0, %r0, 9, 0, 31
	xor %r7, %r7, %r0
	add %r0, %r7, %r6
	rlwinm %r0, %r0, 13, 0, 31
	xor %r8, %r8, %r0
	add %r0, %r8, %r7
	rlwinm %r0, %r0, 18, 0, 31
	xor %r5, %r5, %r0
	add %r0, %r10, %r9
	rlwinm %r0, %r0, 7, 0, 31
	xor %r11, %r11, %r0
	add %r0, %r11, %r10
	rlwinm %r0, %r0, 9, 0, 31
	xor %r12, %r12, %r0
	add %r0, %r12, %r11
	rlwinm %r0, %r0, 13, 0, 31
	xor %r9, %r9, %r0
	add %r0, %r9, %r12
	rlwinm %r0, %r0, 18, 0, 31
	xor %r10, %r10, %r0
	add %r0, %r16, %r15
	rlwinm %r0, %r0, 7, 0, 31
	xor %r17, %r17, %r0
	add %r0, %r17, %r16
	rlwinm %r0, %r0, 9, 0, 31
	xor %r14, %r14, %r0
	add %r0, %r14, %r17
	rlwinm %r0, %r0, 13, 0, 31
	xor %r15, %r15, %r0
	add %r0, %r15, %r14
	rlwinm %r0, %r0, 18, 0, 31
	xor %r16, %r16, %r0
	add %r0, %r21, %r20
	rlwinm %r0, %r0, 7, 0, 31
	xor %r18, %r18, %r0
	add %r0, %r18, %r21
	rlwinm %r0, %r0, 9, 0, 31
	xor %r19, %r19, %r0
	add %r0, %r19, %r18
	rlwinm %r0, %r0, 13, 0, 31
	xor %r20, %r20, %r0
	add %r0, %r20, %r19
	rlwinm %r0, %r0, 18, 0, 31
	xor %r21, %r21, %r0
	lwz %r0, 0(%r3)
	add %r5, %r5, %r0
	stw %r5, 0(%r3)
	lwz %r0, 4(%r3)
	add %r6, %r6, %r0
	stw %r6, 4(%r3)
	lwz %r0, 8(%r3)
	add %r7, %r7, %r0
	stw %r7, 8(%r3)
	lwz %r0, 12(%r3)
	add %r8, %r8, %r0
	stw %r8, 12(%r3)
	lwz %r0, 16(%r3)
	add %r9, %r9, %r0
	stw %r9, 16(%r3)
	lwz %r0, 20(%r3)
	add %r10, %r10, %r0
	stw %r10, 20(%r3)
	lwz %r0, 24(%r3)
	add %r11, %r11, %r0
	stw %r11, 24(%r3)
	lwz %r0, 28(%r3)
	add %r12, %r12, %r0
	stw %r12, 28(%r3)
	lwz %r0, 32(%r3)
	add %r14, %r14, %r0
	stw %r14, 32(%r3)
	lwz %r0, 36(%r3)
	add %r15, %r15, %r0
	stw %r15, 36(%r3)
	lwz %r0, 40(%r3)
	add %r16, %r16, %r0
	stw %r16, 40(%r3)
	lwz %r0, 44(%r3)
	add %r17, %r17, %r0
	stw %r17, 44(%r3)
	lwz %r0, 48(%r3)
	add %r18, %r18, %r0
	stw %r18, 48(%r3)
	lwz %r0, 52(%r3)
	add %r19, %r19, %r0
	stw %r19, 52(%r3)
	lwz %r0, 56(%r3)
	add %r20, %r20, %r0
	stw %r20, 56(%r3)
	lwz %r0, 60(%r3)
	add %r21, %r21, %r0
	stw %r21, 60(%r3)
	ld %r14, 0(%r4)
	ld %r15, 8(%r4)
	ld %r16, 16(%r4)
	ld %r17, 24(%r4)
	ld %r18, 32(%r4)
	ld %r19, 40(%r4)
	ld %r20, 48(%r4)
	ld %r21, 56(%r4)
	blr

vg_scrypt_blockmix:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r24, 64(%r7)
	std %r25, 72(%r7)
	std %r26, 80(%r7)
	std %r28, 88(%r7)
	std %r29, 96(%r7)
	std %r27, 104(%r7)
	addi %r28, %r4, 0
	addi %r24, %r3, 0
	addi %r25, %r5, 0
	addi %r27, %r7, 0
	rldicr %r9, %r4, 6, 57
	add %r26, %r5, %r9
	rldicr %r9, %r4, 7, 56
	add %r29, %r3, %r9
	addi %r29, %r29, -64
20:
	ld %r9, 0(%r29)
	ld %r10, 0(%r24)
	xor %r9, %r9, %r10
	std %r9, 0(%r25)
	ld %r9, 8(%r29)
	ld %r10, 8(%r24)
	xor %r9, %r9, %r10
	std %r9, 8(%r25)
	ld %r9, 16(%r29)
	ld %r10, 16(%r24)
	xor %r9, %r9, %r10
	std %r9, 16(%r25)
	ld %r9, 24(%r29)
	ld %r10, 24(%r24)
	xor %r9, %r9, %r10
	std %r9, 24(%r25)
	ld %r9, 32(%r29)
	ld %r10, 32(%r24)
	xor %r9, %r9, %r10
	std %r9, 32(%r25)
	ld %r9, 40(%r29)
	ld %r10, 40(%r24)
	xor %r9, %r9, %r10
	std %r9, 40(%r25)
	ld %r9, 48(%r29)
	ld %r10, 48(%r24)
	xor %r9, %r9, %r10
	std %r9, 48(%r25)
	ld %r9, 56(%r29)
	ld %r10, 56(%r24)
	xor %r9, %r9, %r10
	std %r9, 56(%r25)
	addi %r3, %r25, 0
	addi %r4, %r27, 0
	bl {vg_salsa20_8}
	addi %r24, %r24, 64
	ld %r9, 0(%r25)
	ld %r10, 0(%r24)
	xor %r9, %r9, %r10
	std %r9, 0(%r26)
	ld %r9, 8(%r25)
	ld %r10, 8(%r24)
	xor %r9, %r9, %r10
	std %r9, 8(%r26)
	ld %r9, 16(%r25)
	ld %r10, 16(%r24)
	xor %r9, %r9, %r10
	std %r9, 16(%r26)
	ld %r9, 24(%r25)
	ld %r10, 24(%r24)
	xor %r9, %r9, %r10
	std %r9, 24(%r26)
	ld %r9, 32(%r25)
	ld %r10, 32(%r24)
	xor %r9, %r9, %r10
	std %r9, 32(%r26)
	ld %r9, 40(%r25)
	ld %r10, 40(%r24)
	xor %r9, %r9, %r10
	std %r9, 40(%r26)
	ld %r9, 48(%r25)
	ld %r10, 48(%r24)
	xor %r9, %r9, %r10
	std %r9, 48(%r26)
	ld %r9, 56(%r25)
	ld %r10, 56(%r24)
	xor %r9, %r9, %r10
	std %r9, 56(%r26)
	addi %r3, %r26, 0
	addi %r4, %r27, 0
	bl {vg_salsa20_8}
	addi %r29, %r26, 0
	addi %r24, %r24, 64
	addi %r25, %r25, 64
	addi %r26, %r26, 64
	addi %r28, %r28, -1
	cmpldi %cr0, %r28, 0
	bne %cr0, 20b
	ld %r24, 64(%r27)
	ld %r25, 72(%r27)
	ld %r26, 80(%r27)
	ld %r28, 88(%r27)
	ld %r29, 96(%r27)
	ld %r27, 104(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr

vg_scrypt_romix:
	std %r24, 128(%r7)
	std %r25, 136(%r7)
	std %r26, 144(%r7)
	std %r28, 152(%r7)
	std %r29, 160(%r7)
	std %r27, 176(%r7)
	mflr %r0
	std %r0, 168(%r7)
	addi %r24, %r3, 0
	addi %r25, %r5, 0
	addi %r27, %r7, 0
	rldicr %r26, %r4, 7, 56
	addi %r9, %r4, 0
	li %r10, 1
	add %r11, %r6, %r6
20:
	add %r9, %r9, %r9
	add %r10, %r10, %r10
	subf %r12, %r11, %r9
	cmpldi %cr0, %r12, 0
	bne %cr0, 20b
	rldicl %r10, %r10, 63, 1
	std %r10, 184(%r27)
	addi %r28, %r10, 0
	addi %r29, %r25, 0
21:
	addi %r9, %r24, 0
	addi %r10, %r29, 0
	rldicl %r11, %r26, 61, 3
22:
	ld %r12, 0(%r9)
	std %r12, 0(%r10)
	addi %r9, %r9, 8
	addi %r10, %r10, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 22b
	addi %r3, %r29, 0
	rldicl %r4, %r26, 57, 7
	addi %r5, %r24, 0
	addi %r6, %r4, 0
	addi %r7, %r27, 0
	bl {vg_scrypt_blockmix}
	add %r29, %r29, %r26
	addi %r28, %r28, -1
	cmpldi %cr0, %r28, 0
	bne %cr0, 21b
	ld %r28, 184(%r27)
	addi %r29, %r28, -1
23:
	add %r9, %r24, %r26
	addi %r9, %r9, -64
	ld %r9, 0(%r9)
	and %r9, %r9, %r29
	mulld %r10, %r9, %r26
	add %r10, %r10, %r25
	addi %r9, %r24, 0
	addi %r11, %r27, 192
	rldicl %r12, %r26, 61, 3
24:
	ld %r6, 0(%r9)
	ld %r8, 0(%r10)
	xor %r6, %r6, %r8
	std %r6, 0(%r11)
	addi %r9, %r9, 8
	addi %r10, %r10, 8
	addi %r11, %r11, 8
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 24b
	addi %r3, %r27, 192
	rldicl %r4, %r26, 57, 7
	addi %r5, %r24, 0
	addi %r6, %r4, 0
	addi %r7, %r27, 0
	bl {vg_scrypt_blockmix}
	addi %r28, %r28, -1
	cmpldi %cr0, %r28, 0
	bne %cr0, 23b
	ld %r0, 168(%r27)
	mtlr %r0
	ld %r24, 128(%r27)
	ld %r25, 136(%r27)
	ld %r26, 144(%r27)
	ld %r28, 152(%r27)
	ld %r29, 160(%r27)
	ld %r27, 176(%r27)
	blr

vg_scrypt:
	stdu %r1, -112(%r1)
	addi %r12, %r1, 0
	mflr %r0
	std %r0, 32(%r12)
	std %r30, 40(%r12)
	std %r3, 48(%r12)
	std %r4, 56(%r12)
	std %r7, 64(%r12)
	std %r8, 72(%r12)
	std %r9, 80(%r12)
	std %r10, 88(%r12)
	addi %r30, %r12, 0
	li %r7, 1
	rldicr %r9, %r9, 7, 56
	ld %r10, 216(%r30)
	bl {vg_pbkdf2_hmac_sha256_scratch}
	ld %r3, 72(%r30)
	std %r3, 96(%r30)
20:
	ld %r3, 96(%r30)
	ld %r4, 64(%r30)
	ld %r5, 88(%r30)
	ld %r6, 208(%r30)
	ld %r7, 216(%r30)
	addi %r8, %r4, 2
	bl {vg_scrypt_romix}
	ld %r3, 96(%r30)
	ld %r4, 64(%r30)
	rldicr %r4, %r4, 7, 56
	add %r3, %r3, %r4
	std %r3, 96(%r30)
	ld %r5, 72(%r30)
	ld %r6, 80(%r30)
	rldicr %r6, %r6, 7, 56
	add %r5, %r5, %r6
	subf %r5, %r3, %r5
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	ld %r3, 48(%r30)
	ld %r4, 56(%r30)
	ld %r5, 72(%r30)
	ld %r6, 80(%r30)
	rldicr %r6, %r6, 7, 56
	li %r7, 1
	ld %r8, 232(%r30)
	ld %r9, 240(%r30)
	ld %r10, 216(%r30)
	bl {vg_pbkdf2_hmac_sha256_scratch}
	ld %r0, 32(%r30)
	mtlr %r0
	ld %r30, 40(%r30)
	addi %r1, %r1, 112
	blr
