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

vg_ed448_scalar_reduce:
	std %r14, 1064(%r5)
	std %r15, 1072(%r5)
	std %r16, 1080(%r5)
	std %r17, 1088(%r5)
	std %r18, 1096(%r5)
	std %r19, 1104(%r5)
	std %r26, 1112(%r5)
	std %r27, 1120(%r5)
	std %r28, 1128(%r5)
	std %r29, 1136(%r5)
	std %r30, 1144(%r5)
	std %r31, 1152(%r5)
	addi %r6, %r5, 0
	addi %r27, %r3, 0
	addi %r14, %r4, 0
	li %r7, 0
	stw %r7, 0(%r6)
	stw %r7, 4(%r6)
	stw %r7, 8(%r6)
	stw %r7, 12(%r6)
	stw %r7, 16(%r6)
	stw %r7, 20(%r6)
	stw %r7, 24(%r6)
	stw %r7, 28(%r6)
	stw %r7, 32(%r6)
	stw %r7, 36(%r6)
	stw %r7, 40(%r6)
	stw %r7, 44(%r6)
	stw %r7, 48(%r6)
	stw %r7, 52(%r6)
	li %r15, 114
20:
	addi %r15, %r15, -1
	add %r7, %r14, %r15
	lbz %r16, 0(%r7)
	rldicr %r8, %r16, 56, 7
	rldicl %r8, %r8, 1, 63
	lwz %r7, 0(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 0(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 0(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 57, 6
	rldicl %r8, %r8, 1, 63
	lwz %r7, 0(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 0(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 0(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 58, 5
	rldicl %r8, %r8, 1, 63
	lwz %r7, 0(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 0(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 0(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 59, 4
	rldicl %r8, %r8, 1, 63
	lwz %r7, 0(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 0(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 0(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 60, 3
	rldicl %r8, %r8, 1, 63
	lwz %r7, 0(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 0(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 0(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 61, 2
	rldicl %r8, %r8, 1, 63
	lwz %r7, 0(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 0(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 0(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 62, 1
	rldicl %r8, %r8, 1, 63
	lwz %r7, 0(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 0(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 0(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 63, 0
	rldicl %r8, %r8, 1, 63
	lwz %r7, 0(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 0(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 0(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 108(%r6)
	cmpldi %cr0, %r15, 0
	bne %cr0, 20b
	addi %r14, %r27, 0
	lwz %r7, 0(%r6)
	stw %r7, 0(%r14)
	lwz %r7, 4(%r6)
	stw %r7, 4(%r14)
	lwz %r7, 8(%r6)
	stw %r7, 8(%r14)
	lwz %r7, 12(%r6)
	stw %r7, 12(%r14)
	lwz %r7, 16(%r6)
	stw %r7, 16(%r14)
	lwz %r7, 20(%r6)
	stw %r7, 20(%r14)
	lwz %r7, 24(%r6)
	stw %r7, 24(%r14)
	lwz %r7, 28(%r6)
	stw %r7, 28(%r14)
	lwz %r7, 32(%r6)
	stw %r7, 32(%r14)
	lwz %r7, 36(%r6)
	stw %r7, 36(%r14)
	lwz %r7, 40(%r6)
	stw %r7, 40(%r14)
	lwz %r7, 44(%r6)
	stw %r7, 44(%r14)
	lwz %r7, 48(%r6)
	stw %r7, 48(%r14)
	lwz %r7, 52(%r6)
	stw %r7, 52(%r14)
	li %r7, 0
	stb %r7, 56(%r14)
	ld %r14, 1064(%r6)
	ld %r15, 1072(%r6)
	ld %r16, 1080(%r6)
	ld %r17, 1088(%r6)
	ld %r18, 1096(%r6)
	ld %r19, 1104(%r6)
	ld %r26, 1112(%r6)
	ld %r27, 1120(%r6)
	ld %r28, 1128(%r6)
	ld %r29, 1136(%r6)
	ld %r30, 1144(%r6)
	ld %r31, 1152(%r6)
	blr

vg_ed448_scalar_mul_add:
	std %r14, 1064(%r7)
	std %r15, 1072(%r7)
	std %r16, 1080(%r7)
	std %r17, 1088(%r7)
	std %r18, 1096(%r7)
	std %r19, 1104(%r7)
	std %r26, 1112(%r7)
	std %r27, 1120(%r7)
	std %r28, 1128(%r7)
	std %r29, 1136(%r7)
	std %r30, 1144(%r7)
	std %r31, 1152(%r7)
	addi %r27, %r3, 0
	addi %r26, %r4, 0
	addi %r17, %r6, 0
	addi %r6, %r7, 0
	addi %r14, %r5, 0
	li %r7, 0
	stw %r7, 112(%r6)
	stw %r7, 116(%r6)
	stw %r7, 120(%r6)
	stw %r7, 124(%r6)
	stw %r7, 128(%r6)
	stw %r7, 132(%r6)
	stw %r7, 136(%r6)
	stw %r7, 140(%r6)
	stw %r7, 144(%r6)
	stw %r7, 148(%r6)
	stw %r7, 152(%r6)
	stw %r7, 156(%r6)
	stw %r7, 160(%r6)
	stw %r7, 164(%r6)
	li %r15, 57
20:
	addi %r15, %r15, -1
	add %r7, %r14, %r15
	lbz %r16, 0(%r7)
	rldicr %r8, %r16, 56, 7
	rldicl %r8, %r8, 1, 63
	lwz %r7, 112(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 112(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 112(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 57, 6
	rldicl %r8, %r8, 1, 63
	lwz %r7, 112(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 112(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 112(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 58, 5
	rldicl %r8, %r8, 1, 63
	lwz %r7, 112(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 112(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 112(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 59, 4
	rldicl %r8, %r8, 1, 63
	lwz %r7, 112(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 112(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 112(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 60, 3
	rldicl %r8, %r8, 1, 63
	lwz %r7, 112(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 112(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 112(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 61, 2
	rldicl %r8, %r8, 1, 63
	lwz %r7, 112(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 112(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 112(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 62, 1
	rldicl %r8, %r8, 1, 63
	lwz %r7, 112(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 112(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 112(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 63, 0
	rldicl %r8, %r8, 1, 63
	lwz %r7, 112(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 112(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 112(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 108(%r6)
	cmpldi %cr0, %r15, 0
	bne %cr0, 20b
	addi %r14, %r17, 0
	li %r7, 0
	stw %r7, 168(%r6)
	stw %r7, 172(%r6)
	stw %r7, 176(%r6)
	stw %r7, 180(%r6)
	stw %r7, 184(%r6)
	stw %r7, 188(%r6)
	stw %r7, 192(%r6)
	stw %r7, 196(%r6)
	stw %r7, 200(%r6)
	stw %r7, 204(%r6)
	stw %r7, 208(%r6)
	stw %r7, 212(%r6)
	stw %r7, 216(%r6)
	stw %r7, 220(%r6)
	li %r15, 57
21:
	addi %r15, %r15, -1
	add %r7, %r14, %r15
	lbz %r16, 0(%r7)
	rldicr %r8, %r16, 56, 7
	rldicl %r8, %r8, 1, 63
	lwz %r7, 168(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 168(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 168(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 192(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 192(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 196(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 196(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 200(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 200(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 204(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 204(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 208(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 208(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 212(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 212(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 216(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 216(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 220(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 220(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 57, 6
	rldicl %r8, %r8, 1, 63
	lwz %r7, 168(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 168(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 168(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 192(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 192(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 196(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 196(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 200(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 200(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 204(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 204(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 208(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 208(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 212(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 212(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 216(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 216(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 220(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 220(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 58, 5
	rldicl %r8, %r8, 1, 63
	lwz %r7, 168(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 168(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 168(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 192(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 192(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 196(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 196(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 200(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 200(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 204(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 204(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 208(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 208(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 212(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 212(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 216(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 216(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 220(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 220(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 59, 4
	rldicl %r8, %r8, 1, 63
	lwz %r7, 168(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 168(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 168(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 192(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 192(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 196(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 196(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 200(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 200(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 204(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 204(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 208(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 208(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 212(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 212(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 216(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 216(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 220(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 220(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 60, 3
	rldicl %r8, %r8, 1, 63
	lwz %r7, 168(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 168(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 168(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 192(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 192(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 196(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 196(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 200(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 200(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 204(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 204(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 208(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 208(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 212(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 212(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 216(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 216(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 220(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 220(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 61, 2
	rldicl %r8, %r8, 1, 63
	lwz %r7, 168(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 168(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 168(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 192(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 192(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 196(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 196(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 200(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 200(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 204(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 204(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 208(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 208(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 212(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 212(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 216(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 216(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 220(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 220(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 62, 1
	rldicl %r8, %r8, 1, 63
	lwz %r7, 168(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 168(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 168(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 192(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 192(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 196(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 196(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 200(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 200(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 204(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 204(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 208(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 208(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 212(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 212(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 216(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 216(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 220(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 220(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 63, 0
	rldicl %r8, %r8, 1, 63
	lwz %r7, 168(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 168(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 172(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 176(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 180(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 184(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 188(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 192(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 196(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 200(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 204(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 208(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 212(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 216(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 220(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 168(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 168(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 168(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 172(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 176(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 180(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 184(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 188(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 192(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 192(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 196(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 196(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 200(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 200(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 204(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 204(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 208(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 208(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 212(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 212(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 216(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 216(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 220(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 220(%r6)
	stw %r7, 108(%r6)
	cmpldi %cr0, %r15, 0
	bne %cr0, 21b
	addi %r14, %r26, 0
	li %r7, 0
	stw %r7, 224(%r6)
	stw %r7, 228(%r6)
	stw %r7, 232(%r6)
	stw %r7, 236(%r6)
	stw %r7, 240(%r6)
	stw %r7, 244(%r6)
	stw %r7, 248(%r6)
	stw %r7, 252(%r6)
	stw %r7, 256(%r6)
	stw %r7, 260(%r6)
	stw %r7, 264(%r6)
	stw %r7, 268(%r6)
	stw %r7, 272(%r6)
	stw %r7, 276(%r6)
	li %r15, 57
22:
	addi %r15, %r15, -1
	add %r7, %r14, %r15
	lbz %r16, 0(%r7)
	rldicr %r8, %r16, 56, 7
	rldicl %r8, %r8, 1, 63
	lwz %r7, 224(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 224(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 228(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 232(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 236(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 240(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 244(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 248(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 252(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 256(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 260(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 264(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 268(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 272(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 276(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 224(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 224(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 224(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 228(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 228(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 232(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 232(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 236(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 236(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 240(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 240(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 244(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 244(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 248(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 248(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 252(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 252(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 256(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 256(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 260(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 260(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 264(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 264(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 268(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 268(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 272(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 272(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 276(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 276(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 57, 6
	rldicl %r8, %r8, 1, 63
	lwz %r7, 224(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 224(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 228(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 232(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 236(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 240(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 244(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 248(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 252(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 256(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 260(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 264(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 268(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 272(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 276(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 224(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 224(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 224(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 228(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 228(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 232(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 232(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 236(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 236(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 240(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 240(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 244(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 244(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 248(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 248(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 252(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 252(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 256(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 256(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 260(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 260(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 264(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 264(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 268(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 268(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 272(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 272(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 276(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 276(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 58, 5
	rldicl %r8, %r8, 1, 63
	lwz %r7, 224(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 224(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 228(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 232(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 236(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 240(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 244(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 248(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 252(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 256(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 260(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 264(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 268(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 272(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 276(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 224(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 224(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 224(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 228(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 228(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 232(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 232(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 236(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 236(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 240(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 240(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 244(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 244(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 248(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 248(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 252(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 252(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 256(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 256(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 260(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 260(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 264(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 264(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 268(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 268(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 272(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 272(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 276(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 276(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 59, 4
	rldicl %r8, %r8, 1, 63
	lwz %r7, 224(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 224(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 228(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 232(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 236(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 240(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 244(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 248(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 252(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 256(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 260(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 264(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 268(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 272(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 276(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 224(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 224(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 224(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 228(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 228(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 232(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 232(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 236(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 236(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 240(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 240(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 244(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 244(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 248(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 248(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 252(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 252(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 256(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 256(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 260(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 260(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 264(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 264(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 268(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 268(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 272(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 272(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 276(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 276(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 60, 3
	rldicl %r8, %r8, 1, 63
	lwz %r7, 224(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 224(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 228(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 232(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 236(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 240(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 244(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 248(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 252(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 256(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 260(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 264(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 268(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 272(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 276(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 224(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 224(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 224(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 228(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 228(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 232(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 232(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 236(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 236(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 240(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 240(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 244(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 244(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 248(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 248(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 252(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 252(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 256(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 256(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 260(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 260(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 264(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 264(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 268(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 268(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 272(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 272(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 276(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 276(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 61, 2
	rldicl %r8, %r8, 1, 63
	lwz %r7, 224(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 224(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 228(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 232(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 236(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 240(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 244(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 248(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 252(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 256(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 260(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 264(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 268(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 272(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 276(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 224(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 224(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 224(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 228(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 228(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 232(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 232(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 236(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 236(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 240(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 240(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 244(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 244(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 248(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 248(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 252(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 252(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 256(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 256(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 260(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 260(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 264(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 264(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 268(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 268(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 272(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 272(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 276(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 276(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 62, 1
	rldicl %r8, %r8, 1, 63
	lwz %r7, 224(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 224(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 228(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 232(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 236(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 240(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 244(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 248(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 252(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 256(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 260(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 264(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 268(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 272(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 276(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 224(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 224(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 224(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 228(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 228(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 232(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 232(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 236(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 236(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 240(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 240(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 244(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 244(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 248(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 248(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 252(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 252(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 256(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 256(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 260(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 260(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 264(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 264(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 268(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 268(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 272(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 272(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 276(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 276(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 63, 0
	rldicl %r8, %r8, 1, 63
	lwz %r7, 224(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 224(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 228(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 232(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 236(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 240(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 244(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 248(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 252(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 256(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 260(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 264(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 268(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 272(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 276(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 224(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 228(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 232(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 236(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 240(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 244(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 248(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 252(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 256(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 260(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 264(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 268(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 272(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 276(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 224(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 224(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 228(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 228(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 232(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 232(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 236(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 236(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 240(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 240(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 244(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 244(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 248(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 248(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 252(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 252(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 256(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 256(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 260(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 260(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 264(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 264(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 268(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 268(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 272(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 272(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 276(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 276(%r6)
	stw %r7, 108(%r6)
	cmpldi %cr0, %r15, 0
	bne %cr0, 22b
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
23:
	lwz %r4, 112(%r9)
	li %r8, 0
	lwz %r5, 168(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 172(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 176(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 180(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 184(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 188(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 192(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 196(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 200(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 204(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 208(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 212(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 216(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 220(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 23b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 224(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 228(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 232(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 236(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 240(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 244(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 248(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 252(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 256(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 260(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 264(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 268(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 272(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 276(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1008(%r6)
	add %r7, %r7, %r8
	stw %r7, 1008(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1012(%r6)
	add %r7, %r7, %r8
	stw %r7, 1012(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1016(%r6)
	add %r7, %r7, %r8
	stw %r7, 1016(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1020(%r6)
	add %r7, %r7, %r8
	stw %r7, 1020(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1024(%r6)
	add %r7, %r7, %r8
	stw %r7, 1024(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1028(%r6)
	add %r7, %r7, %r8
	stw %r7, 1028(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1032(%r6)
	add %r7, %r7, %r8
	stw %r7, 1032(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1036(%r6)
	add %r7, %r7, %r8
	stw %r7, 1036(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1040(%r6)
	add %r7, %r7, %r8
	stw %r7, 1040(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1044(%r6)
	add %r7, %r7, %r8
	stw %r7, 1044(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1048(%r6)
	add %r7, %r7, %r8
	stw %r7, 1048(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1052(%r6)
	add %r7, %r7, %r8
	stw %r7, 1052(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1056(%r6)
	add %r7, %r7, %r8
	stw %r7, 1056(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1060(%r6)
	add %r7, %r7, %r8
	stw %r7, 1060(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r14, %r6, 280
	lwz %r7, 952(%r6)
	stw %r7, 0(%r14)
	lwz %r7, 956(%r6)
	stw %r7, 4(%r14)
	lwz %r7, 960(%r6)
	stw %r7, 8(%r14)
	lwz %r7, 964(%r6)
	stw %r7, 12(%r14)
	lwz %r7, 968(%r6)
	stw %r7, 16(%r14)
	lwz %r7, 972(%r6)
	stw %r7, 20(%r14)
	lwz %r7, 976(%r6)
	stw %r7, 24(%r14)
	lwz %r7, 980(%r6)
	stw %r7, 28(%r14)
	lwz %r7, 984(%r6)
	stw %r7, 32(%r14)
	lwz %r7, 988(%r6)
	stw %r7, 36(%r14)
	lwz %r7, 992(%r6)
	stw %r7, 40(%r14)
	lwz %r7, 996(%r6)
	stw %r7, 44(%r14)
	lwz %r7, 1000(%r6)
	stw %r7, 48(%r14)
	lwz %r7, 1004(%r6)
	stw %r7, 52(%r14)
	lwz %r7, 1008(%r6)
	stw %r7, 56(%r14)
	lwz %r7, 1012(%r6)
	stw %r7, 60(%r14)
	lwz %r7, 1016(%r6)
	stw %r7, 64(%r14)
	lwz %r7, 1020(%r6)
	stw %r7, 68(%r14)
	lwz %r7, 1024(%r6)
	stw %r7, 72(%r14)
	lwz %r7, 1028(%r6)
	stw %r7, 76(%r14)
	lwz %r7, 1032(%r6)
	stw %r7, 80(%r14)
	lwz %r7, 1036(%r6)
	stw %r7, 84(%r14)
	lwz %r7, 1040(%r6)
	stw %r7, 88(%r14)
	lwz %r7, 1044(%r6)
	stw %r7, 92(%r14)
	lwz %r7, 1048(%r6)
	stw %r7, 96(%r14)
	lwz %r7, 1052(%r6)
	stw %r7, 100(%r14)
	lwz %r7, 1056(%r6)
	stw %r7, 104(%r14)
	lwz %r7, 1060(%r6)
	stw %r7, 108(%r14)
	li %r7, 0
	stw %r7, 0(%r6)
	stw %r7, 4(%r6)
	stw %r7, 8(%r6)
	stw %r7, 12(%r6)
	stw %r7, 16(%r6)
	stw %r7, 20(%r6)
	stw %r7, 24(%r6)
	stw %r7, 28(%r6)
	stw %r7, 32(%r6)
	stw %r7, 36(%r6)
	stw %r7, 40(%r6)
	stw %r7, 44(%r6)
	stw %r7, 48(%r6)
	stw %r7, 52(%r6)
	li %r15, 112
24:
	addi %r15, %r15, -1
	add %r7, %r14, %r15
	lbz %r16, 0(%r7)
	rldicr %r8, %r16, 56, 7
	rldicl %r8, %r8, 1, 63
	lwz %r7, 0(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 0(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 0(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 57, 6
	rldicl %r8, %r8, 1, 63
	lwz %r7, 0(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 0(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 0(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 58, 5
	rldicl %r8, %r8, 1, 63
	lwz %r7, 0(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 0(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 0(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 59, 4
	rldicl %r8, %r8, 1, 63
	lwz %r7, 0(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 0(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 0(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 60, 3
	rldicl %r8, %r8, 1, 63
	lwz %r7, 0(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 0(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 0(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 61, 2
	rldicl %r8, %r8, 1, 63
	lwz %r7, 0(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 0(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 0(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 62, 1
	rldicl %r8, %r8, 1, 63
	lwz %r7, 0(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 0(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 0(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 108(%r6)
	rldicr %r8, %r16, 63, 0
	rldicl %r8, %r8, 1, 63
	lwz %r7, 0(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 0(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 4(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 8(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 12(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 16(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 20(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 24(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 28(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r7
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	lwz %r7, 0(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 0(%r6)
	lwz %r7, 56(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 56(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 60(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 60(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 64(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 64(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 68(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 68(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 72(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 72(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 76(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 76(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 80(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 80(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 84(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 84(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 88(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 88(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 92(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 92(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 96(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 96(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 100(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 100(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 104(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 104(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 108(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 108(%r6)
	cmpldi %cr0, %r15, 0
	bne %cr0, 24b
	addi %r14, %r27, 0
	lwz %r7, 0(%r6)
	stw %r7, 0(%r14)
	lwz %r7, 4(%r6)
	stw %r7, 4(%r14)
	lwz %r7, 8(%r6)
	stw %r7, 8(%r14)
	lwz %r7, 12(%r6)
	stw %r7, 12(%r14)
	lwz %r7, 16(%r6)
	stw %r7, 16(%r14)
	lwz %r7, 20(%r6)
	stw %r7, 20(%r14)
	lwz %r7, 24(%r6)
	stw %r7, 24(%r14)
	lwz %r7, 28(%r6)
	stw %r7, 28(%r14)
	lwz %r7, 32(%r6)
	stw %r7, 32(%r14)
	lwz %r7, 36(%r6)
	stw %r7, 36(%r14)
	lwz %r7, 40(%r6)
	stw %r7, 40(%r14)
	lwz %r7, 44(%r6)
	stw %r7, 44(%r14)
	lwz %r7, 48(%r6)
	stw %r7, 48(%r14)
	lwz %r7, 52(%r6)
	stw %r7, 52(%r14)
	li %r7, 0
	stb %r7, 56(%r14)
	ld %r14, 1064(%r6)
	ld %r15, 1072(%r6)
	ld %r16, 1080(%r6)
	ld %r17, 1088(%r6)
	ld %r18, 1096(%r6)
	ld %r19, 1104(%r6)
	ld %r26, 1112(%r6)
	ld %r27, 1120(%r6)
	ld %r28, 1128(%r6)
	ld %r29, 1136(%r6)
	ld %r30, 1144(%r6)
	ld %r31, 1152(%r6)
	blr

vg_ed448_scalar_base:
	addi %r6, %r5, 0
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 56(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 60(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 64(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 68(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 72(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 76(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 80(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 84(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 88(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 92(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 96(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 100(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 104(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 108(%r6)
	lis %r7, 0
	ori %r7, %r7, 1
	stw %r7, 0(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 4(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 8(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 12(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 16(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 20(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 24(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 28(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 32(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 36(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 40(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 44(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 48(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 52(%r6)
	lis %r7, 0
	ori %r7, %r7, 1
	stw %r7, 112(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 116(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 120(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 124(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 128(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 132(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 136(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 140(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 144(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 148(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 152(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 156(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 160(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 164(%r6)
	lis %r7, -14580
	ori %r7, %r7, 49246
	stw %r7, 1520(%r6)
	lis %r7, 9766
	ori %r7, %r7, 43051
	stw %r7, 1524(%r6)
	lis %r7, -29952
	ori %r7, %r7, 37774
	stw %r7, 1528(%r6)
	lis %r7, 17211
	ori %r7, %r7, 32993
	stw %r7, 1532(%r6)
	lis %r7, 10934
	ori %r7, %r7, 25873
	stw %r7, 1536(%r6)
	lis %r7, 4782
	ori %r7, %r7, 6903
	stw %r7, 1540(%r6)
	lis %r7, -23597
	ori %r7, %r7, 42084
	stw %r7, 1544(%r6)
	lis %r7, -5523
	ori %r7, %r7, 58148
	stw %r7, 1548(%r6)
	lis %r7, 18191
	ori %r7, %r7, 5991
	stw %r7, 1552(%r6)
	lis %r7, -25068
	ori %r7, %r7, 25968
	stw %r7, 1556(%r6)
	lis %r7, 8895
	ori %r7, %r7, 14042
	stw %r7, 1560(%r6)
	lis %r7, 8733
	ori %r7, %r7, 5542
	stw %r7, 1564(%r6)
	lis %r7, 27629
	ori %r7, %r7, 3565
	stw %r7, 1568(%r6)
	lis %r7, 20249
	ori %r7, %r7, 28870
	stw %r7, 1572(%r6)
	lis %r7, -3536
	ori %r7, %r7, 64020
	stw %r7, 1576(%r6)
	lis %r7, -26616
	ori %r7, %r7, 31067
	stw %r7, 1580(%r6)
	lis %r7, 20183
	ori %r7, %r7, 51373
	stw %r7, 1584(%r6)
	lis %r7, -579
	ori %r7, %r7, 4908
	stw %r7, 1588(%r6)
	lis %r7, -6532
	ori %r7, %r7, 14788
	stw %r7, 1592(%r6)
	lis %r7, 15059
	ori %r7, %r7, 65308
	stw %r7, 1596(%r6)
	lis %r7, 1440
	ori %r7, %r7, 49879
	stw %r7, 1600(%r6)
	lis %r7, -30856
	ori %r7, %r7, 39966
	stw %r7, 1604(%r6)
	lis %r7, 27811
	ori %r7, %r7, 38976
	stw %r7, 1608(%r6)
	lis %r7, 19434
	ori %r7, %r7, 29555
	stw %r7, 1612(%r6)
	lis %r7, 22217
	ori %r7, %r7, 51042
	stw %r7, 1616(%r6)
	lis %r7, -30602
	ori %r7, %r7, 8247
	stw %r7, 1620(%r6)
	lis %r7, 28342
	ori %r7, %r7, 48164
	stw %r7, 1624(%r6)
	lis %r7, 26943
	ori %r7, %r7, 18033
	stw %r7, 1628(%r6)
	lis %r7, 0
	ori %r7, %r7, 1
	stw %r7, 1632(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 1636(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 1640(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 1644(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 1648(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 1652(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 1656(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 1660(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 1664(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 1668(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 1672(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 1676(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 1680(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 1684(%r6)
	lis %r7, -1
	ori %r7, %r7, 26454
	stw %r7, 336(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 340(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 344(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 348(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 352(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 356(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 360(%r6)
	lis %r7, -1
	ori %r7, %r7, 65534
	stw %r7, 364(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 368(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 372(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 376(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 380(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 384(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 388(%r6)
	addi %r9, %r6, 0
	li %r11, 57
20:
	lbz %r7, 0(%r4)
	rldicr %r8, %r7, 63, 0
	rldicl %r8, %r8, 1, 63
	stb %r8, 1064(%r9)
	rldicr %r8, %r7, 62, 1
	rldicl %r8, %r8, 1, 63
	stb %r8, 1065(%r9)
	rldicr %r8, %r7, 61, 2
	rldicl %r8, %r8, 1, 63
	stb %r8, 1066(%r9)
	rldicr %r8, %r7, 60, 3
	rldicl %r8, %r8, 1, 63
	stb %r8, 1067(%r9)
	rldicr %r8, %r7, 59, 4
	rldicl %r8, %r8, 1, 63
	stb %r8, 1068(%r9)
	rldicr %r8, %r7, 58, 5
	rldicl %r8, %r8, 1, 63
	stb %r8, 1069(%r9)
	rldicr %r8, %r7, 57, 6
	rldicl %r8, %r8, 1, 63
	stb %r8, 1070(%r9)
	rldicr %r8, %r7, 56, 7
	rldicl %r8, %r8, 1, 63
	stb %r8, 1071(%r9)
	addi %r4, %r4, 1
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 20b
	li %r12, 912
21:
	addi %r12, %r12, -1
	rldicr %r4, %r12, 63, 0
	rldicl %r4, %r4, 1, 63
	addi %r0, %r4, 0
	li %r11, 0
	subf %r11, %r4, %r11
	lwz %r5, 1520(%r6)
	lwz %r7, 56(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 168(%r6)
	lwz %r5, 1524(%r6)
	lwz %r7, 60(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 172(%r6)
	lwz %r5, 1528(%r6)
	lwz %r7, 64(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 176(%r6)
	lwz %r5, 1532(%r6)
	lwz %r7, 68(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 180(%r6)
	lwz %r5, 1536(%r6)
	lwz %r7, 72(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 184(%r6)
	lwz %r5, 1540(%r6)
	lwz %r7, 76(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 188(%r6)
	lwz %r5, 1544(%r6)
	lwz %r7, 80(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 192(%r6)
	lwz %r5, 1548(%r6)
	lwz %r7, 84(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 196(%r6)
	lwz %r5, 1552(%r6)
	lwz %r7, 88(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 200(%r6)
	lwz %r5, 1556(%r6)
	lwz %r7, 92(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 204(%r6)
	lwz %r5, 1560(%r6)
	lwz %r7, 96(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 208(%r6)
	lwz %r5, 1564(%r6)
	lwz %r7, 100(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 212(%r6)
	lwz %r5, 1568(%r6)
	lwz %r7, 104(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 216(%r6)
	lwz %r5, 1572(%r6)
	lwz %r7, 108(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 220(%r6)
	lwz %r5, 1576(%r6)
	lwz %r7, 0(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 224(%r6)
	lwz %r5, 1580(%r6)
	lwz %r7, 4(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 228(%r6)
	lwz %r5, 1584(%r6)
	lwz %r7, 8(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 232(%r6)
	lwz %r5, 1588(%r6)
	lwz %r7, 12(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 236(%r6)
	lwz %r5, 1592(%r6)
	lwz %r7, 16(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 240(%r6)
	lwz %r5, 1596(%r6)
	lwz %r7, 20(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 244(%r6)
	lwz %r5, 1600(%r6)
	lwz %r7, 24(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 248(%r6)
	lwz %r5, 1604(%r6)
	lwz %r7, 28(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 252(%r6)
	lwz %r5, 1608(%r6)
	lwz %r7, 32(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 256(%r6)
	lwz %r5, 1612(%r6)
	lwz %r7, 36(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 260(%r6)
	lwz %r5, 1616(%r6)
	lwz %r7, 40(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 264(%r6)
	lwz %r5, 1620(%r6)
	lwz %r7, 44(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 268(%r6)
	lwz %r5, 1624(%r6)
	lwz %r7, 48(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 272(%r6)
	lwz %r5, 1628(%r6)
	lwz %r7, 52(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 276(%r6)
	lwz %r5, 1632(%r6)
	lwz %r7, 112(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 280(%r6)
	lwz %r5, 1636(%r6)
	lwz %r7, 116(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 284(%r6)
	lwz %r5, 1640(%r6)
	lwz %r7, 120(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 288(%r6)
	lwz %r5, 1644(%r6)
	lwz %r7, 124(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 292(%r6)
	lwz %r5, 1648(%r6)
	lwz %r7, 128(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 296(%r6)
	lwz %r5, 1652(%r6)
	lwz %r7, 132(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 300(%r6)
	lwz %r5, 1656(%r6)
	lwz %r7, 136(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 304(%r6)
	lwz %r5, 1660(%r6)
	lwz %r7, 140(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 308(%r6)
	lwz %r5, 1664(%r6)
	lwz %r7, 144(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 312(%r6)
	lwz %r5, 1668(%r6)
	lwz %r7, 148(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 316(%r6)
	lwz %r5, 1672(%r6)
	lwz %r7, 152(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 320(%r6)
	lwz %r5, 1676(%r6)
	lwz %r7, 156(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 324(%r6)
	lwz %r5, 1680(%r6)
	lwz %r7, 160(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 328(%r6)
	lwz %r5, 1684(%r6)
	lwz %r7, 164(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 332(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
22:
	lwz %r4, 112(%r9)
	li %r8, 0
	lwz %r5, 280(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 284(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 288(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 292(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 296(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 300(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 304(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 308(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 312(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 316(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 320(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 324(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 328(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 332(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 22b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
23:
	lwz %r4, 560(%r9)
	li %r8, 0
	lwz %r5, 560(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 564(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 568(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 572(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 576(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 580(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 584(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 588(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 592(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 596(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 600(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 604(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 608(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 612(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 23b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
24:
	lwz %r4, 56(%r9)
	li %r8, 0
	lwz %r5, 168(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 172(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 176(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 180(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 184(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 188(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 192(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 196(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 200(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 204(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 208(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 212(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 216(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 220(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 24b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
25:
	lwz %r4, 0(%r9)
	li %r8, 0
	lwz %r5, 224(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 228(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 232(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 236(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 240(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 244(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 248(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 252(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 256(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 260(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 264(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 268(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 272(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 276(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 25b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 672(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 676(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 680(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 684(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 688(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 692(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 696(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 700(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 704(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 708(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 712(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 716(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 720(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 724(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 672(%r6)
	add %r7, %r7, %r8
	stw %r7, 672(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 676(%r6)
	add %r7, %r7, %r8
	stw %r7, 676(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 680(%r6)
	add %r7, %r7, %r8
	stw %r7, 680(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 684(%r6)
	add %r7, %r7, %r8
	stw %r7, 684(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 688(%r6)
	add %r7, %r7, %r8
	stw %r7, 688(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 692(%r6)
	add %r7, %r7, %r8
	stw %r7, 692(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 696(%r6)
	add %r7, %r7, %r8
	stw %r7, 696(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 700(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 700(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 704(%r6)
	add %r7, %r7, %r8
	stw %r7, 704(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 708(%r6)
	add %r7, %r7, %r8
	stw %r7, 708(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 712(%r6)
	add %r7, %r7, %r8
	stw %r7, 712(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 716(%r6)
	add %r7, %r7, %r8
	stw %r7, 716(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 720(%r6)
	add %r7, %r7, %r8
	stw %r7, 720(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 724(%r6)
	add %r7, %r7, %r8
	stw %r7, 724(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 672(%r6)
	add %r7, %r7, %r8
	stw %r7, 672(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 676(%r6)
	add %r7, %r7, %r8
	stw %r7, 676(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 680(%r6)
	add %r7, %r7, %r8
	stw %r7, 680(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 684(%r6)
	add %r7, %r7, %r8
	stw %r7, 684(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 688(%r6)
	add %r7, %r7, %r8
	stw %r7, 688(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 692(%r6)
	add %r7, %r7, %r8
	stw %r7, 692(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 696(%r6)
	add %r7, %r7, %r8
	stw %r7, 696(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 700(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 700(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 704(%r6)
	add %r7, %r7, %r8
	stw %r7, 704(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 708(%r6)
	add %r7, %r7, %r8
	stw %r7, 708(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 712(%r6)
	add %r7, %r7, %r8
	stw %r7, 712(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 716(%r6)
	add %r7, %r7, %r8
	stw %r7, 716(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 720(%r6)
	add %r7, %r7, %r8
	stw %r7, 720(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 724(%r6)
	add %r7, %r7, %r8
	stw %r7, 724(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
26:
	lwz %r4, 336(%r9)
	li %r8, 0
	lwz %r5, 616(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 620(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 624(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 628(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 632(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 636(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 640(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 644(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 648(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 652(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 656(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 660(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 664(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 668(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 26b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
27:
	lwz %r4, 504(%r9)
	li %r8, 0
	lwz %r5, 672(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 676(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 680(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 684(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 688(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 692(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 696(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 700(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 704(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 708(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 712(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 716(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 720(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 724(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 27b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 34, 29
	lwz %r7, 448(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 504(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 508(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 512(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 516(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 520(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 524(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 528(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -8
	lwz %r5, 532(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 536(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 540(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 544(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 548(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 552(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 556(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 728(%r6)
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 732(%r6)
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 740(%r6)
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 744(%r6)
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 748(%r6)
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 752(%r6)
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 756(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 760(%r6)
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 764(%r6)
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 768(%r6)
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 772(%r6)
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 776(%r6)
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 780(%r6)
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 728(%r6)
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 732(%r6)
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 740(%r6)
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 744(%r6)
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 748(%r6)
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 752(%r6)
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 756(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 760(%r6)
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 764(%r6)
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 768(%r6)
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 772(%r6)
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 776(%r6)
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 780(%r6)
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	lwz %r7, 448(%r6)
	lwz %r5, 504(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 784(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	lwz %r5, 508(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 788(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	lwz %r5, 512(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 792(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	lwz %r5, 516(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 796(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	lwz %r5, 520(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 800(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	lwz %r5, 524(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 804(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	lwz %r5, 528(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 808(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	lwz %r5, 532(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 812(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	lwz %r5, 536(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 816(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	lwz %r5, 540(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 820(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	lwz %r5, 544(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 824(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	lwz %r5, 548(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 828(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	lwz %r5, 552(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 832(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	lwz %r5, 556(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 836(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 784(%r6)
	add %r7, %r7, %r8
	stw %r7, 784(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 788(%r6)
	add %r7, %r7, %r8
	stw %r7, 788(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 792(%r6)
	add %r7, %r7, %r8
	stw %r7, 792(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 796(%r6)
	add %r7, %r7, %r8
	stw %r7, 796(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 800(%r6)
	add %r7, %r7, %r8
	stw %r7, 800(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 804(%r6)
	add %r7, %r7, %r8
	stw %r7, 804(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 808(%r6)
	add %r7, %r7, %r8
	stw %r7, 808(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 812(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 812(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 816(%r6)
	add %r7, %r7, %r8
	stw %r7, 816(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 820(%r6)
	add %r7, %r7, %r8
	stw %r7, 820(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 824(%r6)
	add %r7, %r7, %r8
	stw %r7, 824(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 828(%r6)
	add %r7, %r7, %r8
	stw %r7, 828(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 832(%r6)
	add %r7, %r7, %r8
	stw %r7, 832(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 836(%r6)
	add %r7, %r7, %r8
	stw %r7, 836(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 784(%r6)
	add %r7, %r7, %r8
	stw %r7, 784(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 788(%r6)
	add %r7, %r7, %r8
	stw %r7, 788(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 792(%r6)
	add %r7, %r7, %r8
	stw %r7, 792(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 796(%r6)
	add %r7, %r7, %r8
	stw %r7, 796(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 800(%r6)
	add %r7, %r7, %r8
	stw %r7, 800(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 804(%r6)
	add %r7, %r7, %r8
	stw %r7, 804(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 808(%r6)
	add %r7, %r7, %r8
	stw %r7, 808(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 812(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 812(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 816(%r6)
	add %r7, %r7, %r8
	stw %r7, 816(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 820(%r6)
	add %r7, %r7, %r8
	stw %r7, 820(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 824(%r6)
	add %r7, %r7, %r8
	stw %r7, 824(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 828(%r6)
	add %r7, %r7, %r8
	stw %r7, 828(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 832(%r6)
	add %r7, %r7, %r8
	stw %r7, 832(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 836(%r6)
	add %r7, %r7, %r8
	stw %r7, 836(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	lwz %r7, 56(%r6)
	lwz %r5, 0(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	lwz %r5, 4(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	lwz %r5, 8(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	lwz %r5, 12(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	lwz %r5, 16(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	lwz %r5, 20(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	lwz %r5, 24(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	lwz %r5, 28(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	lwz %r5, 32(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	lwz %r5, 36(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	lwz %r5, 40(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	lwz %r5, 44(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	lwz %r5, 48(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	lwz %r5, 52(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	lwz %r7, 168(%r6)
	lwz %r5, 224(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lwz %r5, 228(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lwz %r5, 232(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lwz %r5, 236(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lwz %r5, 240(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lwz %r5, 244(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	lwz %r5, 248(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	lwz %r5, 252(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	lwz %r5, 256(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	lwz %r5, 260(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	lwz %r5, 264(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	lwz %r5, 268(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	lwz %r5, 272(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	lwz %r5, 276(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 392(%r6)
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 416(%r6)
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 392(%r6)
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 416(%r6)
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
28:
	lwz %r4, 840(%r9)
	li %r8, 0
	lwz %r5, 392(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 396(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 400(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 404(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 408(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 412(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 416(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 420(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 424(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 428(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 432(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 436(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 440(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 444(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 28b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
29:
	lwz %r4, 560(%r9)
	li %r8, 0
	lwz %r5, 728(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 732(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 736(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 740(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 744(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 748(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 752(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 756(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 760(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 764(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 768(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 772(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 776(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 780(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 29b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 392(%r6)
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 416(%r6)
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 392(%r6)
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 416(%r6)
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 34, 29
	lwz %r7, 840(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 616(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 620(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 624(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 628(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 632(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 636(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 640(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -8
	lwz %r5, 644(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 648(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 652(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 656(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 660(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 664(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 668(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 34, 29
	lwz %r7, 840(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 672(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 676(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 680(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 684(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 688(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 692(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 696(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -8
	lwz %r5, 700(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 704(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 708(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 712(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 716(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 720(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 724(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
210:
	lwz %r4, 392(%r9)
	li %r8, 0
	lwz %r5, 840(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 844(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 848(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 852(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 856(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 860(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 864(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 868(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 872(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 876(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 880(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 884(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 888(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 892(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 210b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 392(%r6)
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 416(%r6)
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 392(%r6)
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 416(%r6)
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
211:
	lwz %r4, 560(%r9)
	li %r8, 0
	lwz %r5, 784(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 788(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 792(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 796(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 800(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 804(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 808(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 812(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 816(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 820(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 824(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 828(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 832(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 836(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 211b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 34, 29
	lwz %r7, 672(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 616(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 676(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 620(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 680(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 624(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 684(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 628(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 688(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 632(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 692(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 636(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 696(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 640(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 700(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -8
	lwz %r5, 644(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 704(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 648(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 708(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 652(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 712(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 656(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 716(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 660(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 720(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 664(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 724(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 668(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
212:
	lwz %r4, 448(%r9)
	li %r8, 0
	lwz %r5, 840(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 844(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 848(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 852(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 856(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 860(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 864(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 868(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 872(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 876(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 880(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 884(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 888(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 892(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 212b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
213:
	lwz %r4, 728(%r9)
	li %r8, 0
	lwz %r5, 784(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 788(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 792(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 796(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 800(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 804(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 808(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 812(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 816(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 820(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 824(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 828(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 832(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 836(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 213b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	rldicl %r4, %r12, 63, 1
	add %r4, %r6, %r4
	lbz %r4, 1064(%r4)
	or %r4, %r4, %r0
	li %r11, 0
	subf %r11, %r4, %r11
	lwz %r5, 56(%r6)
	lwz %r7, 392(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 56(%r6)
	stw %r7, 392(%r6)
	lwz %r5, 60(%r6)
	lwz %r7, 396(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 60(%r6)
	stw %r7, 396(%r6)
	lwz %r5, 64(%r6)
	lwz %r7, 400(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 64(%r6)
	stw %r7, 400(%r6)
	lwz %r5, 68(%r6)
	lwz %r7, 404(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 68(%r6)
	stw %r7, 404(%r6)
	lwz %r5, 72(%r6)
	lwz %r7, 408(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 72(%r6)
	stw %r7, 408(%r6)
	lwz %r5, 76(%r6)
	lwz %r7, 412(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 76(%r6)
	stw %r7, 412(%r6)
	lwz %r5, 80(%r6)
	lwz %r7, 416(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 80(%r6)
	stw %r7, 416(%r6)
	lwz %r5, 84(%r6)
	lwz %r7, 420(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 84(%r6)
	stw %r7, 420(%r6)
	lwz %r5, 88(%r6)
	lwz %r7, 424(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 88(%r6)
	stw %r7, 424(%r6)
	lwz %r5, 92(%r6)
	lwz %r7, 428(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 92(%r6)
	stw %r7, 428(%r6)
	lwz %r5, 96(%r6)
	lwz %r7, 432(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 96(%r6)
	stw %r7, 432(%r6)
	lwz %r5, 100(%r6)
	lwz %r7, 436(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 100(%r6)
	stw %r7, 436(%r6)
	lwz %r5, 104(%r6)
	lwz %r7, 440(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 104(%r6)
	stw %r7, 440(%r6)
	lwz %r5, 108(%r6)
	lwz %r7, 444(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 108(%r6)
	stw %r7, 444(%r6)
	lwz %r5, 0(%r6)
	lwz %r7, 448(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 448(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 452(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 452(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 456(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 456(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 460(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 460(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 464(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 464(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 468(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 468(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 472(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 472(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 476(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 476(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 480(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 480(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 484(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 484(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 488(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 488(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 492(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 492(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 496(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 496(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 500(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 500(%r6)
	lwz %r5, 112(%r6)
	lwz %r7, 504(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 504(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 508(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 508(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 512(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 512(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 516(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 516(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 520(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 520(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 524(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 524(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 528(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 528(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 532(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 532(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 536(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 536(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 540(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 540(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 544(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 544(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 548(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 548(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 552(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 552(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 556(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 556(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 21b
	li %r4, 1
	li %r5, 0
	stw %r4, 840(%r6)
	stw %r5, 844(%r6)
	stw %r5, 848(%r6)
	stw %r5, 852(%r6)
	stw %r5, 856(%r6)
	stw %r5, 860(%r6)
	stw %r5, 864(%r6)
	stw %r5, 868(%r6)
	stw %r5, 872(%r6)
	stw %r5, 876(%r6)
	stw %r5, 880(%r6)
	stw %r5, 884(%r6)
	stw %r5, 888(%r6)
	stw %r5, 892(%r6)
	li %r12, 448
214:
	addi %r12, %r12, -1
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
215:
	lwz %r4, 840(%r9)
	li %r8, 0
	lwz %r5, 840(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 844(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 848(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 852(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 856(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 860(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 864(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 868(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 872(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 876(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 880(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 884(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 888(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 892(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 215b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r5, %r12, -224
	cmpldi %cr0, %r5, 0
	beq %cr0, 216f
	addi %r5, %r12, -1
	cmpldi %cr0, %r5, 0
	beq %cr0, 218f
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
220:
	lwz %r4, 840(%r9)
	li %r8, 0
	lwz %r5, 112(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 116(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 120(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 124(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 128(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 132(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 136(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 140(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 144(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 148(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 152(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 156(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 160(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 164(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 220b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	b 219f
218:
219:
	b 217f
216:
217:
	cmpldi %cr0, %r12, 0
	bne %cr0, 214b
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
221:
	lwz %r4, 56(%r9)
	li %r8, 0
	lwz %r5, 840(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 844(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 848(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 852(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 856(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 860(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 864(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 868(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 872(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 876(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 880(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 884(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 888(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 892(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 221b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	li %r10, 1
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 896(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 900(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 904(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 908(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 912(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 916(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 920(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 924(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 928(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 932(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 936(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 940(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 944(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 948(%r6)
	rldicl %r8, %r7, 32, 32
	li %r4, 0
	subf %r11, %r8, %r4
	lwz %r5, 56(%r6)
	lwz %r7, 896(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 0(%r3)
	lwz %r5, 60(%r6)
	lwz %r7, 900(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 4(%r3)
	lwz %r5, 64(%r6)
	lwz %r7, 904(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 8(%r3)
	lwz %r5, 68(%r6)
	lwz %r7, 908(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 12(%r3)
	lwz %r5, 72(%r6)
	lwz %r7, 912(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 16(%r3)
	lwz %r5, 76(%r6)
	lwz %r7, 916(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 20(%r3)
	lwz %r5, 80(%r6)
	lwz %r7, 920(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 24(%r3)
	lwz %r5, 84(%r6)
	lwz %r7, 924(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 28(%r3)
	lwz %r5, 88(%r6)
	lwz %r7, 928(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 32(%r3)
	lwz %r5, 92(%r6)
	lwz %r7, 932(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 36(%r3)
	lwz %r5, 96(%r6)
	lwz %r7, 936(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 40(%r3)
	lwz %r5, 100(%r6)
	lwz %r7, 940(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 44(%r3)
	lwz %r5, 104(%r6)
	lwz %r7, 944(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 48(%r3)
	lwz %r5, 108(%r6)
	lwz %r7, 948(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 52(%r3)
	lbz %r12, 0(%r3)
	li %r9, 1
	and %r12, %r12, %r9
	rldicr %r12, %r12, 7, 56
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
222:
	lwz %r4, 0(%r9)
	li %r8, 0
	lwz %r5, 840(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 844(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 848(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 852(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 856(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 860(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 864(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 868(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 872(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 876(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 880(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 884(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 888(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 892(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 222b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	li %r10, 1
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 896(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 900(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 904(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 908(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 912(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 916(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 920(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 924(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 928(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 932(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 936(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 940(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 944(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 948(%r6)
	rldicl %r8, %r7, 32, 32
	li %r4, 0
	subf %r11, %r8, %r4
	lwz %r5, 56(%r6)
	lwz %r7, 896(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 0(%r3)
	lwz %r5, 60(%r6)
	lwz %r7, 900(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 4(%r3)
	lwz %r5, 64(%r6)
	lwz %r7, 904(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 8(%r3)
	lwz %r5, 68(%r6)
	lwz %r7, 908(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 12(%r3)
	lwz %r5, 72(%r6)
	lwz %r7, 912(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 16(%r3)
	lwz %r5, 76(%r6)
	lwz %r7, 916(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 20(%r3)
	lwz %r5, 80(%r6)
	lwz %r7, 920(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 24(%r3)
	lwz %r5, 84(%r6)
	lwz %r7, 924(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 28(%r3)
	lwz %r5, 88(%r6)
	lwz %r7, 928(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 32(%r3)
	lwz %r5, 92(%r6)
	lwz %r7, 932(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 36(%r3)
	lwz %r5, 96(%r6)
	lwz %r7, 936(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 40(%r3)
	lwz %r5, 100(%r6)
	lwz %r7, 940(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 44(%r3)
	lwz %r5, 104(%r6)
	lwz %r7, 944(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 48(%r3)
	lwz %r5, 108(%r6)
	lwz %r7, 948(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 52(%r3)
	stb %r12, 56(%r3)
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

vg_ed448_verify_equation:
	lbz %r7, 0(%r3)
	stb %r7, 3288(%r6)
	lbz %r7, 1(%r3)
	stb %r7, 3289(%r6)
	lbz %r7, 2(%r3)
	stb %r7, 3290(%r6)
	lbz %r7, 3(%r3)
	stb %r7, 3291(%r6)
	lbz %r7, 4(%r3)
	stb %r7, 3292(%r6)
	lbz %r7, 5(%r3)
	stb %r7, 3293(%r6)
	lbz %r7, 6(%r3)
	stb %r7, 3294(%r6)
	lbz %r7, 7(%r3)
	stb %r7, 3295(%r6)
	lbz %r7, 8(%r3)
	stb %r7, 3296(%r6)
	lbz %r7, 9(%r3)
	stb %r7, 3297(%r6)
	lbz %r7, 10(%r3)
	stb %r7, 3298(%r6)
	lbz %r7, 11(%r3)
	stb %r7, 3299(%r6)
	lbz %r7, 12(%r3)
	stb %r7, 3300(%r6)
	lbz %r7, 13(%r3)
	stb %r7, 3301(%r6)
	lbz %r7, 14(%r3)
	stb %r7, 3302(%r6)
	lbz %r7, 15(%r3)
	stb %r7, 3303(%r6)
	lbz %r7, 16(%r3)
	stb %r7, 3304(%r6)
	lbz %r7, 17(%r3)
	stb %r7, 3305(%r6)
	lbz %r7, 18(%r3)
	stb %r7, 3306(%r6)
	lbz %r7, 19(%r3)
	stb %r7, 3307(%r6)
	lbz %r7, 20(%r3)
	stb %r7, 3308(%r6)
	lbz %r7, 21(%r3)
	stb %r7, 3309(%r6)
	lbz %r7, 22(%r3)
	stb %r7, 3310(%r6)
	lbz %r7, 23(%r3)
	stb %r7, 3311(%r6)
	lbz %r7, 24(%r3)
	stb %r7, 3312(%r6)
	lbz %r7, 25(%r3)
	stb %r7, 3313(%r6)
	lbz %r7, 26(%r3)
	stb %r7, 3314(%r6)
	lbz %r7, 27(%r3)
	stb %r7, 3315(%r6)
	lbz %r7, 28(%r3)
	stb %r7, 3316(%r6)
	lbz %r7, 29(%r3)
	stb %r7, 3317(%r6)
	lbz %r7, 30(%r3)
	stb %r7, 3318(%r6)
	lbz %r7, 31(%r3)
	stb %r7, 3319(%r6)
	lbz %r7, 32(%r3)
	stb %r7, 3320(%r6)
	lbz %r7, 33(%r3)
	stb %r7, 3321(%r6)
	lbz %r7, 34(%r3)
	stb %r7, 3322(%r6)
	lbz %r7, 35(%r3)
	stb %r7, 3323(%r6)
	lbz %r7, 36(%r3)
	stb %r7, 3324(%r6)
	lbz %r7, 37(%r3)
	stb %r7, 3325(%r6)
	lbz %r7, 38(%r3)
	stb %r7, 3326(%r6)
	lbz %r7, 39(%r3)
	stb %r7, 3327(%r6)
	lbz %r7, 40(%r3)
	stb %r7, 3328(%r6)
	lbz %r7, 41(%r3)
	stb %r7, 3329(%r6)
	lbz %r7, 42(%r3)
	stb %r7, 3330(%r6)
	lbz %r7, 43(%r3)
	stb %r7, 3331(%r6)
	lbz %r7, 44(%r3)
	stb %r7, 3332(%r6)
	lbz %r7, 45(%r3)
	stb %r7, 3333(%r6)
	lbz %r7, 46(%r3)
	stb %r7, 3334(%r6)
	lbz %r7, 47(%r3)
	stb %r7, 3335(%r6)
	lbz %r7, 48(%r3)
	stb %r7, 3336(%r6)
	lbz %r7, 49(%r3)
	stb %r7, 3337(%r6)
	lbz %r7, 50(%r3)
	stb %r7, 3338(%r6)
	lbz %r7, 51(%r3)
	stb %r7, 3339(%r6)
	lbz %r7, 52(%r3)
	stb %r7, 3340(%r6)
	lbz %r7, 53(%r3)
	stb %r7, 3341(%r6)
	lbz %r7, 54(%r3)
	stb %r7, 3342(%r6)
	lbz %r7, 55(%r3)
	stb %r7, 3343(%r6)
	lbz %r7, 56(%r3)
	stb %r7, 3344(%r6)
	lbz %r7, 0(%r4)
	stb %r7, 3345(%r6)
	lbz %r7, 1(%r4)
	stb %r7, 3346(%r6)
	lbz %r7, 2(%r4)
	stb %r7, 3347(%r6)
	lbz %r7, 3(%r4)
	stb %r7, 3348(%r6)
	lbz %r7, 4(%r4)
	stb %r7, 3349(%r6)
	lbz %r7, 5(%r4)
	stb %r7, 3350(%r6)
	lbz %r7, 6(%r4)
	stb %r7, 3351(%r6)
	lbz %r7, 7(%r4)
	stb %r7, 3352(%r6)
	lbz %r7, 8(%r4)
	stb %r7, 3353(%r6)
	lbz %r7, 9(%r4)
	stb %r7, 3354(%r6)
	lbz %r7, 10(%r4)
	stb %r7, 3355(%r6)
	lbz %r7, 11(%r4)
	stb %r7, 3356(%r6)
	lbz %r7, 12(%r4)
	stb %r7, 3357(%r6)
	lbz %r7, 13(%r4)
	stb %r7, 3358(%r6)
	lbz %r7, 14(%r4)
	stb %r7, 3359(%r6)
	lbz %r7, 15(%r4)
	stb %r7, 3360(%r6)
	lbz %r7, 16(%r4)
	stb %r7, 3361(%r6)
	lbz %r7, 17(%r4)
	stb %r7, 3362(%r6)
	lbz %r7, 18(%r4)
	stb %r7, 3363(%r6)
	lbz %r7, 19(%r4)
	stb %r7, 3364(%r6)
	lbz %r7, 20(%r4)
	stb %r7, 3365(%r6)
	lbz %r7, 21(%r4)
	stb %r7, 3366(%r6)
	lbz %r7, 22(%r4)
	stb %r7, 3367(%r6)
	lbz %r7, 23(%r4)
	stb %r7, 3368(%r6)
	lbz %r7, 24(%r4)
	stb %r7, 3369(%r6)
	lbz %r7, 25(%r4)
	stb %r7, 3370(%r6)
	lbz %r7, 26(%r4)
	stb %r7, 3371(%r6)
	lbz %r7, 27(%r4)
	stb %r7, 3372(%r6)
	lbz %r7, 28(%r4)
	stb %r7, 3373(%r6)
	lbz %r7, 29(%r4)
	stb %r7, 3374(%r6)
	lbz %r7, 30(%r4)
	stb %r7, 3375(%r6)
	lbz %r7, 31(%r4)
	stb %r7, 3376(%r6)
	lbz %r7, 32(%r4)
	stb %r7, 3377(%r6)
	lbz %r7, 33(%r4)
	stb %r7, 3378(%r6)
	lbz %r7, 34(%r4)
	stb %r7, 3379(%r6)
	lbz %r7, 35(%r4)
	stb %r7, 3380(%r6)
	lbz %r7, 36(%r4)
	stb %r7, 3381(%r6)
	lbz %r7, 37(%r4)
	stb %r7, 3382(%r6)
	lbz %r7, 38(%r4)
	stb %r7, 3383(%r6)
	lbz %r7, 39(%r4)
	stb %r7, 3384(%r6)
	lbz %r7, 40(%r4)
	stb %r7, 3385(%r6)
	lbz %r7, 41(%r4)
	stb %r7, 3386(%r6)
	lbz %r7, 42(%r4)
	stb %r7, 3387(%r6)
	lbz %r7, 43(%r4)
	stb %r7, 3388(%r6)
	lbz %r7, 44(%r4)
	stb %r7, 3389(%r6)
	lbz %r7, 45(%r4)
	stb %r7, 3390(%r6)
	lbz %r7, 46(%r4)
	stb %r7, 3391(%r6)
	lbz %r7, 47(%r4)
	stb %r7, 3392(%r6)
	lbz %r7, 48(%r4)
	stb %r7, 3393(%r6)
	lbz %r7, 49(%r4)
	stb %r7, 3394(%r6)
	lbz %r7, 50(%r4)
	stb %r7, 3395(%r6)
	lbz %r7, 51(%r4)
	stb %r7, 3396(%r6)
	lbz %r7, 52(%r4)
	stb %r7, 3397(%r6)
	lbz %r7, 53(%r4)
	stb %r7, 3398(%r6)
	lbz %r7, 54(%r4)
	stb %r7, 3399(%r6)
	lbz %r7, 55(%r4)
	stb %r7, 3400(%r6)
	lbz %r7, 56(%r4)
	stb %r7, 3401(%r6)
	lbz %r7, 57(%r4)
	stb %r7, 3402(%r6)
	lbz %r7, 58(%r4)
	stb %r7, 3403(%r6)
	lbz %r7, 59(%r4)
	stb %r7, 3404(%r6)
	lbz %r7, 60(%r4)
	stb %r7, 3405(%r6)
	lbz %r7, 61(%r4)
	stb %r7, 3406(%r6)
	lbz %r7, 62(%r4)
	stb %r7, 3407(%r6)
	lbz %r7, 63(%r4)
	stb %r7, 3408(%r6)
	lbz %r7, 64(%r4)
	stb %r7, 3409(%r6)
	lbz %r7, 65(%r4)
	stb %r7, 3410(%r6)
	lbz %r7, 66(%r4)
	stb %r7, 3411(%r6)
	lbz %r7, 67(%r4)
	stb %r7, 3412(%r6)
	lbz %r7, 68(%r4)
	stb %r7, 3413(%r6)
	lbz %r7, 69(%r4)
	stb %r7, 3414(%r6)
	lbz %r7, 70(%r4)
	stb %r7, 3415(%r6)
	lbz %r7, 71(%r4)
	stb %r7, 3416(%r6)
	lbz %r7, 72(%r4)
	stb %r7, 3417(%r6)
	lbz %r7, 73(%r4)
	stb %r7, 3418(%r6)
	lbz %r7, 74(%r4)
	stb %r7, 3419(%r6)
	lbz %r7, 75(%r4)
	stb %r7, 3420(%r6)
	lbz %r7, 76(%r4)
	stb %r7, 3421(%r6)
	lbz %r7, 77(%r4)
	stb %r7, 3422(%r6)
	lbz %r7, 78(%r4)
	stb %r7, 3423(%r6)
	lbz %r7, 79(%r4)
	stb %r7, 3424(%r6)
	lbz %r7, 80(%r4)
	stb %r7, 3425(%r6)
	lbz %r7, 81(%r4)
	stb %r7, 3426(%r6)
	lbz %r7, 82(%r4)
	stb %r7, 3427(%r6)
	lbz %r7, 83(%r4)
	stb %r7, 3428(%r6)
	lbz %r7, 84(%r4)
	stb %r7, 3429(%r6)
	lbz %r7, 85(%r4)
	stb %r7, 3430(%r6)
	lbz %r7, 86(%r4)
	stb %r7, 3431(%r6)
	lbz %r7, 87(%r4)
	stb %r7, 3432(%r6)
	lbz %r7, 88(%r4)
	stb %r7, 3433(%r6)
	lbz %r7, 89(%r4)
	stb %r7, 3434(%r6)
	lbz %r7, 90(%r4)
	stb %r7, 3435(%r6)
	lbz %r7, 91(%r4)
	stb %r7, 3436(%r6)
	lbz %r7, 92(%r4)
	stb %r7, 3437(%r6)
	lbz %r7, 93(%r4)
	stb %r7, 3438(%r6)
	lbz %r7, 94(%r4)
	stb %r7, 3439(%r6)
	lbz %r7, 95(%r4)
	stb %r7, 3440(%r6)
	lbz %r7, 96(%r4)
	stb %r7, 3441(%r6)
	lbz %r7, 97(%r4)
	stb %r7, 3442(%r6)
	lbz %r7, 98(%r4)
	stb %r7, 3443(%r6)
	lbz %r7, 99(%r4)
	stb %r7, 3444(%r6)
	lbz %r7, 100(%r4)
	stb %r7, 3445(%r6)
	lbz %r7, 101(%r4)
	stb %r7, 3446(%r6)
	lbz %r7, 102(%r4)
	stb %r7, 3447(%r6)
	lbz %r7, 103(%r4)
	stb %r7, 3448(%r6)
	lbz %r7, 104(%r4)
	stb %r7, 3449(%r6)
	lbz %r7, 105(%r4)
	stb %r7, 3450(%r6)
	lbz %r7, 106(%r4)
	stb %r7, 3451(%r6)
	lbz %r7, 107(%r4)
	stb %r7, 3452(%r6)
	lbz %r7, 108(%r4)
	stb %r7, 3453(%r6)
	lbz %r7, 109(%r4)
	stb %r7, 3454(%r6)
	lbz %r7, 110(%r4)
	stb %r7, 3455(%r6)
	lbz %r7, 111(%r4)
	stb %r7, 3456(%r6)
	lbz %r7, 112(%r4)
	stb %r7, 3457(%r6)
	lbz %r7, 113(%r4)
	stb %r7, 3458(%r6)
	lbz %r7, 0(%r5)
	stb %r7, 3459(%r6)
	lbz %r7, 1(%r5)
	stb %r7, 3460(%r6)
	lbz %r7, 2(%r5)
	stb %r7, 3461(%r6)
	lbz %r7, 3(%r5)
	stb %r7, 3462(%r6)
	lbz %r7, 4(%r5)
	stb %r7, 3463(%r6)
	lbz %r7, 5(%r5)
	stb %r7, 3464(%r6)
	lbz %r7, 6(%r5)
	stb %r7, 3465(%r6)
	lbz %r7, 7(%r5)
	stb %r7, 3466(%r6)
	lbz %r7, 8(%r5)
	stb %r7, 3467(%r6)
	lbz %r7, 9(%r5)
	stb %r7, 3468(%r6)
	lbz %r7, 10(%r5)
	stb %r7, 3469(%r6)
	lbz %r7, 11(%r5)
	stb %r7, 3470(%r6)
	lbz %r7, 12(%r5)
	stb %r7, 3471(%r6)
	lbz %r7, 13(%r5)
	stb %r7, 3472(%r6)
	lbz %r7, 14(%r5)
	stb %r7, 3473(%r6)
	lbz %r7, 15(%r5)
	stb %r7, 3474(%r6)
	lbz %r7, 16(%r5)
	stb %r7, 3475(%r6)
	lbz %r7, 17(%r5)
	stb %r7, 3476(%r6)
	lbz %r7, 18(%r5)
	stb %r7, 3477(%r6)
	lbz %r7, 19(%r5)
	stb %r7, 3478(%r6)
	lbz %r7, 20(%r5)
	stb %r7, 3479(%r6)
	lbz %r7, 21(%r5)
	stb %r7, 3480(%r6)
	lbz %r7, 22(%r5)
	stb %r7, 3481(%r6)
	lbz %r7, 23(%r5)
	stb %r7, 3482(%r6)
	lbz %r7, 24(%r5)
	stb %r7, 3483(%r6)
	lbz %r7, 25(%r5)
	stb %r7, 3484(%r6)
	lbz %r7, 26(%r5)
	stb %r7, 3485(%r6)
	lbz %r7, 27(%r5)
	stb %r7, 3486(%r6)
	lbz %r7, 28(%r5)
	stb %r7, 3487(%r6)
	lbz %r7, 29(%r5)
	stb %r7, 3488(%r6)
	lbz %r7, 30(%r5)
	stb %r7, 3489(%r6)
	lbz %r7, 31(%r5)
	stb %r7, 3490(%r6)
	lbz %r7, 32(%r5)
	stb %r7, 3491(%r6)
	lbz %r7, 33(%r5)
	stb %r7, 3492(%r6)
	lbz %r7, 34(%r5)
	stb %r7, 3493(%r6)
	lbz %r7, 35(%r5)
	stb %r7, 3494(%r6)
	lbz %r7, 36(%r5)
	stb %r7, 3495(%r6)
	lbz %r7, 37(%r5)
	stb %r7, 3496(%r6)
	lbz %r7, 38(%r5)
	stb %r7, 3497(%r6)
	lbz %r7, 39(%r5)
	stb %r7, 3498(%r6)
	lbz %r7, 40(%r5)
	stb %r7, 3499(%r6)
	lbz %r7, 41(%r5)
	stb %r7, 3500(%r6)
	lbz %r7, 42(%r5)
	stb %r7, 3501(%r6)
	lbz %r7, 43(%r5)
	stb %r7, 3502(%r6)
	lbz %r7, 44(%r5)
	stb %r7, 3503(%r6)
	lbz %r7, 45(%r5)
	stb %r7, 3504(%r6)
	lbz %r7, 46(%r5)
	stb %r7, 3505(%r6)
	lbz %r7, 47(%r5)
	stb %r7, 3506(%r6)
	lbz %r7, 48(%r5)
	stb %r7, 3507(%r6)
	lbz %r7, 49(%r5)
	stb %r7, 3508(%r6)
	lbz %r7, 50(%r5)
	stb %r7, 3509(%r6)
	lbz %r7, 51(%r5)
	stb %r7, 3510(%r6)
	lbz %r7, 52(%r5)
	stb %r7, 3511(%r6)
	lbz %r7, 53(%r5)
	stb %r7, 3512(%r6)
	lbz %r7, 54(%r5)
	stb %r7, 3513(%r6)
	lbz %r7, 55(%r5)
	stb %r7, 3514(%r6)
	lbz %r7, 56(%r5)
	stb %r7, 3515(%r6)
	addi %r3, %r6, 4096
	li %r7, 0
	std %r7, 3520(%r6)
	lis %r7, -1
	ori %r7, %r7, 26454
	stw %r7, 336(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 340(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 344(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 348(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 352(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 356(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 360(%r6)
	lis %r7, -1
	ori %r7, %r7, 65534
	stw %r7, 364(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 368(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 372(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 376(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 380(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 384(%r6)
	lis %r7, -1
	ori %r7, %r7, 65535
	stw %r7, 388(%r6)
	lis %r7, -14580
	ori %r7, %r7, 49246
	stw %r7, 2896(%r6)
	lis %r7, 9766
	ori %r7, %r7, 43051
	stw %r7, 2900(%r6)
	lis %r7, -29952
	ori %r7, %r7, 37774
	stw %r7, 2904(%r6)
	lis %r7, 17211
	ori %r7, %r7, 32993
	stw %r7, 2908(%r6)
	lis %r7, 10934
	ori %r7, %r7, 25873
	stw %r7, 2912(%r6)
	lis %r7, 4782
	ori %r7, %r7, 6903
	stw %r7, 2916(%r6)
	lis %r7, -23597
	ori %r7, %r7, 42084
	stw %r7, 2920(%r6)
	lis %r7, -5523
	ori %r7, %r7, 58148
	stw %r7, 2924(%r6)
	lis %r7, 18191
	ori %r7, %r7, 5991
	stw %r7, 2928(%r6)
	lis %r7, -25068
	ori %r7, %r7, 25968
	stw %r7, 2932(%r6)
	lis %r7, 8895
	ori %r7, %r7, 14042
	stw %r7, 2936(%r6)
	lis %r7, 8733
	ori %r7, %r7, 5542
	stw %r7, 2940(%r6)
	lis %r7, 27629
	ori %r7, %r7, 3565
	stw %r7, 2944(%r6)
	lis %r7, 20249
	ori %r7, %r7, 28870
	stw %r7, 2948(%r6)
	lis %r7, -3536
	ori %r7, %r7, 64020
	stw %r7, 2952(%r6)
	lis %r7, -26616
	ori %r7, %r7, 31067
	stw %r7, 2956(%r6)
	lis %r7, 20183
	ori %r7, %r7, 51373
	stw %r7, 2960(%r6)
	lis %r7, -579
	ori %r7, %r7, 4908
	stw %r7, 2964(%r6)
	lis %r7, -6532
	ori %r7, %r7, 14788
	stw %r7, 2968(%r6)
	lis %r7, 15059
	ori %r7, %r7, 65308
	stw %r7, 2972(%r6)
	lis %r7, 1440
	ori %r7, %r7, 49879
	stw %r7, 2976(%r6)
	lis %r7, -30856
	ori %r7, %r7, 39966
	stw %r7, 2980(%r6)
	lis %r7, 27811
	ori %r7, %r7, 38976
	stw %r7, 2984(%r6)
	lis %r7, 19434
	ori %r7, %r7, 29555
	stw %r7, 2988(%r6)
	lis %r7, 22217
	ori %r7, %r7, 51042
	stw %r7, 2992(%r6)
	lis %r7, -30602
	ori %r7, %r7, 8247
	stw %r7, 2996(%r6)
	lis %r7, 28342
	ori %r7, %r7, 48164
	stw %r7, 3000(%r6)
	lis %r7, 26943
	ori %r7, %r7, 18033
	stw %r7, 3004(%r6)
	lis %r7, 0
	ori %r7, %r7, 1
	stw %r7, 3232(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3236(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3240(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3244(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3248(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3252(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3256(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3260(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3264(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3268(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3272(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3276(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3280(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 3284(%r6)
	lwz %r7, 3345(%r6)
	stw %r7, 168(%r6)
	stw %r7, 56(%r6)
	lwz %r7, 3349(%r6)
	stw %r7, 172(%r6)
	stw %r7, 60(%r6)
	lwz %r7, 3353(%r6)
	stw %r7, 176(%r6)
	stw %r7, 64(%r6)
	lwz %r7, 3357(%r6)
	stw %r7, 180(%r6)
	stw %r7, 68(%r6)
	lwz %r7, 3361(%r6)
	stw %r7, 184(%r6)
	stw %r7, 72(%r6)
	lwz %r7, 3365(%r6)
	stw %r7, 188(%r6)
	stw %r7, 76(%r6)
	lwz %r7, 3369(%r6)
	stw %r7, 192(%r6)
	stw %r7, 80(%r6)
	lwz %r7, 3373(%r6)
	stw %r7, 196(%r6)
	stw %r7, 84(%r6)
	lwz %r7, 3377(%r6)
	stw %r7, 200(%r6)
	stw %r7, 88(%r6)
	lwz %r7, 3381(%r6)
	stw %r7, 204(%r6)
	stw %r7, 92(%r6)
	lwz %r7, 3385(%r6)
	stw %r7, 208(%r6)
	stw %r7, 96(%r6)
	lwz %r7, 3389(%r6)
	stw %r7, 212(%r6)
	stw %r7, 100(%r6)
	lwz %r7, 3393(%r6)
	stw %r7, 216(%r6)
	stw %r7, 104(%r6)
	lwz %r7, 3397(%r6)
	stw %r7, 220(%r6)
	stw %r7, 108(%r6)
	li %r8, 1
	li %r10, 1
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 896(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 900(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 904(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 908(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 912(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 916(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 920(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 924(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 928(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 932(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 936(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 940(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 944(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 948(%r6)
	rldicl %r8, %r7, 32, 32
	li %r4, 0
	subf %r11, %r8, %r4
	lwz %r5, 56(%r6)
	lwz %r7, 896(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 0(%r3)
	lwz %r5, 60(%r6)
	lwz %r7, 900(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 4(%r3)
	lwz %r5, 64(%r6)
	lwz %r7, 904(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 8(%r3)
	lwz %r5, 68(%r6)
	lwz %r7, 908(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 12(%r3)
	lwz %r5, 72(%r6)
	lwz %r7, 912(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 16(%r3)
	lwz %r5, 76(%r6)
	lwz %r7, 916(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 20(%r3)
	lwz %r5, 80(%r6)
	lwz %r7, 920(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 24(%r3)
	lwz %r5, 84(%r6)
	lwz %r7, 924(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 28(%r3)
	lwz %r5, 88(%r6)
	lwz %r7, 928(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 32(%r3)
	lwz %r5, 92(%r6)
	lwz %r7, 932(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 36(%r3)
	lwz %r5, 96(%r6)
	lwz %r7, 936(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 40(%r3)
	lwz %r5, 100(%r6)
	lwz %r7, 940(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 44(%r3)
	lwz %r5, 104(%r6)
	lwz %r7, 944(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 48(%r3)
	lwz %r5, 108(%r6)
	lwz %r7, 948(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 52(%r3)
	li %r10, 0
	lwz %r7, 0(%r3)
	lwz %r8, 3345(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 4(%r3)
	lwz %r8, 3349(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 8(%r3)
	lwz %r8, 3353(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 12(%r3)
	lwz %r8, 3357(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 16(%r3)
	lwz %r8, 3361(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 20(%r3)
	lwz %r8, 3365(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 24(%r3)
	lwz %r8, 3369(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 28(%r3)
	lwz %r8, 3373(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 32(%r3)
	lwz %r8, 3377(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 36(%r3)
	lwz %r8, 3381(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 40(%r3)
	lwz %r8, 3385(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 44(%r3)
	lwz %r8, 3389(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 48(%r3)
	lwz %r8, 3393(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 52(%r3)
	lwz %r8, 3397(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	ld %r9, 3520(%r6)
	or %r9, %r9, %r10
	std %r9, 3520(%r6)
	lbz %r7, 3401(%r6)
	li %r8, 127
	and %r8, %r7, %r8
	ld %r9, 3520(%r6)
	or %r9, %r9, %r8
	std %r9, 3520(%r6)
	rldicl %r7, %r7, 57, 7
	stb %r7, 3528(%r6)
	lis %r7, 0
	ori %r7, %r7, 1
	stw %r7, 224(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 228(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 232(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 236(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 240(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 244(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 248(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 252(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 256(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 260(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 264(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 268(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 272(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 276(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
20:
	lwz %r4, 168(%r9)
	li %r8, 0
	lwz %r5, 168(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 172(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 176(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 180(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 184(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 188(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 192(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 196(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 200(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 204(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 208(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 212(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 216(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 220(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 20b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 280(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 284(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 288(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 292(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 296(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 300(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 304(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 308(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 312(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 316(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 320(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 324(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 328(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 332(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 280(%r6)
	add %r7, %r7, %r8
	stw %r7, 280(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 284(%r6)
	add %r7, %r7, %r8
	stw %r7, 284(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 288(%r6)
	add %r7, %r7, %r8
	stw %r7, 288(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 292(%r6)
	add %r7, %r7, %r8
	stw %r7, 292(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 296(%r6)
	add %r7, %r7, %r8
	stw %r7, 296(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 300(%r6)
	add %r7, %r7, %r8
	stw %r7, 300(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 304(%r6)
	add %r7, %r7, %r8
	stw %r7, 304(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 308(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 308(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 312(%r6)
	add %r7, %r7, %r8
	stw %r7, 312(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 316(%r6)
	add %r7, %r7, %r8
	stw %r7, 316(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 320(%r6)
	add %r7, %r7, %r8
	stw %r7, 320(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 324(%r6)
	add %r7, %r7, %r8
	stw %r7, 324(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 328(%r6)
	add %r7, %r7, %r8
	stw %r7, 328(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 332(%r6)
	add %r7, %r7, %r8
	stw %r7, 332(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 280(%r6)
	add %r7, %r7, %r8
	stw %r7, 280(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 284(%r6)
	add %r7, %r7, %r8
	stw %r7, 284(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 288(%r6)
	add %r7, %r7, %r8
	stw %r7, 288(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 292(%r6)
	add %r7, %r7, %r8
	stw %r7, 292(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 296(%r6)
	add %r7, %r7, %r8
	stw %r7, 296(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 300(%r6)
	add %r7, %r7, %r8
	stw %r7, 300(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 304(%r6)
	add %r7, %r7, %r8
	stw %r7, 304(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 308(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 308(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 312(%r6)
	add %r7, %r7, %r8
	stw %r7, 312(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 316(%r6)
	add %r7, %r7, %r8
	stw %r7, 316(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 320(%r6)
	add %r7, %r7, %r8
	stw %r7, 320(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 324(%r6)
	add %r7, %r7, %r8
	stw %r7, 324(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 328(%r6)
	add %r7, %r7, %r8
	stw %r7, 328(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 332(%r6)
	add %r7, %r7, %r8
	stw %r7, 332(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 34, 29
	lwz %r7, 280(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 224(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 284(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 228(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 288(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 232(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 292(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 236(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 296(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 240(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 300(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 244(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 304(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 248(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 308(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -8
	lwz %r5, 252(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 312(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 256(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 316(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 260(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 320(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 264(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 324(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 268(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 328(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 272(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 332(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 276(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 392(%r6)
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 416(%r6)
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 392(%r6)
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 416(%r6)
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
21:
	lwz %r4, 336(%r9)
	li %r8, 0
	lwz %r5, 280(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 284(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 288(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 292(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 296(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 300(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 304(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 308(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 312(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 316(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 320(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 324(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 328(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 332(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 21b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 34, 29
	lwz %r7, 448(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 224(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 228(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 232(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 236(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 240(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 244(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 248(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -8
	lwz %r5, 252(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 256(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 260(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 264(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 268(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 272(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 276(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
22:
	lwz %r4, 392(%r9)
	li %r8, 0
	lwz %r5, 392(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 396(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 400(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 404(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 408(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 412(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 416(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 420(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 424(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 428(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 432(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 436(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 440(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 444(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 22b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
23:
	lwz %r4, 504(%r9)
	li %r8, 0
	lwz %r5, 392(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 396(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 400(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 404(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 408(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 412(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 416(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 420(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 424(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 428(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 432(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 436(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 440(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 444(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 23b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
24:
	lwz %r4, 504(%r9)
	li %r8, 0
	lwz %r5, 448(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 452(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 456(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 460(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 464(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 468(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 472(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 476(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 480(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 484(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 488(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 492(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 496(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 500(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 24b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
25:
	lwz %r4, 392(%r9)
	li %r8, 0
	lwz %r5, 448(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 452(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 456(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 460(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 464(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 468(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 472(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 476(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 480(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 484(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 488(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 492(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 496(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 500(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 25b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
26:
	lwz %r4, 560(%r9)
	li %r8, 0
	lwz %r5, 560(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 564(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 568(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 572(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 576(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 580(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 584(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 588(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 592(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 596(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 600(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 604(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 608(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 612(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 26b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
27:
	lwz %r4, 504(%r9)
	li %r8, 0
	lwz %r5, 560(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 564(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 568(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 572(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 576(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 580(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 584(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 588(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 592(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 596(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 600(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 604(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 608(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 612(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 27b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 112(%r6)
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 112(%r6)
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	li %r4, 1
	li %r5, 0
	stw %r4, 840(%r6)
	stw %r5, 844(%r6)
	stw %r5, 848(%r6)
	stw %r5, 852(%r6)
	stw %r5, 856(%r6)
	stw %r5, 860(%r6)
	stw %r5, 864(%r6)
	stw %r5, 868(%r6)
	stw %r5, 872(%r6)
	stw %r5, 876(%r6)
	stw %r5, 880(%r6)
	stw %r5, 884(%r6)
	stw %r5, 888(%r6)
	stw %r5, 892(%r6)
	li %r12, 446
28:
	addi %r12, %r12, -1
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
29:
	lwz %r4, 840(%r9)
	li %r8, 0
	lwz %r5, 840(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 844(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 848(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 852(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 856(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 860(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 864(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 868(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 872(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 876(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 880(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 884(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 888(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 892(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 29b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r5, %r12, -222
	cmpldi %cr0, %r5, 0
	beq %cr0, 210f
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
212:
	lwz %r4, 840(%r9)
	li %r8, 0
	lwz %r5, 112(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 116(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 120(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 124(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 128(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 132(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 136(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 140(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 144(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 148(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 152(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 156(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 160(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 164(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 212b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	b 211f
210:
211:
	cmpldi %cr0, %r12, 0
	bne %cr0, 28b
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
213:
	lwz %r4, 504(%r9)
	li %r8, 0
	lwz %r5, 840(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 844(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 848(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 852(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 856(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 860(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 864(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 868(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 872(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 876(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 880(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 884(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 888(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 892(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 213b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 672(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 676(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 680(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 684(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 688(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 692(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 696(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 700(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 704(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 708(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 712(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 716(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 720(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 724(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 672(%r6)
	add %r7, %r7, %r8
	stw %r7, 672(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 676(%r6)
	add %r7, %r7, %r8
	stw %r7, 676(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 680(%r6)
	add %r7, %r7, %r8
	stw %r7, 680(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 684(%r6)
	add %r7, %r7, %r8
	stw %r7, 684(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 688(%r6)
	add %r7, %r7, %r8
	stw %r7, 688(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 692(%r6)
	add %r7, %r7, %r8
	stw %r7, 692(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 696(%r6)
	add %r7, %r7, %r8
	stw %r7, 696(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 700(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 700(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 704(%r6)
	add %r7, %r7, %r8
	stw %r7, 704(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 708(%r6)
	add %r7, %r7, %r8
	stw %r7, 708(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 712(%r6)
	add %r7, %r7, %r8
	stw %r7, 712(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 716(%r6)
	add %r7, %r7, %r8
	stw %r7, 716(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 720(%r6)
	add %r7, %r7, %r8
	stw %r7, 720(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 724(%r6)
	add %r7, %r7, %r8
	stw %r7, 724(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 672(%r6)
	add %r7, %r7, %r8
	stw %r7, 672(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 676(%r6)
	add %r7, %r7, %r8
	stw %r7, 676(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 680(%r6)
	add %r7, %r7, %r8
	stw %r7, 680(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 684(%r6)
	add %r7, %r7, %r8
	stw %r7, 684(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 688(%r6)
	add %r7, %r7, %r8
	stw %r7, 688(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 692(%r6)
	add %r7, %r7, %r8
	stw %r7, 692(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 696(%r6)
	add %r7, %r7, %r8
	stw %r7, 696(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 700(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 700(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 704(%r6)
	add %r7, %r7, %r8
	stw %r7, 704(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 708(%r6)
	add %r7, %r7, %r8
	stw %r7, 708(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 712(%r6)
	add %r7, %r7, %r8
	stw %r7, 712(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 716(%r6)
	add %r7, %r7, %r8
	stw %r7, 716(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 720(%r6)
	add %r7, %r7, %r8
	stw %r7, 720(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 724(%r6)
	add %r7, %r7, %r8
	stw %r7, 724(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
214:
	lwz %r4, 672(%r9)
	li %r8, 0
	lwz %r5, 672(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 676(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 680(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 684(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 688(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 692(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 696(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 700(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 704(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 708(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 712(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 716(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 720(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 724(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 214b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
215:
	lwz %r4, 448(%r9)
	li %r8, 0
	lwz %r5, 616(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 620(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 624(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 628(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 632(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 636(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 640(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 644(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 648(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 652(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 656(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 660(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 664(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 668(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 215b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 34, 29
	lwz %r7, 616(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 392(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 396(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 400(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 404(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 408(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 412(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 416(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -8
	lwz %r5, 420(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 424(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 428(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 432(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 436(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 440(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 444(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	li %r10, 1
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 896(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 900(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 904(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 908(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 912(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 916(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 920(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 924(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 928(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 932(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 936(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 940(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 944(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 948(%r6)
	rldicl %r8, %r7, 32, 32
	li %r4, 0
	subf %r11, %r8, %r4
	lwz %r5, 56(%r6)
	lwz %r7, 896(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 0(%r3)
	lwz %r5, 60(%r6)
	lwz %r7, 900(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 4(%r3)
	lwz %r5, 64(%r6)
	lwz %r7, 904(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 8(%r3)
	lwz %r5, 68(%r6)
	lwz %r7, 908(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 12(%r3)
	lwz %r5, 72(%r6)
	lwz %r7, 912(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 16(%r3)
	lwz %r5, 76(%r6)
	lwz %r7, 916(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 20(%r3)
	lwz %r5, 80(%r6)
	lwz %r7, 920(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 24(%r3)
	lwz %r5, 84(%r6)
	lwz %r7, 924(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 28(%r3)
	lwz %r5, 88(%r6)
	lwz %r7, 928(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 32(%r3)
	lwz %r5, 92(%r6)
	lwz %r7, 932(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 36(%r3)
	lwz %r5, 96(%r6)
	lwz %r7, 936(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 40(%r3)
	lwz %r5, 100(%r6)
	lwz %r7, 940(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 44(%r3)
	lwz %r5, 104(%r6)
	lwz %r7, 944(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 48(%r3)
	lwz %r5, 108(%r6)
	lwz %r7, 948(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 52(%r3)
	li %r10, 0
	lwz %r7, 0(%r3)
	or %r10, %r10, %r7
	lwz %r7, 4(%r3)
	or %r10, %r10, %r7
	lwz %r7, 8(%r3)
	or %r10, %r10, %r7
	lwz %r7, 12(%r3)
	or %r10, %r10, %r7
	lwz %r7, 16(%r3)
	or %r10, %r10, %r7
	lwz %r7, 20(%r3)
	or %r10, %r10, %r7
	lwz %r7, 24(%r3)
	or %r10, %r10, %r7
	lwz %r7, 28(%r3)
	or %r10, %r10, %r7
	lwz %r7, 32(%r3)
	or %r10, %r10, %r7
	lwz %r7, 36(%r3)
	or %r10, %r10, %r7
	lwz %r7, 40(%r3)
	or %r10, %r10, %r7
	lwz %r7, 44(%r3)
	or %r10, %r10, %r7
	lwz %r7, 48(%r3)
	or %r10, %r10, %r7
	lwz %r7, 52(%r3)
	or %r10, %r10, %r7
	ld %r9, 3520(%r6)
	or %r9, %r9, %r10
	std %r9, 3520(%r6)
	li %r11, 0
	lwz %r5, 672(%r6)
	lwz %r7, 672(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 56(%r6)
	lwz %r5, 676(%r6)
	lwz %r7, 676(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 60(%r6)
	lwz %r5, 680(%r6)
	lwz %r7, 680(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 64(%r6)
	lwz %r5, 684(%r6)
	lwz %r7, 684(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 68(%r6)
	lwz %r5, 688(%r6)
	lwz %r7, 688(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 72(%r6)
	lwz %r5, 692(%r6)
	lwz %r7, 692(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 76(%r6)
	lwz %r5, 696(%r6)
	lwz %r7, 696(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 80(%r6)
	lwz %r5, 700(%r6)
	lwz %r7, 700(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 84(%r6)
	lwz %r5, 704(%r6)
	lwz %r7, 704(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 88(%r6)
	lwz %r5, 708(%r6)
	lwz %r7, 708(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 92(%r6)
	lwz %r5, 712(%r6)
	lwz %r7, 712(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 96(%r6)
	lwz %r5, 716(%r6)
	lwz %r7, 716(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 100(%r6)
	lwz %r5, 720(%r6)
	lwz %r7, 720(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 104(%r6)
	lwz %r5, 724(%r6)
	lwz %r7, 724(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 108(%r6)
	li %r8, 1
	li %r10, 1
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 896(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 900(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 904(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 908(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 912(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 916(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 920(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 924(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 928(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 932(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 936(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 940(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 944(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 948(%r6)
	rldicl %r8, %r7, 32, 32
	li %r4, 0
	subf %r11, %r8, %r4
	lwz %r5, 56(%r6)
	lwz %r7, 896(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 0(%r3)
	lwz %r5, 60(%r6)
	lwz %r7, 900(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 4(%r3)
	lwz %r5, 64(%r6)
	lwz %r7, 904(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 8(%r3)
	lwz %r5, 68(%r6)
	lwz %r7, 908(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 12(%r3)
	lwz %r5, 72(%r6)
	lwz %r7, 912(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 16(%r3)
	lwz %r5, 76(%r6)
	lwz %r7, 916(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 20(%r3)
	lwz %r5, 80(%r6)
	lwz %r7, 920(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 24(%r3)
	lwz %r5, 84(%r6)
	lwz %r7, 924(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 28(%r3)
	lwz %r5, 88(%r6)
	lwz %r7, 928(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 32(%r3)
	lwz %r5, 92(%r6)
	lwz %r7, 932(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 36(%r3)
	lwz %r5, 96(%r6)
	lwz %r7, 936(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 40(%r3)
	lwz %r5, 100(%r6)
	lwz %r7, 940(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 44(%r3)
	lwz %r5, 104(%r6)
	lwz %r7, 944(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 48(%r3)
	lwz %r5, 108(%r6)
	lwz %r7, 948(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 52(%r3)
	li %r10, 0
	lwz %r7, 0(%r3)
	or %r10, %r10, %r7
	lwz %r7, 4(%r3)
	or %r10, %r10, %r7
	lwz %r7, 8(%r3)
	or %r10, %r10, %r7
	lwz %r7, 12(%r3)
	or %r10, %r10, %r7
	lwz %r7, 16(%r3)
	or %r10, %r10, %r7
	lwz %r7, 20(%r3)
	or %r10, %r10, %r7
	lwz %r7, 24(%r3)
	or %r10, %r10, %r7
	lwz %r7, 28(%r3)
	or %r10, %r10, %r7
	lwz %r7, 32(%r3)
	or %r10, %r10, %r7
	lwz %r7, 36(%r3)
	or %r10, %r10, %r7
	lwz %r7, 40(%r3)
	or %r10, %r10, %r7
	lwz %r7, 44(%r3)
	or %r10, %r10, %r7
	lwz %r7, 48(%r3)
	or %r10, %r10, %r7
	lwz %r7, 52(%r3)
	or %r10, %r10, %r7
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	lbz %r7, 3528(%r6)
	and %r8, %r10, %r7
	ld %r9, 3520(%r6)
	or %r9, %r9, %r8
	std %r9, 3520(%r6)
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 34, 29
	lwz %r7, 672(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 672(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 676(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 676(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 680(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 680(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 684(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 684(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 688(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 688(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 692(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 692(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 696(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 696(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 700(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -8
	lwz %r5, 700(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 704(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 704(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 708(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 708(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 712(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 712(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 716(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 716(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 720(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 720(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 724(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 724(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 34, 29
	lwz %r7, 616(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 672(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 676(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 680(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 684(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 688(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 692(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 696(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -8
	lwz %r5, 700(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 704(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 708(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 712(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 716(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 720(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 724(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 728(%r6)
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 732(%r6)
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 740(%r6)
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 744(%r6)
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 748(%r6)
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 752(%r6)
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 756(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 760(%r6)
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 764(%r6)
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 768(%r6)
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 772(%r6)
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 776(%r6)
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 780(%r6)
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 728(%r6)
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 732(%r6)
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 740(%r6)
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 744(%r6)
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 748(%r6)
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 752(%r6)
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 756(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 760(%r6)
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 764(%r6)
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 768(%r6)
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 772(%r6)
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 776(%r6)
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 780(%r6)
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	lbz %r8, 0(%r3)
	li %r9, 1
	and %r8, %r8, %r9
	lbz %r7, 3528(%r6)
	xor %r8, %r8, %r7
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 728(%r6)
	lwz %r7, 672(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3120(%r6)
	lwz %r5, 732(%r6)
	lwz %r7, 676(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3124(%r6)
	lwz %r5, 736(%r6)
	lwz %r7, 680(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3128(%r6)
	lwz %r5, 740(%r6)
	lwz %r7, 684(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3132(%r6)
	lwz %r5, 744(%r6)
	lwz %r7, 688(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3136(%r6)
	lwz %r5, 748(%r6)
	lwz %r7, 692(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3140(%r6)
	lwz %r5, 752(%r6)
	lwz %r7, 696(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3144(%r6)
	lwz %r5, 756(%r6)
	lwz %r7, 700(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3148(%r6)
	lwz %r5, 760(%r6)
	lwz %r7, 704(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3152(%r6)
	lwz %r5, 764(%r6)
	lwz %r7, 708(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3156(%r6)
	lwz %r5, 768(%r6)
	lwz %r7, 712(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3160(%r6)
	lwz %r5, 772(%r6)
	lwz %r7, 716(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3164(%r6)
	lwz %r5, 776(%r6)
	lwz %r7, 720(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3168(%r6)
	lwz %r5, 780(%r6)
	lwz %r7, 724(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3172(%r6)
	lwz %r5, 168(%r6)
	lwz %r7, 168(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3176(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 172(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3180(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 176(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3184(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 180(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3188(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 184(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3192(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 188(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3196(%r6)
	lwz %r5, 192(%r6)
	lwz %r7, 192(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3200(%r6)
	lwz %r5, 196(%r6)
	lwz %r7, 196(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3204(%r6)
	lwz %r5, 200(%r6)
	lwz %r7, 200(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3208(%r6)
	lwz %r5, 204(%r6)
	lwz %r7, 204(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3212(%r6)
	lwz %r5, 208(%r6)
	lwz %r7, 208(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3216(%r6)
	lwz %r5, 212(%r6)
	lwz %r7, 212(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3220(%r6)
	lwz %r5, 216(%r6)
	lwz %r7, 216(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3224(%r6)
	lwz %r5, 220(%r6)
	lwz %r7, 220(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3228(%r6)
	lwz %r7, 3288(%r6)
	stw %r7, 168(%r6)
	stw %r7, 56(%r6)
	lwz %r7, 3292(%r6)
	stw %r7, 172(%r6)
	stw %r7, 60(%r6)
	lwz %r7, 3296(%r6)
	stw %r7, 176(%r6)
	stw %r7, 64(%r6)
	lwz %r7, 3300(%r6)
	stw %r7, 180(%r6)
	stw %r7, 68(%r6)
	lwz %r7, 3304(%r6)
	stw %r7, 184(%r6)
	stw %r7, 72(%r6)
	lwz %r7, 3308(%r6)
	stw %r7, 188(%r6)
	stw %r7, 76(%r6)
	lwz %r7, 3312(%r6)
	stw %r7, 192(%r6)
	stw %r7, 80(%r6)
	lwz %r7, 3316(%r6)
	stw %r7, 196(%r6)
	stw %r7, 84(%r6)
	lwz %r7, 3320(%r6)
	stw %r7, 200(%r6)
	stw %r7, 88(%r6)
	lwz %r7, 3324(%r6)
	stw %r7, 204(%r6)
	stw %r7, 92(%r6)
	lwz %r7, 3328(%r6)
	stw %r7, 208(%r6)
	stw %r7, 96(%r6)
	lwz %r7, 3332(%r6)
	stw %r7, 212(%r6)
	stw %r7, 100(%r6)
	lwz %r7, 3336(%r6)
	stw %r7, 216(%r6)
	stw %r7, 104(%r6)
	lwz %r7, 3340(%r6)
	stw %r7, 220(%r6)
	stw %r7, 108(%r6)
	li %r8, 1
	li %r10, 1
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 896(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 900(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 904(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 908(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 912(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 916(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 920(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 924(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 928(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 932(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 936(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 940(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 944(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 948(%r6)
	rldicl %r8, %r7, 32, 32
	li %r4, 0
	subf %r11, %r8, %r4
	lwz %r5, 56(%r6)
	lwz %r7, 896(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 0(%r3)
	lwz %r5, 60(%r6)
	lwz %r7, 900(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 4(%r3)
	lwz %r5, 64(%r6)
	lwz %r7, 904(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 8(%r3)
	lwz %r5, 68(%r6)
	lwz %r7, 908(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 12(%r3)
	lwz %r5, 72(%r6)
	lwz %r7, 912(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 16(%r3)
	lwz %r5, 76(%r6)
	lwz %r7, 916(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 20(%r3)
	lwz %r5, 80(%r6)
	lwz %r7, 920(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 24(%r3)
	lwz %r5, 84(%r6)
	lwz %r7, 924(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 28(%r3)
	lwz %r5, 88(%r6)
	lwz %r7, 928(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 32(%r3)
	lwz %r5, 92(%r6)
	lwz %r7, 932(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 36(%r3)
	lwz %r5, 96(%r6)
	lwz %r7, 936(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 40(%r3)
	lwz %r5, 100(%r6)
	lwz %r7, 940(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 44(%r3)
	lwz %r5, 104(%r6)
	lwz %r7, 944(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 48(%r3)
	lwz %r5, 108(%r6)
	lwz %r7, 948(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 52(%r3)
	li %r10, 0
	lwz %r7, 0(%r3)
	lwz %r8, 3288(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 4(%r3)
	lwz %r8, 3292(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 8(%r3)
	lwz %r8, 3296(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 12(%r3)
	lwz %r8, 3300(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 16(%r3)
	lwz %r8, 3304(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 20(%r3)
	lwz %r8, 3308(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 24(%r3)
	lwz %r8, 3312(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 28(%r3)
	lwz %r8, 3316(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 32(%r3)
	lwz %r8, 3320(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 36(%r3)
	lwz %r8, 3324(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 40(%r3)
	lwz %r8, 3328(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 44(%r3)
	lwz %r8, 3332(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 48(%r3)
	lwz %r8, 3336(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 52(%r3)
	lwz %r8, 3340(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	ld %r9, 3520(%r6)
	or %r9, %r9, %r10
	std %r9, 3520(%r6)
	lbz %r7, 3344(%r6)
	li %r8, 127
	and %r8, %r7, %r8
	ld %r9, 3520(%r6)
	or %r9, %r9, %r8
	std %r9, 3520(%r6)
	rldicl %r7, %r7, 57, 7
	stb %r7, 3528(%r6)
	lis %r7, 0
	ori %r7, %r7, 1
	stw %r7, 224(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 228(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 232(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 236(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 240(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 244(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 248(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 252(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 256(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 260(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 264(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 268(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 272(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 276(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
216:
	lwz %r4, 168(%r9)
	li %r8, 0
	lwz %r5, 168(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 172(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 176(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 180(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 184(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 188(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 192(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 196(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 200(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 204(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 208(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 212(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 216(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 220(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 216b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 280(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 284(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 288(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 292(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 296(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 300(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 304(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 308(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 312(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 316(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 320(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 324(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 328(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 332(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 280(%r6)
	add %r7, %r7, %r8
	stw %r7, 280(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 284(%r6)
	add %r7, %r7, %r8
	stw %r7, 284(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 288(%r6)
	add %r7, %r7, %r8
	stw %r7, 288(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 292(%r6)
	add %r7, %r7, %r8
	stw %r7, 292(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 296(%r6)
	add %r7, %r7, %r8
	stw %r7, 296(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 300(%r6)
	add %r7, %r7, %r8
	stw %r7, 300(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 304(%r6)
	add %r7, %r7, %r8
	stw %r7, 304(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 308(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 308(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 312(%r6)
	add %r7, %r7, %r8
	stw %r7, 312(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 316(%r6)
	add %r7, %r7, %r8
	stw %r7, 316(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 320(%r6)
	add %r7, %r7, %r8
	stw %r7, 320(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 324(%r6)
	add %r7, %r7, %r8
	stw %r7, 324(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 328(%r6)
	add %r7, %r7, %r8
	stw %r7, 328(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 332(%r6)
	add %r7, %r7, %r8
	stw %r7, 332(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 280(%r6)
	add %r7, %r7, %r8
	stw %r7, 280(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 284(%r6)
	add %r7, %r7, %r8
	stw %r7, 284(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 288(%r6)
	add %r7, %r7, %r8
	stw %r7, 288(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 292(%r6)
	add %r7, %r7, %r8
	stw %r7, 292(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 296(%r6)
	add %r7, %r7, %r8
	stw %r7, 296(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 300(%r6)
	add %r7, %r7, %r8
	stw %r7, 300(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 304(%r6)
	add %r7, %r7, %r8
	stw %r7, 304(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 308(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 308(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 312(%r6)
	add %r7, %r7, %r8
	stw %r7, 312(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 316(%r6)
	add %r7, %r7, %r8
	stw %r7, 316(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 320(%r6)
	add %r7, %r7, %r8
	stw %r7, 320(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 324(%r6)
	add %r7, %r7, %r8
	stw %r7, 324(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 328(%r6)
	add %r7, %r7, %r8
	stw %r7, 328(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 332(%r6)
	add %r7, %r7, %r8
	stw %r7, 332(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 34, 29
	lwz %r7, 280(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 224(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 284(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 228(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 288(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 232(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 292(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 236(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 296(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 240(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 300(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 244(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 304(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 248(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 308(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -8
	lwz %r5, 252(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 312(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 256(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 316(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 260(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 320(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 264(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 324(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 268(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 328(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 272(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 332(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 276(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 392(%r6)
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 416(%r6)
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 392(%r6)
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 416(%r6)
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
217:
	lwz %r4, 336(%r9)
	li %r8, 0
	lwz %r5, 280(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 284(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 288(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 292(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 296(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 300(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 304(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 308(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 312(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 316(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 320(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 324(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 328(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 332(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 217b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 34, 29
	lwz %r7, 448(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 224(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 228(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 232(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 236(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 240(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 244(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 248(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -8
	lwz %r5, 252(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 256(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 260(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 264(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 268(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 272(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 276(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
218:
	lwz %r4, 392(%r9)
	li %r8, 0
	lwz %r5, 392(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 396(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 400(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 404(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 408(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 412(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 416(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 420(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 424(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 428(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 432(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 436(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 440(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 444(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 218b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
219:
	lwz %r4, 504(%r9)
	li %r8, 0
	lwz %r5, 392(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 396(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 400(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 404(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 408(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 412(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 416(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 420(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 424(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 428(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 432(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 436(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 440(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 444(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 219b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
220:
	lwz %r4, 504(%r9)
	li %r8, 0
	lwz %r5, 448(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 452(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 456(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 460(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 464(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 468(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 472(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 476(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 480(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 484(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 488(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 492(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 496(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 500(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 220b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
221:
	lwz %r4, 392(%r9)
	li %r8, 0
	lwz %r5, 448(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 452(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 456(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 460(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 464(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 468(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 472(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 476(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 480(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 484(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 488(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 492(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 496(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 500(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 221b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
222:
	lwz %r4, 560(%r9)
	li %r8, 0
	lwz %r5, 560(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 564(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 568(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 572(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 576(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 580(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 584(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 588(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 592(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 596(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 600(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 604(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 608(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 612(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 222b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
223:
	lwz %r4, 504(%r9)
	li %r8, 0
	lwz %r5, 560(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 564(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 568(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 572(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 576(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 580(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 584(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 588(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 592(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 596(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 600(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 604(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 608(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 612(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 223b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 112(%r6)
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 112(%r6)
	add %r7, %r7, %r8
	stw %r7, 112(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 116(%r6)
	add %r7, %r7, %r8
	stw %r7, 116(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 120(%r6)
	add %r7, %r7, %r8
	stw %r7, 120(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 124(%r6)
	add %r7, %r7, %r8
	stw %r7, 124(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 128(%r6)
	add %r7, %r7, %r8
	stw %r7, 128(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 132(%r6)
	add %r7, %r7, %r8
	stw %r7, 132(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 136(%r6)
	add %r7, %r7, %r8
	stw %r7, 136(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 140(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 140(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 144(%r6)
	add %r7, %r7, %r8
	stw %r7, 144(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 148(%r6)
	add %r7, %r7, %r8
	stw %r7, 148(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 152(%r6)
	add %r7, %r7, %r8
	stw %r7, 152(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 156(%r6)
	add %r7, %r7, %r8
	stw %r7, 156(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 160(%r6)
	add %r7, %r7, %r8
	stw %r7, 160(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 164(%r6)
	add %r7, %r7, %r8
	stw %r7, 164(%r6)
	rldicl %r8, %r7, 32, 32
	li %r4, 1
	li %r5, 0
	stw %r4, 840(%r6)
	stw %r5, 844(%r6)
	stw %r5, 848(%r6)
	stw %r5, 852(%r6)
	stw %r5, 856(%r6)
	stw %r5, 860(%r6)
	stw %r5, 864(%r6)
	stw %r5, 868(%r6)
	stw %r5, 872(%r6)
	stw %r5, 876(%r6)
	stw %r5, 880(%r6)
	stw %r5, 884(%r6)
	stw %r5, 888(%r6)
	stw %r5, 892(%r6)
	li %r12, 446
224:
	addi %r12, %r12, -1
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
225:
	lwz %r4, 840(%r9)
	li %r8, 0
	lwz %r5, 840(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 844(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 848(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 852(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 856(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 860(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 864(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 868(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 872(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 876(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 880(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 884(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 888(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 892(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 225b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r5, %r12, -222
	cmpldi %cr0, %r5, 0
	beq %cr0, 226f
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
228:
	lwz %r4, 840(%r9)
	li %r8, 0
	lwz %r5, 112(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 116(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 120(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 124(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 128(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 132(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 136(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 140(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 144(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 148(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 152(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 156(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 160(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 164(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 228b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	b 227f
226:
227:
	cmpldi %cr0, %r12, 0
	bne %cr0, 224b
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
229:
	lwz %r4, 504(%r9)
	li %r8, 0
	lwz %r5, 840(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 844(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 848(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 852(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 856(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 860(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 864(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 868(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 872(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 876(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 880(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 884(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 888(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 892(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 229b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 672(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 676(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 680(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 684(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 688(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 692(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 696(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 700(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 704(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 708(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 712(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 716(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 720(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 724(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 672(%r6)
	add %r7, %r7, %r8
	stw %r7, 672(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 676(%r6)
	add %r7, %r7, %r8
	stw %r7, 676(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 680(%r6)
	add %r7, %r7, %r8
	stw %r7, 680(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 684(%r6)
	add %r7, %r7, %r8
	stw %r7, 684(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 688(%r6)
	add %r7, %r7, %r8
	stw %r7, 688(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 692(%r6)
	add %r7, %r7, %r8
	stw %r7, 692(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 696(%r6)
	add %r7, %r7, %r8
	stw %r7, 696(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 700(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 700(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 704(%r6)
	add %r7, %r7, %r8
	stw %r7, 704(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 708(%r6)
	add %r7, %r7, %r8
	stw %r7, 708(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 712(%r6)
	add %r7, %r7, %r8
	stw %r7, 712(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 716(%r6)
	add %r7, %r7, %r8
	stw %r7, 716(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 720(%r6)
	add %r7, %r7, %r8
	stw %r7, 720(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 724(%r6)
	add %r7, %r7, %r8
	stw %r7, 724(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 672(%r6)
	add %r7, %r7, %r8
	stw %r7, 672(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 676(%r6)
	add %r7, %r7, %r8
	stw %r7, 676(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 680(%r6)
	add %r7, %r7, %r8
	stw %r7, 680(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 684(%r6)
	add %r7, %r7, %r8
	stw %r7, 684(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 688(%r6)
	add %r7, %r7, %r8
	stw %r7, 688(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 692(%r6)
	add %r7, %r7, %r8
	stw %r7, 692(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 696(%r6)
	add %r7, %r7, %r8
	stw %r7, 696(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 700(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 700(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 704(%r6)
	add %r7, %r7, %r8
	stw %r7, 704(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 708(%r6)
	add %r7, %r7, %r8
	stw %r7, 708(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 712(%r6)
	add %r7, %r7, %r8
	stw %r7, 712(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 716(%r6)
	add %r7, %r7, %r8
	stw %r7, 716(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 720(%r6)
	add %r7, %r7, %r8
	stw %r7, 720(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 724(%r6)
	add %r7, %r7, %r8
	stw %r7, 724(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
230:
	lwz %r4, 672(%r9)
	li %r8, 0
	lwz %r5, 672(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 676(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 680(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 684(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 688(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 692(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 696(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 700(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 704(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 708(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 712(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 716(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 720(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 724(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 230b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
231:
	lwz %r4, 448(%r9)
	li %r8, 0
	lwz %r5, 616(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 620(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 624(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 628(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 632(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 636(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 640(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 644(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 648(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 652(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 656(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 660(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 664(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 668(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 231b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 34, 29
	lwz %r7, 616(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 392(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 396(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 400(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 404(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 408(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 412(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 416(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -8
	lwz %r5, 420(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 424(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 428(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 432(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 436(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 440(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 444(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 1
	li %r10, 1
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 896(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 900(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 904(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 908(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 912(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 916(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 920(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 924(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 928(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 932(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 936(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 940(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 944(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 948(%r6)
	rldicl %r8, %r7, 32, 32
	li %r4, 0
	subf %r11, %r8, %r4
	lwz %r5, 56(%r6)
	lwz %r7, 896(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 0(%r3)
	lwz %r5, 60(%r6)
	lwz %r7, 900(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 4(%r3)
	lwz %r5, 64(%r6)
	lwz %r7, 904(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 8(%r3)
	lwz %r5, 68(%r6)
	lwz %r7, 908(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 12(%r3)
	lwz %r5, 72(%r6)
	lwz %r7, 912(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 16(%r3)
	lwz %r5, 76(%r6)
	lwz %r7, 916(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 20(%r3)
	lwz %r5, 80(%r6)
	lwz %r7, 920(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 24(%r3)
	lwz %r5, 84(%r6)
	lwz %r7, 924(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 28(%r3)
	lwz %r5, 88(%r6)
	lwz %r7, 928(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 32(%r3)
	lwz %r5, 92(%r6)
	lwz %r7, 932(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 36(%r3)
	lwz %r5, 96(%r6)
	lwz %r7, 936(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 40(%r3)
	lwz %r5, 100(%r6)
	lwz %r7, 940(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 44(%r3)
	lwz %r5, 104(%r6)
	lwz %r7, 944(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 48(%r3)
	lwz %r5, 108(%r6)
	lwz %r7, 948(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 52(%r3)
	li %r10, 0
	lwz %r7, 0(%r3)
	or %r10, %r10, %r7
	lwz %r7, 4(%r3)
	or %r10, %r10, %r7
	lwz %r7, 8(%r3)
	or %r10, %r10, %r7
	lwz %r7, 12(%r3)
	or %r10, %r10, %r7
	lwz %r7, 16(%r3)
	or %r10, %r10, %r7
	lwz %r7, 20(%r3)
	or %r10, %r10, %r7
	lwz %r7, 24(%r3)
	or %r10, %r10, %r7
	lwz %r7, 28(%r3)
	or %r10, %r10, %r7
	lwz %r7, 32(%r3)
	or %r10, %r10, %r7
	lwz %r7, 36(%r3)
	or %r10, %r10, %r7
	lwz %r7, 40(%r3)
	or %r10, %r10, %r7
	lwz %r7, 44(%r3)
	or %r10, %r10, %r7
	lwz %r7, 48(%r3)
	or %r10, %r10, %r7
	lwz %r7, 52(%r3)
	or %r10, %r10, %r7
	ld %r9, 3520(%r6)
	or %r9, %r9, %r10
	std %r9, 3520(%r6)
	li %r11, 0
	lwz %r5, 672(%r6)
	lwz %r7, 672(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 56(%r6)
	lwz %r5, 676(%r6)
	lwz %r7, 676(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 60(%r6)
	lwz %r5, 680(%r6)
	lwz %r7, 680(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 64(%r6)
	lwz %r5, 684(%r6)
	lwz %r7, 684(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 68(%r6)
	lwz %r5, 688(%r6)
	lwz %r7, 688(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 72(%r6)
	lwz %r5, 692(%r6)
	lwz %r7, 692(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 76(%r6)
	lwz %r5, 696(%r6)
	lwz %r7, 696(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 80(%r6)
	lwz %r5, 700(%r6)
	lwz %r7, 700(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 84(%r6)
	lwz %r5, 704(%r6)
	lwz %r7, 704(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 88(%r6)
	lwz %r5, 708(%r6)
	lwz %r7, 708(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 92(%r6)
	lwz %r5, 712(%r6)
	lwz %r7, 712(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 96(%r6)
	lwz %r5, 716(%r6)
	lwz %r7, 716(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 100(%r6)
	lwz %r5, 720(%r6)
	lwz %r7, 720(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 104(%r6)
	lwz %r5, 724(%r6)
	lwz %r7, 724(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 108(%r6)
	li %r8, 1
	li %r10, 1
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 896(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 900(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 904(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 908(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 912(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 916(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 920(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 924(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 928(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 932(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 936(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 940(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 944(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 948(%r6)
	rldicl %r8, %r7, 32, 32
	li %r4, 0
	subf %r11, %r8, %r4
	lwz %r5, 56(%r6)
	lwz %r7, 896(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 0(%r3)
	lwz %r5, 60(%r6)
	lwz %r7, 900(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 4(%r3)
	lwz %r5, 64(%r6)
	lwz %r7, 904(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 8(%r3)
	lwz %r5, 68(%r6)
	lwz %r7, 908(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 12(%r3)
	lwz %r5, 72(%r6)
	lwz %r7, 912(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 16(%r3)
	lwz %r5, 76(%r6)
	lwz %r7, 916(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 20(%r3)
	lwz %r5, 80(%r6)
	lwz %r7, 920(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 24(%r3)
	lwz %r5, 84(%r6)
	lwz %r7, 924(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 28(%r3)
	lwz %r5, 88(%r6)
	lwz %r7, 928(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 32(%r3)
	lwz %r5, 92(%r6)
	lwz %r7, 932(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 36(%r3)
	lwz %r5, 96(%r6)
	lwz %r7, 936(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 40(%r3)
	lwz %r5, 100(%r6)
	lwz %r7, 940(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 44(%r3)
	lwz %r5, 104(%r6)
	lwz %r7, 944(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 48(%r3)
	lwz %r5, 108(%r6)
	lwz %r7, 948(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 52(%r3)
	li %r10, 0
	lwz %r7, 0(%r3)
	or %r10, %r10, %r7
	lwz %r7, 4(%r3)
	or %r10, %r10, %r7
	lwz %r7, 8(%r3)
	or %r10, %r10, %r7
	lwz %r7, 12(%r3)
	or %r10, %r10, %r7
	lwz %r7, 16(%r3)
	or %r10, %r10, %r7
	lwz %r7, 20(%r3)
	or %r10, %r10, %r7
	lwz %r7, 24(%r3)
	or %r10, %r10, %r7
	lwz %r7, 28(%r3)
	or %r10, %r10, %r7
	lwz %r7, 32(%r3)
	or %r10, %r10, %r7
	lwz %r7, 36(%r3)
	or %r10, %r10, %r7
	lwz %r7, 40(%r3)
	or %r10, %r10, %r7
	lwz %r7, 44(%r3)
	or %r10, %r10, %r7
	lwz %r7, 48(%r3)
	or %r10, %r10, %r7
	lwz %r7, 52(%r3)
	or %r10, %r10, %r7
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	lbz %r7, 3528(%r6)
	and %r8, %r10, %r7
	ld %r9, 3520(%r6)
	or %r9, %r9, %r8
	std %r9, 3520(%r6)
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 34, 29
	lwz %r7, 672(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 672(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 676(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 676(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 680(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 680(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 684(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 684(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 688(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 688(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 692(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 692(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 696(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 696(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 700(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -8
	lwz %r5, 700(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 704(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 704(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 708(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 708(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 712(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 712(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 716(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 716(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 720(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 720(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 724(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 724(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 34, 29
	lwz %r7, 616(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 672(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 676(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 680(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 684(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 688(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 692(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 696(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -8
	lwz %r5, 700(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 704(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 708(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 712(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 716(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 720(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 724(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 728(%r6)
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 732(%r6)
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 740(%r6)
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 744(%r6)
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 748(%r6)
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 752(%r6)
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 756(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 760(%r6)
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 764(%r6)
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 768(%r6)
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 772(%r6)
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 776(%r6)
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 780(%r6)
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 728(%r6)
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 732(%r6)
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 740(%r6)
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 744(%r6)
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 748(%r6)
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 752(%r6)
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 756(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 760(%r6)
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 764(%r6)
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 768(%r6)
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 772(%r6)
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 776(%r6)
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 780(%r6)
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	lbz %r8, 0(%r3)
	li %r9, 1
	and %r8, %r8, %r9
	lbz %r7, 3528(%r6)
	xor %r8, %r8, %r7
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 728(%r6)
	lwz %r7, 672(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3008(%r6)
	lwz %r5, 732(%r6)
	lwz %r7, 676(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3012(%r6)
	lwz %r5, 736(%r6)
	lwz %r7, 680(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3016(%r6)
	lwz %r5, 740(%r6)
	lwz %r7, 684(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3020(%r6)
	lwz %r5, 744(%r6)
	lwz %r7, 688(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3024(%r6)
	lwz %r5, 748(%r6)
	lwz %r7, 692(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3028(%r6)
	lwz %r5, 752(%r6)
	lwz %r7, 696(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3032(%r6)
	lwz %r5, 756(%r6)
	lwz %r7, 700(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3036(%r6)
	lwz %r5, 760(%r6)
	lwz %r7, 704(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3040(%r6)
	lwz %r5, 764(%r6)
	lwz %r7, 708(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3044(%r6)
	lwz %r5, 768(%r6)
	lwz %r7, 712(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3048(%r6)
	lwz %r5, 772(%r6)
	lwz %r7, 716(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3052(%r6)
	lwz %r5, 776(%r6)
	lwz %r7, 720(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3056(%r6)
	lwz %r5, 780(%r6)
	lwz %r7, 724(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3060(%r6)
	lwz %r5, 168(%r6)
	lwz %r7, 168(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3064(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 172(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3068(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 176(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3072(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 180(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3076(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 184(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3080(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 188(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3084(%r6)
	lwz %r5, 192(%r6)
	lwz %r7, 192(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3088(%r6)
	lwz %r5, 196(%r6)
	lwz %r7, 196(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3092(%r6)
	lwz %r5, 200(%r6)
	lwz %r7, 200(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3096(%r6)
	lwz %r5, 204(%r6)
	lwz %r7, 204(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3100(%r6)
	lwz %r5, 208(%r6)
	lwz %r7, 208(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3104(%r6)
	lwz %r5, 212(%r6)
	lwz %r7, 212(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3108(%r6)
	lwz %r5, 216(%r6)
	lwz %r7, 216(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3112(%r6)
	lwz %r5, 220(%r6)
	lwz %r7, 220(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 3116(%r6)
	lwz %r7, 3402(%r6)
	stw %r7, 168(%r6)
	stw %r7, 56(%r6)
	lwz %r7, 3406(%r6)
	stw %r7, 172(%r6)
	stw %r7, 60(%r6)
	lwz %r7, 3410(%r6)
	stw %r7, 176(%r6)
	stw %r7, 64(%r6)
	lwz %r7, 3414(%r6)
	stw %r7, 180(%r6)
	stw %r7, 68(%r6)
	lwz %r7, 3418(%r6)
	stw %r7, 184(%r6)
	stw %r7, 72(%r6)
	lwz %r7, 3422(%r6)
	stw %r7, 188(%r6)
	stw %r7, 76(%r6)
	lwz %r7, 3426(%r6)
	stw %r7, 192(%r6)
	stw %r7, 80(%r6)
	lwz %r7, 3430(%r6)
	stw %r7, 196(%r6)
	stw %r7, 84(%r6)
	lwz %r7, 3434(%r6)
	stw %r7, 200(%r6)
	stw %r7, 88(%r6)
	lwz %r7, 3438(%r6)
	stw %r7, 204(%r6)
	stw %r7, 92(%r6)
	lwz %r7, 3442(%r6)
	stw %r7, 208(%r6)
	stw %r7, 96(%r6)
	lwz %r7, 3446(%r6)
	stw %r7, 212(%r6)
	stw %r7, 100(%r6)
	lwz %r7, 3450(%r6)
	stw %r7, 216(%r6)
	stw %r7, 104(%r6)
	lwz %r7, 3454(%r6)
	stw %r7, 220(%r6)
	stw %r7, 108(%r6)
	li %r8, 1
	lwz %r7, 168(%r6)
	lis %r5, 21671
	ori %r5, %r5, 47884
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lis %r5, -9081
	ori %r5, %r5, 15725
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lis %r5, 29242
	ori %r5, %r5, 28842
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 64(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lis %r5, -8557
	ori %r5, %r5, 15757
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 68(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lis %r5, 20777
	ori %r5, %r5, 51567
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 72(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lis %r5, 15281
	ori %r5, %r5, 9398
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 76(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	lis %r5, -31947
	ori %r5, %r5, 56342
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 80(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 84(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 88(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 92(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 96(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 100(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	lis %r5, 0
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 104(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	lis %r5, -16384
	ori %r5, %r5, 0
	rlwinm %r5, %r5, 0, 0, 31
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 108(%r6)
	rldicl %r8, %r7, 32, 32
	ld %r9, 3520(%r6)
	or %r9, %r9, %r8
	std %r9, 3520(%r6)
	lbz %r7, 3458(%r6)
	ld %r9, 3520(%r6)
	or %r9, %r9, %r7
	std %r9, 3520(%r6)
	addi %r9, %r6, 0
	li %r11, 458
	li %r7, 0
	li %r8, 1
232:
	stb %r7, 1064(%r9)
	stb %r7, 1065(%r9)
	stb %r7, 1066(%r9)
	stb %r8, 1067(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 232b
	stb %r8, 1072(%r6)
	addi %r9, %r6, 0
	addi %r4, %r6, 3402
	li %r11, 57
233:
	lbz %r7, 0(%r4)
	rldicr %r8, %r7, 63, 0
	rldicl %r8, %r8, 1, 63
	stb %r8, 1074(%r9)
	rldicr %r8, %r7, 62, 1
	rldicl %r8, %r8, 1, 63
	stb %r8, 1078(%r9)
	rldicr %r8, %r7, 61, 2
	rldicl %r8, %r8, 1, 63
	stb %r8, 1082(%r9)
	rldicr %r8, %r7, 60, 3
	rldicl %r8, %r8, 1, 63
	stb %r8, 1086(%r9)
	rldicr %r8, %r7, 59, 4
	rldicl %r8, %r8, 1, 63
	stb %r8, 1090(%r9)
	rldicr %r8, %r7, 58, 5
	rldicl %r8, %r8, 1, 63
	stb %r8, 1094(%r9)
	rldicr %r8, %r7, 57, 6
	rldicl %r8, %r8, 1, 63
	stb %r8, 1098(%r9)
	rldicr %r8, %r7, 56, 7
	rldicl %r8, %r8, 1, 63
	stb %r8, 1102(%r9)
	addi %r4, %r4, 1
	addi %r9, %r9, 32
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 233b
	addi %r9, %r6, 0
	addi %r4, %r6, 3459
	li %r11, 57
234:
	lbz %r7, 0(%r4)
	rldicr %r8, %r7, 63, 0
	rldicl %r8, %r8, 1, 63
	stb %r8, 1073(%r9)
	rldicr %r8, %r7, 62, 1
	rldicl %r8, %r8, 1, 63
	stb %r8, 1077(%r9)
	rldicr %r8, %r7, 61, 2
	rldicl %r8, %r8, 1, 63
	stb %r8, 1081(%r9)
	rldicr %r8, %r7, 60, 3
	rldicl %r8, %r8, 1, 63
	stb %r8, 1085(%r9)
	rldicr %r8, %r7, 59, 4
	rldicl %r8, %r8, 1, 63
	stb %r8, 1089(%r9)
	rldicr %r8, %r7, 58, 5
	rldicl %r8, %r8, 1, 63
	stb %r8, 1093(%r9)
	rldicr %r8, %r7, 57, 6
	rldicl %r8, %r8, 1, 63
	stb %r8, 1097(%r9)
	rldicr %r8, %r7, 56, 7
	rldicl %r8, %r8, 1, 63
	stb %r8, 1101(%r9)
	addi %r4, %r4, 1
	addi %r9, %r9, 32
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 234b
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 56(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 60(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 64(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 68(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 72(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 76(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 80(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 84(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 88(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 92(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 96(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 100(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 104(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 108(%r6)
	lis %r7, 0
	ori %r7, %r7, 1
	stw %r7, 0(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 4(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 8(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 12(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 16(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 20(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 24(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 28(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 32(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 36(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 40(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 44(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 48(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 52(%r6)
	lis %r7, 0
	ori %r7, %r7, 1
	stw %r7, 112(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 116(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 120(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 124(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 128(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 132(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 136(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 140(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 144(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 148(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 152(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 156(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 160(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 164(%r6)
	li %r12, 1832
235:
	addi %r12, %r12, -1
	rldicr %r4, %r12, 63, 0
	rldicl %r4, %r4, 1, 63
	li %r11, 0
	subf %r11, %r4, %r11
	lwz %r5, 3120(%r6)
	lwz %r7, 3008(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 168(%r6)
	lwz %r5, 3124(%r6)
	lwz %r7, 3012(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 172(%r6)
	lwz %r5, 3128(%r6)
	lwz %r7, 3016(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 176(%r6)
	lwz %r5, 3132(%r6)
	lwz %r7, 3020(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 180(%r6)
	lwz %r5, 3136(%r6)
	lwz %r7, 3024(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 184(%r6)
	lwz %r5, 3140(%r6)
	lwz %r7, 3028(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 188(%r6)
	lwz %r5, 3144(%r6)
	lwz %r7, 3032(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 192(%r6)
	lwz %r5, 3148(%r6)
	lwz %r7, 3036(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 196(%r6)
	lwz %r5, 3152(%r6)
	lwz %r7, 3040(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 200(%r6)
	lwz %r5, 3156(%r6)
	lwz %r7, 3044(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 204(%r6)
	lwz %r5, 3160(%r6)
	lwz %r7, 3048(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 208(%r6)
	lwz %r5, 3164(%r6)
	lwz %r7, 3052(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 212(%r6)
	lwz %r5, 3168(%r6)
	lwz %r7, 3056(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 216(%r6)
	lwz %r5, 3172(%r6)
	lwz %r7, 3060(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 220(%r6)
	lwz %r5, 3176(%r6)
	lwz %r7, 3064(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 224(%r6)
	lwz %r5, 3180(%r6)
	lwz %r7, 3068(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 228(%r6)
	lwz %r5, 3184(%r6)
	lwz %r7, 3072(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 232(%r6)
	lwz %r5, 3188(%r6)
	lwz %r7, 3076(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 236(%r6)
	lwz %r5, 3192(%r6)
	lwz %r7, 3080(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 240(%r6)
	lwz %r5, 3196(%r6)
	lwz %r7, 3084(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 244(%r6)
	lwz %r5, 3200(%r6)
	lwz %r7, 3088(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 248(%r6)
	lwz %r5, 3204(%r6)
	lwz %r7, 3092(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 252(%r6)
	lwz %r5, 3208(%r6)
	lwz %r7, 3096(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 256(%r6)
	lwz %r5, 3212(%r6)
	lwz %r7, 3100(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 260(%r6)
	lwz %r5, 3216(%r6)
	lwz %r7, 3104(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 264(%r6)
	lwz %r5, 3220(%r6)
	lwz %r7, 3108(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 268(%r6)
	lwz %r5, 3224(%r6)
	lwz %r7, 3112(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 272(%r6)
	lwz %r5, 3228(%r6)
	lwz %r7, 3116(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 276(%r6)
	lwz %r5, 2896(%r6)
	lwz %r7, 56(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 392(%r6)
	lwz %r5, 2900(%r6)
	lwz %r7, 60(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 396(%r6)
	lwz %r5, 2904(%r6)
	lwz %r7, 64(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 400(%r6)
	lwz %r5, 2908(%r6)
	lwz %r7, 68(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 404(%r6)
	lwz %r5, 2912(%r6)
	lwz %r7, 72(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 408(%r6)
	lwz %r5, 2916(%r6)
	lwz %r7, 76(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 412(%r6)
	lwz %r5, 2920(%r6)
	lwz %r7, 80(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 416(%r6)
	lwz %r5, 2924(%r6)
	lwz %r7, 84(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 420(%r6)
	lwz %r5, 2928(%r6)
	lwz %r7, 88(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 424(%r6)
	lwz %r5, 2932(%r6)
	lwz %r7, 92(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 428(%r6)
	lwz %r5, 2936(%r6)
	lwz %r7, 96(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 432(%r6)
	lwz %r5, 2940(%r6)
	lwz %r7, 100(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 436(%r6)
	lwz %r5, 2944(%r6)
	lwz %r7, 104(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 440(%r6)
	lwz %r5, 2948(%r6)
	lwz %r7, 108(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 444(%r6)
	lwz %r5, 2952(%r6)
	lwz %r7, 0(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 448(%r6)
	lwz %r5, 2956(%r6)
	lwz %r7, 4(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 452(%r6)
	lwz %r5, 2960(%r6)
	lwz %r7, 8(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 456(%r6)
	lwz %r5, 2964(%r6)
	lwz %r7, 12(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 460(%r6)
	lwz %r5, 2968(%r6)
	lwz %r7, 16(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 464(%r6)
	lwz %r5, 2972(%r6)
	lwz %r7, 20(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 468(%r6)
	lwz %r5, 2976(%r6)
	lwz %r7, 24(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 472(%r6)
	lwz %r5, 2980(%r6)
	lwz %r7, 28(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 476(%r6)
	lwz %r5, 2984(%r6)
	lwz %r7, 32(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 480(%r6)
	lwz %r5, 2988(%r6)
	lwz %r7, 36(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 484(%r6)
	lwz %r5, 2992(%r6)
	lwz %r7, 40(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 488(%r6)
	lwz %r5, 2996(%r6)
	lwz %r7, 44(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 492(%r6)
	lwz %r5, 3000(%r6)
	lwz %r7, 48(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 496(%r6)
	lwz %r5, 3004(%r6)
	lwz %r7, 52(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 500(%r6)
	lwz %r5, 3232(%r6)
	lwz %r7, 112(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 504(%r6)
	lwz %r5, 3236(%r6)
	lwz %r7, 116(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 508(%r6)
	lwz %r5, 3240(%r6)
	lwz %r7, 120(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 512(%r6)
	lwz %r5, 3244(%r6)
	lwz %r7, 124(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 516(%r6)
	lwz %r5, 3248(%r6)
	lwz %r7, 128(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 520(%r6)
	lwz %r5, 3252(%r6)
	lwz %r7, 132(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 524(%r6)
	lwz %r5, 3256(%r6)
	lwz %r7, 136(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 528(%r6)
	lwz %r5, 3260(%r6)
	lwz %r7, 140(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 532(%r6)
	lwz %r5, 3264(%r6)
	lwz %r7, 144(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 536(%r6)
	lwz %r5, 3268(%r6)
	lwz %r7, 148(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 540(%r6)
	lwz %r5, 3272(%r6)
	lwz %r7, 152(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 544(%r6)
	lwz %r5, 3276(%r6)
	lwz %r7, 156(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 548(%r6)
	lwz %r5, 3280(%r6)
	lwz %r7, 160(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 552(%r6)
	lwz %r5, 3284(%r6)
	lwz %r7, 164(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 556(%r6)
	rldicr %r4, %r12, 62, 1
	rldicl %r4, %r4, 1, 63
	li %r11, 0
	subf %r11, %r4, %r11
	lwz %r5, 168(%r6)
	lwz %r7, 392(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 168(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 396(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 172(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 400(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 176(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 404(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 180(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 408(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 184(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 412(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 188(%r6)
	lwz %r5, 192(%r6)
	lwz %r7, 416(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 192(%r6)
	lwz %r5, 196(%r6)
	lwz %r7, 420(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 196(%r6)
	lwz %r5, 200(%r6)
	lwz %r7, 424(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 200(%r6)
	lwz %r5, 204(%r6)
	lwz %r7, 428(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 204(%r6)
	lwz %r5, 208(%r6)
	lwz %r7, 432(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 208(%r6)
	lwz %r5, 212(%r6)
	lwz %r7, 436(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 212(%r6)
	lwz %r5, 216(%r6)
	lwz %r7, 440(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 216(%r6)
	lwz %r5, 220(%r6)
	lwz %r7, 444(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 220(%r6)
	lwz %r5, 224(%r6)
	lwz %r7, 448(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 224(%r6)
	lwz %r5, 228(%r6)
	lwz %r7, 452(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 228(%r6)
	lwz %r5, 232(%r6)
	lwz %r7, 456(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 232(%r6)
	lwz %r5, 236(%r6)
	lwz %r7, 460(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 236(%r6)
	lwz %r5, 240(%r6)
	lwz %r7, 464(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 240(%r6)
	lwz %r5, 244(%r6)
	lwz %r7, 468(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 244(%r6)
	lwz %r5, 248(%r6)
	lwz %r7, 472(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 248(%r6)
	lwz %r5, 252(%r6)
	lwz %r7, 476(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 252(%r6)
	lwz %r5, 256(%r6)
	lwz %r7, 480(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 256(%r6)
	lwz %r5, 260(%r6)
	lwz %r7, 484(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 260(%r6)
	lwz %r5, 264(%r6)
	lwz %r7, 488(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 264(%r6)
	lwz %r5, 268(%r6)
	lwz %r7, 492(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 268(%r6)
	lwz %r5, 272(%r6)
	lwz %r7, 496(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 272(%r6)
	lwz %r5, 276(%r6)
	lwz %r7, 500(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 276(%r6)
	lwz %r5, 3232(%r6)
	lwz %r7, 504(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 280(%r6)
	lwz %r5, 3236(%r6)
	lwz %r7, 508(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 284(%r6)
	lwz %r5, 3240(%r6)
	lwz %r7, 512(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 288(%r6)
	lwz %r5, 3244(%r6)
	lwz %r7, 516(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 292(%r6)
	lwz %r5, 3248(%r6)
	lwz %r7, 520(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 296(%r6)
	lwz %r5, 3252(%r6)
	lwz %r7, 524(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 300(%r6)
	lwz %r5, 3256(%r6)
	lwz %r7, 528(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 304(%r6)
	lwz %r5, 3260(%r6)
	lwz %r7, 532(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 308(%r6)
	lwz %r5, 3264(%r6)
	lwz %r7, 536(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 312(%r6)
	lwz %r5, 3268(%r6)
	lwz %r7, 540(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 316(%r6)
	lwz %r5, 3272(%r6)
	lwz %r7, 544(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 320(%r6)
	lwz %r5, 3276(%r6)
	lwz %r7, 548(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 324(%r6)
	lwz %r5, 3280(%r6)
	lwz %r7, 552(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 328(%r6)
	lwz %r5, 3284(%r6)
	lwz %r7, 556(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 332(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
236:
	lwz %r4, 112(%r9)
	li %r8, 0
	lwz %r5, 280(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 284(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 288(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 292(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 296(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 300(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 304(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 308(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 312(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 316(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 320(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 324(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 328(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 332(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 236b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
237:
	lwz %r4, 560(%r9)
	li %r8, 0
	lwz %r5, 560(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 564(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 568(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 572(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 576(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 580(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 584(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 588(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 592(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 596(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 600(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 604(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 608(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 612(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 237b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
238:
	lwz %r4, 56(%r9)
	li %r8, 0
	lwz %r5, 168(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 172(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 176(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 180(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 184(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 188(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 192(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 196(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 200(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 204(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 208(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 212(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 216(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 220(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 238b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 616(%r6)
	add %r7, %r7, %r8
	stw %r7, 616(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 620(%r6)
	add %r7, %r7, %r8
	stw %r7, 620(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 624(%r6)
	add %r7, %r7, %r8
	stw %r7, 624(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 628(%r6)
	add %r7, %r7, %r8
	stw %r7, 628(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 632(%r6)
	add %r7, %r7, %r8
	stw %r7, 632(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 636(%r6)
	add %r7, %r7, %r8
	stw %r7, 636(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 640(%r6)
	add %r7, %r7, %r8
	stw %r7, 640(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 644(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 644(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 648(%r6)
	add %r7, %r7, %r8
	stw %r7, 648(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 652(%r6)
	add %r7, %r7, %r8
	stw %r7, 652(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 656(%r6)
	add %r7, %r7, %r8
	stw %r7, 656(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 660(%r6)
	add %r7, %r7, %r8
	stw %r7, 660(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 664(%r6)
	add %r7, %r7, %r8
	stw %r7, 664(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 668(%r6)
	add %r7, %r7, %r8
	stw %r7, 668(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
239:
	lwz %r4, 0(%r9)
	li %r8, 0
	lwz %r5, 224(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 228(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 232(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 236(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 240(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 244(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 248(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 252(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 256(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 260(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 264(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 268(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 272(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 276(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 239b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 672(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 676(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 680(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 684(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 688(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 692(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 696(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 700(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 704(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 708(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 712(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 716(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 720(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 724(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 672(%r6)
	add %r7, %r7, %r8
	stw %r7, 672(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 676(%r6)
	add %r7, %r7, %r8
	stw %r7, 676(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 680(%r6)
	add %r7, %r7, %r8
	stw %r7, 680(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 684(%r6)
	add %r7, %r7, %r8
	stw %r7, 684(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 688(%r6)
	add %r7, %r7, %r8
	stw %r7, 688(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 692(%r6)
	add %r7, %r7, %r8
	stw %r7, 692(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 696(%r6)
	add %r7, %r7, %r8
	stw %r7, 696(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 700(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 700(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 704(%r6)
	add %r7, %r7, %r8
	stw %r7, 704(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 708(%r6)
	add %r7, %r7, %r8
	stw %r7, 708(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 712(%r6)
	add %r7, %r7, %r8
	stw %r7, 712(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 716(%r6)
	add %r7, %r7, %r8
	stw %r7, 716(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 720(%r6)
	add %r7, %r7, %r8
	stw %r7, 720(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 724(%r6)
	add %r7, %r7, %r8
	stw %r7, 724(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 672(%r6)
	add %r7, %r7, %r8
	stw %r7, 672(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 676(%r6)
	add %r7, %r7, %r8
	stw %r7, 676(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 680(%r6)
	add %r7, %r7, %r8
	stw %r7, 680(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 684(%r6)
	add %r7, %r7, %r8
	stw %r7, 684(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 688(%r6)
	add %r7, %r7, %r8
	stw %r7, 688(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 692(%r6)
	add %r7, %r7, %r8
	stw %r7, 692(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 696(%r6)
	add %r7, %r7, %r8
	stw %r7, 696(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 700(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 700(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 704(%r6)
	add %r7, %r7, %r8
	stw %r7, 704(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 708(%r6)
	add %r7, %r7, %r8
	stw %r7, 708(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 712(%r6)
	add %r7, %r7, %r8
	stw %r7, 712(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 716(%r6)
	add %r7, %r7, %r8
	stw %r7, 716(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 720(%r6)
	add %r7, %r7, %r8
	stw %r7, 720(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 724(%r6)
	add %r7, %r7, %r8
	stw %r7, 724(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
240:
	lwz %r4, 336(%r9)
	li %r8, 0
	lwz %r5, 616(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 620(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 624(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 628(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 632(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 636(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 640(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 644(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 648(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 652(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 656(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 660(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 664(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 668(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 240b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
241:
	lwz %r4, 504(%r9)
	li %r8, 0
	lwz %r5, 672(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 676(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 680(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 684(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 688(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 692(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 696(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 700(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 704(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 708(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 712(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 716(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 720(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 724(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 241b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 34, 29
	lwz %r7, 448(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 504(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 508(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 512(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 516(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 520(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 524(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 528(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -8
	lwz %r5, 532(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 536(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 540(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 544(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 548(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 552(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 556(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 728(%r6)
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 732(%r6)
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 740(%r6)
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 744(%r6)
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 748(%r6)
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 752(%r6)
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 756(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 760(%r6)
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 764(%r6)
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 768(%r6)
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 772(%r6)
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 776(%r6)
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 780(%r6)
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 728(%r6)
	add %r7, %r7, %r8
	stw %r7, 728(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 732(%r6)
	add %r7, %r7, %r8
	stw %r7, 732(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 736(%r6)
	add %r7, %r7, %r8
	stw %r7, 736(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 740(%r6)
	add %r7, %r7, %r8
	stw %r7, 740(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 744(%r6)
	add %r7, %r7, %r8
	stw %r7, 744(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 748(%r6)
	add %r7, %r7, %r8
	stw %r7, 748(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 752(%r6)
	add %r7, %r7, %r8
	stw %r7, 752(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 756(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 756(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 760(%r6)
	add %r7, %r7, %r8
	stw %r7, 760(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 764(%r6)
	add %r7, %r7, %r8
	stw %r7, 764(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 768(%r6)
	add %r7, %r7, %r8
	stw %r7, 768(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 772(%r6)
	add %r7, %r7, %r8
	stw %r7, 772(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 776(%r6)
	add %r7, %r7, %r8
	stw %r7, 776(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 780(%r6)
	add %r7, %r7, %r8
	stw %r7, 780(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	lwz %r7, 448(%r6)
	lwz %r5, 504(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 784(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	lwz %r5, 508(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 788(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	lwz %r5, 512(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 792(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	lwz %r5, 516(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 796(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	lwz %r5, 520(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 800(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	lwz %r5, 524(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 804(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	lwz %r5, 528(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 808(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	lwz %r5, 532(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 812(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	lwz %r5, 536(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 816(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	lwz %r5, 540(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 820(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	lwz %r5, 544(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 824(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	lwz %r5, 548(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 828(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	lwz %r5, 552(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 832(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	lwz %r5, 556(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 836(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 784(%r6)
	add %r7, %r7, %r8
	stw %r7, 784(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 788(%r6)
	add %r7, %r7, %r8
	stw %r7, 788(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 792(%r6)
	add %r7, %r7, %r8
	stw %r7, 792(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 796(%r6)
	add %r7, %r7, %r8
	stw %r7, 796(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 800(%r6)
	add %r7, %r7, %r8
	stw %r7, 800(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 804(%r6)
	add %r7, %r7, %r8
	stw %r7, 804(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 808(%r6)
	add %r7, %r7, %r8
	stw %r7, 808(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 812(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 812(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 816(%r6)
	add %r7, %r7, %r8
	stw %r7, 816(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 820(%r6)
	add %r7, %r7, %r8
	stw %r7, 820(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 824(%r6)
	add %r7, %r7, %r8
	stw %r7, 824(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 828(%r6)
	add %r7, %r7, %r8
	stw %r7, 828(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 832(%r6)
	add %r7, %r7, %r8
	stw %r7, 832(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 836(%r6)
	add %r7, %r7, %r8
	stw %r7, 836(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 784(%r6)
	add %r7, %r7, %r8
	stw %r7, 784(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 788(%r6)
	add %r7, %r7, %r8
	stw %r7, 788(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 792(%r6)
	add %r7, %r7, %r8
	stw %r7, 792(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 796(%r6)
	add %r7, %r7, %r8
	stw %r7, 796(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 800(%r6)
	add %r7, %r7, %r8
	stw %r7, 800(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 804(%r6)
	add %r7, %r7, %r8
	stw %r7, 804(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 808(%r6)
	add %r7, %r7, %r8
	stw %r7, 808(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 812(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 812(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 816(%r6)
	add %r7, %r7, %r8
	stw %r7, 816(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 820(%r6)
	add %r7, %r7, %r8
	stw %r7, 820(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 824(%r6)
	add %r7, %r7, %r8
	stw %r7, 824(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 828(%r6)
	add %r7, %r7, %r8
	stw %r7, 828(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 832(%r6)
	add %r7, %r7, %r8
	stw %r7, 832(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 836(%r6)
	add %r7, %r7, %r8
	stw %r7, 836(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	lwz %r7, 56(%r6)
	lwz %r5, 0(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	lwz %r5, 4(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	lwz %r5, 8(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	lwz %r5, 12(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	lwz %r5, 16(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	lwz %r5, 20(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	lwz %r5, 24(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	lwz %r5, 28(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	lwz %r5, 32(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	lwz %r5, 36(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	lwz %r5, 40(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	lwz %r5, 44(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	lwz %r5, 48(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	lwz %r5, 52(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	lwz %r7, 168(%r6)
	lwz %r5, 224(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 172(%r6)
	lwz %r5, 228(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 176(%r6)
	lwz %r5, 232(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 180(%r6)
	lwz %r5, 236(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 184(%r6)
	lwz %r5, 240(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 188(%r6)
	lwz %r5, 244(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 192(%r6)
	lwz %r5, 248(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 196(%r6)
	lwz %r5, 252(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 200(%r6)
	lwz %r5, 256(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 204(%r6)
	lwz %r5, 260(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 208(%r6)
	lwz %r5, 264(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 212(%r6)
	lwz %r5, 268(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 216(%r6)
	lwz %r5, 272(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 220(%r6)
	lwz %r5, 276(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 392(%r6)
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 416(%r6)
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 392(%r6)
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 416(%r6)
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
242:
	lwz %r4, 840(%r9)
	li %r8, 0
	lwz %r5, 392(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 396(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 400(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 404(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 408(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 412(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 416(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 420(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 424(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 428(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 432(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 436(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 440(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 444(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 242b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
243:
	lwz %r4, 560(%r9)
	li %r8, 0
	lwz %r5, 728(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 732(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 736(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 740(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 744(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 748(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 752(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 756(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 760(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 764(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 768(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 772(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 776(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 780(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 243b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 392(%r6)
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 416(%r6)
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 392(%r6)
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 416(%r6)
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 34, 29
	lwz %r7, 840(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 616(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 620(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 624(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 628(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 632(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 636(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 640(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -8
	lwz %r5, 644(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 648(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 652(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 656(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 660(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 664(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 668(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 34, 29
	lwz %r7, 840(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 672(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 676(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 680(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 684(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 688(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 692(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 696(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -8
	lwz %r5, 700(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 704(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 708(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 712(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 716(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 720(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 724(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
244:
	lwz %r4, 392(%r9)
	li %r8, 0
	lwz %r5, 840(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 844(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 848(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 852(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 856(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 860(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 864(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 868(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 872(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 876(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 880(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 884(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 888(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 892(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 244b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 392(%r6)
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 416(%r6)
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 392(%r6)
	add %r7, %r7, %r8
	stw %r7, 392(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 396(%r6)
	add %r7, %r7, %r8
	stw %r7, 396(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 400(%r6)
	add %r7, %r7, %r8
	stw %r7, 400(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 404(%r6)
	add %r7, %r7, %r8
	stw %r7, 404(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 408(%r6)
	add %r7, %r7, %r8
	stw %r7, 408(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 412(%r6)
	add %r7, %r7, %r8
	stw %r7, 412(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 416(%r6)
	add %r7, %r7, %r8
	stw %r7, 416(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 420(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 420(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 424(%r6)
	add %r7, %r7, %r8
	stw %r7, 424(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 428(%r6)
	add %r7, %r7, %r8
	stw %r7, 428(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 432(%r6)
	add %r7, %r7, %r8
	stw %r7, 432(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 436(%r6)
	add %r7, %r7, %r8
	stw %r7, 436(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 440(%r6)
	add %r7, %r7, %r8
	stw %r7, 440(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 444(%r6)
	add %r7, %r7, %r8
	stw %r7, 444(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
245:
	lwz %r4, 560(%r9)
	li %r8, 0
	lwz %r5, 784(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 788(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 792(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 796(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 800(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 804(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 808(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 812(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 816(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 820(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 824(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 828(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 832(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 836(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 245b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 34, 29
	lwz %r7, 672(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 616(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 676(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 620(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 680(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 624(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 684(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 628(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 688(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 632(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 692(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 636(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 696(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 640(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 700(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -8
	lwz %r5, 644(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 704(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 648(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 708(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 652(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 712(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 656(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 716(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 660(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 720(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 664(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 724(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 668(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 840(%r6)
	add %r7, %r7, %r8
	stw %r7, 840(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 844(%r6)
	add %r7, %r7, %r8
	stw %r7, 844(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 848(%r6)
	add %r7, %r7, %r8
	stw %r7, 848(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 852(%r6)
	add %r7, %r7, %r8
	stw %r7, 852(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 856(%r6)
	add %r7, %r7, %r8
	stw %r7, 856(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 860(%r6)
	add %r7, %r7, %r8
	stw %r7, 860(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 864(%r6)
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
246:
	lwz %r4, 448(%r9)
	li %r8, 0
	lwz %r5, 840(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 844(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 848(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 852(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 856(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 860(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 864(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 868(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 872(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 876(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 880(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 884(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 888(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 892(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 246b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 448(%r6)
	add %r7, %r7, %r8
	stw %r7, 448(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 452(%r6)
	add %r7, %r7, %r8
	stw %r7, 452(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 456(%r6)
	add %r7, %r7, %r8
	stw %r7, 456(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 460(%r6)
	add %r7, %r7, %r8
	stw %r7, 460(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 464(%r6)
	add %r7, %r7, %r8
	stw %r7, 464(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 468(%r6)
	add %r7, %r7, %r8
	stw %r7, 468(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 472(%r6)
	add %r7, %r7, %r8
	stw %r7, 472(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 476(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 476(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 480(%r6)
	add %r7, %r7, %r8
	stw %r7, 480(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 484(%r6)
	add %r7, %r7, %r8
	stw %r7, 484(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 488(%r6)
	add %r7, %r7, %r8
	stw %r7, 488(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 492(%r6)
	add %r7, %r7, %r8
	stw %r7, 492(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 496(%r6)
	add %r7, %r7, %r8
	stw %r7, 496(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 500(%r6)
	add %r7, %r7, %r8
	stw %r7, 500(%r6)
	rldicl %r8, %r7, 32, 32
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 14
247:
	lwz %r4, 728(%r9)
	li %r8, 0
	lwz %r5, 784(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 952(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 952(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 788(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 956(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 956(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 792(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 960(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 960(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 796(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 964(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 964(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 800(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 968(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 968(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 804(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 972(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 972(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 808(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 976(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 976(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 812(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 980(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 980(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 816(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 984(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 984(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 820(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 988(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 988(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 824(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 992(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 992(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 828(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 996(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 996(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 832(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1000(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1000(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 836(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 1004(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 1004(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 1008(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 247b
	li %r8, 0
	lwz %r7, 952(%r6)
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 956(%r6)
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 960(%r6)
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 964(%r6)
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 968(%r6)
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 972(%r6)
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 976(%r6)
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 980(%r6)
	lwz %r5, 1036(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1008(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 984(%r6)
	lwz %r5, 1040(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1012(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 988(%r6)
	lwz %r5, 1044(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1016(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 992(%r6)
	lwz %r5, 1048(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1020(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 996(%r6)
	lwz %r5, 1052(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1024(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1000(%r6)
	lwz %r5, 1056(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1028(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 1004(%r6)
	lwz %r5, 1060(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r5
	lwz %r5, 1032(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 504(%r6)
	add %r7, %r7, %r8
	stw %r7, 504(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 508(%r6)
	add %r7, %r7, %r8
	stw %r7, 508(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 512(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 516(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 520(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 524(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 528(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 532(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 536(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 544(%r6)
	add %r7, %r7, %r8
	stw %r7, 544(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 548(%r6)
	add %r7, %r7, %r8
	stw %r7, 548(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 552(%r6)
	add %r7, %r7, %r8
	stw %r7, 552(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 556(%r6)
	add %r7, %r7, %r8
	stw %r7, 556(%r6)
	rldicl %r8, %r7, 32, 32
	add %r4, %r6, %r12
	lbz %r4, 1064(%r4)
	li %r11, 0
	subf %r11, %r4, %r11
	lwz %r5, 56(%r6)
	lwz %r7, 392(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 56(%r6)
	stw %r7, 392(%r6)
	lwz %r5, 60(%r6)
	lwz %r7, 396(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 60(%r6)
	stw %r7, 396(%r6)
	lwz %r5, 64(%r6)
	lwz %r7, 400(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 64(%r6)
	stw %r7, 400(%r6)
	lwz %r5, 68(%r6)
	lwz %r7, 404(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 68(%r6)
	stw %r7, 404(%r6)
	lwz %r5, 72(%r6)
	lwz %r7, 408(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 72(%r6)
	stw %r7, 408(%r6)
	lwz %r5, 76(%r6)
	lwz %r7, 412(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 76(%r6)
	stw %r7, 412(%r6)
	lwz %r5, 80(%r6)
	lwz %r7, 416(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 80(%r6)
	stw %r7, 416(%r6)
	lwz %r5, 84(%r6)
	lwz %r7, 420(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 84(%r6)
	stw %r7, 420(%r6)
	lwz %r5, 88(%r6)
	lwz %r7, 424(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 88(%r6)
	stw %r7, 424(%r6)
	lwz %r5, 92(%r6)
	lwz %r7, 428(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 92(%r6)
	stw %r7, 428(%r6)
	lwz %r5, 96(%r6)
	lwz %r7, 432(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 96(%r6)
	stw %r7, 432(%r6)
	lwz %r5, 100(%r6)
	lwz %r7, 436(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 100(%r6)
	stw %r7, 436(%r6)
	lwz %r5, 104(%r6)
	lwz %r7, 440(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 104(%r6)
	stw %r7, 440(%r6)
	lwz %r5, 108(%r6)
	lwz %r7, 444(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 108(%r6)
	stw %r7, 444(%r6)
	lwz %r5, 0(%r6)
	lwz %r7, 448(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 0(%r6)
	stw %r7, 448(%r6)
	lwz %r5, 4(%r6)
	lwz %r7, 452(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 4(%r6)
	stw %r7, 452(%r6)
	lwz %r5, 8(%r6)
	lwz %r7, 456(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 8(%r6)
	stw %r7, 456(%r6)
	lwz %r5, 12(%r6)
	lwz %r7, 460(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 12(%r6)
	stw %r7, 460(%r6)
	lwz %r5, 16(%r6)
	lwz %r7, 464(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 16(%r6)
	stw %r7, 464(%r6)
	lwz %r5, 20(%r6)
	lwz %r7, 468(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 20(%r6)
	stw %r7, 468(%r6)
	lwz %r5, 24(%r6)
	lwz %r7, 472(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 24(%r6)
	stw %r7, 472(%r6)
	lwz %r5, 28(%r6)
	lwz %r7, 476(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 28(%r6)
	stw %r7, 476(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 480(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 32(%r6)
	stw %r7, 480(%r6)
	lwz %r5, 36(%r6)
	lwz %r7, 484(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 36(%r6)
	stw %r7, 484(%r6)
	lwz %r5, 40(%r6)
	lwz %r7, 488(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 40(%r6)
	stw %r7, 488(%r6)
	lwz %r5, 44(%r6)
	lwz %r7, 492(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 44(%r6)
	stw %r7, 492(%r6)
	lwz %r5, 48(%r6)
	lwz %r7, 496(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 48(%r6)
	stw %r7, 496(%r6)
	lwz %r5, 52(%r6)
	lwz %r7, 500(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 52(%r6)
	stw %r7, 500(%r6)
	lwz %r5, 112(%r6)
	lwz %r7, 504(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 504(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 508(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 508(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 512(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 512(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 516(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 516(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 520(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 520(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 524(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 524(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 528(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 528(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 532(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 532(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 536(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 536(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 540(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 540(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 544(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 544(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 548(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 548(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 552(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 552(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 556(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 556(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 235b
	li %r8, 1
	li %r10, 1
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 896(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 900(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 904(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 908(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 912(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 916(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 920(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 924(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 928(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 932(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 936(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 940(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 944(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 948(%r6)
	rldicl %r8, %r7, 32, 32
	li %r4, 0
	subf %r11, %r8, %r4
	lwz %r5, 56(%r6)
	lwz %r7, 896(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 0(%r3)
	lwz %r5, 60(%r6)
	lwz %r7, 900(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 4(%r3)
	lwz %r5, 64(%r6)
	lwz %r7, 904(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 8(%r3)
	lwz %r5, 68(%r6)
	lwz %r7, 908(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 12(%r3)
	lwz %r5, 72(%r6)
	lwz %r7, 912(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 16(%r3)
	lwz %r5, 76(%r6)
	lwz %r7, 916(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 20(%r3)
	lwz %r5, 80(%r6)
	lwz %r7, 920(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 24(%r3)
	lwz %r5, 84(%r6)
	lwz %r7, 924(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 28(%r3)
	lwz %r5, 88(%r6)
	lwz %r7, 928(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 32(%r3)
	lwz %r5, 92(%r6)
	lwz %r7, 932(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 36(%r3)
	lwz %r5, 96(%r6)
	lwz %r7, 936(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 40(%r3)
	lwz %r5, 100(%r6)
	lwz %r7, 940(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 44(%r3)
	lwz %r5, 104(%r6)
	lwz %r7, 944(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 48(%r3)
	lwz %r5, 108(%r6)
	lwz %r7, 948(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 52(%r3)
	li %r10, 0
	lwz %r7, 0(%r3)
	or %r10, %r10, %r7
	lwz %r7, 4(%r3)
	or %r10, %r10, %r7
	lwz %r7, 8(%r3)
	or %r10, %r10, %r7
	lwz %r7, 12(%r3)
	or %r10, %r10, %r7
	lwz %r7, 16(%r3)
	or %r10, %r10, %r7
	lwz %r7, 20(%r3)
	or %r10, %r10, %r7
	lwz %r7, 24(%r3)
	or %r10, %r10, %r7
	lwz %r7, 28(%r3)
	or %r10, %r10, %r7
	lwz %r7, 32(%r3)
	or %r10, %r10, %r7
	lwz %r7, 36(%r3)
	or %r10, %r10, %r7
	lwz %r7, 40(%r3)
	or %r10, %r10, %r7
	lwz %r7, 44(%r3)
	or %r10, %r10, %r7
	lwz %r7, 48(%r3)
	or %r10, %r10, %r7
	lwz %r7, 52(%r3)
	or %r10, %r10, %r7
	ld %r9, 3520(%r6)
	or %r9, %r9, %r10
	std %r9, 3520(%r6)
	li %r8, 0
	li %r4, 1
	rldicr %r4, %r4, 34, 29
	lwz %r7, 0(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 112(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 4(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 116(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 8(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 120(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 12(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 124(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 16(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 128(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 20(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 132(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 24(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 136(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 28(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -8
	lwz %r5, 140(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 32(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 144(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 148(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 152(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 156(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 160(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r4
	addi %r7, %r7, -4
	lwz %r5, 164(%r6)
	subf %r7, %r5, %r7
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r10, %r8, 0
	lwz %r7, 560(%r6)
	add %r7, %r7, %r8
	stw %r7, 560(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 564(%r6)
	add %r7, %r7, %r8
	stw %r7, 564(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 568(%r6)
	add %r7, %r7, %r8
	stw %r7, 568(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 572(%r6)
	add %r7, %r7, %r8
	stw %r7, 572(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 576(%r6)
	add %r7, %r7, %r8
	stw %r7, 576(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 580(%r6)
	add %r7, %r7, %r8
	stw %r7, 580(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 584(%r6)
	add %r7, %r7, %r8
	stw %r7, 584(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 588(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 588(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 592(%r6)
	add %r7, %r7, %r8
	stw %r7, 592(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 596(%r6)
	add %r7, %r7, %r8
	stw %r7, 596(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 600(%r6)
	add %r7, %r7, %r8
	stw %r7, 600(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 604(%r6)
	add %r7, %r7, %r8
	stw %r7, 604(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 608(%r6)
	add %r7, %r7, %r8
	stw %r7, 608(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 612(%r6)
	add %r7, %r7, %r8
	stw %r7, 612(%r6)
	rldicl %r8, %r7, 32, 32
	li %r11, 0
	lwz %r5, 560(%r6)
	lwz %r7, 560(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 56(%r6)
	lwz %r5, 564(%r6)
	lwz %r7, 564(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 60(%r6)
	lwz %r5, 568(%r6)
	lwz %r7, 568(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 64(%r6)
	lwz %r5, 572(%r6)
	lwz %r7, 572(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 68(%r6)
	lwz %r5, 576(%r6)
	lwz %r7, 576(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 72(%r6)
	lwz %r5, 580(%r6)
	lwz %r7, 580(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 76(%r6)
	lwz %r5, 584(%r6)
	lwz %r7, 584(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 80(%r6)
	lwz %r5, 588(%r6)
	lwz %r7, 588(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 84(%r6)
	lwz %r5, 592(%r6)
	lwz %r7, 592(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 88(%r6)
	lwz %r5, 596(%r6)
	lwz %r7, 596(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 92(%r6)
	lwz %r5, 600(%r6)
	lwz %r7, 600(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 96(%r6)
	lwz %r5, 604(%r6)
	lwz %r7, 604(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 100(%r6)
	lwz %r5, 608(%r6)
	lwz %r7, 608(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 104(%r6)
	lwz %r5, 612(%r6)
	lwz %r7, 612(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 108(%r6)
	li %r8, 1
	li %r10, 1
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 896(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 900(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 904(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 908(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 912(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 916(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 920(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 924(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 928(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 932(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 936(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 940(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 944(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 948(%r6)
	rldicl %r8, %r7, 32, 32
	li %r4, 0
	subf %r11, %r8, %r4
	lwz %r5, 56(%r6)
	lwz %r7, 896(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 0(%r3)
	lwz %r5, 60(%r6)
	lwz %r7, 900(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 4(%r3)
	lwz %r5, 64(%r6)
	lwz %r7, 904(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 8(%r3)
	lwz %r5, 68(%r6)
	lwz %r7, 908(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 12(%r3)
	lwz %r5, 72(%r6)
	lwz %r7, 912(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 16(%r3)
	lwz %r5, 76(%r6)
	lwz %r7, 916(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 20(%r3)
	lwz %r5, 80(%r6)
	lwz %r7, 920(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 24(%r3)
	lwz %r5, 84(%r6)
	lwz %r7, 924(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 28(%r3)
	lwz %r5, 88(%r6)
	lwz %r7, 928(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 32(%r3)
	lwz %r5, 92(%r6)
	lwz %r7, 932(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 36(%r3)
	lwz %r5, 96(%r6)
	lwz %r7, 936(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 40(%r3)
	lwz %r5, 100(%r6)
	lwz %r7, 940(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 44(%r3)
	lwz %r5, 104(%r6)
	lwz %r7, 944(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 48(%r3)
	lwz %r5, 108(%r6)
	lwz %r7, 948(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 52(%r3)
	li %r10, 0
	lwz %r7, 0(%r3)
	or %r10, %r10, %r7
	lwz %r7, 4(%r3)
	or %r10, %r10, %r7
	lwz %r7, 8(%r3)
	or %r10, %r10, %r7
	lwz %r7, 12(%r3)
	or %r10, %r10, %r7
	lwz %r7, 16(%r3)
	or %r10, %r10, %r7
	lwz %r7, 20(%r3)
	or %r10, %r10, %r7
	lwz %r7, 24(%r3)
	or %r10, %r10, %r7
	lwz %r7, 28(%r3)
	or %r10, %r10, %r7
	lwz %r7, 32(%r3)
	or %r10, %r10, %r7
	lwz %r7, 36(%r3)
	or %r10, %r10, %r7
	lwz %r7, 40(%r3)
	or %r10, %r10, %r7
	lwz %r7, 44(%r3)
	or %r10, %r10, %r7
	lwz %r7, 48(%r3)
	or %r10, %r10, %r7
	lwz %r7, 52(%r3)
	or %r10, %r10, %r7
	ld %r9, 3520(%r6)
	or %r9, %r9, %r10
	std %r9, 3520(%r6)
	ld %r9, 3520(%r6)
	li %r8, 0
	subf %r8, %r9, %r8
	or %r9, %r9, %r8
	rldicl %r9, %r9, 1, 63
	li %r3, 1
	subf %r3, %r9, %r3
	blr
