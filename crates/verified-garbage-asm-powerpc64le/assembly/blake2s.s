// The functions of `src/blake2s.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2s_compress:
	std %r14, 0(%r8)
	std %r15, 8(%r8)
	std %r16, 16(%r8)
	std %r17, 24(%r8)
	std %r18, 32(%r8)
	std %r19, 40(%r8)
	std %r20, 48(%r8)
	std %r21, 56(%r8)
	std %r22, 64(%r8)
	std %r23, 72(%r8)
	std %r6, 80(%r8)
	li %r0, 0
	std %r0, 88(%r8)
	rlwinm %r7, %r7, 0, 0, 31
	subf %r6, %r7, %r0
	or %r7, %r7, %r6
	rldicl %r7, %r7, 1, 63
	subf %r7, %r7, %r0
	std %r7, 96(%r8)
	cmpldi %cr0, %r5, 0
	beq %cr0, 20f
22:
	lwz %r6, 0(%r3)
	lwz %r7, 4(%r3)
	lwz %r9, 8(%r3)
	lwz %r10, 12(%r3)
	lwz %r11, 16(%r3)
	lwz %r12, 20(%r3)
	lwz %r14, 24(%r3)
	lwz %r15, 28(%r3)
	lis %r16, 27145
	ori %r16, %r16, 58983
	lis %r17, -17561
	ori %r17, %r17, 44677
	lis %r18, 15470
	ori %r18, %r18, 62322
	lis %r19, -23217
	ori %r19, %r19, 62778
	lis %r20, 20750
	ori %r20, %r20, 21119
	lis %r21, -25851
	ori %r21, %r21, 26764
	lis %r22, 8067
	ori %r22, %r22, 55723
	lis %r23, 23520
	ori %r23, %r23, 52505
	ld %r0, 80(%r8)
	xor %r20, %r20, %r0
	ld %r0, 80(%r8)
	rldicl %r0, %r0, 32, 32
	xor %r21, %r21, %r0
	ld %r0, 96(%r8)
	xor %r22, %r22, %r0
	lwz %r0, 0(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rlwinm %r20, %r20, 16, 0, 31
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rlwinm %r11, %r11, 20, 0, 31
	lwz %r0, 4(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rlwinm %r20, %r20, 24, 0, 31
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rlwinm %r11, %r11, 25, 0, 31
	lwz %r0, 8(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rlwinm %r21, %r21, 16, 0, 31
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rlwinm %r12, %r12, 20, 0, 31
	lwz %r0, 12(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rlwinm %r21, %r21, 24, 0, 31
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rlwinm %r12, %r12, 25, 0, 31
	lwz %r0, 16(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rlwinm %r22, %r22, 16, 0, 31
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rlwinm %r14, %r14, 20, 0, 31
	lwz %r0, 20(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rlwinm %r22, %r22, 24, 0, 31
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rlwinm %r14, %r14, 25, 0, 31
	lwz %r0, 24(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rlwinm %r23, %r23, 16, 0, 31
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rlwinm %r15, %r15, 20, 0, 31
	lwz %r0, 28(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rlwinm %r23, %r23, 24, 0, 31
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rlwinm %r15, %r15, 25, 0, 31
	lwz %r0, 32(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rlwinm %r23, %r23, 16, 0, 31
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rlwinm %r12, %r12, 20, 0, 31
	lwz %r0, 36(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rlwinm %r23, %r23, 24, 0, 31
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rlwinm %r12, %r12, 25, 0, 31
	lwz %r0, 40(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rlwinm %r20, %r20, 16, 0, 31
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rlwinm %r14, %r14, 20, 0, 31
	lwz %r0, 44(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rlwinm %r20, %r20, 24, 0, 31
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rlwinm %r14, %r14, 25, 0, 31
	lwz %r0, 48(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rlwinm %r21, %r21, 16, 0, 31
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rlwinm %r15, %r15, 20, 0, 31
	lwz %r0, 52(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rlwinm %r21, %r21, 24, 0, 31
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rlwinm %r15, %r15, 25, 0, 31
	lwz %r0, 56(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rlwinm %r22, %r22, 16, 0, 31
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rlwinm %r11, %r11, 20, 0, 31
	lwz %r0, 60(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rlwinm %r22, %r22, 24, 0, 31
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rlwinm %r11, %r11, 25, 0, 31
	lwz %r0, 56(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rlwinm %r20, %r20, 16, 0, 31
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rlwinm %r11, %r11, 20, 0, 31
	lwz %r0, 40(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rlwinm %r20, %r20, 24, 0, 31
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rlwinm %r11, %r11, 25, 0, 31
	lwz %r0, 16(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rlwinm %r21, %r21, 16, 0, 31
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rlwinm %r12, %r12, 20, 0, 31
	lwz %r0, 32(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rlwinm %r21, %r21, 24, 0, 31
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rlwinm %r12, %r12, 25, 0, 31
	lwz %r0, 36(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rlwinm %r22, %r22, 16, 0, 31
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rlwinm %r14, %r14, 20, 0, 31
	lwz %r0, 60(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rlwinm %r22, %r22, 24, 0, 31
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rlwinm %r14, %r14, 25, 0, 31
	lwz %r0, 52(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rlwinm %r23, %r23, 16, 0, 31
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rlwinm %r15, %r15, 20, 0, 31
	lwz %r0, 24(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rlwinm %r23, %r23, 24, 0, 31
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rlwinm %r15, %r15, 25, 0, 31
	lwz %r0, 4(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rlwinm %r23, %r23, 16, 0, 31
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rlwinm %r12, %r12, 20, 0, 31
	lwz %r0, 48(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rlwinm %r23, %r23, 24, 0, 31
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rlwinm %r12, %r12, 25, 0, 31
	lwz %r0, 0(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rlwinm %r20, %r20, 16, 0, 31
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rlwinm %r14, %r14, 20, 0, 31
	lwz %r0, 8(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rlwinm %r20, %r20, 24, 0, 31
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rlwinm %r14, %r14, 25, 0, 31
	lwz %r0, 44(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rlwinm %r21, %r21, 16, 0, 31
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rlwinm %r15, %r15, 20, 0, 31
	lwz %r0, 28(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rlwinm %r21, %r21, 24, 0, 31
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rlwinm %r15, %r15, 25, 0, 31
	lwz %r0, 20(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rlwinm %r22, %r22, 16, 0, 31
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rlwinm %r11, %r11, 20, 0, 31
	lwz %r0, 12(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rlwinm %r22, %r22, 24, 0, 31
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rlwinm %r11, %r11, 25, 0, 31
	lwz %r0, 44(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rlwinm %r20, %r20, 16, 0, 31
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rlwinm %r11, %r11, 20, 0, 31
	lwz %r0, 32(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rlwinm %r20, %r20, 24, 0, 31
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rlwinm %r11, %r11, 25, 0, 31
	lwz %r0, 48(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rlwinm %r21, %r21, 16, 0, 31
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rlwinm %r12, %r12, 20, 0, 31
	lwz %r0, 0(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rlwinm %r21, %r21, 24, 0, 31
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rlwinm %r12, %r12, 25, 0, 31
	lwz %r0, 20(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rlwinm %r22, %r22, 16, 0, 31
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rlwinm %r14, %r14, 20, 0, 31
	lwz %r0, 8(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rlwinm %r22, %r22, 24, 0, 31
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rlwinm %r14, %r14, 25, 0, 31
	lwz %r0, 60(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rlwinm %r23, %r23, 16, 0, 31
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rlwinm %r15, %r15, 20, 0, 31
	lwz %r0, 52(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rlwinm %r23, %r23, 24, 0, 31
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rlwinm %r15, %r15, 25, 0, 31
	lwz %r0, 40(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rlwinm %r23, %r23, 16, 0, 31
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rlwinm %r12, %r12, 20, 0, 31
	lwz %r0, 56(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rlwinm %r23, %r23, 24, 0, 31
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rlwinm %r12, %r12, 25, 0, 31
	lwz %r0, 12(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rlwinm %r20, %r20, 16, 0, 31
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rlwinm %r14, %r14, 20, 0, 31
	lwz %r0, 24(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rlwinm %r20, %r20, 24, 0, 31
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rlwinm %r14, %r14, 25, 0, 31
	lwz %r0, 28(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rlwinm %r21, %r21, 16, 0, 31
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rlwinm %r15, %r15, 20, 0, 31
	lwz %r0, 4(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rlwinm %r21, %r21, 24, 0, 31
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rlwinm %r15, %r15, 25, 0, 31
	lwz %r0, 36(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rlwinm %r22, %r22, 16, 0, 31
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rlwinm %r11, %r11, 20, 0, 31
	lwz %r0, 16(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rlwinm %r22, %r22, 24, 0, 31
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rlwinm %r11, %r11, 25, 0, 31
	lwz %r0, 28(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rlwinm %r20, %r20, 16, 0, 31
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rlwinm %r11, %r11, 20, 0, 31
	lwz %r0, 36(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rlwinm %r20, %r20, 24, 0, 31
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rlwinm %r11, %r11, 25, 0, 31
	lwz %r0, 12(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rlwinm %r21, %r21, 16, 0, 31
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rlwinm %r12, %r12, 20, 0, 31
	lwz %r0, 4(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rlwinm %r21, %r21, 24, 0, 31
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rlwinm %r12, %r12, 25, 0, 31
	lwz %r0, 52(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rlwinm %r22, %r22, 16, 0, 31
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rlwinm %r14, %r14, 20, 0, 31
	lwz %r0, 48(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rlwinm %r22, %r22, 24, 0, 31
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rlwinm %r14, %r14, 25, 0, 31
	lwz %r0, 44(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rlwinm %r23, %r23, 16, 0, 31
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rlwinm %r15, %r15, 20, 0, 31
	lwz %r0, 56(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rlwinm %r23, %r23, 24, 0, 31
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rlwinm %r15, %r15, 25, 0, 31
	lwz %r0, 8(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rlwinm %r23, %r23, 16, 0, 31
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rlwinm %r12, %r12, 20, 0, 31
	lwz %r0, 24(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rlwinm %r23, %r23, 24, 0, 31
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rlwinm %r12, %r12, 25, 0, 31
	lwz %r0, 20(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rlwinm %r20, %r20, 16, 0, 31
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rlwinm %r14, %r14, 20, 0, 31
	lwz %r0, 40(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rlwinm %r20, %r20, 24, 0, 31
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rlwinm %r14, %r14, 25, 0, 31
	lwz %r0, 16(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rlwinm %r21, %r21, 16, 0, 31
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rlwinm %r15, %r15, 20, 0, 31
	lwz %r0, 0(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rlwinm %r21, %r21, 24, 0, 31
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rlwinm %r15, %r15, 25, 0, 31
	lwz %r0, 60(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rlwinm %r22, %r22, 16, 0, 31
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rlwinm %r11, %r11, 20, 0, 31
	lwz %r0, 32(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rlwinm %r22, %r22, 24, 0, 31
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rlwinm %r11, %r11, 25, 0, 31
	lwz %r0, 36(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rlwinm %r20, %r20, 16, 0, 31
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rlwinm %r11, %r11, 20, 0, 31
	lwz %r0, 0(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rlwinm %r20, %r20, 24, 0, 31
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rlwinm %r11, %r11, 25, 0, 31
	lwz %r0, 20(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rlwinm %r21, %r21, 16, 0, 31
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rlwinm %r12, %r12, 20, 0, 31
	lwz %r0, 28(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rlwinm %r21, %r21, 24, 0, 31
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rlwinm %r12, %r12, 25, 0, 31
	lwz %r0, 8(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rlwinm %r22, %r22, 16, 0, 31
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rlwinm %r14, %r14, 20, 0, 31
	lwz %r0, 16(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rlwinm %r22, %r22, 24, 0, 31
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rlwinm %r14, %r14, 25, 0, 31
	lwz %r0, 40(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rlwinm %r23, %r23, 16, 0, 31
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rlwinm %r15, %r15, 20, 0, 31
	lwz %r0, 60(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rlwinm %r23, %r23, 24, 0, 31
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rlwinm %r15, %r15, 25, 0, 31
	lwz %r0, 56(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rlwinm %r23, %r23, 16, 0, 31
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rlwinm %r12, %r12, 20, 0, 31
	lwz %r0, 4(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rlwinm %r23, %r23, 24, 0, 31
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rlwinm %r12, %r12, 25, 0, 31
	lwz %r0, 44(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rlwinm %r20, %r20, 16, 0, 31
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rlwinm %r14, %r14, 20, 0, 31
	lwz %r0, 48(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rlwinm %r20, %r20, 24, 0, 31
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rlwinm %r14, %r14, 25, 0, 31
	lwz %r0, 24(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rlwinm %r21, %r21, 16, 0, 31
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rlwinm %r15, %r15, 20, 0, 31
	lwz %r0, 32(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rlwinm %r21, %r21, 24, 0, 31
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rlwinm %r15, %r15, 25, 0, 31
	lwz %r0, 12(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rlwinm %r22, %r22, 16, 0, 31
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rlwinm %r11, %r11, 20, 0, 31
	lwz %r0, 52(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rlwinm %r22, %r22, 24, 0, 31
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rlwinm %r11, %r11, 25, 0, 31
	lwz %r0, 8(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rlwinm %r20, %r20, 16, 0, 31
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rlwinm %r11, %r11, 20, 0, 31
	lwz %r0, 48(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rlwinm %r20, %r20, 24, 0, 31
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rlwinm %r11, %r11, 25, 0, 31
	lwz %r0, 24(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rlwinm %r21, %r21, 16, 0, 31
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rlwinm %r12, %r12, 20, 0, 31
	lwz %r0, 40(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rlwinm %r21, %r21, 24, 0, 31
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rlwinm %r12, %r12, 25, 0, 31
	lwz %r0, 0(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rlwinm %r22, %r22, 16, 0, 31
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rlwinm %r14, %r14, 20, 0, 31
	lwz %r0, 44(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rlwinm %r22, %r22, 24, 0, 31
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rlwinm %r14, %r14, 25, 0, 31
	lwz %r0, 32(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rlwinm %r23, %r23, 16, 0, 31
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rlwinm %r15, %r15, 20, 0, 31
	lwz %r0, 12(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rlwinm %r23, %r23, 24, 0, 31
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rlwinm %r15, %r15, 25, 0, 31
	lwz %r0, 16(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rlwinm %r23, %r23, 16, 0, 31
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rlwinm %r12, %r12, 20, 0, 31
	lwz %r0, 52(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rlwinm %r23, %r23, 24, 0, 31
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rlwinm %r12, %r12, 25, 0, 31
	lwz %r0, 28(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rlwinm %r20, %r20, 16, 0, 31
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rlwinm %r14, %r14, 20, 0, 31
	lwz %r0, 20(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rlwinm %r20, %r20, 24, 0, 31
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rlwinm %r14, %r14, 25, 0, 31
	lwz %r0, 60(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rlwinm %r21, %r21, 16, 0, 31
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rlwinm %r15, %r15, 20, 0, 31
	lwz %r0, 56(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rlwinm %r21, %r21, 24, 0, 31
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rlwinm %r15, %r15, 25, 0, 31
	lwz %r0, 4(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rlwinm %r22, %r22, 16, 0, 31
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rlwinm %r11, %r11, 20, 0, 31
	lwz %r0, 36(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rlwinm %r22, %r22, 24, 0, 31
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rlwinm %r11, %r11, 25, 0, 31
	lwz %r0, 48(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rlwinm %r20, %r20, 16, 0, 31
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rlwinm %r11, %r11, 20, 0, 31
	lwz %r0, 20(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rlwinm %r20, %r20, 24, 0, 31
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rlwinm %r11, %r11, 25, 0, 31
	lwz %r0, 4(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rlwinm %r21, %r21, 16, 0, 31
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rlwinm %r12, %r12, 20, 0, 31
	lwz %r0, 60(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rlwinm %r21, %r21, 24, 0, 31
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rlwinm %r12, %r12, 25, 0, 31
	lwz %r0, 56(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rlwinm %r22, %r22, 16, 0, 31
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rlwinm %r14, %r14, 20, 0, 31
	lwz %r0, 52(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rlwinm %r22, %r22, 24, 0, 31
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rlwinm %r14, %r14, 25, 0, 31
	lwz %r0, 16(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rlwinm %r23, %r23, 16, 0, 31
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rlwinm %r15, %r15, 20, 0, 31
	lwz %r0, 40(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rlwinm %r23, %r23, 24, 0, 31
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rlwinm %r15, %r15, 25, 0, 31
	lwz %r0, 0(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rlwinm %r23, %r23, 16, 0, 31
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rlwinm %r12, %r12, 20, 0, 31
	lwz %r0, 28(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rlwinm %r23, %r23, 24, 0, 31
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rlwinm %r12, %r12, 25, 0, 31
	lwz %r0, 24(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rlwinm %r20, %r20, 16, 0, 31
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rlwinm %r14, %r14, 20, 0, 31
	lwz %r0, 12(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rlwinm %r20, %r20, 24, 0, 31
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rlwinm %r14, %r14, 25, 0, 31
	lwz %r0, 36(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rlwinm %r21, %r21, 16, 0, 31
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rlwinm %r15, %r15, 20, 0, 31
	lwz %r0, 8(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rlwinm %r21, %r21, 24, 0, 31
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rlwinm %r15, %r15, 25, 0, 31
	lwz %r0, 32(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rlwinm %r22, %r22, 16, 0, 31
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rlwinm %r11, %r11, 20, 0, 31
	lwz %r0, 44(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rlwinm %r22, %r22, 24, 0, 31
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rlwinm %r11, %r11, 25, 0, 31
	lwz %r0, 52(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rlwinm %r20, %r20, 16, 0, 31
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rlwinm %r11, %r11, 20, 0, 31
	lwz %r0, 44(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rlwinm %r20, %r20, 24, 0, 31
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rlwinm %r11, %r11, 25, 0, 31
	lwz %r0, 28(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rlwinm %r21, %r21, 16, 0, 31
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rlwinm %r12, %r12, 20, 0, 31
	lwz %r0, 56(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rlwinm %r21, %r21, 24, 0, 31
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rlwinm %r12, %r12, 25, 0, 31
	lwz %r0, 48(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rlwinm %r22, %r22, 16, 0, 31
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rlwinm %r14, %r14, 20, 0, 31
	lwz %r0, 4(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rlwinm %r22, %r22, 24, 0, 31
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rlwinm %r14, %r14, 25, 0, 31
	lwz %r0, 12(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rlwinm %r23, %r23, 16, 0, 31
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rlwinm %r15, %r15, 20, 0, 31
	lwz %r0, 36(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rlwinm %r23, %r23, 24, 0, 31
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rlwinm %r15, %r15, 25, 0, 31
	lwz %r0, 20(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rlwinm %r23, %r23, 16, 0, 31
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rlwinm %r12, %r12, 20, 0, 31
	lwz %r0, 0(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rlwinm %r23, %r23, 24, 0, 31
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rlwinm %r12, %r12, 25, 0, 31
	lwz %r0, 60(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rlwinm %r20, %r20, 16, 0, 31
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rlwinm %r14, %r14, 20, 0, 31
	lwz %r0, 16(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rlwinm %r20, %r20, 24, 0, 31
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rlwinm %r14, %r14, 25, 0, 31
	lwz %r0, 32(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rlwinm %r21, %r21, 16, 0, 31
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rlwinm %r15, %r15, 20, 0, 31
	lwz %r0, 24(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rlwinm %r21, %r21, 24, 0, 31
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rlwinm %r15, %r15, 25, 0, 31
	lwz %r0, 8(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rlwinm %r22, %r22, 16, 0, 31
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rlwinm %r11, %r11, 20, 0, 31
	lwz %r0, 40(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rlwinm %r22, %r22, 24, 0, 31
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rlwinm %r11, %r11, 25, 0, 31
	lwz %r0, 24(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rlwinm %r20, %r20, 16, 0, 31
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rlwinm %r11, %r11, 20, 0, 31
	lwz %r0, 60(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rlwinm %r20, %r20, 24, 0, 31
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rlwinm %r11, %r11, 25, 0, 31
	lwz %r0, 56(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rlwinm %r21, %r21, 16, 0, 31
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rlwinm %r12, %r12, 20, 0, 31
	lwz %r0, 36(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rlwinm %r21, %r21, 24, 0, 31
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rlwinm %r12, %r12, 25, 0, 31
	lwz %r0, 44(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rlwinm %r22, %r22, 16, 0, 31
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rlwinm %r14, %r14, 20, 0, 31
	lwz %r0, 12(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rlwinm %r22, %r22, 24, 0, 31
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rlwinm %r14, %r14, 25, 0, 31
	lwz %r0, 0(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rlwinm %r23, %r23, 16, 0, 31
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rlwinm %r15, %r15, 20, 0, 31
	lwz %r0, 32(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rlwinm %r23, %r23, 24, 0, 31
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rlwinm %r15, %r15, 25, 0, 31
	lwz %r0, 48(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rlwinm %r23, %r23, 16, 0, 31
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rlwinm %r12, %r12, 20, 0, 31
	lwz %r0, 8(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rlwinm %r23, %r23, 24, 0, 31
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rlwinm %r12, %r12, 25, 0, 31
	lwz %r0, 52(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rlwinm %r20, %r20, 16, 0, 31
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rlwinm %r14, %r14, 20, 0, 31
	lwz %r0, 28(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rlwinm %r20, %r20, 24, 0, 31
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rlwinm %r14, %r14, 25, 0, 31
	lwz %r0, 4(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rlwinm %r21, %r21, 16, 0, 31
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rlwinm %r15, %r15, 20, 0, 31
	lwz %r0, 16(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rlwinm %r21, %r21, 24, 0, 31
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rlwinm %r15, %r15, 25, 0, 31
	lwz %r0, 40(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rlwinm %r22, %r22, 16, 0, 31
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rlwinm %r11, %r11, 20, 0, 31
	lwz %r0, 20(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rlwinm %r22, %r22, 24, 0, 31
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rlwinm %r11, %r11, 25, 0, 31
	lwz %r0, 40(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rlwinm %r20, %r20, 16, 0, 31
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rlwinm %r11, %r11, 20, 0, 31
	lwz %r0, 8(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rlwinm %r20, %r20, 24, 0, 31
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rlwinm %r11, %r11, 25, 0, 31
	lwz %r0, 32(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rlwinm %r21, %r21, 16, 0, 31
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rlwinm %r12, %r12, 20, 0, 31
	lwz %r0, 16(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rlwinm %r21, %r21, 24, 0, 31
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rlwinm %r12, %r12, 25, 0, 31
	lwz %r0, 28(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rlwinm %r22, %r22, 16, 0, 31
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rlwinm %r14, %r14, 20, 0, 31
	lwz %r0, 24(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rlwinm %r22, %r22, 24, 0, 31
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rlwinm %r14, %r14, 25, 0, 31
	lwz %r0, 4(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rlwinm %r23, %r23, 16, 0, 31
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rlwinm %r15, %r15, 20, 0, 31
	lwz %r0, 20(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rlwinm %r23, %r23, 24, 0, 31
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rlwinm %r15, %r15, 25, 0, 31
	lwz %r0, 60(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rlwinm %r23, %r23, 16, 0, 31
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rlwinm %r12, %r12, 20, 0, 31
	lwz %r0, 44(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rlwinm %r23, %r23, 24, 0, 31
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rlwinm %r12, %r12, 25, 0, 31
	lwz %r0, 36(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rlwinm %r20, %r20, 16, 0, 31
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rlwinm %r14, %r14, 20, 0, 31
	lwz %r0, 56(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rlwinm %r20, %r20, 24, 0, 31
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rlwinm %r14, %r14, 25, 0, 31
	lwz %r0, 12(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rlwinm %r21, %r21, 16, 0, 31
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rlwinm %r15, %r15, 20, 0, 31
	lwz %r0, 48(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rlwinm %r21, %r21, 24, 0, 31
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rlwinm %r15, %r15, 25, 0, 31
	lwz %r0, 52(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rlwinm %r22, %r22, 16, 0, 31
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rlwinm %r11, %r11, 20, 0, 31
	lwz %r0, 0(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rlwinm %r22, %r22, 24, 0, 31
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rlwinm %r11, %r11, 25, 0, 31
	lwz %r0, 0(%r3)
	xor %r0, %r0, %r6
	xor %r0, %r0, %r16
	stw %r0, 0(%r3)
	lwz %r0, 4(%r3)
	xor %r0, %r0, %r7
	xor %r0, %r0, %r17
	stw %r0, 4(%r3)
	lwz %r0, 8(%r3)
	xor %r0, %r0, %r9
	xor %r0, %r0, %r18
	stw %r0, 8(%r3)
	lwz %r0, 12(%r3)
	xor %r0, %r0, %r10
	xor %r0, %r0, %r19
	stw %r0, 12(%r3)
	lwz %r0, 16(%r3)
	xor %r0, %r0, %r11
	xor %r0, %r0, %r20
	stw %r0, 16(%r3)
	lwz %r0, 20(%r3)
	xor %r0, %r0, %r12
	xor %r0, %r0, %r21
	stw %r0, 20(%r3)
	lwz %r0, 24(%r3)
	xor %r0, %r0, %r14
	xor %r0, %r0, %r22
	stw %r0, 24(%r3)
	lwz %r0, 28(%r3)
	xor %r0, %r0, %r15
	xor %r0, %r0, %r23
	stw %r0, 28(%r3)
	addi %r4, %r4, 64
	ld %r6, 80(%r8)
	addi %r6, %r6, 64
	std %r6, 80(%r8)
	rldicl %r7, %r6, 58, 6
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	ld %r9, 88(%r8)
	add %r9, %r9, %r7
	std %r9, 88(%r8)
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r14, 0(%r8)
	ld %r15, 8(%r8)
	ld %r16, 16(%r8)
	ld %r17, 24(%r8)
	ld %r18, 32(%r8)
	ld %r19, 40(%r8)
	ld %r20, 48(%r8)
	ld %r21, 56(%r8)
	ld %r22, 64(%r8)
	ld %r23, 72(%r8)
	blr

vg_blake2s_init:
	lis %r9, -17561
	ori %r9, %r9, 44677
	stw %r9, 4(%r3)
	lis %r9, 15470
	ori %r9, %r9, 62322
	stw %r9, 8(%r3)
	lis %r9, -23217
	ori %r9, %r9, 62778
	stw %r9, 12(%r3)
	lis %r9, 20750
	ori %r9, %r9, 21119
	stw %r9, 16(%r3)
	lis %r9, -25851
	ori %r9, %r9, 26764
	stw %r9, 20(%r3)
	lis %r9, 8067
	ori %r9, %r9, 55723
	stw %r9, 24(%r3)
	lis %r9, 23520
	ori %r9, %r9, 52505
	stw %r9, 28(%r3)
	lis %r9, 27400
	ori %r9, %r9, 58983
	rldicr %r10, %r6, 8, 55
	xor %r9, %r9, %r10
	xor %r9, %r9, %r4
	stw %r9, 0(%r3)
	cmpldi %cr0, %r6, 0
	beq %cr0, 20f
	li %r9, 0
	std %r9, 32(%r3)
	std %r9, 40(%r3)
	std %r9, 48(%r3)
	std %r9, 56(%r3)
	std %r9, 64(%r3)
	std %r9, 72(%r3)
	std %r9, 80(%r3)
	std %r9, 88(%r3)
	addi %r12, %r3, 32
22:
	lbz %r9, 0(%r5)
	stb %r9, 0(%r12)
	addi %r5, %r5, 1
	addi %r12, %r12, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 22b
	b 21f
20:
21:
	blr

vg_blake2s_update:
	stdu %r1, -608(%r1)
	addi %r7, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 512(%r7)
	std %r27, 520(%r7)
	std %r28, 528(%r7)
	std %r29, 536(%r7)
	std %r30, 544(%r7)
	std %r31, 552(%r7)
	addi %r26, %r3, 0
	addi %r27, %r7, 0
	addi %r28, %r5, 0
	addi %r29, %r6, 0
	addi %r31, %r4, 0
	addi %r30, %r31, -1
	li %r9, 63
	and %r30, %r30, %r9
	addi %r30, %r30, 1
	cmpldi %cr0, %r31, 0
	beq %cr0, 20f
	b 21f
20:
	li %r30, 0
21:
	cmpldi %cr0, %r29, 0
	beq %cr0, 22f
	cmpldi %cr0, %r30, 0
	beq %cr0, 24f
	li %r11, 64
	subf %r11, %r30, %r11
	rldicl %r9, %r29, 58, 6
	cmpldi %cr0, %r9, 0
	beq %cr0, 26f
	b 27f
26:
	add %r9, %r29, %r30
	rldicl %r9, %r9, 58, 6
	cmpldi %cr0, %r9, 0
	beq %cr0, 28f
	b 29f
28:
	addi %r11, %r29, 0
29:
27:
	subf %r29, %r11, %r29
	add %r31, %r31, %r11
	cmpldi %cr0, %r11, 0
	beq %cr0, 210f
212:
	lbz %r9, 0(%r28)
	add %r12, %r26, %r30
	stb %r9, 32(%r12)
	addi %r28, %r28, 1
	addi %r30, %r30, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 212b
	b 211f
210:
211:
	cmpldi %cr0, %r29, 0
	beq %cr0, 213f
	addi %r3, %r26, 0
	addi %r4, %r26, 32
	li %r5, 1
	addi %r6, %r31, 0
	li %r7, 0
	addi %r8, %r27, 0
	bl {vg_blake2s_compress}
	li %r30, 0
	b 214f
213:
214:
	b 25f
24:
25:
	cmpldi %cr0, %r29, 0
	beq %cr0, 215f
	addi %r9, %r29, -1
	rldicl %r10, %r9, 58, 6
	cmpldi %cr0, %r10, 0
	beq %cr0, 217f
	addi %r3, %r26, 0
	addi %r4, %r28, 0
	addi %r5, %r10, 0
	addi %r6, %r31, 64
	li %r7, 0
	addi %r8, %r27, 0
	bl {vg_blake2s_compress}
	addi %r9, %r29, -1
	li %r10, 63
	and %r9, %r9, %r10
	addi %r9, %r9, 1
	subf %r10, %r9, %r29
	add %r28, %r28, %r10
	add %r31, %r31, %r10
	addi %r29, %r9, 0
	b 218f
217:
218:
	addi %r11, %r29, 0
	add %r31, %r31, %r29
	li %r29, 0
219:
	lbz %r9, 0(%r28)
	add %r12, %r26, %r30
	stb %r9, 32(%r12)
	addi %r28, %r28, 1
	addi %r30, %r30, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 219b
	b 216f
215:
216:
	b 23f
22:
23:
	ld %r26, 512(%r27)
	ld %r28, 528(%r27)
	ld %r29, 536(%r27)
	ld %r30, 544(%r27)
	ld %r31, 552(%r27)
	ld %r27, 520(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 608
	blr

vg_blake2s_finalize:
	stdu %r1, -608(%r1)
	addi %r6, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 512(%r6)
	std %r27, 520(%r6)
	std %r28, 528(%r6)
	std %r29, 536(%r6)
	std %r30, 544(%r6)
	std %r31, 552(%r6)
	addi %r26, %r3, 0
	addi %r27, %r6, 0
	addi %r28, %r5, 0
	addi %r31, %r4, 0
	addi %r30, %r31, -1
	li %r9, 63
	and %r30, %r30, %r9
	addi %r30, %r30, 1
	cmpldi %cr0, %r31, 0
	beq %cr0, 20f
	b 21f
20:
	li %r30, 0
21:
	li %r9, 0
	li %r11, 64
	subf %r11, %r30, %r11
	cmpldi %cr0, %r11, 0
	beq %cr0, 22f
24:
	add %r12, %r26, %r30
	stb %r9, 32(%r12)
	addi %r30, %r30, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 24b
	b 23f
22:
23:
	addi %r3, %r26, 0
	addi %r4, %r26, 32
	li %r5, 1
	addi %r6, %r31, 0
	li %r7, 1
	addi %r8, %r27, 0
	bl {vg_blake2s_compress}
	ld %r9, 0(%r26)
	std %r9, 0(%r28)
	ld %r9, 8(%r26)
	std %r9, 8(%r28)
	ld %r9, 16(%r26)
	std %r9, 16(%r28)
	ld %r9, 24(%r26)
	std %r9, 24(%r28)
	ld %r26, 512(%r27)
	ld %r28, 528(%r27)
	ld %r29, 536(%r27)
	ld %r30, 544(%r27)
	ld %r31, 552(%r27)
	ld %r27, 520(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 608
	blr
