// The functions of `src/internal/vg_blake2s_compress.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
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
