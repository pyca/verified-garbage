// The functions of `src/internal/vg_blake2b_compress.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2b_compress:
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
	ld %r6, 0(%r3)
	ld %r7, 8(%r3)
	ld %r9, 16(%r3)
	ld %r10, 24(%r3)
	ld %r11, 32(%r3)
	ld %r12, 40(%r3)
	ld %r14, 48(%r3)
	ld %r15, 56(%r3)
	lis %r16, 27145
	ori %r16, %r16, 58983
	rldicr %r16, %r16, 32, 31
	oris %r16, %r16, 62396
	ori %r16, %r16, 51464
	lis %r17, -17561
	ori %r17, %r17, 44677
	rldicr %r17, %r17, 32, 31
	oris %r17, %r17, 33994
	ori %r17, %r17, 42811
	lis %r18, 15470
	ori %r18, %r18, 62322
	rldicr %r18, %r18, 32, 31
	oris %r18, %r18, 65172
	ori %r18, %r18, 63531
	lis %r19, -23217
	ori %r19, %r19, 62778
	rldicr %r19, %r19, 32, 31
	oris %r19, %r19, 24349
	ori %r19, %r19, 14065
	lis %r20, 20750
	ori %r20, %r20, 21119
	rldicr %r20, %r20, 32, 31
	oris %r20, %r20, 44518
	ori %r20, %r20, 33489
	lis %r21, -25851
	ori %r21, %r21, 26764
	rldicr %r21, %r21, 32, 31
	oris %r21, %r21, 11070
	ori %r21, %r21, 27679
	lis %r22, 8067
	ori %r22, %r22, 55723
	rldicr %r22, %r22, 32, 31
	oris %r22, %r22, 64321
	ori %r22, %r22, 48491
	lis %r23, 23520
	ori %r23, %r23, 52505
	rldicr %r23, %r23, 32, 31
	oris %r23, %r23, 4990
	ori %r23, %r23, 8569
	ld %r0, 80(%r8)
	xor %r20, %r20, %r0
	ld %r0, 88(%r8)
	xor %r21, %r21, %r0
	ld %r0, 96(%r8)
	xor %r22, %r22, %r0
	ld %r0, 0(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rldicl %r20, %r20, 32, 0
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	ld %r0, 8(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rldicl %r20, %r20, 48, 0
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	ld %r0, 16(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rldicl %r21, %r21, 32, 0
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	ld %r0, 24(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rldicl %r21, %r21, 48, 0
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	ld %r0, 32(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rldicl %r22, %r22, 32, 0
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rldicl %r14, %r14, 40, 0
	ld %r0, 40(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rldicl %r22, %r22, 48, 0
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rldicl %r14, %r14, 1, 0
	ld %r0, 48(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rldicl %r23, %r23, 32, 0
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rldicl %r15, %r15, 40, 0
	ld %r0, 56(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rldicl %r23, %r23, 48, 0
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rldicl %r15, %r15, 1, 0
	ld %r0, 64(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rldicl %r23, %r23, 32, 0
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rldicl %r12, %r12, 40, 0
	ld %r0, 72(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rldicl %r23, %r23, 48, 0
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rldicl %r12, %r12, 1, 0
	ld %r0, 80(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rldicl %r14, %r14, 40, 0
	ld %r0, 88(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rldicl %r14, %r14, 1, 0
	ld %r0, 96(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rldicl %r21, %r21, 32, 0
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rldicl %r15, %r15, 40, 0
	ld %r0, 104(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rldicl %r21, %r21, 48, 0
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rldicl %r15, %r15, 1, 0
	ld %r0, 112(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rldicl %r22, %r22, 32, 0
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	ld %r0, 120(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rldicl %r22, %r22, 48, 0
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	ld %r0, 112(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rldicl %r20, %r20, 32, 0
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	ld %r0, 80(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rldicl %r20, %r20, 48, 0
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	ld %r0, 32(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rldicl %r21, %r21, 32, 0
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	ld %r0, 64(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rldicl %r21, %r21, 48, 0
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	ld %r0, 72(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rldicl %r22, %r22, 32, 0
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rldicl %r14, %r14, 40, 0
	ld %r0, 120(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rldicl %r22, %r22, 48, 0
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rldicl %r14, %r14, 1, 0
	ld %r0, 104(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rldicl %r23, %r23, 32, 0
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rldicl %r15, %r15, 40, 0
	ld %r0, 48(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rldicl %r23, %r23, 48, 0
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rldicl %r15, %r15, 1, 0
	ld %r0, 8(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rldicl %r23, %r23, 32, 0
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rldicl %r12, %r12, 40, 0
	ld %r0, 96(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rldicl %r23, %r23, 48, 0
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rldicl %r12, %r12, 1, 0
	ld %r0, 0(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rldicl %r14, %r14, 40, 0
	ld %r0, 16(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rldicl %r14, %r14, 1, 0
	ld %r0, 88(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rldicl %r21, %r21, 32, 0
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rldicl %r15, %r15, 40, 0
	ld %r0, 56(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rldicl %r21, %r21, 48, 0
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rldicl %r15, %r15, 1, 0
	ld %r0, 40(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rldicl %r22, %r22, 32, 0
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	ld %r0, 24(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rldicl %r22, %r22, 48, 0
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	ld %r0, 88(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rldicl %r20, %r20, 32, 0
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	ld %r0, 64(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rldicl %r20, %r20, 48, 0
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	ld %r0, 96(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rldicl %r21, %r21, 32, 0
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	ld %r0, 0(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rldicl %r21, %r21, 48, 0
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	ld %r0, 40(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rldicl %r22, %r22, 32, 0
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rldicl %r14, %r14, 40, 0
	ld %r0, 16(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rldicl %r22, %r22, 48, 0
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rldicl %r14, %r14, 1, 0
	ld %r0, 120(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rldicl %r23, %r23, 32, 0
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rldicl %r15, %r15, 40, 0
	ld %r0, 104(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rldicl %r23, %r23, 48, 0
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rldicl %r15, %r15, 1, 0
	ld %r0, 80(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rldicl %r23, %r23, 32, 0
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rldicl %r12, %r12, 40, 0
	ld %r0, 112(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rldicl %r23, %r23, 48, 0
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rldicl %r12, %r12, 1, 0
	ld %r0, 24(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rldicl %r14, %r14, 40, 0
	ld %r0, 48(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rldicl %r14, %r14, 1, 0
	ld %r0, 56(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rldicl %r21, %r21, 32, 0
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rldicl %r15, %r15, 40, 0
	ld %r0, 8(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rldicl %r21, %r21, 48, 0
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rldicl %r15, %r15, 1, 0
	ld %r0, 72(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rldicl %r22, %r22, 32, 0
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	ld %r0, 32(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rldicl %r22, %r22, 48, 0
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	ld %r0, 56(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rldicl %r20, %r20, 32, 0
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	ld %r0, 72(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rldicl %r20, %r20, 48, 0
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	ld %r0, 24(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rldicl %r21, %r21, 32, 0
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	ld %r0, 8(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rldicl %r21, %r21, 48, 0
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	ld %r0, 104(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rldicl %r22, %r22, 32, 0
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rldicl %r14, %r14, 40, 0
	ld %r0, 96(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rldicl %r22, %r22, 48, 0
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rldicl %r14, %r14, 1, 0
	ld %r0, 88(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rldicl %r23, %r23, 32, 0
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rldicl %r15, %r15, 40, 0
	ld %r0, 112(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rldicl %r23, %r23, 48, 0
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rldicl %r15, %r15, 1, 0
	ld %r0, 16(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rldicl %r23, %r23, 32, 0
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rldicl %r12, %r12, 40, 0
	ld %r0, 48(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rldicl %r23, %r23, 48, 0
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rldicl %r12, %r12, 1, 0
	ld %r0, 40(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rldicl %r14, %r14, 40, 0
	ld %r0, 80(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rldicl %r14, %r14, 1, 0
	ld %r0, 32(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rldicl %r21, %r21, 32, 0
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rldicl %r15, %r15, 40, 0
	ld %r0, 0(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rldicl %r21, %r21, 48, 0
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rldicl %r15, %r15, 1, 0
	ld %r0, 120(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rldicl %r22, %r22, 32, 0
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	ld %r0, 64(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rldicl %r22, %r22, 48, 0
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	ld %r0, 72(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rldicl %r20, %r20, 32, 0
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	ld %r0, 0(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rldicl %r20, %r20, 48, 0
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	ld %r0, 40(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rldicl %r21, %r21, 32, 0
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	ld %r0, 56(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rldicl %r21, %r21, 48, 0
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	ld %r0, 16(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rldicl %r22, %r22, 32, 0
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rldicl %r14, %r14, 40, 0
	ld %r0, 32(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rldicl %r22, %r22, 48, 0
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rldicl %r14, %r14, 1, 0
	ld %r0, 80(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rldicl %r23, %r23, 32, 0
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rldicl %r15, %r15, 40, 0
	ld %r0, 120(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rldicl %r23, %r23, 48, 0
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rldicl %r15, %r15, 1, 0
	ld %r0, 112(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rldicl %r23, %r23, 32, 0
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rldicl %r12, %r12, 40, 0
	ld %r0, 8(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rldicl %r23, %r23, 48, 0
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rldicl %r12, %r12, 1, 0
	ld %r0, 88(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rldicl %r14, %r14, 40, 0
	ld %r0, 96(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rldicl %r14, %r14, 1, 0
	ld %r0, 48(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rldicl %r21, %r21, 32, 0
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rldicl %r15, %r15, 40, 0
	ld %r0, 64(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rldicl %r21, %r21, 48, 0
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rldicl %r15, %r15, 1, 0
	ld %r0, 24(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rldicl %r22, %r22, 32, 0
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	ld %r0, 104(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rldicl %r22, %r22, 48, 0
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	ld %r0, 16(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rldicl %r20, %r20, 32, 0
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	ld %r0, 96(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rldicl %r20, %r20, 48, 0
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	ld %r0, 48(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rldicl %r21, %r21, 32, 0
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	ld %r0, 80(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rldicl %r21, %r21, 48, 0
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	ld %r0, 0(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rldicl %r22, %r22, 32, 0
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rldicl %r14, %r14, 40, 0
	ld %r0, 88(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rldicl %r22, %r22, 48, 0
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rldicl %r14, %r14, 1, 0
	ld %r0, 64(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rldicl %r23, %r23, 32, 0
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rldicl %r15, %r15, 40, 0
	ld %r0, 24(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rldicl %r23, %r23, 48, 0
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rldicl %r15, %r15, 1, 0
	ld %r0, 32(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rldicl %r23, %r23, 32, 0
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rldicl %r12, %r12, 40, 0
	ld %r0, 104(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rldicl %r23, %r23, 48, 0
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rldicl %r12, %r12, 1, 0
	ld %r0, 56(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rldicl %r14, %r14, 40, 0
	ld %r0, 40(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rldicl %r14, %r14, 1, 0
	ld %r0, 120(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rldicl %r21, %r21, 32, 0
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rldicl %r15, %r15, 40, 0
	ld %r0, 112(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rldicl %r21, %r21, 48, 0
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rldicl %r15, %r15, 1, 0
	ld %r0, 8(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rldicl %r22, %r22, 32, 0
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	ld %r0, 72(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rldicl %r22, %r22, 48, 0
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	ld %r0, 96(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rldicl %r20, %r20, 32, 0
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	ld %r0, 40(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rldicl %r20, %r20, 48, 0
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	ld %r0, 8(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rldicl %r21, %r21, 32, 0
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	ld %r0, 120(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rldicl %r21, %r21, 48, 0
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	ld %r0, 112(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rldicl %r22, %r22, 32, 0
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rldicl %r14, %r14, 40, 0
	ld %r0, 104(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rldicl %r22, %r22, 48, 0
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rldicl %r14, %r14, 1, 0
	ld %r0, 32(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rldicl %r23, %r23, 32, 0
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rldicl %r15, %r15, 40, 0
	ld %r0, 80(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rldicl %r23, %r23, 48, 0
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rldicl %r15, %r15, 1, 0
	ld %r0, 0(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rldicl %r23, %r23, 32, 0
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rldicl %r12, %r12, 40, 0
	ld %r0, 56(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rldicl %r23, %r23, 48, 0
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rldicl %r12, %r12, 1, 0
	ld %r0, 48(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rldicl %r14, %r14, 40, 0
	ld %r0, 24(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rldicl %r14, %r14, 1, 0
	ld %r0, 72(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rldicl %r21, %r21, 32, 0
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rldicl %r15, %r15, 40, 0
	ld %r0, 16(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rldicl %r21, %r21, 48, 0
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rldicl %r15, %r15, 1, 0
	ld %r0, 64(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rldicl %r22, %r22, 32, 0
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	ld %r0, 88(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rldicl %r22, %r22, 48, 0
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	ld %r0, 104(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rldicl %r20, %r20, 32, 0
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	ld %r0, 88(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rldicl %r20, %r20, 48, 0
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	ld %r0, 56(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rldicl %r21, %r21, 32, 0
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	ld %r0, 112(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rldicl %r21, %r21, 48, 0
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	ld %r0, 96(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rldicl %r22, %r22, 32, 0
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rldicl %r14, %r14, 40, 0
	ld %r0, 8(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rldicl %r22, %r22, 48, 0
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rldicl %r14, %r14, 1, 0
	ld %r0, 24(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rldicl %r23, %r23, 32, 0
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rldicl %r15, %r15, 40, 0
	ld %r0, 72(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rldicl %r23, %r23, 48, 0
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rldicl %r15, %r15, 1, 0
	ld %r0, 40(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rldicl %r23, %r23, 32, 0
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rldicl %r12, %r12, 40, 0
	ld %r0, 0(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rldicl %r23, %r23, 48, 0
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rldicl %r12, %r12, 1, 0
	ld %r0, 120(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rldicl %r14, %r14, 40, 0
	ld %r0, 32(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rldicl %r14, %r14, 1, 0
	ld %r0, 64(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rldicl %r21, %r21, 32, 0
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rldicl %r15, %r15, 40, 0
	ld %r0, 48(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rldicl %r21, %r21, 48, 0
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rldicl %r15, %r15, 1, 0
	ld %r0, 16(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rldicl %r22, %r22, 32, 0
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	ld %r0, 80(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rldicl %r22, %r22, 48, 0
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	ld %r0, 48(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rldicl %r20, %r20, 32, 0
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	ld %r0, 120(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rldicl %r20, %r20, 48, 0
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	ld %r0, 112(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rldicl %r21, %r21, 32, 0
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	ld %r0, 72(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rldicl %r21, %r21, 48, 0
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	ld %r0, 88(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rldicl %r22, %r22, 32, 0
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rldicl %r14, %r14, 40, 0
	ld %r0, 24(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rldicl %r22, %r22, 48, 0
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rldicl %r14, %r14, 1, 0
	ld %r0, 0(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rldicl %r23, %r23, 32, 0
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rldicl %r15, %r15, 40, 0
	ld %r0, 64(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rldicl %r23, %r23, 48, 0
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rldicl %r15, %r15, 1, 0
	ld %r0, 96(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rldicl %r23, %r23, 32, 0
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rldicl %r12, %r12, 40, 0
	ld %r0, 16(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rldicl %r23, %r23, 48, 0
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rldicl %r12, %r12, 1, 0
	ld %r0, 104(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rldicl %r14, %r14, 40, 0
	ld %r0, 56(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rldicl %r14, %r14, 1, 0
	ld %r0, 8(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rldicl %r21, %r21, 32, 0
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rldicl %r15, %r15, 40, 0
	ld %r0, 32(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rldicl %r21, %r21, 48, 0
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rldicl %r15, %r15, 1, 0
	ld %r0, 80(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rldicl %r22, %r22, 32, 0
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	ld %r0, 40(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rldicl %r22, %r22, 48, 0
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	ld %r0, 80(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rldicl %r20, %r20, 32, 0
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	ld %r0, 16(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rldicl %r20, %r20, 48, 0
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	ld %r0, 64(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rldicl %r21, %r21, 32, 0
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	ld %r0, 32(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rldicl %r21, %r21, 48, 0
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	ld %r0, 56(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rldicl %r22, %r22, 32, 0
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rldicl %r14, %r14, 40, 0
	ld %r0, 48(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rldicl %r22, %r22, 48, 0
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rldicl %r14, %r14, 1, 0
	ld %r0, 8(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rldicl %r23, %r23, 32, 0
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rldicl %r15, %r15, 40, 0
	ld %r0, 40(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rldicl %r23, %r23, 48, 0
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rldicl %r15, %r15, 1, 0
	ld %r0, 120(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rldicl %r23, %r23, 32, 0
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rldicl %r12, %r12, 40, 0
	ld %r0, 88(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rldicl %r23, %r23, 48, 0
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rldicl %r12, %r12, 1, 0
	ld %r0, 72(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rldicl %r14, %r14, 40, 0
	ld %r0, 112(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rldicl %r14, %r14, 1, 0
	ld %r0, 24(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rldicl %r21, %r21, 32, 0
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rldicl %r15, %r15, 40, 0
	ld %r0, 96(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rldicl %r21, %r21, 48, 0
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rldicl %r15, %r15, 1, 0
	ld %r0, 104(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rldicl %r22, %r22, 32, 0
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	ld %r0, 0(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rldicl %r22, %r22, 48, 0
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	ld %r0, 0(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rldicl %r20, %r20, 32, 0
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	ld %r0, 8(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rldicl %r20, %r20, 48, 0
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	ld %r0, 16(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rldicl %r21, %r21, 32, 0
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	ld %r0, 24(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rldicl %r21, %r21, 48, 0
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	ld %r0, 32(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rldicl %r22, %r22, 32, 0
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rldicl %r14, %r14, 40, 0
	ld %r0, 40(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rldicl %r22, %r22, 48, 0
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rldicl %r14, %r14, 1, 0
	ld %r0, 48(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rldicl %r23, %r23, 32, 0
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rldicl %r15, %r15, 40, 0
	ld %r0, 56(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rldicl %r23, %r23, 48, 0
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rldicl %r15, %r15, 1, 0
	ld %r0, 64(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rldicl %r23, %r23, 32, 0
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rldicl %r12, %r12, 40, 0
	ld %r0, 72(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rldicl %r23, %r23, 48, 0
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rldicl %r12, %r12, 1, 0
	ld %r0, 80(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rldicl %r14, %r14, 40, 0
	ld %r0, 88(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rldicl %r14, %r14, 1, 0
	ld %r0, 96(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rldicl %r21, %r21, 32, 0
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rldicl %r15, %r15, 40, 0
	ld %r0, 104(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rldicl %r21, %r21, 48, 0
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rldicl %r15, %r15, 1, 0
	ld %r0, 112(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rldicl %r22, %r22, 32, 0
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	ld %r0, 120(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rldicl %r22, %r22, 48, 0
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	ld %r0, 112(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rldicl %r20, %r20, 32, 0
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 40, 0
	ld %r0, 80(%r4)
	add %r6, %r6, %r11
	add %r6, %r6, %r0
	xor %r20, %r20, %r6
	rldicl %r20, %r20, 48, 0
	add %r16, %r16, %r20
	xor %r11, %r11, %r16
	rldicl %r11, %r11, 1, 0
	ld %r0, 32(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rldicl %r21, %r21, 32, 0
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 40, 0
	ld %r0, 64(%r4)
	add %r7, %r7, %r12
	add %r7, %r7, %r0
	xor %r21, %r21, %r7
	rldicl %r21, %r21, 48, 0
	add %r17, %r17, %r21
	xor %r12, %r12, %r17
	rldicl %r12, %r12, 1, 0
	ld %r0, 72(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rldicl %r22, %r22, 32, 0
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rldicl %r14, %r14, 40, 0
	ld %r0, 120(%r4)
	add %r9, %r9, %r14
	add %r9, %r9, %r0
	xor %r22, %r22, %r9
	rldicl %r22, %r22, 48, 0
	add %r18, %r18, %r22
	xor %r14, %r14, %r18
	rldicl %r14, %r14, 1, 0
	ld %r0, 104(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rldicl %r23, %r23, 32, 0
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rldicl %r15, %r15, 40, 0
	ld %r0, 48(%r4)
	add %r10, %r10, %r15
	add %r10, %r10, %r0
	xor %r23, %r23, %r10
	rldicl %r23, %r23, 48, 0
	add %r19, %r19, %r23
	xor %r15, %r15, %r19
	rldicl %r15, %r15, 1, 0
	ld %r0, 8(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rldicl %r23, %r23, 32, 0
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rldicl %r12, %r12, 40, 0
	ld %r0, 96(%r4)
	add %r6, %r6, %r12
	add %r6, %r6, %r0
	xor %r23, %r23, %r6
	rldicl %r23, %r23, 48, 0
	add %r18, %r18, %r23
	xor %r12, %r12, %r18
	rldicl %r12, %r12, 1, 0
	ld %r0, 0(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 32, 0
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rldicl %r14, %r14, 40, 0
	ld %r0, 16(%r4)
	add %r7, %r7, %r14
	add %r7, %r7, %r0
	xor %r20, %r20, %r7
	rldicl %r20, %r20, 48, 0
	add %r19, %r19, %r20
	xor %r14, %r14, %r19
	rldicl %r14, %r14, 1, 0
	ld %r0, 88(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rldicl %r21, %r21, 32, 0
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rldicl %r15, %r15, 40, 0
	ld %r0, 56(%r4)
	add %r9, %r9, %r15
	add %r9, %r9, %r0
	xor %r21, %r21, %r9
	rldicl %r21, %r21, 48, 0
	add %r16, %r16, %r21
	xor %r15, %r15, %r16
	rldicl %r15, %r15, 1, 0
	ld %r0, 40(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rldicl %r22, %r22, 32, 0
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 40, 0
	ld %r0, 24(%r4)
	add %r10, %r10, %r11
	add %r10, %r10, %r0
	xor %r22, %r22, %r10
	rldicl %r22, %r22, 48, 0
	add %r17, %r17, %r22
	xor %r11, %r11, %r17
	rldicl %r11, %r11, 1, 0
	ld %r0, 0(%r3)
	xor %r0, %r0, %r6
	xor %r0, %r0, %r16
	std %r0, 0(%r3)
	ld %r0, 8(%r3)
	xor %r0, %r0, %r7
	xor %r0, %r0, %r17
	std %r0, 8(%r3)
	ld %r0, 16(%r3)
	xor %r0, %r0, %r9
	xor %r0, %r0, %r18
	std %r0, 16(%r3)
	ld %r0, 24(%r3)
	xor %r0, %r0, %r10
	xor %r0, %r0, %r19
	std %r0, 24(%r3)
	ld %r0, 32(%r3)
	xor %r0, %r0, %r11
	xor %r0, %r0, %r20
	std %r0, 32(%r3)
	ld %r0, 40(%r3)
	xor %r0, %r0, %r12
	xor %r0, %r0, %r21
	std %r0, 40(%r3)
	ld %r0, 48(%r3)
	xor %r0, %r0, %r14
	xor %r0, %r0, %r22
	std %r0, 48(%r3)
	ld %r0, 56(%r3)
	xor %r0, %r0, %r15
	xor %r0, %r0, %r23
	std %r0, 56(%r3)
	addi %r4, %r4, 128
	ld %r6, 80(%r8)
	addi %r6, %r6, 128
	std %r6, 80(%r8)
	rldicl %r7, %r6, 57, 7
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
