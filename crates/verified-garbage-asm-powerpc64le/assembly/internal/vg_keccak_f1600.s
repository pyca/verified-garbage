// The functions of `src/internal/vg_keccak_f1600.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_f1600:
	std %r2, 32(%r4)
	std %r14, 40(%r4)
	std %r15, 48(%r4)
	std %r16, 56(%r4)
	std %r17, 64(%r4)
	std %r18, 72(%r4)
	std %r19, 80(%r4)
	std %r20, 88(%r4)
	std %r21, 96(%r4)
	std %r22, 104(%r4)
	std %r23, 112(%r4)
	std %r24, 120(%r4)
	std %r25, 128(%r4)
	std %r26, 136(%r4)
	std %r27, 144(%r4)
	std %r28, 152(%r4)
	std %r29, 160(%r4)
	std %r30, 168(%r4)
	std %r31, 176(%r4)
	lis %r0, -1
	ori %r0, %r0, 65535
	std %r0, 24(%r4)
	ld %r2, 0(%r3)
	ld %r7, 8(%r3)
	xor %r7, %r7, %r0
	ld %r8, 16(%r3)
	xor %r8, %r8, %r0
	ld %r9, 24(%r3)
	ld %r10, 32(%r3)
	ld %r11, 40(%r3)
	ld %r12, 48(%r3)
	ld %r14, 56(%r3)
	ld %r15, 64(%r3)
	xor %r15, %r15, %r0
	ld %r16, 72(%r3)
	ld %r17, 80(%r3)
	ld %r18, 88(%r3)
	ld %r19, 96(%r3)
	xor %r19, %r19, %r0
	ld %r20, 104(%r3)
	ld %r21, 112(%r3)
	ld %r22, 120(%r3)
	ld %r23, 128(%r3)
	ld %r24, 136(%r3)
	xor %r24, %r24, %r0
	ld %r25, 144(%r3)
	ld %r26, 152(%r3)
	ld %r27, 160(%r3)
	xor %r27, %r27, %r0
	ld %r28, 168(%r3)
	ld %r29, 176(%r3)
	ld %r30, 184(%r3)
	ld %r31, 192(%r3)
	xor %r0, %r2, %r11
	xor %r0, %r0, %r17
	xor %r0, %r0, %r22
	xor %r0, %r0, %r27
	xor %r5, %r7, %r12
	xor %r5, %r5, %r18
	xor %r5, %r5, %r23
	xor %r5, %r5, %r28
	xor %r6, %r8, %r14
	xor %r6, %r6, %r19
	xor %r6, %r6, %r24
	xor %r6, %r6, %r29
	std %r9, 0(%r4)
	xor %r9, %r9, %r15
	xor %r9, %r9, %r20
	xor %r9, %r9, %r25
	xor %r9, %r9, %r30
	std %r10, 8(%r4)
	xor %r10, %r10, %r16
	xor %r10, %r10, %r21
	xor %r10, %r10, %r26
	xor %r10, %r10, %r31
	std %r16, 16(%r4)
	rldicl %r16, %r6, 1, 0
	xor %r16, %r16, %r0
	xor %r7, %r7, %r16
	xor %r12, %r12, %r16
	xor %r18, %r18, %r16
	xor %r23, %r23, %r16
	xor %r28, %r28, %r16
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r9
	xor %r21, %r21, %r0
	xor %r26, %r26, %r0
	xor %r31, %r31, %r0
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r5
	xor %r8, %r8, %r9
	xor %r14, %r14, %r9
	xor %r19, %r19, %r9
	xor %r24, %r24, %r9
	xor %r29, %r29, %r9
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r10
	xor %r2, %r2, %r5
	xor %r11, %r11, %r5
	xor %r17, %r17, %r5
	xor %r22, %r22, %r5
	xor %r27, %r27, %r5
	rldicl %r10, %r10, 1, 0
	xor %r10, %r10, %r6
	xor %r15, %r15, %r10
	xor %r20, %r20, %r10
	xor %r25, %r25, %r10
	xor %r30, %r30, %r10
	ld %r5, 8(%r4)
	xor %r5, %r5, %r0
	ld %r6, 0(%r4)
	xor %r6, %r6, %r10
	ld %r16, 16(%r4)
	xor %r0, %r0, %r16
	rldicl %r9, %r25, 21, 0
	rldicl %r25, %r24, 15, 0
	rldicl %r24, %r18, 10, 0
	rldicl %r18, %r14, 6, 0
	rldicl %r14, %r17, 3, 0
	rldicl %r17, %r7, 1, 0
	rldicl %r7, %r12, 44, 0
	rldicl %r12, %r0, 20, 0
	rldicl %r10, %r31, 14, 0
	rldicl %r31, %r28, 2, 0
	rldicl %r28, %r15, 55, 0
	rldicl %r15, %r23, 45, 0
	rldicl %r23, %r11, 36, 0
	rldicl %r11, %r6, 28, 0
	rldicl %r16, %r29, 61, 0
	rldicl %r29, %r21, 39, 0
	rldicl %r21, %r27, 18, 0
	rldicl %r27, %r8, 62, 0
	rldicl %r8, %r19, 43, 0
	rldicl %r19, %r20, 25, 0
	rldicl %r20, %r26, 8, 0
	rldicl %r26, %r30, 56, 0
	rldicl %r30, %r22, 41, 0
	rldicl %r22, %r5, 27, 0
	and %r0, %r2, %r7
	or %r5, %r10, %r2
	or %r6, %r7, %r8
	xor %r2, %r2, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r8
	or %r6, %r6, %r9
	xor %r7, %r7, %r6
	and %r6, %r9, %r10
	xor %r8, %r8, %r6
	xor %r9, %r9, %r5
	xor %r10, %r10, %r0
	and %r0, %r11, %r12
	or %r5, %r16, %r11
	or %r6, %r12, %r14
	xor %r11, %r11, %r6
	and %r6, %r14, %r15
	xor %r12, %r12, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r16
	or %r6, %r6, %r15
	xor %r14, %r14, %r6
	xor %r15, %r15, %r5
	xor %r16, %r16, %r0
	or %r0, %r18, %r19
	and %r5, %r19, %r20
	and %r6, %r17, %r18
	xor %r18, %r18, %r5
	or %r5, %r21, %r17
	xor %r17, %r17, %r0
	ld %r0, 24(%r4)
	xor %r20, %r20, %r0
	and %r0, %r20, %r21
	xor %r19, %r19, %r0
	xor %r20, %r20, %r5
	xor %r21, %r21, %r6
	and %r0, %r23, %r24
	or %r5, %r24, %r25
	or %r6, %r22, %r23
	xor %r23, %r23, %r5
	and %r5, %r26, %r22
	xor %r22, %r22, %r0
	ld %r0, 24(%r4)
	xor %r25, %r25, %r0
	or %r0, %r25, %r26
	xor %r24, %r24, %r0
	xor %r25, %r25, %r5
	xor %r26, %r26, %r6
	or %r0, %r29, %r30
	and %r5, %r30, %r31
	or %r6, %r31, %r27
	xor %r30, %r30, %r6
	and %r6, %r27, %r28
	xor %r31, %r31, %r6
	ld %r6, 24(%r4)
	xor %r28, %r28, %r6
	and %r6, %r28, %r29
	xor %r27, %r27, %r6
	xor %r28, %r28, %r0
	xor %r29, %r29, %r5
	lis %r5, 0
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 1
	xor %r2, %r2, %r5
	xor %r0, %r2, %r11
	xor %r0, %r0, %r17
	xor %r0, %r0, %r22
	xor %r0, %r0, %r27
	xor %r5, %r7, %r12
	xor %r5, %r5, %r18
	xor %r5, %r5, %r23
	xor %r5, %r5, %r28
	xor %r6, %r8, %r14
	xor %r6, %r6, %r19
	xor %r6, %r6, %r24
	xor %r6, %r6, %r29
	std %r9, 0(%r4)
	xor %r9, %r9, %r15
	xor %r9, %r9, %r20
	xor %r9, %r9, %r25
	xor %r9, %r9, %r30
	std %r10, 8(%r4)
	xor %r10, %r10, %r16
	xor %r10, %r10, %r21
	xor %r10, %r10, %r26
	xor %r10, %r10, %r31
	std %r16, 16(%r4)
	rldicl %r16, %r6, 1, 0
	xor %r16, %r16, %r0
	xor %r7, %r7, %r16
	xor %r12, %r12, %r16
	xor %r18, %r18, %r16
	xor %r23, %r23, %r16
	xor %r28, %r28, %r16
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r9
	xor %r21, %r21, %r0
	xor %r26, %r26, %r0
	xor %r31, %r31, %r0
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r5
	xor %r8, %r8, %r9
	xor %r14, %r14, %r9
	xor %r19, %r19, %r9
	xor %r24, %r24, %r9
	xor %r29, %r29, %r9
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r10
	xor %r2, %r2, %r5
	xor %r11, %r11, %r5
	xor %r17, %r17, %r5
	xor %r22, %r22, %r5
	xor %r27, %r27, %r5
	rldicl %r10, %r10, 1, 0
	xor %r10, %r10, %r6
	xor %r15, %r15, %r10
	xor %r20, %r20, %r10
	xor %r25, %r25, %r10
	xor %r30, %r30, %r10
	ld %r5, 8(%r4)
	xor %r5, %r5, %r0
	ld %r6, 0(%r4)
	xor %r6, %r6, %r10
	ld %r16, 16(%r4)
	xor %r0, %r0, %r16
	rldicl %r9, %r25, 21, 0
	rldicl %r25, %r24, 15, 0
	rldicl %r24, %r18, 10, 0
	rldicl %r18, %r14, 6, 0
	rldicl %r14, %r17, 3, 0
	rldicl %r17, %r7, 1, 0
	rldicl %r7, %r12, 44, 0
	rldicl %r12, %r0, 20, 0
	rldicl %r10, %r31, 14, 0
	rldicl %r31, %r28, 2, 0
	rldicl %r28, %r15, 55, 0
	rldicl %r15, %r23, 45, 0
	rldicl %r23, %r11, 36, 0
	rldicl %r11, %r6, 28, 0
	rldicl %r16, %r29, 61, 0
	rldicl %r29, %r21, 39, 0
	rldicl %r21, %r27, 18, 0
	rldicl %r27, %r8, 62, 0
	rldicl %r8, %r19, 43, 0
	rldicl %r19, %r20, 25, 0
	rldicl %r20, %r26, 8, 0
	rldicl %r26, %r30, 56, 0
	rldicl %r30, %r22, 41, 0
	rldicl %r22, %r5, 27, 0
	and %r0, %r2, %r7
	or %r5, %r10, %r2
	or %r6, %r7, %r8
	xor %r2, %r2, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r8
	or %r6, %r6, %r9
	xor %r7, %r7, %r6
	and %r6, %r9, %r10
	xor %r8, %r8, %r6
	xor %r9, %r9, %r5
	xor %r10, %r10, %r0
	and %r0, %r11, %r12
	or %r5, %r16, %r11
	or %r6, %r12, %r14
	xor %r11, %r11, %r6
	and %r6, %r14, %r15
	xor %r12, %r12, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r16
	or %r6, %r6, %r15
	xor %r14, %r14, %r6
	xor %r15, %r15, %r5
	xor %r16, %r16, %r0
	or %r0, %r18, %r19
	and %r5, %r19, %r20
	and %r6, %r17, %r18
	xor %r18, %r18, %r5
	or %r5, %r21, %r17
	xor %r17, %r17, %r0
	ld %r0, 24(%r4)
	xor %r20, %r20, %r0
	and %r0, %r20, %r21
	xor %r19, %r19, %r0
	xor %r20, %r20, %r5
	xor %r21, %r21, %r6
	and %r0, %r23, %r24
	or %r5, %r24, %r25
	or %r6, %r22, %r23
	xor %r23, %r23, %r5
	and %r5, %r26, %r22
	xor %r22, %r22, %r0
	ld %r0, 24(%r4)
	xor %r25, %r25, %r0
	or %r0, %r25, %r26
	xor %r24, %r24, %r0
	xor %r25, %r25, %r5
	xor %r26, %r26, %r6
	or %r0, %r29, %r30
	and %r5, %r30, %r31
	or %r6, %r31, %r27
	xor %r30, %r30, %r6
	and %r6, %r27, %r28
	xor %r31, %r31, %r6
	ld %r6, 24(%r4)
	xor %r28, %r28, %r6
	and %r6, %r28, %r29
	xor %r27, %r27, %r6
	xor %r28, %r28, %r0
	xor %r29, %r29, %r5
	lis %r5, 0
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 32898
	xor %r2, %r2, %r5
	xor %r0, %r2, %r11
	xor %r0, %r0, %r17
	xor %r0, %r0, %r22
	xor %r0, %r0, %r27
	xor %r5, %r7, %r12
	xor %r5, %r5, %r18
	xor %r5, %r5, %r23
	xor %r5, %r5, %r28
	xor %r6, %r8, %r14
	xor %r6, %r6, %r19
	xor %r6, %r6, %r24
	xor %r6, %r6, %r29
	std %r9, 0(%r4)
	xor %r9, %r9, %r15
	xor %r9, %r9, %r20
	xor %r9, %r9, %r25
	xor %r9, %r9, %r30
	std %r10, 8(%r4)
	xor %r10, %r10, %r16
	xor %r10, %r10, %r21
	xor %r10, %r10, %r26
	xor %r10, %r10, %r31
	std %r16, 16(%r4)
	rldicl %r16, %r6, 1, 0
	xor %r16, %r16, %r0
	xor %r7, %r7, %r16
	xor %r12, %r12, %r16
	xor %r18, %r18, %r16
	xor %r23, %r23, %r16
	xor %r28, %r28, %r16
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r9
	xor %r21, %r21, %r0
	xor %r26, %r26, %r0
	xor %r31, %r31, %r0
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r5
	xor %r8, %r8, %r9
	xor %r14, %r14, %r9
	xor %r19, %r19, %r9
	xor %r24, %r24, %r9
	xor %r29, %r29, %r9
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r10
	xor %r2, %r2, %r5
	xor %r11, %r11, %r5
	xor %r17, %r17, %r5
	xor %r22, %r22, %r5
	xor %r27, %r27, %r5
	rldicl %r10, %r10, 1, 0
	xor %r10, %r10, %r6
	xor %r15, %r15, %r10
	xor %r20, %r20, %r10
	xor %r25, %r25, %r10
	xor %r30, %r30, %r10
	ld %r5, 8(%r4)
	xor %r5, %r5, %r0
	ld %r6, 0(%r4)
	xor %r6, %r6, %r10
	ld %r16, 16(%r4)
	xor %r0, %r0, %r16
	rldicl %r9, %r25, 21, 0
	rldicl %r25, %r24, 15, 0
	rldicl %r24, %r18, 10, 0
	rldicl %r18, %r14, 6, 0
	rldicl %r14, %r17, 3, 0
	rldicl %r17, %r7, 1, 0
	rldicl %r7, %r12, 44, 0
	rldicl %r12, %r0, 20, 0
	rldicl %r10, %r31, 14, 0
	rldicl %r31, %r28, 2, 0
	rldicl %r28, %r15, 55, 0
	rldicl %r15, %r23, 45, 0
	rldicl %r23, %r11, 36, 0
	rldicl %r11, %r6, 28, 0
	rldicl %r16, %r29, 61, 0
	rldicl %r29, %r21, 39, 0
	rldicl %r21, %r27, 18, 0
	rldicl %r27, %r8, 62, 0
	rldicl %r8, %r19, 43, 0
	rldicl %r19, %r20, 25, 0
	rldicl %r20, %r26, 8, 0
	rldicl %r26, %r30, 56, 0
	rldicl %r30, %r22, 41, 0
	rldicl %r22, %r5, 27, 0
	and %r0, %r2, %r7
	or %r5, %r10, %r2
	or %r6, %r7, %r8
	xor %r2, %r2, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r8
	or %r6, %r6, %r9
	xor %r7, %r7, %r6
	and %r6, %r9, %r10
	xor %r8, %r8, %r6
	xor %r9, %r9, %r5
	xor %r10, %r10, %r0
	and %r0, %r11, %r12
	or %r5, %r16, %r11
	or %r6, %r12, %r14
	xor %r11, %r11, %r6
	and %r6, %r14, %r15
	xor %r12, %r12, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r16
	or %r6, %r6, %r15
	xor %r14, %r14, %r6
	xor %r15, %r15, %r5
	xor %r16, %r16, %r0
	or %r0, %r18, %r19
	and %r5, %r19, %r20
	and %r6, %r17, %r18
	xor %r18, %r18, %r5
	or %r5, %r21, %r17
	xor %r17, %r17, %r0
	ld %r0, 24(%r4)
	xor %r20, %r20, %r0
	and %r0, %r20, %r21
	xor %r19, %r19, %r0
	xor %r20, %r20, %r5
	xor %r21, %r21, %r6
	and %r0, %r23, %r24
	or %r5, %r24, %r25
	or %r6, %r22, %r23
	xor %r23, %r23, %r5
	and %r5, %r26, %r22
	xor %r22, %r22, %r0
	ld %r0, 24(%r4)
	xor %r25, %r25, %r0
	or %r0, %r25, %r26
	xor %r24, %r24, %r0
	xor %r25, %r25, %r5
	xor %r26, %r26, %r6
	or %r0, %r29, %r30
	and %r5, %r30, %r31
	or %r6, %r31, %r27
	xor %r30, %r30, %r6
	and %r6, %r27, %r28
	xor %r31, %r31, %r6
	ld %r6, 24(%r4)
	xor %r28, %r28, %r6
	and %r6, %r28, %r29
	xor %r27, %r27, %r6
	xor %r28, %r28, %r0
	xor %r29, %r29, %r5
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 32906
	xor %r2, %r2, %r5
	xor %r0, %r2, %r11
	xor %r0, %r0, %r17
	xor %r0, %r0, %r22
	xor %r0, %r0, %r27
	xor %r5, %r7, %r12
	xor %r5, %r5, %r18
	xor %r5, %r5, %r23
	xor %r5, %r5, %r28
	xor %r6, %r8, %r14
	xor %r6, %r6, %r19
	xor %r6, %r6, %r24
	xor %r6, %r6, %r29
	std %r9, 0(%r4)
	xor %r9, %r9, %r15
	xor %r9, %r9, %r20
	xor %r9, %r9, %r25
	xor %r9, %r9, %r30
	std %r10, 8(%r4)
	xor %r10, %r10, %r16
	xor %r10, %r10, %r21
	xor %r10, %r10, %r26
	xor %r10, %r10, %r31
	std %r16, 16(%r4)
	rldicl %r16, %r6, 1, 0
	xor %r16, %r16, %r0
	xor %r7, %r7, %r16
	xor %r12, %r12, %r16
	xor %r18, %r18, %r16
	xor %r23, %r23, %r16
	xor %r28, %r28, %r16
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r9
	xor %r21, %r21, %r0
	xor %r26, %r26, %r0
	xor %r31, %r31, %r0
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r5
	xor %r8, %r8, %r9
	xor %r14, %r14, %r9
	xor %r19, %r19, %r9
	xor %r24, %r24, %r9
	xor %r29, %r29, %r9
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r10
	xor %r2, %r2, %r5
	xor %r11, %r11, %r5
	xor %r17, %r17, %r5
	xor %r22, %r22, %r5
	xor %r27, %r27, %r5
	rldicl %r10, %r10, 1, 0
	xor %r10, %r10, %r6
	xor %r15, %r15, %r10
	xor %r20, %r20, %r10
	xor %r25, %r25, %r10
	xor %r30, %r30, %r10
	ld %r5, 8(%r4)
	xor %r5, %r5, %r0
	ld %r6, 0(%r4)
	xor %r6, %r6, %r10
	ld %r16, 16(%r4)
	xor %r0, %r0, %r16
	rldicl %r9, %r25, 21, 0
	rldicl %r25, %r24, 15, 0
	rldicl %r24, %r18, 10, 0
	rldicl %r18, %r14, 6, 0
	rldicl %r14, %r17, 3, 0
	rldicl %r17, %r7, 1, 0
	rldicl %r7, %r12, 44, 0
	rldicl %r12, %r0, 20, 0
	rldicl %r10, %r31, 14, 0
	rldicl %r31, %r28, 2, 0
	rldicl %r28, %r15, 55, 0
	rldicl %r15, %r23, 45, 0
	rldicl %r23, %r11, 36, 0
	rldicl %r11, %r6, 28, 0
	rldicl %r16, %r29, 61, 0
	rldicl %r29, %r21, 39, 0
	rldicl %r21, %r27, 18, 0
	rldicl %r27, %r8, 62, 0
	rldicl %r8, %r19, 43, 0
	rldicl %r19, %r20, 25, 0
	rldicl %r20, %r26, 8, 0
	rldicl %r26, %r30, 56, 0
	rldicl %r30, %r22, 41, 0
	rldicl %r22, %r5, 27, 0
	and %r0, %r2, %r7
	or %r5, %r10, %r2
	or %r6, %r7, %r8
	xor %r2, %r2, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r8
	or %r6, %r6, %r9
	xor %r7, %r7, %r6
	and %r6, %r9, %r10
	xor %r8, %r8, %r6
	xor %r9, %r9, %r5
	xor %r10, %r10, %r0
	and %r0, %r11, %r12
	or %r5, %r16, %r11
	or %r6, %r12, %r14
	xor %r11, %r11, %r6
	and %r6, %r14, %r15
	xor %r12, %r12, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r16
	or %r6, %r6, %r15
	xor %r14, %r14, %r6
	xor %r15, %r15, %r5
	xor %r16, %r16, %r0
	or %r0, %r18, %r19
	and %r5, %r19, %r20
	and %r6, %r17, %r18
	xor %r18, %r18, %r5
	or %r5, %r21, %r17
	xor %r17, %r17, %r0
	ld %r0, 24(%r4)
	xor %r20, %r20, %r0
	and %r0, %r20, %r21
	xor %r19, %r19, %r0
	xor %r20, %r20, %r5
	xor %r21, %r21, %r6
	and %r0, %r23, %r24
	or %r5, %r24, %r25
	or %r6, %r22, %r23
	xor %r23, %r23, %r5
	and %r5, %r26, %r22
	xor %r22, %r22, %r0
	ld %r0, 24(%r4)
	xor %r25, %r25, %r0
	or %r0, %r25, %r26
	xor %r24, %r24, %r0
	xor %r25, %r25, %r5
	xor %r26, %r26, %r6
	or %r0, %r29, %r30
	and %r5, %r30, %r31
	or %r6, %r31, %r27
	xor %r30, %r30, %r6
	and %r6, %r27, %r28
	xor %r31, %r31, %r6
	ld %r6, 24(%r4)
	xor %r28, %r28, %r6
	and %r6, %r28, %r29
	xor %r27, %r27, %r6
	xor %r28, %r28, %r0
	xor %r29, %r29, %r5
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 32768
	ori %r5, %r5, 32768
	xor %r2, %r2, %r5
	xor %r0, %r2, %r11
	xor %r0, %r0, %r17
	xor %r0, %r0, %r22
	xor %r0, %r0, %r27
	xor %r5, %r7, %r12
	xor %r5, %r5, %r18
	xor %r5, %r5, %r23
	xor %r5, %r5, %r28
	xor %r6, %r8, %r14
	xor %r6, %r6, %r19
	xor %r6, %r6, %r24
	xor %r6, %r6, %r29
	std %r9, 0(%r4)
	xor %r9, %r9, %r15
	xor %r9, %r9, %r20
	xor %r9, %r9, %r25
	xor %r9, %r9, %r30
	std %r10, 8(%r4)
	xor %r10, %r10, %r16
	xor %r10, %r10, %r21
	xor %r10, %r10, %r26
	xor %r10, %r10, %r31
	std %r16, 16(%r4)
	rldicl %r16, %r6, 1, 0
	xor %r16, %r16, %r0
	xor %r7, %r7, %r16
	xor %r12, %r12, %r16
	xor %r18, %r18, %r16
	xor %r23, %r23, %r16
	xor %r28, %r28, %r16
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r9
	xor %r21, %r21, %r0
	xor %r26, %r26, %r0
	xor %r31, %r31, %r0
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r5
	xor %r8, %r8, %r9
	xor %r14, %r14, %r9
	xor %r19, %r19, %r9
	xor %r24, %r24, %r9
	xor %r29, %r29, %r9
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r10
	xor %r2, %r2, %r5
	xor %r11, %r11, %r5
	xor %r17, %r17, %r5
	xor %r22, %r22, %r5
	xor %r27, %r27, %r5
	rldicl %r10, %r10, 1, 0
	xor %r10, %r10, %r6
	xor %r15, %r15, %r10
	xor %r20, %r20, %r10
	xor %r25, %r25, %r10
	xor %r30, %r30, %r10
	ld %r5, 8(%r4)
	xor %r5, %r5, %r0
	ld %r6, 0(%r4)
	xor %r6, %r6, %r10
	ld %r16, 16(%r4)
	xor %r0, %r0, %r16
	rldicl %r9, %r25, 21, 0
	rldicl %r25, %r24, 15, 0
	rldicl %r24, %r18, 10, 0
	rldicl %r18, %r14, 6, 0
	rldicl %r14, %r17, 3, 0
	rldicl %r17, %r7, 1, 0
	rldicl %r7, %r12, 44, 0
	rldicl %r12, %r0, 20, 0
	rldicl %r10, %r31, 14, 0
	rldicl %r31, %r28, 2, 0
	rldicl %r28, %r15, 55, 0
	rldicl %r15, %r23, 45, 0
	rldicl %r23, %r11, 36, 0
	rldicl %r11, %r6, 28, 0
	rldicl %r16, %r29, 61, 0
	rldicl %r29, %r21, 39, 0
	rldicl %r21, %r27, 18, 0
	rldicl %r27, %r8, 62, 0
	rldicl %r8, %r19, 43, 0
	rldicl %r19, %r20, 25, 0
	rldicl %r20, %r26, 8, 0
	rldicl %r26, %r30, 56, 0
	rldicl %r30, %r22, 41, 0
	rldicl %r22, %r5, 27, 0
	and %r0, %r2, %r7
	or %r5, %r10, %r2
	or %r6, %r7, %r8
	xor %r2, %r2, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r8
	or %r6, %r6, %r9
	xor %r7, %r7, %r6
	and %r6, %r9, %r10
	xor %r8, %r8, %r6
	xor %r9, %r9, %r5
	xor %r10, %r10, %r0
	and %r0, %r11, %r12
	or %r5, %r16, %r11
	or %r6, %r12, %r14
	xor %r11, %r11, %r6
	and %r6, %r14, %r15
	xor %r12, %r12, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r16
	or %r6, %r6, %r15
	xor %r14, %r14, %r6
	xor %r15, %r15, %r5
	xor %r16, %r16, %r0
	or %r0, %r18, %r19
	and %r5, %r19, %r20
	and %r6, %r17, %r18
	xor %r18, %r18, %r5
	or %r5, %r21, %r17
	xor %r17, %r17, %r0
	ld %r0, 24(%r4)
	xor %r20, %r20, %r0
	and %r0, %r20, %r21
	xor %r19, %r19, %r0
	xor %r20, %r20, %r5
	xor %r21, %r21, %r6
	and %r0, %r23, %r24
	or %r5, %r24, %r25
	or %r6, %r22, %r23
	xor %r23, %r23, %r5
	and %r5, %r26, %r22
	xor %r22, %r22, %r0
	ld %r0, 24(%r4)
	xor %r25, %r25, %r0
	or %r0, %r25, %r26
	xor %r24, %r24, %r0
	xor %r25, %r25, %r5
	xor %r26, %r26, %r6
	or %r0, %r29, %r30
	and %r5, %r30, %r31
	or %r6, %r31, %r27
	xor %r30, %r30, %r6
	and %r6, %r27, %r28
	xor %r31, %r31, %r6
	ld %r6, 24(%r4)
	xor %r28, %r28, %r6
	and %r6, %r28, %r29
	xor %r27, %r27, %r6
	xor %r28, %r28, %r0
	xor %r29, %r29, %r5
	lis %r5, 0
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 32907
	xor %r2, %r2, %r5
	xor %r0, %r2, %r11
	xor %r0, %r0, %r17
	xor %r0, %r0, %r22
	xor %r0, %r0, %r27
	xor %r5, %r7, %r12
	xor %r5, %r5, %r18
	xor %r5, %r5, %r23
	xor %r5, %r5, %r28
	xor %r6, %r8, %r14
	xor %r6, %r6, %r19
	xor %r6, %r6, %r24
	xor %r6, %r6, %r29
	std %r9, 0(%r4)
	xor %r9, %r9, %r15
	xor %r9, %r9, %r20
	xor %r9, %r9, %r25
	xor %r9, %r9, %r30
	std %r10, 8(%r4)
	xor %r10, %r10, %r16
	xor %r10, %r10, %r21
	xor %r10, %r10, %r26
	xor %r10, %r10, %r31
	std %r16, 16(%r4)
	rldicl %r16, %r6, 1, 0
	xor %r16, %r16, %r0
	xor %r7, %r7, %r16
	xor %r12, %r12, %r16
	xor %r18, %r18, %r16
	xor %r23, %r23, %r16
	xor %r28, %r28, %r16
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r9
	xor %r21, %r21, %r0
	xor %r26, %r26, %r0
	xor %r31, %r31, %r0
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r5
	xor %r8, %r8, %r9
	xor %r14, %r14, %r9
	xor %r19, %r19, %r9
	xor %r24, %r24, %r9
	xor %r29, %r29, %r9
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r10
	xor %r2, %r2, %r5
	xor %r11, %r11, %r5
	xor %r17, %r17, %r5
	xor %r22, %r22, %r5
	xor %r27, %r27, %r5
	rldicl %r10, %r10, 1, 0
	xor %r10, %r10, %r6
	xor %r15, %r15, %r10
	xor %r20, %r20, %r10
	xor %r25, %r25, %r10
	xor %r30, %r30, %r10
	ld %r5, 8(%r4)
	xor %r5, %r5, %r0
	ld %r6, 0(%r4)
	xor %r6, %r6, %r10
	ld %r16, 16(%r4)
	xor %r0, %r0, %r16
	rldicl %r9, %r25, 21, 0
	rldicl %r25, %r24, 15, 0
	rldicl %r24, %r18, 10, 0
	rldicl %r18, %r14, 6, 0
	rldicl %r14, %r17, 3, 0
	rldicl %r17, %r7, 1, 0
	rldicl %r7, %r12, 44, 0
	rldicl %r12, %r0, 20, 0
	rldicl %r10, %r31, 14, 0
	rldicl %r31, %r28, 2, 0
	rldicl %r28, %r15, 55, 0
	rldicl %r15, %r23, 45, 0
	rldicl %r23, %r11, 36, 0
	rldicl %r11, %r6, 28, 0
	rldicl %r16, %r29, 61, 0
	rldicl %r29, %r21, 39, 0
	rldicl %r21, %r27, 18, 0
	rldicl %r27, %r8, 62, 0
	rldicl %r8, %r19, 43, 0
	rldicl %r19, %r20, 25, 0
	rldicl %r20, %r26, 8, 0
	rldicl %r26, %r30, 56, 0
	rldicl %r30, %r22, 41, 0
	rldicl %r22, %r5, 27, 0
	and %r0, %r2, %r7
	or %r5, %r10, %r2
	or %r6, %r7, %r8
	xor %r2, %r2, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r8
	or %r6, %r6, %r9
	xor %r7, %r7, %r6
	and %r6, %r9, %r10
	xor %r8, %r8, %r6
	xor %r9, %r9, %r5
	xor %r10, %r10, %r0
	and %r0, %r11, %r12
	or %r5, %r16, %r11
	or %r6, %r12, %r14
	xor %r11, %r11, %r6
	and %r6, %r14, %r15
	xor %r12, %r12, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r16
	or %r6, %r6, %r15
	xor %r14, %r14, %r6
	xor %r15, %r15, %r5
	xor %r16, %r16, %r0
	or %r0, %r18, %r19
	and %r5, %r19, %r20
	and %r6, %r17, %r18
	xor %r18, %r18, %r5
	or %r5, %r21, %r17
	xor %r17, %r17, %r0
	ld %r0, 24(%r4)
	xor %r20, %r20, %r0
	and %r0, %r20, %r21
	xor %r19, %r19, %r0
	xor %r20, %r20, %r5
	xor %r21, %r21, %r6
	and %r0, %r23, %r24
	or %r5, %r24, %r25
	or %r6, %r22, %r23
	xor %r23, %r23, %r5
	and %r5, %r26, %r22
	xor %r22, %r22, %r0
	ld %r0, 24(%r4)
	xor %r25, %r25, %r0
	or %r0, %r25, %r26
	xor %r24, %r24, %r0
	xor %r25, %r25, %r5
	xor %r26, %r26, %r6
	or %r0, %r29, %r30
	and %r5, %r30, %r31
	or %r6, %r31, %r27
	xor %r30, %r30, %r6
	and %r6, %r27, %r28
	xor %r31, %r31, %r6
	ld %r6, 24(%r4)
	xor %r28, %r28, %r6
	and %r6, %r28, %r29
	xor %r27, %r27, %r6
	xor %r28, %r28, %r0
	xor %r29, %r29, %r5
	lis %r5, 0
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 32768
	ori %r5, %r5, 1
	xor %r2, %r2, %r5
	xor %r0, %r2, %r11
	xor %r0, %r0, %r17
	xor %r0, %r0, %r22
	xor %r0, %r0, %r27
	xor %r5, %r7, %r12
	xor %r5, %r5, %r18
	xor %r5, %r5, %r23
	xor %r5, %r5, %r28
	xor %r6, %r8, %r14
	xor %r6, %r6, %r19
	xor %r6, %r6, %r24
	xor %r6, %r6, %r29
	std %r9, 0(%r4)
	xor %r9, %r9, %r15
	xor %r9, %r9, %r20
	xor %r9, %r9, %r25
	xor %r9, %r9, %r30
	std %r10, 8(%r4)
	xor %r10, %r10, %r16
	xor %r10, %r10, %r21
	xor %r10, %r10, %r26
	xor %r10, %r10, %r31
	std %r16, 16(%r4)
	rldicl %r16, %r6, 1, 0
	xor %r16, %r16, %r0
	xor %r7, %r7, %r16
	xor %r12, %r12, %r16
	xor %r18, %r18, %r16
	xor %r23, %r23, %r16
	xor %r28, %r28, %r16
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r9
	xor %r21, %r21, %r0
	xor %r26, %r26, %r0
	xor %r31, %r31, %r0
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r5
	xor %r8, %r8, %r9
	xor %r14, %r14, %r9
	xor %r19, %r19, %r9
	xor %r24, %r24, %r9
	xor %r29, %r29, %r9
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r10
	xor %r2, %r2, %r5
	xor %r11, %r11, %r5
	xor %r17, %r17, %r5
	xor %r22, %r22, %r5
	xor %r27, %r27, %r5
	rldicl %r10, %r10, 1, 0
	xor %r10, %r10, %r6
	xor %r15, %r15, %r10
	xor %r20, %r20, %r10
	xor %r25, %r25, %r10
	xor %r30, %r30, %r10
	ld %r5, 8(%r4)
	xor %r5, %r5, %r0
	ld %r6, 0(%r4)
	xor %r6, %r6, %r10
	ld %r16, 16(%r4)
	xor %r0, %r0, %r16
	rldicl %r9, %r25, 21, 0
	rldicl %r25, %r24, 15, 0
	rldicl %r24, %r18, 10, 0
	rldicl %r18, %r14, 6, 0
	rldicl %r14, %r17, 3, 0
	rldicl %r17, %r7, 1, 0
	rldicl %r7, %r12, 44, 0
	rldicl %r12, %r0, 20, 0
	rldicl %r10, %r31, 14, 0
	rldicl %r31, %r28, 2, 0
	rldicl %r28, %r15, 55, 0
	rldicl %r15, %r23, 45, 0
	rldicl %r23, %r11, 36, 0
	rldicl %r11, %r6, 28, 0
	rldicl %r16, %r29, 61, 0
	rldicl %r29, %r21, 39, 0
	rldicl %r21, %r27, 18, 0
	rldicl %r27, %r8, 62, 0
	rldicl %r8, %r19, 43, 0
	rldicl %r19, %r20, 25, 0
	rldicl %r20, %r26, 8, 0
	rldicl %r26, %r30, 56, 0
	rldicl %r30, %r22, 41, 0
	rldicl %r22, %r5, 27, 0
	and %r0, %r2, %r7
	or %r5, %r10, %r2
	or %r6, %r7, %r8
	xor %r2, %r2, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r8
	or %r6, %r6, %r9
	xor %r7, %r7, %r6
	and %r6, %r9, %r10
	xor %r8, %r8, %r6
	xor %r9, %r9, %r5
	xor %r10, %r10, %r0
	and %r0, %r11, %r12
	or %r5, %r16, %r11
	or %r6, %r12, %r14
	xor %r11, %r11, %r6
	and %r6, %r14, %r15
	xor %r12, %r12, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r16
	or %r6, %r6, %r15
	xor %r14, %r14, %r6
	xor %r15, %r15, %r5
	xor %r16, %r16, %r0
	or %r0, %r18, %r19
	and %r5, %r19, %r20
	and %r6, %r17, %r18
	xor %r18, %r18, %r5
	or %r5, %r21, %r17
	xor %r17, %r17, %r0
	ld %r0, 24(%r4)
	xor %r20, %r20, %r0
	and %r0, %r20, %r21
	xor %r19, %r19, %r0
	xor %r20, %r20, %r5
	xor %r21, %r21, %r6
	and %r0, %r23, %r24
	or %r5, %r24, %r25
	or %r6, %r22, %r23
	xor %r23, %r23, %r5
	and %r5, %r26, %r22
	xor %r22, %r22, %r0
	ld %r0, 24(%r4)
	xor %r25, %r25, %r0
	or %r0, %r25, %r26
	xor %r24, %r24, %r0
	xor %r25, %r25, %r5
	xor %r26, %r26, %r6
	or %r0, %r29, %r30
	and %r5, %r30, %r31
	or %r6, %r31, %r27
	xor %r30, %r30, %r6
	and %r6, %r27, %r28
	xor %r31, %r31, %r6
	ld %r6, 24(%r4)
	xor %r28, %r28, %r6
	and %r6, %r28, %r29
	xor %r27, %r27, %r6
	xor %r28, %r28, %r0
	xor %r29, %r29, %r5
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 32768
	ori %r5, %r5, 32897
	xor %r2, %r2, %r5
	xor %r0, %r2, %r11
	xor %r0, %r0, %r17
	xor %r0, %r0, %r22
	xor %r0, %r0, %r27
	xor %r5, %r7, %r12
	xor %r5, %r5, %r18
	xor %r5, %r5, %r23
	xor %r5, %r5, %r28
	xor %r6, %r8, %r14
	xor %r6, %r6, %r19
	xor %r6, %r6, %r24
	xor %r6, %r6, %r29
	std %r9, 0(%r4)
	xor %r9, %r9, %r15
	xor %r9, %r9, %r20
	xor %r9, %r9, %r25
	xor %r9, %r9, %r30
	std %r10, 8(%r4)
	xor %r10, %r10, %r16
	xor %r10, %r10, %r21
	xor %r10, %r10, %r26
	xor %r10, %r10, %r31
	std %r16, 16(%r4)
	rldicl %r16, %r6, 1, 0
	xor %r16, %r16, %r0
	xor %r7, %r7, %r16
	xor %r12, %r12, %r16
	xor %r18, %r18, %r16
	xor %r23, %r23, %r16
	xor %r28, %r28, %r16
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r9
	xor %r21, %r21, %r0
	xor %r26, %r26, %r0
	xor %r31, %r31, %r0
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r5
	xor %r8, %r8, %r9
	xor %r14, %r14, %r9
	xor %r19, %r19, %r9
	xor %r24, %r24, %r9
	xor %r29, %r29, %r9
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r10
	xor %r2, %r2, %r5
	xor %r11, %r11, %r5
	xor %r17, %r17, %r5
	xor %r22, %r22, %r5
	xor %r27, %r27, %r5
	rldicl %r10, %r10, 1, 0
	xor %r10, %r10, %r6
	xor %r15, %r15, %r10
	xor %r20, %r20, %r10
	xor %r25, %r25, %r10
	xor %r30, %r30, %r10
	ld %r5, 8(%r4)
	xor %r5, %r5, %r0
	ld %r6, 0(%r4)
	xor %r6, %r6, %r10
	ld %r16, 16(%r4)
	xor %r0, %r0, %r16
	rldicl %r9, %r25, 21, 0
	rldicl %r25, %r24, 15, 0
	rldicl %r24, %r18, 10, 0
	rldicl %r18, %r14, 6, 0
	rldicl %r14, %r17, 3, 0
	rldicl %r17, %r7, 1, 0
	rldicl %r7, %r12, 44, 0
	rldicl %r12, %r0, 20, 0
	rldicl %r10, %r31, 14, 0
	rldicl %r31, %r28, 2, 0
	rldicl %r28, %r15, 55, 0
	rldicl %r15, %r23, 45, 0
	rldicl %r23, %r11, 36, 0
	rldicl %r11, %r6, 28, 0
	rldicl %r16, %r29, 61, 0
	rldicl %r29, %r21, 39, 0
	rldicl %r21, %r27, 18, 0
	rldicl %r27, %r8, 62, 0
	rldicl %r8, %r19, 43, 0
	rldicl %r19, %r20, 25, 0
	rldicl %r20, %r26, 8, 0
	rldicl %r26, %r30, 56, 0
	rldicl %r30, %r22, 41, 0
	rldicl %r22, %r5, 27, 0
	and %r0, %r2, %r7
	or %r5, %r10, %r2
	or %r6, %r7, %r8
	xor %r2, %r2, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r8
	or %r6, %r6, %r9
	xor %r7, %r7, %r6
	and %r6, %r9, %r10
	xor %r8, %r8, %r6
	xor %r9, %r9, %r5
	xor %r10, %r10, %r0
	and %r0, %r11, %r12
	or %r5, %r16, %r11
	or %r6, %r12, %r14
	xor %r11, %r11, %r6
	and %r6, %r14, %r15
	xor %r12, %r12, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r16
	or %r6, %r6, %r15
	xor %r14, %r14, %r6
	xor %r15, %r15, %r5
	xor %r16, %r16, %r0
	or %r0, %r18, %r19
	and %r5, %r19, %r20
	and %r6, %r17, %r18
	xor %r18, %r18, %r5
	or %r5, %r21, %r17
	xor %r17, %r17, %r0
	ld %r0, 24(%r4)
	xor %r20, %r20, %r0
	and %r0, %r20, %r21
	xor %r19, %r19, %r0
	xor %r20, %r20, %r5
	xor %r21, %r21, %r6
	and %r0, %r23, %r24
	or %r5, %r24, %r25
	or %r6, %r22, %r23
	xor %r23, %r23, %r5
	and %r5, %r26, %r22
	xor %r22, %r22, %r0
	ld %r0, 24(%r4)
	xor %r25, %r25, %r0
	or %r0, %r25, %r26
	xor %r24, %r24, %r0
	xor %r25, %r25, %r5
	xor %r26, %r26, %r6
	or %r0, %r29, %r30
	and %r5, %r30, %r31
	or %r6, %r31, %r27
	xor %r30, %r30, %r6
	and %r6, %r27, %r28
	xor %r31, %r31, %r6
	ld %r6, 24(%r4)
	xor %r28, %r28, %r6
	and %r6, %r28, %r29
	xor %r27, %r27, %r6
	xor %r28, %r28, %r0
	xor %r29, %r29, %r5
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 32777
	xor %r2, %r2, %r5
	xor %r0, %r2, %r11
	xor %r0, %r0, %r17
	xor %r0, %r0, %r22
	xor %r0, %r0, %r27
	xor %r5, %r7, %r12
	xor %r5, %r5, %r18
	xor %r5, %r5, %r23
	xor %r5, %r5, %r28
	xor %r6, %r8, %r14
	xor %r6, %r6, %r19
	xor %r6, %r6, %r24
	xor %r6, %r6, %r29
	std %r9, 0(%r4)
	xor %r9, %r9, %r15
	xor %r9, %r9, %r20
	xor %r9, %r9, %r25
	xor %r9, %r9, %r30
	std %r10, 8(%r4)
	xor %r10, %r10, %r16
	xor %r10, %r10, %r21
	xor %r10, %r10, %r26
	xor %r10, %r10, %r31
	std %r16, 16(%r4)
	rldicl %r16, %r6, 1, 0
	xor %r16, %r16, %r0
	xor %r7, %r7, %r16
	xor %r12, %r12, %r16
	xor %r18, %r18, %r16
	xor %r23, %r23, %r16
	xor %r28, %r28, %r16
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r9
	xor %r21, %r21, %r0
	xor %r26, %r26, %r0
	xor %r31, %r31, %r0
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r5
	xor %r8, %r8, %r9
	xor %r14, %r14, %r9
	xor %r19, %r19, %r9
	xor %r24, %r24, %r9
	xor %r29, %r29, %r9
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r10
	xor %r2, %r2, %r5
	xor %r11, %r11, %r5
	xor %r17, %r17, %r5
	xor %r22, %r22, %r5
	xor %r27, %r27, %r5
	rldicl %r10, %r10, 1, 0
	xor %r10, %r10, %r6
	xor %r15, %r15, %r10
	xor %r20, %r20, %r10
	xor %r25, %r25, %r10
	xor %r30, %r30, %r10
	ld %r5, 8(%r4)
	xor %r5, %r5, %r0
	ld %r6, 0(%r4)
	xor %r6, %r6, %r10
	ld %r16, 16(%r4)
	xor %r0, %r0, %r16
	rldicl %r9, %r25, 21, 0
	rldicl %r25, %r24, 15, 0
	rldicl %r24, %r18, 10, 0
	rldicl %r18, %r14, 6, 0
	rldicl %r14, %r17, 3, 0
	rldicl %r17, %r7, 1, 0
	rldicl %r7, %r12, 44, 0
	rldicl %r12, %r0, 20, 0
	rldicl %r10, %r31, 14, 0
	rldicl %r31, %r28, 2, 0
	rldicl %r28, %r15, 55, 0
	rldicl %r15, %r23, 45, 0
	rldicl %r23, %r11, 36, 0
	rldicl %r11, %r6, 28, 0
	rldicl %r16, %r29, 61, 0
	rldicl %r29, %r21, 39, 0
	rldicl %r21, %r27, 18, 0
	rldicl %r27, %r8, 62, 0
	rldicl %r8, %r19, 43, 0
	rldicl %r19, %r20, 25, 0
	rldicl %r20, %r26, 8, 0
	rldicl %r26, %r30, 56, 0
	rldicl %r30, %r22, 41, 0
	rldicl %r22, %r5, 27, 0
	and %r0, %r2, %r7
	or %r5, %r10, %r2
	or %r6, %r7, %r8
	xor %r2, %r2, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r8
	or %r6, %r6, %r9
	xor %r7, %r7, %r6
	and %r6, %r9, %r10
	xor %r8, %r8, %r6
	xor %r9, %r9, %r5
	xor %r10, %r10, %r0
	and %r0, %r11, %r12
	or %r5, %r16, %r11
	or %r6, %r12, %r14
	xor %r11, %r11, %r6
	and %r6, %r14, %r15
	xor %r12, %r12, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r16
	or %r6, %r6, %r15
	xor %r14, %r14, %r6
	xor %r15, %r15, %r5
	xor %r16, %r16, %r0
	or %r0, %r18, %r19
	and %r5, %r19, %r20
	and %r6, %r17, %r18
	xor %r18, %r18, %r5
	or %r5, %r21, %r17
	xor %r17, %r17, %r0
	ld %r0, 24(%r4)
	xor %r20, %r20, %r0
	and %r0, %r20, %r21
	xor %r19, %r19, %r0
	xor %r20, %r20, %r5
	xor %r21, %r21, %r6
	and %r0, %r23, %r24
	or %r5, %r24, %r25
	or %r6, %r22, %r23
	xor %r23, %r23, %r5
	and %r5, %r26, %r22
	xor %r22, %r22, %r0
	ld %r0, 24(%r4)
	xor %r25, %r25, %r0
	or %r0, %r25, %r26
	xor %r24, %r24, %r0
	xor %r25, %r25, %r5
	xor %r26, %r26, %r6
	or %r0, %r29, %r30
	and %r5, %r30, %r31
	or %r6, %r31, %r27
	xor %r30, %r30, %r6
	and %r6, %r27, %r28
	xor %r31, %r31, %r6
	ld %r6, 24(%r4)
	xor %r28, %r28, %r6
	and %r6, %r28, %r29
	xor %r27, %r27, %r6
	xor %r28, %r28, %r0
	xor %r29, %r29, %r5
	lis %r5, 0
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 138
	xor %r2, %r2, %r5
	xor %r0, %r2, %r11
	xor %r0, %r0, %r17
	xor %r0, %r0, %r22
	xor %r0, %r0, %r27
	xor %r5, %r7, %r12
	xor %r5, %r5, %r18
	xor %r5, %r5, %r23
	xor %r5, %r5, %r28
	xor %r6, %r8, %r14
	xor %r6, %r6, %r19
	xor %r6, %r6, %r24
	xor %r6, %r6, %r29
	std %r9, 0(%r4)
	xor %r9, %r9, %r15
	xor %r9, %r9, %r20
	xor %r9, %r9, %r25
	xor %r9, %r9, %r30
	std %r10, 8(%r4)
	xor %r10, %r10, %r16
	xor %r10, %r10, %r21
	xor %r10, %r10, %r26
	xor %r10, %r10, %r31
	std %r16, 16(%r4)
	rldicl %r16, %r6, 1, 0
	xor %r16, %r16, %r0
	xor %r7, %r7, %r16
	xor %r12, %r12, %r16
	xor %r18, %r18, %r16
	xor %r23, %r23, %r16
	xor %r28, %r28, %r16
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r9
	xor %r21, %r21, %r0
	xor %r26, %r26, %r0
	xor %r31, %r31, %r0
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r5
	xor %r8, %r8, %r9
	xor %r14, %r14, %r9
	xor %r19, %r19, %r9
	xor %r24, %r24, %r9
	xor %r29, %r29, %r9
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r10
	xor %r2, %r2, %r5
	xor %r11, %r11, %r5
	xor %r17, %r17, %r5
	xor %r22, %r22, %r5
	xor %r27, %r27, %r5
	rldicl %r10, %r10, 1, 0
	xor %r10, %r10, %r6
	xor %r15, %r15, %r10
	xor %r20, %r20, %r10
	xor %r25, %r25, %r10
	xor %r30, %r30, %r10
	ld %r5, 8(%r4)
	xor %r5, %r5, %r0
	ld %r6, 0(%r4)
	xor %r6, %r6, %r10
	ld %r16, 16(%r4)
	xor %r0, %r0, %r16
	rldicl %r9, %r25, 21, 0
	rldicl %r25, %r24, 15, 0
	rldicl %r24, %r18, 10, 0
	rldicl %r18, %r14, 6, 0
	rldicl %r14, %r17, 3, 0
	rldicl %r17, %r7, 1, 0
	rldicl %r7, %r12, 44, 0
	rldicl %r12, %r0, 20, 0
	rldicl %r10, %r31, 14, 0
	rldicl %r31, %r28, 2, 0
	rldicl %r28, %r15, 55, 0
	rldicl %r15, %r23, 45, 0
	rldicl %r23, %r11, 36, 0
	rldicl %r11, %r6, 28, 0
	rldicl %r16, %r29, 61, 0
	rldicl %r29, %r21, 39, 0
	rldicl %r21, %r27, 18, 0
	rldicl %r27, %r8, 62, 0
	rldicl %r8, %r19, 43, 0
	rldicl %r19, %r20, 25, 0
	rldicl %r20, %r26, 8, 0
	rldicl %r26, %r30, 56, 0
	rldicl %r30, %r22, 41, 0
	rldicl %r22, %r5, 27, 0
	and %r0, %r2, %r7
	or %r5, %r10, %r2
	or %r6, %r7, %r8
	xor %r2, %r2, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r8
	or %r6, %r6, %r9
	xor %r7, %r7, %r6
	and %r6, %r9, %r10
	xor %r8, %r8, %r6
	xor %r9, %r9, %r5
	xor %r10, %r10, %r0
	and %r0, %r11, %r12
	or %r5, %r16, %r11
	or %r6, %r12, %r14
	xor %r11, %r11, %r6
	and %r6, %r14, %r15
	xor %r12, %r12, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r16
	or %r6, %r6, %r15
	xor %r14, %r14, %r6
	xor %r15, %r15, %r5
	xor %r16, %r16, %r0
	or %r0, %r18, %r19
	and %r5, %r19, %r20
	and %r6, %r17, %r18
	xor %r18, %r18, %r5
	or %r5, %r21, %r17
	xor %r17, %r17, %r0
	ld %r0, 24(%r4)
	xor %r20, %r20, %r0
	and %r0, %r20, %r21
	xor %r19, %r19, %r0
	xor %r20, %r20, %r5
	xor %r21, %r21, %r6
	and %r0, %r23, %r24
	or %r5, %r24, %r25
	or %r6, %r22, %r23
	xor %r23, %r23, %r5
	and %r5, %r26, %r22
	xor %r22, %r22, %r0
	ld %r0, 24(%r4)
	xor %r25, %r25, %r0
	or %r0, %r25, %r26
	xor %r24, %r24, %r0
	xor %r25, %r25, %r5
	xor %r26, %r26, %r6
	or %r0, %r29, %r30
	and %r5, %r30, %r31
	or %r6, %r31, %r27
	xor %r30, %r30, %r6
	and %r6, %r27, %r28
	xor %r31, %r31, %r6
	ld %r6, 24(%r4)
	xor %r28, %r28, %r6
	and %r6, %r28, %r29
	xor %r27, %r27, %r6
	xor %r28, %r28, %r0
	xor %r29, %r29, %r5
	lis %r5, 0
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 136
	xor %r2, %r2, %r5
	xor %r0, %r2, %r11
	xor %r0, %r0, %r17
	xor %r0, %r0, %r22
	xor %r0, %r0, %r27
	xor %r5, %r7, %r12
	xor %r5, %r5, %r18
	xor %r5, %r5, %r23
	xor %r5, %r5, %r28
	xor %r6, %r8, %r14
	xor %r6, %r6, %r19
	xor %r6, %r6, %r24
	xor %r6, %r6, %r29
	std %r9, 0(%r4)
	xor %r9, %r9, %r15
	xor %r9, %r9, %r20
	xor %r9, %r9, %r25
	xor %r9, %r9, %r30
	std %r10, 8(%r4)
	xor %r10, %r10, %r16
	xor %r10, %r10, %r21
	xor %r10, %r10, %r26
	xor %r10, %r10, %r31
	std %r16, 16(%r4)
	rldicl %r16, %r6, 1, 0
	xor %r16, %r16, %r0
	xor %r7, %r7, %r16
	xor %r12, %r12, %r16
	xor %r18, %r18, %r16
	xor %r23, %r23, %r16
	xor %r28, %r28, %r16
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r9
	xor %r21, %r21, %r0
	xor %r26, %r26, %r0
	xor %r31, %r31, %r0
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r5
	xor %r8, %r8, %r9
	xor %r14, %r14, %r9
	xor %r19, %r19, %r9
	xor %r24, %r24, %r9
	xor %r29, %r29, %r9
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r10
	xor %r2, %r2, %r5
	xor %r11, %r11, %r5
	xor %r17, %r17, %r5
	xor %r22, %r22, %r5
	xor %r27, %r27, %r5
	rldicl %r10, %r10, 1, 0
	xor %r10, %r10, %r6
	xor %r15, %r15, %r10
	xor %r20, %r20, %r10
	xor %r25, %r25, %r10
	xor %r30, %r30, %r10
	ld %r5, 8(%r4)
	xor %r5, %r5, %r0
	ld %r6, 0(%r4)
	xor %r6, %r6, %r10
	ld %r16, 16(%r4)
	xor %r0, %r0, %r16
	rldicl %r9, %r25, 21, 0
	rldicl %r25, %r24, 15, 0
	rldicl %r24, %r18, 10, 0
	rldicl %r18, %r14, 6, 0
	rldicl %r14, %r17, 3, 0
	rldicl %r17, %r7, 1, 0
	rldicl %r7, %r12, 44, 0
	rldicl %r12, %r0, 20, 0
	rldicl %r10, %r31, 14, 0
	rldicl %r31, %r28, 2, 0
	rldicl %r28, %r15, 55, 0
	rldicl %r15, %r23, 45, 0
	rldicl %r23, %r11, 36, 0
	rldicl %r11, %r6, 28, 0
	rldicl %r16, %r29, 61, 0
	rldicl %r29, %r21, 39, 0
	rldicl %r21, %r27, 18, 0
	rldicl %r27, %r8, 62, 0
	rldicl %r8, %r19, 43, 0
	rldicl %r19, %r20, 25, 0
	rldicl %r20, %r26, 8, 0
	rldicl %r26, %r30, 56, 0
	rldicl %r30, %r22, 41, 0
	rldicl %r22, %r5, 27, 0
	and %r0, %r2, %r7
	or %r5, %r10, %r2
	or %r6, %r7, %r8
	xor %r2, %r2, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r8
	or %r6, %r6, %r9
	xor %r7, %r7, %r6
	and %r6, %r9, %r10
	xor %r8, %r8, %r6
	xor %r9, %r9, %r5
	xor %r10, %r10, %r0
	and %r0, %r11, %r12
	or %r5, %r16, %r11
	or %r6, %r12, %r14
	xor %r11, %r11, %r6
	and %r6, %r14, %r15
	xor %r12, %r12, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r16
	or %r6, %r6, %r15
	xor %r14, %r14, %r6
	xor %r15, %r15, %r5
	xor %r16, %r16, %r0
	or %r0, %r18, %r19
	and %r5, %r19, %r20
	and %r6, %r17, %r18
	xor %r18, %r18, %r5
	or %r5, %r21, %r17
	xor %r17, %r17, %r0
	ld %r0, 24(%r4)
	xor %r20, %r20, %r0
	and %r0, %r20, %r21
	xor %r19, %r19, %r0
	xor %r20, %r20, %r5
	xor %r21, %r21, %r6
	and %r0, %r23, %r24
	or %r5, %r24, %r25
	or %r6, %r22, %r23
	xor %r23, %r23, %r5
	and %r5, %r26, %r22
	xor %r22, %r22, %r0
	ld %r0, 24(%r4)
	xor %r25, %r25, %r0
	or %r0, %r25, %r26
	xor %r24, %r24, %r0
	xor %r25, %r25, %r5
	xor %r26, %r26, %r6
	or %r0, %r29, %r30
	and %r5, %r30, %r31
	or %r6, %r31, %r27
	xor %r30, %r30, %r6
	and %r6, %r27, %r28
	xor %r31, %r31, %r6
	ld %r6, 24(%r4)
	xor %r28, %r28, %r6
	and %r6, %r28, %r29
	xor %r27, %r27, %r6
	xor %r28, %r28, %r0
	xor %r29, %r29, %r5
	lis %r5, 0
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 32768
	ori %r5, %r5, 32777
	xor %r2, %r2, %r5
	xor %r0, %r2, %r11
	xor %r0, %r0, %r17
	xor %r0, %r0, %r22
	xor %r0, %r0, %r27
	xor %r5, %r7, %r12
	xor %r5, %r5, %r18
	xor %r5, %r5, %r23
	xor %r5, %r5, %r28
	xor %r6, %r8, %r14
	xor %r6, %r6, %r19
	xor %r6, %r6, %r24
	xor %r6, %r6, %r29
	std %r9, 0(%r4)
	xor %r9, %r9, %r15
	xor %r9, %r9, %r20
	xor %r9, %r9, %r25
	xor %r9, %r9, %r30
	std %r10, 8(%r4)
	xor %r10, %r10, %r16
	xor %r10, %r10, %r21
	xor %r10, %r10, %r26
	xor %r10, %r10, %r31
	std %r16, 16(%r4)
	rldicl %r16, %r6, 1, 0
	xor %r16, %r16, %r0
	xor %r7, %r7, %r16
	xor %r12, %r12, %r16
	xor %r18, %r18, %r16
	xor %r23, %r23, %r16
	xor %r28, %r28, %r16
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r9
	xor %r21, %r21, %r0
	xor %r26, %r26, %r0
	xor %r31, %r31, %r0
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r5
	xor %r8, %r8, %r9
	xor %r14, %r14, %r9
	xor %r19, %r19, %r9
	xor %r24, %r24, %r9
	xor %r29, %r29, %r9
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r10
	xor %r2, %r2, %r5
	xor %r11, %r11, %r5
	xor %r17, %r17, %r5
	xor %r22, %r22, %r5
	xor %r27, %r27, %r5
	rldicl %r10, %r10, 1, 0
	xor %r10, %r10, %r6
	xor %r15, %r15, %r10
	xor %r20, %r20, %r10
	xor %r25, %r25, %r10
	xor %r30, %r30, %r10
	ld %r5, 8(%r4)
	xor %r5, %r5, %r0
	ld %r6, 0(%r4)
	xor %r6, %r6, %r10
	ld %r16, 16(%r4)
	xor %r0, %r0, %r16
	rldicl %r9, %r25, 21, 0
	rldicl %r25, %r24, 15, 0
	rldicl %r24, %r18, 10, 0
	rldicl %r18, %r14, 6, 0
	rldicl %r14, %r17, 3, 0
	rldicl %r17, %r7, 1, 0
	rldicl %r7, %r12, 44, 0
	rldicl %r12, %r0, 20, 0
	rldicl %r10, %r31, 14, 0
	rldicl %r31, %r28, 2, 0
	rldicl %r28, %r15, 55, 0
	rldicl %r15, %r23, 45, 0
	rldicl %r23, %r11, 36, 0
	rldicl %r11, %r6, 28, 0
	rldicl %r16, %r29, 61, 0
	rldicl %r29, %r21, 39, 0
	rldicl %r21, %r27, 18, 0
	rldicl %r27, %r8, 62, 0
	rldicl %r8, %r19, 43, 0
	rldicl %r19, %r20, 25, 0
	rldicl %r20, %r26, 8, 0
	rldicl %r26, %r30, 56, 0
	rldicl %r30, %r22, 41, 0
	rldicl %r22, %r5, 27, 0
	and %r0, %r2, %r7
	or %r5, %r10, %r2
	or %r6, %r7, %r8
	xor %r2, %r2, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r8
	or %r6, %r6, %r9
	xor %r7, %r7, %r6
	and %r6, %r9, %r10
	xor %r8, %r8, %r6
	xor %r9, %r9, %r5
	xor %r10, %r10, %r0
	and %r0, %r11, %r12
	or %r5, %r16, %r11
	or %r6, %r12, %r14
	xor %r11, %r11, %r6
	and %r6, %r14, %r15
	xor %r12, %r12, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r16
	or %r6, %r6, %r15
	xor %r14, %r14, %r6
	xor %r15, %r15, %r5
	xor %r16, %r16, %r0
	or %r0, %r18, %r19
	and %r5, %r19, %r20
	and %r6, %r17, %r18
	xor %r18, %r18, %r5
	or %r5, %r21, %r17
	xor %r17, %r17, %r0
	ld %r0, 24(%r4)
	xor %r20, %r20, %r0
	and %r0, %r20, %r21
	xor %r19, %r19, %r0
	xor %r20, %r20, %r5
	xor %r21, %r21, %r6
	and %r0, %r23, %r24
	or %r5, %r24, %r25
	or %r6, %r22, %r23
	xor %r23, %r23, %r5
	and %r5, %r26, %r22
	xor %r22, %r22, %r0
	ld %r0, 24(%r4)
	xor %r25, %r25, %r0
	or %r0, %r25, %r26
	xor %r24, %r24, %r0
	xor %r25, %r25, %r5
	xor %r26, %r26, %r6
	or %r0, %r29, %r30
	and %r5, %r30, %r31
	or %r6, %r31, %r27
	xor %r30, %r30, %r6
	and %r6, %r27, %r28
	xor %r31, %r31, %r6
	ld %r6, 24(%r4)
	xor %r28, %r28, %r6
	and %r6, %r28, %r29
	xor %r27, %r27, %r6
	xor %r28, %r28, %r0
	xor %r29, %r29, %r5
	lis %r5, 0
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 32768
	ori %r5, %r5, 10
	xor %r2, %r2, %r5
	xor %r0, %r2, %r11
	xor %r0, %r0, %r17
	xor %r0, %r0, %r22
	xor %r0, %r0, %r27
	xor %r5, %r7, %r12
	xor %r5, %r5, %r18
	xor %r5, %r5, %r23
	xor %r5, %r5, %r28
	xor %r6, %r8, %r14
	xor %r6, %r6, %r19
	xor %r6, %r6, %r24
	xor %r6, %r6, %r29
	std %r9, 0(%r4)
	xor %r9, %r9, %r15
	xor %r9, %r9, %r20
	xor %r9, %r9, %r25
	xor %r9, %r9, %r30
	std %r10, 8(%r4)
	xor %r10, %r10, %r16
	xor %r10, %r10, %r21
	xor %r10, %r10, %r26
	xor %r10, %r10, %r31
	std %r16, 16(%r4)
	rldicl %r16, %r6, 1, 0
	xor %r16, %r16, %r0
	xor %r7, %r7, %r16
	xor %r12, %r12, %r16
	xor %r18, %r18, %r16
	xor %r23, %r23, %r16
	xor %r28, %r28, %r16
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r9
	xor %r21, %r21, %r0
	xor %r26, %r26, %r0
	xor %r31, %r31, %r0
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r5
	xor %r8, %r8, %r9
	xor %r14, %r14, %r9
	xor %r19, %r19, %r9
	xor %r24, %r24, %r9
	xor %r29, %r29, %r9
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r10
	xor %r2, %r2, %r5
	xor %r11, %r11, %r5
	xor %r17, %r17, %r5
	xor %r22, %r22, %r5
	xor %r27, %r27, %r5
	rldicl %r10, %r10, 1, 0
	xor %r10, %r10, %r6
	xor %r15, %r15, %r10
	xor %r20, %r20, %r10
	xor %r25, %r25, %r10
	xor %r30, %r30, %r10
	ld %r5, 8(%r4)
	xor %r5, %r5, %r0
	ld %r6, 0(%r4)
	xor %r6, %r6, %r10
	ld %r16, 16(%r4)
	xor %r0, %r0, %r16
	rldicl %r9, %r25, 21, 0
	rldicl %r25, %r24, 15, 0
	rldicl %r24, %r18, 10, 0
	rldicl %r18, %r14, 6, 0
	rldicl %r14, %r17, 3, 0
	rldicl %r17, %r7, 1, 0
	rldicl %r7, %r12, 44, 0
	rldicl %r12, %r0, 20, 0
	rldicl %r10, %r31, 14, 0
	rldicl %r31, %r28, 2, 0
	rldicl %r28, %r15, 55, 0
	rldicl %r15, %r23, 45, 0
	rldicl %r23, %r11, 36, 0
	rldicl %r11, %r6, 28, 0
	rldicl %r16, %r29, 61, 0
	rldicl %r29, %r21, 39, 0
	rldicl %r21, %r27, 18, 0
	rldicl %r27, %r8, 62, 0
	rldicl %r8, %r19, 43, 0
	rldicl %r19, %r20, 25, 0
	rldicl %r20, %r26, 8, 0
	rldicl %r26, %r30, 56, 0
	rldicl %r30, %r22, 41, 0
	rldicl %r22, %r5, 27, 0
	and %r0, %r2, %r7
	or %r5, %r10, %r2
	or %r6, %r7, %r8
	xor %r2, %r2, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r8
	or %r6, %r6, %r9
	xor %r7, %r7, %r6
	and %r6, %r9, %r10
	xor %r8, %r8, %r6
	xor %r9, %r9, %r5
	xor %r10, %r10, %r0
	and %r0, %r11, %r12
	or %r5, %r16, %r11
	or %r6, %r12, %r14
	xor %r11, %r11, %r6
	and %r6, %r14, %r15
	xor %r12, %r12, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r16
	or %r6, %r6, %r15
	xor %r14, %r14, %r6
	xor %r15, %r15, %r5
	xor %r16, %r16, %r0
	or %r0, %r18, %r19
	and %r5, %r19, %r20
	and %r6, %r17, %r18
	xor %r18, %r18, %r5
	or %r5, %r21, %r17
	xor %r17, %r17, %r0
	ld %r0, 24(%r4)
	xor %r20, %r20, %r0
	and %r0, %r20, %r21
	xor %r19, %r19, %r0
	xor %r20, %r20, %r5
	xor %r21, %r21, %r6
	and %r0, %r23, %r24
	or %r5, %r24, %r25
	or %r6, %r22, %r23
	xor %r23, %r23, %r5
	and %r5, %r26, %r22
	xor %r22, %r22, %r0
	ld %r0, 24(%r4)
	xor %r25, %r25, %r0
	or %r0, %r25, %r26
	xor %r24, %r24, %r0
	xor %r25, %r25, %r5
	xor %r26, %r26, %r6
	or %r0, %r29, %r30
	and %r5, %r30, %r31
	or %r6, %r31, %r27
	xor %r30, %r30, %r6
	and %r6, %r27, %r28
	xor %r31, %r31, %r6
	ld %r6, 24(%r4)
	xor %r28, %r28, %r6
	and %r6, %r28, %r29
	xor %r27, %r27, %r6
	xor %r28, %r28, %r0
	xor %r29, %r29, %r5
	lis %r5, 0
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 32768
	ori %r5, %r5, 32907
	xor %r2, %r2, %r5
	xor %r0, %r2, %r11
	xor %r0, %r0, %r17
	xor %r0, %r0, %r22
	xor %r0, %r0, %r27
	xor %r5, %r7, %r12
	xor %r5, %r5, %r18
	xor %r5, %r5, %r23
	xor %r5, %r5, %r28
	xor %r6, %r8, %r14
	xor %r6, %r6, %r19
	xor %r6, %r6, %r24
	xor %r6, %r6, %r29
	std %r9, 0(%r4)
	xor %r9, %r9, %r15
	xor %r9, %r9, %r20
	xor %r9, %r9, %r25
	xor %r9, %r9, %r30
	std %r10, 8(%r4)
	xor %r10, %r10, %r16
	xor %r10, %r10, %r21
	xor %r10, %r10, %r26
	xor %r10, %r10, %r31
	std %r16, 16(%r4)
	rldicl %r16, %r6, 1, 0
	xor %r16, %r16, %r0
	xor %r7, %r7, %r16
	xor %r12, %r12, %r16
	xor %r18, %r18, %r16
	xor %r23, %r23, %r16
	xor %r28, %r28, %r16
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r9
	xor %r21, %r21, %r0
	xor %r26, %r26, %r0
	xor %r31, %r31, %r0
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r5
	xor %r8, %r8, %r9
	xor %r14, %r14, %r9
	xor %r19, %r19, %r9
	xor %r24, %r24, %r9
	xor %r29, %r29, %r9
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r10
	xor %r2, %r2, %r5
	xor %r11, %r11, %r5
	xor %r17, %r17, %r5
	xor %r22, %r22, %r5
	xor %r27, %r27, %r5
	rldicl %r10, %r10, 1, 0
	xor %r10, %r10, %r6
	xor %r15, %r15, %r10
	xor %r20, %r20, %r10
	xor %r25, %r25, %r10
	xor %r30, %r30, %r10
	ld %r5, 8(%r4)
	xor %r5, %r5, %r0
	ld %r6, 0(%r4)
	xor %r6, %r6, %r10
	ld %r16, 16(%r4)
	xor %r0, %r0, %r16
	rldicl %r9, %r25, 21, 0
	rldicl %r25, %r24, 15, 0
	rldicl %r24, %r18, 10, 0
	rldicl %r18, %r14, 6, 0
	rldicl %r14, %r17, 3, 0
	rldicl %r17, %r7, 1, 0
	rldicl %r7, %r12, 44, 0
	rldicl %r12, %r0, 20, 0
	rldicl %r10, %r31, 14, 0
	rldicl %r31, %r28, 2, 0
	rldicl %r28, %r15, 55, 0
	rldicl %r15, %r23, 45, 0
	rldicl %r23, %r11, 36, 0
	rldicl %r11, %r6, 28, 0
	rldicl %r16, %r29, 61, 0
	rldicl %r29, %r21, 39, 0
	rldicl %r21, %r27, 18, 0
	rldicl %r27, %r8, 62, 0
	rldicl %r8, %r19, 43, 0
	rldicl %r19, %r20, 25, 0
	rldicl %r20, %r26, 8, 0
	rldicl %r26, %r30, 56, 0
	rldicl %r30, %r22, 41, 0
	rldicl %r22, %r5, 27, 0
	and %r0, %r2, %r7
	or %r5, %r10, %r2
	or %r6, %r7, %r8
	xor %r2, %r2, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r8
	or %r6, %r6, %r9
	xor %r7, %r7, %r6
	and %r6, %r9, %r10
	xor %r8, %r8, %r6
	xor %r9, %r9, %r5
	xor %r10, %r10, %r0
	and %r0, %r11, %r12
	or %r5, %r16, %r11
	or %r6, %r12, %r14
	xor %r11, %r11, %r6
	and %r6, %r14, %r15
	xor %r12, %r12, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r16
	or %r6, %r6, %r15
	xor %r14, %r14, %r6
	xor %r15, %r15, %r5
	xor %r16, %r16, %r0
	or %r0, %r18, %r19
	and %r5, %r19, %r20
	and %r6, %r17, %r18
	xor %r18, %r18, %r5
	or %r5, %r21, %r17
	xor %r17, %r17, %r0
	ld %r0, 24(%r4)
	xor %r20, %r20, %r0
	and %r0, %r20, %r21
	xor %r19, %r19, %r0
	xor %r20, %r20, %r5
	xor %r21, %r21, %r6
	and %r0, %r23, %r24
	or %r5, %r24, %r25
	or %r6, %r22, %r23
	xor %r23, %r23, %r5
	and %r5, %r26, %r22
	xor %r22, %r22, %r0
	ld %r0, 24(%r4)
	xor %r25, %r25, %r0
	or %r0, %r25, %r26
	xor %r24, %r24, %r0
	xor %r25, %r25, %r5
	xor %r26, %r26, %r6
	or %r0, %r29, %r30
	and %r5, %r30, %r31
	or %r6, %r31, %r27
	xor %r30, %r30, %r6
	and %r6, %r27, %r28
	xor %r31, %r31, %r6
	ld %r6, 24(%r4)
	xor %r28, %r28, %r6
	and %r6, %r28, %r29
	xor %r27, %r27, %r6
	xor %r28, %r28, %r0
	xor %r29, %r29, %r5
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 139
	xor %r2, %r2, %r5
	xor %r0, %r2, %r11
	xor %r0, %r0, %r17
	xor %r0, %r0, %r22
	xor %r0, %r0, %r27
	xor %r5, %r7, %r12
	xor %r5, %r5, %r18
	xor %r5, %r5, %r23
	xor %r5, %r5, %r28
	xor %r6, %r8, %r14
	xor %r6, %r6, %r19
	xor %r6, %r6, %r24
	xor %r6, %r6, %r29
	std %r9, 0(%r4)
	xor %r9, %r9, %r15
	xor %r9, %r9, %r20
	xor %r9, %r9, %r25
	xor %r9, %r9, %r30
	std %r10, 8(%r4)
	xor %r10, %r10, %r16
	xor %r10, %r10, %r21
	xor %r10, %r10, %r26
	xor %r10, %r10, %r31
	std %r16, 16(%r4)
	rldicl %r16, %r6, 1, 0
	xor %r16, %r16, %r0
	xor %r7, %r7, %r16
	xor %r12, %r12, %r16
	xor %r18, %r18, %r16
	xor %r23, %r23, %r16
	xor %r28, %r28, %r16
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r9
	xor %r21, %r21, %r0
	xor %r26, %r26, %r0
	xor %r31, %r31, %r0
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r5
	xor %r8, %r8, %r9
	xor %r14, %r14, %r9
	xor %r19, %r19, %r9
	xor %r24, %r24, %r9
	xor %r29, %r29, %r9
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r10
	xor %r2, %r2, %r5
	xor %r11, %r11, %r5
	xor %r17, %r17, %r5
	xor %r22, %r22, %r5
	xor %r27, %r27, %r5
	rldicl %r10, %r10, 1, 0
	xor %r10, %r10, %r6
	xor %r15, %r15, %r10
	xor %r20, %r20, %r10
	xor %r25, %r25, %r10
	xor %r30, %r30, %r10
	ld %r5, 8(%r4)
	xor %r5, %r5, %r0
	ld %r6, 0(%r4)
	xor %r6, %r6, %r10
	ld %r16, 16(%r4)
	xor %r0, %r0, %r16
	rldicl %r9, %r25, 21, 0
	rldicl %r25, %r24, 15, 0
	rldicl %r24, %r18, 10, 0
	rldicl %r18, %r14, 6, 0
	rldicl %r14, %r17, 3, 0
	rldicl %r17, %r7, 1, 0
	rldicl %r7, %r12, 44, 0
	rldicl %r12, %r0, 20, 0
	rldicl %r10, %r31, 14, 0
	rldicl %r31, %r28, 2, 0
	rldicl %r28, %r15, 55, 0
	rldicl %r15, %r23, 45, 0
	rldicl %r23, %r11, 36, 0
	rldicl %r11, %r6, 28, 0
	rldicl %r16, %r29, 61, 0
	rldicl %r29, %r21, 39, 0
	rldicl %r21, %r27, 18, 0
	rldicl %r27, %r8, 62, 0
	rldicl %r8, %r19, 43, 0
	rldicl %r19, %r20, 25, 0
	rldicl %r20, %r26, 8, 0
	rldicl %r26, %r30, 56, 0
	rldicl %r30, %r22, 41, 0
	rldicl %r22, %r5, 27, 0
	and %r0, %r2, %r7
	or %r5, %r10, %r2
	or %r6, %r7, %r8
	xor %r2, %r2, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r8
	or %r6, %r6, %r9
	xor %r7, %r7, %r6
	and %r6, %r9, %r10
	xor %r8, %r8, %r6
	xor %r9, %r9, %r5
	xor %r10, %r10, %r0
	and %r0, %r11, %r12
	or %r5, %r16, %r11
	or %r6, %r12, %r14
	xor %r11, %r11, %r6
	and %r6, %r14, %r15
	xor %r12, %r12, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r16
	or %r6, %r6, %r15
	xor %r14, %r14, %r6
	xor %r15, %r15, %r5
	xor %r16, %r16, %r0
	or %r0, %r18, %r19
	and %r5, %r19, %r20
	and %r6, %r17, %r18
	xor %r18, %r18, %r5
	or %r5, %r21, %r17
	xor %r17, %r17, %r0
	ld %r0, 24(%r4)
	xor %r20, %r20, %r0
	and %r0, %r20, %r21
	xor %r19, %r19, %r0
	xor %r20, %r20, %r5
	xor %r21, %r21, %r6
	and %r0, %r23, %r24
	or %r5, %r24, %r25
	or %r6, %r22, %r23
	xor %r23, %r23, %r5
	and %r5, %r26, %r22
	xor %r22, %r22, %r0
	ld %r0, 24(%r4)
	xor %r25, %r25, %r0
	or %r0, %r25, %r26
	xor %r24, %r24, %r0
	xor %r25, %r25, %r5
	xor %r26, %r26, %r6
	or %r0, %r29, %r30
	and %r5, %r30, %r31
	or %r6, %r31, %r27
	xor %r30, %r30, %r6
	and %r6, %r27, %r28
	xor %r31, %r31, %r6
	ld %r6, 24(%r4)
	xor %r28, %r28, %r6
	and %r6, %r28, %r29
	xor %r27, %r27, %r6
	xor %r28, %r28, %r0
	xor %r29, %r29, %r5
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 32905
	xor %r2, %r2, %r5
	xor %r0, %r2, %r11
	xor %r0, %r0, %r17
	xor %r0, %r0, %r22
	xor %r0, %r0, %r27
	xor %r5, %r7, %r12
	xor %r5, %r5, %r18
	xor %r5, %r5, %r23
	xor %r5, %r5, %r28
	xor %r6, %r8, %r14
	xor %r6, %r6, %r19
	xor %r6, %r6, %r24
	xor %r6, %r6, %r29
	std %r9, 0(%r4)
	xor %r9, %r9, %r15
	xor %r9, %r9, %r20
	xor %r9, %r9, %r25
	xor %r9, %r9, %r30
	std %r10, 8(%r4)
	xor %r10, %r10, %r16
	xor %r10, %r10, %r21
	xor %r10, %r10, %r26
	xor %r10, %r10, %r31
	std %r16, 16(%r4)
	rldicl %r16, %r6, 1, 0
	xor %r16, %r16, %r0
	xor %r7, %r7, %r16
	xor %r12, %r12, %r16
	xor %r18, %r18, %r16
	xor %r23, %r23, %r16
	xor %r28, %r28, %r16
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r9
	xor %r21, %r21, %r0
	xor %r26, %r26, %r0
	xor %r31, %r31, %r0
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r5
	xor %r8, %r8, %r9
	xor %r14, %r14, %r9
	xor %r19, %r19, %r9
	xor %r24, %r24, %r9
	xor %r29, %r29, %r9
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r10
	xor %r2, %r2, %r5
	xor %r11, %r11, %r5
	xor %r17, %r17, %r5
	xor %r22, %r22, %r5
	xor %r27, %r27, %r5
	rldicl %r10, %r10, 1, 0
	xor %r10, %r10, %r6
	xor %r15, %r15, %r10
	xor %r20, %r20, %r10
	xor %r25, %r25, %r10
	xor %r30, %r30, %r10
	ld %r5, 8(%r4)
	xor %r5, %r5, %r0
	ld %r6, 0(%r4)
	xor %r6, %r6, %r10
	ld %r16, 16(%r4)
	xor %r0, %r0, %r16
	rldicl %r9, %r25, 21, 0
	rldicl %r25, %r24, 15, 0
	rldicl %r24, %r18, 10, 0
	rldicl %r18, %r14, 6, 0
	rldicl %r14, %r17, 3, 0
	rldicl %r17, %r7, 1, 0
	rldicl %r7, %r12, 44, 0
	rldicl %r12, %r0, 20, 0
	rldicl %r10, %r31, 14, 0
	rldicl %r31, %r28, 2, 0
	rldicl %r28, %r15, 55, 0
	rldicl %r15, %r23, 45, 0
	rldicl %r23, %r11, 36, 0
	rldicl %r11, %r6, 28, 0
	rldicl %r16, %r29, 61, 0
	rldicl %r29, %r21, 39, 0
	rldicl %r21, %r27, 18, 0
	rldicl %r27, %r8, 62, 0
	rldicl %r8, %r19, 43, 0
	rldicl %r19, %r20, 25, 0
	rldicl %r20, %r26, 8, 0
	rldicl %r26, %r30, 56, 0
	rldicl %r30, %r22, 41, 0
	rldicl %r22, %r5, 27, 0
	and %r0, %r2, %r7
	or %r5, %r10, %r2
	or %r6, %r7, %r8
	xor %r2, %r2, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r8
	or %r6, %r6, %r9
	xor %r7, %r7, %r6
	and %r6, %r9, %r10
	xor %r8, %r8, %r6
	xor %r9, %r9, %r5
	xor %r10, %r10, %r0
	and %r0, %r11, %r12
	or %r5, %r16, %r11
	or %r6, %r12, %r14
	xor %r11, %r11, %r6
	and %r6, %r14, %r15
	xor %r12, %r12, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r16
	or %r6, %r6, %r15
	xor %r14, %r14, %r6
	xor %r15, %r15, %r5
	xor %r16, %r16, %r0
	or %r0, %r18, %r19
	and %r5, %r19, %r20
	and %r6, %r17, %r18
	xor %r18, %r18, %r5
	or %r5, %r21, %r17
	xor %r17, %r17, %r0
	ld %r0, 24(%r4)
	xor %r20, %r20, %r0
	and %r0, %r20, %r21
	xor %r19, %r19, %r0
	xor %r20, %r20, %r5
	xor %r21, %r21, %r6
	and %r0, %r23, %r24
	or %r5, %r24, %r25
	or %r6, %r22, %r23
	xor %r23, %r23, %r5
	and %r5, %r26, %r22
	xor %r22, %r22, %r0
	ld %r0, 24(%r4)
	xor %r25, %r25, %r0
	or %r0, %r25, %r26
	xor %r24, %r24, %r0
	xor %r25, %r25, %r5
	xor %r26, %r26, %r6
	or %r0, %r29, %r30
	and %r5, %r30, %r31
	or %r6, %r31, %r27
	xor %r30, %r30, %r6
	and %r6, %r27, %r28
	xor %r31, %r31, %r6
	ld %r6, 24(%r4)
	xor %r28, %r28, %r6
	and %r6, %r28, %r29
	xor %r27, %r27, %r6
	xor %r28, %r28, %r0
	xor %r29, %r29, %r5
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 32771
	xor %r2, %r2, %r5
	xor %r0, %r2, %r11
	xor %r0, %r0, %r17
	xor %r0, %r0, %r22
	xor %r0, %r0, %r27
	xor %r5, %r7, %r12
	xor %r5, %r5, %r18
	xor %r5, %r5, %r23
	xor %r5, %r5, %r28
	xor %r6, %r8, %r14
	xor %r6, %r6, %r19
	xor %r6, %r6, %r24
	xor %r6, %r6, %r29
	std %r9, 0(%r4)
	xor %r9, %r9, %r15
	xor %r9, %r9, %r20
	xor %r9, %r9, %r25
	xor %r9, %r9, %r30
	std %r10, 8(%r4)
	xor %r10, %r10, %r16
	xor %r10, %r10, %r21
	xor %r10, %r10, %r26
	xor %r10, %r10, %r31
	std %r16, 16(%r4)
	rldicl %r16, %r6, 1, 0
	xor %r16, %r16, %r0
	xor %r7, %r7, %r16
	xor %r12, %r12, %r16
	xor %r18, %r18, %r16
	xor %r23, %r23, %r16
	xor %r28, %r28, %r16
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r9
	xor %r21, %r21, %r0
	xor %r26, %r26, %r0
	xor %r31, %r31, %r0
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r5
	xor %r8, %r8, %r9
	xor %r14, %r14, %r9
	xor %r19, %r19, %r9
	xor %r24, %r24, %r9
	xor %r29, %r29, %r9
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r10
	xor %r2, %r2, %r5
	xor %r11, %r11, %r5
	xor %r17, %r17, %r5
	xor %r22, %r22, %r5
	xor %r27, %r27, %r5
	rldicl %r10, %r10, 1, 0
	xor %r10, %r10, %r6
	xor %r15, %r15, %r10
	xor %r20, %r20, %r10
	xor %r25, %r25, %r10
	xor %r30, %r30, %r10
	ld %r5, 8(%r4)
	xor %r5, %r5, %r0
	ld %r6, 0(%r4)
	xor %r6, %r6, %r10
	ld %r16, 16(%r4)
	xor %r0, %r0, %r16
	rldicl %r9, %r25, 21, 0
	rldicl %r25, %r24, 15, 0
	rldicl %r24, %r18, 10, 0
	rldicl %r18, %r14, 6, 0
	rldicl %r14, %r17, 3, 0
	rldicl %r17, %r7, 1, 0
	rldicl %r7, %r12, 44, 0
	rldicl %r12, %r0, 20, 0
	rldicl %r10, %r31, 14, 0
	rldicl %r31, %r28, 2, 0
	rldicl %r28, %r15, 55, 0
	rldicl %r15, %r23, 45, 0
	rldicl %r23, %r11, 36, 0
	rldicl %r11, %r6, 28, 0
	rldicl %r16, %r29, 61, 0
	rldicl %r29, %r21, 39, 0
	rldicl %r21, %r27, 18, 0
	rldicl %r27, %r8, 62, 0
	rldicl %r8, %r19, 43, 0
	rldicl %r19, %r20, 25, 0
	rldicl %r20, %r26, 8, 0
	rldicl %r26, %r30, 56, 0
	rldicl %r30, %r22, 41, 0
	rldicl %r22, %r5, 27, 0
	and %r0, %r2, %r7
	or %r5, %r10, %r2
	or %r6, %r7, %r8
	xor %r2, %r2, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r8
	or %r6, %r6, %r9
	xor %r7, %r7, %r6
	and %r6, %r9, %r10
	xor %r8, %r8, %r6
	xor %r9, %r9, %r5
	xor %r10, %r10, %r0
	and %r0, %r11, %r12
	or %r5, %r16, %r11
	or %r6, %r12, %r14
	xor %r11, %r11, %r6
	and %r6, %r14, %r15
	xor %r12, %r12, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r16
	or %r6, %r6, %r15
	xor %r14, %r14, %r6
	xor %r15, %r15, %r5
	xor %r16, %r16, %r0
	or %r0, %r18, %r19
	and %r5, %r19, %r20
	and %r6, %r17, %r18
	xor %r18, %r18, %r5
	or %r5, %r21, %r17
	xor %r17, %r17, %r0
	ld %r0, 24(%r4)
	xor %r20, %r20, %r0
	and %r0, %r20, %r21
	xor %r19, %r19, %r0
	xor %r20, %r20, %r5
	xor %r21, %r21, %r6
	and %r0, %r23, %r24
	or %r5, %r24, %r25
	or %r6, %r22, %r23
	xor %r23, %r23, %r5
	and %r5, %r26, %r22
	xor %r22, %r22, %r0
	ld %r0, 24(%r4)
	xor %r25, %r25, %r0
	or %r0, %r25, %r26
	xor %r24, %r24, %r0
	xor %r25, %r25, %r5
	xor %r26, %r26, %r6
	or %r0, %r29, %r30
	and %r5, %r30, %r31
	or %r6, %r31, %r27
	xor %r30, %r30, %r6
	and %r6, %r27, %r28
	xor %r31, %r31, %r6
	ld %r6, 24(%r4)
	xor %r28, %r28, %r6
	and %r6, %r28, %r29
	xor %r27, %r27, %r6
	xor %r28, %r28, %r0
	xor %r29, %r29, %r5
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 32770
	xor %r2, %r2, %r5
	xor %r0, %r2, %r11
	xor %r0, %r0, %r17
	xor %r0, %r0, %r22
	xor %r0, %r0, %r27
	xor %r5, %r7, %r12
	xor %r5, %r5, %r18
	xor %r5, %r5, %r23
	xor %r5, %r5, %r28
	xor %r6, %r8, %r14
	xor %r6, %r6, %r19
	xor %r6, %r6, %r24
	xor %r6, %r6, %r29
	std %r9, 0(%r4)
	xor %r9, %r9, %r15
	xor %r9, %r9, %r20
	xor %r9, %r9, %r25
	xor %r9, %r9, %r30
	std %r10, 8(%r4)
	xor %r10, %r10, %r16
	xor %r10, %r10, %r21
	xor %r10, %r10, %r26
	xor %r10, %r10, %r31
	std %r16, 16(%r4)
	rldicl %r16, %r6, 1, 0
	xor %r16, %r16, %r0
	xor %r7, %r7, %r16
	xor %r12, %r12, %r16
	xor %r18, %r18, %r16
	xor %r23, %r23, %r16
	xor %r28, %r28, %r16
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r9
	xor %r21, %r21, %r0
	xor %r26, %r26, %r0
	xor %r31, %r31, %r0
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r5
	xor %r8, %r8, %r9
	xor %r14, %r14, %r9
	xor %r19, %r19, %r9
	xor %r24, %r24, %r9
	xor %r29, %r29, %r9
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r10
	xor %r2, %r2, %r5
	xor %r11, %r11, %r5
	xor %r17, %r17, %r5
	xor %r22, %r22, %r5
	xor %r27, %r27, %r5
	rldicl %r10, %r10, 1, 0
	xor %r10, %r10, %r6
	xor %r15, %r15, %r10
	xor %r20, %r20, %r10
	xor %r25, %r25, %r10
	xor %r30, %r30, %r10
	ld %r5, 8(%r4)
	xor %r5, %r5, %r0
	ld %r6, 0(%r4)
	xor %r6, %r6, %r10
	ld %r16, 16(%r4)
	xor %r0, %r0, %r16
	rldicl %r9, %r25, 21, 0
	rldicl %r25, %r24, 15, 0
	rldicl %r24, %r18, 10, 0
	rldicl %r18, %r14, 6, 0
	rldicl %r14, %r17, 3, 0
	rldicl %r17, %r7, 1, 0
	rldicl %r7, %r12, 44, 0
	rldicl %r12, %r0, 20, 0
	rldicl %r10, %r31, 14, 0
	rldicl %r31, %r28, 2, 0
	rldicl %r28, %r15, 55, 0
	rldicl %r15, %r23, 45, 0
	rldicl %r23, %r11, 36, 0
	rldicl %r11, %r6, 28, 0
	rldicl %r16, %r29, 61, 0
	rldicl %r29, %r21, 39, 0
	rldicl %r21, %r27, 18, 0
	rldicl %r27, %r8, 62, 0
	rldicl %r8, %r19, 43, 0
	rldicl %r19, %r20, 25, 0
	rldicl %r20, %r26, 8, 0
	rldicl %r26, %r30, 56, 0
	rldicl %r30, %r22, 41, 0
	rldicl %r22, %r5, 27, 0
	and %r0, %r2, %r7
	or %r5, %r10, %r2
	or %r6, %r7, %r8
	xor %r2, %r2, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r8
	or %r6, %r6, %r9
	xor %r7, %r7, %r6
	and %r6, %r9, %r10
	xor %r8, %r8, %r6
	xor %r9, %r9, %r5
	xor %r10, %r10, %r0
	and %r0, %r11, %r12
	or %r5, %r16, %r11
	or %r6, %r12, %r14
	xor %r11, %r11, %r6
	and %r6, %r14, %r15
	xor %r12, %r12, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r16
	or %r6, %r6, %r15
	xor %r14, %r14, %r6
	xor %r15, %r15, %r5
	xor %r16, %r16, %r0
	or %r0, %r18, %r19
	and %r5, %r19, %r20
	and %r6, %r17, %r18
	xor %r18, %r18, %r5
	or %r5, %r21, %r17
	xor %r17, %r17, %r0
	ld %r0, 24(%r4)
	xor %r20, %r20, %r0
	and %r0, %r20, %r21
	xor %r19, %r19, %r0
	xor %r20, %r20, %r5
	xor %r21, %r21, %r6
	and %r0, %r23, %r24
	or %r5, %r24, %r25
	or %r6, %r22, %r23
	xor %r23, %r23, %r5
	and %r5, %r26, %r22
	xor %r22, %r22, %r0
	ld %r0, 24(%r4)
	xor %r25, %r25, %r0
	or %r0, %r25, %r26
	xor %r24, %r24, %r0
	xor %r25, %r25, %r5
	xor %r26, %r26, %r6
	or %r0, %r29, %r30
	and %r5, %r30, %r31
	or %r6, %r31, %r27
	xor %r30, %r30, %r6
	and %r6, %r27, %r28
	xor %r31, %r31, %r6
	ld %r6, 24(%r4)
	xor %r28, %r28, %r6
	and %r6, %r28, %r29
	xor %r27, %r27, %r6
	xor %r28, %r28, %r0
	xor %r29, %r29, %r5
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 128
	xor %r2, %r2, %r5
	xor %r0, %r2, %r11
	xor %r0, %r0, %r17
	xor %r0, %r0, %r22
	xor %r0, %r0, %r27
	xor %r5, %r7, %r12
	xor %r5, %r5, %r18
	xor %r5, %r5, %r23
	xor %r5, %r5, %r28
	xor %r6, %r8, %r14
	xor %r6, %r6, %r19
	xor %r6, %r6, %r24
	xor %r6, %r6, %r29
	std %r9, 0(%r4)
	xor %r9, %r9, %r15
	xor %r9, %r9, %r20
	xor %r9, %r9, %r25
	xor %r9, %r9, %r30
	std %r10, 8(%r4)
	xor %r10, %r10, %r16
	xor %r10, %r10, %r21
	xor %r10, %r10, %r26
	xor %r10, %r10, %r31
	std %r16, 16(%r4)
	rldicl %r16, %r6, 1, 0
	xor %r16, %r16, %r0
	xor %r7, %r7, %r16
	xor %r12, %r12, %r16
	xor %r18, %r18, %r16
	xor %r23, %r23, %r16
	xor %r28, %r28, %r16
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r9
	xor %r21, %r21, %r0
	xor %r26, %r26, %r0
	xor %r31, %r31, %r0
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r5
	xor %r8, %r8, %r9
	xor %r14, %r14, %r9
	xor %r19, %r19, %r9
	xor %r24, %r24, %r9
	xor %r29, %r29, %r9
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r10
	xor %r2, %r2, %r5
	xor %r11, %r11, %r5
	xor %r17, %r17, %r5
	xor %r22, %r22, %r5
	xor %r27, %r27, %r5
	rldicl %r10, %r10, 1, 0
	xor %r10, %r10, %r6
	xor %r15, %r15, %r10
	xor %r20, %r20, %r10
	xor %r25, %r25, %r10
	xor %r30, %r30, %r10
	ld %r5, 8(%r4)
	xor %r5, %r5, %r0
	ld %r6, 0(%r4)
	xor %r6, %r6, %r10
	ld %r16, 16(%r4)
	xor %r0, %r0, %r16
	rldicl %r9, %r25, 21, 0
	rldicl %r25, %r24, 15, 0
	rldicl %r24, %r18, 10, 0
	rldicl %r18, %r14, 6, 0
	rldicl %r14, %r17, 3, 0
	rldicl %r17, %r7, 1, 0
	rldicl %r7, %r12, 44, 0
	rldicl %r12, %r0, 20, 0
	rldicl %r10, %r31, 14, 0
	rldicl %r31, %r28, 2, 0
	rldicl %r28, %r15, 55, 0
	rldicl %r15, %r23, 45, 0
	rldicl %r23, %r11, 36, 0
	rldicl %r11, %r6, 28, 0
	rldicl %r16, %r29, 61, 0
	rldicl %r29, %r21, 39, 0
	rldicl %r21, %r27, 18, 0
	rldicl %r27, %r8, 62, 0
	rldicl %r8, %r19, 43, 0
	rldicl %r19, %r20, 25, 0
	rldicl %r20, %r26, 8, 0
	rldicl %r26, %r30, 56, 0
	rldicl %r30, %r22, 41, 0
	rldicl %r22, %r5, 27, 0
	and %r0, %r2, %r7
	or %r5, %r10, %r2
	or %r6, %r7, %r8
	xor %r2, %r2, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r8
	or %r6, %r6, %r9
	xor %r7, %r7, %r6
	and %r6, %r9, %r10
	xor %r8, %r8, %r6
	xor %r9, %r9, %r5
	xor %r10, %r10, %r0
	and %r0, %r11, %r12
	or %r5, %r16, %r11
	or %r6, %r12, %r14
	xor %r11, %r11, %r6
	and %r6, %r14, %r15
	xor %r12, %r12, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r16
	or %r6, %r6, %r15
	xor %r14, %r14, %r6
	xor %r15, %r15, %r5
	xor %r16, %r16, %r0
	or %r0, %r18, %r19
	and %r5, %r19, %r20
	and %r6, %r17, %r18
	xor %r18, %r18, %r5
	or %r5, %r21, %r17
	xor %r17, %r17, %r0
	ld %r0, 24(%r4)
	xor %r20, %r20, %r0
	and %r0, %r20, %r21
	xor %r19, %r19, %r0
	xor %r20, %r20, %r5
	xor %r21, %r21, %r6
	and %r0, %r23, %r24
	or %r5, %r24, %r25
	or %r6, %r22, %r23
	xor %r23, %r23, %r5
	and %r5, %r26, %r22
	xor %r22, %r22, %r0
	ld %r0, 24(%r4)
	xor %r25, %r25, %r0
	or %r0, %r25, %r26
	xor %r24, %r24, %r0
	xor %r25, %r25, %r5
	xor %r26, %r26, %r6
	or %r0, %r29, %r30
	and %r5, %r30, %r31
	or %r6, %r31, %r27
	xor %r30, %r30, %r6
	and %r6, %r27, %r28
	xor %r31, %r31, %r6
	ld %r6, 24(%r4)
	xor %r28, %r28, %r6
	and %r6, %r28, %r29
	xor %r27, %r27, %r6
	xor %r28, %r28, %r0
	xor %r29, %r29, %r5
	lis %r5, 0
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 32778
	xor %r2, %r2, %r5
	xor %r0, %r2, %r11
	xor %r0, %r0, %r17
	xor %r0, %r0, %r22
	xor %r0, %r0, %r27
	xor %r5, %r7, %r12
	xor %r5, %r5, %r18
	xor %r5, %r5, %r23
	xor %r5, %r5, %r28
	xor %r6, %r8, %r14
	xor %r6, %r6, %r19
	xor %r6, %r6, %r24
	xor %r6, %r6, %r29
	std %r9, 0(%r4)
	xor %r9, %r9, %r15
	xor %r9, %r9, %r20
	xor %r9, %r9, %r25
	xor %r9, %r9, %r30
	std %r10, 8(%r4)
	xor %r10, %r10, %r16
	xor %r10, %r10, %r21
	xor %r10, %r10, %r26
	xor %r10, %r10, %r31
	std %r16, 16(%r4)
	rldicl %r16, %r6, 1, 0
	xor %r16, %r16, %r0
	xor %r7, %r7, %r16
	xor %r12, %r12, %r16
	xor %r18, %r18, %r16
	xor %r23, %r23, %r16
	xor %r28, %r28, %r16
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r9
	xor %r21, %r21, %r0
	xor %r26, %r26, %r0
	xor %r31, %r31, %r0
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r5
	xor %r8, %r8, %r9
	xor %r14, %r14, %r9
	xor %r19, %r19, %r9
	xor %r24, %r24, %r9
	xor %r29, %r29, %r9
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r10
	xor %r2, %r2, %r5
	xor %r11, %r11, %r5
	xor %r17, %r17, %r5
	xor %r22, %r22, %r5
	xor %r27, %r27, %r5
	rldicl %r10, %r10, 1, 0
	xor %r10, %r10, %r6
	xor %r15, %r15, %r10
	xor %r20, %r20, %r10
	xor %r25, %r25, %r10
	xor %r30, %r30, %r10
	ld %r5, 8(%r4)
	xor %r5, %r5, %r0
	ld %r6, 0(%r4)
	xor %r6, %r6, %r10
	ld %r16, 16(%r4)
	xor %r0, %r0, %r16
	rldicl %r9, %r25, 21, 0
	rldicl %r25, %r24, 15, 0
	rldicl %r24, %r18, 10, 0
	rldicl %r18, %r14, 6, 0
	rldicl %r14, %r17, 3, 0
	rldicl %r17, %r7, 1, 0
	rldicl %r7, %r12, 44, 0
	rldicl %r12, %r0, 20, 0
	rldicl %r10, %r31, 14, 0
	rldicl %r31, %r28, 2, 0
	rldicl %r28, %r15, 55, 0
	rldicl %r15, %r23, 45, 0
	rldicl %r23, %r11, 36, 0
	rldicl %r11, %r6, 28, 0
	rldicl %r16, %r29, 61, 0
	rldicl %r29, %r21, 39, 0
	rldicl %r21, %r27, 18, 0
	rldicl %r27, %r8, 62, 0
	rldicl %r8, %r19, 43, 0
	rldicl %r19, %r20, 25, 0
	rldicl %r20, %r26, 8, 0
	rldicl %r26, %r30, 56, 0
	rldicl %r30, %r22, 41, 0
	rldicl %r22, %r5, 27, 0
	and %r0, %r2, %r7
	or %r5, %r10, %r2
	or %r6, %r7, %r8
	xor %r2, %r2, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r8
	or %r6, %r6, %r9
	xor %r7, %r7, %r6
	and %r6, %r9, %r10
	xor %r8, %r8, %r6
	xor %r9, %r9, %r5
	xor %r10, %r10, %r0
	and %r0, %r11, %r12
	or %r5, %r16, %r11
	or %r6, %r12, %r14
	xor %r11, %r11, %r6
	and %r6, %r14, %r15
	xor %r12, %r12, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r16
	or %r6, %r6, %r15
	xor %r14, %r14, %r6
	xor %r15, %r15, %r5
	xor %r16, %r16, %r0
	or %r0, %r18, %r19
	and %r5, %r19, %r20
	and %r6, %r17, %r18
	xor %r18, %r18, %r5
	or %r5, %r21, %r17
	xor %r17, %r17, %r0
	ld %r0, 24(%r4)
	xor %r20, %r20, %r0
	and %r0, %r20, %r21
	xor %r19, %r19, %r0
	xor %r20, %r20, %r5
	xor %r21, %r21, %r6
	and %r0, %r23, %r24
	or %r5, %r24, %r25
	or %r6, %r22, %r23
	xor %r23, %r23, %r5
	and %r5, %r26, %r22
	xor %r22, %r22, %r0
	ld %r0, 24(%r4)
	xor %r25, %r25, %r0
	or %r0, %r25, %r26
	xor %r24, %r24, %r0
	xor %r25, %r25, %r5
	xor %r26, %r26, %r6
	or %r0, %r29, %r30
	and %r5, %r30, %r31
	or %r6, %r31, %r27
	xor %r30, %r30, %r6
	and %r6, %r27, %r28
	xor %r31, %r31, %r6
	ld %r6, 24(%r4)
	xor %r28, %r28, %r6
	and %r6, %r28, %r29
	xor %r27, %r27, %r6
	xor %r28, %r28, %r0
	xor %r29, %r29, %r5
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 32768
	ori %r5, %r5, 10
	xor %r2, %r2, %r5
	xor %r0, %r2, %r11
	xor %r0, %r0, %r17
	xor %r0, %r0, %r22
	xor %r0, %r0, %r27
	xor %r5, %r7, %r12
	xor %r5, %r5, %r18
	xor %r5, %r5, %r23
	xor %r5, %r5, %r28
	xor %r6, %r8, %r14
	xor %r6, %r6, %r19
	xor %r6, %r6, %r24
	xor %r6, %r6, %r29
	std %r9, 0(%r4)
	xor %r9, %r9, %r15
	xor %r9, %r9, %r20
	xor %r9, %r9, %r25
	xor %r9, %r9, %r30
	std %r10, 8(%r4)
	xor %r10, %r10, %r16
	xor %r10, %r10, %r21
	xor %r10, %r10, %r26
	xor %r10, %r10, %r31
	std %r16, 16(%r4)
	rldicl %r16, %r6, 1, 0
	xor %r16, %r16, %r0
	xor %r7, %r7, %r16
	xor %r12, %r12, %r16
	xor %r18, %r18, %r16
	xor %r23, %r23, %r16
	xor %r28, %r28, %r16
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r9
	xor %r21, %r21, %r0
	xor %r26, %r26, %r0
	xor %r31, %r31, %r0
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r5
	xor %r8, %r8, %r9
	xor %r14, %r14, %r9
	xor %r19, %r19, %r9
	xor %r24, %r24, %r9
	xor %r29, %r29, %r9
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r10
	xor %r2, %r2, %r5
	xor %r11, %r11, %r5
	xor %r17, %r17, %r5
	xor %r22, %r22, %r5
	xor %r27, %r27, %r5
	rldicl %r10, %r10, 1, 0
	xor %r10, %r10, %r6
	xor %r15, %r15, %r10
	xor %r20, %r20, %r10
	xor %r25, %r25, %r10
	xor %r30, %r30, %r10
	ld %r5, 8(%r4)
	xor %r5, %r5, %r0
	ld %r6, 0(%r4)
	xor %r6, %r6, %r10
	ld %r16, 16(%r4)
	xor %r0, %r0, %r16
	rldicl %r9, %r25, 21, 0
	rldicl %r25, %r24, 15, 0
	rldicl %r24, %r18, 10, 0
	rldicl %r18, %r14, 6, 0
	rldicl %r14, %r17, 3, 0
	rldicl %r17, %r7, 1, 0
	rldicl %r7, %r12, 44, 0
	rldicl %r12, %r0, 20, 0
	rldicl %r10, %r31, 14, 0
	rldicl %r31, %r28, 2, 0
	rldicl %r28, %r15, 55, 0
	rldicl %r15, %r23, 45, 0
	rldicl %r23, %r11, 36, 0
	rldicl %r11, %r6, 28, 0
	rldicl %r16, %r29, 61, 0
	rldicl %r29, %r21, 39, 0
	rldicl %r21, %r27, 18, 0
	rldicl %r27, %r8, 62, 0
	rldicl %r8, %r19, 43, 0
	rldicl %r19, %r20, 25, 0
	rldicl %r20, %r26, 8, 0
	rldicl %r26, %r30, 56, 0
	rldicl %r30, %r22, 41, 0
	rldicl %r22, %r5, 27, 0
	and %r0, %r2, %r7
	or %r5, %r10, %r2
	or %r6, %r7, %r8
	xor %r2, %r2, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r8
	or %r6, %r6, %r9
	xor %r7, %r7, %r6
	and %r6, %r9, %r10
	xor %r8, %r8, %r6
	xor %r9, %r9, %r5
	xor %r10, %r10, %r0
	and %r0, %r11, %r12
	or %r5, %r16, %r11
	or %r6, %r12, %r14
	xor %r11, %r11, %r6
	and %r6, %r14, %r15
	xor %r12, %r12, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r16
	or %r6, %r6, %r15
	xor %r14, %r14, %r6
	xor %r15, %r15, %r5
	xor %r16, %r16, %r0
	or %r0, %r18, %r19
	and %r5, %r19, %r20
	and %r6, %r17, %r18
	xor %r18, %r18, %r5
	or %r5, %r21, %r17
	xor %r17, %r17, %r0
	ld %r0, 24(%r4)
	xor %r20, %r20, %r0
	and %r0, %r20, %r21
	xor %r19, %r19, %r0
	xor %r20, %r20, %r5
	xor %r21, %r21, %r6
	and %r0, %r23, %r24
	or %r5, %r24, %r25
	or %r6, %r22, %r23
	xor %r23, %r23, %r5
	and %r5, %r26, %r22
	xor %r22, %r22, %r0
	ld %r0, 24(%r4)
	xor %r25, %r25, %r0
	or %r0, %r25, %r26
	xor %r24, %r24, %r0
	xor %r25, %r25, %r5
	xor %r26, %r26, %r6
	or %r0, %r29, %r30
	and %r5, %r30, %r31
	or %r6, %r31, %r27
	xor %r30, %r30, %r6
	and %r6, %r27, %r28
	xor %r31, %r31, %r6
	ld %r6, 24(%r4)
	xor %r28, %r28, %r6
	and %r6, %r28, %r29
	xor %r27, %r27, %r6
	xor %r28, %r28, %r0
	xor %r29, %r29, %r5
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 32768
	ori %r5, %r5, 32897
	xor %r2, %r2, %r5
	xor %r0, %r2, %r11
	xor %r0, %r0, %r17
	xor %r0, %r0, %r22
	xor %r0, %r0, %r27
	xor %r5, %r7, %r12
	xor %r5, %r5, %r18
	xor %r5, %r5, %r23
	xor %r5, %r5, %r28
	xor %r6, %r8, %r14
	xor %r6, %r6, %r19
	xor %r6, %r6, %r24
	xor %r6, %r6, %r29
	std %r9, 0(%r4)
	xor %r9, %r9, %r15
	xor %r9, %r9, %r20
	xor %r9, %r9, %r25
	xor %r9, %r9, %r30
	std %r10, 8(%r4)
	xor %r10, %r10, %r16
	xor %r10, %r10, %r21
	xor %r10, %r10, %r26
	xor %r10, %r10, %r31
	std %r16, 16(%r4)
	rldicl %r16, %r6, 1, 0
	xor %r16, %r16, %r0
	xor %r7, %r7, %r16
	xor %r12, %r12, %r16
	xor %r18, %r18, %r16
	xor %r23, %r23, %r16
	xor %r28, %r28, %r16
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r9
	xor %r21, %r21, %r0
	xor %r26, %r26, %r0
	xor %r31, %r31, %r0
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r5
	xor %r8, %r8, %r9
	xor %r14, %r14, %r9
	xor %r19, %r19, %r9
	xor %r24, %r24, %r9
	xor %r29, %r29, %r9
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r10
	xor %r2, %r2, %r5
	xor %r11, %r11, %r5
	xor %r17, %r17, %r5
	xor %r22, %r22, %r5
	xor %r27, %r27, %r5
	rldicl %r10, %r10, 1, 0
	xor %r10, %r10, %r6
	xor %r15, %r15, %r10
	xor %r20, %r20, %r10
	xor %r25, %r25, %r10
	xor %r30, %r30, %r10
	ld %r5, 8(%r4)
	xor %r5, %r5, %r0
	ld %r6, 0(%r4)
	xor %r6, %r6, %r10
	ld %r16, 16(%r4)
	xor %r0, %r0, %r16
	rldicl %r9, %r25, 21, 0
	rldicl %r25, %r24, 15, 0
	rldicl %r24, %r18, 10, 0
	rldicl %r18, %r14, 6, 0
	rldicl %r14, %r17, 3, 0
	rldicl %r17, %r7, 1, 0
	rldicl %r7, %r12, 44, 0
	rldicl %r12, %r0, 20, 0
	rldicl %r10, %r31, 14, 0
	rldicl %r31, %r28, 2, 0
	rldicl %r28, %r15, 55, 0
	rldicl %r15, %r23, 45, 0
	rldicl %r23, %r11, 36, 0
	rldicl %r11, %r6, 28, 0
	rldicl %r16, %r29, 61, 0
	rldicl %r29, %r21, 39, 0
	rldicl %r21, %r27, 18, 0
	rldicl %r27, %r8, 62, 0
	rldicl %r8, %r19, 43, 0
	rldicl %r19, %r20, 25, 0
	rldicl %r20, %r26, 8, 0
	rldicl %r26, %r30, 56, 0
	rldicl %r30, %r22, 41, 0
	rldicl %r22, %r5, 27, 0
	and %r0, %r2, %r7
	or %r5, %r10, %r2
	or %r6, %r7, %r8
	xor %r2, %r2, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r8
	or %r6, %r6, %r9
	xor %r7, %r7, %r6
	and %r6, %r9, %r10
	xor %r8, %r8, %r6
	xor %r9, %r9, %r5
	xor %r10, %r10, %r0
	and %r0, %r11, %r12
	or %r5, %r16, %r11
	or %r6, %r12, %r14
	xor %r11, %r11, %r6
	and %r6, %r14, %r15
	xor %r12, %r12, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r16
	or %r6, %r6, %r15
	xor %r14, %r14, %r6
	xor %r15, %r15, %r5
	xor %r16, %r16, %r0
	or %r0, %r18, %r19
	and %r5, %r19, %r20
	and %r6, %r17, %r18
	xor %r18, %r18, %r5
	or %r5, %r21, %r17
	xor %r17, %r17, %r0
	ld %r0, 24(%r4)
	xor %r20, %r20, %r0
	and %r0, %r20, %r21
	xor %r19, %r19, %r0
	xor %r20, %r20, %r5
	xor %r21, %r21, %r6
	and %r0, %r23, %r24
	or %r5, %r24, %r25
	or %r6, %r22, %r23
	xor %r23, %r23, %r5
	and %r5, %r26, %r22
	xor %r22, %r22, %r0
	ld %r0, 24(%r4)
	xor %r25, %r25, %r0
	or %r0, %r25, %r26
	xor %r24, %r24, %r0
	xor %r25, %r25, %r5
	xor %r26, %r26, %r6
	or %r0, %r29, %r30
	and %r5, %r30, %r31
	or %r6, %r31, %r27
	xor %r30, %r30, %r6
	and %r6, %r27, %r28
	xor %r31, %r31, %r6
	ld %r6, 24(%r4)
	xor %r28, %r28, %r6
	and %r6, %r28, %r29
	xor %r27, %r27, %r6
	xor %r28, %r28, %r0
	xor %r29, %r29, %r5
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 32896
	xor %r2, %r2, %r5
	xor %r0, %r2, %r11
	xor %r0, %r0, %r17
	xor %r0, %r0, %r22
	xor %r0, %r0, %r27
	xor %r5, %r7, %r12
	xor %r5, %r5, %r18
	xor %r5, %r5, %r23
	xor %r5, %r5, %r28
	xor %r6, %r8, %r14
	xor %r6, %r6, %r19
	xor %r6, %r6, %r24
	xor %r6, %r6, %r29
	std %r9, 0(%r4)
	xor %r9, %r9, %r15
	xor %r9, %r9, %r20
	xor %r9, %r9, %r25
	xor %r9, %r9, %r30
	std %r10, 8(%r4)
	xor %r10, %r10, %r16
	xor %r10, %r10, %r21
	xor %r10, %r10, %r26
	xor %r10, %r10, %r31
	std %r16, 16(%r4)
	rldicl %r16, %r6, 1, 0
	xor %r16, %r16, %r0
	xor %r7, %r7, %r16
	xor %r12, %r12, %r16
	xor %r18, %r18, %r16
	xor %r23, %r23, %r16
	xor %r28, %r28, %r16
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r9
	xor %r21, %r21, %r0
	xor %r26, %r26, %r0
	xor %r31, %r31, %r0
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r5
	xor %r8, %r8, %r9
	xor %r14, %r14, %r9
	xor %r19, %r19, %r9
	xor %r24, %r24, %r9
	xor %r29, %r29, %r9
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r10
	xor %r2, %r2, %r5
	xor %r11, %r11, %r5
	xor %r17, %r17, %r5
	xor %r22, %r22, %r5
	xor %r27, %r27, %r5
	rldicl %r10, %r10, 1, 0
	xor %r10, %r10, %r6
	xor %r15, %r15, %r10
	xor %r20, %r20, %r10
	xor %r25, %r25, %r10
	xor %r30, %r30, %r10
	ld %r5, 8(%r4)
	xor %r5, %r5, %r0
	ld %r6, 0(%r4)
	xor %r6, %r6, %r10
	ld %r16, 16(%r4)
	xor %r0, %r0, %r16
	rldicl %r9, %r25, 21, 0
	rldicl %r25, %r24, 15, 0
	rldicl %r24, %r18, 10, 0
	rldicl %r18, %r14, 6, 0
	rldicl %r14, %r17, 3, 0
	rldicl %r17, %r7, 1, 0
	rldicl %r7, %r12, 44, 0
	rldicl %r12, %r0, 20, 0
	rldicl %r10, %r31, 14, 0
	rldicl %r31, %r28, 2, 0
	rldicl %r28, %r15, 55, 0
	rldicl %r15, %r23, 45, 0
	rldicl %r23, %r11, 36, 0
	rldicl %r11, %r6, 28, 0
	rldicl %r16, %r29, 61, 0
	rldicl %r29, %r21, 39, 0
	rldicl %r21, %r27, 18, 0
	rldicl %r27, %r8, 62, 0
	rldicl %r8, %r19, 43, 0
	rldicl %r19, %r20, 25, 0
	rldicl %r20, %r26, 8, 0
	rldicl %r26, %r30, 56, 0
	rldicl %r30, %r22, 41, 0
	rldicl %r22, %r5, 27, 0
	and %r0, %r2, %r7
	or %r5, %r10, %r2
	or %r6, %r7, %r8
	xor %r2, %r2, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r8
	or %r6, %r6, %r9
	xor %r7, %r7, %r6
	and %r6, %r9, %r10
	xor %r8, %r8, %r6
	xor %r9, %r9, %r5
	xor %r10, %r10, %r0
	and %r0, %r11, %r12
	or %r5, %r16, %r11
	or %r6, %r12, %r14
	xor %r11, %r11, %r6
	and %r6, %r14, %r15
	xor %r12, %r12, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r16
	or %r6, %r6, %r15
	xor %r14, %r14, %r6
	xor %r15, %r15, %r5
	xor %r16, %r16, %r0
	or %r0, %r18, %r19
	and %r5, %r19, %r20
	and %r6, %r17, %r18
	xor %r18, %r18, %r5
	or %r5, %r21, %r17
	xor %r17, %r17, %r0
	ld %r0, 24(%r4)
	xor %r20, %r20, %r0
	and %r0, %r20, %r21
	xor %r19, %r19, %r0
	xor %r20, %r20, %r5
	xor %r21, %r21, %r6
	and %r0, %r23, %r24
	or %r5, %r24, %r25
	or %r6, %r22, %r23
	xor %r23, %r23, %r5
	and %r5, %r26, %r22
	xor %r22, %r22, %r0
	ld %r0, 24(%r4)
	xor %r25, %r25, %r0
	or %r0, %r25, %r26
	xor %r24, %r24, %r0
	xor %r25, %r25, %r5
	xor %r26, %r26, %r6
	or %r0, %r29, %r30
	and %r5, %r30, %r31
	or %r6, %r31, %r27
	xor %r30, %r30, %r6
	and %r6, %r27, %r28
	xor %r31, %r31, %r6
	ld %r6, 24(%r4)
	xor %r28, %r28, %r6
	and %r6, %r28, %r29
	xor %r27, %r27, %r6
	xor %r28, %r28, %r0
	xor %r29, %r29, %r5
	lis %r5, 0
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 32768
	ori %r5, %r5, 1
	xor %r2, %r2, %r5
	xor %r0, %r2, %r11
	xor %r0, %r0, %r17
	xor %r0, %r0, %r22
	xor %r0, %r0, %r27
	xor %r5, %r7, %r12
	xor %r5, %r5, %r18
	xor %r5, %r5, %r23
	xor %r5, %r5, %r28
	xor %r6, %r8, %r14
	xor %r6, %r6, %r19
	xor %r6, %r6, %r24
	xor %r6, %r6, %r29
	std %r9, 0(%r4)
	xor %r9, %r9, %r15
	xor %r9, %r9, %r20
	xor %r9, %r9, %r25
	xor %r9, %r9, %r30
	std %r10, 8(%r4)
	xor %r10, %r10, %r16
	xor %r10, %r10, %r21
	xor %r10, %r10, %r26
	xor %r10, %r10, %r31
	std %r16, 16(%r4)
	rldicl %r16, %r6, 1, 0
	xor %r16, %r16, %r0
	xor %r7, %r7, %r16
	xor %r12, %r12, %r16
	xor %r18, %r18, %r16
	xor %r23, %r23, %r16
	xor %r28, %r28, %r16
	rldicl %r0, %r0, 1, 0
	xor %r0, %r0, %r9
	xor %r21, %r21, %r0
	xor %r26, %r26, %r0
	xor %r31, %r31, %r0
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r5
	xor %r8, %r8, %r9
	xor %r14, %r14, %r9
	xor %r19, %r19, %r9
	xor %r24, %r24, %r9
	xor %r29, %r29, %r9
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r10
	xor %r2, %r2, %r5
	xor %r11, %r11, %r5
	xor %r17, %r17, %r5
	xor %r22, %r22, %r5
	xor %r27, %r27, %r5
	rldicl %r10, %r10, 1, 0
	xor %r10, %r10, %r6
	xor %r15, %r15, %r10
	xor %r20, %r20, %r10
	xor %r25, %r25, %r10
	xor %r30, %r30, %r10
	ld %r5, 8(%r4)
	xor %r5, %r5, %r0
	ld %r6, 0(%r4)
	xor %r6, %r6, %r10
	ld %r16, 16(%r4)
	xor %r0, %r0, %r16
	rldicl %r9, %r25, 21, 0
	rldicl %r25, %r24, 15, 0
	rldicl %r24, %r18, 10, 0
	rldicl %r18, %r14, 6, 0
	rldicl %r14, %r17, 3, 0
	rldicl %r17, %r7, 1, 0
	rldicl %r7, %r12, 44, 0
	rldicl %r12, %r0, 20, 0
	rldicl %r10, %r31, 14, 0
	rldicl %r31, %r28, 2, 0
	rldicl %r28, %r15, 55, 0
	rldicl %r15, %r23, 45, 0
	rldicl %r23, %r11, 36, 0
	rldicl %r11, %r6, 28, 0
	rldicl %r16, %r29, 61, 0
	rldicl %r29, %r21, 39, 0
	rldicl %r21, %r27, 18, 0
	rldicl %r27, %r8, 62, 0
	rldicl %r8, %r19, 43, 0
	rldicl %r19, %r20, 25, 0
	rldicl %r20, %r26, 8, 0
	rldicl %r26, %r30, 56, 0
	rldicl %r30, %r22, 41, 0
	rldicl %r22, %r5, 27, 0
	and %r0, %r2, %r7
	or %r5, %r10, %r2
	or %r6, %r7, %r8
	xor %r2, %r2, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r8
	or %r6, %r6, %r9
	xor %r7, %r7, %r6
	and %r6, %r9, %r10
	xor %r8, %r8, %r6
	xor %r9, %r9, %r5
	xor %r10, %r10, %r0
	and %r0, %r11, %r12
	or %r5, %r16, %r11
	or %r6, %r12, %r14
	xor %r11, %r11, %r6
	and %r6, %r14, %r15
	xor %r12, %r12, %r6
	ld %r6, 24(%r4)
	xor %r6, %r6, %r16
	or %r6, %r6, %r15
	xor %r14, %r14, %r6
	xor %r15, %r15, %r5
	xor %r16, %r16, %r0
	or %r0, %r18, %r19
	and %r5, %r19, %r20
	and %r6, %r17, %r18
	xor %r18, %r18, %r5
	or %r5, %r21, %r17
	xor %r17, %r17, %r0
	ld %r0, 24(%r4)
	xor %r20, %r20, %r0
	and %r0, %r20, %r21
	xor %r19, %r19, %r0
	xor %r20, %r20, %r5
	xor %r21, %r21, %r6
	and %r0, %r23, %r24
	or %r5, %r24, %r25
	or %r6, %r22, %r23
	xor %r23, %r23, %r5
	and %r5, %r26, %r22
	xor %r22, %r22, %r0
	ld %r0, 24(%r4)
	xor %r25, %r25, %r0
	or %r0, %r25, %r26
	xor %r24, %r24, %r0
	xor %r25, %r25, %r5
	xor %r26, %r26, %r6
	or %r0, %r29, %r30
	and %r5, %r30, %r31
	or %r6, %r31, %r27
	xor %r30, %r30, %r6
	and %r6, %r27, %r28
	xor %r31, %r31, %r6
	ld %r6, 24(%r4)
	xor %r28, %r28, %r6
	and %r6, %r28, %r29
	xor %r27, %r27, %r6
	xor %r28, %r28, %r0
	xor %r29, %r29, %r5
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 32768
	ori %r5, %r5, 32776
	xor %r2, %r2, %r5
	ld %r0, 24(%r4)
	std %r2, 0(%r3)
	xor %r7, %r7, %r0
	std %r7, 8(%r3)
	xor %r8, %r8, %r0
	std %r8, 16(%r3)
	std %r9, 24(%r3)
	std %r10, 32(%r3)
	std %r11, 40(%r3)
	std %r12, 48(%r3)
	std %r14, 56(%r3)
	xor %r15, %r15, %r0
	std %r15, 64(%r3)
	std %r16, 72(%r3)
	std %r17, 80(%r3)
	std %r18, 88(%r3)
	xor %r19, %r19, %r0
	std %r19, 96(%r3)
	std %r20, 104(%r3)
	std %r21, 112(%r3)
	std %r22, 120(%r3)
	std %r23, 128(%r3)
	xor %r24, %r24, %r0
	std %r24, 136(%r3)
	std %r25, 144(%r3)
	std %r26, 152(%r3)
	xor %r27, %r27, %r0
	std %r27, 160(%r3)
	std %r28, 168(%r3)
	std %r29, 176(%r3)
	std %r30, 184(%r3)
	std %r31, 192(%r3)
	ld %r2, 32(%r4)
	ld %r14, 40(%r4)
	ld %r15, 48(%r4)
	ld %r16, 56(%r4)
	ld %r17, 64(%r4)
	ld %r18, 72(%r4)
	ld %r19, 80(%r4)
	ld %r20, 88(%r4)
	ld %r21, 96(%r4)
	ld %r22, 104(%r4)
	ld %r23, 112(%r4)
	ld %r24, 120(%r4)
	ld %r25, 128(%r4)
	ld %r26, 136(%r4)
	ld %r27, 144(%r4)
	ld %r28, 152(%r4)
	ld %r29, 160(%r4)
	ld %r30, 168(%r4)
	ld %r31, 176(%r4)
	blr
