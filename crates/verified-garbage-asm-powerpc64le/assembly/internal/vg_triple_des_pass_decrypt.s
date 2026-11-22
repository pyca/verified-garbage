// The functions of `src/internal/vg_triple_des_pass_decrypt.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_pass_decrypt:
	lis %r11, -1
	ori %r11, %r11, 65535
	li %r5, 8
20:
	ld %r9, 0(%r3)
	xor %r9, %r9, %r11
	addi %r3, %r3, -8
	rldicr %r12, %r9, 21, 42
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 248(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 20, 43
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 312(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 19, 44
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 376(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 18, 45
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 440(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 17, 46
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 504(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 16, 47
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 8(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r14
	xor %r6, %r6, %r14
	xor %r2, %r15, %r6
	or %r19, %r16, %r12
	xor %r20, %r18, %r16
	and %r21, %r19, %r20
	xor %r22, %r15, %r21
	or %r23, %r22, %r2
	xor %r23, %r23, %r2
	xor %r24, %r14, %r12
	xor %r25, %r16, %r24
	xor %r25, %r25, %r11
	and %r25, %r25, %r2
	or %r21, %r12, %r21
	xor %r25, %r25, %r21
	or %r21, %r25, %r23
	xor %r21, %r21, %r23
	or %r12, %r18, %r12
	or %r26, %r25, %r12
	xor %r22, %r22, %r11
	and %r22, %r22, %r14
	xor %r27, %r26, %r22
	or %r15, %r15, %r12
	xor %r15, %r15, %r12
	xor %r15, %r22, %r15
	xor %r20, %r20, %r11
	and %r20, %r20, %r24
	or %r15, %r15, %r20
	or %r16, %r16, %r6
	xor %r16, %r16, %r6
	xor %r6, %r2, %r26
	or %r6, %r6, %r16
	xor %r6, %r6, %r16
	xor %r16, %r6, %r11
	and %r25, %r19, %r25
	xor %r16, %r16, %r25
	or %r27, %r27, %r17
	xor %r27, %r27, %r17
	xor %r27, %r27, %r16
	xor %r6, %r24, %r6
	or %r22, %r22, %r6
	xor %r22, %r19, %r22
	xor %r18, %r18, %r22
	xor %r16, %r16, %r18
	or %r23, %r23, %r17
	xor %r23, %r23, %r16
	xor %r19, %r19, %r26
	or %r19, %r15, %r19
	xor %r19, %r18, %r19
	or %r24, %r24, %r16
	xor %r24, %r19, %r24
	or %r16, %r21, %r17
	xor %r16, %r16, %r24
	or %r14, %r14, %r2
	or %r14, %r14, %r19
	xor %r14, %r14, %r19
	and %r21, %r21, %r18
	xor %r14, %r14, %r21
	or %r14, %r14, %r17
	xor %r14, %r14, %r15
	ld %r0, 64(%r10)
	xor %r0, %r0, %r14
	std %r0, 64(%r10)
	ld %r0, 80(%r10)
	xor %r0, %r0, %r27
	std %r0, 80(%r10)
	ld %r0, 464(%r10)
	xor %r0, %r0, %r16
	std %r0, 464(%r10)
	ld %r0, 480(%r10)
	xor %r0, %r0, %r23
	std %r0, 480(%r10)
	rldicr %r12, %r9, 27, 36
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 488(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 26, 37
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 56(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 25, 38
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 120(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 24, 39
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 184(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 23, 40
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 248(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 22, 41
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 312(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r18, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r19, %r17, %r2
	or %r20, %r6, %r12
	xor %r20, %r20, %r12
	and %r21, %r18, %r6
	xor %r14, %r14, %r21
	or %r21, %r14, %r20
	xor %r21, %r21, %r20
	and %r22, %r16, %r12
	xor %r2, %r2, %r20
	and %r2, %r19, %r2
	or %r20, %r2, %r22
	xor %r20, %r20, %r22
	and %r23, %r16, %r2
	xor %r18, %r18, %r11
	xor %r18, %r23, %r18
	xor %r12, %r12, %r6
	or %r24, %r12, %r22
	xor %r24, %r24, %r22
	xor %r25, %r18, %r24
	xor %r20, %r20, %r11
	and %r20, %r20, %r15
	xor %r20, %r20, %r25
	or %r17, %r17, %r24
	xor %r17, %r17, %r24
	xor %r14, %r14, %r17
	or %r18, %r18, %r14
	xor %r18, %r18, %r14
	xor %r16, %r16, %r12
	xor %r18, %r18, %r16
	or %r24, %r19, %r15
	xor %r24, %r24, %r15
	xor %r24, %r24, %r18
	xor %r23, %r23, %r17
	or %r16, %r16, %r23
	xor %r19, %r19, %r25
	or %r22, %r22, %r19
	xor %r23, %r16, %r22
	xor %r2, %r2, %r25
	xor %r18, %r18, %r2
	and %r22, %r22, %r18
	and %r6, %r6, %r16
	xor %r22, %r22, %r6
	or %r6, %r22, %r15
	xor %r6, %r6, %r23
	or %r22, %r22, %r14
	xor %r22, %r22, %r14
	or %r12, %r12, %r19
	xor %r22, %r22, %r12
	or %r21, %r21, %r15
	xor %r21, %r21, %r22
	ld %r0, 400(%r10)
	xor %r0, %r0, %r21
	std %r0, 400(%r10)
	ld %r0, 432(%r10)
	xor %r0, %r0, %r6
	std %r0, 432(%r10)
	ld %r0, 256(%r10)
	xor %r0, %r0, %r20
	std %r0, 256(%r10)
	ld %r0, 224(%r10)
	xor %r0, %r0, %r24
	std %r0, 224(%r10)
	rldicr %r12, %r9, 33, 30
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 232(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 32, 31
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 296(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 31, 32
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 360(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 30, 33
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 424(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 29, 34
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 488(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 28, 35
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 56(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r17
	xor %r6, %r6, %r17
	xor %r2, %r16, %r12
	or %r19, %r6, %r2
	xor %r20, %r15, %r12
	or %r21, %r20, %r18
	xor %r21, %r21, %r18
	xor %r22, %r19, %r21
	xor %r23, %r17, %r2
	or %r24, %r23, %r12
	xor %r24, %r24, %r12
	xor %r19, %r19, %r24
	or %r24, %r22, %r19
	xor %r24, %r24, %r19
	and %r25, %r12, %r22
	or %r25, %r15, %r25
	and %r25, %r18, %r25
	xor %r25, %r23, %r25
	or %r26, %r22, %r14
	xor %r26, %r26, %r14
	xor %r26, %r26, %r25
	and %r2, %r2, %r20
	xor %r20, %r18, %r15
	xor %r27, %r19, %r20
	or %r27, %r16, %r27
	or %r27, %r27, %r2
	xor %r27, %r27, %r2
	or %r21, %r21, %r20
	or %r20, %r25, %r21
	xor %r20, %r20, %r21
	and %r12, %r15, %r12
	or %r2, %r12, %r17
	xor %r2, %r2, %r17
	xor %r20, %r20, %r2
	and %r19, %r19, %r20
	or %r12, %r23, %r12
	or %r12, %r12, %r19
	xor %r12, %r12, %r19
	xor %r18, %r18, %r12
	and %r27, %r27, %r14
	xor %r27, %r27, %r18
	xor %r22, %r22, %r11
	or %r17, %r17, %r22
	or %r16, %r16, %r17
	xor %r23, %r23, %r16
	xor %r21, %r21, %r23
	xor %r24, %r24, %r11
	and %r24, %r24, %r14
	xor %r24, %r24, %r21
	and %r15, %r15, %r22
	xor %r25, %r25, %r15
	or %r23, %r23, %r25
	xor %r6, %r6, %r18
	xor %r23, %r23, %r6
	or %r20, %r20, %r14
	xor %r20, %r20, %r23
	ld %r0, 176(%r10)
	xor %r0, %r0, %r26
	std %r0, 176(%r10)
	ld %r0, 128(%r10)
	xor %r0, %r0, %r20
	std %r0, 128(%r10)
	ld %r0, 32(%r10)
	xor %r0, %r0, %r27
	std %r0, 32(%r10)
	ld %r0, 16(%r10)
	xor %r0, %r0, %r24
	std %r0, 16(%r10)
	rldicr %r12, %r9, 39, 24
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 472(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 38, 25
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 40(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 37, 26
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 104(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 36, 27
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 168(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 35, 28
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 232(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 34, 29
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 296(%r10)
	xor %r18, %r18, %r0
	xor %r18, %r18, %r16
	xor %r16, %r16, %r14
	or %r6, %r17, %r15
	xor %r6, %r14, %r6
	xor %r6, %r6, %r11
	and %r6, %r6, %r16
	or %r2, %r16, %r17
	xor %r2, %r2, %r17
	xor %r19, %r15, %r2
	or %r20, %r18, %r19
	or %r20, %r20, %r6
	xor %r20, %r20, %r6
	xor %r21, %r17, %r20
	and %r19, %r19, %r21
	or %r16, %r16, %r19
	xor %r16, %r16, %r19
	xor %r18, %r18, %r21
	xor %r16, %r16, %r11
	and %r16, %r16, %r18
	xor %r6, %r6, %r16
	xor %r17, %r17, %r15
	or %r14, %r14, %r2
	xor %r18, %r18, %r14
	or %r14, %r18, %r17
	xor %r14, %r14, %r17
	xor %r20, %r20, %r14
	or %r14, %r12, %r6
	xor %r14, %r14, %r6
	xor %r14, %r14, %r20
	xor %r20, %r20, %r11
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r20
	xor %r6, %r6, %r20
	or %r6, %r6, %r17
	xor %r6, %r6, %r17
	or %r19, %r19, %r6
	xor %r18, %r18, %r19
	or %r19, %r21, %r12
	xor %r19, %r19, %r18
	and %r12, %r12, %r21
	xor %r12, %r12, %r18
	ld %r0, 496(%r10)
	xor %r0, %r0, %r12
	std %r0, 496(%r10)
	ld %r0, 416(%r10)
	xor %r0, %r0, %r19
	std %r0, 416(%r10)
	ld %r0, 272(%r10)
	xor %r0, %r0, %r2
	std %r0, 272(%r10)
	ld %r0, 384(%r10)
	xor %r0, %r0, %r14
	std %r0, 384(%r10)
	rldicr %r12, %r9, 45, 18
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 216(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 44, 19
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 280(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 43, 20
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 344(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 42, 21
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 408(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 41, 22
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 472(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 40, 23
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 40(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r16
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r19, %r18, %r2
	xor %r20, %r16, %r19
	or %r21, %r15, %r20
	or %r2, %r2, %r15
	xor %r2, %r2, %r15
	xor %r16, %r16, %r2
	and %r2, %r14, %r16
	or %r20, %r18, %r20
	xor %r2, %r2, %r20
	xor %r2, %r15, %r2
	xor %r12, %r12, %r2
	or %r22, %r19, %r12
	and %r23, %r14, %r22
	xor %r24, %r19, %r23
	and %r25, %r15, %r20
	xor %r24, %r24, %r25
	or %r22, %r22, %r18
	xor %r22, %r22, %r18
	xor %r25, %r16, %r22
	xor %r14, %r14, %r21
	xor %r25, %r25, %r11
	and %r25, %r25, %r14
	xor %r25, %r25, %r11
	or %r25, %r25, %r17
	xor %r25, %r25, %r17
	xor %r25, %r25, %r2
	or %r2, %r16, %r23
	xor %r2, %r2, %r23
	xor %r22, %r22, %r14
	or %r22, %r24, %r22
	or %r22, %r22, %r2
	xor %r22, %r22, %r2
	or %r2, %r21, %r22
	xor %r2, %r2, %r22
	and %r12, %r12, %r22
	xor %r14, %r14, %r12
	and %r20, %r16, %r20
	or %r20, %r14, %r20
	xor %r23, %r23, %r20
	and %r23, %r23, %r17
	xor %r23, %r23, %r24
	xor %r18, %r18, %r6
	xor %r22, %r22, %r18
	and %r15, %r15, %r14
	xor %r22, %r22, %r15
	or %r2, %r2, %r17
	xor %r2, %r2, %r22
	xor %r16, %r21, %r16
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r19, %r19, %r14
	xor %r16, %r16, %r19
	and %r21, %r21, %r17
	xor %r21, %r21, %r16
	ld %r0, 368(%r10)
	xor %r0, %r0, %r23
	std %r0, 368(%r10)
	ld %r0, 448(%r10)
	xor %r0, %r0, %r25
	std %r0, 448(%r10)
	ld %r0, 160(%r10)
	xor %r0, %r0, %r21
	std %r0, 160(%r10)
	ld %r0, 48(%r10)
	xor %r0, %r0, %r2
	std %r0, 48(%r10)
	rldicr %r12, %r9, 51, 12
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 456(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 50, 13
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 24(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 49, 14
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 88(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 48, 15
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 152(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 47, 16
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 216(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 46, 17
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 280(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r17, %r12
	and %r2, %r18, %r2
	xor %r6, %r6, %r2
	xor %r19, %r12, %r6
	or %r20, %r14, %r19
	xor %r20, %r20, %r19
	and %r19, %r18, %r19
	xor %r21, %r17, %r19
	xor %r22, %r18, %r16
	or %r23, %r21, %r22
	xor %r24, %r6, %r23
	and %r25, %r16, %r24
	or %r26, %r25, %r12
	xor %r26, %r26, %r12
	or %r21, %r20, %r21
	xor %r27, %r26, %r21
	and %r28, %r27, %r15
	xor %r28, %r28, %r24
	xor %r23, %r17, %r23
	or %r29, %r12, %r23
	xor %r29, %r29, %r23
	xor %r16, %r16, %r29
	or %r29, %r14, %r25
	xor %r29, %r29, %r25
	or %r29, %r16, %r29
	or %r17, %r17, %r22
	xor %r27, %r27, %r17
	or %r2, %r2, %r29
	xor %r27, %r27, %r2
	or %r24, %r18, %r24
	and %r21, %r21, %r24
	xor %r21, %r16, %r21
	xor %r26, %r26, %r11
	and %r26, %r26, %r21
	or %r20, %r20, %r15
	xor %r20, %r20, %r26
	xor %r6, %r6, %r21
	or %r14, %r14, %r6
	xor %r14, %r14, %r6
	xor %r17, %r17, %r11
	xor %r23, %r23, %r17
	xor %r14, %r14, %r23
	or %r14, %r14, %r15
	xor %r14, %r14, %r15
	xor %r14, %r14, %r27
	xor %r12, %r12, %r19
	xor %r18, %r18, %r16
	and %r12, %r12, %r18
	xor %r25, %r25, %r23
	xor %r12, %r12, %r25
	or %r29, %r29, %r15
	xor %r29, %r29, %r15
	xor %r29, %r29, %r12
	ld %r0, 336(%r10)
	xor %r0, %r0, %r28
	std %r0, 336(%r10)
	ld %r0, 352(%r10)
	xor %r0, %r0, %r20
	std %r0, 352(%r10)
	ld %r0, 192(%r10)
	xor %r0, %r0, %r14
	std %r0, 192(%r10)
	ld %r0, 304(%r10)
	xor %r0, %r0, %r29
	std %r0, 304(%r10)
	rldicr %r12, %r9, 57, 6
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 200(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 56, 7
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 264(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 55, 8
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 328(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 54, 9
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 392(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 53, 10
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 456(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 52, 11
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 24(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r15, %r14
	xor %r2, %r16, %r6
	and %r19, %r12, %r2
	and %r20, %r15, %r6
	xor %r21, %r17, %r20
	and %r22, %r19, %r21
	and %r23, %r12, %r20
	xor %r24, %r16, %r23
	or %r25, %r21, %r24
	xor %r6, %r12, %r6
	xor %r26, %r25, %r6
	or %r27, %r18, %r22
	xor %r27, %r27, %r22
	xor %r27, %r27, %r26
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r26, %r21, %r2
	xor %r24, %r19, %r24
	xor %r26, %r26, %r24
	xor %r19, %r19, %r6
	or %r15, %r15, %r19
	xor %r15, %r15, %r19
	or %r6, %r21, %r15
	xor %r6, %r6, %r15
	xor %r14, %r14, %r24
	xor %r6, %r6, %r14
	or %r19, %r19, %r23
	xor %r19, %r19, %r23
	or %r15, %r15, %r19
	xor %r25, %r17, %r25
	and %r25, %r6, %r25
	xor %r25, %r15, %r25
	and %r23, %r25, %r18
	xor %r23, %r23, %r6
	or %r21, %r21, %r16
	xor %r21, %r21, %r16
	or %r19, %r19, %r21
	or %r20, %r20, %r6
	and %r19, %r19, %r20
	xor %r25, %r25, %r19
	xor %r2, %r2, %r15
	and %r12, %r12, %r2
	or %r22, %r22, %r12
	xor %r19, %r19, %r22
	or %r12, %r19, %r18
	xor %r12, %r12, %r18
	xor %r12, %r12, %r26
	and %r17, %r17, %r22
	xor %r26, %r26, %r11
	xor %r17, %r17, %r26
	xor %r19, %r19, %r17
	or %r25, %r25, %r18
	xor %r25, %r25, %r19
	ld %r0, 112(%r10)
	xor %r0, %r0, %r27
	std %r0, 112(%r10)
	ld %r0, 144(%r10)
	xor %r0, %r0, %r23
	std %r0, 144(%r10)
	ld %r0, 288(%r10)
	xor %r0, %r0, %r25
	std %r0, 288(%r10)
	ld %r0, 0(%r10)
	xor %r0, %r0, %r12
	std %r0, 0(%r10)
	rldicr %r12, %r9, 63, 0
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 504(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 62, 1
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 8(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 61, 2
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 72(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 60, 3
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 136(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 59, 4
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 200(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 58, 5
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 264(%r10)
	xor %r18, %r18, %r0
	or %r6, %r16, %r17
	xor %r6, %r6, %r17
	or %r2, %r14, %r16
	xor %r2, %r2, %r16
	xor %r2, %r15, %r2
	and %r19, %r18, %r2
	or %r20, %r19, %r6
	xor %r20, %r20, %r6
	or %r21, %r17, %r2
	xor %r21, %r21, %r2
	or %r22, %r18, %r21
	or %r23, %r17, %r16
	xor %r23, %r23, %r16
	xor %r23, %r14, %r23
	and %r24, %r22, %r23
	or %r19, %r19, %r24
	xor %r2, %r2, %r11
	xor %r24, %r24, %r2
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r24, %r24, %r16
	xor %r6, %r6, %r24
	or %r16, %r20, %r12
	xor %r16, %r16, %r6
	xor %r6, %r18, %r6
	and %r22, %r14, %r6
	xor %r24, %r17, %r24
	xor %r22, %r22, %r24
	xor %r21, %r21, %r22
	xor %r22, %r19, %r22
	or %r17, %r17, %r22
	xor %r14, %r14, %r6
	xor %r17, %r17, %r14
	and %r19, %r19, %r12
	xor %r19, %r19, %r17
	xor %r23, %r23, %r21
	or %r24, %r15, %r24
	xor %r24, %r23, %r24
	xor %r18, %r18, %r24
	and %r18, %r18, %r12
	xor %r18, %r18, %r21
	or %r23, %r23, %r15
	xor %r23, %r23, %r15
	and %r17, %r17, %r23
	xor %r20, %r20, %r24
	xor %r17, %r17, %r20
	or %r17, %r17, %r12
	xor %r17, %r17, %r21
	ld %r0, 208(%r10)
	xor %r0, %r0, %r18
	std %r0, 208(%r10)
	ld %r0, 96(%r10)
	xor %r0, %r0, %r19
	std %r0, 96(%r10)
	ld %r0, 320(%r10)
	xor %r0, %r0, %r16
	std %r0, 320(%r10)
	ld %r0, 240(%r10)
	xor %r0, %r0, %r17
	std %r0, 240(%r10)
	ld %r9, 0(%r3)
	xor %r9, %r9, %r11
	addi %r3, %r3, -8
	rldicr %r12, %r9, 21, 42
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 240(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 20, 43
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 304(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 19, 44
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 368(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 18, 45
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 432(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 17, 46
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 496(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 16, 47
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 0(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r14
	xor %r6, %r6, %r14
	xor %r2, %r15, %r6
	or %r19, %r16, %r12
	xor %r20, %r18, %r16
	and %r21, %r19, %r20
	xor %r22, %r15, %r21
	or %r23, %r22, %r2
	xor %r23, %r23, %r2
	xor %r24, %r14, %r12
	xor %r25, %r16, %r24
	xor %r25, %r25, %r11
	and %r25, %r25, %r2
	or %r21, %r12, %r21
	xor %r25, %r25, %r21
	or %r21, %r25, %r23
	xor %r21, %r21, %r23
	or %r12, %r18, %r12
	or %r26, %r25, %r12
	xor %r22, %r22, %r11
	and %r22, %r22, %r14
	xor %r27, %r26, %r22
	or %r15, %r15, %r12
	xor %r15, %r15, %r12
	xor %r15, %r22, %r15
	xor %r20, %r20, %r11
	and %r20, %r20, %r24
	or %r15, %r15, %r20
	or %r16, %r16, %r6
	xor %r16, %r16, %r6
	xor %r6, %r2, %r26
	or %r6, %r6, %r16
	xor %r6, %r6, %r16
	xor %r16, %r6, %r11
	and %r25, %r19, %r25
	xor %r16, %r16, %r25
	or %r27, %r27, %r17
	xor %r27, %r27, %r17
	xor %r27, %r27, %r16
	xor %r6, %r24, %r6
	or %r22, %r22, %r6
	xor %r22, %r19, %r22
	xor %r18, %r18, %r22
	xor %r16, %r16, %r18
	or %r23, %r23, %r17
	xor %r23, %r23, %r16
	xor %r19, %r19, %r26
	or %r19, %r15, %r19
	xor %r19, %r18, %r19
	or %r24, %r24, %r16
	xor %r24, %r19, %r24
	or %r16, %r21, %r17
	xor %r16, %r16, %r24
	or %r14, %r14, %r2
	or %r14, %r14, %r19
	xor %r14, %r14, %r19
	and %r21, %r21, %r18
	xor %r14, %r14, %r21
	or %r14, %r14, %r17
	xor %r14, %r14, %r15
	ld %r0, 72(%r10)
	xor %r0, %r0, %r14
	std %r0, 72(%r10)
	ld %r0, 88(%r10)
	xor %r0, %r0, %r27
	std %r0, 88(%r10)
	ld %r0, 472(%r10)
	xor %r0, %r0, %r16
	std %r0, 472(%r10)
	ld %r0, 488(%r10)
	xor %r0, %r0, %r23
	std %r0, 488(%r10)
	rldicr %r12, %r9, 27, 36
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 480(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 26, 37
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 48(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 25, 38
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 112(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 24, 39
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 176(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 23, 40
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 240(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 22, 41
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 304(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r18, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r19, %r17, %r2
	or %r20, %r6, %r12
	xor %r20, %r20, %r12
	and %r21, %r18, %r6
	xor %r14, %r14, %r21
	or %r21, %r14, %r20
	xor %r21, %r21, %r20
	and %r22, %r16, %r12
	xor %r2, %r2, %r20
	and %r2, %r19, %r2
	or %r20, %r2, %r22
	xor %r20, %r20, %r22
	and %r23, %r16, %r2
	xor %r18, %r18, %r11
	xor %r18, %r23, %r18
	xor %r12, %r12, %r6
	or %r24, %r12, %r22
	xor %r24, %r24, %r22
	xor %r25, %r18, %r24
	xor %r20, %r20, %r11
	and %r20, %r20, %r15
	xor %r20, %r20, %r25
	or %r17, %r17, %r24
	xor %r17, %r17, %r24
	xor %r14, %r14, %r17
	or %r18, %r18, %r14
	xor %r18, %r18, %r14
	xor %r16, %r16, %r12
	xor %r18, %r18, %r16
	or %r24, %r19, %r15
	xor %r24, %r24, %r15
	xor %r24, %r24, %r18
	xor %r23, %r23, %r17
	or %r16, %r16, %r23
	xor %r19, %r19, %r25
	or %r22, %r22, %r19
	xor %r23, %r16, %r22
	xor %r2, %r2, %r25
	xor %r18, %r18, %r2
	and %r22, %r22, %r18
	and %r6, %r6, %r16
	xor %r22, %r22, %r6
	or %r6, %r22, %r15
	xor %r6, %r6, %r23
	or %r22, %r22, %r14
	xor %r22, %r22, %r14
	or %r12, %r12, %r19
	xor %r22, %r22, %r12
	or %r21, %r21, %r15
	xor %r21, %r21, %r22
	ld %r0, 408(%r10)
	xor %r0, %r0, %r21
	std %r0, 408(%r10)
	ld %r0, 440(%r10)
	xor %r0, %r0, %r6
	std %r0, 440(%r10)
	ld %r0, 264(%r10)
	xor %r0, %r0, %r20
	std %r0, 264(%r10)
	ld %r0, 232(%r10)
	xor %r0, %r0, %r24
	std %r0, 232(%r10)
	rldicr %r12, %r9, 33, 30
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 224(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 32, 31
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 288(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 31, 32
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 352(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 30, 33
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 416(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 29, 34
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 480(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 28, 35
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 48(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r17
	xor %r6, %r6, %r17
	xor %r2, %r16, %r12
	or %r19, %r6, %r2
	xor %r20, %r15, %r12
	or %r21, %r20, %r18
	xor %r21, %r21, %r18
	xor %r22, %r19, %r21
	xor %r23, %r17, %r2
	or %r24, %r23, %r12
	xor %r24, %r24, %r12
	xor %r19, %r19, %r24
	or %r24, %r22, %r19
	xor %r24, %r24, %r19
	and %r25, %r12, %r22
	or %r25, %r15, %r25
	and %r25, %r18, %r25
	xor %r25, %r23, %r25
	or %r26, %r22, %r14
	xor %r26, %r26, %r14
	xor %r26, %r26, %r25
	and %r2, %r2, %r20
	xor %r20, %r18, %r15
	xor %r27, %r19, %r20
	or %r27, %r16, %r27
	or %r27, %r27, %r2
	xor %r27, %r27, %r2
	or %r21, %r21, %r20
	or %r20, %r25, %r21
	xor %r20, %r20, %r21
	and %r12, %r15, %r12
	or %r2, %r12, %r17
	xor %r2, %r2, %r17
	xor %r20, %r20, %r2
	and %r19, %r19, %r20
	or %r12, %r23, %r12
	or %r12, %r12, %r19
	xor %r12, %r12, %r19
	xor %r18, %r18, %r12
	and %r27, %r27, %r14
	xor %r27, %r27, %r18
	xor %r22, %r22, %r11
	or %r17, %r17, %r22
	or %r16, %r16, %r17
	xor %r23, %r23, %r16
	xor %r21, %r21, %r23
	xor %r24, %r24, %r11
	and %r24, %r24, %r14
	xor %r24, %r24, %r21
	and %r15, %r15, %r22
	xor %r25, %r25, %r15
	or %r23, %r23, %r25
	xor %r6, %r6, %r18
	xor %r23, %r23, %r6
	or %r20, %r20, %r14
	xor %r20, %r20, %r23
	ld %r0, 184(%r10)
	xor %r0, %r0, %r26
	std %r0, 184(%r10)
	ld %r0, 136(%r10)
	xor %r0, %r0, %r20
	std %r0, 136(%r10)
	ld %r0, 40(%r10)
	xor %r0, %r0, %r27
	std %r0, 40(%r10)
	ld %r0, 24(%r10)
	xor %r0, %r0, %r24
	std %r0, 24(%r10)
	rldicr %r12, %r9, 39, 24
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 464(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 38, 25
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 32(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 37, 26
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 96(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 36, 27
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 160(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 35, 28
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 224(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 34, 29
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 288(%r10)
	xor %r18, %r18, %r0
	xor %r18, %r18, %r16
	xor %r16, %r16, %r14
	or %r6, %r17, %r15
	xor %r6, %r14, %r6
	xor %r6, %r6, %r11
	and %r6, %r6, %r16
	or %r2, %r16, %r17
	xor %r2, %r2, %r17
	xor %r19, %r15, %r2
	or %r20, %r18, %r19
	or %r20, %r20, %r6
	xor %r20, %r20, %r6
	xor %r21, %r17, %r20
	and %r19, %r19, %r21
	or %r16, %r16, %r19
	xor %r16, %r16, %r19
	xor %r18, %r18, %r21
	xor %r16, %r16, %r11
	and %r16, %r16, %r18
	xor %r6, %r6, %r16
	xor %r17, %r17, %r15
	or %r14, %r14, %r2
	xor %r18, %r18, %r14
	or %r14, %r18, %r17
	xor %r14, %r14, %r17
	xor %r20, %r20, %r14
	or %r14, %r12, %r6
	xor %r14, %r14, %r6
	xor %r14, %r14, %r20
	xor %r20, %r20, %r11
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r2, %r2, %r20
	xor %r6, %r6, %r20
	or %r6, %r6, %r17
	xor %r6, %r6, %r17
	or %r19, %r19, %r6
	xor %r18, %r18, %r19
	or %r19, %r21, %r12
	xor %r19, %r19, %r18
	and %r12, %r12, %r21
	xor %r12, %r12, %r18
	ld %r0, 504(%r10)
	xor %r0, %r0, %r12
	std %r0, 504(%r10)
	ld %r0, 424(%r10)
	xor %r0, %r0, %r19
	std %r0, 424(%r10)
	ld %r0, 280(%r10)
	xor %r0, %r0, %r2
	std %r0, 280(%r10)
	ld %r0, 392(%r10)
	xor %r0, %r0, %r14
	std %r0, 392(%r10)
	rldicr %r12, %r9, 45, 18
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 208(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 44, 19
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 272(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 43, 20
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 336(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 42, 21
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 400(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 41, 22
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 464(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 40, 23
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 32(%r10)
	xor %r18, %r18, %r0
	or %r6, %r18, %r16
	or %r2, %r6, %r12
	xor %r2, %r2, %r12
	xor %r19, %r18, %r2
	xor %r20, %r16, %r19
	or %r21, %r15, %r20
	or %r2, %r2, %r15
	xor %r2, %r2, %r15
	xor %r16, %r16, %r2
	and %r2, %r14, %r16
	or %r20, %r18, %r20
	xor %r2, %r2, %r20
	xor %r2, %r15, %r2
	xor %r12, %r12, %r2
	or %r22, %r19, %r12
	and %r23, %r14, %r22
	xor %r24, %r19, %r23
	and %r25, %r15, %r20
	xor %r24, %r24, %r25
	or %r22, %r22, %r18
	xor %r22, %r22, %r18
	xor %r25, %r16, %r22
	xor %r14, %r14, %r21
	xor %r25, %r25, %r11
	and %r25, %r25, %r14
	xor %r25, %r25, %r11
	or %r25, %r25, %r17
	xor %r25, %r25, %r17
	xor %r25, %r25, %r2
	or %r2, %r16, %r23
	xor %r2, %r2, %r23
	xor %r22, %r22, %r14
	or %r22, %r24, %r22
	or %r22, %r22, %r2
	xor %r22, %r22, %r2
	or %r2, %r21, %r22
	xor %r2, %r2, %r22
	and %r12, %r12, %r22
	xor %r14, %r14, %r12
	and %r20, %r16, %r20
	or %r20, %r14, %r20
	xor %r23, %r23, %r20
	and %r23, %r23, %r17
	xor %r23, %r23, %r24
	xor %r18, %r18, %r6
	xor %r22, %r22, %r18
	and %r15, %r15, %r14
	xor %r22, %r22, %r15
	or %r2, %r2, %r17
	xor %r2, %r2, %r22
	xor %r16, %r21, %r16
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r19, %r19, %r14
	xor %r16, %r16, %r19
	and %r21, %r21, %r17
	xor %r21, %r21, %r16
	ld %r0, 376(%r10)
	xor %r0, %r0, %r23
	std %r0, 376(%r10)
	ld %r0, 456(%r10)
	xor %r0, %r0, %r25
	std %r0, 456(%r10)
	ld %r0, 168(%r10)
	xor %r0, %r0, %r21
	std %r0, 168(%r10)
	ld %r0, 56(%r10)
	xor %r0, %r0, %r2
	std %r0, 56(%r10)
	rldicr %r12, %r9, 51, 12
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 448(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 50, 13
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 16(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 49, 14
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 80(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 48, 15
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 144(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 47, 16
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 208(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 46, 17
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 272(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r17, %r14
	or %r2, %r17, %r12
	and %r2, %r18, %r2
	xor %r6, %r6, %r2
	xor %r19, %r12, %r6
	or %r20, %r14, %r19
	xor %r20, %r20, %r19
	and %r19, %r18, %r19
	xor %r21, %r17, %r19
	xor %r22, %r18, %r16
	or %r23, %r21, %r22
	xor %r24, %r6, %r23
	and %r25, %r16, %r24
	or %r26, %r25, %r12
	xor %r26, %r26, %r12
	or %r21, %r20, %r21
	xor %r27, %r26, %r21
	and %r28, %r27, %r15
	xor %r28, %r28, %r24
	xor %r23, %r17, %r23
	or %r29, %r12, %r23
	xor %r29, %r29, %r23
	xor %r16, %r16, %r29
	or %r29, %r14, %r25
	xor %r29, %r29, %r25
	or %r29, %r16, %r29
	or %r17, %r17, %r22
	xor %r27, %r27, %r17
	or %r2, %r2, %r29
	xor %r27, %r27, %r2
	or %r24, %r18, %r24
	and %r21, %r21, %r24
	xor %r21, %r16, %r21
	xor %r26, %r26, %r11
	and %r26, %r26, %r21
	or %r20, %r20, %r15
	xor %r20, %r20, %r26
	xor %r6, %r6, %r21
	or %r14, %r14, %r6
	xor %r14, %r14, %r6
	xor %r17, %r17, %r11
	xor %r23, %r23, %r17
	xor %r14, %r14, %r23
	or %r14, %r14, %r15
	xor %r14, %r14, %r15
	xor %r14, %r14, %r27
	xor %r12, %r12, %r19
	xor %r18, %r18, %r16
	and %r12, %r12, %r18
	xor %r25, %r25, %r23
	xor %r12, %r12, %r25
	or %r29, %r29, %r15
	xor %r29, %r29, %r15
	xor %r29, %r29, %r12
	ld %r0, 344(%r10)
	xor %r0, %r0, %r28
	std %r0, 344(%r10)
	ld %r0, 360(%r10)
	xor %r0, %r0, %r20
	std %r0, 360(%r10)
	ld %r0, 200(%r10)
	xor %r0, %r0, %r14
	std %r0, 200(%r10)
	ld %r0, 312(%r10)
	xor %r0, %r0, %r29
	std %r0, 312(%r10)
	rldicr %r12, %r9, 57, 6
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 192(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 56, 7
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 256(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 55, 8
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 320(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 54, 9
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 384(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 53, 10
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 448(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 52, 11
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 16(%r10)
	xor %r18, %r18, %r0
	xor %r6, %r15, %r14
	xor %r2, %r16, %r6
	and %r19, %r12, %r2
	and %r20, %r15, %r6
	xor %r21, %r17, %r20
	and %r22, %r19, %r21
	and %r23, %r12, %r20
	xor %r24, %r16, %r23
	or %r25, %r21, %r24
	xor %r6, %r12, %r6
	xor %r26, %r25, %r6
	or %r27, %r18, %r22
	xor %r27, %r27, %r22
	xor %r27, %r27, %r26
	xor %r2, %r2, %r11
	and %r2, %r2, %r14
	or %r26, %r21, %r2
	xor %r24, %r19, %r24
	xor %r26, %r26, %r24
	xor %r19, %r19, %r6
	or %r15, %r15, %r19
	xor %r15, %r15, %r19
	or %r6, %r21, %r15
	xor %r6, %r6, %r15
	xor %r14, %r14, %r24
	xor %r6, %r6, %r14
	or %r19, %r19, %r23
	xor %r19, %r19, %r23
	or %r15, %r15, %r19
	xor %r25, %r17, %r25
	and %r25, %r6, %r25
	xor %r25, %r15, %r25
	and %r23, %r25, %r18
	xor %r23, %r23, %r6
	or %r21, %r21, %r16
	xor %r21, %r21, %r16
	or %r19, %r19, %r21
	or %r20, %r20, %r6
	and %r19, %r19, %r20
	xor %r25, %r25, %r19
	xor %r2, %r2, %r15
	and %r12, %r12, %r2
	or %r22, %r22, %r12
	xor %r19, %r19, %r22
	or %r12, %r19, %r18
	xor %r12, %r12, %r18
	xor %r12, %r12, %r26
	and %r17, %r17, %r22
	xor %r26, %r26, %r11
	xor %r17, %r17, %r26
	xor %r19, %r19, %r17
	or %r25, %r25, %r18
	xor %r25, %r25, %r19
	ld %r0, 120(%r10)
	xor %r0, %r0, %r27
	std %r0, 120(%r10)
	ld %r0, 152(%r10)
	xor %r0, %r0, %r23
	std %r0, 152(%r10)
	ld %r0, 296(%r10)
	xor %r0, %r0, %r25
	std %r0, 296(%r10)
	ld %r0, 8(%r10)
	xor %r0, %r0, %r12
	std %r0, 8(%r10)
	rldicr %r12, %r9, 63, 0
	rldicl %r12, %r12, 1, 63
	addi %r12, %r12, -1
	ld %r0, 496(%r10)
	xor %r12, %r12, %r0
	rldicr %r14, %r9, 62, 1
	rldicl %r14, %r14, 1, 63
	addi %r14, %r14, -1
	ld %r0, 0(%r10)
	xor %r14, %r14, %r0
	rldicr %r15, %r9, 61, 2
	rldicl %r15, %r15, 1, 63
	addi %r15, %r15, -1
	ld %r0, 64(%r10)
	xor %r15, %r15, %r0
	rldicr %r16, %r9, 60, 3
	rldicl %r16, %r16, 1, 63
	addi %r16, %r16, -1
	ld %r0, 128(%r10)
	xor %r16, %r16, %r0
	rldicr %r17, %r9, 59, 4
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r0, 192(%r10)
	xor %r17, %r17, %r0
	rldicr %r18, %r9, 58, 5
	rldicl %r18, %r18, 1, 63
	addi %r18, %r18, -1
	ld %r0, 256(%r10)
	xor %r18, %r18, %r0
	or %r6, %r16, %r17
	xor %r6, %r6, %r17
	or %r2, %r14, %r16
	xor %r2, %r2, %r16
	xor %r2, %r15, %r2
	and %r19, %r18, %r2
	or %r20, %r19, %r6
	xor %r20, %r20, %r6
	or %r21, %r17, %r2
	xor %r21, %r21, %r2
	or %r22, %r18, %r21
	or %r23, %r17, %r16
	xor %r23, %r23, %r16
	xor %r23, %r14, %r23
	and %r24, %r22, %r23
	or %r19, %r19, %r24
	xor %r2, %r2, %r11
	xor %r24, %r24, %r2
	or %r16, %r16, %r22
	xor %r16, %r16, %r22
	xor %r24, %r24, %r16
	xor %r6, %r6, %r24
	or %r16, %r20, %r12
	xor %r16, %r16, %r6
	xor %r6, %r18, %r6
	and %r22, %r14, %r6
	xor %r24, %r17, %r24
	xor %r22, %r22, %r24
	xor %r21, %r21, %r22
	xor %r22, %r19, %r22
	or %r17, %r17, %r22
	xor %r14, %r14, %r6
	xor %r17, %r17, %r14
	and %r19, %r19, %r12
	xor %r19, %r19, %r17
	xor %r23, %r23, %r21
	or %r24, %r15, %r24
	xor %r24, %r23, %r24
	xor %r18, %r18, %r24
	and %r18, %r18, %r12
	xor %r18, %r18, %r21
	or %r23, %r23, %r15
	xor %r23, %r23, %r15
	and %r17, %r17, %r23
	xor %r20, %r20, %r24
	xor %r17, %r17, %r20
	or %r17, %r17, %r12
	xor %r17, %r17, %r21
	ld %r0, 216(%r10)
	xor %r0, %r0, %r18
	std %r0, 216(%r10)
	ld %r0, 104(%r10)
	xor %r0, %r0, %r19
	std %r0, 104(%r10)
	ld %r0, 328(%r10)
	xor %r0, %r0, %r16
	std %r0, 328(%r10)
	ld %r0, 248(%r10)
	xor %r0, %r0, %r17
	std %r0, 248(%r10)
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	ld %r12, 0(%r10)
	ld %r14, 8(%r10)
	std %r14, 0(%r10)
	std %r12, 8(%r10)
	ld %r12, 64(%r10)
	ld %r14, 72(%r10)
	std %r14, 64(%r10)
	std %r12, 72(%r10)
	ld %r12, 128(%r10)
	ld %r14, 136(%r10)
	std %r14, 128(%r10)
	std %r12, 136(%r10)
	ld %r12, 192(%r10)
	ld %r14, 200(%r10)
	std %r14, 192(%r10)
	std %r12, 200(%r10)
	ld %r12, 256(%r10)
	ld %r14, 264(%r10)
	std %r14, 256(%r10)
	std %r12, 264(%r10)
	ld %r12, 320(%r10)
	ld %r14, 328(%r10)
	std %r14, 320(%r10)
	std %r12, 328(%r10)
	ld %r12, 384(%r10)
	ld %r14, 392(%r10)
	std %r14, 384(%r10)
	std %r12, 392(%r10)
	ld %r12, 448(%r10)
	ld %r14, 456(%r10)
	std %r14, 448(%r10)
	std %r12, 456(%r10)
	ld %r12, 16(%r10)
	ld %r14, 24(%r10)
	std %r14, 16(%r10)
	std %r12, 24(%r10)
	ld %r12, 80(%r10)
	ld %r14, 88(%r10)
	std %r14, 80(%r10)
	std %r12, 88(%r10)
	ld %r12, 144(%r10)
	ld %r14, 152(%r10)
	std %r14, 144(%r10)
	std %r12, 152(%r10)
	ld %r12, 208(%r10)
	ld %r14, 216(%r10)
	std %r14, 208(%r10)
	std %r12, 216(%r10)
	ld %r12, 272(%r10)
	ld %r14, 280(%r10)
	std %r14, 272(%r10)
	std %r12, 280(%r10)
	ld %r12, 336(%r10)
	ld %r14, 344(%r10)
	std %r14, 336(%r10)
	std %r12, 344(%r10)
	ld %r12, 400(%r10)
	ld %r14, 408(%r10)
	std %r14, 400(%r10)
	std %r12, 408(%r10)
	ld %r12, 464(%r10)
	ld %r14, 472(%r10)
	std %r14, 464(%r10)
	std %r12, 472(%r10)
	ld %r12, 32(%r10)
	ld %r14, 40(%r10)
	std %r14, 32(%r10)
	std %r12, 40(%r10)
	ld %r12, 96(%r10)
	ld %r14, 104(%r10)
	std %r14, 96(%r10)
	std %r12, 104(%r10)
	ld %r12, 160(%r10)
	ld %r14, 168(%r10)
	std %r14, 160(%r10)
	std %r12, 168(%r10)
	ld %r12, 224(%r10)
	ld %r14, 232(%r10)
	std %r14, 224(%r10)
	std %r12, 232(%r10)
	ld %r12, 288(%r10)
	ld %r14, 296(%r10)
	std %r14, 288(%r10)
	std %r12, 296(%r10)
	ld %r12, 352(%r10)
	ld %r14, 360(%r10)
	std %r14, 352(%r10)
	std %r12, 360(%r10)
	ld %r12, 416(%r10)
	ld %r14, 424(%r10)
	std %r14, 416(%r10)
	std %r12, 424(%r10)
	ld %r12, 480(%r10)
	ld %r14, 488(%r10)
	std %r14, 480(%r10)
	std %r12, 488(%r10)
	ld %r12, 48(%r10)
	ld %r14, 56(%r10)
	std %r14, 48(%r10)
	std %r12, 56(%r10)
	ld %r12, 112(%r10)
	ld %r14, 120(%r10)
	std %r14, 112(%r10)
	std %r12, 120(%r10)
	ld %r12, 176(%r10)
	ld %r14, 184(%r10)
	std %r14, 176(%r10)
	std %r12, 184(%r10)
	ld %r12, 240(%r10)
	ld %r14, 248(%r10)
	std %r14, 240(%r10)
	std %r12, 248(%r10)
	ld %r12, 304(%r10)
	ld %r14, 312(%r10)
	std %r14, 304(%r10)
	std %r12, 312(%r10)
	ld %r12, 368(%r10)
	ld %r14, 376(%r10)
	std %r14, 368(%r10)
	std %r12, 376(%r10)
	ld %r12, 432(%r10)
	ld %r14, 440(%r10)
	std %r14, 432(%r10)
	std %r12, 440(%r10)
	ld %r12, 496(%r10)
	ld %r14, 504(%r10)
	std %r14, 496(%r10)
	std %r12, 504(%r10)
	blr
