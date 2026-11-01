// The functions of `src/sha3.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_f1600:
	std %r14, 392(%r4)
	std %r15, 400(%r4)
	std %r16, 408(%r4)
	std %r17, 416(%r4)
	std %r18, 424(%r4)
	std %r19, 432(%r4)
	std %r20, 440(%r4)
	lis %r5, 0
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 1
	std %r5, 200(%r4)
	lis %r5, 0
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 32898
	std %r5, 208(%r4)
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 32906
	std %r5, 216(%r4)
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 32768
	ori %r5, %r5, 32768
	std %r5, 224(%r4)
	lis %r5, 0
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 32907
	std %r5, 232(%r4)
	lis %r5, 0
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 32768
	ori %r5, %r5, 1
	std %r5, 240(%r4)
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 32768
	ori %r5, %r5, 32897
	std %r5, 248(%r4)
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 32777
	std %r5, 256(%r4)
	lis %r5, 0
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 138
	std %r5, 264(%r4)
	lis %r5, 0
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 136
	std %r5, 272(%r4)
	lis %r5, 0
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 32768
	ori %r5, %r5, 32777
	std %r5, 280(%r4)
	lis %r5, 0
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 32768
	ori %r5, %r5, 10
	std %r5, 288(%r4)
	lis %r5, 0
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 32768
	ori %r5, %r5, 32907
	std %r5, 296(%r4)
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 139
	std %r5, 304(%r4)
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 32905
	std %r5, 312(%r4)
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 32771
	std %r5, 320(%r4)
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 32770
	std %r5, 328(%r4)
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 128
	std %r5, 336(%r4)
	lis %r5, 0
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 32778
	std %r5, 344(%r4)
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 32768
	ori %r5, %r5, 10
	std %r5, 352(%r4)
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 32768
	ori %r5, %r5, 32897
	std %r5, 360(%r4)
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 0
	ori %r5, %r5, 32896
	std %r5, 368(%r4)
	lis %r5, 0
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 32768
	ori %r5, %r5, 1
	std %r5, 376(%r4)
	lis %r5, -32768
	ori %r5, %r5, 0
	rldicr %r5, %r5, 32, 31
	oris %r5, %r5, 32768
	ori %r5, %r5, 32776
	std %r5, 384(%r4)
	lis %r18, -1
	ori %r18, %r18, 65535
	addi %r19, %r4, 200
	li %r20, 12
	ld %r5, 8(%r3)
	xor %r5, %r5, %r18
	std %r5, 8(%r3)
	ld %r5, 16(%r3)
	xor %r5, %r5, %r18
	std %r5, 16(%r3)
	ld %r5, 64(%r3)
	xor %r5, %r5, %r18
	std %r5, 64(%r3)
	ld %r5, 96(%r3)
	xor %r5, %r5, %r18
	std %r5, 96(%r3)
	ld %r5, 136(%r3)
	xor %r5, %r5, %r18
	std %r5, 136(%r3)
	ld %r5, 160(%r3)
	xor %r5, %r5, %r18
	std %r5, 160(%r3)
	ld %r6, 168(%r3)
	ld %r7, 176(%r3)
	ld %r8, 184(%r3)
	ld %r9, 192(%r3)
20:
	ld %r10, 0(%r3)
	ld %r11, 48(%r3)
	ld %r12, 96(%r3)
	ld %r14, 144(%r3)
	ld %r0, 16(%r3)
	xor %r7, %r7, %r0
	ld %r0, 24(%r3)
	xor %r8, %r8, %r0
	xor %r5, %r5, %r10
	ld %r0, 8(%r3)
	xor %r6, %r6, %r0
	ld %r0, 56(%r3)
	xor %r7, %r7, %r0
	ld %r0, 40(%r3)
	xor %r5, %r5, %r0
	addi %r15, %r9, 0
	ld %r0, 32(%r3)
	xor %r9, %r9, %r0
	xor %r7, %r7, %r12
	ld %r0, 80(%r3)
	xor %r5, %r5, %r0
	ld %r0, 64(%r3)
	xor %r8, %r8, %r0
	xor %r6, %r6, %r11
	ld %r0, 72(%r3)
	xor %r9, %r9, %r0
	ld %r0, 136(%r3)
	xor %r7, %r7, %r0
	ld %r0, 120(%r3)
	xor %r5, %r5, %r0
	ld %r0, 104(%r3)
	xor %r8, %r8, %r0
	ld %r0, 88(%r3)
	xor %r6, %r6, %r0
	ld %r0, 112(%r3)
	xor %r9, %r9, %r0
	addi %r16, %r7, 0
	rldicl %r7, %r7, 1, 0
	xor %r7, %r7, %r5
	xor %r8, %r8, %r14
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r8
	ld %r0, 128(%r3)
	xor %r6, %r6, %r0
	rldicl %r8, %r8, 1, 0
	xor %r8, %r8, %r6
	ld %r0, 152(%r3)
	xor %r9, %r9, %r0
	rldicl %r6, %r6, 1, 0
	xor %r6, %r6, %r9
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r16
	xor %r11, %r11, %r7
	xor %r12, %r12, %r8
	rldicl %r11, %r11, 44, 0
	xor %r14, %r14, %r9
	xor %r15, %r15, %r5
	rldicl %r12, %r12, 43, 0
	xor %r10, %r10, %r6
	addi %r16, %r11, 0
	rldicl %r14, %r14, 21, 0
	or %r11, %r11, %r12
	xor %r11, %r11, %r10
	rldicl %r15, %r15, 14, 0
	ld %r0, 0(%r19)
	xor %r11, %r11, %r0
	addi %r17, %r15, 0
	and %r15, %r15, %r14
	std %r11, 0(%r4)
	xor %r15, %r15, %r12
	xor %r12, %r12, %r18
	std %r15, 16(%r4)
	or %r12, %r12, %r14
	ld %r15, 176(%r3)
	xor %r12, %r12, %r16
	std %r12, 8(%r4)
	and %r16, %r16, %r10
	ld %r11, 72(%r3)
	xor %r16, %r16, %r17
	ld %r12, 80(%r3)
	std %r16, 32(%r4)
	or %r17, %r17, %r10
	ld %r10, 24(%r3)
	xor %r17, %r17, %r14
	ld %r14, 128(%r3)
	std %r17, 24(%r4)
	xor %r10, %r10, %r9
	xor %r15, %r15, %r8
	rldicl %r10, %r10, 28, 0
	xor %r14, %r14, %r7
	xor %r11, %r11, %r5
	rldicl %r15, %r15, 61, 0
	rldicl %r14, %r14, 45, 0
	xor %r12, %r12, %r6
	rldicl %r11, %r11, 20, 0
	addi %r16, %r10, 0
	or %r10, %r10, %r15
	rldicl %r12, %r12, 3, 0
	xor %r10, %r10, %r14
	std %r10, 64(%r4)
	addi %r17, %r11, 0
	and %r11, %r11, %r16
	ld %r10, 8(%r3)
	xor %r11, %r11, %r15
	xor %r15, %r15, %r18
	std %r11, 72(%r4)
	or %r15, %r15, %r14
	ld %r11, 56(%r3)
	xor %r15, %r15, %r12
	std %r15, 56(%r4)
	and %r14, %r14, %r12
	ld %r15, 160(%r3)
	xor %r14, %r14, %r17
	std %r14, 48(%r4)
	or %r17, %r17, %r12
	ld %r12, 104(%r3)
	xor %r17, %r17, %r16
	ld %r14, 152(%r3)
	std %r17, 40(%r4)
	xor %r12, %r12, %r9
	xor %r14, %r14, %r5
	rldicl %r12, %r12, 25, 0
	xor %r11, %r11, %r8
	rldicl %r14, %r14, 8, 0
	xor %r15, %r15, %r6
	rldicl %r11, %r11, 6, 0
	xor %r10, %r10, %r7
	rldicl %r15, %r15, 18, 0
	addi %r16, %r12, 0
	and %r12, %r12, %r14
	rldicl %r10, %r10, 1, 0
	xor %r14, %r14, %r18
	xor %r12, %r12, %r11
	std %r12, 88(%r4)
	addi %r17, %r15, 0
	and %r15, %r15, %r14
	ld %r12, 88(%r3)
	xor %r15, %r15, %r16
	std %r15, 96(%r4)
	or %r16, %r16, %r11
	ld %r15, 184(%r3)
	xor %r16, %r16, %r10
	std %r16, 80(%r4)
	and %r11, %r11, %r10
	xor %r11, %r11, %r17
	std %r11, 112(%r4)
	or %r17, %r17, %r10
	ld %r11, 40(%r3)
	xor %r17, %r17, %r14
	ld %r14, 136(%r3)
	std %r17, 104(%r4)
	ld %r10, 32(%r3)
	xor %r12, %r12, %r7
	xor %r14, %r14, %r8
	rldicl %r12, %r12, 10, 0
	xor %r11, %r11, %r6
	rldicl %r14, %r14, 15, 0
	xor %r15, %r15, %r9
	rldicl %r11, %r11, 36, 0
	xor %r10, %r10, %r5
	rldicl %r15, %r15, 56, 0
	addi %r16, %r12, 0
	or %r12, %r12, %r14
	rldicl %r10, %r10, 27, 0
	xor %r14, %r14, %r18
	xor %r12, %r12, %r11
	std %r12, 128(%r4)
	addi %r17, %r15, 0
	or %r15, %r15, %r14
	xor %r15, %r15, %r16
	std %r15, 136(%r4)
	and %r16, %r16, %r11
	xor %r16, %r16, %r10
	std %r16, 120(%r4)
	or %r11, %r11, %r10
	xor %r11, %r11, %r17
	std %r11, 152(%r4)
	and %r10, %r10, %r17
	xor %r10, %r10, %r14
	std %r10, 144(%r4)
	ld %r0, 16(%r3)
	xor %r8, %r8, %r0
	ld %r0, 64(%r3)
	xor %r9, %r9, %r0
	rldicl %r8, %r8, 62, 0
	ld %r0, 168(%r3)
	xor %r7, %r7, %r0
	rldicl %r9, %r9, 55, 0
	ld %r0, 112(%r3)
	xor %r5, %r5, %r0
	rldicl %r7, %r7, 2, 0
	ld %r0, 120(%r3)
	xor %r6, %r6, %r0
	rldicl %r5, %r5, 39, 0
	rldicl %r6, %r6, 41, 0
	addi %r16, %r8, 0
	and %r8, %r8, %r9
	xor %r9, %r9, %r18
	xor %r8, %r8, %r7
	std %r8, 192(%r4)
	addi %r17, %r5, 0
	and %r5, %r5, %r9
	xor %r5, %r5, %r16
	std %r5, 160(%r4)
	or %r16, %r16, %r7
	xor %r16, %r16, %r6
	std %r16, 184(%r4)
	and %r7, %r7, %r6
	xor %r7, %r7, %r17
	std %r7, 176(%r4)
	or %r6, %r6, %r17
	xor %r6, %r6, %r9
	std %r6, 168(%r4)
	addi %r9, %r8, 0
	addi %r8, %r16, 0
	ld %r10, 0(%r4)
	ld %r11, 48(%r4)
	ld %r12, 96(%r4)
	ld %r14, 144(%r4)
	ld %r0, 16(%r4)
	xor %r7, %r7, %r0
	ld %r0, 24(%r4)
	xor %r8, %r8, %r0
	xor %r5, %r5, %r10
	ld %r0, 8(%r4)
	xor %r6, %r6, %r0
	ld %r0, 56(%r4)
	xor %r7, %r7, %r0
	ld %r0, 40(%r4)
	xor %r5, %r5, %r0
	addi %r15, %r9, 0
	ld %r0, 32(%r4)
	xor %r9, %r9, %r0
	xor %r7, %r7, %r12
	ld %r0, 80(%r4)
	xor %r5, %r5, %r0
	ld %r0, 64(%r4)
	xor %r8, %r8, %r0
	xor %r6, %r6, %r11
	ld %r0, 72(%r4)
	xor %r9, %r9, %r0
	ld %r0, 136(%r4)
	xor %r7, %r7, %r0
	ld %r0, 120(%r4)
	xor %r5, %r5, %r0
	ld %r0, 104(%r4)
	xor %r8, %r8, %r0
	ld %r0, 88(%r4)
	xor %r6, %r6, %r0
	ld %r0, 112(%r4)
	xor %r9, %r9, %r0
	addi %r16, %r7, 0
	rldicl %r7, %r7, 1, 0
	xor %r7, %r7, %r5
	xor %r8, %r8, %r14
	rldicl %r5, %r5, 1, 0
	xor %r5, %r5, %r8
	ld %r0, 128(%r4)
	xor %r6, %r6, %r0
	rldicl %r8, %r8, 1, 0
	xor %r8, %r8, %r6
	ld %r0, 152(%r4)
	xor %r9, %r9, %r0
	rldicl %r6, %r6, 1, 0
	xor %r6, %r6, %r9
	rldicl %r9, %r9, 1, 0
	xor %r9, %r9, %r16
	xor %r11, %r11, %r7
	xor %r12, %r12, %r8
	rldicl %r11, %r11, 44, 0
	xor %r14, %r14, %r9
	xor %r15, %r15, %r5
	rldicl %r12, %r12, 43, 0
	xor %r10, %r10, %r6
	addi %r16, %r11, 0
	rldicl %r14, %r14, 21, 0
	or %r11, %r11, %r12
	xor %r11, %r11, %r10
	rldicl %r15, %r15, 14, 0
	ld %r0, 8(%r19)
	xor %r11, %r11, %r0
	addi %r17, %r15, 0
	and %r15, %r15, %r14
	std %r11, 0(%r3)
	xor %r15, %r15, %r12
	xor %r12, %r12, %r18
	std %r15, 16(%r3)
	or %r12, %r12, %r14
	ld %r15, 176(%r4)
	xor %r12, %r12, %r16
	std %r12, 8(%r3)
	and %r16, %r16, %r10
	ld %r11, 72(%r4)
	xor %r16, %r16, %r17
	ld %r12, 80(%r4)
	std %r16, 32(%r3)
	or %r17, %r17, %r10
	ld %r10, 24(%r4)
	xor %r17, %r17, %r14
	ld %r14, 128(%r4)
	std %r17, 24(%r3)
	xor %r10, %r10, %r9
	xor %r15, %r15, %r8
	rldicl %r10, %r10, 28, 0
	xor %r14, %r14, %r7
	xor %r11, %r11, %r5
	rldicl %r15, %r15, 61, 0
	rldicl %r14, %r14, 45, 0
	xor %r12, %r12, %r6
	rldicl %r11, %r11, 20, 0
	addi %r16, %r10, 0
	or %r10, %r10, %r15
	rldicl %r12, %r12, 3, 0
	xor %r10, %r10, %r14
	std %r10, 64(%r3)
	addi %r17, %r11, 0
	and %r11, %r11, %r16
	ld %r10, 8(%r4)
	xor %r11, %r11, %r15
	xor %r15, %r15, %r18
	std %r11, 72(%r3)
	or %r15, %r15, %r14
	ld %r11, 56(%r4)
	xor %r15, %r15, %r12
	std %r15, 56(%r3)
	and %r14, %r14, %r12
	ld %r15, 160(%r4)
	xor %r14, %r14, %r17
	std %r14, 48(%r3)
	or %r17, %r17, %r12
	ld %r12, 104(%r4)
	xor %r17, %r17, %r16
	ld %r14, 152(%r4)
	std %r17, 40(%r3)
	xor %r12, %r12, %r9
	xor %r14, %r14, %r5
	rldicl %r12, %r12, 25, 0
	xor %r11, %r11, %r8
	rldicl %r14, %r14, 8, 0
	xor %r15, %r15, %r6
	rldicl %r11, %r11, 6, 0
	xor %r10, %r10, %r7
	rldicl %r15, %r15, 18, 0
	addi %r16, %r12, 0
	and %r12, %r12, %r14
	rldicl %r10, %r10, 1, 0
	xor %r14, %r14, %r18
	xor %r12, %r12, %r11
	std %r12, 88(%r3)
	addi %r17, %r15, 0
	and %r15, %r15, %r14
	ld %r12, 88(%r4)
	xor %r15, %r15, %r16
	std %r15, 96(%r3)
	or %r16, %r16, %r11
	ld %r15, 184(%r4)
	xor %r16, %r16, %r10
	std %r16, 80(%r3)
	and %r11, %r11, %r10
	xor %r11, %r11, %r17
	std %r11, 112(%r3)
	or %r17, %r17, %r10
	ld %r11, 40(%r4)
	xor %r17, %r17, %r14
	ld %r14, 136(%r4)
	std %r17, 104(%r3)
	ld %r10, 32(%r4)
	xor %r12, %r12, %r7
	xor %r14, %r14, %r8
	rldicl %r12, %r12, 10, 0
	xor %r11, %r11, %r6
	rldicl %r14, %r14, 15, 0
	xor %r15, %r15, %r9
	rldicl %r11, %r11, 36, 0
	xor %r10, %r10, %r5
	rldicl %r15, %r15, 56, 0
	addi %r16, %r12, 0
	or %r12, %r12, %r14
	rldicl %r10, %r10, 27, 0
	xor %r14, %r14, %r18
	xor %r12, %r12, %r11
	std %r12, 128(%r3)
	addi %r17, %r15, 0
	or %r15, %r15, %r14
	xor %r15, %r15, %r16
	std %r15, 136(%r3)
	and %r16, %r16, %r11
	xor %r16, %r16, %r10
	std %r16, 120(%r3)
	or %r11, %r11, %r10
	xor %r11, %r11, %r17
	std %r11, 152(%r3)
	and %r10, %r10, %r17
	xor %r10, %r10, %r14
	std %r10, 144(%r3)
	ld %r0, 16(%r4)
	xor %r8, %r8, %r0
	ld %r0, 64(%r4)
	xor %r9, %r9, %r0
	rldicl %r8, %r8, 62, 0
	ld %r0, 168(%r4)
	xor %r7, %r7, %r0
	rldicl %r9, %r9, 55, 0
	ld %r0, 112(%r4)
	xor %r5, %r5, %r0
	rldicl %r7, %r7, 2, 0
	ld %r0, 120(%r4)
	xor %r6, %r6, %r0
	rldicl %r5, %r5, 39, 0
	rldicl %r6, %r6, 41, 0
	addi %r16, %r8, 0
	and %r8, %r8, %r9
	xor %r9, %r9, %r18
	xor %r8, %r8, %r7
	std %r8, 192(%r3)
	addi %r17, %r5, 0
	and %r5, %r5, %r9
	xor %r5, %r5, %r16
	std %r5, 160(%r3)
	or %r16, %r16, %r7
	xor %r16, %r16, %r6
	std %r16, 184(%r3)
	and %r7, %r7, %r6
	xor %r7, %r7, %r17
	std %r7, 176(%r3)
	or %r6, %r6, %r17
	xor %r6, %r6, %r9
	std %r6, 168(%r3)
	addi %r9, %r8, 0
	addi %r8, %r16, 0
	addi %r19, %r19, 16
	addi %r20, %r20, -1
	cmpldi %cr0, %r20, 0
	bne %cr0, 20b
	ld %r5, 8(%r3)
	xor %r5, %r5, %r18
	std %r5, 8(%r3)
	ld %r5, 16(%r3)
	xor %r5, %r5, %r18
	std %r5, 16(%r3)
	ld %r5, 64(%r3)
	xor %r5, %r5, %r18
	std %r5, 64(%r3)
	ld %r5, 96(%r3)
	xor %r5, %r5, %r18
	std %r5, 96(%r3)
	ld %r5, 136(%r3)
	xor %r5, %r5, %r18
	std %r5, 136(%r3)
	ld %r5, 160(%r3)
	xor %r5, %r5, %r18
	std %r5, 160(%r3)
	ld %r14, 392(%r4)
	ld %r15, 400(%r4)
	ld %r16, 408(%r4)
	ld %r17, 416(%r4)
	ld %r18, 424(%r4)
	ld %r19, 432(%r4)
	ld %r20, 440(%r4)
	blr

vg_keccak_absorb:
	stdu %r1, -672(%r1)
	addi %r8, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 512(%r8)
	std %r27, 520(%r8)
	std %r28, 528(%r8)
	std %r29, 536(%r8)
	std %r30, 544(%r8)
	std %r31, 552(%r8)
	addi %r26, %r3, 0
	addi %r27, %r8, 0
	addi %r28, %r4, 0
	addi %r29, %r5, 0
	addi %r30, %r6, 0
	addi %r31, %r7, 0
	cmpldi %cr0, %r31, 0
	beq %cr0, 20f
22:
	li %r10, 7
	and %r10, %r29, %r10
	addi %r11, %r31, -8
	rldicl %r11, %r11, 1, 63
	or %r10, %r10, %r11
	cmpldi %cr0, %r10, 0
	beq %cr0, 23f
	lbz %r9, 0(%r30)
	add %r10, %r26, %r29
	lbz %r11, 0(%r10)
	xor %r9, %r9, %r11
	stb %r9, 0(%r10)
	addi %r30, %r30, 1
	addi %r29, %r29, 1
	addi %r31, %r31, -1
	subf %r9, %r28, %r29
	b 24f
23:
	ld %r9, 0(%r30)
	add %r10, %r26, %r29
	ld %r11, 0(%r10)
	xor %r9, %r9, %r11
	std %r9, 0(%r10)
	addi %r30, %r30, 8
	addi %r29, %r29, 8
	addi %r31, %r31, -8
	subf %r9, %r28, %r29
24:
	cmpldi %cr0, %r9, 0
	beq %cr0, 25f
	b 26f
25:
	li %r29, 0
	addi %r3, %r26, 0
	addi %r4, %r27, 0
	bl {vg_keccak_f1600}
26:
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	b 21f
20:
21:
	addi %r3, %r29, 0
	ld %r26, 512(%r27)
	ld %r28, 528(%r27)
	ld %r29, 536(%r27)
	ld %r30, 544(%r27)
	ld %r31, 552(%r27)
	ld %r27, 520(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 672
	blr

vg_keccak_absorb_scratch:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 512(%r8)
	std %r27, 520(%r8)
	std %r28, 528(%r8)
	std %r29, 536(%r8)
	std %r30, 544(%r8)
	std %r31, 552(%r8)
	addi %r26, %r3, 0
	addi %r27, %r8, 0
	addi %r28, %r4, 0
	addi %r29, %r5, 0
	addi %r30, %r6, 0
	addi %r31, %r7, 0
	cmpldi %cr0, %r31, 0
	beq %cr0, 20f
22:
	li %r10, 7
	and %r10, %r29, %r10
	addi %r11, %r31, -8
	rldicl %r11, %r11, 1, 63
	or %r10, %r10, %r11
	cmpldi %cr0, %r10, 0
	beq %cr0, 23f
	lbz %r9, 0(%r30)
	add %r10, %r26, %r29
	lbz %r11, 0(%r10)
	xor %r9, %r9, %r11
	stb %r9, 0(%r10)
	addi %r30, %r30, 1
	addi %r29, %r29, 1
	addi %r31, %r31, -1
	subf %r9, %r28, %r29
	b 24f
23:
	ld %r9, 0(%r30)
	add %r10, %r26, %r29
	ld %r11, 0(%r10)
	xor %r9, %r9, %r11
	std %r9, 0(%r10)
	addi %r30, %r30, 8
	addi %r29, %r29, 8
	addi %r31, %r31, -8
	subf %r9, %r28, %r29
24:
	cmpldi %cr0, %r9, 0
	beq %cr0, 25f
	b 26f
25:
	li %r29, 0
	addi %r3, %r26, 0
	addi %r4, %r27, 0
	bl {vg_keccak_f1600}
26:
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	b 21f
20:
21:
	addi %r3, %r29, 0
	ld %r26, 512(%r27)
	ld %r28, 528(%r27)
	ld %r29, 536(%r27)
	ld %r30, 544(%r27)
	ld %r31, 552(%r27)
	ld %r27, 520(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr

vg_keccak_pad:
	stdu %r1, -672(%r1)
	addi %r7, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	add %r9, %r3, %r5
	lbz %r10, 0(%r9)
	xor %r10, %r10, %r6
	stb %r10, 0(%r9)
	add %r9, %r3, %r4
	addi %r9, %r9, -1
	lbz %r10, 0(%r9)
	li %r11, 128
	xor %r10, %r10, %r11
	stb %r10, 0(%r9)
	addi %r4, %r7, 0
	bl {vg_keccak_f1600}
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 672
	blr

vg_keccak_pad_scratch:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	add %r9, %r3, %r5
	lbz %r10, 0(%r9)
	xor %r10, %r10, %r6
	stb %r10, 0(%r9)
	add %r9, %r3, %r4
	addi %r9, %r9, -1
	lbz %r10, 0(%r9)
	li %r11, 128
	xor %r10, %r10, %r11
	stb %r10, 0(%r9)
	addi %r4, %r7, 0
	bl {vg_keccak_f1600}
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr

vg_keccak_squeeze:
	stdu %r1, -672(%r1)
	addi %r8, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 512(%r8)
	std %r27, 520(%r8)
	std %r28, 528(%r8)
	std %r29, 536(%r8)
	std %r30, 544(%r8)
	std %r31, 552(%r8)
	addi %r26, %r3, 0
	addi %r27, %r8, 0
	addi %r28, %r4, 0
	addi %r29, %r5, 0
	addi %r30, %r6, 0
	addi %r31, %r7, 0
	cmpldi %cr0, %r31, 0
	beq %cr0, 20f
22:
	subf %r9, %r28, %r29
	cmpldi %cr0, %r9, 0
	beq %cr0, 23f
	b 24f
23:
	li %r29, 0
	addi %r3, %r26, 0
	addi %r4, %r27, 0
	bl {vg_keccak_f1600}
24:
	li %r10, 7
	and %r10, %r29, %r10
	addi %r11, %r31, -8
	rldicl %r11, %r11, 1, 63
	or %r10, %r10, %r11
	cmpldi %cr0, %r10, 0
	beq %cr0, 25f
	add %r10, %r26, %r29
	lbz %r9, 0(%r10)
	stb %r9, 0(%r30)
	addi %r30, %r30, 1
	addi %r29, %r29, 1
	addi %r31, %r31, -1
	b 26f
25:
	add %r10, %r26, %r29
	ld %r9, 0(%r10)
	std %r9, 0(%r30)
	addi %r30, %r30, 8
	addi %r29, %r29, 8
	addi %r31, %r31, -8
26:
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	b 21f
20:
21:
	addi %r3, %r29, 0
	ld %r26, 512(%r27)
	ld %r28, 528(%r27)
	ld %r29, 536(%r27)
	ld %r30, 544(%r27)
	ld %r31, 552(%r27)
	ld %r27, 520(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 672
	blr

vg_keccak_squeeze_scratch:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r26, 512(%r8)
	std %r27, 520(%r8)
	std %r28, 528(%r8)
	std %r29, 536(%r8)
	std %r30, 544(%r8)
	std %r31, 552(%r8)
	addi %r26, %r3, 0
	addi %r27, %r8, 0
	addi %r28, %r4, 0
	addi %r29, %r5, 0
	addi %r30, %r6, 0
	addi %r31, %r7, 0
	cmpldi %cr0, %r31, 0
	beq %cr0, 20f
22:
	subf %r9, %r28, %r29
	cmpldi %cr0, %r9, 0
	beq %cr0, 23f
	b 24f
23:
	li %r29, 0
	addi %r3, %r26, 0
	addi %r4, %r27, 0
	bl {vg_keccak_f1600}
24:
	li %r10, 7
	and %r10, %r29, %r10
	addi %r11, %r31, -8
	rldicl %r11, %r11, 1, 63
	or %r10, %r10, %r11
	cmpldi %cr0, %r10, 0
	beq %cr0, 25f
	add %r10, %r26, %r29
	lbz %r9, 0(%r10)
	stb %r9, 0(%r30)
	addi %r30, %r30, 1
	addi %r29, %r29, 1
	addi %r31, %r31, -1
	b 26f
25:
	add %r10, %r26, %r29
	ld %r9, 0(%r10)
	std %r9, 0(%r30)
	addi %r30, %r30, 8
	addi %r29, %r29, 8
	addi %r31, %r31, -8
26:
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	b 21f
20:
21:
	addi %r3, %r29, 0
	ld %r26, 512(%r27)
	ld %r28, 528(%r27)
	ld %r29, 536(%r27)
	ld %r30, 544(%r27)
	ld %r31, 552(%r27)
	ld %r27, 520(%r27)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr
