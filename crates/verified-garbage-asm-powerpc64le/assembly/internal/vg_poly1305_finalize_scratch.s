// The functions of `src/internal/vg_poly1305_finalize_scratch.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_poly1305_finalize_scratch:
	std %r14, 0(%r6)
	std %r15, 8(%r6)
	std %r16, 16(%r6)
	std %r17, 24(%r6)
	std %r18, 32(%r6)
	std %r19, 40(%r6)
	std %r20, 48(%r6)
	std %r21, 56(%r6)
	addi %r21, %r6, 0
	addi %r6, %r5, 0
	li %r5, 15
	and %r5, %r4, %r5
	lis %r20, 1023
	ori %r20, %r20, 65535
	ld %r18, 24(%r3)
	ld %r19, 32(%r3)
	lis %r0, 4095
	ori %r0, %r0, 65532
	rldicr %r0, %r0, 32, 31
	oris %r0, %r0, 4095
	ori %r0, %r0, 65535
	and %r18, %r18, %r0
	lis %r0, 4095
	ori %r0, %r0, 65532
	rldicr %r0, %r0, 32, 31
	oris %r0, %r0, 4095
	ori %r0, %r0, 65532
	and %r19, %r19, %r0
	and %r12, %r18, %r20
	rldicl %r14, %r18, 38, 26
	and %r14, %r14, %r20
	rldicl %r15, %r18, 12, 52
	rldicr %r0, %r19, 12, 51
	add %r15, %r15, %r0
	and %r15, %r15, %r20
	rldicl %r16, %r19, 50, 14
	and %r16, %r16, %r20
	rldicl %r17, %r19, 24, 40
	rldicr %r7, %r14, 2, 61
	add %r7, %r7, %r14
	rldicr %r8, %r15, 2, 61
	add %r8, %r8, %r15
	rldicr %r9, %r16, 2, 61
	add %r9, %r9, %r16
	rldicr %r10, %r17, 2, 61
	add %r10, %r10, %r17
	stw %r12, 72(%r3)
	stw %r14, 76(%r3)
	stw %r15, 80(%r3)
	stw %r16, 84(%r3)
	stw %r17, 88(%r3)
	stw %r7, 92(%r3)
	stw %r8, 96(%r3)
	stw %r9, 100(%r3)
	stw %r10, 104(%r3)
	ld %r18, 0(%r3)
	ld %r19, 8(%r3)
	and %r12, %r18, %r20
	rldicl %r14, %r18, 38, 26
	and %r14, %r14, %r20
	rldicl %r15, %r18, 12, 52
	rldicr %r0, %r19, 12, 51
	add %r15, %r15, %r0
	and %r15, %r15, %r20
	rldicl %r16, %r19, 50, 14
	and %r16, %r16, %r20
	rldicl %r17, %r19, 24, 40
	ld %r0, 16(%r3)
	rldicr %r0, %r0, 24, 39
	addi %r7, %r12, 0
	addi %r8, %r14, 0
	addi %r9, %r15, 0
	addi %r10, %r16, 0
	add %r11, %r17, %r0
	cmpldi %cr0, %r5, 0
	beq %cr0, 20f
	li %r15, 0
	add %r12, %r3, %r5
	li %r14, 16
	subf %r14, %r5, %r14
22:
	stb %r15, 56(%r12)
	addi %r12, %r12, 1
	addi %r14, %r14, -1
	cmpldi %cr0, %r14, 0
	bne %cr0, 22b
	li %r15, 1
	add %r12, %r3, %r5
	stb %r15, 56(%r12)
	addi %r4, %r3, 56
	ld %r18, 0(%r4)
	ld %r19, 8(%r4)
	and %r12, %r18, %r20
	rldicl %r14, %r18, 38, 26
	and %r14, %r14, %r20
	rldicl %r15, %r18, 12, 52
	rldicr %r0, %r19, 12, 51
	add %r15, %r15, %r0
	and %r15, %r15, %r20
	rldicl %r16, %r19, 50, 14
	and %r16, %r16, %r20
	rldicl %r17, %r19, 24, 40
	add %r7, %r7, %r12
	add %r8, %r8, %r14
	add %r9, %r9, %r15
	add %r10, %r10, %r16
	add %r11, %r11, %r17
	lwz %r18, 72(%r3)
	mulld %r12, %r7, %r18
	lwz %r18, 104(%r3)
	mulld %r18, %r8, %r18
	add %r12, %r12, %r18
	lwz %r18, 100(%r3)
	mulld %r18, %r9, %r18
	add %r12, %r12, %r18
	lwz %r18, 96(%r3)
	mulld %r18, %r10, %r18
	add %r12, %r12, %r18
	lwz %r18, 92(%r3)
	mulld %r18, %r11, %r18
	add %r12, %r12, %r18
	lwz %r18, 76(%r3)
	mulld %r14, %r7, %r18
	lwz %r18, 72(%r3)
	mulld %r18, %r8, %r18
	add %r14, %r14, %r18
	lwz %r18, 104(%r3)
	mulld %r18, %r9, %r18
	add %r14, %r14, %r18
	lwz %r18, 100(%r3)
	mulld %r18, %r10, %r18
	add %r14, %r14, %r18
	lwz %r18, 96(%r3)
	mulld %r18, %r11, %r18
	add %r14, %r14, %r18
	lwz %r18, 80(%r3)
	mulld %r15, %r7, %r18
	lwz %r18, 76(%r3)
	mulld %r18, %r8, %r18
	add %r15, %r15, %r18
	lwz %r18, 72(%r3)
	mulld %r18, %r9, %r18
	add %r15, %r15, %r18
	lwz %r18, 104(%r3)
	mulld %r18, %r10, %r18
	add %r15, %r15, %r18
	lwz %r18, 100(%r3)
	mulld %r18, %r11, %r18
	add %r15, %r15, %r18
	lwz %r18, 84(%r3)
	mulld %r16, %r7, %r18
	lwz %r18, 80(%r3)
	mulld %r18, %r8, %r18
	add %r16, %r16, %r18
	lwz %r18, 76(%r3)
	mulld %r18, %r9, %r18
	add %r16, %r16, %r18
	lwz %r18, 72(%r3)
	mulld %r18, %r10, %r18
	add %r16, %r16, %r18
	lwz %r18, 104(%r3)
	mulld %r18, %r11, %r18
	add %r16, %r16, %r18
	lwz %r18, 88(%r3)
	mulld %r17, %r7, %r18
	lwz %r18, 84(%r3)
	mulld %r18, %r8, %r18
	add %r17, %r17, %r18
	lwz %r18, 80(%r3)
	mulld %r18, %r9, %r18
	add %r17, %r17, %r18
	lwz %r18, 76(%r3)
	mulld %r18, %r10, %r18
	add %r17, %r17, %r18
	lwz %r18, 72(%r3)
	mulld %r18, %r11, %r18
	add %r17, %r17, %r18
	rldicl %r18, %r12, 38, 26
	and %r7, %r12, %r20
	add %r14, %r14, %r18
	rldicl %r18, %r14, 38, 26
	and %r8, %r14, %r20
	add %r15, %r15, %r18
	rldicl %r18, %r15, 38, 26
	and %r9, %r15, %r20
	add %r16, %r16, %r18
	rldicl %r18, %r16, 38, 26
	and %r10, %r16, %r20
	add %r17, %r17, %r18
	rldicl %r18, %r17, 38, 26
	and %r11, %r17, %r20
	rldicr %r19, %r18, 2, 61
	add %r18, %r18, %r19
	add %r7, %r7, %r18
	rldicl %r18, %r7, 38, 26
	and %r7, %r7, %r20
	add %r8, %r8, %r18
	b 21f
20:
21:
	rldicl %r18, %r8, 38, 26
	and %r8, %r8, %r20
	add %r9, %r9, %r18
	rldicl %r18, %r9, 38, 26
	and %r9, %r9, %r20
	add %r10, %r10, %r18
	rldicl %r18, %r10, 38, 26
	and %r10, %r10, %r20
	add %r11, %r11, %r18
	addi %r12, %r7, 5
	rldicl %r18, %r12, 38, 26
	and %r12, %r12, %r20
	add %r14, %r8, %r18
	rldicl %r18, %r14, 38, 26
	and %r14, %r14, %r20
	add %r15, %r9, %r18
	rldicl %r18, %r15, 38, 26
	and %r15, %r15, %r20
	add %r16, %r10, %r18
	rldicl %r18, %r16, 38, 26
	and %r16, %r16, %r20
	add %r17, %r11, %r18
	rldicl %r18, %r17, 38, 26
	and %r17, %r17, %r20
	addi %r18, %r18, -1
	xor %r19, %r7, %r12
	and %r19, %r19, %r18
	xor %r7, %r12, %r19
	xor %r19, %r8, %r14
	and %r19, %r19, %r18
	xor %r8, %r14, %r19
	xor %r19, %r9, %r15
	and %r19, %r19, %r18
	xor %r9, %r15, %r19
	xor %r19, %r10, %r16
	and %r19, %r19, %r18
	xor %r10, %r16, %r19
	xor %r19, %r11, %r17
	and %r19, %r19, %r18
	xor %r11, %r17, %r19
	ld %r18, 40(%r3)
	ld %r19, 48(%r3)
	and %r12, %r18, %r20
	rldicl %r14, %r18, 38, 26
	and %r14, %r14, %r20
	rldicl %r15, %r18, 12, 52
	rldicr %r0, %r19, 12, 51
	add %r15, %r15, %r0
	and %r15, %r15, %r20
	rldicl %r16, %r19, 50, 14
	and %r16, %r16, %r20
	rldicl %r17, %r19, 24, 40
	add %r7, %r7, %r12
	add %r8, %r8, %r14
	add %r9, %r9, %r15
	add %r10, %r10, %r16
	add %r11, %r11, %r17
	rldicl %r18, %r7, 38, 26
	and %r7, %r7, %r20
	add %r8, %r8, %r18
	rldicl %r18, %r8, 38, 26
	and %r8, %r8, %r20
	add %r9, %r9, %r18
	rldicl %r18, %r9, 38, 26
	and %r9, %r9, %r20
	add %r10, %r10, %r18
	rldicl %r18, %r10, 38, 26
	and %r10, %r10, %r20
	add %r11, %r11, %r18
	rldicr %r12, %r8, 26, 37
	add %r18, %r7, %r12
	rldicr %r12, %r9, 52, 11
	add %r18, %r18, %r12
	rldicl %r19, %r9, 52, 12
	rldicr %r12, %r10, 14, 49
	add %r19, %r19, %r12
	rldicr %r12, %r11, 40, 23
	add %r19, %r19, %r12
	rldicl %r0, %r11, 40, 24
	std %r18, 0(%r6)
	std %r19, 8(%r6)
	ld %r14, 0(%r21)
	ld %r15, 8(%r21)
	ld %r16, 16(%r21)
	ld %r17, 24(%r21)
	ld %r18, 32(%r21)
	ld %r19, 40(%r21)
	ld %r20, 48(%r21)
	ld %r21, 56(%r21)
	blr
