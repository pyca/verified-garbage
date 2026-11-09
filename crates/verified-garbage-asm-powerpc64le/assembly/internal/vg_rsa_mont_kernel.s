// The functions of `src/internal/vg_rsa_mont_kernel.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_mont_kernel:
	addi %r12, %r3, 0
	addi %r11, %r4, 0
	rldicr %r3, %r4, 2, 61
	add %r3, %r9, %r3
	std %r14, 8(%r3)
	ld %r3, 0(%r10)
	mulld %r22, %r3, %r12
	addi %r22, %r22, 2
	mulld %r22, %r22, %r12
	rldicr %r14, %r11, 2, 61
	add %r14, %r14, %r8
	std %r22, 8(%r14)
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r3, 0
20:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 20b
21:
	ld %r17, 0(%r6)
	addi %r6, %r6, 8
	ld %r19, 0(%r7)
	ld %r20, 0(%r8)
	mulld %r18, %r17, %r19
	mulhdu %r19, %r17, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r3, 0(%r10)
	mulld %r0, %r20, %r22
	mulld %r22, %r0, %r3
	mulhdu %r19, %r0, %r3
	addc %r22, %r22, %r20
	addze %r22, %r19
	addi %r14, %r8, 0
	addi %r15, %r7, 0
	addi %r3, %r10, 0
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicr %r16, %r16, 62, 1
	rldicl %r16, %r16, 2, 62
	cmpldi %cr0, %r16, 0
	beq %cr0, 22f
24:
	ld %r19, 8(%r14)
	ld %r20, 8(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 8(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r3, %r3, 8
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 24b
	b 23f
22:
23:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 25f
27:
	ld %r19, 8(%r14)
	ld %r20, 8(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 8(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 0(%r14)
	ld %r19, 16(%r14)
	ld %r20, 16(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 16(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 8(%r14)
	ld %r19, 24(%r14)
	ld %r20, 24(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 24(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 16(%r14)
	ld %r19, 32(%r14)
	ld %r20, 32(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 32(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r3, %r3, 32
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 27b
	b 26f
25:
26:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	li %r19, 0
	addze %r19, %r19
	addc %r18, %r18, %r22
	addze %r19, %r19
	std %r18, 0(%r14)
	std %r19, 8(%r14)
	ld %r22, 16(%r14)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 21b
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
28:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 28b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
29:
	ld %r0, 0(%r15)
	ld %r3, 0(%r14)
	xor %r3, %r3, %r0
	and %r3, %r3, %r20
	xor %r3, %r3, %r0
	std %r3, 0(%r16)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 29b
	rldicr %r3, %r11, 2, 61
	add %r3, %r9, %r3
	ld %r14, 8(%r3)
	blr
