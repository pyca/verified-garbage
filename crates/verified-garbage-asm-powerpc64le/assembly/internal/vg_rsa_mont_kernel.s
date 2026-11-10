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
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
21:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 22f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 24f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 26f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 27f
26:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
27:
	b 25f
24:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
25:
	b 23f
22:
23:
	cmplwi %cr0, %r17, 0
	beq %cr0, 28f
210:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 210b
	b 29f
28:
29:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 21b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
211:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 211b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
212:
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
	bne %cr0, 212b
	rldicr %r3, %r11, 2, 61
	add %r3, %r9, %r3
	ld %r14, 8(%r3)
	blr
