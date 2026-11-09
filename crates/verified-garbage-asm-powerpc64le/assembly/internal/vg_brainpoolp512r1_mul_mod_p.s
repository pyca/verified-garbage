// The functions of `src/internal/vg_brainpoolp512r1_mul_mod_p.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp512r1_mul_mod_p:
	rlwinm %r4, %r4, 0, 0, 31
	rlwinm %r5, %r5, 0, 0, 31
	rlwinm %r6, %r6, 0, 0, 31
	add %r4, %r3, %r4
	add %r5, %r3, %r5
	add %r6, %r3, %r6
	lis %r11, 22586
	ori %r11, %r11, 18675
	stw %r11, 3784(%r3)
	lis %r11, 10410
	ori %r11, %r11, 24662
	stw %r11, 3788(%r3)
	lis %r11, 11650
	ori %r11, %r11, 50821
	stw %r11, 3792(%r3)
	lis %r11, 10369
	ori %r11, %r11, 65327
	stw %r11, 3796(%r3)
	lis %r11, -6493
	ori %r11, %r11, 32998
	stw %r11, 3800(%r3)
	lis %r11, -20787
	ori %r11, %r11, 41258
	stw %r11, 3804(%r3)
	lis %r11, -25658
	ori %r11, %r11, 26690
	stw %r11, 3808(%r3)
	lis %r11, 32077
	ori %r11, %r11, 39680
	stw %r11, 3812(%r3)
	lis %r11, 28723
	ori %r11, %r11, 2161
	stw %r11, 3816(%r3)
	lis %r11, -10653
	ori %r11, %r11, 40138
	stw %r11, 3820(%r3)
	lis %r11, -19511
	ori %r11, %r11, 53774
	stw %r11, 3824(%r3)
	lis %r11, -13520
	ori %r11, %r11, 36275
	stw %r11, 3828(%r3)
	lis %r11, 13257
	ori %r11, %r11, 64519
	stw %r11, 3832(%r3)
	lis %r11, 16340
	ori %r11, %r11, 59054
	stw %r11, 3836(%r3)
	lis %r11, -9239
	ori %r11, %r11, 50315
	stw %r11, 3840(%r3)
	lis %r11, -21795
	ori %r11, %r11, 40376
	stw %r11, 3844(%r3)
	lis %r11, 32137
	ori %r11, %r11, 61381
	stw %r11, 3656(%r3)
	lis %r11, -31845
	ori %r11, %r11, 12832
	stw %r11, 3660(%r3)
	std %r15, 3584(%r3)
	std %r16, 3592(%r3)
	std %r17, 3600(%r3)
	std %r18, 3608(%r3)
	std %r19, 3616(%r3)
	std %r20, 3624(%r3)
	std %r21, 3632(%r3)
	std %r22, 3640(%r3)
	std %r23, 3648(%r3)
	li %r15, 0
	li %r16, 0
	li %r17, 0
	li %r18, 0
	li %r19, 0
	li %r20, 0
	li %r21, 0
	li %r22, 0
	li %r23, 0
	addi %r7, %r3, 3784
	li %r8, 8
20:
	ld %r9, 0(%r5)
	ld %r11, 0(%r6)
	mulld %r11, %r9, %r11
	addc %r15, %r15, %r11
	ld %r11, 8(%r6)
	mulld %r11, %r9, %r11
	adde %r16, %r16, %r11
	ld %r11, 16(%r6)
	mulld %r11, %r9, %r11
	adde %r17, %r17, %r11
	ld %r11, 24(%r6)
	mulld %r11, %r9, %r11
	adde %r18, %r18, %r11
	ld %r11, 32(%r6)
	mulld %r11, %r9, %r11
	adde %r19, %r19, %r11
	ld %r11, 40(%r6)
	mulld %r11, %r9, %r11
	adde %r20, %r20, %r11
	ld %r11, 48(%r6)
	mulld %r11, %r9, %r11
	adde %r21, %r21, %r11
	ld %r11, 56(%r6)
	mulld %r11, %r9, %r11
	adde %r22, %r22, %r11
	addze %r23, %r23
	li %r12, 0
	addze %r12, %r12
	ld %r11, 0(%r6)
	mulhdu %r11, %r9, %r11
	addc %r16, %r16, %r11
	ld %r11, 8(%r6)
	mulhdu %r11, %r9, %r11
	adde %r17, %r17, %r11
	ld %r11, 16(%r6)
	mulhdu %r11, %r9, %r11
	adde %r18, %r18, %r11
	ld %r11, 24(%r6)
	mulhdu %r11, %r9, %r11
	adde %r19, %r19, %r11
	ld %r11, 32(%r6)
	mulhdu %r11, %r9, %r11
	adde %r20, %r20, %r11
	ld %r11, 40(%r6)
	mulhdu %r11, %r9, %r11
	adde %r21, %r21, %r11
	ld %r11, 48(%r6)
	mulhdu %r11, %r9, %r11
	adde %r22, %r22, %r11
	ld %r11, 56(%r6)
	mulhdu %r11, %r9, %r11
	adde %r23, %r23, %r11
	addze %r12, %r12
	ld %r10, 3656(%r3)
	mulld %r9, %r15, %r10
	ld %r10, 0(%r7)
	mulhdu %r0, %r9, %r10
	mulld %r10, %r9, %r10
	addc %r10, %r10, %r15
	addze %r0, %r0
	ld %r11, 8(%r7)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	addc %r15, %r11, %r16
	addze %r0, %r10
	ld %r11, 16(%r7)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	addc %r16, %r11, %r17
	addze %r0, %r10
	ld %r11, 24(%r7)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	addc %r17, %r11, %r18
	addze %r0, %r10
	ld %r11, 32(%r7)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	addc %r18, %r11, %r19
	addze %r0, %r10
	ld %r11, 40(%r7)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	addc %r19, %r11, %r20
	addze %r0, %r10
	ld %r11, 48(%r7)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	addc %r20, %r11, %r21
	addze %r0, %r10
	ld %r11, 56(%r7)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	addc %r21, %r11, %r22
	addze %r0, %r10
	addc %r22, %r23, %r0
	addze %r23, %r12
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 20b
	ld %r12, 0(%r7)
	subfc %r11, %r12, %r15
	std %r11, 3720(%r3)
	ld %r12, 8(%r7)
	subfe %r11, %r12, %r16
	std %r11, 3728(%r3)
	ld %r12, 16(%r7)
	subfe %r11, %r12, %r17
	std %r11, 3736(%r3)
	ld %r12, 24(%r7)
	subfe %r11, %r12, %r18
	std %r11, 3744(%r3)
	ld %r12, 32(%r7)
	subfe %r11, %r12, %r19
	std %r11, 3752(%r3)
	ld %r12, 40(%r7)
	subfe %r11, %r12, %r20
	std %r11, 3760(%r3)
	ld %r12, 48(%r7)
	subfe %r11, %r12, %r21
	std %r11, 3768(%r3)
	ld %r12, 56(%r7)
	subfe %r11, %r12, %r22
	std %r11, 3776(%r3)
	addze %r10, %r23
	li %r11, 0
	subf %r10, %r10, %r11
	ld %r12, 3720(%r3)
	xor %r12, %r12, %r15
	and %r12, %r12, %r10
	xor %r11, %r15, %r12
	std %r11, 0(%r4)
	ld %r12, 3728(%r3)
	xor %r12, %r12, %r16
	and %r12, %r12, %r10
	xor %r11, %r16, %r12
	std %r11, 8(%r4)
	ld %r12, 3736(%r3)
	xor %r12, %r12, %r17
	and %r12, %r12, %r10
	xor %r11, %r17, %r12
	std %r11, 16(%r4)
	ld %r12, 3744(%r3)
	xor %r12, %r12, %r18
	and %r12, %r12, %r10
	xor %r11, %r18, %r12
	std %r11, 24(%r4)
	ld %r12, 3752(%r3)
	xor %r12, %r12, %r19
	and %r12, %r12, %r10
	xor %r11, %r19, %r12
	std %r11, 32(%r4)
	ld %r12, 3760(%r3)
	xor %r12, %r12, %r20
	and %r12, %r12, %r10
	xor %r11, %r20, %r12
	std %r11, 40(%r4)
	ld %r12, 3768(%r3)
	xor %r12, %r12, %r21
	and %r12, %r12, %r10
	xor %r11, %r21, %r12
	std %r11, 48(%r4)
	ld %r12, 3776(%r3)
	xor %r12, %r12, %r22
	and %r12, %r12, %r10
	xor %r11, %r22, %r12
	std %r11, 56(%r4)
	ld %r15, 3584(%r3)
	ld %r16, 3592(%r3)
	ld %r17, 3600(%r3)
	ld %r18, 3608(%r3)
	ld %r19, 3616(%r3)
	ld %r20, 3624(%r3)
	ld %r21, 3632(%r3)
	ld %r22, 3640(%r3)
	ld %r23, 3648(%r3)
	blr
