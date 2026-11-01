// The functions of `src/brainpoolp512r1_mont.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
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
	li %r11, 0
	std %r11, 3584(%r3)
	std %r11, 3592(%r3)
	std %r11, 3600(%r3)
	std %r11, 3608(%r3)
	std %r11, 3616(%r3)
	std %r11, 3624(%r3)
	std %r11, 3632(%r3)
	std %r11, 3640(%r3)
	std %r11, 3648(%r3)
	addi %r7, %r3, 3784
	li %r8, 8
20:
	ld %r9, 0(%r5)
	li %r0, 0
	ld %r11, 0(%r6)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3584(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3584(%r3)
	ld %r11, 8(%r6)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3592(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3592(%r3)
	ld %r11, 16(%r6)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3600(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3600(%r3)
	ld %r11, 24(%r6)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3608(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3608(%r3)
	ld %r11, 32(%r6)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3616(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3616(%r3)
	ld %r11, 40(%r6)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3624(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3624(%r3)
	ld %r11, 48(%r6)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3632(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3632(%r3)
	ld %r11, 56(%r6)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3640(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3640(%r3)
	ld %r10, 3648(%r3)
	addc %r10, %r10, %r0
	std %r10, 3648(%r3)
	li %r12, 0
	addze %r12, %r12
	ld %r11, 3584(%r3)
	ld %r10, 3656(%r3)
	mulld %r9, %r11, %r10
	ld %r10, 0(%r7)
	mulhdu %r0, %r9, %r10
	mulld %r10, %r9, %r10
	addc %r10, %r10, %r11
	addze %r0, %r0
	ld %r11, 8(%r7)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3592(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3584(%r3)
	ld %r11, 16(%r7)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3600(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3592(%r3)
	ld %r11, 24(%r7)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3608(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3600(%r3)
	ld %r11, 32(%r7)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3616(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3608(%r3)
	ld %r11, 40(%r7)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3624(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3616(%r3)
	ld %r11, 48(%r7)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3632(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3624(%r3)
	ld %r11, 56(%r7)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3640(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3632(%r3)
	ld %r10, 3648(%r3)
	addc %r10, %r10, %r0
	std %r10, 3640(%r3)
	addze %r12, %r12
	std %r12, 3648(%r3)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 20b
	ld %r11, 3584(%r3)
	ld %r12, 0(%r7)
	subfc %r11, %r12, %r11
	std %r11, 3720(%r3)
	ld %r11, 3592(%r3)
	ld %r12, 8(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3728(%r3)
	ld %r11, 3600(%r3)
	ld %r12, 16(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3736(%r3)
	ld %r11, 3608(%r3)
	ld %r12, 24(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3744(%r3)
	ld %r11, 3616(%r3)
	ld %r12, 32(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3752(%r3)
	ld %r11, 3624(%r3)
	ld %r12, 40(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3760(%r3)
	ld %r11, 3632(%r3)
	ld %r12, 48(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3768(%r3)
	ld %r11, 3640(%r3)
	ld %r12, 56(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3776(%r3)
	ld %r11, 3648(%r3)
	addze %r10, %r11
	li %r11, 0
	subf %r10, %r10, %r11
	ld %r11, 3584(%r3)
	ld %r12, 3720(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 0(%r4)
	ld %r11, 3592(%r3)
	ld %r12, 3728(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 8(%r4)
	ld %r11, 3600(%r3)
	ld %r12, 3736(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 16(%r4)
	ld %r11, 3608(%r3)
	ld %r12, 3744(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 24(%r4)
	ld %r11, 3616(%r3)
	ld %r12, 3752(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 32(%r4)
	ld %r11, 3624(%r3)
	ld %r12, 3760(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 40(%r4)
	ld %r11, 3632(%r3)
	ld %r12, 3768(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 48(%r4)
	ld %r11, 3640(%r3)
	ld %r12, 3776(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 56(%r4)
	blr

vg_brainpoolp512r1_add_mod_p:
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
	addi %r7, %r3, 3784
	ld %r11, 0(%r5)
	ld %r12, 0(%r6)
	addc %r11, %r11, %r12
	std %r11, 3584(%r3)
	ld %r11, 8(%r5)
	ld %r12, 8(%r6)
	adde %r11, %r11, %r12
	std %r11, 3592(%r3)
	ld %r11, 16(%r5)
	ld %r12, 16(%r6)
	adde %r11, %r11, %r12
	std %r11, 3600(%r3)
	ld %r11, 24(%r5)
	ld %r12, 24(%r6)
	adde %r11, %r11, %r12
	std %r11, 3608(%r3)
	ld %r11, 32(%r5)
	ld %r12, 32(%r6)
	adde %r11, %r11, %r12
	std %r11, 3616(%r3)
	ld %r11, 40(%r5)
	ld %r12, 40(%r6)
	adde %r11, %r11, %r12
	std %r11, 3624(%r3)
	ld %r11, 48(%r5)
	ld %r12, 48(%r6)
	adde %r11, %r11, %r12
	std %r11, 3632(%r3)
	ld %r11, 56(%r5)
	ld %r12, 56(%r6)
	adde %r11, %r11, %r12
	std %r11, 3640(%r3)
	li %r10, 0
	addze %r10, %r10
	std %r10, 3648(%r3)
	ld %r11, 3584(%r3)
	ld %r12, 0(%r7)
	subfc %r11, %r12, %r11
	std %r11, 3720(%r3)
	ld %r11, 3592(%r3)
	ld %r12, 8(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3728(%r3)
	ld %r11, 3600(%r3)
	ld %r12, 16(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3736(%r3)
	ld %r11, 3608(%r3)
	ld %r12, 24(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3744(%r3)
	ld %r11, 3616(%r3)
	ld %r12, 32(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3752(%r3)
	ld %r11, 3624(%r3)
	ld %r12, 40(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3760(%r3)
	ld %r11, 3632(%r3)
	ld %r12, 48(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3768(%r3)
	ld %r11, 3640(%r3)
	ld %r12, 56(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3776(%r3)
	ld %r11, 3648(%r3)
	addze %r10, %r11
	li %r11, 0
	subf %r10, %r10, %r11
	ld %r11, 3584(%r3)
	ld %r12, 3720(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 0(%r4)
	ld %r11, 3592(%r3)
	ld %r12, 3728(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 8(%r4)
	ld %r11, 3600(%r3)
	ld %r12, 3736(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 16(%r4)
	ld %r11, 3608(%r3)
	ld %r12, 3744(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 24(%r4)
	ld %r11, 3616(%r3)
	ld %r12, 3752(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 32(%r4)
	ld %r11, 3624(%r3)
	ld %r12, 3760(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 40(%r4)
	ld %r11, 3632(%r3)
	ld %r12, 3768(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 48(%r4)
	ld %r11, 3640(%r3)
	ld %r12, 3776(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 56(%r4)
	blr

vg_brainpoolp512r1_sub_mod_p:
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
	addi %r7, %r3, 3784
	ld %r11, 0(%r5)
	ld %r12, 0(%r6)
	subfc %r11, %r12, %r11
	std %r11, 3584(%r3)
	ld %r11, 8(%r5)
	ld %r12, 8(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3592(%r3)
	ld %r11, 16(%r5)
	ld %r12, 16(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3600(%r3)
	ld %r11, 24(%r5)
	ld %r12, 24(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3608(%r3)
	ld %r11, 32(%r5)
	ld %r12, 32(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3616(%r3)
	ld %r11, 40(%r5)
	ld %r12, 40(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3624(%r3)
	ld %r11, 48(%r5)
	ld %r12, 48(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3632(%r3)
	ld %r11, 56(%r5)
	ld %r12, 56(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3640(%r3)
	subfe %r10, %r10, %r10
	ld %r11, 3584(%r3)
	ld %r12, 0(%r7)
	addc %r11, %r11, %r12
	std %r11, 3720(%r3)
	ld %r11, 3592(%r3)
	ld %r12, 8(%r7)
	adde %r11, %r11, %r12
	std %r11, 3728(%r3)
	ld %r11, 3600(%r3)
	ld %r12, 16(%r7)
	adde %r11, %r11, %r12
	std %r11, 3736(%r3)
	ld %r11, 3608(%r3)
	ld %r12, 24(%r7)
	adde %r11, %r11, %r12
	std %r11, 3744(%r3)
	ld %r11, 3616(%r3)
	ld %r12, 32(%r7)
	adde %r11, %r11, %r12
	std %r11, 3752(%r3)
	ld %r11, 3624(%r3)
	ld %r12, 40(%r7)
	adde %r11, %r11, %r12
	std %r11, 3760(%r3)
	ld %r11, 3632(%r3)
	ld %r12, 48(%r7)
	adde %r11, %r11, %r12
	std %r11, 3768(%r3)
	ld %r11, 3640(%r3)
	ld %r12, 56(%r7)
	adde %r11, %r11, %r12
	std %r11, 3776(%r3)
	ld %r11, 3584(%r3)
	ld %r12, 3720(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 0(%r4)
	ld %r11, 3592(%r3)
	ld %r12, 3728(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 8(%r4)
	ld %r11, 3600(%r3)
	ld %r12, 3736(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 16(%r4)
	ld %r11, 3608(%r3)
	ld %r12, 3744(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 24(%r4)
	ld %r11, 3616(%r3)
	ld %r12, 3752(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 32(%r4)
	ld %r11, 3624(%r3)
	ld %r12, 3760(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 40(%r4)
	ld %r11, 3632(%r3)
	ld %r12, 3768(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 48(%r4)
	ld %r11, 3640(%r3)
	ld %r12, 3776(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 56(%r4)
	blr

vg_brainpoolp512r1_mul_mod_n:
	rlwinm %r4, %r4, 0, 0, 31
	rlwinm %r5, %r5, 0, 0, 31
	rlwinm %r6, %r6, 0, 0, 31
	add %r4, %r3, %r4
	add %r5, %r3, %r5
	add %r6, %r3, %r6
	lis %r11, -25431
	ori %r11, %r11, 105
	stw %r11, 3784(%r3)
	lis %r11, -19065
	ori %r11, %r11, 38530
	stw %r11, 3788(%r3)
	lis %r11, 2141
	ori %r11, %r11, 56029
	stw %r11, 3792(%r3)
	lis %r11, 7601
	ori %r11, %r11, 54145
	stw %r11, 3796(%r3)
	lis %r11, 32684
	ori %r11, %r11, 4167
	stw %r11, 3800(%r3)
	lis %r11, 16774
	ori %r11, %r11, 24857
	stw %r11, 3804(%r3)
	lis %r11, 19625
	ori %r11, %r11, 9753
	stw %r11, 3808(%r3)
	lis %r11, 21822
	ori %r11, %r11, 23617
	stw %r11, 3812(%r3)
	lis %r11, 28723
	ori %r11, %r11, 2160
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
	lis %r11, 3867
	ori %r11, %r11, 28711
	stw %r11, 3656(%r3)
	lis %r11, -21175
	ori %r11, %r11, 21535
	stw %r11, 3660(%r3)
	li %r11, 0
	std %r11, 3584(%r3)
	std %r11, 3592(%r3)
	std %r11, 3600(%r3)
	std %r11, 3608(%r3)
	std %r11, 3616(%r3)
	std %r11, 3624(%r3)
	std %r11, 3632(%r3)
	std %r11, 3640(%r3)
	std %r11, 3648(%r3)
	addi %r7, %r3, 3784
	li %r8, 8
20:
	ld %r9, 0(%r5)
	li %r0, 0
	ld %r11, 0(%r6)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3584(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3584(%r3)
	ld %r11, 8(%r6)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3592(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3592(%r3)
	ld %r11, 16(%r6)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3600(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3600(%r3)
	ld %r11, 24(%r6)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3608(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3608(%r3)
	ld %r11, 32(%r6)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3616(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3616(%r3)
	ld %r11, 40(%r6)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3624(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3624(%r3)
	ld %r11, 48(%r6)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3632(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3632(%r3)
	ld %r11, 56(%r6)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3640(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3640(%r3)
	ld %r10, 3648(%r3)
	addc %r10, %r10, %r0
	std %r10, 3648(%r3)
	li %r12, 0
	addze %r12, %r12
	ld %r11, 3584(%r3)
	ld %r10, 3656(%r3)
	mulld %r9, %r11, %r10
	ld %r10, 0(%r7)
	mulhdu %r0, %r9, %r10
	mulld %r10, %r9, %r10
	addc %r10, %r10, %r11
	addze %r0, %r0
	ld %r11, 8(%r7)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3592(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3584(%r3)
	ld %r11, 16(%r7)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3600(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3592(%r3)
	ld %r11, 24(%r7)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3608(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3600(%r3)
	ld %r11, 32(%r7)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3616(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3608(%r3)
	ld %r11, 40(%r7)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3624(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3616(%r3)
	ld %r11, 48(%r7)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3632(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3624(%r3)
	ld %r11, 56(%r7)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3640(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3632(%r3)
	ld %r10, 3648(%r3)
	addc %r10, %r10, %r0
	std %r10, 3640(%r3)
	addze %r12, %r12
	std %r12, 3648(%r3)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 20b
	ld %r11, 3584(%r3)
	ld %r12, 0(%r7)
	subfc %r11, %r12, %r11
	std %r11, 3720(%r3)
	ld %r11, 3592(%r3)
	ld %r12, 8(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3728(%r3)
	ld %r11, 3600(%r3)
	ld %r12, 16(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3736(%r3)
	ld %r11, 3608(%r3)
	ld %r12, 24(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3744(%r3)
	ld %r11, 3616(%r3)
	ld %r12, 32(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3752(%r3)
	ld %r11, 3624(%r3)
	ld %r12, 40(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3760(%r3)
	ld %r11, 3632(%r3)
	ld %r12, 48(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3768(%r3)
	ld %r11, 3640(%r3)
	ld %r12, 56(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3776(%r3)
	ld %r11, 3648(%r3)
	addze %r10, %r11
	li %r11, 0
	subf %r10, %r10, %r11
	ld %r11, 3584(%r3)
	ld %r12, 3720(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 0(%r4)
	ld %r11, 3592(%r3)
	ld %r12, 3728(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 8(%r4)
	ld %r11, 3600(%r3)
	ld %r12, 3736(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 16(%r4)
	ld %r11, 3608(%r3)
	ld %r12, 3744(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 24(%r4)
	ld %r11, 3616(%r3)
	ld %r12, 3752(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 32(%r4)
	ld %r11, 3624(%r3)
	ld %r12, 3760(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 40(%r4)
	ld %r11, 3632(%r3)
	ld %r12, 3768(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 48(%r4)
	ld %r11, 3640(%r3)
	ld %r12, 3776(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 56(%r4)
	blr

vg_brainpoolp512r1_add_mod_n:
	rlwinm %r4, %r4, 0, 0, 31
	rlwinm %r5, %r5, 0, 0, 31
	rlwinm %r6, %r6, 0, 0, 31
	add %r4, %r3, %r4
	add %r5, %r3, %r5
	add %r6, %r3, %r6
	lis %r11, -25431
	ori %r11, %r11, 105
	stw %r11, 3784(%r3)
	lis %r11, -19065
	ori %r11, %r11, 38530
	stw %r11, 3788(%r3)
	lis %r11, 2141
	ori %r11, %r11, 56029
	stw %r11, 3792(%r3)
	lis %r11, 7601
	ori %r11, %r11, 54145
	stw %r11, 3796(%r3)
	lis %r11, 32684
	ori %r11, %r11, 4167
	stw %r11, 3800(%r3)
	lis %r11, 16774
	ori %r11, %r11, 24857
	stw %r11, 3804(%r3)
	lis %r11, 19625
	ori %r11, %r11, 9753
	stw %r11, 3808(%r3)
	lis %r11, 21822
	ori %r11, %r11, 23617
	stw %r11, 3812(%r3)
	lis %r11, 28723
	ori %r11, %r11, 2160
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
	addi %r7, %r3, 3784
	ld %r11, 0(%r5)
	ld %r12, 0(%r6)
	addc %r11, %r11, %r12
	std %r11, 3584(%r3)
	ld %r11, 8(%r5)
	ld %r12, 8(%r6)
	adde %r11, %r11, %r12
	std %r11, 3592(%r3)
	ld %r11, 16(%r5)
	ld %r12, 16(%r6)
	adde %r11, %r11, %r12
	std %r11, 3600(%r3)
	ld %r11, 24(%r5)
	ld %r12, 24(%r6)
	adde %r11, %r11, %r12
	std %r11, 3608(%r3)
	ld %r11, 32(%r5)
	ld %r12, 32(%r6)
	adde %r11, %r11, %r12
	std %r11, 3616(%r3)
	ld %r11, 40(%r5)
	ld %r12, 40(%r6)
	adde %r11, %r11, %r12
	std %r11, 3624(%r3)
	ld %r11, 48(%r5)
	ld %r12, 48(%r6)
	adde %r11, %r11, %r12
	std %r11, 3632(%r3)
	ld %r11, 56(%r5)
	ld %r12, 56(%r6)
	adde %r11, %r11, %r12
	std %r11, 3640(%r3)
	li %r10, 0
	addze %r10, %r10
	std %r10, 3648(%r3)
	ld %r11, 3584(%r3)
	ld %r12, 0(%r7)
	subfc %r11, %r12, %r11
	std %r11, 3720(%r3)
	ld %r11, 3592(%r3)
	ld %r12, 8(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3728(%r3)
	ld %r11, 3600(%r3)
	ld %r12, 16(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3736(%r3)
	ld %r11, 3608(%r3)
	ld %r12, 24(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3744(%r3)
	ld %r11, 3616(%r3)
	ld %r12, 32(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3752(%r3)
	ld %r11, 3624(%r3)
	ld %r12, 40(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3760(%r3)
	ld %r11, 3632(%r3)
	ld %r12, 48(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3768(%r3)
	ld %r11, 3640(%r3)
	ld %r12, 56(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3776(%r3)
	ld %r11, 3648(%r3)
	addze %r10, %r11
	li %r11, 0
	subf %r10, %r10, %r11
	ld %r11, 3584(%r3)
	ld %r12, 3720(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 0(%r4)
	ld %r11, 3592(%r3)
	ld %r12, 3728(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 8(%r4)
	ld %r11, 3600(%r3)
	ld %r12, 3736(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 16(%r4)
	ld %r11, 3608(%r3)
	ld %r12, 3744(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 24(%r4)
	ld %r11, 3616(%r3)
	ld %r12, 3752(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 32(%r4)
	ld %r11, 3624(%r3)
	ld %r12, 3760(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 40(%r4)
	ld %r11, 3632(%r3)
	ld %r12, 3768(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 48(%r4)
	ld %r11, 3640(%r3)
	ld %r12, 3776(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 56(%r4)
	blr

vg_brainpoolp512r1_sub_mod_n:
	rlwinm %r4, %r4, 0, 0, 31
	rlwinm %r5, %r5, 0, 0, 31
	rlwinm %r6, %r6, 0, 0, 31
	add %r4, %r3, %r4
	add %r5, %r3, %r5
	add %r6, %r3, %r6
	lis %r11, -25431
	ori %r11, %r11, 105
	stw %r11, 3784(%r3)
	lis %r11, -19065
	ori %r11, %r11, 38530
	stw %r11, 3788(%r3)
	lis %r11, 2141
	ori %r11, %r11, 56029
	stw %r11, 3792(%r3)
	lis %r11, 7601
	ori %r11, %r11, 54145
	stw %r11, 3796(%r3)
	lis %r11, 32684
	ori %r11, %r11, 4167
	stw %r11, 3800(%r3)
	lis %r11, 16774
	ori %r11, %r11, 24857
	stw %r11, 3804(%r3)
	lis %r11, 19625
	ori %r11, %r11, 9753
	stw %r11, 3808(%r3)
	lis %r11, 21822
	ori %r11, %r11, 23617
	stw %r11, 3812(%r3)
	lis %r11, 28723
	ori %r11, %r11, 2160
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
	addi %r7, %r3, 3784
	ld %r11, 0(%r5)
	ld %r12, 0(%r6)
	subfc %r11, %r12, %r11
	std %r11, 3584(%r3)
	ld %r11, 8(%r5)
	ld %r12, 8(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3592(%r3)
	ld %r11, 16(%r5)
	ld %r12, 16(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3600(%r3)
	ld %r11, 24(%r5)
	ld %r12, 24(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3608(%r3)
	ld %r11, 32(%r5)
	ld %r12, 32(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3616(%r3)
	ld %r11, 40(%r5)
	ld %r12, 40(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3624(%r3)
	ld %r11, 48(%r5)
	ld %r12, 48(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3632(%r3)
	ld %r11, 56(%r5)
	ld %r12, 56(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3640(%r3)
	subfe %r10, %r10, %r10
	ld %r11, 3584(%r3)
	ld %r12, 0(%r7)
	addc %r11, %r11, %r12
	std %r11, 3720(%r3)
	ld %r11, 3592(%r3)
	ld %r12, 8(%r7)
	adde %r11, %r11, %r12
	std %r11, 3728(%r3)
	ld %r11, 3600(%r3)
	ld %r12, 16(%r7)
	adde %r11, %r11, %r12
	std %r11, 3736(%r3)
	ld %r11, 3608(%r3)
	ld %r12, 24(%r7)
	adde %r11, %r11, %r12
	std %r11, 3744(%r3)
	ld %r11, 3616(%r3)
	ld %r12, 32(%r7)
	adde %r11, %r11, %r12
	std %r11, 3752(%r3)
	ld %r11, 3624(%r3)
	ld %r12, 40(%r7)
	adde %r11, %r11, %r12
	std %r11, 3760(%r3)
	ld %r11, 3632(%r3)
	ld %r12, 48(%r7)
	adde %r11, %r11, %r12
	std %r11, 3768(%r3)
	ld %r11, 3640(%r3)
	ld %r12, 56(%r7)
	adde %r11, %r11, %r12
	std %r11, 3776(%r3)
	ld %r11, 3584(%r3)
	ld %r12, 3720(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 0(%r4)
	ld %r11, 3592(%r3)
	ld %r12, 3728(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 8(%r4)
	ld %r11, 3600(%r3)
	ld %r12, 3736(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 16(%r4)
	ld %r11, 3608(%r3)
	ld %r12, 3744(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 24(%r4)
	ld %r11, 3616(%r3)
	ld %r12, 3752(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 32(%r4)
	ld %r11, 3624(%r3)
	ld %r12, 3760(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 40(%r4)
	ld %r11, 3632(%r3)
	ld %r12, 3768(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 48(%r4)
	ld %r11, 3640(%r3)
	ld %r12, 3776(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 56(%r4)
	blr
