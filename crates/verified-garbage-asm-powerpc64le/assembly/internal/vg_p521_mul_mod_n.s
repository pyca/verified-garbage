// The functions of `src/internal/vg_p521_mul_mod_n.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_mul_mod_n:
	rlwinm %r4, %r4, 0, 0, 31
	rlwinm %r5, %r5, 0, 0, 31
	rlwinm %r6, %r6, 0, 0, 31
	add %r4, %r3, %r4
	add %r5, %r3, %r5
	add %r6, %r3, %r6
	lis %r11, -28360
	ori %r11, %r11, 25609
	stw %r11, 3744(%r3)
	lis %r11, -17553
	ori %r11, %r11, 46878
	stw %r11, 3748(%r3)
	lis %r11, -30308
	ori %r11, %r11, 18350
	stw %r11, 3752(%r3)
	lis %r11, 15285
	ori %r11, %r11, 51640
	stw %r11, 3756(%r3)
	lis %r11, -2295
	ori %r11, %r11, 42448
	stw %r11, 3760(%r3)
	lis %r11, 32716
	ori %r11, %r11, 328
	stw %r11, 3764(%r3)
	lis %r11, -16593
	ori %r11, %r11, 38507
	stw %r11, 3768(%r3)
	lis %r11, 20870
	ori %r11, %r11, 34691
	stw %r11, 3772(%r3)
	lis %r11, -1
	ori %r11, %r11, 65530
	stw %r11, 3776(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3780(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3784(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3788(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3792(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3796(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3800(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3804(%r3)
	lis %r11, 0
	ori %r11, %r11, 511
	stw %r11, 3808(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3812(%r3)
	lis %r11, 31145
	ori %r11, %r11, 38343
	stw %r11, 3600(%r3)
	lis %r11, 7471
	ori %r11, %r11, 23757
	stw %r11, 3604(%r3)
	std %r15, 3520(%r3)
	std %r16, 3528(%r3)
	std %r17, 3536(%r3)
	std %r18, 3544(%r3)
	std %r19, 3552(%r3)
	std %r20, 3560(%r3)
	std %r21, 3568(%r3)
	std %r22, 3576(%r3)
	std %r23, 3584(%r3)
	std %r24, 3592(%r3)
	li %r15, 0
	li %r16, 0
	li %r17, 0
	li %r18, 0
	li %r19, 0
	li %r20, 0
	li %r21, 0
	li %r22, 0
	li %r23, 0
	li %r24, 0
	addi %r7, %r3, 3744
	li %r8, 9
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
	ld %r11, 64(%r6)
	mulld %r11, %r9, %r11
	adde %r23, %r23, %r11
	addze %r24, %r24
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
	ld %r11, 64(%r6)
	mulhdu %r11, %r9, %r11
	adde %r24, %r24, %r11
	addze %r12, %r12
	ld %r10, 3600(%r3)
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
	ld %r11, 64(%r7)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	addc %r22, %r11, %r23
	addze %r0, %r10
	addc %r23, %r24, %r0
	addze %r24, %r12
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 20b
	ld %r12, 0(%r7)
	subfc %r11, %r12, %r15
	std %r11, 3672(%r3)
	ld %r12, 8(%r7)
	subfe %r11, %r12, %r16
	std %r11, 3680(%r3)
	ld %r12, 16(%r7)
	subfe %r11, %r12, %r17
	std %r11, 3688(%r3)
	ld %r12, 24(%r7)
	subfe %r11, %r12, %r18
	std %r11, 3696(%r3)
	ld %r12, 32(%r7)
	subfe %r11, %r12, %r19
	std %r11, 3704(%r3)
	ld %r12, 40(%r7)
	subfe %r11, %r12, %r20
	std %r11, 3712(%r3)
	ld %r12, 48(%r7)
	subfe %r11, %r12, %r21
	std %r11, 3720(%r3)
	ld %r12, 56(%r7)
	subfe %r11, %r12, %r22
	std %r11, 3728(%r3)
	ld %r12, 64(%r7)
	subfe %r11, %r12, %r23
	std %r11, 3736(%r3)
	addze %r10, %r24
	li %r11, 0
	subf %r10, %r10, %r11
	ld %r12, 3672(%r3)
	xor %r12, %r12, %r15
	and %r12, %r12, %r10
	xor %r11, %r15, %r12
	std %r11, 0(%r4)
	ld %r12, 3680(%r3)
	xor %r12, %r12, %r16
	and %r12, %r12, %r10
	xor %r11, %r16, %r12
	std %r11, 8(%r4)
	ld %r12, 3688(%r3)
	xor %r12, %r12, %r17
	and %r12, %r12, %r10
	xor %r11, %r17, %r12
	std %r11, 16(%r4)
	ld %r12, 3696(%r3)
	xor %r12, %r12, %r18
	and %r12, %r12, %r10
	xor %r11, %r18, %r12
	std %r11, 24(%r4)
	ld %r12, 3704(%r3)
	xor %r12, %r12, %r19
	and %r12, %r12, %r10
	xor %r11, %r19, %r12
	std %r11, 32(%r4)
	ld %r12, 3712(%r3)
	xor %r12, %r12, %r20
	and %r12, %r12, %r10
	xor %r11, %r20, %r12
	std %r11, 40(%r4)
	ld %r12, 3720(%r3)
	xor %r12, %r12, %r21
	and %r12, %r12, %r10
	xor %r11, %r21, %r12
	std %r11, 48(%r4)
	ld %r12, 3728(%r3)
	xor %r12, %r12, %r22
	and %r12, %r12, %r10
	xor %r11, %r22, %r12
	std %r11, 56(%r4)
	ld %r12, 3736(%r3)
	xor %r12, %r12, %r23
	and %r12, %r12, %r10
	xor %r11, %r23, %r12
	std %r11, 64(%r4)
	ld %r15, 3520(%r3)
	ld %r16, 3528(%r3)
	ld %r17, 3536(%r3)
	ld %r18, 3544(%r3)
	ld %r19, 3552(%r3)
	ld %r20, 3560(%r3)
	ld %r21, 3568(%r3)
	ld %r22, 3576(%r3)
	ld %r23, 3584(%r3)
	ld %r24, 3592(%r3)
	blr
