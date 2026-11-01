// The functions of `src/internal/vg_p521_sub_mod_p.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_sub_mod_p:
	rlwinm %r4, %r4, 0, 0, 31
	rlwinm %r5, %r5, 0, 0, 31
	rlwinm %r6, %r6, 0, 0, 31
	add %r4, %r3, %r4
	add %r5, %r3, %r5
	add %r6, %r3, %r6
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3744(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3748(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3752(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3756(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3760(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3764(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3768(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3772(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
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
	addi %r7, %r3, 3744
	ld %r11, 0(%r5)
	ld %r12, 0(%r6)
	subfc %r11, %r12, %r11
	std %r11, 3520(%r3)
	ld %r11, 8(%r5)
	ld %r12, 8(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3528(%r3)
	ld %r11, 16(%r5)
	ld %r12, 16(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3536(%r3)
	ld %r11, 24(%r5)
	ld %r12, 24(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3544(%r3)
	ld %r11, 32(%r5)
	ld %r12, 32(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3552(%r3)
	ld %r11, 40(%r5)
	ld %r12, 40(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3560(%r3)
	ld %r11, 48(%r5)
	ld %r12, 48(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3568(%r3)
	ld %r11, 56(%r5)
	ld %r12, 56(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3576(%r3)
	ld %r11, 64(%r5)
	ld %r12, 64(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3584(%r3)
	subfe %r10, %r10, %r10
	ld %r11, 3520(%r3)
	ld %r12, 0(%r7)
	addc %r11, %r11, %r12
	std %r11, 3672(%r3)
	ld %r11, 3528(%r3)
	ld %r12, 8(%r7)
	adde %r11, %r11, %r12
	std %r11, 3680(%r3)
	ld %r11, 3536(%r3)
	ld %r12, 16(%r7)
	adde %r11, %r11, %r12
	std %r11, 3688(%r3)
	ld %r11, 3544(%r3)
	ld %r12, 24(%r7)
	adde %r11, %r11, %r12
	std %r11, 3696(%r3)
	ld %r11, 3552(%r3)
	ld %r12, 32(%r7)
	adde %r11, %r11, %r12
	std %r11, 3704(%r3)
	ld %r11, 3560(%r3)
	ld %r12, 40(%r7)
	adde %r11, %r11, %r12
	std %r11, 3712(%r3)
	ld %r11, 3568(%r3)
	ld %r12, 48(%r7)
	adde %r11, %r11, %r12
	std %r11, 3720(%r3)
	ld %r11, 3576(%r3)
	ld %r12, 56(%r7)
	adde %r11, %r11, %r12
	std %r11, 3728(%r3)
	ld %r11, 3584(%r3)
	ld %r12, 64(%r7)
	adde %r11, %r11, %r12
	std %r11, 3736(%r3)
	ld %r11, 3520(%r3)
	ld %r12, 3672(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 0(%r4)
	ld %r11, 3528(%r3)
	ld %r12, 3680(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 8(%r4)
	ld %r11, 3536(%r3)
	ld %r12, 3688(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 16(%r4)
	ld %r11, 3544(%r3)
	ld %r12, 3696(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 24(%r4)
	ld %r11, 3552(%r3)
	ld %r12, 3704(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 32(%r4)
	ld %r11, 3560(%r3)
	ld %r12, 3712(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 40(%r4)
	ld %r11, 3568(%r3)
	ld %r12, 3720(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 48(%r4)
	ld %r11, 3576(%r3)
	ld %r12, 3728(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 56(%r4)
	ld %r11, 3584(%r3)
	ld %r12, 3736(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 64(%r4)
	blr
