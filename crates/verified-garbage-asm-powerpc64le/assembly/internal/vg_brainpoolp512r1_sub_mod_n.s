// The functions of `src/internal/vg_brainpoolp512r1_sub_mod_n.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

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
