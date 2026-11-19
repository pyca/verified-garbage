// The functions of `src/internal/vg_brainpoolp320r1_mul_mod_n.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp320r1_mul_mod_n:
	rlwinm %r4, %r4, 0, 0, 31
	rlwinm %r5, %r5, 0, 0, 31
	rlwinm %r6, %r6, 0, 0, 31
	add %r4, %r3, %r4
	add %r5, %r3, %r5
	add %r6, %r3, %r6
	lis %r11, 17605
	ori %r11, %r11, 37649
	stw %r11, 3904(%r3)
	lis %r11, -31087
	ori %r11, %r11, 21851
	stw %r11, 3908(%r3)
	lis %r11, -4474
	ori %r11, %r11, 22761
	stw %r11, 3912(%r3)
	lis %r11, 11592
	ori %r11, %r11, 11975
	stw %r11, 3916(%r3)
	lis %r11, -18801
	ori %r11, %r11, 4771
	stw %r11, 3920(%r3)
	lis %r11, -1649
	ori %r11, %r11, 53157
	stw %r11, 3924(%r3)
	lis %r11, -11775
	ori %r11, %r11, 57445
	stw %r11, 3928(%r3)
	lis %r11, -7876
	ori %r11, %r11, 30814
	stw %r11, 3932(%r3)
	lis %r11, 14012
	ori %r11, %r11, 20407
	stw %r11, 3936(%r3)
	lis %r11, -11426
	ori %r11, %r11, 18208
	stw %r11, 3940(%r3)
	lis %r11, -926
	ori %r11, %r11, 16911
	stw %r11, 3824(%r3)
	lis %r11, 27970
	ori %r11, %r11, 58677
	stw %r11, 3828(%r3)
	std %r15, 3776(%r3)
	std %r16, 3784(%r3)
	std %r17, 3792(%r3)
	std %r18, 3800(%r3)
	std %r19, 3808(%r3)
	std %r20, 3816(%r3)
	li %r15, 0
	li %r16, 0
	li %r17, 0
	li %r18, 0
	li %r19, 0
	li %r20, 0
	addi %r7, %r3, 3904
	li %r8, 5
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
	addze %r20, %r20
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
	addze %r12, %r12
	ld %r10, 3824(%r3)
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
	addc %r19, %r20, %r0
	addze %r20, %r12
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 20b
	ld %r12, 0(%r7)
	subfc %r11, %r12, %r15
	std %r11, 3864(%r3)
	ld %r12, 8(%r7)
	subfe %r11, %r12, %r16
	std %r11, 3872(%r3)
	ld %r12, 16(%r7)
	subfe %r11, %r12, %r17
	std %r11, 3880(%r3)
	ld %r12, 24(%r7)
	subfe %r11, %r12, %r18
	std %r11, 3888(%r3)
	ld %r12, 32(%r7)
	subfe %r11, %r12, %r19
	std %r11, 3896(%r3)
	addze %r10, %r20
	li %r11, 0
	subf %r10, %r10, %r11
	ld %r12, 3864(%r3)
	xor %r12, %r12, %r15
	and %r12, %r12, %r10
	xor %r11, %r15, %r12
	std %r11, 0(%r4)
	ld %r12, 3872(%r3)
	xor %r12, %r12, %r16
	and %r12, %r12, %r10
	xor %r11, %r16, %r12
	std %r11, 8(%r4)
	ld %r12, 3880(%r3)
	xor %r12, %r12, %r17
	and %r12, %r12, %r10
	xor %r11, %r17, %r12
	std %r11, 16(%r4)
	ld %r12, 3888(%r3)
	xor %r12, %r12, %r18
	and %r12, %r12, %r10
	xor %r11, %r18, %r12
	std %r11, 24(%r4)
	ld %r12, 3896(%r3)
	xor %r12, %r12, %r19
	and %r12, %r12, %r10
	xor %r11, %r19, %r12
	std %r11, 32(%r4)
	ld %r15, 3776(%r3)
	ld %r16, 3784(%r3)
	ld %r17, 3792(%r3)
	ld %r18, 3800(%r3)
	ld %r19, 3808(%r3)
	ld %r20, 3816(%r3)
	blr
