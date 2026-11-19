// The functions of `src/internal/vg_brainpoolp320r1_sub_mod_n.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp320r1_sub_mod_n:
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
	addi %r7, %r3, 3904
	ld %r11, 0(%r5)
	ld %r12, 0(%r6)
	subfc %r11, %r12, %r11
	std %r11, 3776(%r3)
	ld %r11, 8(%r5)
	ld %r12, 8(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3784(%r3)
	ld %r11, 16(%r5)
	ld %r12, 16(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3792(%r3)
	ld %r11, 24(%r5)
	ld %r12, 24(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3800(%r3)
	ld %r11, 32(%r5)
	ld %r12, 32(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3808(%r3)
	subfe %r10, %r10, %r10
	ld %r11, 3776(%r3)
	ld %r12, 0(%r7)
	addc %r11, %r11, %r12
	std %r11, 3864(%r3)
	ld %r11, 3784(%r3)
	ld %r12, 8(%r7)
	adde %r11, %r11, %r12
	std %r11, 3872(%r3)
	ld %r11, 3792(%r3)
	ld %r12, 16(%r7)
	adde %r11, %r11, %r12
	std %r11, 3880(%r3)
	ld %r11, 3800(%r3)
	ld %r12, 24(%r7)
	adde %r11, %r11, %r12
	std %r11, 3888(%r3)
	ld %r11, 3808(%r3)
	ld %r12, 32(%r7)
	adde %r11, %r11, %r12
	std %r11, 3896(%r3)
	ld %r11, 3776(%r3)
	ld %r12, 3864(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 0(%r4)
	ld %r11, 3784(%r3)
	ld %r12, 3872(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 8(%r4)
	ld %r11, 3792(%r3)
	ld %r12, 3880(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 16(%r4)
	ld %r11, 3800(%r3)
	ld %r12, 3888(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 24(%r4)
	ld %r11, 3808(%r3)
	ld %r12, 3896(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 32(%r4)
	blr
