// The functions of `src/internal/vg_brainpoolp384r1_sub_mod_n.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp384r1_sub_mod_n:
	rlwinm %r4, %r4, 0, 0, 31
	rlwinm %r5, %r5, 0, 0, 31
	rlwinm %r6, %r6, 0, 0, 31
	add %r4, %r3, %r4
	add %r5, %r3, %r5
	add %r6, %r3, %r6
	lis %r11, -5884
	ori %r11, %r11, 25957
	stw %r11, 3864(%r3)
	lis %r11, 15240
	ori %r11, %r11, 12802
	stw %r11, 3868(%r3)
	lis %r11, 27519
	ori %r11, %r11, 49936
	stw %r11, 3872(%r3)
	lis %r11, -12486
	ori %r11, %r11, 46767
	stw %r11, 3876(%r3)
	lis %r11, -21500
	ori %r11, %r11, 9639
	stw %r11, 3880(%r3)
	lis %r11, 7958
	ori %r11, %r11, 28268
	stw %r11, 3884(%r3)
	lis %r11, -4780
	ori %r11, %r11, 22195
	stw %r11, 3888(%r3)
	lis %r11, 5423
	ori %r11, %r11, 28937
	stw %r11, 3892(%r3)
	lis %r11, 20710
	ori %r11, %r11, 16863
	stw %r11, 3896(%r3)
	lis %r11, 3933
	ori %r11, %r11, 28542
	stw %r11, 3900(%r3)
	lis %r11, -23752
	ori %r11, %r11, 27944
	stw %r11, 3904(%r3)
	lis %r11, -29511
	ori %r11, %r11, 7810
	stw %r11, 3908(%r3)
	addi %r7, %r3, 3864
	ld %r11, 0(%r5)
	ld %r12, 0(%r6)
	subfc %r11, %r12, %r11
	std %r11, 3712(%r3)
	ld %r11, 8(%r5)
	ld %r12, 8(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3720(%r3)
	ld %r11, 16(%r5)
	ld %r12, 16(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3728(%r3)
	ld %r11, 24(%r5)
	ld %r12, 24(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3736(%r3)
	ld %r11, 32(%r5)
	ld %r12, 32(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3744(%r3)
	ld %r11, 40(%r5)
	ld %r12, 40(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3752(%r3)
	subfe %r10, %r10, %r10
	ld %r11, 3712(%r3)
	ld %r12, 0(%r7)
	addc %r11, %r11, %r12
	std %r11, 3816(%r3)
	ld %r11, 3720(%r3)
	ld %r12, 8(%r7)
	adde %r11, %r11, %r12
	std %r11, 3824(%r3)
	ld %r11, 3728(%r3)
	ld %r12, 16(%r7)
	adde %r11, %r11, %r12
	std %r11, 3832(%r3)
	ld %r11, 3736(%r3)
	ld %r12, 24(%r7)
	adde %r11, %r11, %r12
	std %r11, 3840(%r3)
	ld %r11, 3744(%r3)
	ld %r12, 32(%r7)
	adde %r11, %r11, %r12
	std %r11, 3848(%r3)
	ld %r11, 3752(%r3)
	ld %r12, 40(%r7)
	adde %r11, %r11, %r12
	std %r11, 3856(%r3)
	ld %r11, 3712(%r3)
	ld %r12, 3816(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 0(%r4)
	ld %r11, 3720(%r3)
	ld %r12, 3824(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 8(%r4)
	ld %r11, 3728(%r3)
	ld %r12, 3832(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 16(%r4)
	ld %r11, 3736(%r3)
	ld %r12, 3840(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 24(%r4)
	ld %r11, 3744(%r3)
	ld %r12, 3848(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 32(%r4)
	ld %r11, 3752(%r3)
	ld %r12, 3856(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 40(%r4)
	blr
