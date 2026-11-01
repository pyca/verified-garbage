// The functions of `src/internal/vg_p384_add_mod_n.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_add_mod_n:
	rlwinm %r4, %r4, 0, 0, 31
	rlwinm %r5, %r5, 0, 0, 31
	rlwinm %r6, %r6, 0, 0, 31
	add %r4, %r3, %r4
	add %r5, %r3, %r5
	add %r6, %r3, %r6
	lis %r11, -13115
	ori %r11, %r11, 10611
	stw %r11, 3864(%r3)
	lis %r11, -4884
	ori %r11, %r11, 6506
	stw %r11, 3868(%r3)
	lis %r11, 18608
	ori %r11, %r11, 42874
	stw %r11, 3872(%r3)
	lis %r11, 22554
	ori %r11, %r11, 3506
	stw %r11, 3876(%r3)
	lis %r11, -3017
	ori %r11, %r11, 11743
	stw %r11, 3880(%r3)
	lis %r11, -14493
	ori %r11, %r11, 19841
	stw %r11, 3884(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3888(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3892(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3896(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3900(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3904(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3908(%r3)
	addi %r7, %r3, 3864
	ld %r11, 0(%r5)
	ld %r12, 0(%r6)
	addc %r11, %r11, %r12
	std %r11, 3712(%r3)
	ld %r11, 8(%r5)
	ld %r12, 8(%r6)
	adde %r11, %r11, %r12
	std %r11, 3720(%r3)
	ld %r11, 16(%r5)
	ld %r12, 16(%r6)
	adde %r11, %r11, %r12
	std %r11, 3728(%r3)
	ld %r11, 24(%r5)
	ld %r12, 24(%r6)
	adde %r11, %r11, %r12
	std %r11, 3736(%r3)
	ld %r11, 32(%r5)
	ld %r12, 32(%r6)
	adde %r11, %r11, %r12
	std %r11, 3744(%r3)
	ld %r11, 40(%r5)
	ld %r12, 40(%r6)
	adde %r11, %r11, %r12
	std %r11, 3752(%r3)
	li %r10, 0
	addze %r10, %r10
	std %r10, 3760(%r3)
	ld %r11, 3712(%r3)
	ld %r12, 0(%r7)
	subfc %r11, %r12, %r11
	std %r11, 3816(%r3)
	ld %r11, 3720(%r3)
	ld %r12, 8(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3824(%r3)
	ld %r11, 3728(%r3)
	ld %r12, 16(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3832(%r3)
	ld %r11, 3736(%r3)
	ld %r12, 24(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3840(%r3)
	ld %r11, 3744(%r3)
	ld %r12, 32(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3848(%r3)
	ld %r11, 3752(%r3)
	ld %r12, 40(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3856(%r3)
	ld %r11, 3760(%r3)
	addze %r10, %r11
	li %r11, 0
	subf %r10, %r10, %r11
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
