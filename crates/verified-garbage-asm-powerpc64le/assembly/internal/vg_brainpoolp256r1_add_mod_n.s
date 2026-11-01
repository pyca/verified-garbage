// The functions of `src/internal/vg_brainpoolp256r1_add_mod_n.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp256r1_add_mod_n:
	rlwinm %r4, %r4, 0, 0, 31
	rlwinm %r5, %r5, 0, 0, 31
	rlwinm %r6, %r6, 0, 0, 31
	add %r4, %r3, %r4
	add %r5, %r3, %r5
	add %r6, %r3, %r6
	lis %r11, -26808
	ori %r11, %r11, 22183
	stw %r11, 3944(%r3)
	lis %r11, -28642
	ori %r11, %r11, 3714
	stw %r11, 3948(%r3)
	lis %r11, -19103
	ori %r11, %r11, 42743
	stw %r11, 3952(%r3)
	lis %r11, -29639
	ori %r11, %r11, 31395
	stw %r11, 3956(%r3)
	lis %r11, -25213
	ori %r11, %r11, 36209
	stw %r11, 3960(%r3)
	lis %r11, 15974
	ori %r11, %r11, 2704
	stw %r11, 3964(%r3)
	lis %r11, -24082
	ori %r11, %r11, 43452
	stw %r11, 3968(%r3)
	lis %r11, -22021
	ori %r11, %r11, 22491
	stw %r11, 3972(%r3)
	addi %r7, %r3, 3944
	ld %r11, 0(%r5)
	ld %r12, 0(%r6)
	addc %r11, %r11, %r12
	std %r11, 3840(%r3)
	ld %r11, 8(%r5)
	ld %r12, 8(%r6)
	adde %r11, %r11, %r12
	std %r11, 3848(%r3)
	ld %r11, 16(%r5)
	ld %r12, 16(%r6)
	adde %r11, %r11, %r12
	std %r11, 3856(%r3)
	ld %r11, 24(%r5)
	ld %r12, 24(%r6)
	adde %r11, %r11, %r12
	std %r11, 3864(%r3)
	li %r10, 0
	addze %r10, %r10
	std %r10, 3872(%r3)
	ld %r11, 3840(%r3)
	ld %r12, 0(%r7)
	subfc %r11, %r12, %r11
	std %r11, 3912(%r3)
	ld %r11, 3848(%r3)
	ld %r12, 8(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3920(%r3)
	ld %r11, 3856(%r3)
	ld %r12, 16(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3928(%r3)
	ld %r11, 3864(%r3)
	ld %r12, 24(%r7)
	subfe %r11, %r12, %r11
	std %r11, 3936(%r3)
	ld %r11, 3872(%r3)
	addze %r10, %r11
	li %r11, 0
	subf %r10, %r10, %r11
	ld %r11, 3840(%r3)
	ld %r12, 3912(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 0(%r4)
	ld %r11, 3848(%r3)
	ld %r12, 3920(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 8(%r4)
	ld %r11, 3856(%r3)
	ld %r12, 3928(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 16(%r4)
	ld %r11, 3864(%r3)
	ld %r12, 3936(%r3)
	xor %r12, %r12, %r11
	and %r12, %r12, %r10
	xor %r11, %r11, %r12
	std %r11, 24(%r4)
	blr
