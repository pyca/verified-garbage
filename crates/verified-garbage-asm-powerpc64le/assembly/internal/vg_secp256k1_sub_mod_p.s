// The functions of `src/internal/vg_secp256k1_sub_mod_p.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_secp256k1_sub_mod_p:
	rlwinm %r4, %r4, 0, 0, 31
	rlwinm %r5, %r5, 0, 0, 31
	rlwinm %r6, %r6, 0, 0, 31
	add %r4, %r3, %r4
	add %r5, %r3, %r5
	add %r6, %r3, %r6
	lis %r11, -1
	ori %r11, %r11, 64559
	stw %r11, 3944(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
	stw %r11, 3948(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3952(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3956(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3960(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3964(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3968(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3972(%r3)
	addi %r7, %r3, 3944
	ld %r11, 0(%r5)
	ld %r12, 0(%r6)
	subfc %r11, %r12, %r11
	std %r11, 3840(%r3)
	ld %r11, 8(%r5)
	ld %r12, 8(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3848(%r3)
	ld %r11, 16(%r5)
	ld %r12, 16(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3856(%r3)
	ld %r11, 24(%r5)
	ld %r12, 24(%r6)
	subfe %r11, %r12, %r11
	std %r11, 3864(%r3)
	subfe %r10, %r10, %r10
	ld %r11, 3840(%r3)
	ld %r12, 0(%r7)
	addc %r11, %r11, %r12
	std %r11, 3912(%r3)
	ld %r11, 3848(%r3)
	ld %r12, 8(%r7)
	adde %r11, %r11, %r12
	std %r11, 3920(%r3)
	ld %r11, 3856(%r3)
	ld %r12, 16(%r7)
	adde %r11, %r11, %r12
	std %r11, 3928(%r3)
	ld %r11, 3864(%r3)
	ld %r12, 24(%r7)
	adde %r11, %r11, %r12
	std %r11, 3936(%r3)
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
