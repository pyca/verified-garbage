// The functions of `src/internal/vg_p224_mul_mod_p.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p224_mul_mod_p:
	rlwinm %r4, %r4, 0, 0, 31
	rlwinm %r5, %r5, 0, 0, 31
	rlwinm %r6, %r6, 0, 0, 31
	add %r4, %r3, %r4
	add %r5, %r3, %r5
	add %r6, %r3, %r6
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 3944(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3948(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
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
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3972(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3880(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3884(%r3)
	li %r11, 0
	std %r11, 3840(%r3)
	std %r11, 3848(%r3)
	std %r11, 3856(%r3)
	std %r11, 3864(%r3)
	std %r11, 3872(%r3)
	addi %r7, %r3, 3944
	li %r8, 4
20:
	ld %r9, 0(%r5)
	li %r0, 0
	ld %r11, 0(%r6)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3840(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3840(%r3)
	ld %r11, 8(%r6)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3848(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3848(%r3)
	ld %r11, 16(%r6)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3856(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3856(%r3)
	ld %r11, 24(%r6)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3864(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3864(%r3)
	ld %r10, 3872(%r3)
	addc %r10, %r10, %r0
	std %r10, 3872(%r3)
	li %r12, 0
	addze %r12, %r12
	ld %r11, 3840(%r3)
	ld %r10, 3880(%r3)
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
	ld %r0, 3848(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3840(%r3)
	ld %r11, 16(%r7)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3856(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3848(%r3)
	ld %r11, 24(%r7)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	ld %r0, 3864(%r3)
	addc %r11, %r11, %r0
	addze %r0, %r10
	std %r11, 3856(%r3)
	ld %r10, 3872(%r3)
	addc %r10, %r10, %r0
	std %r10, 3864(%r3)
	addze %r12, %r12
	std %r12, 3872(%r3)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 20b
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
