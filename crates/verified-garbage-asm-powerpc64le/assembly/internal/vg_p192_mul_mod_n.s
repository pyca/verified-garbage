// The functions of `src/internal/vg_p192_mul_mod_n.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p192_mul_mod_n:
	rlwinm %r4, %r4, 0, 0, 31
	rlwinm %r5, %r5, 0, 0, 31
	rlwinm %r6, %r6, 0, 0, 31
	add %r4, %r3, %r4
	add %r5, %r3, %r5
	add %r6, %r3, %r6
	lis %r11, -19246
	ori %r11, %r11, 10289
	stw %r11, 3984(%r3)
	lis %r11, 5227
	ori %r11, %r11, 51633
	stw %r11, 3988(%r3)
	lis %r11, -26146
	ori %r11, %r11, 63542
	stw %r11, 3992(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 3996(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 4000(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 4004(%r3)
	lis %r11, 3547
	ori %r11, %r11, 53039
	stw %r11, 3936(%r3)
	lis %r11, -30682
	ori %r11, %r11, 29191
	stw %r11, 3940(%r3)
	std %r15, 3904(%r3)
	std %r16, 3912(%r3)
	std %r17, 3920(%r3)
	std %r18, 3928(%r3)
	li %r15, 0
	li %r16, 0
	li %r17, 0
	li %r18, 0
	addi %r7, %r3, 3984
	li %r8, 3
20:
	ld %r9, 0(%r5)
	li %r0, 0
	ld %r11, 0(%r6)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	addc %r15, %r11, %r15
	addze %r0, %r10
	ld %r11, 8(%r6)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	addc %r16, %r11, %r16
	addze %r0, %r10
	ld %r11, 16(%r6)
	mulhdu %r10, %r9, %r11
	mulld %r11, %r9, %r11
	addc %r11, %r11, %r0
	addze %r10, %r10
	addc %r17, %r11, %r17
	addze %r0, %r10
	addc %r18, %r18, %r0
	li %r12, 0
	addze %r12, %r12
	ld %r10, 3936(%r3)
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
	addc %r17, %r18, %r0
	addze %r18, %r12
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 20b
	ld %r12, 0(%r7)
	subfc %r11, %r12, %r15
	std %r11, 3960(%r3)
	ld %r12, 8(%r7)
	subfe %r11, %r12, %r16
	std %r11, 3968(%r3)
	ld %r12, 16(%r7)
	subfe %r11, %r12, %r17
	std %r11, 3976(%r3)
	addze %r10, %r18
	li %r11, 0
	subf %r10, %r10, %r11
	ld %r12, 3960(%r3)
	xor %r12, %r12, %r15
	and %r12, %r12, %r10
	xor %r11, %r15, %r12
	std %r11, 0(%r4)
	ld %r12, 3968(%r3)
	xor %r12, %r12, %r16
	and %r12, %r12, %r10
	xor %r11, %r16, %r12
	std %r11, 8(%r4)
	ld %r12, 3976(%r3)
	xor %r12, %r12, %r17
	and %r12, %r12, %r10
	xor %r11, %r17, %r12
	std %r11, 16(%r4)
	ld %r15, 3904(%r3)
	ld %r16, 3912(%r3)
	ld %r17, 3920(%r3)
	ld %r18, 3928(%r3)
	blr
