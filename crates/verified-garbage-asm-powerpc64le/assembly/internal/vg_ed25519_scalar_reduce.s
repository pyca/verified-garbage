// The functions of `src/internal/vg_ed25519_scalar_reduce.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_scalar_reduce:
	std %r14, 1024(%r5)
	std %r15, 1032(%r5)
	std %r16, 1040(%r5)
	std %r17, 1048(%r5)
	std %r18, 1056(%r5)
	std %r19, 1064(%r5)
	std %r26, 1072(%r5)
	std %r27, 1080(%r5)
	std %r28, 1088(%r5)
	std %r29, 1096(%r5)
	std %r30, 1104(%r5)
	std %r31, 1112(%r5)
	addi %r6, %r5, 0
	addi %r27, %r3, 0
	addi %r14, %r4, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r15, 64
	lis %r16, 22546
	ori %r16, %r16, 25370
	rldicr %r16, %r16, 32, 31
	oris %r16, %r16, 23797
	ori %r16, %r16, 54253
	lis %r19, 5342
	ori %r19, %r19, 63966
	rldicr %r19, %r19, 32, 31
	oris %r19, %r19, 41719
	ori %r19, %r19, 40150
20:
	addi %r15, %r15, -8
	add %r7, %r14, %r15
	ld %r12, 0(%r7)
	rldicl %r3, %r10, 4, 60
	rldicr %r4, %r11, 4, 59
	or %r3, %r3, %r4
	rldicl %r4, %r11, 4, 60
	rldicr %r11, %r10, 4, 59
	rldicl %r11, %r11, 60, 4
	addi %r10, %r9, 0
	addi %r9, %r8, 0
	addi %r8, %r12, 0
	mulld %r5, %r3, %r16
	mulhdu %r7, %r3, %r16
	mulld %r12, %r3, %r19
	mulhdu %r3, %r3, %r19
	addc %r7, %r7, %r12
	addze %r3, %r3
	mulld %r12, %r4, %r16
	addc %r7, %r7, %r12
	addze %r3, %r3
	mulld %r12, %r4, %r19
	add %r3, %r3, %r12
	subfc %r8, %r5, %r8
	subfe %r9, %r7, %r9
	subfe %r10, %r3, %r10
	li %r12, 0
	subfe %r11, %r12, %r11
	addze %r12, %r12
	addi %r12, %r12, -1
	and %r3, %r16, %r12
	addc %r8, %r8, %r3
	and %r3, %r19, %r12
	adde %r9, %r9, %r3
	addze %r10, %r10
	rldicl %r3, %r12, 1, 63
	rldicr %r3, %r3, 60, 3
	adde %r11, %r11, %r3
	cmpldi %cr0, %r15, 0
	bne %cr0, 20b
	std %r8, 160(%r6)
	std %r9, 168(%r6)
	std %r10, 176(%r6)
	std %r11, 184(%r6)
	addi %r14, %r27, 0
	lwz %r7, 160(%r6)
	stw %r7, 0(%r14)
	lwz %r7, 164(%r6)
	stw %r7, 4(%r14)
	lwz %r7, 168(%r6)
	stw %r7, 8(%r14)
	lwz %r7, 172(%r6)
	stw %r7, 12(%r14)
	lwz %r7, 176(%r6)
	stw %r7, 16(%r14)
	lwz %r7, 180(%r6)
	stw %r7, 20(%r14)
	lwz %r7, 184(%r6)
	stw %r7, 24(%r14)
	lwz %r7, 188(%r6)
	stw %r7, 28(%r14)
	ld %r14, 1024(%r6)
	ld %r15, 1032(%r6)
	ld %r16, 1040(%r6)
	ld %r17, 1048(%r6)
	ld %r18, 1056(%r6)
	ld %r19, 1064(%r6)
	ld %r26, 1072(%r6)
	ld %r27, 1080(%r6)
	ld %r28, 1088(%r6)
	ld %r29, 1096(%r6)
	ld %r30, 1104(%r6)
	ld %r31, 1112(%r6)
	blr
