// The functions of `src/internal/vg_ed25519_scalar_mul_add.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_scalar_mul_add:
	std %r14, 1024(%r7)
	std %r15, 1032(%r7)
	std %r16, 1040(%r7)
	std %r17, 1048(%r7)
	std %r18, 1056(%r7)
	std %r19, 1064(%r7)
	std %r26, 1072(%r7)
	std %r27, 1080(%r7)
	std %r28, 1088(%r7)
	std %r29, 1096(%r7)
	std %r30, 1104(%r7)
	std %r31, 1112(%r7)
	addi %r18, %r3, 0
	addi %r17, %r6, 0
	addi %r6, %r7, 0
	addi %r14, %r4, 0
	lwz %r7, 0(%r14)
	stw %r7, 64(%r6)
	lwz %r7, 4(%r14)
	stw %r7, 68(%r6)
	lwz %r7, 8(%r14)
	stw %r7, 72(%r6)
	lwz %r7, 12(%r14)
	stw %r7, 76(%r6)
	lwz %r7, 16(%r14)
	stw %r7, 80(%r6)
	lwz %r7, 20(%r14)
	stw %r7, 84(%r6)
	lwz %r7, 24(%r14)
	stw %r7, 88(%r6)
	lwz %r7, 28(%r14)
	stw %r7, 92(%r6)
	addi %r14, %r5, 0
	lwz %r7, 0(%r14)
	stw %r7, 96(%r6)
	lwz %r7, 4(%r14)
	stw %r7, 100(%r6)
	lwz %r7, 8(%r14)
	stw %r7, 104(%r6)
	lwz %r7, 12(%r14)
	stw %r7, 108(%r6)
	lwz %r7, 16(%r14)
	stw %r7, 112(%r6)
	lwz %r7, 20(%r14)
	stw %r7, 116(%r6)
	lwz %r7, 24(%r14)
	stw %r7, 120(%r6)
	lwz %r7, 28(%r14)
	stw %r7, 124(%r6)
	addi %r14, %r17, 0
	lwz %r7, 0(%r14)
	stw %r7, 128(%r6)
	lwz %r7, 4(%r14)
	stw %r7, 132(%r6)
	lwz %r7, 8(%r14)
	stw %r7, 136(%r6)
	lwz %r7, 12(%r14)
	stw %r7, 140(%r6)
	lwz %r7, 16(%r14)
	stw %r7, 144(%r6)
	lwz %r7, 20(%r14)
	stw %r7, 148(%r6)
	lwz %r7, 24(%r14)
	stw %r7, 152(%r6)
	lwz %r7, 28(%r14)
	stw %r7, 156(%r6)
	li %r10, 38
	li %r8, 0
	li %r7, 0
	stw %r7, 864(%r6)
	stw %r7, 868(%r6)
	stw %r7, 872(%r6)
	stw %r7, 876(%r6)
	stw %r7, 880(%r6)
	stw %r7, 884(%r6)
	stw %r7, 888(%r6)
	stw %r7, 892(%r6)
	addi %r9, %r6, 0
	li %r11, 8
20:
	lwz %r4, 96(%r9)
	li %r8, 0
	lwz %r5, 128(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 864(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 132(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 868(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 136(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 872(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 140(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 876(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 144(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 880(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 148(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 884(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 152(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 888(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r9)
	rldicl %r8, %r7, 32, 32
	lwz %r5, 156(%r6)
	mulld %r5, %r4, %r5
	lwz %r7, 892(%r9)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r9)
	rldicl %r8, %r7, 32, 32
	stw %r8, 896(%r9)
	addi %r9, %r9, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 20b
	li %r8, 0
	lwz %r7, 864(%r6)
	lwz %r5, 64(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 864(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 868(%r6)
	lwz %r5, 68(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 868(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 872(%r6)
	lwz %r5, 72(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 872(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 876(%r6)
	lwz %r5, 76(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 876(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 880(%r6)
	lwz %r5, 80(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 880(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 884(%r6)
	lwz %r5, 84(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 884(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 888(%r6)
	lwz %r5, 88(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 888(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 892(%r6)
	lwz %r5, 92(%r6)
	add %r7, %r7, %r5
	add %r7, %r7, %r8
	stw %r7, 892(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 896(%r6)
	add %r7, %r7, %r8
	stw %r7, 896(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 900(%r6)
	add %r7, %r7, %r8
	stw %r7, 900(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 904(%r6)
	add %r7, %r7, %r8
	stw %r7, 904(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 908(%r6)
	add %r7, %r7, %r8
	stw %r7, 908(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 912(%r6)
	add %r7, %r7, %r8
	stw %r7, 912(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 916(%r6)
	add %r7, %r7, %r8
	stw %r7, 916(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 920(%r6)
	add %r7, %r7, %r8
	stw %r7, 920(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 924(%r6)
	add %r7, %r7, %r8
	stw %r7, 924(%r6)
	rldicl %r8, %r7, 32, 32
	addi %r14, %r6, 512
	lwz %r7, 864(%r6)
	stw %r7, 0(%r14)
	lwz %r7, 868(%r6)
	stw %r7, 4(%r14)
	lwz %r7, 872(%r6)
	stw %r7, 8(%r14)
	lwz %r7, 876(%r6)
	stw %r7, 12(%r14)
	lwz %r7, 880(%r6)
	stw %r7, 16(%r14)
	lwz %r7, 884(%r6)
	stw %r7, 20(%r14)
	lwz %r7, 888(%r6)
	stw %r7, 24(%r14)
	lwz %r7, 892(%r6)
	stw %r7, 28(%r14)
	lwz %r7, 896(%r6)
	stw %r7, 32(%r14)
	lwz %r7, 900(%r6)
	stw %r7, 36(%r14)
	lwz %r7, 904(%r6)
	stw %r7, 40(%r14)
	lwz %r7, 908(%r6)
	stw %r7, 44(%r14)
	lwz %r7, 912(%r6)
	stw %r7, 48(%r14)
	lwz %r7, 916(%r6)
	stw %r7, 52(%r14)
	lwz %r7, 920(%r6)
	stw %r7, 56(%r14)
	lwz %r7, 924(%r6)
	stw %r7, 60(%r14)
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
21:
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
	bne %cr0, 21b
	std %r8, 160(%r6)
	std %r9, 168(%r6)
	std %r10, 176(%r6)
	std %r11, 184(%r6)
	addi %r14, %r18, 0
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
