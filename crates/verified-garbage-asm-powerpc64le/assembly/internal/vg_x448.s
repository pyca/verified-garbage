// The functions of `src/internal/vg_x448.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x448:
	lwz %r7, 0(%r5)
	stw %r7, 0(%r6)
	stw %r7, 168(%r6)
	lwz %r7, 4(%r5)
	stw %r7, 4(%r6)
	stw %r7, 172(%r6)
	lwz %r7, 8(%r5)
	stw %r7, 8(%r6)
	stw %r7, 176(%r6)
	lwz %r7, 12(%r5)
	stw %r7, 12(%r6)
	stw %r7, 180(%r6)
	lwz %r7, 16(%r5)
	stw %r7, 16(%r6)
	stw %r7, 184(%r6)
	lwz %r7, 20(%r5)
	stw %r7, 20(%r6)
	stw %r7, 188(%r6)
	lwz %r7, 24(%r5)
	stw %r7, 24(%r6)
	stw %r7, 192(%r6)
	lwz %r7, 28(%r5)
	stw %r7, 28(%r6)
	stw %r7, 196(%r6)
	lwz %r7, 32(%r5)
	stw %r7, 32(%r6)
	stw %r7, 200(%r6)
	lwz %r7, 36(%r5)
	stw %r7, 36(%r6)
	stw %r7, 204(%r6)
	lwz %r7, 40(%r5)
	stw %r7, 40(%r6)
	stw %r7, 208(%r6)
	lwz %r7, 44(%r5)
	stw %r7, 44(%r6)
	stw %r7, 212(%r6)
	lwz %r7, 48(%r5)
	stw %r7, 48(%r6)
	stw %r7, 216(%r6)
	lwz %r7, 52(%r5)
	stw %r7, 52(%r6)
	stw %r7, 220(%r6)
	li %r7, 1
	li %r8, 0
	li %r5, 0
	ori %r5, %r5, 39081
	stw %r7, 56(%r6)
	stw %r8, 112(%r6)
	stw %r7, 224(%r6)
	stw %r5, 784(%r6)
	stw %r8, 60(%r6)
	stw %r8, 64(%r6)
	stw %r8, 68(%r6)
	stw %r8, 72(%r6)
	stw %r8, 76(%r6)
	stw %r8, 80(%r6)
	stw %r8, 84(%r6)
	stw %r8, 88(%r6)
	stw %r8, 92(%r6)
	stw %r8, 96(%r6)
	stw %r8, 100(%r6)
	stw %r8, 104(%r6)
	stw %r8, 108(%r6)
	stw %r8, 116(%r6)
	stw %r8, 120(%r6)
	stw %r8, 124(%r6)
	stw %r8, 128(%r6)
	stw %r8, 132(%r6)
	stw %r8, 136(%r6)
	stw %r8, 140(%r6)
	stw %r8, 144(%r6)
	stw %r8, 148(%r6)
	stw %r8, 152(%r6)
	stw %r8, 156(%r6)
	stw %r8, 160(%r6)
	stw %r8, 164(%r6)
	stw %r8, 228(%r6)
	stw %r8, 232(%r6)
	stw %r8, 236(%r6)
	stw %r8, 240(%r6)
	stw %r8, 244(%r6)
	stw %r8, 248(%r6)
	stw %r8, 252(%r6)
	stw %r8, 256(%r6)
	stw %r8, 260(%r6)
	stw %r8, 264(%r6)
	stw %r8, 268(%r6)
	stw %r8, 272(%r6)
	stw %r8, 276(%r6)
	stw %r8, 788(%r6)
	stw %r8, 792(%r6)
	stw %r8, 796(%r6)
	stw %r8, 800(%r6)
	stw %r8, 804(%r6)
	stw %r8, 808(%r6)
	stw %r8, 812(%r6)
	stw %r8, 816(%r6)
	stw %r8, 820(%r6)
	stw %r8, 824(%r6)
	stw %r8, 828(%r6)
	stw %r8, 832(%r6)
	stw %r8, 836(%r6)
	addi %r9, %r6, 0
	li %r11, 56
20:
	lbz %r7, 0(%r4)
	rldicr %r8, %r7, 63, 0
	rldicl %r8, %r8, 1, 63
	stb %r8, 1064(%r9)
	rldicr %r8, %r7, 62, 1
	rldicl %r8, %r8, 1, 63
	stb %r8, 1065(%r9)
	rldicr %r8, %r7, 61, 2
	rldicl %r8, %r8, 1, 63
	stb %r8, 1066(%r9)
	rldicr %r8, %r7, 60, 3
	rldicl %r8, %r8, 1, 63
	stb %r8, 1067(%r9)
	rldicr %r8, %r7, 59, 4
	rldicl %r8, %r8, 1, 63
	stb %r8, 1068(%r9)
	rldicr %r8, %r7, 58, 5
	rldicl %r8, %r8, 1, 63
	stb %r8, 1069(%r9)
	rldicr %r8, %r7, 57, 6
	rldicl %r8, %r8, 1, 63
	stb %r8, 1070(%r9)
	rldicr %r8, %r7, 56, 7
	rldicl %r8, %r8, 1, 63
	stb %r8, 1071(%r9)
	addi %r4, %r4, 1
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 20b
	li %r7, 0
	stb %r7, 1064(%r6)
	stb %r7, 1065(%r6)
	li %r7, 1
	stb %r7, 1511(%r6)
	li %r12, 448
	li %r0, 0
21:
	addi %r12, %r12, -1
	add %r4, %r6, %r12
	lbz %r4, 1064(%r4)
	xor %r0, %r0, %r4
	li %r11, 0
	subf %r11, %r0, %r11
	lwz %r5, 56(%r6)
	lwz %r7, 168(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 56(%r6)
	stw %r7, 168(%r6)
	lwz %r5, 60(%r6)
	lwz %r7, 172(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 60(%r6)
	stw %r7, 172(%r6)
	lwz %r5, 64(%r6)
	lwz %r7, 176(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 64(%r6)
	stw %r7, 176(%r6)
	lwz %r5, 68(%r6)
	lwz %r7, 180(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 68(%r6)
	stw %r7, 180(%r6)
	lwz %r5, 72(%r6)
	lwz %r7, 184(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 72(%r6)
	stw %r7, 184(%r6)
	lwz %r5, 76(%r6)
	lwz %r7, 188(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 76(%r6)
	stw %r7, 188(%r6)
	lwz %r5, 80(%r6)
	lwz %r7, 192(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 80(%r6)
	stw %r7, 192(%r6)
	lwz %r5, 84(%r6)
	lwz %r7, 196(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 84(%r6)
	stw %r7, 196(%r6)
	lwz %r5, 88(%r6)
	lwz %r7, 200(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 88(%r6)
	stw %r7, 200(%r6)
	lwz %r5, 92(%r6)
	lwz %r7, 204(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 92(%r6)
	stw %r7, 204(%r6)
	lwz %r5, 96(%r6)
	lwz %r7, 208(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 96(%r6)
	stw %r7, 208(%r6)
	lwz %r5, 100(%r6)
	lwz %r7, 212(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 100(%r6)
	stw %r7, 212(%r6)
	lwz %r5, 104(%r6)
	lwz %r7, 216(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 104(%r6)
	stw %r7, 216(%r6)
	lwz %r5, 108(%r6)
	lwz %r7, 220(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 108(%r6)
	stw %r7, 220(%r6)
	lwz %r5, 112(%r6)
	lwz %r7, 224(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 224(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 228(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 228(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 232(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 232(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 236(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 236(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 240(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 240(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 244(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 244(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 248(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 248(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 252(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 252(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 256(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 256(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 260(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 260(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 264(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 264(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 268(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 268(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 272(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 272(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 276(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 276(%r6)
	addi %r0, %r4, 0
	ld %r7, 56(%r6)
	ld %r8, 112(%r6)
	addc %r7, %r7, %r8
	std %r7, 280(%r6)
	ld %r7, 64(%r6)
	ld %r8, 120(%r6)
	adde %r7, %r7, %r8
	std %r7, 288(%r6)
	ld %r7, 72(%r6)
	ld %r8, 128(%r6)
	adde %r7, %r7, %r8
	std %r7, 296(%r6)
	ld %r7, 80(%r6)
	ld %r8, 136(%r6)
	adde %r7, %r7, %r8
	std %r7, 304(%r6)
	ld %r7, 88(%r6)
	ld %r8, 144(%r6)
	adde %r7, %r7, %r8
	std %r7, 312(%r6)
	ld %r7, 96(%r6)
	ld %r8, 152(%r6)
	adde %r7, %r7, %r8
	std %r7, 320(%r6)
	ld %r7, 104(%r6)
	ld %r8, 160(%r6)
	adde %r7, %r7, %r8
	std %r7, 328(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 280(%r6)
	addc %r7, %r7, %r4
	std %r7, 280(%r6)
	ld %r7, 288(%r6)
	adde %r7, %r7, %r8
	std %r7, 288(%r6)
	ld %r7, 296(%r6)
	adde %r7, %r7, %r8
	std %r7, 296(%r6)
	ld %r7, 304(%r6)
	adde %r7, %r7, %r5
	std %r7, 304(%r6)
	ld %r7, 312(%r6)
	adde %r7, %r7, %r8
	std %r7, 312(%r6)
	ld %r7, 320(%r6)
	adde %r7, %r7, %r8
	std %r7, 320(%r6)
	ld %r7, 328(%r6)
	adde %r7, %r7, %r8
	std %r7, 328(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 280(%r6)
	addc %r7, %r7, %r4
	std %r7, 280(%r6)
	ld %r7, 288(%r6)
	adde %r7, %r7, %r8
	std %r7, 288(%r6)
	ld %r7, 296(%r6)
	adde %r7, %r7, %r8
	std %r7, 296(%r6)
	ld %r7, 304(%r6)
	adde %r7, %r7, %r5
	std %r7, 304(%r6)
	ld %r7, 312(%r6)
	adde %r7, %r7, %r8
	std %r7, 312(%r6)
	ld %r7, 320(%r6)
	adde %r7, %r7, %r8
	std %r7, 320(%r6)
	ld %r7, 328(%r6)
	adde %r7, %r7, %r8
	std %r7, 328(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
22:
	ld %r4, 280(%r9)
	li %r8, 0
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 288(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 296(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 304(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 312(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 320(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 328(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 22b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 504(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 512(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 520(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 528(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 536(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 544(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 552(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 504(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 504(%r6)
	ld %r7, 512(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 512(%r6)
	ld %r7, 520(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 520(%r6)
	ld %r7, 528(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 528(%r6)
	ld %r7, 536(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 536(%r6)
	ld %r7, 544(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 544(%r6)
	ld %r7, 552(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 552(%r6)
	addze %r4, %r4
	ld %r7, 528(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 528(%r6)
	ld %r7, 536(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 536(%r6)
	ld %r7, 544(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 544(%r6)
	ld %r7, 552(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 552(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 504(%r6)
	addc %r7, %r7, %r4
	std %r7, 504(%r6)
	ld %r7, 512(%r6)
	adde %r7, %r7, %r8
	std %r7, 512(%r6)
	ld %r7, 520(%r6)
	adde %r7, %r7, %r8
	std %r7, 520(%r6)
	ld %r7, 528(%r6)
	adde %r7, %r7, %r5
	std %r7, 528(%r6)
	ld %r7, 536(%r6)
	adde %r7, %r7, %r8
	std %r7, 536(%r6)
	ld %r7, 544(%r6)
	adde %r7, %r7, %r8
	std %r7, 544(%r6)
	ld %r7, 552(%r6)
	adde %r7, %r7, %r8
	std %r7, 552(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 504(%r6)
	addc %r7, %r7, %r4
	std %r7, 504(%r6)
	ld %r7, 512(%r6)
	adde %r7, %r7, %r8
	std %r7, 512(%r6)
	ld %r7, 520(%r6)
	adde %r7, %r7, %r8
	std %r7, 520(%r6)
	ld %r7, 528(%r6)
	adde %r7, %r7, %r5
	std %r7, 528(%r6)
	ld %r7, 536(%r6)
	adde %r7, %r7, %r8
	std %r7, 536(%r6)
	ld %r7, 544(%r6)
	adde %r7, %r7, %r8
	std %r7, 544(%r6)
	ld %r7, 552(%r6)
	adde %r7, %r7, %r8
	std %r7, 552(%r6)
	ld %r7, 56(%r6)
	ld %r8, 112(%r6)
	subfc %r7, %r8, %r7
	std %r7, 336(%r6)
	ld %r7, 64(%r6)
	ld %r8, 120(%r6)
	subfe %r7, %r8, %r7
	std %r7, 344(%r6)
	ld %r7, 72(%r6)
	ld %r8, 128(%r6)
	subfe %r7, %r8, %r7
	std %r7, 352(%r6)
	ld %r7, 80(%r6)
	ld %r8, 136(%r6)
	subfe %r7, %r8, %r7
	std %r7, 360(%r6)
	ld %r7, 88(%r6)
	ld %r8, 144(%r6)
	subfe %r7, %r8, %r7
	std %r7, 368(%r6)
	ld %r7, 96(%r6)
	ld %r8, 152(%r6)
	subfe %r7, %r8, %r7
	std %r7, 376(%r6)
	ld %r7, 104(%r6)
	ld %r8, 160(%r6)
	subfe %r7, %r8, %r7
	std %r7, 384(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 336(%r6)
	subfc %r7, %r4, %r7
	std %r7, 336(%r6)
	ld %r7, 344(%r6)
	subfe %r7, %r8, %r7
	std %r7, 344(%r6)
	ld %r7, 352(%r6)
	subfe %r7, %r8, %r7
	std %r7, 352(%r6)
	ld %r7, 360(%r6)
	subfe %r7, %r5, %r7
	std %r7, 360(%r6)
	ld %r7, 368(%r6)
	subfe %r7, %r8, %r7
	std %r7, 368(%r6)
	ld %r7, 376(%r6)
	subfe %r7, %r8, %r7
	std %r7, 376(%r6)
	ld %r7, 384(%r6)
	subfe %r7, %r8, %r7
	std %r7, 384(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 336(%r6)
	subfc %r7, %r4, %r7
	std %r7, 336(%r6)
	ld %r7, 344(%r6)
	subfe %r7, %r8, %r7
	std %r7, 344(%r6)
	ld %r7, 352(%r6)
	subfe %r7, %r8, %r7
	std %r7, 352(%r6)
	ld %r7, 360(%r6)
	subfe %r7, %r5, %r7
	std %r7, 360(%r6)
	ld %r7, 368(%r6)
	subfe %r7, %r8, %r7
	std %r7, 368(%r6)
	ld %r7, 376(%r6)
	subfe %r7, %r8, %r7
	std %r7, 376(%r6)
	ld %r7, 384(%r6)
	subfe %r7, %r8, %r7
	std %r7, 384(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
23:
	ld %r4, 336(%r9)
	li %r8, 0
	ld %r5, 336(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 344(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 352(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 360(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 368(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 376(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 384(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 23b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 560(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 568(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 576(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 584(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 560(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 560(%r6)
	ld %r7, 568(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 568(%r6)
	ld %r7, 576(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 576(%r6)
	ld %r7, 584(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	addze %r4, %r4
	ld %r7, 584(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 560(%r6)
	addc %r7, %r7, %r4
	std %r7, 560(%r6)
	ld %r7, 568(%r6)
	adde %r7, %r7, %r8
	std %r7, 568(%r6)
	ld %r7, 576(%r6)
	adde %r7, %r7, %r8
	std %r7, 576(%r6)
	ld %r7, 584(%r6)
	adde %r7, %r7, %r5
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 560(%r6)
	addc %r7, %r7, %r4
	std %r7, 560(%r6)
	ld %r7, 568(%r6)
	adde %r7, %r7, %r8
	std %r7, 568(%r6)
	ld %r7, 576(%r6)
	adde %r7, %r7, %r8
	std %r7, 576(%r6)
	ld %r7, 584(%r6)
	adde %r7, %r7, %r5
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	ld %r7, 504(%r6)
	ld %r8, 560(%r6)
	subfc %r7, %r8, %r7
	std %r7, 616(%r6)
	ld %r7, 512(%r6)
	ld %r8, 568(%r6)
	subfe %r7, %r8, %r7
	std %r7, 624(%r6)
	ld %r7, 520(%r6)
	ld %r8, 576(%r6)
	subfe %r7, %r8, %r7
	std %r7, 632(%r6)
	ld %r7, 528(%r6)
	ld %r8, 584(%r6)
	subfe %r7, %r8, %r7
	std %r7, 640(%r6)
	ld %r7, 536(%r6)
	ld %r8, 592(%r6)
	subfe %r7, %r8, %r7
	std %r7, 648(%r6)
	ld %r7, 544(%r6)
	ld %r8, 600(%r6)
	subfe %r7, %r8, %r7
	std %r7, 656(%r6)
	ld %r7, 552(%r6)
	ld %r8, 608(%r6)
	subfe %r7, %r8, %r7
	std %r7, 664(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 616(%r6)
	subfc %r7, %r4, %r7
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	subfe %r7, %r8, %r7
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	subfe %r7, %r8, %r7
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	subfe %r7, %r5, %r7
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	subfe %r7, %r8, %r7
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	subfe %r7, %r8, %r7
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	subfe %r7, %r8, %r7
	std %r7, 664(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 616(%r6)
	subfc %r7, %r4, %r7
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	subfe %r7, %r8, %r7
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	subfe %r7, %r8, %r7
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	subfe %r7, %r5, %r7
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	subfe %r7, %r8, %r7
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	subfe %r7, %r8, %r7
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	subfe %r7, %r8, %r7
	std %r7, 664(%r6)
	ld %r7, 168(%r6)
	ld %r8, 224(%r6)
	addc %r7, %r7, %r8
	std %r7, 392(%r6)
	ld %r7, 176(%r6)
	ld %r8, 232(%r6)
	adde %r7, %r7, %r8
	std %r7, 400(%r6)
	ld %r7, 184(%r6)
	ld %r8, 240(%r6)
	adde %r7, %r7, %r8
	std %r7, 408(%r6)
	ld %r7, 192(%r6)
	ld %r8, 248(%r6)
	adde %r7, %r7, %r8
	std %r7, 416(%r6)
	ld %r7, 200(%r6)
	ld %r8, 256(%r6)
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 208(%r6)
	ld %r8, 264(%r6)
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 216(%r6)
	ld %r8, 272(%r6)
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 392(%r6)
	addc %r7, %r7, %r4
	std %r7, 392(%r6)
	ld %r7, 400(%r6)
	adde %r7, %r7, %r8
	std %r7, 400(%r6)
	ld %r7, 408(%r6)
	adde %r7, %r7, %r8
	std %r7, 408(%r6)
	ld %r7, 416(%r6)
	adde %r7, %r7, %r5
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 392(%r6)
	addc %r7, %r7, %r4
	std %r7, 392(%r6)
	ld %r7, 400(%r6)
	adde %r7, %r7, %r8
	std %r7, 400(%r6)
	ld %r7, 408(%r6)
	adde %r7, %r7, %r8
	std %r7, 408(%r6)
	ld %r7, 416(%r6)
	adde %r7, %r7, %r5
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
	ld %r7, 168(%r6)
	ld %r8, 224(%r6)
	subfc %r7, %r8, %r7
	std %r7, 448(%r6)
	ld %r7, 176(%r6)
	ld %r8, 232(%r6)
	subfe %r7, %r8, %r7
	std %r7, 456(%r6)
	ld %r7, 184(%r6)
	ld %r8, 240(%r6)
	subfe %r7, %r8, %r7
	std %r7, 464(%r6)
	ld %r7, 192(%r6)
	ld %r8, 248(%r6)
	subfe %r7, %r8, %r7
	std %r7, 472(%r6)
	ld %r7, 200(%r6)
	ld %r8, 256(%r6)
	subfe %r7, %r8, %r7
	std %r7, 480(%r6)
	ld %r7, 208(%r6)
	ld %r8, 264(%r6)
	subfe %r7, %r8, %r7
	std %r7, 488(%r6)
	ld %r7, 216(%r6)
	ld %r8, 272(%r6)
	subfe %r7, %r8, %r7
	std %r7, 496(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 448(%r6)
	subfc %r7, %r4, %r7
	std %r7, 448(%r6)
	ld %r7, 456(%r6)
	subfe %r7, %r8, %r7
	std %r7, 456(%r6)
	ld %r7, 464(%r6)
	subfe %r7, %r8, %r7
	std %r7, 464(%r6)
	ld %r7, 472(%r6)
	subfe %r7, %r5, %r7
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	subfe %r7, %r8, %r7
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	subfe %r7, %r8, %r7
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	subfe %r7, %r8, %r7
	std %r7, 496(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 448(%r6)
	subfc %r7, %r4, %r7
	std %r7, 448(%r6)
	ld %r7, 456(%r6)
	subfe %r7, %r8, %r7
	std %r7, 456(%r6)
	ld %r7, 464(%r6)
	subfe %r7, %r8, %r7
	std %r7, 464(%r6)
	ld %r7, 472(%r6)
	subfe %r7, %r5, %r7
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	subfe %r7, %r8, %r7
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	subfe %r7, %r8, %r7
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	subfe %r7, %r8, %r7
	std %r7, 496(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
24:
	ld %r4, 448(%r9)
	li %r8, 0
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 288(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 296(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 304(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 312(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 320(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 328(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 24b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 672(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 680(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 688(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 696(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 704(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 712(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 720(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 672(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 672(%r6)
	ld %r7, 680(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 680(%r6)
	ld %r7, 688(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 688(%r6)
	ld %r7, 696(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 696(%r6)
	ld %r7, 704(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 704(%r6)
	ld %r7, 712(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 712(%r6)
	ld %r7, 720(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 720(%r6)
	addze %r4, %r4
	ld %r7, 696(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 696(%r6)
	ld %r7, 704(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 704(%r6)
	ld %r7, 712(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 712(%r6)
	ld %r7, 720(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 720(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 672(%r6)
	addc %r7, %r7, %r4
	std %r7, 672(%r6)
	ld %r7, 680(%r6)
	adde %r7, %r7, %r8
	std %r7, 680(%r6)
	ld %r7, 688(%r6)
	adde %r7, %r7, %r8
	std %r7, 688(%r6)
	ld %r7, 696(%r6)
	adde %r7, %r7, %r5
	std %r7, 696(%r6)
	ld %r7, 704(%r6)
	adde %r7, %r7, %r8
	std %r7, 704(%r6)
	ld %r7, 712(%r6)
	adde %r7, %r7, %r8
	std %r7, 712(%r6)
	ld %r7, 720(%r6)
	adde %r7, %r7, %r8
	std %r7, 720(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 672(%r6)
	addc %r7, %r7, %r4
	std %r7, 672(%r6)
	ld %r7, 680(%r6)
	adde %r7, %r7, %r8
	std %r7, 680(%r6)
	ld %r7, 688(%r6)
	adde %r7, %r7, %r8
	std %r7, 688(%r6)
	ld %r7, 696(%r6)
	adde %r7, %r7, %r5
	std %r7, 696(%r6)
	ld %r7, 704(%r6)
	adde %r7, %r7, %r8
	std %r7, 704(%r6)
	ld %r7, 712(%r6)
	adde %r7, %r7, %r8
	std %r7, 712(%r6)
	ld %r7, 720(%r6)
	adde %r7, %r7, %r8
	std %r7, 720(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
25:
	ld %r4, 392(%r9)
	li %r8, 0
	ld %r5, 336(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 344(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 352(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 360(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 368(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 376(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 384(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 25b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 728(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 736(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 744(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 752(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 760(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 768(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 776(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 728(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 776(%r6)
	addze %r4, %r4
	ld %r7, 752(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 776(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 728(%r6)
	addc %r7, %r7, %r4
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	adde %r7, %r7, %r8
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	adde %r7, %r7, %r8
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	adde %r7, %r7, %r5
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	adde %r7, %r7, %r8
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	adde %r7, %r7, %r8
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	adde %r7, %r7, %r8
	std %r7, 776(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 728(%r6)
	addc %r7, %r7, %r4
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	adde %r7, %r7, %r8
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	adde %r7, %r7, %r8
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	adde %r7, %r7, %r5
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	adde %r7, %r7, %r8
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	adde %r7, %r7, %r8
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	adde %r7, %r7, %r8
	std %r7, 776(%r6)
	ld %r7, 672(%r6)
	ld %r8, 728(%r6)
	addc %r7, %r7, %r8
	std %r7, 168(%r6)
	ld %r7, 680(%r6)
	ld %r8, 736(%r6)
	adde %r7, %r7, %r8
	std %r7, 176(%r6)
	ld %r7, 688(%r6)
	ld %r8, 744(%r6)
	adde %r7, %r7, %r8
	std %r7, 184(%r6)
	ld %r7, 696(%r6)
	ld %r8, 752(%r6)
	adde %r7, %r7, %r8
	std %r7, 192(%r6)
	ld %r7, 704(%r6)
	ld %r8, 760(%r6)
	adde %r7, %r7, %r8
	std %r7, 200(%r6)
	ld %r7, 712(%r6)
	ld %r8, 768(%r6)
	adde %r7, %r7, %r8
	std %r7, 208(%r6)
	ld %r7, 720(%r6)
	ld %r8, 776(%r6)
	adde %r7, %r7, %r8
	std %r7, 216(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 168(%r6)
	addc %r7, %r7, %r4
	std %r7, 168(%r6)
	ld %r7, 176(%r6)
	adde %r7, %r7, %r8
	std %r7, 176(%r6)
	ld %r7, 184(%r6)
	adde %r7, %r7, %r8
	std %r7, 184(%r6)
	ld %r7, 192(%r6)
	adde %r7, %r7, %r5
	std %r7, 192(%r6)
	ld %r7, 200(%r6)
	adde %r7, %r7, %r8
	std %r7, 200(%r6)
	ld %r7, 208(%r6)
	adde %r7, %r7, %r8
	std %r7, 208(%r6)
	ld %r7, 216(%r6)
	adde %r7, %r7, %r8
	std %r7, 216(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 168(%r6)
	addc %r7, %r7, %r4
	std %r7, 168(%r6)
	ld %r7, 176(%r6)
	adde %r7, %r7, %r8
	std %r7, 176(%r6)
	ld %r7, 184(%r6)
	adde %r7, %r7, %r8
	std %r7, 184(%r6)
	ld %r7, 192(%r6)
	adde %r7, %r7, %r5
	std %r7, 192(%r6)
	ld %r7, 200(%r6)
	adde %r7, %r7, %r8
	std %r7, 200(%r6)
	ld %r7, 208(%r6)
	adde %r7, %r7, %r8
	std %r7, 208(%r6)
	ld %r7, 216(%r6)
	adde %r7, %r7, %r8
	std %r7, 216(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
26:
	ld %r4, 168(%r9)
	li %r8, 0
	ld %r5, 168(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 176(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 184(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 192(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 200(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 208(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 216(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 26b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 168(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 176(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 184(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 192(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 200(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 208(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 216(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 168(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 168(%r6)
	ld %r7, 176(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 176(%r6)
	ld %r7, 184(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 184(%r6)
	ld %r7, 192(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 192(%r6)
	ld %r7, 200(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 200(%r6)
	ld %r7, 208(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 208(%r6)
	ld %r7, 216(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 216(%r6)
	addze %r4, %r4
	ld %r7, 192(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 192(%r6)
	ld %r7, 200(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 200(%r6)
	ld %r7, 208(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 208(%r6)
	ld %r7, 216(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 216(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 168(%r6)
	addc %r7, %r7, %r4
	std %r7, 168(%r6)
	ld %r7, 176(%r6)
	adde %r7, %r7, %r8
	std %r7, 176(%r6)
	ld %r7, 184(%r6)
	adde %r7, %r7, %r8
	std %r7, 184(%r6)
	ld %r7, 192(%r6)
	adde %r7, %r7, %r5
	std %r7, 192(%r6)
	ld %r7, 200(%r6)
	adde %r7, %r7, %r8
	std %r7, 200(%r6)
	ld %r7, 208(%r6)
	adde %r7, %r7, %r8
	std %r7, 208(%r6)
	ld %r7, 216(%r6)
	adde %r7, %r7, %r8
	std %r7, 216(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 168(%r6)
	addc %r7, %r7, %r4
	std %r7, 168(%r6)
	ld %r7, 176(%r6)
	adde %r7, %r7, %r8
	std %r7, 176(%r6)
	ld %r7, 184(%r6)
	adde %r7, %r7, %r8
	std %r7, 184(%r6)
	ld %r7, 192(%r6)
	adde %r7, %r7, %r5
	std %r7, 192(%r6)
	ld %r7, 200(%r6)
	adde %r7, %r7, %r8
	std %r7, 200(%r6)
	ld %r7, 208(%r6)
	adde %r7, %r7, %r8
	std %r7, 208(%r6)
	ld %r7, 216(%r6)
	adde %r7, %r7, %r8
	std %r7, 216(%r6)
	ld %r7, 672(%r6)
	ld %r8, 728(%r6)
	subfc %r7, %r8, %r7
	std %r7, 224(%r6)
	ld %r7, 680(%r6)
	ld %r8, 736(%r6)
	subfe %r7, %r8, %r7
	std %r7, 232(%r6)
	ld %r7, 688(%r6)
	ld %r8, 744(%r6)
	subfe %r7, %r8, %r7
	std %r7, 240(%r6)
	ld %r7, 696(%r6)
	ld %r8, 752(%r6)
	subfe %r7, %r8, %r7
	std %r7, 248(%r6)
	ld %r7, 704(%r6)
	ld %r8, 760(%r6)
	subfe %r7, %r8, %r7
	std %r7, 256(%r6)
	ld %r7, 712(%r6)
	ld %r8, 768(%r6)
	subfe %r7, %r8, %r7
	std %r7, 264(%r6)
	ld %r7, 720(%r6)
	ld %r8, 776(%r6)
	subfe %r7, %r8, %r7
	std %r7, 272(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 224(%r6)
	subfc %r7, %r4, %r7
	std %r7, 224(%r6)
	ld %r7, 232(%r6)
	subfe %r7, %r8, %r7
	std %r7, 232(%r6)
	ld %r7, 240(%r6)
	subfe %r7, %r8, %r7
	std %r7, 240(%r6)
	ld %r7, 248(%r6)
	subfe %r7, %r5, %r7
	std %r7, 248(%r6)
	ld %r7, 256(%r6)
	subfe %r7, %r8, %r7
	std %r7, 256(%r6)
	ld %r7, 264(%r6)
	subfe %r7, %r8, %r7
	std %r7, 264(%r6)
	ld %r7, 272(%r6)
	subfe %r7, %r8, %r7
	std %r7, 272(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 224(%r6)
	subfc %r7, %r4, %r7
	std %r7, 224(%r6)
	ld %r7, 232(%r6)
	subfe %r7, %r8, %r7
	std %r7, 232(%r6)
	ld %r7, 240(%r6)
	subfe %r7, %r8, %r7
	std %r7, 240(%r6)
	ld %r7, 248(%r6)
	subfe %r7, %r5, %r7
	std %r7, 248(%r6)
	ld %r7, 256(%r6)
	subfe %r7, %r8, %r7
	std %r7, 256(%r6)
	ld %r7, 264(%r6)
	subfe %r7, %r8, %r7
	std %r7, 264(%r6)
	ld %r7, 272(%r6)
	subfe %r7, %r8, %r7
	std %r7, 272(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
27:
	ld %r4, 224(%r9)
	li %r8, 0
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 27b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 224(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 232(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 240(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 248(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 256(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 264(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 272(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 224(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 224(%r6)
	ld %r7, 232(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 232(%r6)
	ld %r7, 240(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 240(%r6)
	ld %r7, 248(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 248(%r6)
	ld %r7, 256(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 256(%r6)
	ld %r7, 264(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 264(%r6)
	ld %r7, 272(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 272(%r6)
	addze %r4, %r4
	ld %r7, 248(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 248(%r6)
	ld %r7, 256(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 256(%r6)
	ld %r7, 264(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 264(%r6)
	ld %r7, 272(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 272(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 224(%r6)
	addc %r7, %r7, %r4
	std %r7, 224(%r6)
	ld %r7, 232(%r6)
	adde %r7, %r7, %r8
	std %r7, 232(%r6)
	ld %r7, 240(%r6)
	adde %r7, %r7, %r8
	std %r7, 240(%r6)
	ld %r7, 248(%r6)
	adde %r7, %r7, %r5
	std %r7, 248(%r6)
	ld %r7, 256(%r6)
	adde %r7, %r7, %r8
	std %r7, 256(%r6)
	ld %r7, 264(%r6)
	adde %r7, %r7, %r8
	std %r7, 264(%r6)
	ld %r7, 272(%r6)
	adde %r7, %r7, %r8
	std %r7, 272(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 224(%r6)
	addc %r7, %r7, %r4
	std %r7, 224(%r6)
	ld %r7, 232(%r6)
	adde %r7, %r7, %r8
	std %r7, 232(%r6)
	ld %r7, 240(%r6)
	adde %r7, %r7, %r8
	std %r7, 240(%r6)
	ld %r7, 248(%r6)
	adde %r7, %r7, %r5
	std %r7, 248(%r6)
	ld %r7, 256(%r6)
	adde %r7, %r7, %r8
	std %r7, 256(%r6)
	ld %r7, 264(%r6)
	adde %r7, %r7, %r8
	std %r7, 264(%r6)
	ld %r7, 272(%r6)
	adde %r7, %r7, %r8
	std %r7, 272(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
28:
	ld %r4, 0(%r9)
	li %r8, 0
	ld %r5, 224(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 232(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 240(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 248(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 256(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 264(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 272(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 28b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 224(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 232(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 240(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 248(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 256(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 264(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 272(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 224(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 224(%r6)
	ld %r7, 232(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 232(%r6)
	ld %r7, 240(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 240(%r6)
	ld %r7, 248(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 248(%r6)
	ld %r7, 256(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 256(%r6)
	ld %r7, 264(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 264(%r6)
	ld %r7, 272(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 272(%r6)
	addze %r4, %r4
	ld %r7, 248(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 248(%r6)
	ld %r7, 256(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 256(%r6)
	ld %r7, 264(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 264(%r6)
	ld %r7, 272(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 272(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 224(%r6)
	addc %r7, %r7, %r4
	std %r7, 224(%r6)
	ld %r7, 232(%r6)
	adde %r7, %r7, %r8
	std %r7, 232(%r6)
	ld %r7, 240(%r6)
	adde %r7, %r7, %r8
	std %r7, 240(%r6)
	ld %r7, 248(%r6)
	adde %r7, %r7, %r5
	std %r7, 248(%r6)
	ld %r7, 256(%r6)
	adde %r7, %r7, %r8
	std %r7, 256(%r6)
	ld %r7, 264(%r6)
	adde %r7, %r7, %r8
	std %r7, 264(%r6)
	ld %r7, 272(%r6)
	adde %r7, %r7, %r8
	std %r7, 272(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 224(%r6)
	addc %r7, %r7, %r4
	std %r7, 224(%r6)
	ld %r7, 232(%r6)
	adde %r7, %r7, %r8
	std %r7, 232(%r6)
	ld %r7, 240(%r6)
	adde %r7, %r7, %r8
	std %r7, 240(%r6)
	ld %r7, 248(%r6)
	adde %r7, %r7, %r5
	std %r7, 248(%r6)
	ld %r7, 256(%r6)
	adde %r7, %r7, %r8
	std %r7, 256(%r6)
	ld %r7, 264(%r6)
	adde %r7, %r7, %r8
	std %r7, 264(%r6)
	ld %r7, 272(%r6)
	adde %r7, %r7, %r8
	std %r7, 272(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
29:
	ld %r4, 504(%r9)
	li %r8, 0
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 608(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 29b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 56(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 64(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 72(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 80(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 88(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 96(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 104(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 56(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 56(%r6)
	ld %r7, 64(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 64(%r6)
	ld %r7, 72(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 72(%r6)
	ld %r7, 80(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 80(%r6)
	ld %r7, 88(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 88(%r6)
	ld %r7, 96(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 96(%r6)
	ld %r7, 104(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 104(%r6)
	addze %r4, %r4
	ld %r7, 80(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 80(%r6)
	ld %r7, 88(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 88(%r6)
	ld %r7, 96(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 96(%r6)
	ld %r7, 104(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 104(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 56(%r6)
	addc %r7, %r7, %r4
	std %r7, 56(%r6)
	ld %r7, 64(%r6)
	adde %r7, %r7, %r8
	std %r7, 64(%r6)
	ld %r7, 72(%r6)
	adde %r7, %r7, %r8
	std %r7, 72(%r6)
	ld %r7, 80(%r6)
	adde %r7, %r7, %r5
	std %r7, 80(%r6)
	ld %r7, 88(%r6)
	adde %r7, %r7, %r8
	std %r7, 88(%r6)
	ld %r7, 96(%r6)
	adde %r7, %r7, %r8
	std %r7, 96(%r6)
	ld %r7, 104(%r6)
	adde %r7, %r7, %r8
	std %r7, 104(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 56(%r6)
	addc %r7, %r7, %r4
	std %r7, 56(%r6)
	ld %r7, 64(%r6)
	adde %r7, %r7, %r8
	std %r7, 64(%r6)
	ld %r7, 72(%r6)
	adde %r7, %r7, %r8
	std %r7, 72(%r6)
	ld %r7, 80(%r6)
	adde %r7, %r7, %r5
	std %r7, 80(%r6)
	ld %r7, 88(%r6)
	adde %r7, %r7, %r8
	std %r7, 88(%r6)
	ld %r7, 96(%r6)
	adde %r7, %r7, %r8
	std %r7, 96(%r6)
	ld %r7, 104(%r6)
	adde %r7, %r7, %r8
	std %r7, 104(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
210:
	ld %r4, 784(%r9)
	li %r8, 0
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 640(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 648(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 656(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 664(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 210b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 112(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 120(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 128(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 136(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 144(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 152(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 160(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 112(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 112(%r6)
	ld %r7, 120(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 120(%r6)
	ld %r7, 128(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 128(%r6)
	ld %r7, 136(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 136(%r6)
	ld %r7, 144(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 144(%r6)
	ld %r7, 152(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 152(%r6)
	ld %r7, 160(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 160(%r6)
	addze %r4, %r4
	ld %r7, 136(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 136(%r6)
	ld %r7, 144(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 144(%r6)
	ld %r7, 152(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 152(%r6)
	ld %r7, 160(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 160(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 112(%r6)
	addc %r7, %r7, %r4
	std %r7, 112(%r6)
	ld %r7, 120(%r6)
	adde %r7, %r7, %r8
	std %r7, 120(%r6)
	ld %r7, 128(%r6)
	adde %r7, %r7, %r8
	std %r7, 128(%r6)
	ld %r7, 136(%r6)
	adde %r7, %r7, %r5
	std %r7, 136(%r6)
	ld %r7, 144(%r6)
	adde %r7, %r7, %r8
	std %r7, 144(%r6)
	ld %r7, 152(%r6)
	adde %r7, %r7, %r8
	std %r7, 152(%r6)
	ld %r7, 160(%r6)
	adde %r7, %r7, %r8
	std %r7, 160(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 112(%r6)
	addc %r7, %r7, %r4
	std %r7, 112(%r6)
	ld %r7, 120(%r6)
	adde %r7, %r7, %r8
	std %r7, 120(%r6)
	ld %r7, 128(%r6)
	adde %r7, %r7, %r8
	std %r7, 128(%r6)
	ld %r7, 136(%r6)
	adde %r7, %r7, %r5
	std %r7, 136(%r6)
	ld %r7, 144(%r6)
	adde %r7, %r7, %r8
	std %r7, 144(%r6)
	ld %r7, 152(%r6)
	adde %r7, %r7, %r8
	std %r7, 152(%r6)
	ld %r7, 160(%r6)
	adde %r7, %r7, %r8
	std %r7, 160(%r6)
	ld %r7, 504(%r6)
	ld %r8, 112(%r6)
	addc %r7, %r7, %r8
	std %r7, 112(%r6)
	ld %r7, 512(%r6)
	ld %r8, 120(%r6)
	adde %r7, %r7, %r8
	std %r7, 120(%r6)
	ld %r7, 520(%r6)
	ld %r8, 128(%r6)
	adde %r7, %r7, %r8
	std %r7, 128(%r6)
	ld %r7, 528(%r6)
	ld %r8, 136(%r6)
	adde %r7, %r7, %r8
	std %r7, 136(%r6)
	ld %r7, 536(%r6)
	ld %r8, 144(%r6)
	adde %r7, %r7, %r8
	std %r7, 144(%r6)
	ld %r7, 544(%r6)
	ld %r8, 152(%r6)
	adde %r7, %r7, %r8
	std %r7, 152(%r6)
	ld %r7, 552(%r6)
	ld %r8, 160(%r6)
	adde %r7, %r7, %r8
	std %r7, 160(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 112(%r6)
	addc %r7, %r7, %r4
	std %r7, 112(%r6)
	ld %r7, 120(%r6)
	adde %r7, %r7, %r8
	std %r7, 120(%r6)
	ld %r7, 128(%r6)
	adde %r7, %r7, %r8
	std %r7, 128(%r6)
	ld %r7, 136(%r6)
	adde %r7, %r7, %r5
	std %r7, 136(%r6)
	ld %r7, 144(%r6)
	adde %r7, %r7, %r8
	std %r7, 144(%r6)
	ld %r7, 152(%r6)
	adde %r7, %r7, %r8
	std %r7, 152(%r6)
	ld %r7, 160(%r6)
	adde %r7, %r7, %r8
	std %r7, 160(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 112(%r6)
	addc %r7, %r7, %r4
	std %r7, 112(%r6)
	ld %r7, 120(%r6)
	adde %r7, %r7, %r8
	std %r7, 120(%r6)
	ld %r7, 128(%r6)
	adde %r7, %r7, %r8
	std %r7, 128(%r6)
	ld %r7, 136(%r6)
	adde %r7, %r7, %r5
	std %r7, 136(%r6)
	ld %r7, 144(%r6)
	adde %r7, %r7, %r8
	std %r7, 144(%r6)
	ld %r7, 152(%r6)
	adde %r7, %r7, %r8
	std %r7, 152(%r6)
	ld %r7, 160(%r6)
	adde %r7, %r7, %r8
	std %r7, 160(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
211:
	ld %r4, 616(%r9)
	li %r8, 0
	ld %r5, 112(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 120(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 128(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 136(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 144(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 152(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 211b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 112(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 120(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 128(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 136(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 144(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 152(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 160(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 112(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 112(%r6)
	ld %r7, 120(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 120(%r6)
	ld %r7, 128(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 128(%r6)
	ld %r7, 136(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 136(%r6)
	ld %r7, 144(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 144(%r6)
	ld %r7, 152(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 152(%r6)
	ld %r7, 160(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 160(%r6)
	addze %r4, %r4
	ld %r7, 136(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 136(%r6)
	ld %r7, 144(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 144(%r6)
	ld %r7, 152(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 152(%r6)
	ld %r7, 160(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 160(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 112(%r6)
	addc %r7, %r7, %r4
	std %r7, 112(%r6)
	ld %r7, 120(%r6)
	adde %r7, %r7, %r8
	std %r7, 120(%r6)
	ld %r7, 128(%r6)
	adde %r7, %r7, %r8
	std %r7, 128(%r6)
	ld %r7, 136(%r6)
	adde %r7, %r7, %r5
	std %r7, 136(%r6)
	ld %r7, 144(%r6)
	adde %r7, %r7, %r8
	std %r7, 144(%r6)
	ld %r7, 152(%r6)
	adde %r7, %r7, %r8
	std %r7, 152(%r6)
	ld %r7, 160(%r6)
	adde %r7, %r7, %r8
	std %r7, 160(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 112(%r6)
	addc %r7, %r7, %r4
	std %r7, 112(%r6)
	ld %r7, 120(%r6)
	adde %r7, %r7, %r8
	std %r7, 120(%r6)
	ld %r7, 128(%r6)
	adde %r7, %r7, %r8
	std %r7, 128(%r6)
	ld %r7, 136(%r6)
	adde %r7, %r7, %r5
	std %r7, 136(%r6)
	ld %r7, 144(%r6)
	adde %r7, %r7, %r8
	std %r7, 144(%r6)
	ld %r7, 152(%r6)
	adde %r7, %r7, %r8
	std %r7, 152(%r6)
	ld %r7, 160(%r6)
	adde %r7, %r7, %r8
	std %r7, 160(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 21b
	li %r11, 0
	subf %r11, %r0, %r11
	lwz %r5, 56(%r6)
	lwz %r7, 168(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 56(%r6)
	stw %r7, 168(%r6)
	lwz %r5, 60(%r6)
	lwz %r7, 172(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 60(%r6)
	stw %r7, 172(%r6)
	lwz %r5, 64(%r6)
	lwz %r7, 176(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 64(%r6)
	stw %r7, 176(%r6)
	lwz %r5, 68(%r6)
	lwz %r7, 180(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 68(%r6)
	stw %r7, 180(%r6)
	lwz %r5, 72(%r6)
	lwz %r7, 184(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 72(%r6)
	stw %r7, 184(%r6)
	lwz %r5, 76(%r6)
	lwz %r7, 188(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 76(%r6)
	stw %r7, 188(%r6)
	lwz %r5, 80(%r6)
	lwz %r7, 192(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 80(%r6)
	stw %r7, 192(%r6)
	lwz %r5, 84(%r6)
	lwz %r7, 196(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 84(%r6)
	stw %r7, 196(%r6)
	lwz %r5, 88(%r6)
	lwz %r7, 200(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 88(%r6)
	stw %r7, 200(%r6)
	lwz %r5, 92(%r6)
	lwz %r7, 204(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 92(%r6)
	stw %r7, 204(%r6)
	lwz %r5, 96(%r6)
	lwz %r7, 208(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 96(%r6)
	stw %r7, 208(%r6)
	lwz %r5, 100(%r6)
	lwz %r7, 212(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 100(%r6)
	stw %r7, 212(%r6)
	lwz %r5, 104(%r6)
	lwz %r7, 216(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 104(%r6)
	stw %r7, 216(%r6)
	lwz %r5, 108(%r6)
	lwz %r7, 220(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 108(%r6)
	stw %r7, 220(%r6)
	lwz %r5, 112(%r6)
	lwz %r7, 224(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 112(%r6)
	stw %r7, 224(%r6)
	lwz %r5, 116(%r6)
	lwz %r7, 228(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 116(%r6)
	stw %r7, 228(%r6)
	lwz %r5, 120(%r6)
	lwz %r7, 232(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 120(%r6)
	stw %r7, 232(%r6)
	lwz %r5, 124(%r6)
	lwz %r7, 236(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 124(%r6)
	stw %r7, 236(%r6)
	lwz %r5, 128(%r6)
	lwz %r7, 240(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 128(%r6)
	stw %r7, 240(%r6)
	lwz %r5, 132(%r6)
	lwz %r7, 244(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 132(%r6)
	stw %r7, 244(%r6)
	lwz %r5, 136(%r6)
	lwz %r7, 248(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 136(%r6)
	stw %r7, 248(%r6)
	lwz %r5, 140(%r6)
	lwz %r7, 252(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 140(%r6)
	stw %r7, 252(%r6)
	lwz %r5, 144(%r6)
	lwz %r7, 256(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 144(%r6)
	stw %r7, 256(%r6)
	lwz %r5, 148(%r6)
	lwz %r7, 260(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 148(%r6)
	stw %r7, 260(%r6)
	lwz %r5, 152(%r6)
	lwz %r7, 264(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 152(%r6)
	stw %r7, 264(%r6)
	lwz %r5, 156(%r6)
	lwz %r7, 268(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 156(%r6)
	stw %r7, 268(%r6)
	lwz %r5, 160(%r6)
	lwz %r7, 272(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 160(%r6)
	stw %r7, 272(%r6)
	lwz %r5, 164(%r6)
	lwz %r7, 276(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	stw %r5, 164(%r6)
	stw %r7, 276(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
212:
	ld %r4, 112(%r9)
	li %r8, 0
	ld %r5, 112(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 120(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 128(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 136(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 144(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 152(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 212b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 280(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 288(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 296(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 304(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 312(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 320(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 328(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 280(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 280(%r6)
	ld %r7, 288(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 288(%r6)
	ld %r7, 296(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 296(%r6)
	ld %r7, 304(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 304(%r6)
	ld %r7, 312(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 312(%r6)
	ld %r7, 320(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 320(%r6)
	ld %r7, 328(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 328(%r6)
	addze %r4, %r4
	ld %r7, 304(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 304(%r6)
	ld %r7, 312(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 312(%r6)
	ld %r7, 320(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 320(%r6)
	ld %r7, 328(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 328(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 280(%r6)
	addc %r7, %r7, %r4
	std %r7, 280(%r6)
	ld %r7, 288(%r6)
	adde %r7, %r7, %r8
	std %r7, 288(%r6)
	ld %r7, 296(%r6)
	adde %r7, %r7, %r8
	std %r7, 296(%r6)
	ld %r7, 304(%r6)
	adde %r7, %r7, %r5
	std %r7, 304(%r6)
	ld %r7, 312(%r6)
	adde %r7, %r7, %r8
	std %r7, 312(%r6)
	ld %r7, 320(%r6)
	adde %r7, %r7, %r8
	std %r7, 320(%r6)
	ld %r7, 328(%r6)
	adde %r7, %r7, %r8
	std %r7, 328(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 280(%r6)
	addc %r7, %r7, %r4
	std %r7, 280(%r6)
	ld %r7, 288(%r6)
	adde %r7, %r7, %r8
	std %r7, 288(%r6)
	ld %r7, 296(%r6)
	adde %r7, %r7, %r8
	std %r7, 296(%r6)
	ld %r7, 304(%r6)
	adde %r7, %r7, %r5
	std %r7, 304(%r6)
	ld %r7, 312(%r6)
	adde %r7, %r7, %r8
	std %r7, 312(%r6)
	ld %r7, 320(%r6)
	adde %r7, %r7, %r8
	std %r7, 320(%r6)
	ld %r7, 328(%r6)
	adde %r7, %r7, %r8
	std %r7, 328(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
213:
	ld %r4, 280(%r9)
	li %r8, 0
	ld %r5, 112(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 120(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 128(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 136(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 144(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 152(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 213b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 280(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 288(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 296(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 304(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 312(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 320(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 328(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 280(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 280(%r6)
	ld %r7, 288(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 288(%r6)
	ld %r7, 296(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 296(%r6)
	ld %r7, 304(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 304(%r6)
	ld %r7, 312(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 312(%r6)
	ld %r7, 320(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 320(%r6)
	ld %r7, 328(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 328(%r6)
	addze %r4, %r4
	ld %r7, 304(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 304(%r6)
	ld %r7, 312(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 312(%r6)
	ld %r7, 320(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 320(%r6)
	ld %r7, 328(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 328(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 280(%r6)
	addc %r7, %r7, %r4
	std %r7, 280(%r6)
	ld %r7, 288(%r6)
	adde %r7, %r7, %r8
	std %r7, 288(%r6)
	ld %r7, 296(%r6)
	adde %r7, %r7, %r8
	std %r7, 296(%r6)
	ld %r7, 304(%r6)
	adde %r7, %r7, %r5
	std %r7, 304(%r6)
	ld %r7, 312(%r6)
	adde %r7, %r7, %r8
	std %r7, 312(%r6)
	ld %r7, 320(%r6)
	adde %r7, %r7, %r8
	std %r7, 320(%r6)
	ld %r7, 328(%r6)
	adde %r7, %r7, %r8
	std %r7, 328(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 280(%r6)
	addc %r7, %r7, %r4
	std %r7, 280(%r6)
	ld %r7, 288(%r6)
	adde %r7, %r7, %r8
	std %r7, 288(%r6)
	ld %r7, 296(%r6)
	adde %r7, %r7, %r8
	std %r7, 296(%r6)
	ld %r7, 304(%r6)
	adde %r7, %r7, %r5
	std %r7, 304(%r6)
	ld %r7, 312(%r6)
	adde %r7, %r7, %r8
	std %r7, 312(%r6)
	ld %r7, 320(%r6)
	adde %r7, %r7, %r8
	std %r7, 320(%r6)
	ld %r7, 328(%r6)
	adde %r7, %r7, %r8
	std %r7, 328(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
214:
	ld %r4, 280(%r9)
	li %r8, 0
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 288(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 296(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 304(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 312(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 320(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 328(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 214b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 336(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 344(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 352(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 360(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 368(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 376(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 384(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 336(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 336(%r6)
	ld %r7, 344(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 344(%r6)
	ld %r7, 352(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 352(%r6)
	ld %r7, 360(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 360(%r6)
	ld %r7, 368(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 368(%r6)
	ld %r7, 376(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 376(%r6)
	ld %r7, 384(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 384(%r6)
	addze %r4, %r4
	ld %r7, 360(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 360(%r6)
	ld %r7, 368(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 368(%r6)
	ld %r7, 376(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 376(%r6)
	ld %r7, 384(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 384(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 336(%r6)
	addc %r7, %r7, %r4
	std %r7, 336(%r6)
	ld %r7, 344(%r6)
	adde %r7, %r7, %r8
	std %r7, 344(%r6)
	ld %r7, 352(%r6)
	adde %r7, %r7, %r8
	std %r7, 352(%r6)
	ld %r7, 360(%r6)
	adde %r7, %r7, %r5
	std %r7, 360(%r6)
	ld %r7, 368(%r6)
	adde %r7, %r7, %r8
	std %r7, 368(%r6)
	ld %r7, 376(%r6)
	adde %r7, %r7, %r8
	std %r7, 376(%r6)
	ld %r7, 384(%r6)
	adde %r7, %r7, %r8
	std %r7, 384(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 336(%r6)
	addc %r7, %r7, %r4
	std %r7, 336(%r6)
	ld %r7, 344(%r6)
	adde %r7, %r7, %r8
	std %r7, 344(%r6)
	ld %r7, 352(%r6)
	adde %r7, %r7, %r8
	std %r7, 352(%r6)
	ld %r7, 360(%r6)
	adde %r7, %r7, %r5
	std %r7, 360(%r6)
	ld %r7, 368(%r6)
	adde %r7, %r7, %r8
	std %r7, 368(%r6)
	ld %r7, 376(%r6)
	adde %r7, %r7, %r8
	std %r7, 376(%r6)
	ld %r7, 384(%r6)
	adde %r7, %r7, %r8
	std %r7, 384(%r6)
	li %r12, 1
215:
	addi %r12, %r12, -1
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
216:
	ld %r4, 336(%r9)
	li %r8, 0
	ld %r5, 336(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 344(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 352(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 360(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 368(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 376(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 384(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 216b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 336(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 344(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 352(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 360(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 368(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 376(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 384(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 336(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 336(%r6)
	ld %r7, 344(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 344(%r6)
	ld %r7, 352(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 352(%r6)
	ld %r7, 360(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 360(%r6)
	ld %r7, 368(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 368(%r6)
	ld %r7, 376(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 376(%r6)
	ld %r7, 384(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 384(%r6)
	addze %r4, %r4
	ld %r7, 360(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 360(%r6)
	ld %r7, 368(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 368(%r6)
	ld %r7, 376(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 376(%r6)
	ld %r7, 384(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 384(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 336(%r6)
	addc %r7, %r7, %r4
	std %r7, 336(%r6)
	ld %r7, 344(%r6)
	adde %r7, %r7, %r8
	std %r7, 344(%r6)
	ld %r7, 352(%r6)
	adde %r7, %r7, %r8
	std %r7, 352(%r6)
	ld %r7, 360(%r6)
	adde %r7, %r7, %r5
	std %r7, 360(%r6)
	ld %r7, 368(%r6)
	adde %r7, %r7, %r8
	std %r7, 368(%r6)
	ld %r7, 376(%r6)
	adde %r7, %r7, %r8
	std %r7, 376(%r6)
	ld %r7, 384(%r6)
	adde %r7, %r7, %r8
	std %r7, 384(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 336(%r6)
	addc %r7, %r7, %r4
	std %r7, 336(%r6)
	ld %r7, 344(%r6)
	adde %r7, %r7, %r8
	std %r7, 344(%r6)
	ld %r7, 352(%r6)
	adde %r7, %r7, %r8
	std %r7, 352(%r6)
	ld %r7, 360(%r6)
	adde %r7, %r7, %r5
	std %r7, 360(%r6)
	ld %r7, 368(%r6)
	adde %r7, %r7, %r8
	std %r7, 368(%r6)
	ld %r7, 376(%r6)
	adde %r7, %r7, %r8
	std %r7, 376(%r6)
	ld %r7, 384(%r6)
	adde %r7, %r7, %r8
	std %r7, 384(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 215b
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
217:
	ld %r4, 336(%r9)
	li %r8, 0
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 288(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 296(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 304(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 312(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 320(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 328(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 217b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 336(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 344(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 352(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 360(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 368(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 376(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 384(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 336(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 336(%r6)
	ld %r7, 344(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 344(%r6)
	ld %r7, 352(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 352(%r6)
	ld %r7, 360(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 360(%r6)
	ld %r7, 368(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 368(%r6)
	ld %r7, 376(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 376(%r6)
	ld %r7, 384(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 384(%r6)
	addze %r4, %r4
	ld %r7, 360(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 360(%r6)
	ld %r7, 368(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 368(%r6)
	ld %r7, 376(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 376(%r6)
	ld %r7, 384(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 384(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 336(%r6)
	addc %r7, %r7, %r4
	std %r7, 336(%r6)
	ld %r7, 344(%r6)
	adde %r7, %r7, %r8
	std %r7, 344(%r6)
	ld %r7, 352(%r6)
	adde %r7, %r7, %r8
	std %r7, 352(%r6)
	ld %r7, 360(%r6)
	adde %r7, %r7, %r5
	std %r7, 360(%r6)
	ld %r7, 368(%r6)
	adde %r7, %r7, %r8
	std %r7, 368(%r6)
	ld %r7, 376(%r6)
	adde %r7, %r7, %r8
	std %r7, 376(%r6)
	ld %r7, 384(%r6)
	adde %r7, %r7, %r8
	std %r7, 384(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 336(%r6)
	addc %r7, %r7, %r4
	std %r7, 336(%r6)
	ld %r7, 344(%r6)
	adde %r7, %r7, %r8
	std %r7, 344(%r6)
	ld %r7, 352(%r6)
	adde %r7, %r7, %r8
	std %r7, 352(%r6)
	ld %r7, 360(%r6)
	adde %r7, %r7, %r5
	std %r7, 360(%r6)
	ld %r7, 368(%r6)
	adde %r7, %r7, %r8
	std %r7, 368(%r6)
	ld %r7, 376(%r6)
	adde %r7, %r7, %r8
	std %r7, 376(%r6)
	ld %r7, 384(%r6)
	adde %r7, %r7, %r8
	std %r7, 384(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
218:
	ld %r4, 336(%r9)
	li %r8, 0
	ld %r5, 336(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 344(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 352(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 360(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 368(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 376(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 384(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 218b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 392(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 400(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 408(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 416(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 392(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 392(%r6)
	ld %r7, 400(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 400(%r6)
	ld %r7, 408(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 408(%r6)
	ld %r7, 416(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
	addze %r4, %r4
	ld %r7, 416(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 392(%r6)
	addc %r7, %r7, %r4
	std %r7, 392(%r6)
	ld %r7, 400(%r6)
	adde %r7, %r7, %r8
	std %r7, 400(%r6)
	ld %r7, 408(%r6)
	adde %r7, %r7, %r8
	std %r7, 408(%r6)
	ld %r7, 416(%r6)
	adde %r7, %r7, %r5
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 392(%r6)
	addc %r7, %r7, %r4
	std %r7, 392(%r6)
	ld %r7, 400(%r6)
	adde %r7, %r7, %r8
	std %r7, 400(%r6)
	ld %r7, 408(%r6)
	adde %r7, %r7, %r8
	std %r7, 408(%r6)
	ld %r7, 416(%r6)
	adde %r7, %r7, %r5
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
	li %r12, 3
219:
	addi %r12, %r12, -1
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
220:
	ld %r4, 392(%r9)
	li %r8, 0
	ld %r5, 392(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 400(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 408(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 416(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 424(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 432(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 440(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 220b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 392(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 400(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 408(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 416(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 392(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 392(%r6)
	ld %r7, 400(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 400(%r6)
	ld %r7, 408(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 408(%r6)
	ld %r7, 416(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
	addze %r4, %r4
	ld %r7, 416(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 392(%r6)
	addc %r7, %r7, %r4
	std %r7, 392(%r6)
	ld %r7, 400(%r6)
	adde %r7, %r7, %r8
	std %r7, 400(%r6)
	ld %r7, 408(%r6)
	adde %r7, %r7, %r8
	std %r7, 408(%r6)
	ld %r7, 416(%r6)
	adde %r7, %r7, %r5
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 392(%r6)
	addc %r7, %r7, %r4
	std %r7, 392(%r6)
	ld %r7, 400(%r6)
	adde %r7, %r7, %r8
	std %r7, 400(%r6)
	ld %r7, 408(%r6)
	adde %r7, %r7, %r8
	std %r7, 408(%r6)
	ld %r7, 416(%r6)
	adde %r7, %r7, %r5
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 219b
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
221:
	ld %r4, 392(%r9)
	li %r8, 0
	ld %r5, 336(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 344(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 352(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 360(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 368(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 376(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 384(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 221b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 392(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 400(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 408(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 416(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 392(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 392(%r6)
	ld %r7, 400(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 400(%r6)
	ld %r7, 408(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 408(%r6)
	ld %r7, 416(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
	addze %r4, %r4
	ld %r7, 416(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 392(%r6)
	addc %r7, %r7, %r4
	std %r7, 392(%r6)
	ld %r7, 400(%r6)
	adde %r7, %r7, %r8
	std %r7, 400(%r6)
	ld %r7, 408(%r6)
	adde %r7, %r7, %r8
	std %r7, 408(%r6)
	ld %r7, 416(%r6)
	adde %r7, %r7, %r5
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 392(%r6)
	addc %r7, %r7, %r4
	std %r7, 392(%r6)
	ld %r7, 400(%r6)
	adde %r7, %r7, %r8
	std %r7, 400(%r6)
	ld %r7, 408(%r6)
	adde %r7, %r7, %r8
	std %r7, 408(%r6)
	ld %r7, 416(%r6)
	adde %r7, %r7, %r5
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	adde %r7, %r7, %r8
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	adde %r7, %r7, %r8
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	adde %r7, %r7, %r8
	std %r7, 440(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
222:
	ld %r4, 392(%r9)
	li %r8, 0
	ld %r5, 392(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 400(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 408(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 416(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 424(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 432(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 440(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 222b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 448(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 456(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 464(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 472(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 480(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 488(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 496(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 448(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 448(%r6)
	ld %r7, 456(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 456(%r6)
	ld %r7, 464(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 464(%r6)
	ld %r7, 472(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 496(%r6)
	addze %r4, %r4
	ld %r7, 472(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 496(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 448(%r6)
	addc %r7, %r7, %r4
	std %r7, 448(%r6)
	ld %r7, 456(%r6)
	adde %r7, %r7, %r8
	std %r7, 456(%r6)
	ld %r7, 464(%r6)
	adde %r7, %r7, %r8
	std %r7, 464(%r6)
	ld %r7, 472(%r6)
	adde %r7, %r7, %r5
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	adde %r7, %r7, %r8
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	adde %r7, %r7, %r8
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	adde %r7, %r7, %r8
	std %r7, 496(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 448(%r6)
	addc %r7, %r7, %r4
	std %r7, 448(%r6)
	ld %r7, 456(%r6)
	adde %r7, %r7, %r8
	std %r7, 456(%r6)
	ld %r7, 464(%r6)
	adde %r7, %r7, %r8
	std %r7, 464(%r6)
	ld %r7, 472(%r6)
	adde %r7, %r7, %r5
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	adde %r7, %r7, %r8
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	adde %r7, %r7, %r8
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	adde %r7, %r7, %r8
	std %r7, 496(%r6)
	li %r12, 7
223:
	addi %r12, %r12, -1
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
224:
	ld %r4, 448(%r9)
	li %r8, 0
	ld %r5, 448(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 456(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 464(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 472(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 224b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 448(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 456(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 464(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 472(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 480(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 488(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 496(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 448(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 448(%r6)
	ld %r7, 456(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 456(%r6)
	ld %r7, 464(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 464(%r6)
	ld %r7, 472(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 496(%r6)
	addze %r4, %r4
	ld %r7, 472(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 496(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 448(%r6)
	addc %r7, %r7, %r4
	std %r7, 448(%r6)
	ld %r7, 456(%r6)
	adde %r7, %r7, %r8
	std %r7, 456(%r6)
	ld %r7, 464(%r6)
	adde %r7, %r7, %r8
	std %r7, 464(%r6)
	ld %r7, 472(%r6)
	adde %r7, %r7, %r5
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	adde %r7, %r7, %r8
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	adde %r7, %r7, %r8
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	adde %r7, %r7, %r8
	std %r7, 496(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 448(%r6)
	addc %r7, %r7, %r4
	std %r7, 448(%r6)
	ld %r7, 456(%r6)
	adde %r7, %r7, %r8
	std %r7, 456(%r6)
	ld %r7, 464(%r6)
	adde %r7, %r7, %r8
	std %r7, 464(%r6)
	ld %r7, 472(%r6)
	adde %r7, %r7, %r5
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	adde %r7, %r7, %r8
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	adde %r7, %r7, %r8
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	adde %r7, %r7, %r8
	std %r7, 496(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 223b
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
225:
	ld %r4, 448(%r9)
	li %r8, 0
	ld %r5, 392(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 400(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 408(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 416(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 424(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 432(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 440(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 225b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 448(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 456(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 464(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 472(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 480(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 488(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 496(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 448(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 448(%r6)
	ld %r7, 456(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 456(%r6)
	ld %r7, 464(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 464(%r6)
	ld %r7, 472(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 496(%r6)
	addze %r4, %r4
	ld %r7, 472(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 496(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 448(%r6)
	addc %r7, %r7, %r4
	std %r7, 448(%r6)
	ld %r7, 456(%r6)
	adde %r7, %r7, %r8
	std %r7, 456(%r6)
	ld %r7, 464(%r6)
	adde %r7, %r7, %r8
	std %r7, 464(%r6)
	ld %r7, 472(%r6)
	adde %r7, %r7, %r5
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	adde %r7, %r7, %r8
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	adde %r7, %r7, %r8
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	adde %r7, %r7, %r8
	std %r7, 496(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 448(%r6)
	addc %r7, %r7, %r4
	std %r7, 448(%r6)
	ld %r7, 456(%r6)
	adde %r7, %r7, %r8
	std %r7, 456(%r6)
	ld %r7, 464(%r6)
	adde %r7, %r7, %r8
	std %r7, 464(%r6)
	ld %r7, 472(%r6)
	adde %r7, %r7, %r5
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	adde %r7, %r7, %r8
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	adde %r7, %r7, %r8
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
	adde %r7, %r7, %r8
	std %r7, 496(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
226:
	ld %r4, 448(%r9)
	li %r8, 0
	ld %r5, 448(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 456(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 464(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 472(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 226b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 504(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 512(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 520(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 528(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 536(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 544(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 552(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 504(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 504(%r6)
	ld %r7, 512(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 512(%r6)
	ld %r7, 520(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 520(%r6)
	ld %r7, 528(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 528(%r6)
	ld %r7, 536(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 536(%r6)
	ld %r7, 544(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 544(%r6)
	ld %r7, 552(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 552(%r6)
	addze %r4, %r4
	ld %r7, 528(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 528(%r6)
	ld %r7, 536(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 536(%r6)
	ld %r7, 544(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 544(%r6)
	ld %r7, 552(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 552(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 504(%r6)
	addc %r7, %r7, %r4
	std %r7, 504(%r6)
	ld %r7, 512(%r6)
	adde %r7, %r7, %r8
	std %r7, 512(%r6)
	ld %r7, 520(%r6)
	adde %r7, %r7, %r8
	std %r7, 520(%r6)
	ld %r7, 528(%r6)
	adde %r7, %r7, %r5
	std %r7, 528(%r6)
	ld %r7, 536(%r6)
	adde %r7, %r7, %r8
	std %r7, 536(%r6)
	ld %r7, 544(%r6)
	adde %r7, %r7, %r8
	std %r7, 544(%r6)
	ld %r7, 552(%r6)
	adde %r7, %r7, %r8
	std %r7, 552(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 504(%r6)
	addc %r7, %r7, %r4
	std %r7, 504(%r6)
	ld %r7, 512(%r6)
	adde %r7, %r7, %r8
	std %r7, 512(%r6)
	ld %r7, 520(%r6)
	adde %r7, %r7, %r8
	std %r7, 520(%r6)
	ld %r7, 528(%r6)
	adde %r7, %r7, %r5
	std %r7, 528(%r6)
	ld %r7, 536(%r6)
	adde %r7, %r7, %r8
	std %r7, 536(%r6)
	ld %r7, 544(%r6)
	adde %r7, %r7, %r8
	std %r7, 544(%r6)
	ld %r7, 552(%r6)
	adde %r7, %r7, %r8
	std %r7, 552(%r6)
	li %r12, 15
227:
	addi %r12, %r12, -1
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
228:
	ld %r4, 504(%r9)
	li %r8, 0
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 228b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 504(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 512(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 520(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 528(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 536(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 544(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 552(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 504(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 504(%r6)
	ld %r7, 512(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 512(%r6)
	ld %r7, 520(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 520(%r6)
	ld %r7, 528(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 528(%r6)
	ld %r7, 536(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 536(%r6)
	ld %r7, 544(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 544(%r6)
	ld %r7, 552(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 552(%r6)
	addze %r4, %r4
	ld %r7, 528(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 528(%r6)
	ld %r7, 536(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 536(%r6)
	ld %r7, 544(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 544(%r6)
	ld %r7, 552(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 552(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 504(%r6)
	addc %r7, %r7, %r4
	std %r7, 504(%r6)
	ld %r7, 512(%r6)
	adde %r7, %r7, %r8
	std %r7, 512(%r6)
	ld %r7, 520(%r6)
	adde %r7, %r7, %r8
	std %r7, 520(%r6)
	ld %r7, 528(%r6)
	adde %r7, %r7, %r5
	std %r7, 528(%r6)
	ld %r7, 536(%r6)
	adde %r7, %r7, %r8
	std %r7, 536(%r6)
	ld %r7, 544(%r6)
	adde %r7, %r7, %r8
	std %r7, 544(%r6)
	ld %r7, 552(%r6)
	adde %r7, %r7, %r8
	std %r7, 552(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 504(%r6)
	addc %r7, %r7, %r4
	std %r7, 504(%r6)
	ld %r7, 512(%r6)
	adde %r7, %r7, %r8
	std %r7, 512(%r6)
	ld %r7, 520(%r6)
	adde %r7, %r7, %r8
	std %r7, 520(%r6)
	ld %r7, 528(%r6)
	adde %r7, %r7, %r5
	std %r7, 528(%r6)
	ld %r7, 536(%r6)
	adde %r7, %r7, %r8
	std %r7, 536(%r6)
	ld %r7, 544(%r6)
	adde %r7, %r7, %r8
	std %r7, 544(%r6)
	ld %r7, 552(%r6)
	adde %r7, %r7, %r8
	std %r7, 552(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 227b
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
229:
	ld %r4, 504(%r9)
	li %r8, 0
	ld %r5, 448(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 456(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 464(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 472(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 229b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 504(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 512(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 520(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 528(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 536(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 544(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 552(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 504(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 504(%r6)
	ld %r7, 512(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 512(%r6)
	ld %r7, 520(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 520(%r6)
	ld %r7, 528(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 528(%r6)
	ld %r7, 536(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 536(%r6)
	ld %r7, 544(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 544(%r6)
	ld %r7, 552(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 552(%r6)
	addze %r4, %r4
	ld %r7, 528(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 528(%r6)
	ld %r7, 536(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 536(%r6)
	ld %r7, 544(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 544(%r6)
	ld %r7, 552(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 552(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 504(%r6)
	addc %r7, %r7, %r4
	std %r7, 504(%r6)
	ld %r7, 512(%r6)
	adde %r7, %r7, %r8
	std %r7, 512(%r6)
	ld %r7, 520(%r6)
	adde %r7, %r7, %r8
	std %r7, 520(%r6)
	ld %r7, 528(%r6)
	adde %r7, %r7, %r5
	std %r7, 528(%r6)
	ld %r7, 536(%r6)
	adde %r7, %r7, %r8
	std %r7, 536(%r6)
	ld %r7, 544(%r6)
	adde %r7, %r7, %r8
	std %r7, 544(%r6)
	ld %r7, 552(%r6)
	adde %r7, %r7, %r8
	std %r7, 552(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 504(%r6)
	addc %r7, %r7, %r4
	std %r7, 504(%r6)
	ld %r7, 512(%r6)
	adde %r7, %r7, %r8
	std %r7, 512(%r6)
	ld %r7, 520(%r6)
	adde %r7, %r7, %r8
	std %r7, 520(%r6)
	ld %r7, 528(%r6)
	adde %r7, %r7, %r5
	std %r7, 528(%r6)
	ld %r7, 536(%r6)
	adde %r7, %r7, %r8
	std %r7, 536(%r6)
	ld %r7, 544(%r6)
	adde %r7, %r7, %r8
	std %r7, 544(%r6)
	ld %r7, 552(%r6)
	adde %r7, %r7, %r8
	std %r7, 552(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
230:
	ld %r4, 504(%r9)
	li %r8, 0
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 230b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 560(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 568(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 576(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 584(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 560(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 560(%r6)
	ld %r7, 568(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 568(%r6)
	ld %r7, 576(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 576(%r6)
	ld %r7, 584(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	addze %r4, %r4
	ld %r7, 584(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 560(%r6)
	addc %r7, %r7, %r4
	std %r7, 560(%r6)
	ld %r7, 568(%r6)
	adde %r7, %r7, %r8
	std %r7, 568(%r6)
	ld %r7, 576(%r6)
	adde %r7, %r7, %r8
	std %r7, 576(%r6)
	ld %r7, 584(%r6)
	adde %r7, %r7, %r5
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 560(%r6)
	addc %r7, %r7, %r4
	std %r7, 560(%r6)
	ld %r7, 568(%r6)
	adde %r7, %r7, %r8
	std %r7, 568(%r6)
	ld %r7, 576(%r6)
	adde %r7, %r7, %r8
	std %r7, 576(%r6)
	ld %r7, 584(%r6)
	adde %r7, %r7, %r5
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	li %r12, 31
231:
	addi %r12, %r12, -1
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
232:
	ld %r4, 560(%r9)
	li %r8, 0
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 608(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 232b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 560(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 568(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 576(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 584(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 560(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 560(%r6)
	ld %r7, 568(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 568(%r6)
	ld %r7, 576(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 576(%r6)
	ld %r7, 584(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	addze %r4, %r4
	ld %r7, 584(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 560(%r6)
	addc %r7, %r7, %r4
	std %r7, 560(%r6)
	ld %r7, 568(%r6)
	adde %r7, %r7, %r8
	std %r7, 568(%r6)
	ld %r7, 576(%r6)
	adde %r7, %r7, %r8
	std %r7, 576(%r6)
	ld %r7, 584(%r6)
	adde %r7, %r7, %r5
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 560(%r6)
	addc %r7, %r7, %r4
	std %r7, 560(%r6)
	ld %r7, 568(%r6)
	adde %r7, %r7, %r8
	std %r7, 568(%r6)
	ld %r7, 576(%r6)
	adde %r7, %r7, %r8
	std %r7, 576(%r6)
	ld %r7, 584(%r6)
	adde %r7, %r7, %r5
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 231b
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
233:
	ld %r4, 560(%r9)
	li %r8, 0
	ld %r5, 504(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 512(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 520(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 528(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 536(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 544(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 552(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 233b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 560(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 568(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 576(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 584(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 560(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 560(%r6)
	ld %r7, 568(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 568(%r6)
	ld %r7, 576(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 576(%r6)
	ld %r7, 584(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	addze %r4, %r4
	ld %r7, 584(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 560(%r6)
	addc %r7, %r7, %r4
	std %r7, 560(%r6)
	ld %r7, 568(%r6)
	adde %r7, %r7, %r8
	std %r7, 568(%r6)
	ld %r7, 576(%r6)
	adde %r7, %r7, %r8
	std %r7, 576(%r6)
	ld %r7, 584(%r6)
	adde %r7, %r7, %r5
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 560(%r6)
	addc %r7, %r7, %r4
	std %r7, 560(%r6)
	ld %r7, 568(%r6)
	adde %r7, %r7, %r8
	std %r7, 568(%r6)
	ld %r7, 576(%r6)
	adde %r7, %r7, %r8
	std %r7, 576(%r6)
	ld %r7, 584(%r6)
	adde %r7, %r7, %r5
	std %r7, 584(%r6)
	ld %r7, 592(%r6)
	adde %r7, %r7, %r8
	std %r7, 592(%r6)
	ld %r7, 600(%r6)
	adde %r7, %r7, %r8
	std %r7, 600(%r6)
	ld %r7, 608(%r6)
	adde %r7, %r7, %r8
	std %r7, 608(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
234:
	ld %r4, 560(%r9)
	li %r8, 0
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 608(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 234b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 616(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	ld %r7, 640(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r12, 63
235:
	addi %r12, %r12, -1
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
236:
	ld %r4, 616(%r9)
	li %r8, 0
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 640(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 648(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 656(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 664(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 236b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 616(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	ld %r7, 640(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 235b
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
237:
	ld %r4, 616(%r9)
	li %r8, 0
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 608(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 237b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 616(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	ld %r7, 640(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
238:
	ld %r4, 616(%r9)
	li %r8, 0
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 640(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 648(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 656(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 664(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 238b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 616(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	ld %r7, 640(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r12, 63
239:
	addi %r12, %r12, -1
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
240:
	ld %r4, 616(%r9)
	li %r8, 0
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 640(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 648(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 656(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 664(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 240b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 616(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	ld %r7, 640(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 239b
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
241:
	ld %r4, 616(%r9)
	li %r8, 0
	ld %r5, 560(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 568(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 576(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 584(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 592(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 600(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 608(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 241b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 616(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	ld %r7, 640(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
242:
	ld %r4, 616(%r9)
	li %r8, 0
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 640(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 648(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 656(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 664(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 242b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 616(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	ld %r7, 640(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r12, 15
243:
	addi %r12, %r12, -1
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
244:
	ld %r4, 616(%r9)
	li %r8, 0
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 640(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 648(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 656(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 664(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 244b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 616(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	ld %r7, 640(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 243b
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
245:
	ld %r4, 616(%r9)
	li %r8, 0
	ld %r5, 448(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 456(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 464(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 472(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 480(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 488(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 496(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 245b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 616(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	ld %r7, 640(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
246:
	ld %r4, 616(%r9)
	li %r8, 0
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 640(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 648(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 656(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 664(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 246b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 616(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	ld %r7, 640(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r12, 7
247:
	addi %r12, %r12, -1
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
248:
	ld %r4, 616(%r9)
	li %r8, 0
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 640(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 648(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 656(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 664(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 248b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 616(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	ld %r7, 640(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 247b
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
249:
	ld %r4, 616(%r9)
	li %r8, 0
	ld %r5, 392(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 400(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 408(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 416(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 424(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 432(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 440(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 249b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 616(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	ld %r7, 640(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
250:
	ld %r4, 616(%r9)
	li %r8, 0
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 640(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 648(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 656(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 664(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 250b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 616(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	ld %r7, 640(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r12, 3
251:
	addi %r12, %r12, -1
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
252:
	ld %r4, 616(%r9)
	li %r8, 0
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 640(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 648(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 656(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 664(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 252b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 616(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	ld %r7, 640(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 251b
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
253:
	ld %r4, 616(%r9)
	li %r8, 0
	ld %r5, 336(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 344(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 352(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 360(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 368(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 376(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 384(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 253b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 616(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	ld %r7, 640(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
254:
	ld %r4, 616(%r9)
	li %r8, 0
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 640(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 648(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 656(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 664(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 254b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 616(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	ld %r7, 640(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r12, 1
255:
	addi %r12, %r12, -1
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
256:
	ld %r4, 616(%r9)
	li %r8, 0
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 640(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 648(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 656(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 664(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 256b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 616(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	ld %r7, 640(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 255b
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
257:
	ld %r4, 616(%r9)
	li %r8, 0
	ld %r5, 280(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 288(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 296(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 304(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 312(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 320(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 328(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 257b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 616(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	ld %r7, 640(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
258:
	ld %r4, 616(%r9)
	li %r8, 0
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 640(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 648(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 656(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 664(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 258b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 840(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 848(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 856(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 864(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 872(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 880(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 888(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 840(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 840(%r6)
	ld %r7, 848(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 848(%r6)
	ld %r7, 856(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 856(%r6)
	ld %r7, 864(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 864(%r6)
	ld %r7, 872(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 872(%r6)
	ld %r7, 880(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 880(%r6)
	ld %r7, 888(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 888(%r6)
	addze %r4, %r4
	ld %r7, 864(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 864(%r6)
	ld %r7, 872(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 872(%r6)
	ld %r7, 880(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 880(%r6)
	ld %r7, 888(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 888(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 840(%r6)
	addc %r7, %r7, %r4
	std %r7, 840(%r6)
	ld %r7, 848(%r6)
	adde %r7, %r7, %r8
	std %r7, 848(%r6)
	ld %r7, 856(%r6)
	adde %r7, %r7, %r8
	std %r7, 856(%r6)
	ld %r7, 864(%r6)
	adde %r7, %r7, %r5
	std %r7, 864(%r6)
	ld %r7, 872(%r6)
	adde %r7, %r7, %r8
	std %r7, 872(%r6)
	ld %r7, 880(%r6)
	adde %r7, %r7, %r8
	std %r7, 880(%r6)
	ld %r7, 888(%r6)
	adde %r7, %r7, %r8
	std %r7, 888(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 840(%r6)
	addc %r7, %r7, %r4
	std %r7, 840(%r6)
	ld %r7, 848(%r6)
	adde %r7, %r7, %r8
	std %r7, 848(%r6)
	ld %r7, 856(%r6)
	adde %r7, %r7, %r8
	std %r7, 856(%r6)
	ld %r7, 864(%r6)
	adde %r7, %r7, %r5
	std %r7, 864(%r6)
	ld %r7, 872(%r6)
	adde %r7, %r7, %r8
	std %r7, 872(%r6)
	ld %r7, 880(%r6)
	adde %r7, %r7, %r8
	std %r7, 880(%r6)
	ld %r7, 888(%r6)
	adde %r7, %r7, %r8
	std %r7, 888(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
259:
	ld %r4, 840(%r9)
	li %r8, 0
	ld %r5, 112(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 120(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 128(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 136(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 144(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 152(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 259b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 840(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 848(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 856(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 864(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 872(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 880(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 888(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 840(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 840(%r6)
	ld %r7, 848(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 848(%r6)
	ld %r7, 856(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 856(%r6)
	ld %r7, 864(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 864(%r6)
	ld %r7, 872(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 872(%r6)
	ld %r7, 880(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 880(%r6)
	ld %r7, 888(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 888(%r6)
	addze %r4, %r4
	ld %r7, 864(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 864(%r6)
	ld %r7, 872(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 872(%r6)
	ld %r7, 880(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 880(%r6)
	ld %r7, 888(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 888(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 840(%r6)
	addc %r7, %r7, %r4
	std %r7, 840(%r6)
	ld %r7, 848(%r6)
	adde %r7, %r7, %r8
	std %r7, 848(%r6)
	ld %r7, 856(%r6)
	adde %r7, %r7, %r8
	std %r7, 856(%r6)
	ld %r7, 864(%r6)
	adde %r7, %r7, %r5
	std %r7, 864(%r6)
	ld %r7, 872(%r6)
	adde %r7, %r7, %r8
	std %r7, 872(%r6)
	ld %r7, 880(%r6)
	adde %r7, %r7, %r8
	std %r7, 880(%r6)
	ld %r7, 888(%r6)
	adde %r7, %r7, %r8
	std %r7, 888(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 840(%r6)
	addc %r7, %r7, %r4
	std %r7, 840(%r6)
	ld %r7, 848(%r6)
	adde %r7, %r7, %r8
	std %r7, 848(%r6)
	ld %r7, 856(%r6)
	adde %r7, %r7, %r8
	std %r7, 856(%r6)
	ld %r7, 864(%r6)
	adde %r7, %r7, %r5
	std %r7, 864(%r6)
	ld %r7, 872(%r6)
	adde %r7, %r7, %r8
	std %r7, 872(%r6)
	ld %r7, 880(%r6)
	adde %r7, %r7, %r8
	std %r7, 880(%r6)
	ld %r7, 888(%r6)
	adde %r7, %r7, %r8
	std %r7, 888(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
260:
	ld %r4, 840(%r9)
	li %r8, 0
	ld %r5, 840(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 848(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 856(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 864(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 872(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 880(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 888(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 260b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 840(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 848(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 856(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 864(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 872(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 880(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 888(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 840(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 840(%r6)
	ld %r7, 848(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 848(%r6)
	ld %r7, 856(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 856(%r6)
	ld %r7, 864(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 864(%r6)
	ld %r7, 872(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 872(%r6)
	ld %r7, 880(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 880(%r6)
	ld %r7, 888(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 888(%r6)
	addze %r4, %r4
	ld %r7, 864(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 864(%r6)
	ld %r7, 872(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 872(%r6)
	ld %r7, 880(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 880(%r6)
	ld %r7, 888(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 888(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 840(%r6)
	addc %r7, %r7, %r4
	std %r7, 840(%r6)
	ld %r7, 848(%r6)
	adde %r7, %r7, %r8
	std %r7, 848(%r6)
	ld %r7, 856(%r6)
	adde %r7, %r7, %r8
	std %r7, 856(%r6)
	ld %r7, 864(%r6)
	adde %r7, %r7, %r5
	std %r7, 864(%r6)
	ld %r7, 872(%r6)
	adde %r7, %r7, %r8
	std %r7, 872(%r6)
	ld %r7, 880(%r6)
	adde %r7, %r7, %r8
	std %r7, 880(%r6)
	ld %r7, 888(%r6)
	adde %r7, %r7, %r8
	std %r7, 888(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 840(%r6)
	addc %r7, %r7, %r4
	std %r7, 840(%r6)
	ld %r7, 848(%r6)
	adde %r7, %r7, %r8
	std %r7, 848(%r6)
	ld %r7, 856(%r6)
	adde %r7, %r7, %r8
	std %r7, 856(%r6)
	ld %r7, 864(%r6)
	adde %r7, %r7, %r5
	std %r7, 864(%r6)
	ld %r7, 872(%r6)
	adde %r7, %r7, %r8
	std %r7, 872(%r6)
	ld %r7, 880(%r6)
	adde %r7, %r7, %r8
	std %r7, 880(%r6)
	ld %r7, 888(%r6)
	adde %r7, %r7, %r8
	std %r7, 888(%r6)
	li %r12, 224
261:
	addi %r12, %r12, -1
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
262:
	ld %r4, 840(%r9)
	li %r8, 0
	ld %r5, 840(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 848(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 856(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 864(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 872(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 880(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 888(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 262b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 840(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 848(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 856(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 864(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 872(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 880(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 888(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 840(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 840(%r6)
	ld %r7, 848(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 848(%r6)
	ld %r7, 856(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 856(%r6)
	ld %r7, 864(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 864(%r6)
	ld %r7, 872(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 872(%r6)
	ld %r7, 880(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 880(%r6)
	ld %r7, 888(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 888(%r6)
	addze %r4, %r4
	ld %r7, 864(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 864(%r6)
	ld %r7, 872(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 872(%r6)
	ld %r7, 880(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 880(%r6)
	ld %r7, 888(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 888(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 840(%r6)
	addc %r7, %r7, %r4
	std %r7, 840(%r6)
	ld %r7, 848(%r6)
	adde %r7, %r7, %r8
	std %r7, 848(%r6)
	ld %r7, 856(%r6)
	adde %r7, %r7, %r8
	std %r7, 856(%r6)
	ld %r7, 864(%r6)
	adde %r7, %r7, %r5
	std %r7, 864(%r6)
	ld %r7, 872(%r6)
	adde %r7, %r7, %r8
	std %r7, 872(%r6)
	ld %r7, 880(%r6)
	adde %r7, %r7, %r8
	std %r7, 880(%r6)
	ld %r7, 888(%r6)
	adde %r7, %r7, %r8
	std %r7, 888(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 840(%r6)
	addc %r7, %r7, %r4
	std %r7, 840(%r6)
	ld %r7, 848(%r6)
	adde %r7, %r7, %r8
	std %r7, 848(%r6)
	ld %r7, 856(%r6)
	adde %r7, %r7, %r8
	std %r7, 856(%r6)
	ld %r7, 864(%r6)
	adde %r7, %r7, %r5
	std %r7, 864(%r6)
	ld %r7, 872(%r6)
	adde %r7, %r7, %r8
	std %r7, 872(%r6)
	ld %r7, 880(%r6)
	adde %r7, %r7, %r8
	std %r7, 880(%r6)
	ld %r7, 888(%r6)
	adde %r7, %r7, %r8
	std %r7, 888(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 261b
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
263:
	ld %r4, 616(%r9)
	li %r8, 0
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 640(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 648(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 656(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 664(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 263b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 616(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	ld %r7, 640(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r12, 1
264:
	addi %r12, %r12, -1
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
265:
	ld %r4, 616(%r9)
	li %r8, 0
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 640(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 648(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 656(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 664(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 265b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 616(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	ld %r7, 640(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 264b
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
266:
	ld %r4, 616(%r9)
	li %r8, 0
	ld %r5, 112(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 120(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 128(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 136(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 144(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 152(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 160(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 266b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 616(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	ld %r7, 640(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 616(%r6)
	addc %r7, %r7, %r4
	std %r7, 616(%r6)
	ld %r7, 624(%r6)
	adde %r7, %r7, %r8
	std %r7, 624(%r6)
	ld %r7, 632(%r6)
	adde %r7, %r7, %r8
	std %r7, 632(%r6)
	ld %r7, 640(%r6)
	adde %r7, %r7, %r5
	std %r7, 640(%r6)
	ld %r7, 648(%r6)
	adde %r7, %r7, %r8
	std %r7, 648(%r6)
	ld %r7, 656(%r6)
	adde %r7, %r7, %r8
	std %r7, 656(%r6)
	ld %r7, 664(%r6)
	adde %r7, %r7, %r8
	std %r7, 664(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
267:
	ld %r4, 840(%r9)
	li %r8, 0
	ld %r5, 616(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 624(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 632(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 640(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 648(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 656(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 664(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 267b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 840(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 848(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 856(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 864(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 872(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 880(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 888(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 840(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 840(%r6)
	ld %r7, 848(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 848(%r6)
	ld %r7, 856(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 856(%r6)
	ld %r7, 864(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 864(%r6)
	ld %r7, 872(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 872(%r6)
	ld %r7, 880(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 880(%r6)
	ld %r7, 888(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 888(%r6)
	addze %r4, %r4
	ld %r7, 864(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 864(%r6)
	ld %r7, 872(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 872(%r6)
	ld %r7, 880(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 880(%r6)
	ld %r7, 888(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 888(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 840(%r6)
	addc %r7, %r7, %r4
	std %r7, 840(%r6)
	ld %r7, 848(%r6)
	adde %r7, %r7, %r8
	std %r7, 848(%r6)
	ld %r7, 856(%r6)
	adde %r7, %r7, %r8
	std %r7, 856(%r6)
	ld %r7, 864(%r6)
	adde %r7, %r7, %r5
	std %r7, 864(%r6)
	ld %r7, 872(%r6)
	adde %r7, %r7, %r8
	std %r7, 872(%r6)
	ld %r7, 880(%r6)
	adde %r7, %r7, %r8
	std %r7, 880(%r6)
	ld %r7, 888(%r6)
	adde %r7, %r7, %r8
	std %r7, 888(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 840(%r6)
	addc %r7, %r7, %r4
	std %r7, 840(%r6)
	ld %r7, 848(%r6)
	adde %r7, %r7, %r8
	std %r7, 848(%r6)
	ld %r7, 856(%r6)
	adde %r7, %r7, %r8
	std %r7, 856(%r6)
	ld %r7, 864(%r6)
	adde %r7, %r7, %r5
	std %r7, 864(%r6)
	ld %r7, 872(%r6)
	adde %r7, %r7, %r8
	std %r7, 872(%r6)
	ld %r7, 880(%r6)
	adde %r7, %r7, %r8
	std %r7, 880(%r6)
	ld %r7, 888(%r6)
	adde %r7, %r7, %r8
	std %r7, 888(%r6)
	li %r7, 0
	stw %r7, 952(%r6)
	stw %r7, 956(%r6)
	stw %r7, 960(%r6)
	stw %r7, 964(%r6)
	stw %r7, 968(%r6)
	stw %r7, 972(%r6)
	stw %r7, 976(%r6)
	stw %r7, 980(%r6)
	stw %r7, 984(%r6)
	stw %r7, 988(%r6)
	stw %r7, 992(%r6)
	stw %r7, 996(%r6)
	stw %r7, 1000(%r6)
	stw %r7, 1004(%r6)
	addi %r9, %r6, 0
	li %r11, 7
268:
	ld %r4, 56(%r9)
	li %r8, 0
	ld %r5, 840(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 952(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 952(%r9)
	ld %r5, 848(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 960(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 960(%r9)
	ld %r5, 856(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 968(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 968(%r9)
	ld %r5, 864(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 976(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 976(%r9)
	ld %r5, 872(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 984(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 984(%r9)
	ld %r5, 880(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 992(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 992(%r9)
	ld %r5, 888(%r6)
	mulld %r7, %r4, %r5
	mulhdu %r5, %r4, %r5
	ld %r10, 1000(%r9)
	addc %r7, %r7, %r10
	addze %r5, %r5
	addc %r7, %r7, %r8
	addze %r8, %r5
	std %r7, 1000(%r9)
	std %r8, 1008(%r9)
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 268b
	ld %r7, 952(%r6)
	ld %r8, 1008(%r6)
	addc %r7, %r7, %r8
	std %r7, 56(%r6)
	ld %r7, 960(%r6)
	ld %r8, 1016(%r6)
	adde %r7, %r7, %r8
	std %r7, 64(%r6)
	ld %r7, 968(%r6)
	ld %r8, 1024(%r6)
	adde %r7, %r7, %r8
	std %r7, 72(%r6)
	ld %r7, 976(%r6)
	ld %r8, 1032(%r6)
	adde %r7, %r7, %r8
	std %r7, 80(%r6)
	ld %r7, 984(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 88(%r6)
	ld %r7, 992(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 96(%r6)
	ld %r7, 1000(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 104(%r6)
	li %r4, 0
	addze %r4, %r4
	ld %r7, 56(%r6)
	ld %r5, 1032(%r6)
	ld %r10, 1040(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	addc %r7, %r7, %r8
	std %r7, 56(%r6)
	ld %r7, 64(%r6)
	ld %r5, 1040(%r6)
	ld %r10, 1048(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 64(%r6)
	ld %r7, 72(%r6)
	ld %r5, 1048(%r6)
	ld %r10, 1056(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 72(%r6)
	ld %r7, 80(%r6)
	ld %r5, 1056(%r6)
	ld %r10, 1008(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 80(%r6)
	ld %r7, 88(%r6)
	ld %r5, 1008(%r6)
	ld %r10, 1016(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 88(%r6)
	ld %r7, 96(%r6)
	ld %r5, 1016(%r6)
	ld %r10, 1024(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 96(%r6)
	ld %r7, 104(%r6)
	ld %r5, 1024(%r6)
	ld %r10, 1032(%r6)
	rldicl %r5, %r5, 32, 32
	rldicr %r10, %r10, 32, 31
	add %r8, %r5, %r10
	adde %r7, %r7, %r8
	std %r7, 104(%r6)
	addze %r4, %r4
	ld %r7, 80(%r6)
	ld %r8, 1032(%r6)
	rldicl %r8, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	adde %r7, %r7, %r8
	std %r7, 80(%r6)
	ld %r7, 88(%r6)
	ld %r8, 1040(%r6)
	adde %r7, %r7, %r8
	std %r7, 88(%r6)
	ld %r7, 96(%r6)
	ld %r8, 1048(%r6)
	adde %r7, %r7, %r8
	std %r7, 96(%r6)
	ld %r7, 104(%r6)
	ld %r8, 1056(%r6)
	adde %r7, %r7, %r8
	std %r7, 104(%r6)
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 56(%r6)
	addc %r7, %r7, %r4
	std %r7, 56(%r6)
	ld %r7, 64(%r6)
	adde %r7, %r7, %r8
	std %r7, 64(%r6)
	ld %r7, 72(%r6)
	adde %r7, %r7, %r8
	std %r7, 72(%r6)
	ld %r7, 80(%r6)
	adde %r7, %r7, %r5
	std %r7, 80(%r6)
	ld %r7, 88(%r6)
	adde %r7, %r7, %r8
	std %r7, 88(%r6)
	ld %r7, 96(%r6)
	adde %r7, %r7, %r8
	std %r7, 96(%r6)
	ld %r7, 104(%r6)
	adde %r7, %r7, %r8
	std %r7, 104(%r6)
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	li %r8, 0
	ld %r7, 56(%r6)
	addc %r7, %r7, %r4
	std %r7, 56(%r6)
	ld %r7, 64(%r6)
	adde %r7, %r7, %r8
	std %r7, 64(%r6)
	ld %r7, 72(%r6)
	adde %r7, %r7, %r8
	std %r7, 72(%r6)
	ld %r7, 80(%r6)
	adde %r7, %r7, %r5
	std %r7, 80(%r6)
	ld %r7, 88(%r6)
	adde %r7, %r7, %r8
	std %r7, 88(%r6)
	ld %r7, 96(%r6)
	adde %r7, %r7, %r8
	std %r7, 96(%r6)
	ld %r7, 104(%r6)
	adde %r7, %r7, %r8
	std %r7, 104(%r6)
	li %r8, 1
	li %r10, 1
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 896(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 900(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 64(%r6)
	add %r7, %r7, %r8
	stw %r7, 904(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 68(%r6)
	add %r7, %r7, %r8
	stw %r7, 908(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 72(%r6)
	add %r7, %r7, %r8
	stw %r7, 912(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 76(%r6)
	add %r7, %r7, %r8
	stw %r7, 916(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 80(%r6)
	add %r7, %r7, %r8
	stw %r7, 920(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 84(%r6)
	add %r7, %r7, %r10
	add %r7, %r7, %r8
	stw %r7, 924(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 88(%r6)
	add %r7, %r7, %r8
	stw %r7, 928(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 92(%r6)
	add %r7, %r7, %r8
	stw %r7, 932(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 96(%r6)
	add %r7, %r7, %r8
	stw %r7, 936(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 100(%r6)
	add %r7, %r7, %r8
	stw %r7, 940(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 104(%r6)
	add %r7, %r7, %r8
	stw %r7, 944(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 108(%r6)
	add %r7, %r7, %r8
	stw %r7, 948(%r6)
	rldicl %r8, %r7, 32, 32
	li %r4, 0
	subf %r11, %r8, %r4
	lwz %r5, 56(%r6)
	lwz %r7, 896(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 0(%r3)
	lwz %r5, 60(%r6)
	lwz %r7, 900(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 4(%r3)
	lwz %r5, 64(%r6)
	lwz %r7, 904(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 8(%r3)
	lwz %r5, 68(%r6)
	lwz %r7, 908(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 12(%r3)
	lwz %r5, 72(%r6)
	lwz %r7, 912(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 16(%r3)
	lwz %r5, 76(%r6)
	lwz %r7, 916(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 20(%r3)
	lwz %r5, 80(%r6)
	lwz %r7, 920(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 24(%r3)
	lwz %r5, 84(%r6)
	lwz %r7, 924(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 28(%r3)
	lwz %r5, 88(%r6)
	lwz %r7, 928(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 32(%r3)
	lwz %r5, 92(%r6)
	lwz %r7, 932(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 36(%r3)
	lwz %r5, 96(%r6)
	lwz %r7, 936(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 40(%r3)
	lwz %r5, 100(%r6)
	lwz %r7, 940(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 44(%r3)
	lwz %r5, 104(%r6)
	lwz %r7, 944(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 48(%r3)
	lwz %r5, 108(%r6)
	lwz %r7, 948(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 52(%r3)
	blr
