// The functions of `src/sm4_cbc.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_cbc_encrypt_chained:
	stdu %r1, -3296(%r1)
	addi %r7, %r1, 32
	mflr %r0
	std %r0, 3240(%r7)
	std %r29, 3216(%r7)
	std %r30, 3224(%r7)
	std %r31, 3232(%r7)
	or %r29, %r4, %r4
	or %r30, %r6, %r6
	or %r31, %r4, %r4
	or %r6, %r5, %r5
	or %r5, %r7, %r7
	lwz %r8, 0(%r31)
	stw %r8, 3248(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 3252(%r5)
	lwz %r8, 8(%r31)
	stw %r8, 3256(%r5)
	lwz %r8, 12(%r31)
	stw %r8, 3260(%r5)
	or %r31, %r6, %r6
	cmpldi %cr0, %r30, 0
	beq %cr0, 20f
22:
	lwz %r8, 0(%r31)
	lwz %r9, 3248(%r5)
	xor %r8, %r8, %r9
	stw %r8, 768(%r5)
	lwz %r8, 4(%r31)
	lwz %r9, 3252(%r5)
	xor %r8, %r8, %r9
	stw %r8, 772(%r5)
	lwz %r8, 8(%r31)
	lwz %r9, 3256(%r5)
	xor %r8, %r8, %r9
	stw %r8, 776(%r5)
	lwz %r8, 12(%r31)
	lwz %r9, 3260(%r5)
	xor %r8, %r8, %r9
	stw %r8, 780(%r5)
	bl {vg_sm4_serial_encrypt}
	lwz %r8, 768(%r5)
	stw %r8, 3248(%r5)
	lwz %r8, 772(%r5)
	stw %r8, 3252(%r5)
	lwz %r8, 776(%r5)
	stw %r8, 3256(%r5)
	lwz %r8, 780(%r5)
	stw %r8, 3260(%r5)
	lwz %r8, 768(%r5)
	stw %r8, 0(%r31)
	lwz %r8, 772(%r5)
	stw %r8, 4(%r31)
	lwz %r8, 776(%r5)
	stw %r8, 8(%r31)
	lwz %r8, 780(%r5)
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 22b
	b 21f
20:
21:
	or %r31, %r29, %r29
	lwz %r8, 3248(%r5)
	stw %r8, 0(%r31)
	lwz %r8, 3252(%r5)
	stw %r8, 4(%r31)
	lwz %r8, 3256(%r5)
	stw %r8, 8(%r31)
	lwz %r8, 3260(%r5)
	stw %r8, 12(%r31)
	ld %r29, 3216(%r5)
	ld %r30, 3224(%r5)
	ld %r31, 3232(%r5)
	ld %r0, 3240(%r5)
	mtlr %r0
	addi %r12, %r1, 32
	li %r0, 0
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	std %r0, 128(%r12)
	std %r0, 136(%r12)
	std %r0, 144(%r12)
	std %r0, 152(%r12)
	std %r0, 160(%r12)
	std %r0, 168(%r12)
	std %r0, 176(%r12)
	std %r0, 184(%r12)
	addi %r1, %r1, 3296
	li %r0, 0
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v12, %v12, %v12
	vxor %v13, %v13, %v13
	vxor %v14, %v14, %v14
	vxor %v15, %v15, %v15
	blr

vg_sm4_cbc_decrypt_chained:
	stdu %r1, -3296(%r1)
	addi %r7, %r1, 32
	rldicl %r8, %r6, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 20f
	mflr %r0
	std %r0, 3240(%r7)
	std %r29, 3216(%r7)
	std %r30, 3224(%r7)
	std %r31, 3232(%r7)
	or %r29, %r4, %r4
	or %r30, %r6, %r6
	or %r31, %r4, %r4
	or %r6, %r5, %r5
	or %r5, %r7, %r7
	lwz %r8, 0(%r31)
	stw %r8, 3248(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 3252(%r5)
	lwz %r8, 8(%r31)
	stw %r8, 3256(%r5)
	lwz %r8, 12(%r31)
	stw %r8, 3260(%r5)
	or %r31, %r6, %r6
	or %r7, %r3, %r3
	li %r4, 1
	li %r6, 402
	bl {vg_sm4_prepare_keys}
	or %r3, %r7, %r7
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 22f
24:
	lwz %r8, 0(%r31)
	stw %r8, 768(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 772(%r5)
	lwz %r8, 8(%r31)
	stw %r8, 776(%r5)
	lwz %r8, 12(%r31)
	stw %r8, 780(%r5)
	lwz %r8, 16(%r31)
	stw %r8, 784(%r5)
	lwz %r8, 20(%r31)
	stw %r8, 788(%r5)
	lwz %r8, 24(%r31)
	stw %r8, 792(%r5)
	lwz %r8, 28(%r31)
	stw %r8, 796(%r5)
	lwz %r8, 32(%r31)
	stw %r8, 800(%r5)
	lwz %r8, 36(%r31)
	stw %r8, 804(%r5)
	lwz %r8, 40(%r31)
	stw %r8, 808(%r5)
	lwz %r8, 44(%r31)
	stw %r8, 812(%r5)
	lwz %r8, 48(%r31)
	stw %r8, 816(%r5)
	lwz %r8, 52(%r31)
	stw %r8, 820(%r5)
	lwz %r8, 56(%r31)
	stw %r8, 824(%r5)
	lwz %r8, 60(%r31)
	stw %r8, 828(%r5)
	lwz %r8, 64(%r31)
	stw %r8, 832(%r5)
	lwz %r8, 68(%r31)
	stw %r8, 836(%r5)
	lwz %r8, 72(%r31)
	stw %r8, 840(%r5)
	lwz %r8, 76(%r31)
	stw %r8, 844(%r5)
	lwz %r8, 80(%r31)
	stw %r8, 848(%r5)
	lwz %r8, 84(%r31)
	stw %r8, 852(%r5)
	lwz %r8, 88(%r31)
	stw %r8, 856(%r5)
	lwz %r8, 92(%r31)
	stw %r8, 860(%r5)
	lwz %r8, 96(%r31)
	stw %r8, 864(%r5)
	lwz %r8, 100(%r31)
	stw %r8, 868(%r5)
	lwz %r8, 104(%r31)
	stw %r8, 872(%r5)
	lwz %r8, 108(%r31)
	stw %r8, 876(%r5)
	lwz %r8, 112(%r31)
	stw %r8, 880(%r5)
	lwz %r8, 116(%r31)
	stw %r8, 884(%r5)
	lwz %r8, 120(%r31)
	stw %r8, 888(%r5)
	lwz %r8, 124(%r31)
	stw %r8, 892(%r5)
	lwz %r8, 128(%r31)
	stw %r8, 896(%r5)
	lwz %r8, 132(%r31)
	stw %r8, 900(%r5)
	lwz %r8, 136(%r31)
	stw %r8, 904(%r5)
	lwz %r8, 140(%r31)
	stw %r8, 908(%r5)
	lwz %r8, 144(%r31)
	stw %r8, 912(%r5)
	lwz %r8, 148(%r31)
	stw %r8, 916(%r5)
	lwz %r8, 152(%r31)
	stw %r8, 920(%r5)
	lwz %r8, 156(%r31)
	stw %r8, 924(%r5)
	lwz %r8, 160(%r31)
	stw %r8, 928(%r5)
	lwz %r8, 164(%r31)
	stw %r8, 932(%r5)
	lwz %r8, 168(%r31)
	stw %r8, 936(%r5)
	lwz %r8, 172(%r31)
	stw %r8, 940(%r5)
	lwz %r8, 176(%r31)
	stw %r8, 944(%r5)
	lwz %r8, 180(%r31)
	stw %r8, 948(%r5)
	lwz %r8, 184(%r31)
	stw %r8, 952(%r5)
	lwz %r8, 188(%r31)
	stw %r8, 956(%r5)
	lwz %r8, 192(%r31)
	stw %r8, 960(%r5)
	lwz %r8, 196(%r31)
	stw %r8, 964(%r5)
	lwz %r8, 200(%r31)
	stw %r8, 968(%r5)
	lwz %r8, 204(%r31)
	stw %r8, 972(%r5)
	lwz %r8, 208(%r31)
	stw %r8, 976(%r5)
	lwz %r8, 212(%r31)
	stw %r8, 980(%r5)
	lwz %r8, 216(%r31)
	stw %r8, 984(%r5)
	lwz %r8, 220(%r31)
	stw %r8, 988(%r5)
	lwz %r8, 224(%r31)
	stw %r8, 992(%r5)
	lwz %r8, 228(%r31)
	stw %r8, 996(%r5)
	lwz %r8, 232(%r31)
	stw %r8, 1000(%r5)
	lwz %r8, 236(%r31)
	stw %r8, 1004(%r5)
	lwz %r8, 240(%r31)
	stw %r8, 1008(%r5)
	lwz %r8, 244(%r31)
	stw %r8, 1012(%r5)
	lwz %r8, 248(%r31)
	stw %r8, 1016(%r5)
	lwz %r8, 252(%r31)
	stw %r8, 1020(%r5)
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 768(%r5)
	lwz %r9, 3248(%r5)
	xor %r8, %r8, %r9
	stw %r8, 768(%r5)
	lwz %r8, 772(%r5)
	lwz %r9, 3252(%r5)
	xor %r8, %r8, %r9
	stw %r8, 772(%r5)
	lwz %r8, 776(%r5)
	lwz %r9, 3256(%r5)
	xor %r8, %r8, %r9
	stw %r8, 776(%r5)
	lwz %r8, 780(%r5)
	lwz %r9, 3260(%r5)
	xor %r8, %r8, %r9
	stw %r8, 780(%r5)
	lwz %r8, 0(%r31)
	stw %r8, 3248(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 3252(%r5)
	lwz %r8, 8(%r31)
	stw %r8, 3256(%r5)
	lwz %r8, 12(%r31)
	stw %r8, 3260(%r5)
	lwz %r8, 768(%r5)
	stw %r8, 0(%r31)
	lwz %r8, 772(%r5)
	stw %r8, 4(%r31)
	lwz %r8, 776(%r5)
	stw %r8, 8(%r31)
	lwz %r8, 780(%r5)
	stw %r8, 12(%r31)
	lwz %r8, 784(%r5)
	lwz %r9, 3248(%r5)
	xor %r8, %r8, %r9
	stw %r8, 784(%r5)
	lwz %r8, 788(%r5)
	lwz %r9, 3252(%r5)
	xor %r8, %r8, %r9
	stw %r8, 788(%r5)
	lwz %r8, 792(%r5)
	lwz %r9, 3256(%r5)
	xor %r8, %r8, %r9
	stw %r8, 792(%r5)
	lwz %r8, 796(%r5)
	lwz %r9, 3260(%r5)
	xor %r8, %r8, %r9
	stw %r8, 796(%r5)
	lwz %r8, 16(%r31)
	stw %r8, 3248(%r5)
	lwz %r8, 20(%r31)
	stw %r8, 3252(%r5)
	lwz %r8, 24(%r31)
	stw %r8, 3256(%r5)
	lwz %r8, 28(%r31)
	stw %r8, 3260(%r5)
	lwz %r8, 784(%r5)
	stw %r8, 16(%r31)
	lwz %r8, 788(%r5)
	stw %r8, 20(%r31)
	lwz %r8, 792(%r5)
	stw %r8, 24(%r31)
	lwz %r8, 796(%r5)
	stw %r8, 28(%r31)
	lwz %r8, 800(%r5)
	lwz %r9, 3248(%r5)
	xor %r8, %r8, %r9
	stw %r8, 800(%r5)
	lwz %r8, 804(%r5)
	lwz %r9, 3252(%r5)
	xor %r8, %r8, %r9
	stw %r8, 804(%r5)
	lwz %r8, 808(%r5)
	lwz %r9, 3256(%r5)
	xor %r8, %r8, %r9
	stw %r8, 808(%r5)
	lwz %r8, 812(%r5)
	lwz %r9, 3260(%r5)
	xor %r8, %r8, %r9
	stw %r8, 812(%r5)
	lwz %r8, 32(%r31)
	stw %r8, 3248(%r5)
	lwz %r8, 36(%r31)
	stw %r8, 3252(%r5)
	lwz %r8, 40(%r31)
	stw %r8, 3256(%r5)
	lwz %r8, 44(%r31)
	stw %r8, 3260(%r5)
	lwz %r8, 800(%r5)
	stw %r8, 32(%r31)
	lwz %r8, 804(%r5)
	stw %r8, 36(%r31)
	lwz %r8, 808(%r5)
	stw %r8, 40(%r31)
	lwz %r8, 812(%r5)
	stw %r8, 44(%r31)
	lwz %r8, 816(%r5)
	lwz %r9, 3248(%r5)
	xor %r8, %r8, %r9
	stw %r8, 816(%r5)
	lwz %r8, 820(%r5)
	lwz %r9, 3252(%r5)
	xor %r8, %r8, %r9
	stw %r8, 820(%r5)
	lwz %r8, 824(%r5)
	lwz %r9, 3256(%r5)
	xor %r8, %r8, %r9
	stw %r8, 824(%r5)
	lwz %r8, 828(%r5)
	lwz %r9, 3260(%r5)
	xor %r8, %r8, %r9
	stw %r8, 828(%r5)
	lwz %r8, 48(%r31)
	stw %r8, 3248(%r5)
	lwz %r8, 52(%r31)
	stw %r8, 3252(%r5)
	lwz %r8, 56(%r31)
	stw %r8, 3256(%r5)
	lwz %r8, 60(%r31)
	stw %r8, 3260(%r5)
	lwz %r8, 816(%r5)
	stw %r8, 48(%r31)
	lwz %r8, 820(%r5)
	stw %r8, 52(%r31)
	lwz %r8, 824(%r5)
	stw %r8, 56(%r31)
	lwz %r8, 828(%r5)
	stw %r8, 60(%r31)
	lwz %r8, 832(%r5)
	lwz %r9, 3248(%r5)
	xor %r8, %r8, %r9
	stw %r8, 832(%r5)
	lwz %r8, 836(%r5)
	lwz %r9, 3252(%r5)
	xor %r8, %r8, %r9
	stw %r8, 836(%r5)
	lwz %r8, 840(%r5)
	lwz %r9, 3256(%r5)
	xor %r8, %r8, %r9
	stw %r8, 840(%r5)
	lwz %r8, 844(%r5)
	lwz %r9, 3260(%r5)
	xor %r8, %r8, %r9
	stw %r8, 844(%r5)
	lwz %r8, 64(%r31)
	stw %r8, 3248(%r5)
	lwz %r8, 68(%r31)
	stw %r8, 3252(%r5)
	lwz %r8, 72(%r31)
	stw %r8, 3256(%r5)
	lwz %r8, 76(%r31)
	stw %r8, 3260(%r5)
	lwz %r8, 832(%r5)
	stw %r8, 64(%r31)
	lwz %r8, 836(%r5)
	stw %r8, 68(%r31)
	lwz %r8, 840(%r5)
	stw %r8, 72(%r31)
	lwz %r8, 844(%r5)
	stw %r8, 76(%r31)
	lwz %r8, 848(%r5)
	lwz %r9, 3248(%r5)
	xor %r8, %r8, %r9
	stw %r8, 848(%r5)
	lwz %r8, 852(%r5)
	lwz %r9, 3252(%r5)
	xor %r8, %r8, %r9
	stw %r8, 852(%r5)
	lwz %r8, 856(%r5)
	lwz %r9, 3256(%r5)
	xor %r8, %r8, %r9
	stw %r8, 856(%r5)
	lwz %r8, 860(%r5)
	lwz %r9, 3260(%r5)
	xor %r8, %r8, %r9
	stw %r8, 860(%r5)
	lwz %r8, 80(%r31)
	stw %r8, 3248(%r5)
	lwz %r8, 84(%r31)
	stw %r8, 3252(%r5)
	lwz %r8, 88(%r31)
	stw %r8, 3256(%r5)
	lwz %r8, 92(%r31)
	stw %r8, 3260(%r5)
	lwz %r8, 848(%r5)
	stw %r8, 80(%r31)
	lwz %r8, 852(%r5)
	stw %r8, 84(%r31)
	lwz %r8, 856(%r5)
	stw %r8, 88(%r31)
	lwz %r8, 860(%r5)
	stw %r8, 92(%r31)
	lwz %r8, 864(%r5)
	lwz %r9, 3248(%r5)
	xor %r8, %r8, %r9
	stw %r8, 864(%r5)
	lwz %r8, 868(%r5)
	lwz %r9, 3252(%r5)
	xor %r8, %r8, %r9
	stw %r8, 868(%r5)
	lwz %r8, 872(%r5)
	lwz %r9, 3256(%r5)
	xor %r8, %r8, %r9
	stw %r8, 872(%r5)
	lwz %r8, 876(%r5)
	lwz %r9, 3260(%r5)
	xor %r8, %r8, %r9
	stw %r8, 876(%r5)
	lwz %r8, 96(%r31)
	stw %r8, 3248(%r5)
	lwz %r8, 100(%r31)
	stw %r8, 3252(%r5)
	lwz %r8, 104(%r31)
	stw %r8, 3256(%r5)
	lwz %r8, 108(%r31)
	stw %r8, 3260(%r5)
	lwz %r8, 864(%r5)
	stw %r8, 96(%r31)
	lwz %r8, 868(%r5)
	stw %r8, 100(%r31)
	lwz %r8, 872(%r5)
	stw %r8, 104(%r31)
	lwz %r8, 876(%r5)
	stw %r8, 108(%r31)
	lwz %r8, 880(%r5)
	lwz %r9, 3248(%r5)
	xor %r8, %r8, %r9
	stw %r8, 880(%r5)
	lwz %r8, 884(%r5)
	lwz %r9, 3252(%r5)
	xor %r8, %r8, %r9
	stw %r8, 884(%r5)
	lwz %r8, 888(%r5)
	lwz %r9, 3256(%r5)
	xor %r8, %r8, %r9
	stw %r8, 888(%r5)
	lwz %r8, 892(%r5)
	lwz %r9, 3260(%r5)
	xor %r8, %r8, %r9
	stw %r8, 892(%r5)
	lwz %r8, 112(%r31)
	stw %r8, 3248(%r5)
	lwz %r8, 116(%r31)
	stw %r8, 3252(%r5)
	lwz %r8, 120(%r31)
	stw %r8, 3256(%r5)
	lwz %r8, 124(%r31)
	stw %r8, 3260(%r5)
	lwz %r8, 880(%r5)
	stw %r8, 112(%r31)
	lwz %r8, 884(%r5)
	stw %r8, 116(%r31)
	lwz %r8, 888(%r5)
	stw %r8, 120(%r31)
	lwz %r8, 892(%r5)
	stw %r8, 124(%r31)
	lwz %r8, 896(%r5)
	lwz %r9, 3248(%r5)
	xor %r8, %r8, %r9
	stw %r8, 896(%r5)
	lwz %r8, 900(%r5)
	lwz %r9, 3252(%r5)
	xor %r8, %r8, %r9
	stw %r8, 900(%r5)
	lwz %r8, 904(%r5)
	lwz %r9, 3256(%r5)
	xor %r8, %r8, %r9
	stw %r8, 904(%r5)
	lwz %r8, 908(%r5)
	lwz %r9, 3260(%r5)
	xor %r8, %r8, %r9
	stw %r8, 908(%r5)
	lwz %r8, 128(%r31)
	stw %r8, 3248(%r5)
	lwz %r8, 132(%r31)
	stw %r8, 3252(%r5)
	lwz %r8, 136(%r31)
	stw %r8, 3256(%r5)
	lwz %r8, 140(%r31)
	stw %r8, 3260(%r5)
	lwz %r8, 896(%r5)
	stw %r8, 128(%r31)
	lwz %r8, 900(%r5)
	stw %r8, 132(%r31)
	lwz %r8, 904(%r5)
	stw %r8, 136(%r31)
	lwz %r8, 908(%r5)
	stw %r8, 140(%r31)
	lwz %r8, 912(%r5)
	lwz %r9, 3248(%r5)
	xor %r8, %r8, %r9
	stw %r8, 912(%r5)
	lwz %r8, 916(%r5)
	lwz %r9, 3252(%r5)
	xor %r8, %r8, %r9
	stw %r8, 916(%r5)
	lwz %r8, 920(%r5)
	lwz %r9, 3256(%r5)
	xor %r8, %r8, %r9
	stw %r8, 920(%r5)
	lwz %r8, 924(%r5)
	lwz %r9, 3260(%r5)
	xor %r8, %r8, %r9
	stw %r8, 924(%r5)
	lwz %r8, 144(%r31)
	stw %r8, 3248(%r5)
	lwz %r8, 148(%r31)
	stw %r8, 3252(%r5)
	lwz %r8, 152(%r31)
	stw %r8, 3256(%r5)
	lwz %r8, 156(%r31)
	stw %r8, 3260(%r5)
	lwz %r8, 912(%r5)
	stw %r8, 144(%r31)
	lwz %r8, 916(%r5)
	stw %r8, 148(%r31)
	lwz %r8, 920(%r5)
	stw %r8, 152(%r31)
	lwz %r8, 924(%r5)
	stw %r8, 156(%r31)
	lwz %r8, 928(%r5)
	lwz %r9, 3248(%r5)
	xor %r8, %r8, %r9
	stw %r8, 928(%r5)
	lwz %r8, 932(%r5)
	lwz %r9, 3252(%r5)
	xor %r8, %r8, %r9
	stw %r8, 932(%r5)
	lwz %r8, 936(%r5)
	lwz %r9, 3256(%r5)
	xor %r8, %r8, %r9
	stw %r8, 936(%r5)
	lwz %r8, 940(%r5)
	lwz %r9, 3260(%r5)
	xor %r8, %r8, %r9
	stw %r8, 940(%r5)
	lwz %r8, 160(%r31)
	stw %r8, 3248(%r5)
	lwz %r8, 164(%r31)
	stw %r8, 3252(%r5)
	lwz %r8, 168(%r31)
	stw %r8, 3256(%r5)
	lwz %r8, 172(%r31)
	stw %r8, 3260(%r5)
	lwz %r8, 928(%r5)
	stw %r8, 160(%r31)
	lwz %r8, 932(%r5)
	stw %r8, 164(%r31)
	lwz %r8, 936(%r5)
	stw %r8, 168(%r31)
	lwz %r8, 940(%r5)
	stw %r8, 172(%r31)
	lwz %r8, 944(%r5)
	lwz %r9, 3248(%r5)
	xor %r8, %r8, %r9
	stw %r8, 944(%r5)
	lwz %r8, 948(%r5)
	lwz %r9, 3252(%r5)
	xor %r8, %r8, %r9
	stw %r8, 948(%r5)
	lwz %r8, 952(%r5)
	lwz %r9, 3256(%r5)
	xor %r8, %r8, %r9
	stw %r8, 952(%r5)
	lwz %r8, 956(%r5)
	lwz %r9, 3260(%r5)
	xor %r8, %r8, %r9
	stw %r8, 956(%r5)
	lwz %r8, 176(%r31)
	stw %r8, 3248(%r5)
	lwz %r8, 180(%r31)
	stw %r8, 3252(%r5)
	lwz %r8, 184(%r31)
	stw %r8, 3256(%r5)
	lwz %r8, 188(%r31)
	stw %r8, 3260(%r5)
	lwz %r8, 944(%r5)
	stw %r8, 176(%r31)
	lwz %r8, 948(%r5)
	stw %r8, 180(%r31)
	lwz %r8, 952(%r5)
	stw %r8, 184(%r31)
	lwz %r8, 956(%r5)
	stw %r8, 188(%r31)
	lwz %r8, 960(%r5)
	lwz %r9, 3248(%r5)
	xor %r8, %r8, %r9
	stw %r8, 960(%r5)
	lwz %r8, 964(%r5)
	lwz %r9, 3252(%r5)
	xor %r8, %r8, %r9
	stw %r8, 964(%r5)
	lwz %r8, 968(%r5)
	lwz %r9, 3256(%r5)
	xor %r8, %r8, %r9
	stw %r8, 968(%r5)
	lwz %r8, 972(%r5)
	lwz %r9, 3260(%r5)
	xor %r8, %r8, %r9
	stw %r8, 972(%r5)
	lwz %r8, 192(%r31)
	stw %r8, 3248(%r5)
	lwz %r8, 196(%r31)
	stw %r8, 3252(%r5)
	lwz %r8, 200(%r31)
	stw %r8, 3256(%r5)
	lwz %r8, 204(%r31)
	stw %r8, 3260(%r5)
	lwz %r8, 960(%r5)
	stw %r8, 192(%r31)
	lwz %r8, 964(%r5)
	stw %r8, 196(%r31)
	lwz %r8, 968(%r5)
	stw %r8, 200(%r31)
	lwz %r8, 972(%r5)
	stw %r8, 204(%r31)
	lwz %r8, 976(%r5)
	lwz %r9, 3248(%r5)
	xor %r8, %r8, %r9
	stw %r8, 976(%r5)
	lwz %r8, 980(%r5)
	lwz %r9, 3252(%r5)
	xor %r8, %r8, %r9
	stw %r8, 980(%r5)
	lwz %r8, 984(%r5)
	lwz %r9, 3256(%r5)
	xor %r8, %r8, %r9
	stw %r8, 984(%r5)
	lwz %r8, 988(%r5)
	lwz %r9, 3260(%r5)
	xor %r8, %r8, %r9
	stw %r8, 988(%r5)
	lwz %r8, 208(%r31)
	stw %r8, 3248(%r5)
	lwz %r8, 212(%r31)
	stw %r8, 3252(%r5)
	lwz %r8, 216(%r31)
	stw %r8, 3256(%r5)
	lwz %r8, 220(%r31)
	stw %r8, 3260(%r5)
	lwz %r8, 976(%r5)
	stw %r8, 208(%r31)
	lwz %r8, 980(%r5)
	stw %r8, 212(%r31)
	lwz %r8, 984(%r5)
	stw %r8, 216(%r31)
	lwz %r8, 988(%r5)
	stw %r8, 220(%r31)
	lwz %r8, 992(%r5)
	lwz %r9, 3248(%r5)
	xor %r8, %r8, %r9
	stw %r8, 992(%r5)
	lwz %r8, 996(%r5)
	lwz %r9, 3252(%r5)
	xor %r8, %r8, %r9
	stw %r8, 996(%r5)
	lwz %r8, 1000(%r5)
	lwz %r9, 3256(%r5)
	xor %r8, %r8, %r9
	stw %r8, 1000(%r5)
	lwz %r8, 1004(%r5)
	lwz %r9, 3260(%r5)
	xor %r8, %r8, %r9
	stw %r8, 1004(%r5)
	lwz %r8, 224(%r31)
	stw %r8, 3248(%r5)
	lwz %r8, 228(%r31)
	stw %r8, 3252(%r5)
	lwz %r8, 232(%r31)
	stw %r8, 3256(%r5)
	lwz %r8, 236(%r31)
	stw %r8, 3260(%r5)
	lwz %r8, 992(%r5)
	stw %r8, 224(%r31)
	lwz %r8, 996(%r5)
	stw %r8, 228(%r31)
	lwz %r8, 1000(%r5)
	stw %r8, 232(%r31)
	lwz %r8, 1004(%r5)
	stw %r8, 236(%r31)
	lwz %r8, 1008(%r5)
	lwz %r9, 3248(%r5)
	xor %r8, %r8, %r9
	stw %r8, 1008(%r5)
	lwz %r8, 1012(%r5)
	lwz %r9, 3252(%r5)
	xor %r8, %r8, %r9
	stw %r8, 1012(%r5)
	lwz %r8, 1016(%r5)
	lwz %r9, 3256(%r5)
	xor %r8, %r8, %r9
	stw %r8, 1016(%r5)
	lwz %r8, 1020(%r5)
	lwz %r9, 3260(%r5)
	xor %r8, %r8, %r9
	stw %r8, 1020(%r5)
	lwz %r8, 240(%r31)
	stw %r8, 3248(%r5)
	lwz %r8, 244(%r31)
	stw %r8, 3252(%r5)
	lwz %r8, 248(%r31)
	stw %r8, 3256(%r5)
	lwz %r8, 252(%r31)
	stw %r8, 3260(%r5)
	lwz %r8, 1008(%r5)
	stw %r8, 240(%r31)
	lwz %r8, 1012(%r5)
	stw %r8, 244(%r31)
	lwz %r8, 1016(%r5)
	stw %r8, 248(%r31)
	lwz %r8, 1020(%r5)
	stw %r8, 252(%r31)
	addi %r31, %r31, 256
	addi %r30, %r30, -16
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	bne %cr0, 24b
	b 23f
22:
23:
	cmpldi %cr0, %r30, 0
	beq %cr0, 25f
27:
	lwz %r8, 0(%r31)
	stw %r8, 768(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 772(%r5)
	lwz %r8, 8(%r31)
	stw %r8, 776(%r5)
	lwz %r8, 12(%r31)
	stw %r8, 780(%r5)
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 768(%r5)
	lwz %r9, 3248(%r5)
	xor %r8, %r8, %r9
	stw %r8, 768(%r5)
	lwz %r8, 772(%r5)
	lwz %r9, 3252(%r5)
	xor %r8, %r8, %r9
	stw %r8, 772(%r5)
	lwz %r8, 776(%r5)
	lwz %r9, 3256(%r5)
	xor %r8, %r8, %r9
	stw %r8, 776(%r5)
	lwz %r8, 780(%r5)
	lwz %r9, 3260(%r5)
	xor %r8, %r8, %r9
	stw %r8, 780(%r5)
	lwz %r8, 0(%r31)
	stw %r8, 3248(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 3252(%r5)
	lwz %r8, 8(%r31)
	stw %r8, 3256(%r5)
	lwz %r8, 12(%r31)
	stw %r8, 3260(%r5)
	lwz %r8, 768(%r5)
	stw %r8, 0(%r31)
	lwz %r8, 772(%r5)
	stw %r8, 4(%r31)
	lwz %r8, 776(%r5)
	stw %r8, 8(%r31)
	lwz %r8, 780(%r5)
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 27b
	b 26f
25:
26:
	or %r31, %r29, %r29
	lwz %r8, 3248(%r5)
	stw %r8, 0(%r31)
	lwz %r8, 3252(%r5)
	stw %r8, 4(%r31)
	lwz %r8, 3256(%r5)
	stw %r8, 8(%r31)
	lwz %r8, 3260(%r5)
	stw %r8, 12(%r31)
	ld %r29, 3216(%r5)
	ld %r30, 3224(%r5)
	ld %r31, 3232(%r5)
	ld %r0, 3240(%r5)
	mtlr %r0
	b 21f
20:
	mflr %r0
	std %r0, 3240(%r7)
	std %r29, 3216(%r7)
	std %r30, 3224(%r7)
	std %r31, 3232(%r7)
	or %r29, %r4, %r4
	or %r30, %r6, %r6
	or %r31, %r4, %r4
	or %r6, %r5, %r5
	or %r5, %r7, %r7
	lwz %r8, 0(%r31)
	stw %r8, 3248(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 3252(%r5)
	lwz %r8, 8(%r31)
	stw %r8, 3256(%r5)
	lwz %r8, 12(%r31)
	stw %r8, 3260(%r5)
	or %r31, %r6, %r6
	cmpldi %cr0, %r30, 0
	beq %cr0, 28f
210:
	lwz %r8, 0(%r31)
	stw %r8, 768(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 772(%r5)
	lwz %r8, 8(%r31)
	stw %r8, 776(%r5)
	lwz %r8, 12(%r31)
	stw %r8, 780(%r5)
	bl {vg_sm4_serial_decrypt}
	lwz %r8, 768(%r5)
	lwz %r9, 3248(%r5)
	xor %r8, %r8, %r9
	stw %r8, 768(%r5)
	lwz %r8, 772(%r5)
	lwz %r9, 3252(%r5)
	xor %r8, %r8, %r9
	stw %r8, 772(%r5)
	lwz %r8, 776(%r5)
	lwz %r9, 3256(%r5)
	xor %r8, %r8, %r9
	stw %r8, 776(%r5)
	lwz %r8, 780(%r5)
	lwz %r9, 3260(%r5)
	xor %r8, %r8, %r9
	stw %r8, 780(%r5)
	lwz %r8, 0(%r31)
	stw %r8, 3248(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 3252(%r5)
	lwz %r8, 8(%r31)
	stw %r8, 3256(%r5)
	lwz %r8, 12(%r31)
	stw %r8, 3260(%r5)
	lwz %r8, 768(%r5)
	stw %r8, 0(%r31)
	lwz %r8, 772(%r5)
	stw %r8, 4(%r31)
	lwz %r8, 776(%r5)
	stw %r8, 8(%r31)
	lwz %r8, 780(%r5)
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 210b
	b 29f
28:
29:
	or %r31, %r29, %r29
	lwz %r8, 3248(%r5)
	stw %r8, 0(%r31)
	lwz %r8, 3252(%r5)
	stw %r8, 4(%r31)
	lwz %r8, 3256(%r5)
	stw %r8, 8(%r31)
	lwz %r8, 3260(%r5)
	stw %r8, 12(%r31)
	ld %r29, 3216(%r5)
	ld %r30, 3224(%r5)
	ld %r31, 3232(%r5)
	ld %r0, 3240(%r5)
	mtlr %r0
21:
	addi %r12, %r1, 32
	li %r0, 0
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	std %r0, 128(%r12)
	std %r0, 136(%r12)
	std %r0, 144(%r12)
	std %r0, 152(%r12)
	std %r0, 160(%r12)
	std %r0, 168(%r12)
	std %r0, 176(%r12)
	std %r0, 184(%r12)
	addi %r1, %r1, 3296
	li %r0, 0
	li %r3, 0
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v12, %v12, %v12
	vxor %v13, %v13, %v13
	vxor %v14, %v14, %v14
	vxor %v15, %v15, %v15
	blr
