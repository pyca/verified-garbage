// The functions of `src/sm4_gcm.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_gcm_init:
	stdu %r1, -320(%r1)
	addi %r5, %r1, 32
	stdu %r1, -3296(%r1)
	addi %r6, %r1, 32
	std %r18, 128(%r5)
	std %r19, 136(%r5)
	std %r20, 144(%r5)
	std %r21, 152(%r5)
	std %r22, 160(%r5)
	std %r23, 168(%r5)
	std %r24, 176(%r5)
	std %r25, 184(%r5)
	std %r26, 192(%r5)
	std %r27, 200(%r5)
	std %r28, 208(%r5)
	std %r29, 216(%r5)
	std %r30, 224(%r5)
	std %r31, 232(%r5)
	mflr %r0
	std %r0, 240(%r5)
	or %r31, %r5, %r5
	or %r29, %r4, %r4
	or %r28, %r6, %r6
	or %r5, %r6, %r6
	bl {vg_sm4_expand_key_core}
	li %r0, 0
	std %r0, 240(%r29)
	std %r0, 248(%r29)
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	or %r3, %r29, %r29
	addi %r4, %r31, 96
	addi %r5, %r29, 240
	li %r6, 1
	or %r7, %r28, %r28
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
	li %r4, 0
	li %r6, 402
	bl {vg_sm4_prepare_keys}
	or %r3, %r7, %r7
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 22f
24:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 784(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 788(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 792(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 796(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 800(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 804(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 808(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 812(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 816(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 820(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 824(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 828(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 832(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 836(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 840(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 844(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 848(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 852(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 856(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 860(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 864(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 868(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 872(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 876(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 880(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 884(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 888(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 892(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 896(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 900(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 904(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 908(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 912(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 916(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 920(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 924(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 928(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 932(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 936(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 940(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 944(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 948(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 952(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 956(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 960(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 964(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 968(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 972(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 976(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 980(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 984(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 988(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 992(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 996(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1000(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1004(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 1008(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 1012(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1016(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1020(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	lwz %r8, 16(%r31)
	lwz %r9, 784(%r5)
	xor %r8, %r8, %r9
	stw %r8, 16(%r31)
	lwz %r8, 20(%r31)
	lwz %r9, 788(%r5)
	xor %r8, %r8, %r9
	stw %r8, 20(%r31)
	lwz %r8, 24(%r31)
	lwz %r9, 792(%r5)
	xor %r8, %r8, %r9
	stw %r8, 24(%r31)
	lwz %r8, 28(%r31)
	lwz %r9, 796(%r5)
	xor %r8, %r8, %r9
	stw %r8, 28(%r31)
	lwz %r8, 32(%r31)
	lwz %r9, 800(%r5)
	xor %r8, %r8, %r9
	stw %r8, 32(%r31)
	lwz %r8, 36(%r31)
	lwz %r9, 804(%r5)
	xor %r8, %r8, %r9
	stw %r8, 36(%r31)
	lwz %r8, 40(%r31)
	lwz %r9, 808(%r5)
	xor %r8, %r8, %r9
	stw %r8, 40(%r31)
	lwz %r8, 44(%r31)
	lwz %r9, 812(%r5)
	xor %r8, %r8, %r9
	stw %r8, 44(%r31)
	lwz %r8, 48(%r31)
	lwz %r9, 816(%r5)
	xor %r8, %r8, %r9
	stw %r8, 48(%r31)
	lwz %r8, 52(%r31)
	lwz %r9, 820(%r5)
	xor %r8, %r8, %r9
	stw %r8, 52(%r31)
	lwz %r8, 56(%r31)
	lwz %r9, 824(%r5)
	xor %r8, %r8, %r9
	stw %r8, 56(%r31)
	lwz %r8, 60(%r31)
	lwz %r9, 828(%r5)
	xor %r8, %r8, %r9
	stw %r8, 60(%r31)
	lwz %r8, 64(%r31)
	lwz %r9, 832(%r5)
	xor %r8, %r8, %r9
	stw %r8, 64(%r31)
	lwz %r8, 68(%r31)
	lwz %r9, 836(%r5)
	xor %r8, %r8, %r9
	stw %r8, 68(%r31)
	lwz %r8, 72(%r31)
	lwz %r9, 840(%r5)
	xor %r8, %r8, %r9
	stw %r8, 72(%r31)
	lwz %r8, 76(%r31)
	lwz %r9, 844(%r5)
	xor %r8, %r8, %r9
	stw %r8, 76(%r31)
	lwz %r8, 80(%r31)
	lwz %r9, 848(%r5)
	xor %r8, %r8, %r9
	stw %r8, 80(%r31)
	lwz %r8, 84(%r31)
	lwz %r9, 852(%r5)
	xor %r8, %r8, %r9
	stw %r8, 84(%r31)
	lwz %r8, 88(%r31)
	lwz %r9, 856(%r5)
	xor %r8, %r8, %r9
	stw %r8, 88(%r31)
	lwz %r8, 92(%r31)
	lwz %r9, 860(%r5)
	xor %r8, %r8, %r9
	stw %r8, 92(%r31)
	lwz %r8, 96(%r31)
	lwz %r9, 864(%r5)
	xor %r8, %r8, %r9
	stw %r8, 96(%r31)
	lwz %r8, 100(%r31)
	lwz %r9, 868(%r5)
	xor %r8, %r8, %r9
	stw %r8, 100(%r31)
	lwz %r8, 104(%r31)
	lwz %r9, 872(%r5)
	xor %r8, %r8, %r9
	stw %r8, 104(%r31)
	lwz %r8, 108(%r31)
	lwz %r9, 876(%r5)
	xor %r8, %r8, %r9
	stw %r8, 108(%r31)
	lwz %r8, 112(%r31)
	lwz %r9, 880(%r5)
	xor %r8, %r8, %r9
	stw %r8, 112(%r31)
	lwz %r8, 116(%r31)
	lwz %r9, 884(%r5)
	xor %r8, %r8, %r9
	stw %r8, 116(%r31)
	lwz %r8, 120(%r31)
	lwz %r9, 888(%r5)
	xor %r8, %r8, %r9
	stw %r8, 120(%r31)
	lwz %r8, 124(%r31)
	lwz %r9, 892(%r5)
	xor %r8, %r8, %r9
	stw %r8, 124(%r31)
	lwz %r8, 128(%r31)
	lwz %r9, 896(%r5)
	xor %r8, %r8, %r9
	stw %r8, 128(%r31)
	lwz %r8, 132(%r31)
	lwz %r9, 900(%r5)
	xor %r8, %r8, %r9
	stw %r8, 132(%r31)
	lwz %r8, 136(%r31)
	lwz %r9, 904(%r5)
	xor %r8, %r8, %r9
	stw %r8, 136(%r31)
	lwz %r8, 140(%r31)
	lwz %r9, 908(%r5)
	xor %r8, %r8, %r9
	stw %r8, 140(%r31)
	lwz %r8, 144(%r31)
	lwz %r9, 912(%r5)
	xor %r8, %r8, %r9
	stw %r8, 144(%r31)
	lwz %r8, 148(%r31)
	lwz %r9, 916(%r5)
	xor %r8, %r8, %r9
	stw %r8, 148(%r31)
	lwz %r8, 152(%r31)
	lwz %r9, 920(%r5)
	xor %r8, %r8, %r9
	stw %r8, 152(%r31)
	lwz %r8, 156(%r31)
	lwz %r9, 924(%r5)
	xor %r8, %r8, %r9
	stw %r8, 156(%r31)
	lwz %r8, 160(%r31)
	lwz %r9, 928(%r5)
	xor %r8, %r8, %r9
	stw %r8, 160(%r31)
	lwz %r8, 164(%r31)
	lwz %r9, 932(%r5)
	xor %r8, %r8, %r9
	stw %r8, 164(%r31)
	lwz %r8, 168(%r31)
	lwz %r9, 936(%r5)
	xor %r8, %r8, %r9
	stw %r8, 168(%r31)
	lwz %r8, 172(%r31)
	lwz %r9, 940(%r5)
	xor %r8, %r8, %r9
	stw %r8, 172(%r31)
	lwz %r8, 176(%r31)
	lwz %r9, 944(%r5)
	xor %r8, %r8, %r9
	stw %r8, 176(%r31)
	lwz %r8, 180(%r31)
	lwz %r9, 948(%r5)
	xor %r8, %r8, %r9
	stw %r8, 180(%r31)
	lwz %r8, 184(%r31)
	lwz %r9, 952(%r5)
	xor %r8, %r8, %r9
	stw %r8, 184(%r31)
	lwz %r8, 188(%r31)
	lwz %r9, 956(%r5)
	xor %r8, %r8, %r9
	stw %r8, 188(%r31)
	lwz %r8, 192(%r31)
	lwz %r9, 960(%r5)
	xor %r8, %r8, %r9
	stw %r8, 192(%r31)
	lwz %r8, 196(%r31)
	lwz %r9, 964(%r5)
	xor %r8, %r8, %r9
	stw %r8, 196(%r31)
	lwz %r8, 200(%r31)
	lwz %r9, 968(%r5)
	xor %r8, %r8, %r9
	stw %r8, 200(%r31)
	lwz %r8, 204(%r31)
	lwz %r9, 972(%r5)
	xor %r8, %r8, %r9
	stw %r8, 204(%r31)
	lwz %r8, 208(%r31)
	lwz %r9, 976(%r5)
	xor %r8, %r8, %r9
	stw %r8, 208(%r31)
	lwz %r8, 212(%r31)
	lwz %r9, 980(%r5)
	xor %r8, %r8, %r9
	stw %r8, 212(%r31)
	lwz %r8, 216(%r31)
	lwz %r9, 984(%r5)
	xor %r8, %r8, %r9
	stw %r8, 216(%r31)
	lwz %r8, 220(%r31)
	lwz %r9, 988(%r5)
	xor %r8, %r8, %r9
	stw %r8, 220(%r31)
	lwz %r8, 224(%r31)
	lwz %r9, 992(%r5)
	xor %r8, %r8, %r9
	stw %r8, 224(%r31)
	lwz %r8, 228(%r31)
	lwz %r9, 996(%r5)
	xor %r8, %r8, %r9
	stw %r8, 228(%r31)
	lwz %r8, 232(%r31)
	lwz %r9, 1000(%r5)
	xor %r8, %r8, %r9
	stw %r8, 232(%r31)
	lwz %r8, 236(%r31)
	lwz %r9, 1004(%r5)
	xor %r8, %r8, %r9
	stw %r8, 236(%r31)
	lwz %r8, 240(%r31)
	lwz %r9, 1008(%r5)
	xor %r8, %r8, %r9
	stw %r8, 240(%r31)
	lwz %r8, 244(%r31)
	lwz %r9, 1012(%r5)
	xor %r8, %r8, %r9
	stw %r8, 244(%r31)
	lwz %r8, 248(%r31)
	lwz %r9, 1016(%r5)
	xor %r8, %r8, %r9
	stw %r8, 248(%r31)
	lwz %r8, 252(%r31)
	lwz %r9, 1020(%r5)
	xor %r8, %r8, %r9
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
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
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
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	bl {vg_sm4_serial_encrypt}
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
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
	or %r12, %r31, %r31
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r18, 128(%r12)
	ld %r19, 136(%r12)
	ld %r20, 144(%r12)
	ld %r21, 152(%r12)
	ld %r22, 160(%r12)
	ld %r23, 168(%r12)
	ld %r24, 176(%r12)
	ld %r25, 184(%r12)
	ld %r26, 192(%r12)
	ld %r27, 200(%r12)
	ld %r28, 208(%r12)
	ld %r29, 216(%r12)
	ld %r30, 224(%r12)
	ld %r31, 232(%r12)
	addi %r1, %r1, 3296
	addi %r1, %r1, 320
	li %r0, 0
	stdu %r1, -3616(%r1)
	addi %r12, %r1, 32
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
	addi %r1, %r1, 3616
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

vg_sm4_gcm_seal:
	stdu %r1, -400(%r1)
	addi %r12, %r1, 0
	addi %r0, %r12, 104
	std %r0, 96(%r12)
	stdu %r1, -3376(%r1)
	addi %r12, %r1, 0
	ld %r0, 3472(%r12)
	std %r0, 96(%r12)
	addi %r0, %r12, 112
	std %r0, 104(%r12)
	addi %r12, %r1, 0
	ld %r12, 96(%r12)
	std %r18, 128(%r12)
	std %r19, 136(%r12)
	std %r20, 144(%r12)
	std %r21, 152(%r12)
	std %r22, 160(%r12)
	std %r23, 168(%r12)
	std %r24, 176(%r12)
	std %r25, 184(%r12)
	std %r26, 192(%r12)
	std %r27, 200(%r12)
	std %r28, 208(%r12)
	std %r29, 216(%r12)
	std %r30, 224(%r12)
	std %r31, 232(%r12)
	mflr %r0
	std %r0, 240(%r12)
	or %r31, %r12, %r12
	or %r29, %r3, %r3
	addi %r30, %r31, 16
	or %r24, %r4, %r4
	or %r25, %r5, %r5
	or %r18, %r5, %r5
	or %r21, %r6, %r6
	or %r22, %r7, %r7
	or %r27, %r8, %r8
	or %r23, %r9, %r9
	or %r20, %r10, %r10
	addi %r12, %r1, 0
	ld %r28, 104(%r12)
	addi %r6, %r25, -12
	cmpldi %cr0, %r6, 0
	beq %cr0, 20f
	li %r0, 0
	std %r0, 0(%r30)
	std %r0, 8(%r30)
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 22f
	cmpldi %cr0, %r26, 0
	beq %cr0, 24f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 26f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 28f
	b 29f
28:
	or %r5, %r25, %r25
29:
	b 27f
26:
27:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
210:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 210b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 211f
	b 212f
211:
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r5, %r30, 32
	li %r6, 1
	bl {vg_ghash}
212:
	b 25f
24:
25:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 213f
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	bl {vg_ghash}
	b 214f
213:
214:
	cmpldi %cr0, %r25, 0
	beq %cr0, 215f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
217:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 217b
	b 216f
215:
216:
	b 23f
22:
23:
	li %r0, 15
	and %r26, %r18, %r0
	cmpldi %cr0, %r26, 0
	beq %cr0, 218f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
220:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 220b
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r5, %r31, 96
	li %r6, 1
	bl {vg_ghash}
	b 219f
218:
219:
	li %r24, 0
	or %r26, %r18, %r18
	rldicr %r3, %r24, 3, 60
	rldicr %r4, %r26, 3, 60
	addi %r5, %r31, 96
	li %r6, 0
	stdbrx %r3, %r5, %r6
	li %r6, 8
	stdbrx %r4, %r5, %r6
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r5, %r31, 96
	li %r6, 1
	bl {vg_ghash}
	b 21f
20:
	lwz %r3, 0(%r24)
	lwz %r4, 4(%r24)
	lwz %r5, 8(%r24)
	lis %r6, 256
	stw %r3, 0(%r30)
	stw %r4, 4(%r30)
	stw %r5, 8(%r30)
	stw %r6, 12(%r30)
21:
	lwz %r3, 0(%r30)
	lwz %r4, 4(%r30)
	lwz %r5, 8(%r30)
	addi %r7, %r30, 12
	li %r8, 0
	lwbrx %r6, %r7, %r8
	addi %r6, %r6, 1
	stw %r3, 48(%r30)
	stw %r4, 52(%r30)
	stw %r5, 56(%r30)
	addi %r7, %r30, 60
	stwbrx %r6, %r7, %r8
	std %r8, 16(%r30)
	std %r8, 24(%r30)
	or %r24, %r21, %r21
	or %r25, %r22, %r22
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 221f
	cmpldi %cr0, %r26, 0
	beq %cr0, 223f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 225f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 227f
	b 228f
227:
	or %r5, %r25, %r25
228:
	b 226f
225:
226:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
229:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 229b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 230f
	b 231f
230:
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r30, 32
	li %r6, 1
	bl {vg_ghash}
231:
	b 224f
223:
224:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 232f
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	bl {vg_ghash}
	b 233f
232:
233:
	cmpldi %cr0, %r25, 0
	beq %cr0, 234f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
236:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 236b
	b 235f
234:
235:
	b 222f
221:
222:
	li %r0, 15
	and %r26, %r22, %r0
	cmpldi %cr0, %r26, 0
	beq %cr0, 237f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
239:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 239b
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	bl {vg_ghash}
	b 238f
237:
238:
	or %r24, %r27, %r27
	or %r25, %r23, %r23
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 240f
	cmpldi %cr0, %r26, 0
	beq %cr0, 242f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 244f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 246f
	b 247f
246:
	or %r5, %r25, %r25
247:
	b 245f
244:
245:
	addi %r3, %r30, 64
	add %r3, %r3, %r26
	or %r4, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
248:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 248b
	b 243f
242:
243:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 249f
	or %r3, %r29, %r29
	addi %r4, %r30, 48
	or %r7, %r28, %r28
	rldicl %r8, %r6, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 251f
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
	li %r4, 0
	li %r6, 402
	bl {vg_sm4_prepare_keys}
	or %r3, %r7, %r7
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 253f
255:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 784(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 788(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 792(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 796(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 800(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 804(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 808(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 812(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 816(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 820(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 824(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 828(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 832(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 836(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 840(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 844(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 848(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 852(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 856(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 860(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 864(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 868(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 872(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 876(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 880(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 884(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 888(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 892(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 896(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 900(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 904(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 908(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 912(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 916(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 920(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 924(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 928(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 932(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 936(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 940(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 944(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 948(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 952(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 956(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 960(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 964(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 968(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 972(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 976(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 980(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 984(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 988(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 992(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 996(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1000(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1004(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 1008(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 1012(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1016(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1020(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	lwz %r8, 16(%r31)
	lwz %r9, 784(%r5)
	xor %r8, %r8, %r9
	stw %r8, 16(%r31)
	lwz %r8, 20(%r31)
	lwz %r9, 788(%r5)
	xor %r8, %r8, %r9
	stw %r8, 20(%r31)
	lwz %r8, 24(%r31)
	lwz %r9, 792(%r5)
	xor %r8, %r8, %r9
	stw %r8, 24(%r31)
	lwz %r8, 28(%r31)
	lwz %r9, 796(%r5)
	xor %r8, %r8, %r9
	stw %r8, 28(%r31)
	lwz %r8, 32(%r31)
	lwz %r9, 800(%r5)
	xor %r8, %r8, %r9
	stw %r8, 32(%r31)
	lwz %r8, 36(%r31)
	lwz %r9, 804(%r5)
	xor %r8, %r8, %r9
	stw %r8, 36(%r31)
	lwz %r8, 40(%r31)
	lwz %r9, 808(%r5)
	xor %r8, %r8, %r9
	stw %r8, 40(%r31)
	lwz %r8, 44(%r31)
	lwz %r9, 812(%r5)
	xor %r8, %r8, %r9
	stw %r8, 44(%r31)
	lwz %r8, 48(%r31)
	lwz %r9, 816(%r5)
	xor %r8, %r8, %r9
	stw %r8, 48(%r31)
	lwz %r8, 52(%r31)
	lwz %r9, 820(%r5)
	xor %r8, %r8, %r9
	stw %r8, 52(%r31)
	lwz %r8, 56(%r31)
	lwz %r9, 824(%r5)
	xor %r8, %r8, %r9
	stw %r8, 56(%r31)
	lwz %r8, 60(%r31)
	lwz %r9, 828(%r5)
	xor %r8, %r8, %r9
	stw %r8, 60(%r31)
	lwz %r8, 64(%r31)
	lwz %r9, 832(%r5)
	xor %r8, %r8, %r9
	stw %r8, 64(%r31)
	lwz %r8, 68(%r31)
	lwz %r9, 836(%r5)
	xor %r8, %r8, %r9
	stw %r8, 68(%r31)
	lwz %r8, 72(%r31)
	lwz %r9, 840(%r5)
	xor %r8, %r8, %r9
	stw %r8, 72(%r31)
	lwz %r8, 76(%r31)
	lwz %r9, 844(%r5)
	xor %r8, %r8, %r9
	stw %r8, 76(%r31)
	lwz %r8, 80(%r31)
	lwz %r9, 848(%r5)
	xor %r8, %r8, %r9
	stw %r8, 80(%r31)
	lwz %r8, 84(%r31)
	lwz %r9, 852(%r5)
	xor %r8, %r8, %r9
	stw %r8, 84(%r31)
	lwz %r8, 88(%r31)
	lwz %r9, 856(%r5)
	xor %r8, %r8, %r9
	stw %r8, 88(%r31)
	lwz %r8, 92(%r31)
	lwz %r9, 860(%r5)
	xor %r8, %r8, %r9
	stw %r8, 92(%r31)
	lwz %r8, 96(%r31)
	lwz %r9, 864(%r5)
	xor %r8, %r8, %r9
	stw %r8, 96(%r31)
	lwz %r8, 100(%r31)
	lwz %r9, 868(%r5)
	xor %r8, %r8, %r9
	stw %r8, 100(%r31)
	lwz %r8, 104(%r31)
	lwz %r9, 872(%r5)
	xor %r8, %r8, %r9
	stw %r8, 104(%r31)
	lwz %r8, 108(%r31)
	lwz %r9, 876(%r5)
	xor %r8, %r8, %r9
	stw %r8, 108(%r31)
	lwz %r8, 112(%r31)
	lwz %r9, 880(%r5)
	xor %r8, %r8, %r9
	stw %r8, 112(%r31)
	lwz %r8, 116(%r31)
	lwz %r9, 884(%r5)
	xor %r8, %r8, %r9
	stw %r8, 116(%r31)
	lwz %r8, 120(%r31)
	lwz %r9, 888(%r5)
	xor %r8, %r8, %r9
	stw %r8, 120(%r31)
	lwz %r8, 124(%r31)
	lwz %r9, 892(%r5)
	xor %r8, %r8, %r9
	stw %r8, 124(%r31)
	lwz %r8, 128(%r31)
	lwz %r9, 896(%r5)
	xor %r8, %r8, %r9
	stw %r8, 128(%r31)
	lwz %r8, 132(%r31)
	lwz %r9, 900(%r5)
	xor %r8, %r8, %r9
	stw %r8, 132(%r31)
	lwz %r8, 136(%r31)
	lwz %r9, 904(%r5)
	xor %r8, %r8, %r9
	stw %r8, 136(%r31)
	lwz %r8, 140(%r31)
	lwz %r9, 908(%r5)
	xor %r8, %r8, %r9
	stw %r8, 140(%r31)
	lwz %r8, 144(%r31)
	lwz %r9, 912(%r5)
	xor %r8, %r8, %r9
	stw %r8, 144(%r31)
	lwz %r8, 148(%r31)
	lwz %r9, 916(%r5)
	xor %r8, %r8, %r9
	stw %r8, 148(%r31)
	lwz %r8, 152(%r31)
	lwz %r9, 920(%r5)
	xor %r8, %r8, %r9
	stw %r8, 152(%r31)
	lwz %r8, 156(%r31)
	lwz %r9, 924(%r5)
	xor %r8, %r8, %r9
	stw %r8, 156(%r31)
	lwz %r8, 160(%r31)
	lwz %r9, 928(%r5)
	xor %r8, %r8, %r9
	stw %r8, 160(%r31)
	lwz %r8, 164(%r31)
	lwz %r9, 932(%r5)
	xor %r8, %r8, %r9
	stw %r8, 164(%r31)
	lwz %r8, 168(%r31)
	lwz %r9, 936(%r5)
	xor %r8, %r8, %r9
	stw %r8, 168(%r31)
	lwz %r8, 172(%r31)
	lwz %r9, 940(%r5)
	xor %r8, %r8, %r9
	stw %r8, 172(%r31)
	lwz %r8, 176(%r31)
	lwz %r9, 944(%r5)
	xor %r8, %r8, %r9
	stw %r8, 176(%r31)
	lwz %r8, 180(%r31)
	lwz %r9, 948(%r5)
	xor %r8, %r8, %r9
	stw %r8, 180(%r31)
	lwz %r8, 184(%r31)
	lwz %r9, 952(%r5)
	xor %r8, %r8, %r9
	stw %r8, 184(%r31)
	lwz %r8, 188(%r31)
	lwz %r9, 956(%r5)
	xor %r8, %r8, %r9
	stw %r8, 188(%r31)
	lwz %r8, 192(%r31)
	lwz %r9, 960(%r5)
	xor %r8, %r8, %r9
	stw %r8, 192(%r31)
	lwz %r8, 196(%r31)
	lwz %r9, 964(%r5)
	xor %r8, %r8, %r9
	stw %r8, 196(%r31)
	lwz %r8, 200(%r31)
	lwz %r9, 968(%r5)
	xor %r8, %r8, %r9
	stw %r8, 200(%r31)
	lwz %r8, 204(%r31)
	lwz %r9, 972(%r5)
	xor %r8, %r8, %r9
	stw %r8, 204(%r31)
	lwz %r8, 208(%r31)
	lwz %r9, 976(%r5)
	xor %r8, %r8, %r9
	stw %r8, 208(%r31)
	lwz %r8, 212(%r31)
	lwz %r9, 980(%r5)
	xor %r8, %r8, %r9
	stw %r8, 212(%r31)
	lwz %r8, 216(%r31)
	lwz %r9, 984(%r5)
	xor %r8, %r8, %r9
	stw %r8, 216(%r31)
	lwz %r8, 220(%r31)
	lwz %r9, 988(%r5)
	xor %r8, %r8, %r9
	stw %r8, 220(%r31)
	lwz %r8, 224(%r31)
	lwz %r9, 992(%r5)
	xor %r8, %r8, %r9
	stw %r8, 224(%r31)
	lwz %r8, 228(%r31)
	lwz %r9, 996(%r5)
	xor %r8, %r8, %r9
	stw %r8, 228(%r31)
	lwz %r8, 232(%r31)
	lwz %r9, 1000(%r5)
	xor %r8, %r8, %r9
	stw %r8, 232(%r31)
	lwz %r8, 236(%r31)
	lwz %r9, 1004(%r5)
	xor %r8, %r8, %r9
	stw %r8, 236(%r31)
	lwz %r8, 240(%r31)
	lwz %r9, 1008(%r5)
	xor %r8, %r8, %r9
	stw %r8, 240(%r31)
	lwz %r8, 244(%r31)
	lwz %r9, 1012(%r5)
	xor %r8, %r8, %r9
	stw %r8, 244(%r31)
	lwz %r8, 248(%r31)
	lwz %r9, 1016(%r5)
	xor %r8, %r8, %r9
	stw %r8, 248(%r31)
	lwz %r8, 252(%r31)
	lwz %r9, 1020(%r5)
	xor %r8, %r8, %r9
	stw %r8, 252(%r31)
	addi %r31, %r31, 256
	addi %r30, %r30, -16
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	bne %cr0, 255b
	b 254f
253:
254:
	cmpldi %cr0, %r30, 0
	beq %cr0, 256f
258:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 258b
	b 257f
256:
257:
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
	b 252f
251:
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
	beq %cr0, 259f
261:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	bl {vg_sm4_serial_encrypt}
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 261b
	b 260f
259:
260:
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
252:
	b 250f
249:
250:
	cmpldi %cr0, %r25, 0
	beq %cr0, 262f
	li %r0, 0
	std %r0, 64(%r30)
	std %r0, 72(%r30)
	addi %r5, %r30, 64
	li %r6, 1
	or %r3, %r29, %r29
	addi %r4, %r30, 48
	or %r7, %r28, %r28
	rldicl %r8, %r6, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 264f
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
	li %r4, 0
	li %r6, 402
	bl {vg_sm4_prepare_keys}
	or %r3, %r7, %r7
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 266f
268:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 784(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 788(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 792(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 796(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 800(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 804(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 808(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 812(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 816(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 820(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 824(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 828(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 832(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 836(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 840(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 844(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 848(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 852(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 856(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 860(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 864(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 868(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 872(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 876(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 880(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 884(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 888(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 892(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 896(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 900(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 904(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 908(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 912(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 916(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 920(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 924(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 928(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 932(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 936(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 940(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 944(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 948(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 952(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 956(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 960(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 964(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 968(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 972(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 976(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 980(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 984(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 988(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 992(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 996(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1000(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1004(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 1008(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 1012(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1016(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1020(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	lwz %r8, 16(%r31)
	lwz %r9, 784(%r5)
	xor %r8, %r8, %r9
	stw %r8, 16(%r31)
	lwz %r8, 20(%r31)
	lwz %r9, 788(%r5)
	xor %r8, %r8, %r9
	stw %r8, 20(%r31)
	lwz %r8, 24(%r31)
	lwz %r9, 792(%r5)
	xor %r8, %r8, %r9
	stw %r8, 24(%r31)
	lwz %r8, 28(%r31)
	lwz %r9, 796(%r5)
	xor %r8, %r8, %r9
	stw %r8, 28(%r31)
	lwz %r8, 32(%r31)
	lwz %r9, 800(%r5)
	xor %r8, %r8, %r9
	stw %r8, 32(%r31)
	lwz %r8, 36(%r31)
	lwz %r9, 804(%r5)
	xor %r8, %r8, %r9
	stw %r8, 36(%r31)
	lwz %r8, 40(%r31)
	lwz %r9, 808(%r5)
	xor %r8, %r8, %r9
	stw %r8, 40(%r31)
	lwz %r8, 44(%r31)
	lwz %r9, 812(%r5)
	xor %r8, %r8, %r9
	stw %r8, 44(%r31)
	lwz %r8, 48(%r31)
	lwz %r9, 816(%r5)
	xor %r8, %r8, %r9
	stw %r8, 48(%r31)
	lwz %r8, 52(%r31)
	lwz %r9, 820(%r5)
	xor %r8, %r8, %r9
	stw %r8, 52(%r31)
	lwz %r8, 56(%r31)
	lwz %r9, 824(%r5)
	xor %r8, %r8, %r9
	stw %r8, 56(%r31)
	lwz %r8, 60(%r31)
	lwz %r9, 828(%r5)
	xor %r8, %r8, %r9
	stw %r8, 60(%r31)
	lwz %r8, 64(%r31)
	lwz %r9, 832(%r5)
	xor %r8, %r8, %r9
	stw %r8, 64(%r31)
	lwz %r8, 68(%r31)
	lwz %r9, 836(%r5)
	xor %r8, %r8, %r9
	stw %r8, 68(%r31)
	lwz %r8, 72(%r31)
	lwz %r9, 840(%r5)
	xor %r8, %r8, %r9
	stw %r8, 72(%r31)
	lwz %r8, 76(%r31)
	lwz %r9, 844(%r5)
	xor %r8, %r8, %r9
	stw %r8, 76(%r31)
	lwz %r8, 80(%r31)
	lwz %r9, 848(%r5)
	xor %r8, %r8, %r9
	stw %r8, 80(%r31)
	lwz %r8, 84(%r31)
	lwz %r9, 852(%r5)
	xor %r8, %r8, %r9
	stw %r8, 84(%r31)
	lwz %r8, 88(%r31)
	lwz %r9, 856(%r5)
	xor %r8, %r8, %r9
	stw %r8, 88(%r31)
	lwz %r8, 92(%r31)
	lwz %r9, 860(%r5)
	xor %r8, %r8, %r9
	stw %r8, 92(%r31)
	lwz %r8, 96(%r31)
	lwz %r9, 864(%r5)
	xor %r8, %r8, %r9
	stw %r8, 96(%r31)
	lwz %r8, 100(%r31)
	lwz %r9, 868(%r5)
	xor %r8, %r8, %r9
	stw %r8, 100(%r31)
	lwz %r8, 104(%r31)
	lwz %r9, 872(%r5)
	xor %r8, %r8, %r9
	stw %r8, 104(%r31)
	lwz %r8, 108(%r31)
	lwz %r9, 876(%r5)
	xor %r8, %r8, %r9
	stw %r8, 108(%r31)
	lwz %r8, 112(%r31)
	lwz %r9, 880(%r5)
	xor %r8, %r8, %r9
	stw %r8, 112(%r31)
	lwz %r8, 116(%r31)
	lwz %r9, 884(%r5)
	xor %r8, %r8, %r9
	stw %r8, 116(%r31)
	lwz %r8, 120(%r31)
	lwz %r9, 888(%r5)
	xor %r8, %r8, %r9
	stw %r8, 120(%r31)
	lwz %r8, 124(%r31)
	lwz %r9, 892(%r5)
	xor %r8, %r8, %r9
	stw %r8, 124(%r31)
	lwz %r8, 128(%r31)
	lwz %r9, 896(%r5)
	xor %r8, %r8, %r9
	stw %r8, 128(%r31)
	lwz %r8, 132(%r31)
	lwz %r9, 900(%r5)
	xor %r8, %r8, %r9
	stw %r8, 132(%r31)
	lwz %r8, 136(%r31)
	lwz %r9, 904(%r5)
	xor %r8, %r8, %r9
	stw %r8, 136(%r31)
	lwz %r8, 140(%r31)
	lwz %r9, 908(%r5)
	xor %r8, %r8, %r9
	stw %r8, 140(%r31)
	lwz %r8, 144(%r31)
	lwz %r9, 912(%r5)
	xor %r8, %r8, %r9
	stw %r8, 144(%r31)
	lwz %r8, 148(%r31)
	lwz %r9, 916(%r5)
	xor %r8, %r8, %r9
	stw %r8, 148(%r31)
	lwz %r8, 152(%r31)
	lwz %r9, 920(%r5)
	xor %r8, %r8, %r9
	stw %r8, 152(%r31)
	lwz %r8, 156(%r31)
	lwz %r9, 924(%r5)
	xor %r8, %r8, %r9
	stw %r8, 156(%r31)
	lwz %r8, 160(%r31)
	lwz %r9, 928(%r5)
	xor %r8, %r8, %r9
	stw %r8, 160(%r31)
	lwz %r8, 164(%r31)
	lwz %r9, 932(%r5)
	xor %r8, %r8, %r9
	stw %r8, 164(%r31)
	lwz %r8, 168(%r31)
	lwz %r9, 936(%r5)
	xor %r8, %r8, %r9
	stw %r8, 168(%r31)
	lwz %r8, 172(%r31)
	lwz %r9, 940(%r5)
	xor %r8, %r8, %r9
	stw %r8, 172(%r31)
	lwz %r8, 176(%r31)
	lwz %r9, 944(%r5)
	xor %r8, %r8, %r9
	stw %r8, 176(%r31)
	lwz %r8, 180(%r31)
	lwz %r9, 948(%r5)
	xor %r8, %r8, %r9
	stw %r8, 180(%r31)
	lwz %r8, 184(%r31)
	lwz %r9, 952(%r5)
	xor %r8, %r8, %r9
	stw %r8, 184(%r31)
	lwz %r8, 188(%r31)
	lwz %r9, 956(%r5)
	xor %r8, %r8, %r9
	stw %r8, 188(%r31)
	lwz %r8, 192(%r31)
	lwz %r9, 960(%r5)
	xor %r8, %r8, %r9
	stw %r8, 192(%r31)
	lwz %r8, 196(%r31)
	lwz %r9, 964(%r5)
	xor %r8, %r8, %r9
	stw %r8, 196(%r31)
	lwz %r8, 200(%r31)
	lwz %r9, 968(%r5)
	xor %r8, %r8, %r9
	stw %r8, 200(%r31)
	lwz %r8, 204(%r31)
	lwz %r9, 972(%r5)
	xor %r8, %r8, %r9
	stw %r8, 204(%r31)
	lwz %r8, 208(%r31)
	lwz %r9, 976(%r5)
	xor %r8, %r8, %r9
	stw %r8, 208(%r31)
	lwz %r8, 212(%r31)
	lwz %r9, 980(%r5)
	xor %r8, %r8, %r9
	stw %r8, 212(%r31)
	lwz %r8, 216(%r31)
	lwz %r9, 984(%r5)
	xor %r8, %r8, %r9
	stw %r8, 216(%r31)
	lwz %r8, 220(%r31)
	lwz %r9, 988(%r5)
	xor %r8, %r8, %r9
	stw %r8, 220(%r31)
	lwz %r8, 224(%r31)
	lwz %r9, 992(%r5)
	xor %r8, %r8, %r9
	stw %r8, 224(%r31)
	lwz %r8, 228(%r31)
	lwz %r9, 996(%r5)
	xor %r8, %r8, %r9
	stw %r8, 228(%r31)
	lwz %r8, 232(%r31)
	lwz %r9, 1000(%r5)
	xor %r8, %r8, %r9
	stw %r8, 232(%r31)
	lwz %r8, 236(%r31)
	lwz %r9, 1004(%r5)
	xor %r8, %r8, %r9
	stw %r8, 236(%r31)
	lwz %r8, 240(%r31)
	lwz %r9, 1008(%r5)
	xor %r8, %r8, %r9
	stw %r8, 240(%r31)
	lwz %r8, 244(%r31)
	lwz %r9, 1012(%r5)
	xor %r8, %r8, %r9
	stw %r8, 244(%r31)
	lwz %r8, 248(%r31)
	lwz %r9, 1016(%r5)
	xor %r8, %r8, %r9
	stw %r8, 248(%r31)
	lwz %r8, 252(%r31)
	lwz %r9, 1020(%r5)
	xor %r8, %r8, %r9
	stw %r8, 252(%r31)
	addi %r31, %r31, 256
	addi %r30, %r30, -16
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	bne %cr0, 268b
	b 267f
266:
267:
	cmpldi %cr0, %r30, 0
	beq %cr0, 269f
271:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 271b
	b 270f
269:
270:
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
	b 265f
264:
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
	beq %cr0, 272f
274:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	bl {vg_sm4_serial_encrypt}
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 274b
	b 273f
272:
273:
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
265:
	addi %r3, %r30, 64
	or %r4, %r24, %r24
	or %r5, %r25, %r25
275:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 275b
	b 263f
262:
263:
	b 241f
240:
241:
	or %r24, %r27, %r27
	or %r25, %r23, %r23
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 276f
	cmpldi %cr0, %r26, 0
	beq %cr0, 278f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 280f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 282f
	b 283f
282:
	or %r5, %r25, %r25
283:
	b 281f
280:
281:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
284:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 284b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 285f
	b 286f
285:
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r30, 32
	li %r6, 1
	bl {vg_ghash}
286:
	b 279f
278:
279:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 287f
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	bl {vg_ghash}
	b 288f
287:
288:
	cmpldi %cr0, %r25, 0
	beq %cr0, 289f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
291:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 291b
	b 290f
289:
290:
	b 277f
276:
277:
	li %r0, 15
	and %r26, %r23, %r0
	cmpldi %cr0, %r26, 0
	beq %cr0, 292f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
294:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 294b
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	bl {vg_ghash}
	b 293f
292:
293:
	or %r24, %r22, %r22
	or %r26, %r23, %r23
	rldicr %r3, %r24, 3, 60
	rldicr %r4, %r26, 3, 60
	addi %r5, %r31, 96
	li %r6, 0
	stdbrx %r3, %r5, %r6
	li %r6, 8
	stdbrx %r4, %r5, %r6
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	bl {vg_ghash}
	ld %r3, 16(%r30)
	std %r3, 0(%r31)
	ld %r3, 24(%r30)
	std %r3, 8(%r31)
	or %r3, %r29, %r29
	or %r4, %r30, %r30
	addi %r5, %r31, 0
	li %r6, 1
	or %r7, %r28, %r28
	rldicl %r8, %r6, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 295f
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
	li %r4, 0
	li %r6, 402
	bl {vg_sm4_prepare_keys}
	or %r3, %r7, %r7
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 297f
299:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 784(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 788(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 792(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 796(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 800(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 804(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 808(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 812(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 816(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 820(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 824(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 828(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 832(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 836(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 840(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 844(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 848(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 852(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 856(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 860(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 864(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 868(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 872(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 876(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 880(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 884(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 888(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 892(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 896(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 900(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 904(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 908(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 912(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 916(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 920(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 924(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 928(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 932(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 936(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 940(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 944(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 948(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 952(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 956(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 960(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 964(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 968(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 972(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 976(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 980(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 984(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 988(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 992(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 996(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1000(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1004(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 1008(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 1012(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1016(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1020(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	lwz %r8, 16(%r31)
	lwz %r9, 784(%r5)
	xor %r8, %r8, %r9
	stw %r8, 16(%r31)
	lwz %r8, 20(%r31)
	lwz %r9, 788(%r5)
	xor %r8, %r8, %r9
	stw %r8, 20(%r31)
	lwz %r8, 24(%r31)
	lwz %r9, 792(%r5)
	xor %r8, %r8, %r9
	stw %r8, 24(%r31)
	lwz %r8, 28(%r31)
	lwz %r9, 796(%r5)
	xor %r8, %r8, %r9
	stw %r8, 28(%r31)
	lwz %r8, 32(%r31)
	lwz %r9, 800(%r5)
	xor %r8, %r8, %r9
	stw %r8, 32(%r31)
	lwz %r8, 36(%r31)
	lwz %r9, 804(%r5)
	xor %r8, %r8, %r9
	stw %r8, 36(%r31)
	lwz %r8, 40(%r31)
	lwz %r9, 808(%r5)
	xor %r8, %r8, %r9
	stw %r8, 40(%r31)
	lwz %r8, 44(%r31)
	lwz %r9, 812(%r5)
	xor %r8, %r8, %r9
	stw %r8, 44(%r31)
	lwz %r8, 48(%r31)
	lwz %r9, 816(%r5)
	xor %r8, %r8, %r9
	stw %r8, 48(%r31)
	lwz %r8, 52(%r31)
	lwz %r9, 820(%r5)
	xor %r8, %r8, %r9
	stw %r8, 52(%r31)
	lwz %r8, 56(%r31)
	lwz %r9, 824(%r5)
	xor %r8, %r8, %r9
	stw %r8, 56(%r31)
	lwz %r8, 60(%r31)
	lwz %r9, 828(%r5)
	xor %r8, %r8, %r9
	stw %r8, 60(%r31)
	lwz %r8, 64(%r31)
	lwz %r9, 832(%r5)
	xor %r8, %r8, %r9
	stw %r8, 64(%r31)
	lwz %r8, 68(%r31)
	lwz %r9, 836(%r5)
	xor %r8, %r8, %r9
	stw %r8, 68(%r31)
	lwz %r8, 72(%r31)
	lwz %r9, 840(%r5)
	xor %r8, %r8, %r9
	stw %r8, 72(%r31)
	lwz %r8, 76(%r31)
	lwz %r9, 844(%r5)
	xor %r8, %r8, %r9
	stw %r8, 76(%r31)
	lwz %r8, 80(%r31)
	lwz %r9, 848(%r5)
	xor %r8, %r8, %r9
	stw %r8, 80(%r31)
	lwz %r8, 84(%r31)
	lwz %r9, 852(%r5)
	xor %r8, %r8, %r9
	stw %r8, 84(%r31)
	lwz %r8, 88(%r31)
	lwz %r9, 856(%r5)
	xor %r8, %r8, %r9
	stw %r8, 88(%r31)
	lwz %r8, 92(%r31)
	lwz %r9, 860(%r5)
	xor %r8, %r8, %r9
	stw %r8, 92(%r31)
	lwz %r8, 96(%r31)
	lwz %r9, 864(%r5)
	xor %r8, %r8, %r9
	stw %r8, 96(%r31)
	lwz %r8, 100(%r31)
	lwz %r9, 868(%r5)
	xor %r8, %r8, %r9
	stw %r8, 100(%r31)
	lwz %r8, 104(%r31)
	lwz %r9, 872(%r5)
	xor %r8, %r8, %r9
	stw %r8, 104(%r31)
	lwz %r8, 108(%r31)
	lwz %r9, 876(%r5)
	xor %r8, %r8, %r9
	stw %r8, 108(%r31)
	lwz %r8, 112(%r31)
	lwz %r9, 880(%r5)
	xor %r8, %r8, %r9
	stw %r8, 112(%r31)
	lwz %r8, 116(%r31)
	lwz %r9, 884(%r5)
	xor %r8, %r8, %r9
	stw %r8, 116(%r31)
	lwz %r8, 120(%r31)
	lwz %r9, 888(%r5)
	xor %r8, %r8, %r9
	stw %r8, 120(%r31)
	lwz %r8, 124(%r31)
	lwz %r9, 892(%r5)
	xor %r8, %r8, %r9
	stw %r8, 124(%r31)
	lwz %r8, 128(%r31)
	lwz %r9, 896(%r5)
	xor %r8, %r8, %r9
	stw %r8, 128(%r31)
	lwz %r8, 132(%r31)
	lwz %r9, 900(%r5)
	xor %r8, %r8, %r9
	stw %r8, 132(%r31)
	lwz %r8, 136(%r31)
	lwz %r9, 904(%r5)
	xor %r8, %r8, %r9
	stw %r8, 136(%r31)
	lwz %r8, 140(%r31)
	lwz %r9, 908(%r5)
	xor %r8, %r8, %r9
	stw %r8, 140(%r31)
	lwz %r8, 144(%r31)
	lwz %r9, 912(%r5)
	xor %r8, %r8, %r9
	stw %r8, 144(%r31)
	lwz %r8, 148(%r31)
	lwz %r9, 916(%r5)
	xor %r8, %r8, %r9
	stw %r8, 148(%r31)
	lwz %r8, 152(%r31)
	lwz %r9, 920(%r5)
	xor %r8, %r8, %r9
	stw %r8, 152(%r31)
	lwz %r8, 156(%r31)
	lwz %r9, 924(%r5)
	xor %r8, %r8, %r9
	stw %r8, 156(%r31)
	lwz %r8, 160(%r31)
	lwz %r9, 928(%r5)
	xor %r8, %r8, %r9
	stw %r8, 160(%r31)
	lwz %r8, 164(%r31)
	lwz %r9, 932(%r5)
	xor %r8, %r8, %r9
	stw %r8, 164(%r31)
	lwz %r8, 168(%r31)
	lwz %r9, 936(%r5)
	xor %r8, %r8, %r9
	stw %r8, 168(%r31)
	lwz %r8, 172(%r31)
	lwz %r9, 940(%r5)
	xor %r8, %r8, %r9
	stw %r8, 172(%r31)
	lwz %r8, 176(%r31)
	lwz %r9, 944(%r5)
	xor %r8, %r8, %r9
	stw %r8, 176(%r31)
	lwz %r8, 180(%r31)
	lwz %r9, 948(%r5)
	xor %r8, %r8, %r9
	stw %r8, 180(%r31)
	lwz %r8, 184(%r31)
	lwz %r9, 952(%r5)
	xor %r8, %r8, %r9
	stw %r8, 184(%r31)
	lwz %r8, 188(%r31)
	lwz %r9, 956(%r5)
	xor %r8, %r8, %r9
	stw %r8, 188(%r31)
	lwz %r8, 192(%r31)
	lwz %r9, 960(%r5)
	xor %r8, %r8, %r9
	stw %r8, 192(%r31)
	lwz %r8, 196(%r31)
	lwz %r9, 964(%r5)
	xor %r8, %r8, %r9
	stw %r8, 196(%r31)
	lwz %r8, 200(%r31)
	lwz %r9, 968(%r5)
	xor %r8, %r8, %r9
	stw %r8, 200(%r31)
	lwz %r8, 204(%r31)
	lwz %r9, 972(%r5)
	xor %r8, %r8, %r9
	stw %r8, 204(%r31)
	lwz %r8, 208(%r31)
	lwz %r9, 976(%r5)
	xor %r8, %r8, %r9
	stw %r8, 208(%r31)
	lwz %r8, 212(%r31)
	lwz %r9, 980(%r5)
	xor %r8, %r8, %r9
	stw %r8, 212(%r31)
	lwz %r8, 216(%r31)
	lwz %r9, 984(%r5)
	xor %r8, %r8, %r9
	stw %r8, 216(%r31)
	lwz %r8, 220(%r31)
	lwz %r9, 988(%r5)
	xor %r8, %r8, %r9
	stw %r8, 220(%r31)
	lwz %r8, 224(%r31)
	lwz %r9, 992(%r5)
	xor %r8, %r8, %r9
	stw %r8, 224(%r31)
	lwz %r8, 228(%r31)
	lwz %r9, 996(%r5)
	xor %r8, %r8, %r9
	stw %r8, 228(%r31)
	lwz %r8, 232(%r31)
	lwz %r9, 1000(%r5)
	xor %r8, %r8, %r9
	stw %r8, 232(%r31)
	lwz %r8, 236(%r31)
	lwz %r9, 1004(%r5)
	xor %r8, %r8, %r9
	stw %r8, 236(%r31)
	lwz %r8, 240(%r31)
	lwz %r9, 1008(%r5)
	xor %r8, %r8, %r9
	stw %r8, 240(%r31)
	lwz %r8, 244(%r31)
	lwz %r9, 1012(%r5)
	xor %r8, %r8, %r9
	stw %r8, 244(%r31)
	lwz %r8, 248(%r31)
	lwz %r9, 1016(%r5)
	xor %r8, %r8, %r9
	stw %r8, 248(%r31)
	lwz %r8, 252(%r31)
	lwz %r9, 1020(%r5)
	xor %r8, %r8, %r9
	stw %r8, 252(%r31)
	addi %r31, %r31, 256
	addi %r30, %r30, -16
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	bne %cr0, 299b
	b 298f
297:
298:
	cmpldi %cr0, %r30, 0
	beq %cr0, 2100f
2102:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 2102b
	b 2101f
2100:
2101:
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
	b 296f
295:
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
	beq %cr0, 2103f
2105:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	bl {vg_sm4_serial_encrypt}
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 2105b
	b 2104f
2103:
2104:
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
296:
	ld %r3, 0(%r31)
	std %r3, 0(%r20)
	ld %r3, 8(%r31)
	std %r3, 8(%r20)
	or %r12, %r31, %r31
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r18, 128(%r12)
	ld %r19, 136(%r12)
	ld %r20, 144(%r12)
	ld %r21, 152(%r12)
	ld %r22, 160(%r12)
	ld %r23, 168(%r12)
	ld %r24, 176(%r12)
	ld %r25, 184(%r12)
	ld %r26, 192(%r12)
	ld %r27, 200(%r12)
	ld %r28, 208(%r12)
	ld %r29, 216(%r12)
	ld %r30, 224(%r12)
	ld %r31, 232(%r12)
	addi %r1, %r1, 3376
	addi %r1, %r1, 400
	li %r0, 0
	stdu %r1, -3776(%r1)
	addi %r12, %r1, 32
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
	addi %r1, %r1, 3776
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
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v9, %v9, %v9
	vxor %v10, %v10, %v10
	vxor %v11, %v11, %v11
	vxor %v12, %v12, %v12
	vxor %v13, %v13, %v13
	vxor %v14, %v14, %v14
	vxor %v15, %v15, %v15
	vxor %v16, %v16, %v16
	vxor %v17, %v17, %v17
	vxor %v18, %v18, %v18
	vxor %v19, %v19, %v19
	blr

vg_sm4_gcm_open:
	stdu %r1, -400(%r1)
	addi %r12, %r1, 0
	ld %r0, 496(%r12)
	std %r0, 96(%r12)
	addi %r0, %r12, 112
	std %r0, 104(%r12)
	stdu %r1, -3392(%r1)
	addi %r12, %r1, 0
	ld %r0, 3488(%r12)
	std %r0, 96(%r12)
	ld %r0, 3496(%r12)
	std %r0, 104(%r12)
	addi %r0, %r12, 120
	std %r0, 112(%r12)
	addi %r12, %r1, 0
	ld %r12, 104(%r12)
	std %r18, 128(%r12)
	std %r19, 136(%r12)
	std %r20, 144(%r12)
	std %r21, 152(%r12)
	std %r22, 160(%r12)
	std %r23, 168(%r12)
	std %r24, 176(%r12)
	std %r25, 184(%r12)
	std %r26, 192(%r12)
	std %r27, 200(%r12)
	std %r28, 208(%r12)
	std %r29, 216(%r12)
	std %r30, 224(%r12)
	std %r31, 232(%r12)
	mflr %r0
	std %r0, 240(%r12)
	or %r31, %r12, %r12
	or %r29, %r3, %r3
	addi %r30, %r31, 16
	or %r24, %r4, %r4
	or %r25, %r5, %r5
	or %r18, %r5, %r5
	or %r21, %r6, %r6
	or %r22, %r7, %r7
	or %r27, %r8, %r8
	or %r23, %r9, %r9
	or %r20, %r10, %r10
	addi %r12, %r1, 0
	ld %r28, 112(%r12)
	addi %r12, %r1, 0
	ld %r19, 96(%r12)
	li %r25, 0
	rldicl %r0, %r19, 62, 2
	cmpldi %cr0, %r0, 0
	beq %cr0, 20f
	rldicl %r0, %r19, 60, 4
	cmpldi %cr0, %r0, 0
	beq %cr0, 22f
	addi %r0, %r19, -16
	cmpldi %cr0, %r0, 0
	beq %cr0, 24f
	b 25f
24:
	li %r25, 1
25:
	b 23f
22:
	li %r25, 1
23:
	b 21f
20:
21:
	cmpldi %cr0, %r25, 0
	beq %cr0, 26f
	or %r25, %r18, %r18
	addi %r6, %r25, -12
	cmpldi %cr0, %r6, 0
	beq %cr0, 28f
	li %r0, 0
	std %r0, 0(%r30)
	std %r0, 8(%r30)
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 210f
	cmpldi %cr0, %r26, 0
	beq %cr0, 212f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 214f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 216f
	b 217f
216:
	or %r5, %r25, %r25
217:
	b 215f
214:
215:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
218:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 218b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 219f
	b 220f
219:
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r5, %r30, 32
	li %r6, 1
	bl {vg_ghash}
220:
	b 213f
212:
213:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 221f
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	bl {vg_ghash}
	b 222f
221:
222:
	cmpldi %cr0, %r25, 0
	beq %cr0, 223f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
225:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 225b
	b 224f
223:
224:
	b 211f
210:
211:
	li %r0, 15
	and %r26, %r18, %r0
	cmpldi %cr0, %r26, 0
	beq %cr0, 226f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
228:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 228b
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r5, %r31, 96
	li %r6, 1
	bl {vg_ghash}
	b 227f
226:
227:
	li %r24, 0
	or %r26, %r18, %r18
	rldicr %r3, %r24, 3, 60
	rldicr %r4, %r26, 3, 60
	addi %r5, %r31, 96
	li %r6, 0
	stdbrx %r3, %r5, %r6
	li %r6, 8
	stdbrx %r4, %r5, %r6
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r5, %r31, 96
	li %r6, 1
	bl {vg_ghash}
	b 29f
28:
	lwz %r3, 0(%r24)
	lwz %r4, 4(%r24)
	lwz %r5, 8(%r24)
	lis %r6, 256
	stw %r3, 0(%r30)
	stw %r4, 4(%r30)
	stw %r5, 8(%r30)
	stw %r6, 12(%r30)
29:
	lwz %r3, 0(%r30)
	lwz %r4, 4(%r30)
	lwz %r5, 8(%r30)
	addi %r7, %r30, 12
	li %r8, 0
	lwbrx %r6, %r7, %r8
	addi %r6, %r6, 1
	stw %r3, 48(%r30)
	stw %r4, 52(%r30)
	stw %r5, 56(%r30)
	addi %r7, %r30, 60
	stwbrx %r6, %r7, %r8
	std %r8, 16(%r30)
	std %r8, 24(%r30)
	or %r24, %r21, %r21
	or %r25, %r22, %r22
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 229f
	cmpldi %cr0, %r26, 0
	beq %cr0, 231f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 233f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 235f
	b 236f
235:
	or %r5, %r25, %r25
236:
	b 234f
233:
234:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
237:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 237b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 238f
	b 239f
238:
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r30, 32
	li %r6, 1
	bl {vg_ghash}
239:
	b 232f
231:
232:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 240f
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	bl {vg_ghash}
	b 241f
240:
241:
	cmpldi %cr0, %r25, 0
	beq %cr0, 242f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
244:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 244b
	b 243f
242:
243:
	b 230f
229:
230:
	li %r0, 15
	and %r26, %r22, %r0
	cmpldi %cr0, %r26, 0
	beq %cr0, 245f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
247:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 247b
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	bl {vg_ghash}
	b 246f
245:
246:
	or %r24, %r27, %r27
	or %r25, %r23, %r23
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 248f
	cmpldi %cr0, %r26, 0
	beq %cr0, 250f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 252f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 254f
	b 255f
254:
	or %r5, %r25, %r25
255:
	b 253f
252:
253:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
256:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 256b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 257f
	b 258f
257:
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r30, 32
	li %r6, 1
	bl {vg_ghash}
258:
	b 251f
250:
251:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 259f
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	bl {vg_ghash}
	b 260f
259:
260:
	cmpldi %cr0, %r25, 0
	beq %cr0, 261f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
263:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 263b
	b 262f
261:
262:
	b 249f
248:
249:
	li %r0, 15
	and %r26, %r23, %r0
	cmpldi %cr0, %r26, 0
	beq %cr0, 264f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
266:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 266b
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	bl {vg_ghash}
	b 265f
264:
265:
	or %r24, %r22, %r22
	or %r26, %r23, %r23
	rldicr %r3, %r24, 3, 60
	rldicr %r4, %r26, 3, 60
	addi %r5, %r31, 96
	li %r6, 0
	stdbrx %r3, %r5, %r6
	li %r6, 8
	stdbrx %r4, %r5, %r6
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	bl {vg_ghash}
	ld %r3, 16(%r30)
	std %r3, 112(%r31)
	ld %r3, 24(%r30)
	std %r3, 120(%r31)
	or %r3, %r29, %r29
	or %r4, %r30, %r30
	addi %r5, %r31, 112
	li %r6, 1
	or %r7, %r28, %r28
	rldicl %r8, %r6, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 267f
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
	li %r4, 0
	li %r6, 402
	bl {vg_sm4_prepare_keys}
	or %r3, %r7, %r7
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 269f
271:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 784(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 788(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 792(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 796(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 800(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 804(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 808(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 812(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 816(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 820(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 824(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 828(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 832(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 836(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 840(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 844(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 848(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 852(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 856(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 860(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 864(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 868(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 872(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 876(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 880(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 884(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 888(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 892(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 896(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 900(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 904(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 908(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 912(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 916(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 920(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 924(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 928(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 932(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 936(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 940(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 944(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 948(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 952(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 956(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 960(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 964(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 968(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 972(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 976(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 980(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 984(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 988(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 992(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 996(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1000(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1004(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 1008(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 1012(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1016(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1020(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	lwz %r8, 16(%r31)
	lwz %r9, 784(%r5)
	xor %r8, %r8, %r9
	stw %r8, 16(%r31)
	lwz %r8, 20(%r31)
	lwz %r9, 788(%r5)
	xor %r8, %r8, %r9
	stw %r8, 20(%r31)
	lwz %r8, 24(%r31)
	lwz %r9, 792(%r5)
	xor %r8, %r8, %r9
	stw %r8, 24(%r31)
	lwz %r8, 28(%r31)
	lwz %r9, 796(%r5)
	xor %r8, %r8, %r9
	stw %r8, 28(%r31)
	lwz %r8, 32(%r31)
	lwz %r9, 800(%r5)
	xor %r8, %r8, %r9
	stw %r8, 32(%r31)
	lwz %r8, 36(%r31)
	lwz %r9, 804(%r5)
	xor %r8, %r8, %r9
	stw %r8, 36(%r31)
	lwz %r8, 40(%r31)
	lwz %r9, 808(%r5)
	xor %r8, %r8, %r9
	stw %r8, 40(%r31)
	lwz %r8, 44(%r31)
	lwz %r9, 812(%r5)
	xor %r8, %r8, %r9
	stw %r8, 44(%r31)
	lwz %r8, 48(%r31)
	lwz %r9, 816(%r5)
	xor %r8, %r8, %r9
	stw %r8, 48(%r31)
	lwz %r8, 52(%r31)
	lwz %r9, 820(%r5)
	xor %r8, %r8, %r9
	stw %r8, 52(%r31)
	lwz %r8, 56(%r31)
	lwz %r9, 824(%r5)
	xor %r8, %r8, %r9
	stw %r8, 56(%r31)
	lwz %r8, 60(%r31)
	lwz %r9, 828(%r5)
	xor %r8, %r8, %r9
	stw %r8, 60(%r31)
	lwz %r8, 64(%r31)
	lwz %r9, 832(%r5)
	xor %r8, %r8, %r9
	stw %r8, 64(%r31)
	lwz %r8, 68(%r31)
	lwz %r9, 836(%r5)
	xor %r8, %r8, %r9
	stw %r8, 68(%r31)
	lwz %r8, 72(%r31)
	lwz %r9, 840(%r5)
	xor %r8, %r8, %r9
	stw %r8, 72(%r31)
	lwz %r8, 76(%r31)
	lwz %r9, 844(%r5)
	xor %r8, %r8, %r9
	stw %r8, 76(%r31)
	lwz %r8, 80(%r31)
	lwz %r9, 848(%r5)
	xor %r8, %r8, %r9
	stw %r8, 80(%r31)
	lwz %r8, 84(%r31)
	lwz %r9, 852(%r5)
	xor %r8, %r8, %r9
	stw %r8, 84(%r31)
	lwz %r8, 88(%r31)
	lwz %r9, 856(%r5)
	xor %r8, %r8, %r9
	stw %r8, 88(%r31)
	lwz %r8, 92(%r31)
	lwz %r9, 860(%r5)
	xor %r8, %r8, %r9
	stw %r8, 92(%r31)
	lwz %r8, 96(%r31)
	lwz %r9, 864(%r5)
	xor %r8, %r8, %r9
	stw %r8, 96(%r31)
	lwz %r8, 100(%r31)
	lwz %r9, 868(%r5)
	xor %r8, %r8, %r9
	stw %r8, 100(%r31)
	lwz %r8, 104(%r31)
	lwz %r9, 872(%r5)
	xor %r8, %r8, %r9
	stw %r8, 104(%r31)
	lwz %r8, 108(%r31)
	lwz %r9, 876(%r5)
	xor %r8, %r8, %r9
	stw %r8, 108(%r31)
	lwz %r8, 112(%r31)
	lwz %r9, 880(%r5)
	xor %r8, %r8, %r9
	stw %r8, 112(%r31)
	lwz %r8, 116(%r31)
	lwz %r9, 884(%r5)
	xor %r8, %r8, %r9
	stw %r8, 116(%r31)
	lwz %r8, 120(%r31)
	lwz %r9, 888(%r5)
	xor %r8, %r8, %r9
	stw %r8, 120(%r31)
	lwz %r8, 124(%r31)
	lwz %r9, 892(%r5)
	xor %r8, %r8, %r9
	stw %r8, 124(%r31)
	lwz %r8, 128(%r31)
	lwz %r9, 896(%r5)
	xor %r8, %r8, %r9
	stw %r8, 128(%r31)
	lwz %r8, 132(%r31)
	lwz %r9, 900(%r5)
	xor %r8, %r8, %r9
	stw %r8, 132(%r31)
	lwz %r8, 136(%r31)
	lwz %r9, 904(%r5)
	xor %r8, %r8, %r9
	stw %r8, 136(%r31)
	lwz %r8, 140(%r31)
	lwz %r9, 908(%r5)
	xor %r8, %r8, %r9
	stw %r8, 140(%r31)
	lwz %r8, 144(%r31)
	lwz %r9, 912(%r5)
	xor %r8, %r8, %r9
	stw %r8, 144(%r31)
	lwz %r8, 148(%r31)
	lwz %r9, 916(%r5)
	xor %r8, %r8, %r9
	stw %r8, 148(%r31)
	lwz %r8, 152(%r31)
	lwz %r9, 920(%r5)
	xor %r8, %r8, %r9
	stw %r8, 152(%r31)
	lwz %r8, 156(%r31)
	lwz %r9, 924(%r5)
	xor %r8, %r8, %r9
	stw %r8, 156(%r31)
	lwz %r8, 160(%r31)
	lwz %r9, 928(%r5)
	xor %r8, %r8, %r9
	stw %r8, 160(%r31)
	lwz %r8, 164(%r31)
	lwz %r9, 932(%r5)
	xor %r8, %r8, %r9
	stw %r8, 164(%r31)
	lwz %r8, 168(%r31)
	lwz %r9, 936(%r5)
	xor %r8, %r8, %r9
	stw %r8, 168(%r31)
	lwz %r8, 172(%r31)
	lwz %r9, 940(%r5)
	xor %r8, %r8, %r9
	stw %r8, 172(%r31)
	lwz %r8, 176(%r31)
	lwz %r9, 944(%r5)
	xor %r8, %r8, %r9
	stw %r8, 176(%r31)
	lwz %r8, 180(%r31)
	lwz %r9, 948(%r5)
	xor %r8, %r8, %r9
	stw %r8, 180(%r31)
	lwz %r8, 184(%r31)
	lwz %r9, 952(%r5)
	xor %r8, %r8, %r9
	stw %r8, 184(%r31)
	lwz %r8, 188(%r31)
	lwz %r9, 956(%r5)
	xor %r8, %r8, %r9
	stw %r8, 188(%r31)
	lwz %r8, 192(%r31)
	lwz %r9, 960(%r5)
	xor %r8, %r8, %r9
	stw %r8, 192(%r31)
	lwz %r8, 196(%r31)
	lwz %r9, 964(%r5)
	xor %r8, %r8, %r9
	stw %r8, 196(%r31)
	lwz %r8, 200(%r31)
	lwz %r9, 968(%r5)
	xor %r8, %r8, %r9
	stw %r8, 200(%r31)
	lwz %r8, 204(%r31)
	lwz %r9, 972(%r5)
	xor %r8, %r8, %r9
	stw %r8, 204(%r31)
	lwz %r8, 208(%r31)
	lwz %r9, 976(%r5)
	xor %r8, %r8, %r9
	stw %r8, 208(%r31)
	lwz %r8, 212(%r31)
	lwz %r9, 980(%r5)
	xor %r8, %r8, %r9
	stw %r8, 212(%r31)
	lwz %r8, 216(%r31)
	lwz %r9, 984(%r5)
	xor %r8, %r8, %r9
	stw %r8, 216(%r31)
	lwz %r8, 220(%r31)
	lwz %r9, 988(%r5)
	xor %r8, %r8, %r9
	stw %r8, 220(%r31)
	lwz %r8, 224(%r31)
	lwz %r9, 992(%r5)
	xor %r8, %r8, %r9
	stw %r8, 224(%r31)
	lwz %r8, 228(%r31)
	lwz %r9, 996(%r5)
	xor %r8, %r8, %r9
	stw %r8, 228(%r31)
	lwz %r8, 232(%r31)
	lwz %r9, 1000(%r5)
	xor %r8, %r8, %r9
	stw %r8, 232(%r31)
	lwz %r8, 236(%r31)
	lwz %r9, 1004(%r5)
	xor %r8, %r8, %r9
	stw %r8, 236(%r31)
	lwz %r8, 240(%r31)
	lwz %r9, 1008(%r5)
	xor %r8, %r8, %r9
	stw %r8, 240(%r31)
	lwz %r8, 244(%r31)
	lwz %r9, 1012(%r5)
	xor %r8, %r8, %r9
	stw %r8, 244(%r31)
	lwz %r8, 248(%r31)
	lwz %r9, 1016(%r5)
	xor %r8, %r8, %r9
	stw %r8, 248(%r31)
	lwz %r8, 252(%r31)
	lwz %r9, 1020(%r5)
	xor %r8, %r8, %r9
	stw %r8, 252(%r31)
	addi %r31, %r31, 256
	addi %r30, %r30, -16
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	bne %cr0, 271b
	b 270f
269:
270:
	cmpldi %cr0, %r30, 0
	beq %cr0, 272f
274:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 274b
	b 273f
272:
273:
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
	b 268f
267:
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
	beq %cr0, 275f
277:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	bl {vg_sm4_serial_encrypt}
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 277b
	b 276f
275:
276:
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
268:
	li %r0, 0
	std %r0, 256(%r31)
	std %r0, 264(%r31)
	or %r3, %r20, %r20
	addi %r4, %r31, 256
	or %r5, %r19, %r19
278:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 278b
	li %r0, 0
	std %r0, 272(%r31)
	std %r0, 280(%r31)
	addi %r3, %r31, 112
	addi %r4, %r31, 272
	or %r5, %r19, %r19
279:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 279b
	ld %r3, 272(%r31)
	ld %r4, 256(%r31)
	xor %r3, %r3, %r4
	ld %r4, 280(%r31)
	ld %r5, 264(%r31)
	xor %r4, %r4, %r5
	or %r3, %r3, %r4
	li %r4, 0
	subf %r4, %r3, %r4
	or %r3, %r3, %r4
	rldicl %r3, %r3, 1, 63
	li %r4, 1
	subf %r3, %r3, %r4
	or %r19, %r3, %r3
	cmpldi %cr0, %r19, 0
	beq %cr0, 280f
	or %r24, %r27, %r27
	or %r25, %r23, %r23
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 282f
	cmpldi %cr0, %r26, 0
	beq %cr0, 284f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 286f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 288f
	b 289f
288:
	or %r5, %r25, %r25
289:
	b 287f
286:
287:
	addi %r3, %r30, 64
	add %r3, %r3, %r26
	or %r4, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
290:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 290b
	b 285f
284:
285:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 291f
	or %r3, %r29, %r29
	addi %r4, %r30, 48
	or %r7, %r28, %r28
	rldicl %r8, %r6, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 293f
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
	li %r4, 0
	li %r6, 402
	bl {vg_sm4_prepare_keys}
	or %r3, %r7, %r7
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 295f
297:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 784(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 788(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 792(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 796(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 800(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 804(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 808(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 812(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 816(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 820(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 824(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 828(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 832(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 836(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 840(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 844(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 848(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 852(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 856(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 860(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 864(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 868(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 872(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 876(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 880(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 884(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 888(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 892(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 896(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 900(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 904(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 908(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 912(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 916(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 920(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 924(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 928(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 932(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 936(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 940(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 944(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 948(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 952(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 956(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 960(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 964(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 968(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 972(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 976(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 980(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 984(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 988(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 992(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 996(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1000(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1004(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 1008(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 1012(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1016(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1020(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	lwz %r8, 16(%r31)
	lwz %r9, 784(%r5)
	xor %r8, %r8, %r9
	stw %r8, 16(%r31)
	lwz %r8, 20(%r31)
	lwz %r9, 788(%r5)
	xor %r8, %r8, %r9
	stw %r8, 20(%r31)
	lwz %r8, 24(%r31)
	lwz %r9, 792(%r5)
	xor %r8, %r8, %r9
	stw %r8, 24(%r31)
	lwz %r8, 28(%r31)
	lwz %r9, 796(%r5)
	xor %r8, %r8, %r9
	stw %r8, 28(%r31)
	lwz %r8, 32(%r31)
	lwz %r9, 800(%r5)
	xor %r8, %r8, %r9
	stw %r8, 32(%r31)
	lwz %r8, 36(%r31)
	lwz %r9, 804(%r5)
	xor %r8, %r8, %r9
	stw %r8, 36(%r31)
	lwz %r8, 40(%r31)
	lwz %r9, 808(%r5)
	xor %r8, %r8, %r9
	stw %r8, 40(%r31)
	lwz %r8, 44(%r31)
	lwz %r9, 812(%r5)
	xor %r8, %r8, %r9
	stw %r8, 44(%r31)
	lwz %r8, 48(%r31)
	lwz %r9, 816(%r5)
	xor %r8, %r8, %r9
	stw %r8, 48(%r31)
	lwz %r8, 52(%r31)
	lwz %r9, 820(%r5)
	xor %r8, %r8, %r9
	stw %r8, 52(%r31)
	lwz %r8, 56(%r31)
	lwz %r9, 824(%r5)
	xor %r8, %r8, %r9
	stw %r8, 56(%r31)
	lwz %r8, 60(%r31)
	lwz %r9, 828(%r5)
	xor %r8, %r8, %r9
	stw %r8, 60(%r31)
	lwz %r8, 64(%r31)
	lwz %r9, 832(%r5)
	xor %r8, %r8, %r9
	stw %r8, 64(%r31)
	lwz %r8, 68(%r31)
	lwz %r9, 836(%r5)
	xor %r8, %r8, %r9
	stw %r8, 68(%r31)
	lwz %r8, 72(%r31)
	lwz %r9, 840(%r5)
	xor %r8, %r8, %r9
	stw %r8, 72(%r31)
	lwz %r8, 76(%r31)
	lwz %r9, 844(%r5)
	xor %r8, %r8, %r9
	stw %r8, 76(%r31)
	lwz %r8, 80(%r31)
	lwz %r9, 848(%r5)
	xor %r8, %r8, %r9
	stw %r8, 80(%r31)
	lwz %r8, 84(%r31)
	lwz %r9, 852(%r5)
	xor %r8, %r8, %r9
	stw %r8, 84(%r31)
	lwz %r8, 88(%r31)
	lwz %r9, 856(%r5)
	xor %r8, %r8, %r9
	stw %r8, 88(%r31)
	lwz %r8, 92(%r31)
	lwz %r9, 860(%r5)
	xor %r8, %r8, %r9
	stw %r8, 92(%r31)
	lwz %r8, 96(%r31)
	lwz %r9, 864(%r5)
	xor %r8, %r8, %r9
	stw %r8, 96(%r31)
	lwz %r8, 100(%r31)
	lwz %r9, 868(%r5)
	xor %r8, %r8, %r9
	stw %r8, 100(%r31)
	lwz %r8, 104(%r31)
	lwz %r9, 872(%r5)
	xor %r8, %r8, %r9
	stw %r8, 104(%r31)
	lwz %r8, 108(%r31)
	lwz %r9, 876(%r5)
	xor %r8, %r8, %r9
	stw %r8, 108(%r31)
	lwz %r8, 112(%r31)
	lwz %r9, 880(%r5)
	xor %r8, %r8, %r9
	stw %r8, 112(%r31)
	lwz %r8, 116(%r31)
	lwz %r9, 884(%r5)
	xor %r8, %r8, %r9
	stw %r8, 116(%r31)
	lwz %r8, 120(%r31)
	lwz %r9, 888(%r5)
	xor %r8, %r8, %r9
	stw %r8, 120(%r31)
	lwz %r8, 124(%r31)
	lwz %r9, 892(%r5)
	xor %r8, %r8, %r9
	stw %r8, 124(%r31)
	lwz %r8, 128(%r31)
	lwz %r9, 896(%r5)
	xor %r8, %r8, %r9
	stw %r8, 128(%r31)
	lwz %r8, 132(%r31)
	lwz %r9, 900(%r5)
	xor %r8, %r8, %r9
	stw %r8, 132(%r31)
	lwz %r8, 136(%r31)
	lwz %r9, 904(%r5)
	xor %r8, %r8, %r9
	stw %r8, 136(%r31)
	lwz %r8, 140(%r31)
	lwz %r9, 908(%r5)
	xor %r8, %r8, %r9
	stw %r8, 140(%r31)
	lwz %r8, 144(%r31)
	lwz %r9, 912(%r5)
	xor %r8, %r8, %r9
	stw %r8, 144(%r31)
	lwz %r8, 148(%r31)
	lwz %r9, 916(%r5)
	xor %r8, %r8, %r9
	stw %r8, 148(%r31)
	lwz %r8, 152(%r31)
	lwz %r9, 920(%r5)
	xor %r8, %r8, %r9
	stw %r8, 152(%r31)
	lwz %r8, 156(%r31)
	lwz %r9, 924(%r5)
	xor %r8, %r8, %r9
	stw %r8, 156(%r31)
	lwz %r8, 160(%r31)
	lwz %r9, 928(%r5)
	xor %r8, %r8, %r9
	stw %r8, 160(%r31)
	lwz %r8, 164(%r31)
	lwz %r9, 932(%r5)
	xor %r8, %r8, %r9
	stw %r8, 164(%r31)
	lwz %r8, 168(%r31)
	lwz %r9, 936(%r5)
	xor %r8, %r8, %r9
	stw %r8, 168(%r31)
	lwz %r8, 172(%r31)
	lwz %r9, 940(%r5)
	xor %r8, %r8, %r9
	stw %r8, 172(%r31)
	lwz %r8, 176(%r31)
	lwz %r9, 944(%r5)
	xor %r8, %r8, %r9
	stw %r8, 176(%r31)
	lwz %r8, 180(%r31)
	lwz %r9, 948(%r5)
	xor %r8, %r8, %r9
	stw %r8, 180(%r31)
	lwz %r8, 184(%r31)
	lwz %r9, 952(%r5)
	xor %r8, %r8, %r9
	stw %r8, 184(%r31)
	lwz %r8, 188(%r31)
	lwz %r9, 956(%r5)
	xor %r8, %r8, %r9
	stw %r8, 188(%r31)
	lwz %r8, 192(%r31)
	lwz %r9, 960(%r5)
	xor %r8, %r8, %r9
	stw %r8, 192(%r31)
	lwz %r8, 196(%r31)
	lwz %r9, 964(%r5)
	xor %r8, %r8, %r9
	stw %r8, 196(%r31)
	lwz %r8, 200(%r31)
	lwz %r9, 968(%r5)
	xor %r8, %r8, %r9
	stw %r8, 200(%r31)
	lwz %r8, 204(%r31)
	lwz %r9, 972(%r5)
	xor %r8, %r8, %r9
	stw %r8, 204(%r31)
	lwz %r8, 208(%r31)
	lwz %r9, 976(%r5)
	xor %r8, %r8, %r9
	stw %r8, 208(%r31)
	lwz %r8, 212(%r31)
	lwz %r9, 980(%r5)
	xor %r8, %r8, %r9
	stw %r8, 212(%r31)
	lwz %r8, 216(%r31)
	lwz %r9, 984(%r5)
	xor %r8, %r8, %r9
	stw %r8, 216(%r31)
	lwz %r8, 220(%r31)
	lwz %r9, 988(%r5)
	xor %r8, %r8, %r9
	stw %r8, 220(%r31)
	lwz %r8, 224(%r31)
	lwz %r9, 992(%r5)
	xor %r8, %r8, %r9
	stw %r8, 224(%r31)
	lwz %r8, 228(%r31)
	lwz %r9, 996(%r5)
	xor %r8, %r8, %r9
	stw %r8, 228(%r31)
	lwz %r8, 232(%r31)
	lwz %r9, 1000(%r5)
	xor %r8, %r8, %r9
	stw %r8, 232(%r31)
	lwz %r8, 236(%r31)
	lwz %r9, 1004(%r5)
	xor %r8, %r8, %r9
	stw %r8, 236(%r31)
	lwz %r8, 240(%r31)
	lwz %r9, 1008(%r5)
	xor %r8, %r8, %r9
	stw %r8, 240(%r31)
	lwz %r8, 244(%r31)
	lwz %r9, 1012(%r5)
	xor %r8, %r8, %r9
	stw %r8, 244(%r31)
	lwz %r8, 248(%r31)
	lwz %r9, 1016(%r5)
	xor %r8, %r8, %r9
	stw %r8, 248(%r31)
	lwz %r8, 252(%r31)
	lwz %r9, 1020(%r5)
	xor %r8, %r8, %r9
	stw %r8, 252(%r31)
	addi %r31, %r31, 256
	addi %r30, %r30, -16
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	bne %cr0, 297b
	b 296f
295:
296:
	cmpldi %cr0, %r30, 0
	beq %cr0, 298f
2100:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 2100b
	b 299f
298:
299:
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
	b 294f
293:
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
	beq %cr0, 2101f
2103:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	bl {vg_sm4_serial_encrypt}
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 2103b
	b 2102f
2101:
2102:
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
294:
	b 292f
291:
292:
	cmpldi %cr0, %r25, 0
	beq %cr0, 2104f
	li %r0, 0
	std %r0, 64(%r30)
	std %r0, 72(%r30)
	addi %r5, %r30, 64
	li %r6, 1
	or %r3, %r29, %r29
	addi %r4, %r30, 48
	or %r7, %r28, %r28
	rldicl %r8, %r6, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 2106f
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
	li %r4, 0
	li %r6, 402
	bl {vg_sm4_prepare_keys}
	or %r3, %r7, %r7
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 2108f
2110:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 784(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 788(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 792(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 796(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 800(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 804(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 808(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 812(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 816(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 820(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 824(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 828(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 832(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 836(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 840(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 844(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 848(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 852(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 856(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 860(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 864(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 868(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 872(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 876(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 880(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 884(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 888(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 892(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 896(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 900(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 904(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 908(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 912(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 916(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 920(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 924(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 928(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 932(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 936(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 940(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 944(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 948(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 952(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 956(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 960(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 964(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 968(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 972(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 976(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 980(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 984(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 988(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 992(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 996(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1000(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1004(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 1008(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 1012(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1016(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1020(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	lwz %r8, 16(%r31)
	lwz %r9, 784(%r5)
	xor %r8, %r8, %r9
	stw %r8, 16(%r31)
	lwz %r8, 20(%r31)
	lwz %r9, 788(%r5)
	xor %r8, %r8, %r9
	stw %r8, 20(%r31)
	lwz %r8, 24(%r31)
	lwz %r9, 792(%r5)
	xor %r8, %r8, %r9
	stw %r8, 24(%r31)
	lwz %r8, 28(%r31)
	lwz %r9, 796(%r5)
	xor %r8, %r8, %r9
	stw %r8, 28(%r31)
	lwz %r8, 32(%r31)
	lwz %r9, 800(%r5)
	xor %r8, %r8, %r9
	stw %r8, 32(%r31)
	lwz %r8, 36(%r31)
	lwz %r9, 804(%r5)
	xor %r8, %r8, %r9
	stw %r8, 36(%r31)
	lwz %r8, 40(%r31)
	lwz %r9, 808(%r5)
	xor %r8, %r8, %r9
	stw %r8, 40(%r31)
	lwz %r8, 44(%r31)
	lwz %r9, 812(%r5)
	xor %r8, %r8, %r9
	stw %r8, 44(%r31)
	lwz %r8, 48(%r31)
	lwz %r9, 816(%r5)
	xor %r8, %r8, %r9
	stw %r8, 48(%r31)
	lwz %r8, 52(%r31)
	lwz %r9, 820(%r5)
	xor %r8, %r8, %r9
	stw %r8, 52(%r31)
	lwz %r8, 56(%r31)
	lwz %r9, 824(%r5)
	xor %r8, %r8, %r9
	stw %r8, 56(%r31)
	lwz %r8, 60(%r31)
	lwz %r9, 828(%r5)
	xor %r8, %r8, %r9
	stw %r8, 60(%r31)
	lwz %r8, 64(%r31)
	lwz %r9, 832(%r5)
	xor %r8, %r8, %r9
	stw %r8, 64(%r31)
	lwz %r8, 68(%r31)
	lwz %r9, 836(%r5)
	xor %r8, %r8, %r9
	stw %r8, 68(%r31)
	lwz %r8, 72(%r31)
	lwz %r9, 840(%r5)
	xor %r8, %r8, %r9
	stw %r8, 72(%r31)
	lwz %r8, 76(%r31)
	lwz %r9, 844(%r5)
	xor %r8, %r8, %r9
	stw %r8, 76(%r31)
	lwz %r8, 80(%r31)
	lwz %r9, 848(%r5)
	xor %r8, %r8, %r9
	stw %r8, 80(%r31)
	lwz %r8, 84(%r31)
	lwz %r9, 852(%r5)
	xor %r8, %r8, %r9
	stw %r8, 84(%r31)
	lwz %r8, 88(%r31)
	lwz %r9, 856(%r5)
	xor %r8, %r8, %r9
	stw %r8, 88(%r31)
	lwz %r8, 92(%r31)
	lwz %r9, 860(%r5)
	xor %r8, %r8, %r9
	stw %r8, 92(%r31)
	lwz %r8, 96(%r31)
	lwz %r9, 864(%r5)
	xor %r8, %r8, %r9
	stw %r8, 96(%r31)
	lwz %r8, 100(%r31)
	lwz %r9, 868(%r5)
	xor %r8, %r8, %r9
	stw %r8, 100(%r31)
	lwz %r8, 104(%r31)
	lwz %r9, 872(%r5)
	xor %r8, %r8, %r9
	stw %r8, 104(%r31)
	lwz %r8, 108(%r31)
	lwz %r9, 876(%r5)
	xor %r8, %r8, %r9
	stw %r8, 108(%r31)
	lwz %r8, 112(%r31)
	lwz %r9, 880(%r5)
	xor %r8, %r8, %r9
	stw %r8, 112(%r31)
	lwz %r8, 116(%r31)
	lwz %r9, 884(%r5)
	xor %r8, %r8, %r9
	stw %r8, 116(%r31)
	lwz %r8, 120(%r31)
	lwz %r9, 888(%r5)
	xor %r8, %r8, %r9
	stw %r8, 120(%r31)
	lwz %r8, 124(%r31)
	lwz %r9, 892(%r5)
	xor %r8, %r8, %r9
	stw %r8, 124(%r31)
	lwz %r8, 128(%r31)
	lwz %r9, 896(%r5)
	xor %r8, %r8, %r9
	stw %r8, 128(%r31)
	lwz %r8, 132(%r31)
	lwz %r9, 900(%r5)
	xor %r8, %r8, %r9
	stw %r8, 132(%r31)
	lwz %r8, 136(%r31)
	lwz %r9, 904(%r5)
	xor %r8, %r8, %r9
	stw %r8, 136(%r31)
	lwz %r8, 140(%r31)
	lwz %r9, 908(%r5)
	xor %r8, %r8, %r9
	stw %r8, 140(%r31)
	lwz %r8, 144(%r31)
	lwz %r9, 912(%r5)
	xor %r8, %r8, %r9
	stw %r8, 144(%r31)
	lwz %r8, 148(%r31)
	lwz %r9, 916(%r5)
	xor %r8, %r8, %r9
	stw %r8, 148(%r31)
	lwz %r8, 152(%r31)
	lwz %r9, 920(%r5)
	xor %r8, %r8, %r9
	stw %r8, 152(%r31)
	lwz %r8, 156(%r31)
	lwz %r9, 924(%r5)
	xor %r8, %r8, %r9
	stw %r8, 156(%r31)
	lwz %r8, 160(%r31)
	lwz %r9, 928(%r5)
	xor %r8, %r8, %r9
	stw %r8, 160(%r31)
	lwz %r8, 164(%r31)
	lwz %r9, 932(%r5)
	xor %r8, %r8, %r9
	stw %r8, 164(%r31)
	lwz %r8, 168(%r31)
	lwz %r9, 936(%r5)
	xor %r8, %r8, %r9
	stw %r8, 168(%r31)
	lwz %r8, 172(%r31)
	lwz %r9, 940(%r5)
	xor %r8, %r8, %r9
	stw %r8, 172(%r31)
	lwz %r8, 176(%r31)
	lwz %r9, 944(%r5)
	xor %r8, %r8, %r9
	stw %r8, 176(%r31)
	lwz %r8, 180(%r31)
	lwz %r9, 948(%r5)
	xor %r8, %r8, %r9
	stw %r8, 180(%r31)
	lwz %r8, 184(%r31)
	lwz %r9, 952(%r5)
	xor %r8, %r8, %r9
	stw %r8, 184(%r31)
	lwz %r8, 188(%r31)
	lwz %r9, 956(%r5)
	xor %r8, %r8, %r9
	stw %r8, 188(%r31)
	lwz %r8, 192(%r31)
	lwz %r9, 960(%r5)
	xor %r8, %r8, %r9
	stw %r8, 192(%r31)
	lwz %r8, 196(%r31)
	lwz %r9, 964(%r5)
	xor %r8, %r8, %r9
	stw %r8, 196(%r31)
	lwz %r8, 200(%r31)
	lwz %r9, 968(%r5)
	xor %r8, %r8, %r9
	stw %r8, 200(%r31)
	lwz %r8, 204(%r31)
	lwz %r9, 972(%r5)
	xor %r8, %r8, %r9
	stw %r8, 204(%r31)
	lwz %r8, 208(%r31)
	lwz %r9, 976(%r5)
	xor %r8, %r8, %r9
	stw %r8, 208(%r31)
	lwz %r8, 212(%r31)
	lwz %r9, 980(%r5)
	xor %r8, %r8, %r9
	stw %r8, 212(%r31)
	lwz %r8, 216(%r31)
	lwz %r9, 984(%r5)
	xor %r8, %r8, %r9
	stw %r8, 216(%r31)
	lwz %r8, 220(%r31)
	lwz %r9, 988(%r5)
	xor %r8, %r8, %r9
	stw %r8, 220(%r31)
	lwz %r8, 224(%r31)
	lwz %r9, 992(%r5)
	xor %r8, %r8, %r9
	stw %r8, 224(%r31)
	lwz %r8, 228(%r31)
	lwz %r9, 996(%r5)
	xor %r8, %r8, %r9
	stw %r8, 228(%r31)
	lwz %r8, 232(%r31)
	lwz %r9, 1000(%r5)
	xor %r8, %r8, %r9
	stw %r8, 232(%r31)
	lwz %r8, 236(%r31)
	lwz %r9, 1004(%r5)
	xor %r8, %r8, %r9
	stw %r8, 236(%r31)
	lwz %r8, 240(%r31)
	lwz %r9, 1008(%r5)
	xor %r8, %r8, %r9
	stw %r8, 240(%r31)
	lwz %r8, 244(%r31)
	lwz %r9, 1012(%r5)
	xor %r8, %r8, %r9
	stw %r8, 244(%r31)
	lwz %r8, 248(%r31)
	lwz %r9, 1016(%r5)
	xor %r8, %r8, %r9
	stw %r8, 248(%r31)
	lwz %r8, 252(%r31)
	lwz %r9, 1020(%r5)
	xor %r8, %r8, %r9
	stw %r8, 252(%r31)
	addi %r31, %r31, 256
	addi %r30, %r30, -16
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	bne %cr0, 2110b
	b 2109f
2108:
2109:
	cmpldi %cr0, %r30, 0
	beq %cr0, 2111f
2113:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 2113b
	b 2112f
2111:
2112:
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
	b 2107f
2106:
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
	beq %cr0, 2114f
2116:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	bl {vg_sm4_serial_encrypt}
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 2116b
	b 2115f
2114:
2115:
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
2107:
	addi %r3, %r30, 64
	or %r4, %r24, %r24
	or %r5, %r25, %r25
2117:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2117b
	b 2105f
2104:
2105:
	b 283f
282:
283:
	b 281f
280:
281:
	or %r3, %r19, %r19
	b 27f
26:
	li %r3, 0
27:
	or %r12, %r31, %r31
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r18, 128(%r12)
	ld %r19, 136(%r12)
	ld %r20, 144(%r12)
	ld %r21, 152(%r12)
	ld %r22, 160(%r12)
	ld %r23, 168(%r12)
	ld %r24, 176(%r12)
	ld %r25, 184(%r12)
	ld %r26, 192(%r12)
	ld %r27, 200(%r12)
	ld %r28, 208(%r12)
	ld %r29, 216(%r12)
	ld %r30, 224(%r12)
	ld %r31, 232(%r12)
	addi %r1, %r1, 3392
	addi %r1, %r1, 400
	li %r0, 0
	stdu %r1, -3792(%r1)
	addi %r12, %r1, 32
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
	addi %r1, %r1, 3792
	rldicr %r3, %r3, 32, 31
	rldicl %r3, %r3, 32, 32
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
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v9, %v9, %v9
	vxor %v10, %v10, %v10
	vxor %v11, %v11, %v11
	vxor %v12, %v12, %v12
	vxor %v13, %v13, %v13
	vxor %v14, %v14, %v14
	vxor %v15, %v15, %v15
	vxor %v16, %v16, %v16
	vxor %v17, %v17, %v17
	vxor %v18, %v18, %v18
	vxor %v19, %v19, %v19
	blr

vg_sm4_gcm_stream_init:
	stdu %r1, -320(%r1)
	addi %r7, %r1, 32
	std %r18, 128(%r7)
	std %r19, 136(%r7)
	std %r20, 144(%r7)
	std %r21, 152(%r7)
	std %r22, 160(%r7)
	std %r23, 168(%r7)
	std %r24, 176(%r7)
	std %r25, 184(%r7)
	std %r26, 192(%r7)
	std %r27, 200(%r7)
	std %r28, 208(%r7)
	std %r29, 216(%r7)
	std %r30, 224(%r7)
	std %r31, 232(%r7)
	mflr %r0
	std %r0, 240(%r7)
	or %r31, %r7, %r7
	or %r30, %r6, %r6
	or %r29, %r3, %r3
	or %r24, %r4, %r4
	or %r25, %r5, %r5
	or %r18, %r5, %r5
	addi %r6, %r25, -12
	cmpldi %cr0, %r6, 0
	beq %cr0, 20f
	li %r0, 0
	std %r0, 0(%r30)
	std %r0, 8(%r30)
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 22f
	cmpldi %cr0, %r26, 0
	beq %cr0, 24f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 26f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 28f
	b 29f
28:
	or %r5, %r25, %r25
29:
	b 27f
26:
27:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
210:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 210b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 211f
	b 212f
211:
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r5, %r30, 32
	li %r6, 1
	bl {vg_ghash}
212:
	b 25f
24:
25:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 213f
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	bl {vg_ghash}
	b 214f
213:
214:
	cmpldi %cr0, %r25, 0
	beq %cr0, 215f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
217:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 217b
	b 216f
215:
216:
	b 23f
22:
23:
	li %r0, 15
	and %r26, %r18, %r0
	cmpldi %cr0, %r26, 0
	beq %cr0, 218f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
220:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 220b
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r5, %r31, 96
	li %r6, 1
	bl {vg_ghash}
	b 219f
218:
219:
	li %r24, 0
	or %r26, %r18, %r18
	rldicr %r3, %r24, 3, 60
	rldicr %r4, %r26, 3, 60
	addi %r5, %r31, 96
	li %r6, 0
	stdbrx %r3, %r5, %r6
	li %r6, 8
	stdbrx %r4, %r5, %r6
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r5, %r31, 96
	li %r6, 1
	bl {vg_ghash}
	b 21f
20:
	lwz %r3, 0(%r24)
	lwz %r4, 4(%r24)
	lwz %r5, 8(%r24)
	lis %r6, 256
	stw %r3, 0(%r30)
	stw %r4, 4(%r30)
	stw %r5, 8(%r30)
	stw %r6, 12(%r30)
21:
	lwz %r3, 0(%r30)
	lwz %r4, 4(%r30)
	lwz %r5, 8(%r30)
	addi %r7, %r30, 12
	li %r8, 0
	lwbrx %r6, %r7, %r8
	addi %r6, %r6, 1
	stw %r3, 48(%r30)
	stw %r4, 52(%r30)
	stw %r5, 56(%r30)
	addi %r7, %r30, 60
	stwbrx %r6, %r7, %r8
	std %r8, 16(%r30)
	std %r8, 24(%r30)
	or %r12, %r31, %r31
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r18, 128(%r12)
	ld %r19, 136(%r12)
	ld %r20, 144(%r12)
	ld %r21, 152(%r12)
	ld %r22, 160(%r12)
	ld %r23, 168(%r12)
	ld %r24, 176(%r12)
	ld %r25, 184(%r12)
	ld %r26, 192(%r12)
	ld %r27, 200(%r12)
	ld %r28, 208(%r12)
	ld %r29, 216(%r12)
	ld %r30, 224(%r12)
	ld %r31, 232(%r12)
	addi %r1, %r1, 320
	li %r0, 0
	stdu %r1, -320(%r1)
	addi %r12, %r1, 32
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
	std %r0, 192(%r12)
	std %r0, 200(%r12)
	std %r0, 208(%r12)
	std %r0, 216(%r12)
	std %r0, 224(%r12)
	std %r0, 232(%r12)
	std %r0, 240(%r12)
	std %r0, 248(%r12)
	std %r0, 256(%r12)
	std %r0, 264(%r12)
	std %r0, 272(%r12)
	std %r0, 280(%r12)
	addi %r1, %r1, 320
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
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v9, %v9, %v9
	vxor %v10, %v10, %v10
	vxor %v11, %v11, %v11
	vxor %v12, %v12, %v12
	vxor %v13, %v13, %v13
	vxor %v14, %v14, %v14
	vxor %v15, %v15, %v15
	vxor %v16, %v16, %v16
	vxor %v17, %v17, %v17
	vxor %v18, %v18, %v18
	vxor %v19, %v19, %v19
	blr

vg_sm4_gcm_stream_aad:
	stdu %r1, -320(%r1)
	addi %r8, %r1, 32
	std %r18, 128(%r8)
	std %r19, 136(%r8)
	std %r20, 144(%r8)
	std %r21, 152(%r8)
	std %r22, 160(%r8)
	std %r23, 168(%r8)
	std %r24, 176(%r8)
	std %r25, 184(%r8)
	std %r26, 192(%r8)
	std %r27, 200(%r8)
	std %r28, 208(%r8)
	std %r29, 216(%r8)
	std %r30, 224(%r8)
	std %r31, 232(%r8)
	mflr %r0
	std %r0, 240(%r8)
	or %r31, %r8, %r8
	or %r30, %r4, %r4
	or %r29, %r3, %r3
	or %r24, %r6, %r6
	or %r25, %r7, %r7
	li %r0, 15
	and %r26, %r5, %r0
	cmpldi %cr0, %r25, 0
	beq %cr0, 20f
	cmpldi %cr0, %r26, 0
	beq %cr0, 22f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 24f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 26f
	b 27f
26:
	or %r5, %r25, %r25
27:
	b 25f
24:
25:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
28:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 28b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 29f
	b 210f
29:
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r30, 32
	li %r6, 1
	bl {vg_ghash}
210:
	b 23f
22:
23:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 211f
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	bl {vg_ghash}
	b 212f
211:
212:
	cmpldi %cr0, %r25, 0
	beq %cr0, 213f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
215:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 215b
	b 214f
213:
214:
	b 21f
20:
21:
	or %r12, %r31, %r31
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r18, 128(%r12)
	ld %r19, 136(%r12)
	ld %r20, 144(%r12)
	ld %r21, 152(%r12)
	ld %r22, 160(%r12)
	ld %r23, 168(%r12)
	ld %r24, 176(%r12)
	ld %r25, 184(%r12)
	ld %r26, 192(%r12)
	ld %r27, 200(%r12)
	ld %r28, 208(%r12)
	ld %r29, 216(%r12)
	ld %r30, 224(%r12)
	ld %r31, 232(%r12)
	addi %r1, %r1, 320
	li %r0, 0
	stdu %r1, -320(%r1)
	addi %r12, %r1, 32
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
	std %r0, 192(%r12)
	std %r0, 200(%r12)
	std %r0, 208(%r12)
	std %r0, 216(%r12)
	std %r0, 224(%r12)
	std %r0, 232(%r12)
	std %r0, 240(%r12)
	std %r0, 248(%r12)
	std %r0, 256(%r12)
	std %r0, 264(%r12)
	std %r0, 272(%r12)
	std %r0, 280(%r12)
	addi %r1, %r1, 320
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
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v9, %v9, %v9
	vxor %v10, %v10, %v10
	vxor %v11, %v11, %v11
	vxor %v12, %v12, %v12
	vxor %v13, %v13, %v13
	vxor %v14, %v14, %v14
	vxor %v15, %v15, %v15
	vxor %v16, %v16, %v16
	vxor %v17, %v17, %v17
	vxor %v18, %v18, %v18
	vxor %v19, %v19, %v19
	blr

vg_sm4_gcm_stream_encrypt:
	stdu %r1, -320(%r1)
	addi %r9, %r1, 32
	stdu %r1, -3296(%r1)
	addi %r10, %r1, 32
	std %r18, 128(%r9)
	std %r19, 136(%r9)
	std %r20, 144(%r9)
	std %r21, 152(%r9)
	std %r22, 160(%r9)
	std %r23, 168(%r9)
	std %r24, 176(%r9)
	std %r25, 184(%r9)
	std %r26, 192(%r9)
	std %r27, 200(%r9)
	std %r28, 208(%r9)
	std %r29, 216(%r9)
	std %r30, 224(%r9)
	std %r31, 232(%r9)
	mflr %r0
	std %r0, 240(%r9)
	or %r31, %r9, %r9
	or %r30, %r4, %r4
	or %r29, %r3, %r3
	or %r22, %r5, %r5
	or %r23, %r6, %r6
	or %r20, %r7, %r7
	or %r19, %r8, %r8
	or %r28, %r10, %r10
	or %r24, %r20, %r20
	or %r25, %r19, %r19
	li %r0, 15
	and %r26, %r23, %r0
	cmpldi %cr0, %r25, 0
	beq %cr0, 20f
	cmpldi %cr0, %r26, 0
	beq %cr0, 22f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 24f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 26f
	b 27f
26:
	or %r5, %r25, %r25
27:
	b 25f
24:
25:
	addi %r3, %r30, 64
	add %r3, %r3, %r26
	or %r4, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
28:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 28b
	b 23f
22:
23:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 29f
	or %r3, %r29, %r29
	addi %r4, %r30, 48
	or %r7, %r28, %r28
	rldicl %r8, %r6, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 211f
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
	li %r4, 0
	li %r6, 402
	bl {vg_sm4_prepare_keys}
	or %r3, %r7, %r7
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 213f
215:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 784(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 788(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 792(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 796(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 800(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 804(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 808(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 812(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 816(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 820(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 824(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 828(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 832(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 836(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 840(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 844(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 848(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 852(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 856(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 860(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 864(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 868(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 872(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 876(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 880(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 884(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 888(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 892(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 896(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 900(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 904(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 908(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 912(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 916(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 920(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 924(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 928(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 932(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 936(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 940(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 944(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 948(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 952(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 956(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 960(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 964(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 968(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 972(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 976(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 980(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 984(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 988(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 992(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 996(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1000(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1004(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 1008(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 1012(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1016(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1020(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	lwz %r8, 16(%r31)
	lwz %r9, 784(%r5)
	xor %r8, %r8, %r9
	stw %r8, 16(%r31)
	lwz %r8, 20(%r31)
	lwz %r9, 788(%r5)
	xor %r8, %r8, %r9
	stw %r8, 20(%r31)
	lwz %r8, 24(%r31)
	lwz %r9, 792(%r5)
	xor %r8, %r8, %r9
	stw %r8, 24(%r31)
	lwz %r8, 28(%r31)
	lwz %r9, 796(%r5)
	xor %r8, %r8, %r9
	stw %r8, 28(%r31)
	lwz %r8, 32(%r31)
	lwz %r9, 800(%r5)
	xor %r8, %r8, %r9
	stw %r8, 32(%r31)
	lwz %r8, 36(%r31)
	lwz %r9, 804(%r5)
	xor %r8, %r8, %r9
	stw %r8, 36(%r31)
	lwz %r8, 40(%r31)
	lwz %r9, 808(%r5)
	xor %r8, %r8, %r9
	stw %r8, 40(%r31)
	lwz %r8, 44(%r31)
	lwz %r9, 812(%r5)
	xor %r8, %r8, %r9
	stw %r8, 44(%r31)
	lwz %r8, 48(%r31)
	lwz %r9, 816(%r5)
	xor %r8, %r8, %r9
	stw %r8, 48(%r31)
	lwz %r8, 52(%r31)
	lwz %r9, 820(%r5)
	xor %r8, %r8, %r9
	stw %r8, 52(%r31)
	lwz %r8, 56(%r31)
	lwz %r9, 824(%r5)
	xor %r8, %r8, %r9
	stw %r8, 56(%r31)
	lwz %r8, 60(%r31)
	lwz %r9, 828(%r5)
	xor %r8, %r8, %r9
	stw %r8, 60(%r31)
	lwz %r8, 64(%r31)
	lwz %r9, 832(%r5)
	xor %r8, %r8, %r9
	stw %r8, 64(%r31)
	lwz %r8, 68(%r31)
	lwz %r9, 836(%r5)
	xor %r8, %r8, %r9
	stw %r8, 68(%r31)
	lwz %r8, 72(%r31)
	lwz %r9, 840(%r5)
	xor %r8, %r8, %r9
	stw %r8, 72(%r31)
	lwz %r8, 76(%r31)
	lwz %r9, 844(%r5)
	xor %r8, %r8, %r9
	stw %r8, 76(%r31)
	lwz %r8, 80(%r31)
	lwz %r9, 848(%r5)
	xor %r8, %r8, %r9
	stw %r8, 80(%r31)
	lwz %r8, 84(%r31)
	lwz %r9, 852(%r5)
	xor %r8, %r8, %r9
	stw %r8, 84(%r31)
	lwz %r8, 88(%r31)
	lwz %r9, 856(%r5)
	xor %r8, %r8, %r9
	stw %r8, 88(%r31)
	lwz %r8, 92(%r31)
	lwz %r9, 860(%r5)
	xor %r8, %r8, %r9
	stw %r8, 92(%r31)
	lwz %r8, 96(%r31)
	lwz %r9, 864(%r5)
	xor %r8, %r8, %r9
	stw %r8, 96(%r31)
	lwz %r8, 100(%r31)
	lwz %r9, 868(%r5)
	xor %r8, %r8, %r9
	stw %r8, 100(%r31)
	lwz %r8, 104(%r31)
	lwz %r9, 872(%r5)
	xor %r8, %r8, %r9
	stw %r8, 104(%r31)
	lwz %r8, 108(%r31)
	lwz %r9, 876(%r5)
	xor %r8, %r8, %r9
	stw %r8, 108(%r31)
	lwz %r8, 112(%r31)
	lwz %r9, 880(%r5)
	xor %r8, %r8, %r9
	stw %r8, 112(%r31)
	lwz %r8, 116(%r31)
	lwz %r9, 884(%r5)
	xor %r8, %r8, %r9
	stw %r8, 116(%r31)
	lwz %r8, 120(%r31)
	lwz %r9, 888(%r5)
	xor %r8, %r8, %r9
	stw %r8, 120(%r31)
	lwz %r8, 124(%r31)
	lwz %r9, 892(%r5)
	xor %r8, %r8, %r9
	stw %r8, 124(%r31)
	lwz %r8, 128(%r31)
	lwz %r9, 896(%r5)
	xor %r8, %r8, %r9
	stw %r8, 128(%r31)
	lwz %r8, 132(%r31)
	lwz %r9, 900(%r5)
	xor %r8, %r8, %r9
	stw %r8, 132(%r31)
	lwz %r8, 136(%r31)
	lwz %r9, 904(%r5)
	xor %r8, %r8, %r9
	stw %r8, 136(%r31)
	lwz %r8, 140(%r31)
	lwz %r9, 908(%r5)
	xor %r8, %r8, %r9
	stw %r8, 140(%r31)
	lwz %r8, 144(%r31)
	lwz %r9, 912(%r5)
	xor %r8, %r8, %r9
	stw %r8, 144(%r31)
	lwz %r8, 148(%r31)
	lwz %r9, 916(%r5)
	xor %r8, %r8, %r9
	stw %r8, 148(%r31)
	lwz %r8, 152(%r31)
	lwz %r9, 920(%r5)
	xor %r8, %r8, %r9
	stw %r8, 152(%r31)
	lwz %r8, 156(%r31)
	lwz %r9, 924(%r5)
	xor %r8, %r8, %r9
	stw %r8, 156(%r31)
	lwz %r8, 160(%r31)
	lwz %r9, 928(%r5)
	xor %r8, %r8, %r9
	stw %r8, 160(%r31)
	lwz %r8, 164(%r31)
	lwz %r9, 932(%r5)
	xor %r8, %r8, %r9
	stw %r8, 164(%r31)
	lwz %r8, 168(%r31)
	lwz %r9, 936(%r5)
	xor %r8, %r8, %r9
	stw %r8, 168(%r31)
	lwz %r8, 172(%r31)
	lwz %r9, 940(%r5)
	xor %r8, %r8, %r9
	stw %r8, 172(%r31)
	lwz %r8, 176(%r31)
	lwz %r9, 944(%r5)
	xor %r8, %r8, %r9
	stw %r8, 176(%r31)
	lwz %r8, 180(%r31)
	lwz %r9, 948(%r5)
	xor %r8, %r8, %r9
	stw %r8, 180(%r31)
	lwz %r8, 184(%r31)
	lwz %r9, 952(%r5)
	xor %r8, %r8, %r9
	stw %r8, 184(%r31)
	lwz %r8, 188(%r31)
	lwz %r9, 956(%r5)
	xor %r8, %r8, %r9
	stw %r8, 188(%r31)
	lwz %r8, 192(%r31)
	lwz %r9, 960(%r5)
	xor %r8, %r8, %r9
	stw %r8, 192(%r31)
	lwz %r8, 196(%r31)
	lwz %r9, 964(%r5)
	xor %r8, %r8, %r9
	stw %r8, 196(%r31)
	lwz %r8, 200(%r31)
	lwz %r9, 968(%r5)
	xor %r8, %r8, %r9
	stw %r8, 200(%r31)
	lwz %r8, 204(%r31)
	lwz %r9, 972(%r5)
	xor %r8, %r8, %r9
	stw %r8, 204(%r31)
	lwz %r8, 208(%r31)
	lwz %r9, 976(%r5)
	xor %r8, %r8, %r9
	stw %r8, 208(%r31)
	lwz %r8, 212(%r31)
	lwz %r9, 980(%r5)
	xor %r8, %r8, %r9
	stw %r8, 212(%r31)
	lwz %r8, 216(%r31)
	lwz %r9, 984(%r5)
	xor %r8, %r8, %r9
	stw %r8, 216(%r31)
	lwz %r8, 220(%r31)
	lwz %r9, 988(%r5)
	xor %r8, %r8, %r9
	stw %r8, 220(%r31)
	lwz %r8, 224(%r31)
	lwz %r9, 992(%r5)
	xor %r8, %r8, %r9
	stw %r8, 224(%r31)
	lwz %r8, 228(%r31)
	lwz %r9, 996(%r5)
	xor %r8, %r8, %r9
	stw %r8, 228(%r31)
	lwz %r8, 232(%r31)
	lwz %r9, 1000(%r5)
	xor %r8, %r8, %r9
	stw %r8, 232(%r31)
	lwz %r8, 236(%r31)
	lwz %r9, 1004(%r5)
	xor %r8, %r8, %r9
	stw %r8, 236(%r31)
	lwz %r8, 240(%r31)
	lwz %r9, 1008(%r5)
	xor %r8, %r8, %r9
	stw %r8, 240(%r31)
	lwz %r8, 244(%r31)
	lwz %r9, 1012(%r5)
	xor %r8, %r8, %r9
	stw %r8, 244(%r31)
	lwz %r8, 248(%r31)
	lwz %r9, 1016(%r5)
	xor %r8, %r8, %r9
	stw %r8, 248(%r31)
	lwz %r8, 252(%r31)
	lwz %r9, 1020(%r5)
	xor %r8, %r8, %r9
	stw %r8, 252(%r31)
	addi %r31, %r31, 256
	addi %r30, %r30, -16
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	bne %cr0, 215b
	b 214f
213:
214:
	cmpldi %cr0, %r30, 0
	beq %cr0, 216f
218:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 218b
	b 217f
216:
217:
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
	b 212f
211:
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
	beq %cr0, 219f
221:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	bl {vg_sm4_serial_encrypt}
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 221b
	b 220f
219:
220:
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
212:
	b 210f
29:
210:
	cmpldi %cr0, %r25, 0
	beq %cr0, 222f
	li %r0, 0
	std %r0, 64(%r30)
	std %r0, 72(%r30)
	addi %r5, %r30, 64
	li %r6, 1
	or %r3, %r29, %r29
	addi %r4, %r30, 48
	or %r7, %r28, %r28
	rldicl %r8, %r6, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 224f
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
	li %r4, 0
	li %r6, 402
	bl {vg_sm4_prepare_keys}
	or %r3, %r7, %r7
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 226f
228:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 784(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 788(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 792(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 796(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 800(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 804(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 808(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 812(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 816(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 820(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 824(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 828(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 832(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 836(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 840(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 844(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 848(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 852(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 856(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 860(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 864(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 868(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 872(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 876(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 880(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 884(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 888(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 892(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 896(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 900(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 904(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 908(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 912(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 916(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 920(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 924(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 928(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 932(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 936(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 940(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 944(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 948(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 952(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 956(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 960(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 964(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 968(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 972(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 976(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 980(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 984(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 988(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 992(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 996(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1000(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1004(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 1008(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 1012(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1016(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1020(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	lwz %r8, 16(%r31)
	lwz %r9, 784(%r5)
	xor %r8, %r8, %r9
	stw %r8, 16(%r31)
	lwz %r8, 20(%r31)
	lwz %r9, 788(%r5)
	xor %r8, %r8, %r9
	stw %r8, 20(%r31)
	lwz %r8, 24(%r31)
	lwz %r9, 792(%r5)
	xor %r8, %r8, %r9
	stw %r8, 24(%r31)
	lwz %r8, 28(%r31)
	lwz %r9, 796(%r5)
	xor %r8, %r8, %r9
	stw %r8, 28(%r31)
	lwz %r8, 32(%r31)
	lwz %r9, 800(%r5)
	xor %r8, %r8, %r9
	stw %r8, 32(%r31)
	lwz %r8, 36(%r31)
	lwz %r9, 804(%r5)
	xor %r8, %r8, %r9
	stw %r8, 36(%r31)
	lwz %r8, 40(%r31)
	lwz %r9, 808(%r5)
	xor %r8, %r8, %r9
	stw %r8, 40(%r31)
	lwz %r8, 44(%r31)
	lwz %r9, 812(%r5)
	xor %r8, %r8, %r9
	stw %r8, 44(%r31)
	lwz %r8, 48(%r31)
	lwz %r9, 816(%r5)
	xor %r8, %r8, %r9
	stw %r8, 48(%r31)
	lwz %r8, 52(%r31)
	lwz %r9, 820(%r5)
	xor %r8, %r8, %r9
	stw %r8, 52(%r31)
	lwz %r8, 56(%r31)
	lwz %r9, 824(%r5)
	xor %r8, %r8, %r9
	stw %r8, 56(%r31)
	lwz %r8, 60(%r31)
	lwz %r9, 828(%r5)
	xor %r8, %r8, %r9
	stw %r8, 60(%r31)
	lwz %r8, 64(%r31)
	lwz %r9, 832(%r5)
	xor %r8, %r8, %r9
	stw %r8, 64(%r31)
	lwz %r8, 68(%r31)
	lwz %r9, 836(%r5)
	xor %r8, %r8, %r9
	stw %r8, 68(%r31)
	lwz %r8, 72(%r31)
	lwz %r9, 840(%r5)
	xor %r8, %r8, %r9
	stw %r8, 72(%r31)
	lwz %r8, 76(%r31)
	lwz %r9, 844(%r5)
	xor %r8, %r8, %r9
	stw %r8, 76(%r31)
	lwz %r8, 80(%r31)
	lwz %r9, 848(%r5)
	xor %r8, %r8, %r9
	stw %r8, 80(%r31)
	lwz %r8, 84(%r31)
	lwz %r9, 852(%r5)
	xor %r8, %r8, %r9
	stw %r8, 84(%r31)
	lwz %r8, 88(%r31)
	lwz %r9, 856(%r5)
	xor %r8, %r8, %r9
	stw %r8, 88(%r31)
	lwz %r8, 92(%r31)
	lwz %r9, 860(%r5)
	xor %r8, %r8, %r9
	stw %r8, 92(%r31)
	lwz %r8, 96(%r31)
	lwz %r9, 864(%r5)
	xor %r8, %r8, %r9
	stw %r8, 96(%r31)
	lwz %r8, 100(%r31)
	lwz %r9, 868(%r5)
	xor %r8, %r8, %r9
	stw %r8, 100(%r31)
	lwz %r8, 104(%r31)
	lwz %r9, 872(%r5)
	xor %r8, %r8, %r9
	stw %r8, 104(%r31)
	lwz %r8, 108(%r31)
	lwz %r9, 876(%r5)
	xor %r8, %r8, %r9
	stw %r8, 108(%r31)
	lwz %r8, 112(%r31)
	lwz %r9, 880(%r5)
	xor %r8, %r8, %r9
	stw %r8, 112(%r31)
	lwz %r8, 116(%r31)
	lwz %r9, 884(%r5)
	xor %r8, %r8, %r9
	stw %r8, 116(%r31)
	lwz %r8, 120(%r31)
	lwz %r9, 888(%r5)
	xor %r8, %r8, %r9
	stw %r8, 120(%r31)
	lwz %r8, 124(%r31)
	lwz %r9, 892(%r5)
	xor %r8, %r8, %r9
	stw %r8, 124(%r31)
	lwz %r8, 128(%r31)
	lwz %r9, 896(%r5)
	xor %r8, %r8, %r9
	stw %r8, 128(%r31)
	lwz %r8, 132(%r31)
	lwz %r9, 900(%r5)
	xor %r8, %r8, %r9
	stw %r8, 132(%r31)
	lwz %r8, 136(%r31)
	lwz %r9, 904(%r5)
	xor %r8, %r8, %r9
	stw %r8, 136(%r31)
	lwz %r8, 140(%r31)
	lwz %r9, 908(%r5)
	xor %r8, %r8, %r9
	stw %r8, 140(%r31)
	lwz %r8, 144(%r31)
	lwz %r9, 912(%r5)
	xor %r8, %r8, %r9
	stw %r8, 144(%r31)
	lwz %r8, 148(%r31)
	lwz %r9, 916(%r5)
	xor %r8, %r8, %r9
	stw %r8, 148(%r31)
	lwz %r8, 152(%r31)
	lwz %r9, 920(%r5)
	xor %r8, %r8, %r9
	stw %r8, 152(%r31)
	lwz %r8, 156(%r31)
	lwz %r9, 924(%r5)
	xor %r8, %r8, %r9
	stw %r8, 156(%r31)
	lwz %r8, 160(%r31)
	lwz %r9, 928(%r5)
	xor %r8, %r8, %r9
	stw %r8, 160(%r31)
	lwz %r8, 164(%r31)
	lwz %r9, 932(%r5)
	xor %r8, %r8, %r9
	stw %r8, 164(%r31)
	lwz %r8, 168(%r31)
	lwz %r9, 936(%r5)
	xor %r8, %r8, %r9
	stw %r8, 168(%r31)
	lwz %r8, 172(%r31)
	lwz %r9, 940(%r5)
	xor %r8, %r8, %r9
	stw %r8, 172(%r31)
	lwz %r8, 176(%r31)
	lwz %r9, 944(%r5)
	xor %r8, %r8, %r9
	stw %r8, 176(%r31)
	lwz %r8, 180(%r31)
	lwz %r9, 948(%r5)
	xor %r8, %r8, %r9
	stw %r8, 180(%r31)
	lwz %r8, 184(%r31)
	lwz %r9, 952(%r5)
	xor %r8, %r8, %r9
	stw %r8, 184(%r31)
	lwz %r8, 188(%r31)
	lwz %r9, 956(%r5)
	xor %r8, %r8, %r9
	stw %r8, 188(%r31)
	lwz %r8, 192(%r31)
	lwz %r9, 960(%r5)
	xor %r8, %r8, %r9
	stw %r8, 192(%r31)
	lwz %r8, 196(%r31)
	lwz %r9, 964(%r5)
	xor %r8, %r8, %r9
	stw %r8, 196(%r31)
	lwz %r8, 200(%r31)
	lwz %r9, 968(%r5)
	xor %r8, %r8, %r9
	stw %r8, 200(%r31)
	lwz %r8, 204(%r31)
	lwz %r9, 972(%r5)
	xor %r8, %r8, %r9
	stw %r8, 204(%r31)
	lwz %r8, 208(%r31)
	lwz %r9, 976(%r5)
	xor %r8, %r8, %r9
	stw %r8, 208(%r31)
	lwz %r8, 212(%r31)
	lwz %r9, 980(%r5)
	xor %r8, %r8, %r9
	stw %r8, 212(%r31)
	lwz %r8, 216(%r31)
	lwz %r9, 984(%r5)
	xor %r8, %r8, %r9
	stw %r8, 216(%r31)
	lwz %r8, 220(%r31)
	lwz %r9, 988(%r5)
	xor %r8, %r8, %r9
	stw %r8, 220(%r31)
	lwz %r8, 224(%r31)
	lwz %r9, 992(%r5)
	xor %r8, %r8, %r9
	stw %r8, 224(%r31)
	lwz %r8, 228(%r31)
	lwz %r9, 996(%r5)
	xor %r8, %r8, %r9
	stw %r8, 228(%r31)
	lwz %r8, 232(%r31)
	lwz %r9, 1000(%r5)
	xor %r8, %r8, %r9
	stw %r8, 232(%r31)
	lwz %r8, 236(%r31)
	lwz %r9, 1004(%r5)
	xor %r8, %r8, %r9
	stw %r8, 236(%r31)
	lwz %r8, 240(%r31)
	lwz %r9, 1008(%r5)
	xor %r8, %r8, %r9
	stw %r8, 240(%r31)
	lwz %r8, 244(%r31)
	lwz %r9, 1012(%r5)
	xor %r8, %r8, %r9
	stw %r8, 244(%r31)
	lwz %r8, 248(%r31)
	lwz %r9, 1016(%r5)
	xor %r8, %r8, %r9
	stw %r8, 248(%r31)
	lwz %r8, 252(%r31)
	lwz %r9, 1020(%r5)
	xor %r8, %r8, %r9
	stw %r8, 252(%r31)
	addi %r31, %r31, 256
	addi %r30, %r30, -16
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	bne %cr0, 228b
	b 227f
226:
227:
	cmpldi %cr0, %r30, 0
	beq %cr0, 229f
231:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 231b
	b 230f
229:
230:
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
	b 225f
224:
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
	beq %cr0, 232f
234:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	bl {vg_sm4_serial_encrypt}
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 234b
	b 233f
232:
233:
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
225:
	addi %r3, %r30, 64
	or %r4, %r24, %r24
	or %r5, %r25, %r25
235:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 235b
	b 223f
222:
223:
	b 21f
20:
21:
	cmpldi %cr0, %r19, 0
	beq %cr0, 236f
	cmpldi %cr0, %r23, 0
	beq %cr0, 238f
	b 239f
238:
	li %r0, 15
	and %r26, %r22, %r0
	cmpldi %cr0, %r26, 0
	beq %cr0, 240f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
242:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 242b
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	bl {vg_ghash}
	b 241f
240:
241:
239:
	or %r24, %r20, %r20
	or %r25, %r19, %r19
	li %r0, 15
	and %r26, %r23, %r0
	cmpldi %cr0, %r25, 0
	beq %cr0, 243f
	cmpldi %cr0, %r26, 0
	beq %cr0, 245f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 247f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 249f
	b 250f
249:
	or %r5, %r25, %r25
250:
	b 248f
247:
248:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
251:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 251b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 252f
	b 253f
252:
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r30, 32
	li %r6, 1
	bl {vg_ghash}
253:
	b 246f
245:
246:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 254f
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	bl {vg_ghash}
	b 255f
254:
255:
	cmpldi %cr0, %r25, 0
	beq %cr0, 256f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
258:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 258b
	b 257f
256:
257:
	b 244f
243:
244:
	b 237f
236:
237:
	or %r12, %r31, %r31
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r18, 128(%r12)
	ld %r19, 136(%r12)
	ld %r20, 144(%r12)
	ld %r21, 152(%r12)
	ld %r22, 160(%r12)
	ld %r23, 168(%r12)
	ld %r24, 176(%r12)
	ld %r25, 184(%r12)
	ld %r26, 192(%r12)
	ld %r27, 200(%r12)
	ld %r28, 208(%r12)
	ld %r29, 216(%r12)
	ld %r30, 224(%r12)
	ld %r31, 232(%r12)
	addi %r1, %r1, 3296
	addi %r1, %r1, 320
	li %r0, 0
	stdu %r1, -3616(%r1)
	addi %r12, %r1, 32
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
	addi %r1, %r1, 3616
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
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v9, %v9, %v9
	vxor %v10, %v10, %v10
	vxor %v11, %v11, %v11
	vxor %v12, %v12, %v12
	vxor %v13, %v13, %v13
	vxor %v14, %v14, %v14
	vxor %v15, %v15, %v15
	vxor %v16, %v16, %v16
	vxor %v17, %v17, %v17
	vxor %v18, %v18, %v18
	vxor %v19, %v19, %v19
	blr

vg_sm4_gcm_stream_decrypt:
	stdu %r1, -320(%r1)
	addi %r9, %r1, 32
	stdu %r1, -3296(%r1)
	addi %r10, %r1, 32
	std %r18, 128(%r9)
	std %r19, 136(%r9)
	std %r20, 144(%r9)
	std %r21, 152(%r9)
	std %r22, 160(%r9)
	std %r23, 168(%r9)
	std %r24, 176(%r9)
	std %r25, 184(%r9)
	std %r26, 192(%r9)
	std %r27, 200(%r9)
	std %r28, 208(%r9)
	std %r29, 216(%r9)
	std %r30, 224(%r9)
	std %r31, 232(%r9)
	mflr %r0
	std %r0, 240(%r9)
	or %r31, %r9, %r9
	or %r30, %r4, %r4
	or %r29, %r3, %r3
	or %r22, %r5, %r5
	or %r23, %r6, %r6
	or %r20, %r7, %r7
	or %r19, %r8, %r8
	or %r28, %r10, %r10
	cmpldi %cr0, %r19, 0
	beq %cr0, 20f
	cmpldi %cr0, %r23, 0
	beq %cr0, 22f
	b 23f
22:
	li %r0, 15
	and %r26, %r22, %r0
	cmpldi %cr0, %r26, 0
	beq %cr0, 24f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
26:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 26b
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	bl {vg_ghash}
	b 25f
24:
25:
23:
	or %r24, %r20, %r20
	or %r25, %r19, %r19
	li %r0, 15
	and %r26, %r23, %r0
	cmpldi %cr0, %r25, 0
	beq %cr0, 27f
	cmpldi %cr0, %r26, 0
	beq %cr0, 29f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 211f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 213f
	b 214f
213:
	or %r5, %r25, %r25
214:
	b 212f
211:
212:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
215:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 215b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 216f
	b 217f
216:
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r30, 32
	li %r6, 1
	bl {vg_ghash}
217:
	b 210f
29:
210:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 218f
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	bl {vg_ghash}
	b 219f
218:
219:
	cmpldi %cr0, %r25, 0
	beq %cr0, 220f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
222:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 222b
	b 221f
220:
221:
	b 28f
27:
28:
	b 21f
20:
21:
	or %r24, %r20, %r20
	or %r25, %r19, %r19
	li %r0, 15
	and %r26, %r23, %r0
	cmpldi %cr0, %r25, 0
	beq %cr0, 223f
	cmpldi %cr0, %r26, 0
	beq %cr0, 225f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 227f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 229f
	b 230f
229:
	or %r5, %r25, %r25
230:
	b 228f
227:
228:
	addi %r3, %r30, 64
	add %r3, %r3, %r26
	or %r4, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
231:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 231b
	b 226f
225:
226:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 232f
	or %r3, %r29, %r29
	addi %r4, %r30, 48
	or %r7, %r28, %r28
	rldicl %r8, %r6, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 234f
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
	li %r4, 0
	li %r6, 402
	bl {vg_sm4_prepare_keys}
	or %r3, %r7, %r7
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 236f
238:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 784(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 788(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 792(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 796(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 800(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 804(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 808(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 812(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 816(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 820(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 824(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 828(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 832(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 836(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 840(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 844(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 848(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 852(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 856(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 860(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 864(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 868(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 872(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 876(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 880(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 884(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 888(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 892(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 896(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 900(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 904(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 908(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 912(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 916(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 920(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 924(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 928(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 932(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 936(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 940(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 944(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 948(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 952(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 956(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 960(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 964(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 968(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 972(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 976(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 980(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 984(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 988(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 992(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 996(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1000(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1004(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 1008(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 1012(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1016(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1020(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	lwz %r8, 16(%r31)
	lwz %r9, 784(%r5)
	xor %r8, %r8, %r9
	stw %r8, 16(%r31)
	lwz %r8, 20(%r31)
	lwz %r9, 788(%r5)
	xor %r8, %r8, %r9
	stw %r8, 20(%r31)
	lwz %r8, 24(%r31)
	lwz %r9, 792(%r5)
	xor %r8, %r8, %r9
	stw %r8, 24(%r31)
	lwz %r8, 28(%r31)
	lwz %r9, 796(%r5)
	xor %r8, %r8, %r9
	stw %r8, 28(%r31)
	lwz %r8, 32(%r31)
	lwz %r9, 800(%r5)
	xor %r8, %r8, %r9
	stw %r8, 32(%r31)
	lwz %r8, 36(%r31)
	lwz %r9, 804(%r5)
	xor %r8, %r8, %r9
	stw %r8, 36(%r31)
	lwz %r8, 40(%r31)
	lwz %r9, 808(%r5)
	xor %r8, %r8, %r9
	stw %r8, 40(%r31)
	lwz %r8, 44(%r31)
	lwz %r9, 812(%r5)
	xor %r8, %r8, %r9
	stw %r8, 44(%r31)
	lwz %r8, 48(%r31)
	lwz %r9, 816(%r5)
	xor %r8, %r8, %r9
	stw %r8, 48(%r31)
	lwz %r8, 52(%r31)
	lwz %r9, 820(%r5)
	xor %r8, %r8, %r9
	stw %r8, 52(%r31)
	lwz %r8, 56(%r31)
	lwz %r9, 824(%r5)
	xor %r8, %r8, %r9
	stw %r8, 56(%r31)
	lwz %r8, 60(%r31)
	lwz %r9, 828(%r5)
	xor %r8, %r8, %r9
	stw %r8, 60(%r31)
	lwz %r8, 64(%r31)
	lwz %r9, 832(%r5)
	xor %r8, %r8, %r9
	stw %r8, 64(%r31)
	lwz %r8, 68(%r31)
	lwz %r9, 836(%r5)
	xor %r8, %r8, %r9
	stw %r8, 68(%r31)
	lwz %r8, 72(%r31)
	lwz %r9, 840(%r5)
	xor %r8, %r8, %r9
	stw %r8, 72(%r31)
	lwz %r8, 76(%r31)
	lwz %r9, 844(%r5)
	xor %r8, %r8, %r9
	stw %r8, 76(%r31)
	lwz %r8, 80(%r31)
	lwz %r9, 848(%r5)
	xor %r8, %r8, %r9
	stw %r8, 80(%r31)
	lwz %r8, 84(%r31)
	lwz %r9, 852(%r5)
	xor %r8, %r8, %r9
	stw %r8, 84(%r31)
	lwz %r8, 88(%r31)
	lwz %r9, 856(%r5)
	xor %r8, %r8, %r9
	stw %r8, 88(%r31)
	lwz %r8, 92(%r31)
	lwz %r9, 860(%r5)
	xor %r8, %r8, %r9
	stw %r8, 92(%r31)
	lwz %r8, 96(%r31)
	lwz %r9, 864(%r5)
	xor %r8, %r8, %r9
	stw %r8, 96(%r31)
	lwz %r8, 100(%r31)
	lwz %r9, 868(%r5)
	xor %r8, %r8, %r9
	stw %r8, 100(%r31)
	lwz %r8, 104(%r31)
	lwz %r9, 872(%r5)
	xor %r8, %r8, %r9
	stw %r8, 104(%r31)
	lwz %r8, 108(%r31)
	lwz %r9, 876(%r5)
	xor %r8, %r8, %r9
	stw %r8, 108(%r31)
	lwz %r8, 112(%r31)
	lwz %r9, 880(%r5)
	xor %r8, %r8, %r9
	stw %r8, 112(%r31)
	lwz %r8, 116(%r31)
	lwz %r9, 884(%r5)
	xor %r8, %r8, %r9
	stw %r8, 116(%r31)
	lwz %r8, 120(%r31)
	lwz %r9, 888(%r5)
	xor %r8, %r8, %r9
	stw %r8, 120(%r31)
	lwz %r8, 124(%r31)
	lwz %r9, 892(%r5)
	xor %r8, %r8, %r9
	stw %r8, 124(%r31)
	lwz %r8, 128(%r31)
	lwz %r9, 896(%r5)
	xor %r8, %r8, %r9
	stw %r8, 128(%r31)
	lwz %r8, 132(%r31)
	lwz %r9, 900(%r5)
	xor %r8, %r8, %r9
	stw %r8, 132(%r31)
	lwz %r8, 136(%r31)
	lwz %r9, 904(%r5)
	xor %r8, %r8, %r9
	stw %r8, 136(%r31)
	lwz %r8, 140(%r31)
	lwz %r9, 908(%r5)
	xor %r8, %r8, %r9
	stw %r8, 140(%r31)
	lwz %r8, 144(%r31)
	lwz %r9, 912(%r5)
	xor %r8, %r8, %r9
	stw %r8, 144(%r31)
	lwz %r8, 148(%r31)
	lwz %r9, 916(%r5)
	xor %r8, %r8, %r9
	stw %r8, 148(%r31)
	lwz %r8, 152(%r31)
	lwz %r9, 920(%r5)
	xor %r8, %r8, %r9
	stw %r8, 152(%r31)
	lwz %r8, 156(%r31)
	lwz %r9, 924(%r5)
	xor %r8, %r8, %r9
	stw %r8, 156(%r31)
	lwz %r8, 160(%r31)
	lwz %r9, 928(%r5)
	xor %r8, %r8, %r9
	stw %r8, 160(%r31)
	lwz %r8, 164(%r31)
	lwz %r9, 932(%r5)
	xor %r8, %r8, %r9
	stw %r8, 164(%r31)
	lwz %r8, 168(%r31)
	lwz %r9, 936(%r5)
	xor %r8, %r8, %r9
	stw %r8, 168(%r31)
	lwz %r8, 172(%r31)
	lwz %r9, 940(%r5)
	xor %r8, %r8, %r9
	stw %r8, 172(%r31)
	lwz %r8, 176(%r31)
	lwz %r9, 944(%r5)
	xor %r8, %r8, %r9
	stw %r8, 176(%r31)
	lwz %r8, 180(%r31)
	lwz %r9, 948(%r5)
	xor %r8, %r8, %r9
	stw %r8, 180(%r31)
	lwz %r8, 184(%r31)
	lwz %r9, 952(%r5)
	xor %r8, %r8, %r9
	stw %r8, 184(%r31)
	lwz %r8, 188(%r31)
	lwz %r9, 956(%r5)
	xor %r8, %r8, %r9
	stw %r8, 188(%r31)
	lwz %r8, 192(%r31)
	lwz %r9, 960(%r5)
	xor %r8, %r8, %r9
	stw %r8, 192(%r31)
	lwz %r8, 196(%r31)
	lwz %r9, 964(%r5)
	xor %r8, %r8, %r9
	stw %r8, 196(%r31)
	lwz %r8, 200(%r31)
	lwz %r9, 968(%r5)
	xor %r8, %r8, %r9
	stw %r8, 200(%r31)
	lwz %r8, 204(%r31)
	lwz %r9, 972(%r5)
	xor %r8, %r8, %r9
	stw %r8, 204(%r31)
	lwz %r8, 208(%r31)
	lwz %r9, 976(%r5)
	xor %r8, %r8, %r9
	stw %r8, 208(%r31)
	lwz %r8, 212(%r31)
	lwz %r9, 980(%r5)
	xor %r8, %r8, %r9
	stw %r8, 212(%r31)
	lwz %r8, 216(%r31)
	lwz %r9, 984(%r5)
	xor %r8, %r8, %r9
	stw %r8, 216(%r31)
	lwz %r8, 220(%r31)
	lwz %r9, 988(%r5)
	xor %r8, %r8, %r9
	stw %r8, 220(%r31)
	lwz %r8, 224(%r31)
	lwz %r9, 992(%r5)
	xor %r8, %r8, %r9
	stw %r8, 224(%r31)
	lwz %r8, 228(%r31)
	lwz %r9, 996(%r5)
	xor %r8, %r8, %r9
	stw %r8, 228(%r31)
	lwz %r8, 232(%r31)
	lwz %r9, 1000(%r5)
	xor %r8, %r8, %r9
	stw %r8, 232(%r31)
	lwz %r8, 236(%r31)
	lwz %r9, 1004(%r5)
	xor %r8, %r8, %r9
	stw %r8, 236(%r31)
	lwz %r8, 240(%r31)
	lwz %r9, 1008(%r5)
	xor %r8, %r8, %r9
	stw %r8, 240(%r31)
	lwz %r8, 244(%r31)
	lwz %r9, 1012(%r5)
	xor %r8, %r8, %r9
	stw %r8, 244(%r31)
	lwz %r8, 248(%r31)
	lwz %r9, 1016(%r5)
	xor %r8, %r8, %r9
	stw %r8, 248(%r31)
	lwz %r8, 252(%r31)
	lwz %r9, 1020(%r5)
	xor %r8, %r8, %r9
	stw %r8, 252(%r31)
	addi %r31, %r31, 256
	addi %r30, %r30, -16
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	bne %cr0, 238b
	b 237f
236:
237:
	cmpldi %cr0, %r30, 0
	beq %cr0, 239f
241:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 241b
	b 240f
239:
240:
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
	b 235f
234:
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
	beq %cr0, 242f
244:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	bl {vg_sm4_serial_encrypt}
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 244b
	b 243f
242:
243:
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
235:
	b 233f
232:
233:
	cmpldi %cr0, %r25, 0
	beq %cr0, 245f
	li %r0, 0
	std %r0, 64(%r30)
	std %r0, 72(%r30)
	addi %r5, %r30, 64
	li %r6, 1
	or %r3, %r29, %r29
	addi %r4, %r30, 48
	or %r7, %r28, %r28
	rldicl %r8, %r6, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 247f
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
	li %r4, 0
	li %r6, 402
	bl {vg_sm4_prepare_keys}
	or %r3, %r7, %r7
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 249f
251:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 784(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 788(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 792(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 796(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 800(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 804(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 808(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 812(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 816(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 820(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 824(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 828(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 832(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 836(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 840(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 844(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 848(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 852(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 856(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 860(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 864(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 868(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 872(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 876(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 880(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 884(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 888(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 892(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 896(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 900(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 904(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 908(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 912(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 916(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 920(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 924(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 928(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 932(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 936(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 940(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 944(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 948(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 952(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 956(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 960(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 964(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 968(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 972(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 976(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 980(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 984(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 988(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 992(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 996(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1000(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1004(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 1008(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 1012(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1016(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1020(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	lwz %r8, 16(%r31)
	lwz %r9, 784(%r5)
	xor %r8, %r8, %r9
	stw %r8, 16(%r31)
	lwz %r8, 20(%r31)
	lwz %r9, 788(%r5)
	xor %r8, %r8, %r9
	stw %r8, 20(%r31)
	lwz %r8, 24(%r31)
	lwz %r9, 792(%r5)
	xor %r8, %r8, %r9
	stw %r8, 24(%r31)
	lwz %r8, 28(%r31)
	lwz %r9, 796(%r5)
	xor %r8, %r8, %r9
	stw %r8, 28(%r31)
	lwz %r8, 32(%r31)
	lwz %r9, 800(%r5)
	xor %r8, %r8, %r9
	stw %r8, 32(%r31)
	lwz %r8, 36(%r31)
	lwz %r9, 804(%r5)
	xor %r8, %r8, %r9
	stw %r8, 36(%r31)
	lwz %r8, 40(%r31)
	lwz %r9, 808(%r5)
	xor %r8, %r8, %r9
	stw %r8, 40(%r31)
	lwz %r8, 44(%r31)
	lwz %r9, 812(%r5)
	xor %r8, %r8, %r9
	stw %r8, 44(%r31)
	lwz %r8, 48(%r31)
	lwz %r9, 816(%r5)
	xor %r8, %r8, %r9
	stw %r8, 48(%r31)
	lwz %r8, 52(%r31)
	lwz %r9, 820(%r5)
	xor %r8, %r8, %r9
	stw %r8, 52(%r31)
	lwz %r8, 56(%r31)
	lwz %r9, 824(%r5)
	xor %r8, %r8, %r9
	stw %r8, 56(%r31)
	lwz %r8, 60(%r31)
	lwz %r9, 828(%r5)
	xor %r8, %r8, %r9
	stw %r8, 60(%r31)
	lwz %r8, 64(%r31)
	lwz %r9, 832(%r5)
	xor %r8, %r8, %r9
	stw %r8, 64(%r31)
	lwz %r8, 68(%r31)
	lwz %r9, 836(%r5)
	xor %r8, %r8, %r9
	stw %r8, 68(%r31)
	lwz %r8, 72(%r31)
	lwz %r9, 840(%r5)
	xor %r8, %r8, %r9
	stw %r8, 72(%r31)
	lwz %r8, 76(%r31)
	lwz %r9, 844(%r5)
	xor %r8, %r8, %r9
	stw %r8, 76(%r31)
	lwz %r8, 80(%r31)
	lwz %r9, 848(%r5)
	xor %r8, %r8, %r9
	stw %r8, 80(%r31)
	lwz %r8, 84(%r31)
	lwz %r9, 852(%r5)
	xor %r8, %r8, %r9
	stw %r8, 84(%r31)
	lwz %r8, 88(%r31)
	lwz %r9, 856(%r5)
	xor %r8, %r8, %r9
	stw %r8, 88(%r31)
	lwz %r8, 92(%r31)
	lwz %r9, 860(%r5)
	xor %r8, %r8, %r9
	stw %r8, 92(%r31)
	lwz %r8, 96(%r31)
	lwz %r9, 864(%r5)
	xor %r8, %r8, %r9
	stw %r8, 96(%r31)
	lwz %r8, 100(%r31)
	lwz %r9, 868(%r5)
	xor %r8, %r8, %r9
	stw %r8, 100(%r31)
	lwz %r8, 104(%r31)
	lwz %r9, 872(%r5)
	xor %r8, %r8, %r9
	stw %r8, 104(%r31)
	lwz %r8, 108(%r31)
	lwz %r9, 876(%r5)
	xor %r8, %r8, %r9
	stw %r8, 108(%r31)
	lwz %r8, 112(%r31)
	lwz %r9, 880(%r5)
	xor %r8, %r8, %r9
	stw %r8, 112(%r31)
	lwz %r8, 116(%r31)
	lwz %r9, 884(%r5)
	xor %r8, %r8, %r9
	stw %r8, 116(%r31)
	lwz %r8, 120(%r31)
	lwz %r9, 888(%r5)
	xor %r8, %r8, %r9
	stw %r8, 120(%r31)
	lwz %r8, 124(%r31)
	lwz %r9, 892(%r5)
	xor %r8, %r8, %r9
	stw %r8, 124(%r31)
	lwz %r8, 128(%r31)
	lwz %r9, 896(%r5)
	xor %r8, %r8, %r9
	stw %r8, 128(%r31)
	lwz %r8, 132(%r31)
	lwz %r9, 900(%r5)
	xor %r8, %r8, %r9
	stw %r8, 132(%r31)
	lwz %r8, 136(%r31)
	lwz %r9, 904(%r5)
	xor %r8, %r8, %r9
	stw %r8, 136(%r31)
	lwz %r8, 140(%r31)
	lwz %r9, 908(%r5)
	xor %r8, %r8, %r9
	stw %r8, 140(%r31)
	lwz %r8, 144(%r31)
	lwz %r9, 912(%r5)
	xor %r8, %r8, %r9
	stw %r8, 144(%r31)
	lwz %r8, 148(%r31)
	lwz %r9, 916(%r5)
	xor %r8, %r8, %r9
	stw %r8, 148(%r31)
	lwz %r8, 152(%r31)
	lwz %r9, 920(%r5)
	xor %r8, %r8, %r9
	stw %r8, 152(%r31)
	lwz %r8, 156(%r31)
	lwz %r9, 924(%r5)
	xor %r8, %r8, %r9
	stw %r8, 156(%r31)
	lwz %r8, 160(%r31)
	lwz %r9, 928(%r5)
	xor %r8, %r8, %r9
	stw %r8, 160(%r31)
	lwz %r8, 164(%r31)
	lwz %r9, 932(%r5)
	xor %r8, %r8, %r9
	stw %r8, 164(%r31)
	lwz %r8, 168(%r31)
	lwz %r9, 936(%r5)
	xor %r8, %r8, %r9
	stw %r8, 168(%r31)
	lwz %r8, 172(%r31)
	lwz %r9, 940(%r5)
	xor %r8, %r8, %r9
	stw %r8, 172(%r31)
	lwz %r8, 176(%r31)
	lwz %r9, 944(%r5)
	xor %r8, %r8, %r9
	stw %r8, 176(%r31)
	lwz %r8, 180(%r31)
	lwz %r9, 948(%r5)
	xor %r8, %r8, %r9
	stw %r8, 180(%r31)
	lwz %r8, 184(%r31)
	lwz %r9, 952(%r5)
	xor %r8, %r8, %r9
	stw %r8, 184(%r31)
	lwz %r8, 188(%r31)
	lwz %r9, 956(%r5)
	xor %r8, %r8, %r9
	stw %r8, 188(%r31)
	lwz %r8, 192(%r31)
	lwz %r9, 960(%r5)
	xor %r8, %r8, %r9
	stw %r8, 192(%r31)
	lwz %r8, 196(%r31)
	lwz %r9, 964(%r5)
	xor %r8, %r8, %r9
	stw %r8, 196(%r31)
	lwz %r8, 200(%r31)
	lwz %r9, 968(%r5)
	xor %r8, %r8, %r9
	stw %r8, 200(%r31)
	lwz %r8, 204(%r31)
	lwz %r9, 972(%r5)
	xor %r8, %r8, %r9
	stw %r8, 204(%r31)
	lwz %r8, 208(%r31)
	lwz %r9, 976(%r5)
	xor %r8, %r8, %r9
	stw %r8, 208(%r31)
	lwz %r8, 212(%r31)
	lwz %r9, 980(%r5)
	xor %r8, %r8, %r9
	stw %r8, 212(%r31)
	lwz %r8, 216(%r31)
	lwz %r9, 984(%r5)
	xor %r8, %r8, %r9
	stw %r8, 216(%r31)
	lwz %r8, 220(%r31)
	lwz %r9, 988(%r5)
	xor %r8, %r8, %r9
	stw %r8, 220(%r31)
	lwz %r8, 224(%r31)
	lwz %r9, 992(%r5)
	xor %r8, %r8, %r9
	stw %r8, 224(%r31)
	lwz %r8, 228(%r31)
	lwz %r9, 996(%r5)
	xor %r8, %r8, %r9
	stw %r8, 228(%r31)
	lwz %r8, 232(%r31)
	lwz %r9, 1000(%r5)
	xor %r8, %r8, %r9
	stw %r8, 232(%r31)
	lwz %r8, 236(%r31)
	lwz %r9, 1004(%r5)
	xor %r8, %r8, %r9
	stw %r8, 236(%r31)
	lwz %r8, 240(%r31)
	lwz %r9, 1008(%r5)
	xor %r8, %r8, %r9
	stw %r8, 240(%r31)
	lwz %r8, 244(%r31)
	lwz %r9, 1012(%r5)
	xor %r8, %r8, %r9
	stw %r8, 244(%r31)
	lwz %r8, 248(%r31)
	lwz %r9, 1016(%r5)
	xor %r8, %r8, %r9
	stw %r8, 248(%r31)
	lwz %r8, 252(%r31)
	lwz %r9, 1020(%r5)
	xor %r8, %r8, %r9
	stw %r8, 252(%r31)
	addi %r31, %r31, 256
	addi %r30, %r30, -16
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	bne %cr0, 251b
	b 250f
249:
250:
	cmpldi %cr0, %r30, 0
	beq %cr0, 252f
254:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 254b
	b 253f
252:
253:
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
	b 248f
247:
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
	beq %cr0, 255f
257:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	bl {vg_sm4_serial_encrypt}
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 257b
	b 256f
255:
256:
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
248:
	addi %r3, %r30, 64
	or %r4, %r24, %r24
	or %r5, %r25, %r25
258:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 258b
	b 246f
245:
246:
	b 224f
223:
224:
	or %r12, %r31, %r31
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r18, 128(%r12)
	ld %r19, 136(%r12)
	ld %r20, 144(%r12)
	ld %r21, 152(%r12)
	ld %r22, 160(%r12)
	ld %r23, 168(%r12)
	ld %r24, 176(%r12)
	ld %r25, 184(%r12)
	ld %r26, 192(%r12)
	ld %r27, 200(%r12)
	ld %r28, 208(%r12)
	ld %r29, 216(%r12)
	ld %r30, 224(%r12)
	ld %r31, 232(%r12)
	addi %r1, %r1, 3296
	addi %r1, %r1, 320
	li %r0, 0
	stdu %r1, -3616(%r1)
	addi %r12, %r1, 32
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
	addi %r1, %r1, 3616
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
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v9, %v9, %v9
	vxor %v10, %v10, %v10
	vxor %v11, %v11, %v11
	vxor %v12, %v12, %v12
	vxor %v13, %v13, %v13
	vxor %v14, %v14, %v14
	vxor %v15, %v15, %v15
	vxor %v16, %v16, %v16
	vxor %v17, %v17, %v17
	vxor %v18, %v18, %v18
	vxor %v19, %v19, %v19
	blr

vg_sm4_gcm_stream_finish:
	stdu %r1, -320(%r1)
	addi %r8, %r1, 32
	stdu %r1, -3296(%r1)
	addi %r9, %r1, 32
	std %r18, 128(%r8)
	std %r19, 136(%r8)
	std %r20, 144(%r8)
	std %r21, 152(%r8)
	std %r22, 160(%r8)
	std %r23, 168(%r8)
	std %r24, 176(%r8)
	std %r25, 184(%r8)
	std %r26, 192(%r8)
	std %r27, 200(%r8)
	std %r28, 208(%r8)
	std %r29, 216(%r8)
	std %r30, 224(%r8)
	std %r31, 232(%r8)
	mflr %r0
	std %r0, 240(%r8)
	or %r31, %r8, %r8
	or %r30, %r4, %r4
	or %r29, %r3, %r3
	or %r22, %r5, %r5
	or %r23, %r6, %r6
	or %r20, %r7, %r7
	or %r28, %r9, %r9
	cmpldi %cr0, %r23, 0
	beq %cr0, 20f
	li %r0, 15
	and %r26, %r23, %r0
	b 21f
20:
	li %r0, 15
	and %r26, %r22, %r0
21:
	cmpldi %cr0, %r26, 0
	beq %cr0, 22f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
24:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 24b
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	bl {vg_ghash}
	b 23f
22:
23:
	or %r24, %r22, %r22
	or %r26, %r23, %r23
	rldicr %r3, %r24, 3, 60
	rldicr %r4, %r26, 3, 60
	addi %r5, %r31, 96
	li %r6, 0
	stdbrx %r3, %r5, %r6
	li %r6, 8
	stdbrx %r4, %r5, %r6
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	bl {vg_ghash}
	ld %r3, 16(%r30)
	std %r3, 0(%r31)
	ld %r3, 24(%r30)
	std %r3, 8(%r31)
	or %r3, %r29, %r29
	or %r4, %r30, %r30
	addi %r5, %r31, 0
	li %r6, 1
	or %r7, %r28, %r28
	rldicl %r8, %r6, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 25f
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
	li %r4, 0
	li %r6, 402
	bl {vg_sm4_prepare_keys}
	or %r3, %r7, %r7
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 27f
29:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 784(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 788(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 792(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 796(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 800(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 804(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 808(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 812(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 816(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 820(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 824(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 828(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 832(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 836(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 840(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 844(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 848(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 852(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 856(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 860(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 864(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 868(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 872(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 876(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 880(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 884(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 888(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 892(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 896(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 900(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 904(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 908(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 912(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 916(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 920(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 924(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 928(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 932(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 936(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 940(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 944(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 948(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 952(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 956(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 960(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 964(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 968(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 972(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 976(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 980(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 984(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 988(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 992(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 996(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1000(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1004(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 1008(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 1012(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1016(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1020(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	lwz %r8, 16(%r31)
	lwz %r9, 784(%r5)
	xor %r8, %r8, %r9
	stw %r8, 16(%r31)
	lwz %r8, 20(%r31)
	lwz %r9, 788(%r5)
	xor %r8, %r8, %r9
	stw %r8, 20(%r31)
	lwz %r8, 24(%r31)
	lwz %r9, 792(%r5)
	xor %r8, %r8, %r9
	stw %r8, 24(%r31)
	lwz %r8, 28(%r31)
	lwz %r9, 796(%r5)
	xor %r8, %r8, %r9
	stw %r8, 28(%r31)
	lwz %r8, 32(%r31)
	lwz %r9, 800(%r5)
	xor %r8, %r8, %r9
	stw %r8, 32(%r31)
	lwz %r8, 36(%r31)
	lwz %r9, 804(%r5)
	xor %r8, %r8, %r9
	stw %r8, 36(%r31)
	lwz %r8, 40(%r31)
	lwz %r9, 808(%r5)
	xor %r8, %r8, %r9
	stw %r8, 40(%r31)
	lwz %r8, 44(%r31)
	lwz %r9, 812(%r5)
	xor %r8, %r8, %r9
	stw %r8, 44(%r31)
	lwz %r8, 48(%r31)
	lwz %r9, 816(%r5)
	xor %r8, %r8, %r9
	stw %r8, 48(%r31)
	lwz %r8, 52(%r31)
	lwz %r9, 820(%r5)
	xor %r8, %r8, %r9
	stw %r8, 52(%r31)
	lwz %r8, 56(%r31)
	lwz %r9, 824(%r5)
	xor %r8, %r8, %r9
	stw %r8, 56(%r31)
	lwz %r8, 60(%r31)
	lwz %r9, 828(%r5)
	xor %r8, %r8, %r9
	stw %r8, 60(%r31)
	lwz %r8, 64(%r31)
	lwz %r9, 832(%r5)
	xor %r8, %r8, %r9
	stw %r8, 64(%r31)
	lwz %r8, 68(%r31)
	lwz %r9, 836(%r5)
	xor %r8, %r8, %r9
	stw %r8, 68(%r31)
	lwz %r8, 72(%r31)
	lwz %r9, 840(%r5)
	xor %r8, %r8, %r9
	stw %r8, 72(%r31)
	lwz %r8, 76(%r31)
	lwz %r9, 844(%r5)
	xor %r8, %r8, %r9
	stw %r8, 76(%r31)
	lwz %r8, 80(%r31)
	lwz %r9, 848(%r5)
	xor %r8, %r8, %r9
	stw %r8, 80(%r31)
	lwz %r8, 84(%r31)
	lwz %r9, 852(%r5)
	xor %r8, %r8, %r9
	stw %r8, 84(%r31)
	lwz %r8, 88(%r31)
	lwz %r9, 856(%r5)
	xor %r8, %r8, %r9
	stw %r8, 88(%r31)
	lwz %r8, 92(%r31)
	lwz %r9, 860(%r5)
	xor %r8, %r8, %r9
	stw %r8, 92(%r31)
	lwz %r8, 96(%r31)
	lwz %r9, 864(%r5)
	xor %r8, %r8, %r9
	stw %r8, 96(%r31)
	lwz %r8, 100(%r31)
	lwz %r9, 868(%r5)
	xor %r8, %r8, %r9
	stw %r8, 100(%r31)
	lwz %r8, 104(%r31)
	lwz %r9, 872(%r5)
	xor %r8, %r8, %r9
	stw %r8, 104(%r31)
	lwz %r8, 108(%r31)
	lwz %r9, 876(%r5)
	xor %r8, %r8, %r9
	stw %r8, 108(%r31)
	lwz %r8, 112(%r31)
	lwz %r9, 880(%r5)
	xor %r8, %r8, %r9
	stw %r8, 112(%r31)
	lwz %r8, 116(%r31)
	lwz %r9, 884(%r5)
	xor %r8, %r8, %r9
	stw %r8, 116(%r31)
	lwz %r8, 120(%r31)
	lwz %r9, 888(%r5)
	xor %r8, %r8, %r9
	stw %r8, 120(%r31)
	lwz %r8, 124(%r31)
	lwz %r9, 892(%r5)
	xor %r8, %r8, %r9
	stw %r8, 124(%r31)
	lwz %r8, 128(%r31)
	lwz %r9, 896(%r5)
	xor %r8, %r8, %r9
	stw %r8, 128(%r31)
	lwz %r8, 132(%r31)
	lwz %r9, 900(%r5)
	xor %r8, %r8, %r9
	stw %r8, 132(%r31)
	lwz %r8, 136(%r31)
	lwz %r9, 904(%r5)
	xor %r8, %r8, %r9
	stw %r8, 136(%r31)
	lwz %r8, 140(%r31)
	lwz %r9, 908(%r5)
	xor %r8, %r8, %r9
	stw %r8, 140(%r31)
	lwz %r8, 144(%r31)
	lwz %r9, 912(%r5)
	xor %r8, %r8, %r9
	stw %r8, 144(%r31)
	lwz %r8, 148(%r31)
	lwz %r9, 916(%r5)
	xor %r8, %r8, %r9
	stw %r8, 148(%r31)
	lwz %r8, 152(%r31)
	lwz %r9, 920(%r5)
	xor %r8, %r8, %r9
	stw %r8, 152(%r31)
	lwz %r8, 156(%r31)
	lwz %r9, 924(%r5)
	xor %r8, %r8, %r9
	stw %r8, 156(%r31)
	lwz %r8, 160(%r31)
	lwz %r9, 928(%r5)
	xor %r8, %r8, %r9
	stw %r8, 160(%r31)
	lwz %r8, 164(%r31)
	lwz %r9, 932(%r5)
	xor %r8, %r8, %r9
	stw %r8, 164(%r31)
	lwz %r8, 168(%r31)
	lwz %r9, 936(%r5)
	xor %r8, %r8, %r9
	stw %r8, 168(%r31)
	lwz %r8, 172(%r31)
	lwz %r9, 940(%r5)
	xor %r8, %r8, %r9
	stw %r8, 172(%r31)
	lwz %r8, 176(%r31)
	lwz %r9, 944(%r5)
	xor %r8, %r8, %r9
	stw %r8, 176(%r31)
	lwz %r8, 180(%r31)
	lwz %r9, 948(%r5)
	xor %r8, %r8, %r9
	stw %r8, 180(%r31)
	lwz %r8, 184(%r31)
	lwz %r9, 952(%r5)
	xor %r8, %r8, %r9
	stw %r8, 184(%r31)
	lwz %r8, 188(%r31)
	lwz %r9, 956(%r5)
	xor %r8, %r8, %r9
	stw %r8, 188(%r31)
	lwz %r8, 192(%r31)
	lwz %r9, 960(%r5)
	xor %r8, %r8, %r9
	stw %r8, 192(%r31)
	lwz %r8, 196(%r31)
	lwz %r9, 964(%r5)
	xor %r8, %r8, %r9
	stw %r8, 196(%r31)
	lwz %r8, 200(%r31)
	lwz %r9, 968(%r5)
	xor %r8, %r8, %r9
	stw %r8, 200(%r31)
	lwz %r8, 204(%r31)
	lwz %r9, 972(%r5)
	xor %r8, %r8, %r9
	stw %r8, 204(%r31)
	lwz %r8, 208(%r31)
	lwz %r9, 976(%r5)
	xor %r8, %r8, %r9
	stw %r8, 208(%r31)
	lwz %r8, 212(%r31)
	lwz %r9, 980(%r5)
	xor %r8, %r8, %r9
	stw %r8, 212(%r31)
	lwz %r8, 216(%r31)
	lwz %r9, 984(%r5)
	xor %r8, %r8, %r9
	stw %r8, 216(%r31)
	lwz %r8, 220(%r31)
	lwz %r9, 988(%r5)
	xor %r8, %r8, %r9
	stw %r8, 220(%r31)
	lwz %r8, 224(%r31)
	lwz %r9, 992(%r5)
	xor %r8, %r8, %r9
	stw %r8, 224(%r31)
	lwz %r8, 228(%r31)
	lwz %r9, 996(%r5)
	xor %r8, %r8, %r9
	stw %r8, 228(%r31)
	lwz %r8, 232(%r31)
	lwz %r9, 1000(%r5)
	xor %r8, %r8, %r9
	stw %r8, 232(%r31)
	lwz %r8, 236(%r31)
	lwz %r9, 1004(%r5)
	xor %r8, %r8, %r9
	stw %r8, 236(%r31)
	lwz %r8, 240(%r31)
	lwz %r9, 1008(%r5)
	xor %r8, %r8, %r9
	stw %r8, 240(%r31)
	lwz %r8, 244(%r31)
	lwz %r9, 1012(%r5)
	xor %r8, %r8, %r9
	stw %r8, 244(%r31)
	lwz %r8, 248(%r31)
	lwz %r9, 1016(%r5)
	xor %r8, %r8, %r9
	stw %r8, 248(%r31)
	lwz %r8, 252(%r31)
	lwz %r9, 1020(%r5)
	xor %r8, %r8, %r9
	stw %r8, 252(%r31)
	addi %r31, %r31, 256
	addi %r30, %r30, -16
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	bne %cr0, 29b
	b 28f
27:
28:
	cmpldi %cr0, %r30, 0
	beq %cr0, 210f
212:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 212b
	b 211f
210:
211:
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
	b 26f
25:
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
	beq %cr0, 213f
215:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	bl {vg_sm4_serial_encrypt}
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 215b
	b 214f
213:
214:
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
26:
	ld %r3, 0(%r31)
	std %r3, 0(%r20)
	ld %r3, 8(%r31)
	std %r3, 8(%r20)
	or %r12, %r31, %r31
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r18, 128(%r12)
	ld %r19, 136(%r12)
	ld %r20, 144(%r12)
	ld %r21, 152(%r12)
	ld %r22, 160(%r12)
	ld %r23, 168(%r12)
	ld %r24, 176(%r12)
	ld %r25, 184(%r12)
	ld %r26, 192(%r12)
	ld %r27, 200(%r12)
	ld %r28, 208(%r12)
	ld %r29, 216(%r12)
	ld %r30, 224(%r12)
	ld %r31, 232(%r12)
	addi %r1, %r1, 3296
	addi %r1, %r1, 320
	li %r0, 0
	stdu %r1, -3616(%r1)
	addi %r12, %r1, 32
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
	addi %r1, %r1, 3616
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
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v9, %v9, %v9
	vxor %v10, %v10, %v10
	vxor %v11, %v11, %v11
	vxor %v12, %v12, %v12
	vxor %v13, %v13, %v13
	vxor %v14, %v14, %v14
	vxor %v15, %v15, %v15
	vxor %v16, %v16, %v16
	vxor %v17, %v17, %v17
	vxor %v18, %v18, %v18
	vxor %v19, %v19, %v19
	blr

vg_sm4_gcm_stream_verify:
	stdu %r1, -320(%r1)
	addi %r9, %r1, 32
	stdu %r1, -3296(%r1)
	addi %r10, %r1, 32
	std %r18, 128(%r9)
	std %r19, 136(%r9)
	std %r20, 144(%r9)
	std %r21, 152(%r9)
	std %r22, 160(%r9)
	std %r23, 168(%r9)
	std %r24, 176(%r9)
	std %r25, 184(%r9)
	std %r26, 192(%r9)
	std %r27, 200(%r9)
	std %r28, 208(%r9)
	std %r29, 216(%r9)
	std %r30, 224(%r9)
	std %r31, 232(%r9)
	mflr %r0
	std %r0, 240(%r9)
	or %r31, %r9, %r9
	or %r30, %r4, %r4
	or %r29, %r3, %r3
	or %r22, %r5, %r5
	or %r23, %r6, %r6
	or %r20, %r7, %r7
	or %r19, %r8, %r8
	or %r28, %r10, %r10
	li %r25, 0
	rldicl %r0, %r19, 62, 2
	cmpldi %cr0, %r0, 0
	beq %cr0, 20f
	rldicl %r0, %r19, 60, 4
	cmpldi %cr0, %r0, 0
	beq %cr0, 22f
	addi %r0, %r19, -16
	cmpldi %cr0, %r0, 0
	beq %cr0, 24f
	b 25f
24:
	li %r25, 1
25:
	b 23f
22:
	li %r25, 1
23:
	b 21f
20:
21:
	cmpldi %cr0, %r25, 0
	beq %cr0, 26f
	li %r0, 0
	std %r0, 256(%r31)
	std %r0, 264(%r31)
	or %r3, %r20, %r20
	addi %r4, %r31, 256
	or %r5, %r19, %r19
28:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 28b
	cmpldi %cr0, %r23, 0
	beq %cr0, 29f
	li %r0, 15
	and %r26, %r23, %r0
	b 210f
29:
	li %r0, 15
	and %r26, %r22, %r0
210:
	cmpldi %cr0, %r26, 0
	beq %cr0, 211f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
213:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 213b
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	bl {vg_ghash}
	b 212f
211:
212:
	or %r24, %r22, %r22
	or %r26, %r23, %r23
	rldicr %r3, %r24, 3, 60
	rldicr %r4, %r26, 3, 60
	addi %r5, %r31, 96
	li %r6, 0
	stdbrx %r3, %r5, %r6
	li %r6, 8
	stdbrx %r4, %r5, %r6
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	bl {vg_ghash}
	ld %r3, 16(%r30)
	std %r3, 0(%r31)
	ld %r3, 24(%r30)
	std %r3, 8(%r31)
	or %r3, %r29, %r29
	or %r4, %r30, %r30
	addi %r5, %r31, 0
	li %r6, 1
	or %r7, %r28, %r28
	rldicl %r8, %r6, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 214f
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
	li %r4, 0
	li %r6, 402
	bl {vg_sm4_prepare_keys}
	or %r3, %r7, %r7
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	beq %cr0, 216f
218:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 784(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 788(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 792(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 796(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 800(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 804(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 808(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 812(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 816(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 820(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 824(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 828(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 832(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 836(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 840(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 844(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 848(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 852(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 856(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 860(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 864(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 868(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 872(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 876(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 880(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 884(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 888(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 892(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 896(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 900(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 904(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 908(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 912(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 916(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 920(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 924(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 928(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 932(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 936(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 940(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 944(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 948(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 952(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 956(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 960(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 964(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 968(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 972(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 976(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 980(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 984(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 988(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 992(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 996(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1000(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1004(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	lwz %r8, 3248(%r5)
	stw %r8, 1008(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 1012(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 1016(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 1020(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	lwz %r8, 16(%r31)
	lwz %r9, 784(%r5)
	xor %r8, %r8, %r9
	stw %r8, 16(%r31)
	lwz %r8, 20(%r31)
	lwz %r9, 788(%r5)
	xor %r8, %r8, %r9
	stw %r8, 20(%r31)
	lwz %r8, 24(%r31)
	lwz %r9, 792(%r5)
	xor %r8, %r8, %r9
	stw %r8, 24(%r31)
	lwz %r8, 28(%r31)
	lwz %r9, 796(%r5)
	xor %r8, %r8, %r9
	stw %r8, 28(%r31)
	lwz %r8, 32(%r31)
	lwz %r9, 800(%r5)
	xor %r8, %r8, %r9
	stw %r8, 32(%r31)
	lwz %r8, 36(%r31)
	lwz %r9, 804(%r5)
	xor %r8, %r8, %r9
	stw %r8, 36(%r31)
	lwz %r8, 40(%r31)
	lwz %r9, 808(%r5)
	xor %r8, %r8, %r9
	stw %r8, 40(%r31)
	lwz %r8, 44(%r31)
	lwz %r9, 812(%r5)
	xor %r8, %r8, %r9
	stw %r8, 44(%r31)
	lwz %r8, 48(%r31)
	lwz %r9, 816(%r5)
	xor %r8, %r8, %r9
	stw %r8, 48(%r31)
	lwz %r8, 52(%r31)
	lwz %r9, 820(%r5)
	xor %r8, %r8, %r9
	stw %r8, 52(%r31)
	lwz %r8, 56(%r31)
	lwz %r9, 824(%r5)
	xor %r8, %r8, %r9
	stw %r8, 56(%r31)
	lwz %r8, 60(%r31)
	lwz %r9, 828(%r5)
	xor %r8, %r8, %r9
	stw %r8, 60(%r31)
	lwz %r8, 64(%r31)
	lwz %r9, 832(%r5)
	xor %r8, %r8, %r9
	stw %r8, 64(%r31)
	lwz %r8, 68(%r31)
	lwz %r9, 836(%r5)
	xor %r8, %r8, %r9
	stw %r8, 68(%r31)
	lwz %r8, 72(%r31)
	lwz %r9, 840(%r5)
	xor %r8, %r8, %r9
	stw %r8, 72(%r31)
	lwz %r8, 76(%r31)
	lwz %r9, 844(%r5)
	xor %r8, %r8, %r9
	stw %r8, 76(%r31)
	lwz %r8, 80(%r31)
	lwz %r9, 848(%r5)
	xor %r8, %r8, %r9
	stw %r8, 80(%r31)
	lwz %r8, 84(%r31)
	lwz %r9, 852(%r5)
	xor %r8, %r8, %r9
	stw %r8, 84(%r31)
	lwz %r8, 88(%r31)
	lwz %r9, 856(%r5)
	xor %r8, %r8, %r9
	stw %r8, 88(%r31)
	lwz %r8, 92(%r31)
	lwz %r9, 860(%r5)
	xor %r8, %r8, %r9
	stw %r8, 92(%r31)
	lwz %r8, 96(%r31)
	lwz %r9, 864(%r5)
	xor %r8, %r8, %r9
	stw %r8, 96(%r31)
	lwz %r8, 100(%r31)
	lwz %r9, 868(%r5)
	xor %r8, %r8, %r9
	stw %r8, 100(%r31)
	lwz %r8, 104(%r31)
	lwz %r9, 872(%r5)
	xor %r8, %r8, %r9
	stw %r8, 104(%r31)
	lwz %r8, 108(%r31)
	lwz %r9, 876(%r5)
	xor %r8, %r8, %r9
	stw %r8, 108(%r31)
	lwz %r8, 112(%r31)
	lwz %r9, 880(%r5)
	xor %r8, %r8, %r9
	stw %r8, 112(%r31)
	lwz %r8, 116(%r31)
	lwz %r9, 884(%r5)
	xor %r8, %r8, %r9
	stw %r8, 116(%r31)
	lwz %r8, 120(%r31)
	lwz %r9, 888(%r5)
	xor %r8, %r8, %r9
	stw %r8, 120(%r31)
	lwz %r8, 124(%r31)
	lwz %r9, 892(%r5)
	xor %r8, %r8, %r9
	stw %r8, 124(%r31)
	lwz %r8, 128(%r31)
	lwz %r9, 896(%r5)
	xor %r8, %r8, %r9
	stw %r8, 128(%r31)
	lwz %r8, 132(%r31)
	lwz %r9, 900(%r5)
	xor %r8, %r8, %r9
	stw %r8, 132(%r31)
	lwz %r8, 136(%r31)
	lwz %r9, 904(%r5)
	xor %r8, %r8, %r9
	stw %r8, 136(%r31)
	lwz %r8, 140(%r31)
	lwz %r9, 908(%r5)
	xor %r8, %r8, %r9
	stw %r8, 140(%r31)
	lwz %r8, 144(%r31)
	lwz %r9, 912(%r5)
	xor %r8, %r8, %r9
	stw %r8, 144(%r31)
	lwz %r8, 148(%r31)
	lwz %r9, 916(%r5)
	xor %r8, %r8, %r9
	stw %r8, 148(%r31)
	lwz %r8, 152(%r31)
	lwz %r9, 920(%r5)
	xor %r8, %r8, %r9
	stw %r8, 152(%r31)
	lwz %r8, 156(%r31)
	lwz %r9, 924(%r5)
	xor %r8, %r8, %r9
	stw %r8, 156(%r31)
	lwz %r8, 160(%r31)
	lwz %r9, 928(%r5)
	xor %r8, %r8, %r9
	stw %r8, 160(%r31)
	lwz %r8, 164(%r31)
	lwz %r9, 932(%r5)
	xor %r8, %r8, %r9
	stw %r8, 164(%r31)
	lwz %r8, 168(%r31)
	lwz %r9, 936(%r5)
	xor %r8, %r8, %r9
	stw %r8, 168(%r31)
	lwz %r8, 172(%r31)
	lwz %r9, 940(%r5)
	xor %r8, %r8, %r9
	stw %r8, 172(%r31)
	lwz %r8, 176(%r31)
	lwz %r9, 944(%r5)
	xor %r8, %r8, %r9
	stw %r8, 176(%r31)
	lwz %r8, 180(%r31)
	lwz %r9, 948(%r5)
	xor %r8, %r8, %r9
	stw %r8, 180(%r31)
	lwz %r8, 184(%r31)
	lwz %r9, 952(%r5)
	xor %r8, %r8, %r9
	stw %r8, 184(%r31)
	lwz %r8, 188(%r31)
	lwz %r9, 956(%r5)
	xor %r8, %r8, %r9
	stw %r8, 188(%r31)
	lwz %r8, 192(%r31)
	lwz %r9, 960(%r5)
	xor %r8, %r8, %r9
	stw %r8, 192(%r31)
	lwz %r8, 196(%r31)
	lwz %r9, 964(%r5)
	xor %r8, %r8, %r9
	stw %r8, 196(%r31)
	lwz %r8, 200(%r31)
	lwz %r9, 968(%r5)
	xor %r8, %r8, %r9
	stw %r8, 200(%r31)
	lwz %r8, 204(%r31)
	lwz %r9, 972(%r5)
	xor %r8, %r8, %r9
	stw %r8, 204(%r31)
	lwz %r8, 208(%r31)
	lwz %r9, 976(%r5)
	xor %r8, %r8, %r9
	stw %r8, 208(%r31)
	lwz %r8, 212(%r31)
	lwz %r9, 980(%r5)
	xor %r8, %r8, %r9
	stw %r8, 212(%r31)
	lwz %r8, 216(%r31)
	lwz %r9, 984(%r5)
	xor %r8, %r8, %r9
	stw %r8, 216(%r31)
	lwz %r8, 220(%r31)
	lwz %r9, 988(%r5)
	xor %r8, %r8, %r9
	stw %r8, 220(%r31)
	lwz %r8, 224(%r31)
	lwz %r9, 992(%r5)
	xor %r8, %r8, %r9
	stw %r8, 224(%r31)
	lwz %r8, 228(%r31)
	lwz %r9, 996(%r5)
	xor %r8, %r8, %r9
	stw %r8, 228(%r31)
	lwz %r8, 232(%r31)
	lwz %r9, 1000(%r5)
	xor %r8, %r8, %r9
	stw %r8, 232(%r31)
	lwz %r8, 236(%r31)
	lwz %r9, 1004(%r5)
	xor %r8, %r8, %r9
	stw %r8, 236(%r31)
	lwz %r8, 240(%r31)
	lwz %r9, 1008(%r5)
	xor %r8, %r8, %r9
	stw %r8, 240(%r31)
	lwz %r8, 244(%r31)
	lwz %r9, 1012(%r5)
	xor %r8, %r8, %r9
	stw %r8, 244(%r31)
	lwz %r8, 248(%r31)
	lwz %r9, 1016(%r5)
	xor %r8, %r8, %r9
	stw %r8, 248(%r31)
	lwz %r8, 252(%r31)
	lwz %r9, 1020(%r5)
	xor %r8, %r8, %r9
	stw %r8, 252(%r31)
	addi %r31, %r31, 256
	addi %r30, %r30, -16
	rldicl %r8, %r30, 60, 4
	cmpldi %cr0, %r8, 0
	bne %cr0, 218b
	b 217f
216:
217:
	cmpldi %cr0, %r30, 0
	beq %cr0, 219f
221:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	or %r7, %r3, %r3
	or %r3, %r5, %r5
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r3, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 221b
	b 220f
219:
220:
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
	b 215f
214:
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
	beq %cr0, 222f
224:
	lwz %r8, 3248(%r5)
	stw %r8, 768(%r5)
	lwz %r8, 3252(%r5)
	stw %r8, 772(%r5)
	lwz %r8, 3256(%r5)
	stw %r8, 776(%r5)
	lwz %r8, 3260(%r5)
	stw %r8, 780(%r5)
	li %r9, 3260
	lwbrx %r8, %r5, %r9
	addi %r8, %r8, 1
	stwbrx %r8, %r5, %r9
	bl {vg_sm4_serial_encrypt}
	lwz %r8, 0(%r31)
	lwz %r9, 768(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 772(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 8(%r31)
	lwz %r9, 776(%r5)
	xor %r8, %r8, %r9
	stw %r8, 8(%r31)
	lwz %r8, 12(%r31)
	lwz %r9, 780(%r5)
	xor %r8, %r8, %r9
	stw %r8, 12(%r31)
	addi %r31, %r31, 16
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 224b
	b 223f
222:
223:
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
215:
	li %r0, 0
	std %r0, 272(%r31)
	std %r0, 280(%r31)
	addi %r3, %r31, 0
	addi %r4, %r31, 272
	or %r5, %r19, %r19
225:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 225b
	ld %r3, 272(%r31)
	ld %r4, 256(%r31)
	xor %r3, %r3, %r4
	ld %r4, 280(%r31)
	ld %r5, 264(%r31)
	xor %r4, %r4, %r5
	or %r3, %r3, %r4
	li %r4, 0
	subf %r4, %r3, %r4
	or %r3, %r3, %r4
	rldicl %r3, %r3, 1, 63
	li %r4, 1
	subf %r3, %r3, %r4
	b 27f
26:
	li %r3, 0
27:
	or %r12, %r31, %r31
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r18, 128(%r12)
	ld %r19, 136(%r12)
	ld %r20, 144(%r12)
	ld %r21, 152(%r12)
	ld %r22, 160(%r12)
	ld %r23, 168(%r12)
	ld %r24, 176(%r12)
	ld %r25, 184(%r12)
	ld %r26, 192(%r12)
	ld %r27, 200(%r12)
	ld %r28, 208(%r12)
	ld %r29, 216(%r12)
	ld %r30, 224(%r12)
	ld %r31, 232(%r12)
	addi %r1, %r1, 3296
	addi %r1, %r1, 320
	li %r0, 0
	stdu %r1, -3616(%r1)
	addi %r12, %r1, 32
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
	addi %r1, %r1, 3616
	rldicr %r3, %r3, 32, 31
	rldicl %r3, %r3, 32, 32
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
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v9, %v9, %v9
	vxor %v10, %v10, %v10
	vxor %v11, %v11, %v11
	vxor %v12, %v12, %v12
	vxor %v13, %v13, %v13
	vxor %v14, %v14, %v14
	vxor %v15, %v15, %v15
	vxor %v16, %v16, %v16
	vxor %v17, %v17, %v17
	vxor %v18, %v18, %v18
	vxor %v19, %v19, %v19
	blr
