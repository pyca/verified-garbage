// The functions of `src/pbkdf2_sha224.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha224_iterate:
	mflr %r0
	rldicr %r5, %r5, 32, 31
	rldicl %r5, %r5, 32, 32
	std %r26, 112(%r7)
	std %r27, 120(%r7)
	std %r28, 128(%r7)
	std %r29, 136(%r7)
	std %r30, 144(%r7)
	std %r31, 152(%r7)
	std %r0, 160(%r7)
	addi %r26, %r7, 168
	addi %r27, %r7, 0
	addi %r28, %r7, 200
	addi %r30, %r6, 0
	addi %r31, %r5, 0
	lwz %r8, 0(%r4)
	stw %r8, 0(%r28)
	lwz %r8, 4(%r4)
	stw %r8, 4(%r28)
	lwz %r8, 8(%r4)
	stw %r8, 8(%r28)
	lwz %r8, 12(%r4)
	stw %r8, 12(%r28)
	lwz %r8, 16(%r4)
	stw %r8, 16(%r28)
	lwz %r8, 20(%r4)
	stw %r8, 20(%r28)
	lwz %r8, 24(%r4)
	stw %r8, 24(%r28)
	li %r8, 128
	stw %r8, 28(%r28)
	li %r8, 0
	stw %r8, 32(%r28)
	stw %r8, 36(%r28)
	stw %r8, 40(%r28)
	stw %r8, 44(%r28)
	stw %r8, 48(%r28)
	stw %r8, 52(%r28)
	li %r29, 92
	add %r8, %r29, %r29
	add %r8, %r8, %r8
	add %r8, %r8, %r8
	li %r11, 88
	stdbrx %r8, %r26, %r11
	addi %r29, %r3, 0
	cmpldi %cr0, %r31, 0
	beq %cr0, 20f
22:
	lwz %r8, 0(%r29)
	stw %r8, 0(%r26)
	lwz %r8, 4(%r29)
	stw %r8, 4(%r26)
	lwz %r8, 8(%r29)
	stw %r8, 8(%r26)
	lwz %r8, 12(%r29)
	stw %r8, 12(%r26)
	lwz %r8, 16(%r29)
	stw %r8, 16(%r26)
	lwz %r8, 20(%r29)
	stw %r8, 20(%r26)
	lwz %r8, 24(%r29)
	stw %r8, 24(%r26)
	lwz %r8, 28(%r29)
	stw %r8, 28(%r26)
	addi %r4, %r28, 0
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 96(%r29)
	stw %r8, 0(%r26)
	lwz %r8, 100(%r29)
	stw %r8, 4(%r26)
	lwz %r8, 104(%r29)
	stw %r8, 8(%r26)
	lwz %r8, 108(%r29)
	stw %r8, 12(%r26)
	lwz %r8, 112(%r29)
	stw %r8, 16(%r26)
	lwz %r8, 116(%r29)
	stw %r8, 20(%r26)
	lwz %r8, 120(%r29)
	stw %r8, 24(%r26)
	lwz %r8, 124(%r29)
	stw %r8, 28(%r26)
	addi %r4, %r28, 0
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 0(%r28)
	lwz %r9, 0(%r30)
	xor %r8, %r8, %r9
	stw %r8, 0(%r30)
	lwz %r8, 4(%r28)
	lwz %r9, 4(%r30)
	xor %r8, %r8, %r9
	stw %r8, 4(%r30)
	lwz %r8, 8(%r28)
	lwz %r9, 8(%r30)
	xor %r8, %r8, %r9
	stw %r8, 8(%r30)
	lwz %r8, 12(%r28)
	lwz %r9, 12(%r30)
	xor %r8, %r8, %r9
	stw %r8, 12(%r30)
	lwz %r8, 16(%r28)
	lwz %r9, 16(%r30)
	xor %r8, %r8, %r9
	stw %r8, 16(%r30)
	lwz %r8, 20(%r28)
	lwz %r9, 20(%r30)
	xor %r8, %r8, %r9
	stw %r8, 20(%r30)
	lwz %r8, 24(%r28)
	lwz %r9, 24(%r30)
	xor %r8, %r8, %r9
	stw %r8, 24(%r30)
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r0, 160(%r27)
	ld %r26, 112(%r27)
	ld %r28, 128(%r27)
	ld %r29, 136(%r27)
	ld %r30, 144(%r27)
	ld %r31, 152(%r27)
	ld %r27, 120(%r27)
	mtlr %r0
	blr

vg_pbkdf2_hmac_sha224:
	stdu %r1, -1632(%r1)
	addi %r10, %r1, 32
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r20, 0(%r10)
	std %r21, 8(%r10)
	std %r22, 16(%r10)
	std %r23, 24(%r10)
	std %r24, 32(%r10)
	std %r25, 40(%r10)
	addi %r21, %r10, 0
	addi %r20, %r6, 0
	addi %r22, %r7, 0
	addi %r23, %r8, 0
	addi %r24, %r9, 0
	addi %r25, %r5, 0
	addi %r5, %r3, 0
	addi %r6, %r4, 0
	addi %r3, %r21, 880
	addi %r4, %r21, 976
	bl {vg_hmac_sha224_init}
	li %r12, 1
	li %r11, 1224
	stwbrx %r12, %r21, %r11
	cmpldi %cr0, %r24, 0
	beq %cr0, 20f
22:
	lwz %r8, 880(%r21)
	stw %r8, 1072(%r21)
	lwz %r8, 884(%r21)
	stw %r8, 1076(%r21)
	lwz %r8, 888(%r21)
	stw %r8, 1080(%r21)
	lwz %r8, 892(%r21)
	stw %r8, 1084(%r21)
	lwz %r8, 896(%r21)
	stw %r8, 1088(%r21)
	lwz %r8, 900(%r21)
	stw %r8, 1092(%r21)
	lwz %r8, 904(%r21)
	stw %r8, 1096(%r21)
	lwz %r8, 908(%r21)
	stw %r8, 1100(%r21)
	lwz %r8, 912(%r21)
	stw %r8, 1104(%r21)
	lwz %r8, 916(%r21)
	stw %r8, 1108(%r21)
	lwz %r8, 920(%r21)
	stw %r8, 1112(%r21)
	lwz %r8, 924(%r21)
	stw %r8, 1116(%r21)
	lwz %r8, 928(%r21)
	stw %r8, 1120(%r21)
	lwz %r8, 932(%r21)
	stw %r8, 1124(%r21)
	lwz %r8, 936(%r21)
	stw %r8, 1128(%r21)
	lwz %r8, 940(%r21)
	stw %r8, 1132(%r21)
	lwz %r8, 944(%r21)
	stw %r8, 1136(%r21)
	lwz %r8, 948(%r21)
	stw %r8, 1140(%r21)
	lwz %r8, 952(%r21)
	stw %r8, 1144(%r21)
	lwz %r8, 956(%r21)
	stw %r8, 1148(%r21)
	lwz %r8, 960(%r21)
	stw %r8, 1152(%r21)
	lwz %r8, 964(%r21)
	stw %r8, 1156(%r21)
	lwz %r8, 968(%r21)
	stw %r8, 1160(%r21)
	lwz %r8, 972(%r21)
	stw %r8, 1164(%r21)
	addi %r3, %r21, 1072
	li %r4, 64
	addi %r5, %r25, 0
	addi %r6, %r20, 0
	addi %r7, %r21, 48
	bl {vg_sha256_update_scratch}
	addi %r3, %r21, 1072
	addi %r4, %r20, 64
	addi %r5, %r21, 1224
	li %r6, 4
	addi %r7, %r21, 48
	bl {vg_sha256_update_scratch}
	addi %r3, %r21, 1072
	addi %r4, %r21, 976
	addi %r5, %r20, 68
	addi %r6, %r21, 1168
	addi %r7, %r21, 48
	bl {vg_hmac_sha224_finalize_scratch}
	lwz %r8, 1168(%r21)
	stw %r8, 1196(%r21)
	lwz %r8, 1172(%r21)
	stw %r8, 1200(%r21)
	lwz %r8, 1176(%r21)
	stw %r8, 1204(%r21)
	lwz %r8, 1180(%r21)
	stw %r8, 1208(%r21)
	lwz %r8, 1184(%r21)
	stw %r8, 1212(%r21)
	lwz %r8, 1188(%r21)
	stw %r8, 1216(%r21)
	lwz %r8, 1192(%r21)
	stw %r8, 1220(%r21)
	addi %r3, %r21, 880
	addi %r4, %r21, 1168
	addi %r5, %r22, -1
	addi %r6, %r21, 1196
	addi %r7, %r21, 48
	bl {vg_pbkdf2_hmac_sha224_iterate}
	addi %r12, %r24, -28
	rldicl %r12, %r12, 1, 63
	addi %r9, %r24, 0
	cmpldi %cr0, %r12, 0
	bne %cr0, 23f
	li %r9, 28
	b 24f
23:
24:
	li %r8, 0
25:
	add %r11, %r21, %r8
	lbz %r12, 1196(%r11)
	add %r11, %r23, %r8
	stb %r12, 0(%r11)
	addi %r8, %r8, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 25b
	add %r23, %r23, %r8
	subf %r24, %r8, %r24
	li %r11, 1224
	lwbrx %r12, %r21, %r11
	addi %r12, %r12, 1
	stwbrx %r12, %r21, %r11
	cmpldi %cr0, %r24, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r20, 0(%r21)
	ld %r22, 16(%r21)
	ld %r23, 24(%r21)
	ld %r24, 32(%r21)
	ld %r25, 40(%r21)
	ld %r21, 8(%r21)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	addi %r1, %r1, 1632
	blr
