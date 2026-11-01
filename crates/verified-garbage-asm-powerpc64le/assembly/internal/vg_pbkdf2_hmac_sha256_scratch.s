// The functions of `src/internal/vg_pbkdf2_hmac_sha256_scratch.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha256_scratch:
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
	bl {vg_hmac_sha256_init}
	li %r12, 1
	li %r11, 1232
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
	addi %r5, %r21, 1232
	li %r6, 4
	addi %r7, %r21, 48
	bl {vg_sha256_update_scratch}
	addi %r3, %r21, 1072
	addi %r4, %r21, 976
	addi %r5, %r20, 68
	addi %r6, %r21, 1168
	addi %r7, %r21, 48
	bl {vg_hmac_sha256_finalize_scratch}
	lwz %r8, 1168(%r21)
	stw %r8, 1200(%r21)
	lwz %r8, 1172(%r21)
	stw %r8, 1204(%r21)
	lwz %r8, 1176(%r21)
	stw %r8, 1208(%r21)
	lwz %r8, 1180(%r21)
	stw %r8, 1212(%r21)
	lwz %r8, 1184(%r21)
	stw %r8, 1216(%r21)
	lwz %r8, 1188(%r21)
	stw %r8, 1220(%r21)
	lwz %r8, 1192(%r21)
	stw %r8, 1224(%r21)
	lwz %r8, 1196(%r21)
	stw %r8, 1228(%r21)
	addi %r3, %r21, 880
	addi %r4, %r21, 1168
	addi %r5, %r22, -1
	addi %r6, %r21, 1200
	addi %r7, %r21, 48
	bl {vg_pbkdf2_hmac_sha256_iterate}
	addi %r12, %r24, -32
	rldicl %r12, %r12, 1, 63
	addi %r9, %r24, 0
	cmpldi %cr0, %r12, 0
	bne %cr0, 23f
	li %r9, 32
	b 24f
23:
24:
	li %r8, 0
25:
	add %r11, %r21, %r8
	lbz %r12, 1200(%r11)
	add %r11, %r23, %r8
	stb %r12, 0(%r11)
	addi %r8, %r8, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 25b
	add %r23, %r23, %r8
	subf %r24, %r8, %r24
	li %r11, 1232
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
	blr
