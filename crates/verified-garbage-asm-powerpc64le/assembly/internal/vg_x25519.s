// The functions of `src/internal/vg_x25519.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x25519:
	lwz %r7, 0(%r5)
	stw %r7, 0(%r6)
	stw %r7, 96(%r6)
	lwz %r7, 4(%r5)
	stw %r7, 4(%r6)
	stw %r7, 100(%r6)
	lwz %r7, 8(%r5)
	stw %r7, 8(%r6)
	stw %r7, 104(%r6)
	lwz %r7, 12(%r5)
	stw %r7, 12(%r6)
	stw %r7, 108(%r6)
	lwz %r7, 16(%r5)
	stw %r7, 16(%r6)
	stw %r7, 112(%r6)
	lwz %r7, 20(%r5)
	stw %r7, 20(%r6)
	stw %r7, 116(%r6)
	lwz %r7, 24(%r5)
	stw %r7, 24(%r6)
	stw %r7, 120(%r6)
	lwz %r7, 28(%r5)
	rldicr %r7, %r7, 33, 30
	rldicl %r7, %r7, 31, 33
	stw %r7, 28(%r6)
	stw %r7, 124(%r6)
	li %r7, 1
	li %r8, 0
	stw %r7, 32(%r6)
	stw %r8, 64(%r6)
	stw %r7, 128(%r6)
	stw %r8, 36(%r6)
	stw %r8, 40(%r6)
	stw %r8, 44(%r6)
	stw %r8, 48(%r6)
	stw %r8, 52(%r6)
	stw %r8, 56(%r6)
	stw %r8, 60(%r6)
	stw %r8, 68(%r6)
	stw %r8, 72(%r6)
	stw %r8, 76(%r6)
	stw %r8, 80(%r6)
	stw %r8, 84(%r6)
	stw %r8, 88(%r6)
	stw %r8, 92(%r6)
	stw %r8, 132(%r6)
	stw %r8, 136(%r6)
	stw %r8, 140(%r6)
	stw %r8, 144(%r6)
	stw %r8, 148(%r6)
	stw %r8, 152(%r6)
	stw %r8, 156(%r6)
	addi %r9, %r6, 0
	li %r11, 32
20:
	lbz %r7, 0(%r4)
	rldicr %r8, %r7, 63, 0
	rldicl %r8, %r8, 1, 63
	stb %r8, 608(%r9)
	rldicr %r8, %r7, 62, 1
	rldicl %r8, %r8, 1, 63
	stb %r8, 609(%r9)
	rldicr %r8, %r7, 61, 2
	rldicl %r8, %r8, 1, 63
	stb %r8, 610(%r9)
	rldicr %r8, %r7, 60, 3
	rldicl %r8, %r8, 1, 63
	stb %r8, 611(%r9)
	rldicr %r8, %r7, 59, 4
	rldicl %r8, %r8, 1, 63
	stb %r8, 612(%r9)
	rldicr %r8, %r7, 58, 5
	rldicl %r8, %r8, 1, 63
	stb %r8, 613(%r9)
	rldicr %r8, %r7, 57, 6
	rldicl %r8, %r8, 1, 63
	stb %r8, 614(%r9)
	rldicr %r8, %r7, 56, 7
	rldicl %r8, %r8, 1, 63
	stb %r8, 615(%r9)
	addi %r4, %r4, 1
	addi %r9, %r9, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 20b
	li %r7, 0
	stb %r7, 608(%r6)
	stb %r7, 609(%r6)
	stb %r7, 610(%r6)
	li %r7, 1
	stb %r7, 862(%r6)
	std %r14, 896(%r6)
	std %r15, 904(%r6)
	std %r16, 912(%r6)
	std %r17, 920(%r6)
	std %r18, 928(%r6)
	std %r19, 936(%r6)
	std %r20, 944(%r6)
	std %r21, 952(%r6)
	std %r22, 960(%r6)
	std %r23, 968(%r6)
	std %r24, 976(%r6)
	std %r25, 984(%r6)
	std %r26, 992(%r6)
	std %r27, 1000(%r6)
	std %r28, 1008(%r6)
	std %r29, 1016(%r6)
	std %r30, 1024(%r6)
	std %r31, 1032(%r6)
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	ld %r7, 0(%r6)
	ld %r8, 8(%r6)
	ld %r9, 16(%r6)
	ld %r10, 24(%r6)
	and %r14, %r7, %r4
	rldicl %r15, %r7, 13, 51
	rldicr %r5, %r8, 13, 50
	add %r15, %r15, %r5
	and %r15, %r15, %r4
	rldicl %r16, %r8, 26, 38
	rldicr %r5, %r9, 26, 37
	add %r16, %r16, %r5
	and %r16, %r16, %r4
	rldicl %r17, %r9, 39, 25
	rldicr %r5, %r10, 39, 24
	add %r17, %r17, %r5
	and %r17, %r17, %r4
	rldicl %r18, %r10, 52, 12
	std %r14, 1088(%r6)
	std %r15, 1096(%r6)
	std %r16, 1104(%r6)
	std %r17, 1112(%r6)
	std %r18, 1120(%r6)
	std %r14, 1208(%r6)
	std %r15, 1216(%r6)
	std %r16, 1224(%r6)
	std %r17, 1232(%r6)
	std %r18, 1240(%r6)
	li %r7, 1
	li %r8, 0
	std %r7, 1128(%r6)
	std %r8, 1136(%r6)
	std %r8, 1144(%r6)
	std %r8, 1152(%r6)
	std %r8, 1160(%r6)
	std %r8, 1168(%r6)
	std %r8, 1176(%r6)
	std %r8, 1184(%r6)
	std %r8, 1192(%r6)
	std %r8, 1200(%r6)
	std %r7, 1248(%r6)
	std %r8, 1256(%r6)
	std %r8, 1264(%r6)
	std %r8, 1272(%r6)
	std %r8, 1280(%r6)
	li %r12, 255
	li %r0, 0
21:
	addi %r12, %r12, -1
	add %r4, %r6, %r12
	lbz %r4, 608(%r4)
	xor %r0, %r0, %r4
	li %r4, 0
	subf %r4, %r0, %r4
	ld %r7, 1128(%r6)
	ld %r8, 1168(%r6)
	add %r7, %r7, %r8
	ld %r10, 1208(%r6)
	ld %r8, 1248(%r6)
	add %r10, %r10, %r8
	xor %r10, %r10, %r7
	and %r10, %r10, %r4
	xor %r14, %r7, %r10
	ld %r7, 1136(%r6)
	ld %r8, 1176(%r6)
	add %r7, %r7, %r8
	ld %r10, 1216(%r6)
	ld %r8, 1256(%r6)
	add %r10, %r10, %r8
	xor %r10, %r10, %r7
	and %r10, %r10, %r4
	xor %r15, %r7, %r10
	ld %r7, 1144(%r6)
	ld %r8, 1184(%r6)
	add %r7, %r7, %r8
	ld %r10, 1224(%r6)
	ld %r8, 1264(%r6)
	add %r10, %r10, %r8
	xor %r10, %r10, %r7
	and %r10, %r10, %r4
	xor %r16, %r7, %r10
	ld %r7, 1152(%r6)
	ld %r8, 1192(%r6)
	add %r7, %r7, %r8
	ld %r10, 1232(%r6)
	ld %r8, 1272(%r6)
	add %r10, %r10, %r8
	xor %r10, %r10, %r7
	and %r10, %r10, %r4
	xor %r17, %r7, %r10
	ld %r7, 1160(%r6)
	ld %r8, 1200(%r6)
	add %r7, %r7, %r8
	ld %r10, 1240(%r6)
	ld %r8, 1280(%r6)
	add %r10, %r10, %r8
	xor %r10, %r10, %r7
	and %r10, %r10, %r4
	xor %r18, %r7, %r10
	rldicr %r19, %r14, 4, 59
	rldicr %r14, %r14, 9, 54
	rldicr %r20, %r15, 5, 58
	rldicr %r21, %r16, 5, 58
	rldicr %r22, %r17, 5, 58
	rldicr %r23, %r18, 5, 58
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	rldicr %r19, %r15, 4, 59
	rldicr %r15, %r15, 9, 54
	li %r24, 19
	mulld %r23, %r23, %r24
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r19
	add %r30, %r30, %r4
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r15, %r23
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r23
	add %r28, %r28, %r4
	rldicr %r19, %r16, 4, 59
	rldicr %r16, %r16, 9, 54
	mulld %r22, %r22, %r24
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r19
	add %r5, %r5, %r4
	mulld %r4, %r16, %r22
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r22
	add %r28, %r28, %r4
	mulld %r4, %r16, %r23
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r23
	add %r29, %r29, %r4
	rldicr %r17, %r17, 8, 55
	mulld %r4, %r17, %r22
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r22
	add %r29, %r29, %r4
	rldicr %r17, %r17, 1, 62
	mulld %r4, %r17, %r23
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r23
	add %r30, %r30, %r4
	rldicr %r18, %r18, 8, 55
	mulld %r4, %r18, %r23
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r23
	add %r31, %r31, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1288(%r6)
	std %r8, 1296(%r6)
	std %r9, 1304(%r6)
	std %r10, 1312(%r6)
	std %r11, 1320(%r6)
	li %r4, 0
	subf %r4, %r0, %r4
	li %r5, 1
	rldicr %r5, %r5, 52, 11
	addi %r9, %r5, -38
	addi %r5, %r5, -2
	ld %r7, 1128(%r6)
	ld %r8, 1168(%r6)
	add %r7, %r7, %r9
	subf %r7, %r8, %r7
	ld %r10, 1208(%r6)
	ld %r8, 1248(%r6)
	add %r10, %r10, %r9
	subf %r10, %r8, %r10
	xor %r10, %r10, %r7
	and %r10, %r10, %r4
	xor %r14, %r7, %r10
	ld %r7, 1136(%r6)
	ld %r8, 1176(%r6)
	add %r7, %r7, %r5
	subf %r7, %r8, %r7
	ld %r10, 1216(%r6)
	ld %r8, 1256(%r6)
	add %r10, %r10, %r5
	subf %r10, %r8, %r10
	xor %r10, %r10, %r7
	and %r10, %r10, %r4
	xor %r15, %r7, %r10
	ld %r7, 1144(%r6)
	ld %r8, 1184(%r6)
	add %r7, %r7, %r5
	subf %r7, %r8, %r7
	ld %r10, 1224(%r6)
	ld %r8, 1264(%r6)
	add %r10, %r10, %r5
	subf %r10, %r8, %r10
	xor %r10, %r10, %r7
	and %r10, %r10, %r4
	xor %r16, %r7, %r10
	ld %r7, 1152(%r6)
	ld %r8, 1192(%r6)
	add %r7, %r7, %r5
	subf %r7, %r8, %r7
	ld %r10, 1232(%r6)
	ld %r8, 1272(%r6)
	add %r10, %r10, %r5
	subf %r10, %r8, %r10
	xor %r10, %r10, %r7
	and %r10, %r10, %r4
	xor %r17, %r7, %r10
	ld %r7, 1160(%r6)
	ld %r8, 1200(%r6)
	add %r7, %r7, %r5
	subf %r7, %r8, %r7
	ld %r10, 1240(%r6)
	ld %r8, 1280(%r6)
	add %r10, %r10, %r5
	subf %r10, %r8, %r10
	xor %r10, %r10, %r7
	and %r10, %r10, %r4
	xor %r18, %r7, %r10
	rldicr %r19, %r14, 4, 59
	rldicr %r14, %r14, 9, 54
	rldicr %r20, %r15, 5, 58
	rldicr %r21, %r16, 5, 58
	rldicr %r22, %r17, 5, 58
	rldicr %r23, %r18, 5, 58
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	rldicr %r19, %r15, 4, 59
	rldicr %r15, %r15, 9, 54
	li %r24, 19
	mulld %r23, %r23, %r24
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r19
	add %r30, %r30, %r4
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r15, %r23
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r23
	add %r28, %r28, %r4
	rldicr %r19, %r16, 4, 59
	rldicr %r16, %r16, 9, 54
	mulld %r22, %r22, %r24
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r19
	add %r5, %r5, %r4
	mulld %r4, %r16, %r22
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r22
	add %r28, %r28, %r4
	mulld %r4, %r16, %r23
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r23
	add %r29, %r29, %r4
	rldicr %r17, %r17, 8, 55
	mulld %r4, %r17, %r22
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r22
	add %r29, %r29, %r4
	rldicr %r17, %r17, 1, 62
	mulld %r4, %r17, %r23
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r23
	add %r30, %r30, %r4
	rldicr %r18, %r18, 8, 55
	mulld %r4, %r18, %r23
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r23
	add %r31, %r31, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1328(%r6)
	std %r8, 1336(%r6)
	std %r9, 1344(%r6)
	std %r10, 1352(%r6)
	std %r11, 1360(%r6)
	add %r4, %r6, %r12
	lbz %r0, 608(%r4)
	li %r5, 1
	rldicr %r5, %r5, 52, 11
	addi %r9, %r5, -38
	addi %r5, %r5, -2
	ld %r14, 1208(%r6)
	ld %r8, 1248(%r6)
	add %r14, %r14, %r9
	subf %r14, %r8, %r14
	ld %r15, 1216(%r6)
	ld %r8, 1256(%r6)
	add %r15, %r15, %r5
	subf %r15, %r8, %r15
	ld %r16, 1224(%r6)
	ld %r8, 1264(%r6)
	add %r16, %r16, %r5
	subf %r16, %r8, %r16
	ld %r17, 1232(%r6)
	ld %r8, 1272(%r6)
	add %r17, %r17, %r5
	subf %r17, %r8, %r17
	ld %r18, 1240(%r6)
	ld %r8, 1280(%r6)
	add %r18, %r18, %r5
	subf %r18, %r8, %r18
	ld %r19, 1128(%r6)
	ld %r8, 1168(%r6)
	add %r19, %r19, %r8
	ld %r20, 1136(%r6)
	ld %r8, 1176(%r6)
	add %r20, %r20, %r8
	ld %r21, 1144(%r6)
	ld %r8, 1184(%r6)
	add %r21, %r21, %r8
	ld %r22, 1152(%r6)
	ld %r8, 1192(%r6)
	add %r22, %r22, %r8
	ld %r23, 1160(%r6)
	ld %r8, 1200(%r6)
	add %r23, %r23, %r8
	rldicr %r14, %r14, 8, 55
	rldicr %r15, %r15, 8, 55
	rldicr %r16, %r16, 8, 55
	rldicr %r17, %r17, 8, 55
	rldicr %r18, %r18, 8, 55
	rldicr %r19, %r19, 5, 58
	rldicr %r20, %r20, 5, 58
	rldicr %r21, %r21, 5, 58
	rldicr %r22, %r22, 5, 58
	rldicr %r23, %r23, 5, 58
	li %r5, 19
	mulld %r24, %r20, %r5
	mulld %r25, %r21, %r5
	mulld %r26, %r22, %r5
	mulld %r27, %r23, %r5
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r15, %r27
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r27
	add %r28, %r28, %r4
	mulld %r4, %r16, %r26
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r26
	add %r28, %r28, %r4
	mulld %r4, %r17, %r25
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r17, %r25
	add %r28, %r28, %r4
	mulld %r4, %r18, %r24
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r18, %r24
	add %r28, %r28, %r4
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r15, %r19
	add %r29, %r29, %r4
	mulld %r4, %r16, %r27
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r27
	add %r29, %r29, %r4
	mulld %r4, %r17, %r26
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r26
	add %r29, %r29, %r4
	mulld %r4, %r18, %r25
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r18, %r25
	add %r29, %r29, %r4
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r15, %r20
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r20
	add %r30, %r30, %r4
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r16, %r19
	add %r30, %r30, %r4
	mulld %r4, %r17, %r27
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r27
	add %r30, %r30, %r4
	mulld %r4, %r18, %r26
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r18, %r26
	add %r30, %r30, %r4
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r16, %r20
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r16, %r20
	add %r31, %r31, %r4
	mulld %r4, %r17, %r19
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r17, %r19
	add %r31, %r31, %r4
	mulld %r4, %r18, %r27
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r27
	add %r31, %r31, %r4
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r16, %r21
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r21
	add %r5, %r5, %r4
	mulld %r4, %r17, %r20
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r17, %r20
	add %r5, %r5, %r4
	mulld %r4, %r18, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r18, %r19
	add %r5, %r5, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1368(%r6)
	std %r8, 1376(%r6)
	std %r9, 1384(%r6)
	std %r10, 1392(%r6)
	std %r11, 1400(%r6)
	li %r5, 1
	rldicr %r5, %r5, 52, 11
	addi %r9, %r5, -38
	addi %r5, %r5, -2
	ld %r14, 1128(%r6)
	ld %r8, 1168(%r6)
	add %r14, %r14, %r9
	subf %r14, %r8, %r14
	ld %r15, 1136(%r6)
	ld %r8, 1176(%r6)
	add %r15, %r15, %r5
	subf %r15, %r8, %r15
	ld %r16, 1144(%r6)
	ld %r8, 1184(%r6)
	add %r16, %r16, %r5
	subf %r16, %r8, %r16
	ld %r17, 1152(%r6)
	ld %r8, 1192(%r6)
	add %r17, %r17, %r5
	subf %r17, %r8, %r17
	ld %r18, 1160(%r6)
	ld %r8, 1200(%r6)
	add %r18, %r18, %r5
	subf %r18, %r8, %r18
	ld %r19, 1208(%r6)
	ld %r8, 1248(%r6)
	add %r19, %r19, %r8
	ld %r20, 1216(%r6)
	ld %r8, 1256(%r6)
	add %r20, %r20, %r8
	ld %r21, 1224(%r6)
	ld %r8, 1264(%r6)
	add %r21, %r21, %r8
	ld %r22, 1232(%r6)
	ld %r8, 1272(%r6)
	add %r22, %r22, %r8
	ld %r23, 1240(%r6)
	ld %r8, 1280(%r6)
	add %r23, %r23, %r8
	rldicr %r14, %r14, 8, 55
	rldicr %r15, %r15, 8, 55
	rldicr %r16, %r16, 8, 55
	rldicr %r17, %r17, 8, 55
	rldicr %r18, %r18, 8, 55
	rldicr %r19, %r19, 5, 58
	rldicr %r20, %r20, 5, 58
	rldicr %r21, %r21, 5, 58
	rldicr %r22, %r22, 5, 58
	rldicr %r23, %r23, 5, 58
	li %r5, 19
	mulld %r24, %r20, %r5
	mulld %r25, %r21, %r5
	mulld %r26, %r22, %r5
	mulld %r27, %r23, %r5
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r15, %r27
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r27
	add %r28, %r28, %r4
	mulld %r4, %r16, %r26
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r26
	add %r28, %r28, %r4
	mulld %r4, %r17, %r25
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r17, %r25
	add %r28, %r28, %r4
	mulld %r4, %r18, %r24
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r18, %r24
	add %r28, %r28, %r4
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r15, %r19
	add %r29, %r29, %r4
	mulld %r4, %r16, %r27
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r27
	add %r29, %r29, %r4
	mulld %r4, %r17, %r26
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r26
	add %r29, %r29, %r4
	mulld %r4, %r18, %r25
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r18, %r25
	add %r29, %r29, %r4
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r15, %r20
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r20
	add %r30, %r30, %r4
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r16, %r19
	add %r30, %r30, %r4
	mulld %r4, %r17, %r27
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r27
	add %r30, %r30, %r4
	mulld %r4, %r18, %r26
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r18, %r26
	add %r30, %r30, %r4
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r16, %r20
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r16, %r20
	add %r31, %r31, %r4
	mulld %r4, %r17, %r19
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r17, %r19
	add %r31, %r31, %r4
	mulld %r4, %r18, %r27
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r27
	add %r31, %r31, %r4
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r16, %r21
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r21
	add %r5, %r5, %r4
	mulld %r4, %r17, %r20
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r17, %r20
	add %r5, %r5, %r4
	mulld %r4, %r18, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r18, %r19
	add %r5, %r5, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1408(%r6)
	std %r8, 1416(%r6)
	std %r9, 1424(%r6)
	std %r10, 1432(%r6)
	std %r11, 1440(%r6)
	li %r5, 1
	rldicr %r5, %r5, 52, 11
	addi %r9, %r5, -38
	addi %r5, %r5, -2
	ld %r19, 1288(%r6)
	ld %r8, 1328(%r6)
	add %r14, %r19, %r9
	subf %r14, %r8, %r14
	rldicr %r14, %r14, 11, 52
	ld %r20, 1296(%r6)
	ld %r8, 1336(%r6)
	add %r15, %r20, %r5
	subf %r15, %r8, %r15
	rldicr %r15, %r15, 11, 52
	ld %r21, 1304(%r6)
	ld %r8, 1344(%r6)
	add %r16, %r21, %r5
	subf %r16, %r8, %r16
	rldicr %r16, %r16, 11, 52
	ld %r22, 1312(%r6)
	ld %r8, 1352(%r6)
	add %r17, %r22, %r5
	subf %r17, %r8, %r17
	rldicr %r17, %r17, 11, 52
	ld %r23, 1320(%r6)
	ld %r8, 1360(%r6)
	add %r18, %r23, %r5
	subf %r18, %r8, %r18
	rldicr %r18, %r18, 11, 52
	lis %r24, 1
	ori %r24, %r24, 56129
	rldicr %r24, %r24, 2, 61
	mulld %r4, %r14, %r24
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r24
	mulld %r4, %r15, %r24
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r15, %r24
	mulld %r4, %r16, %r24
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r16, %r24
	mulld %r4, %r17, %r24
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r17, %r24
	mulld %r4, %r18, %r24
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r18, %r24
	add %r7, %r7, %r19
	add %r8, %r8, %r20
	add %r9, %r9, %r21
	add %r10, %r10, %r22
	add %r11, %r11, %r23
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1488(%r6)
	std %r8, 1496(%r6)
	std %r9, 1504(%r6)
	std %r10, 1512(%r6)
	std %r11, 1520(%r6)
	li %r5, 1
	rldicr %r5, %r5, 52, 11
	addi %r9, %r5, -38
	addi %r5, %r5, -2
	ld %r14, 1368(%r6)
	ld %r8, 1408(%r6)
	add %r14, %r14, %r9
	subf %r14, %r8, %r14
	ld %r15, 1376(%r6)
	ld %r8, 1416(%r6)
	add %r15, %r15, %r5
	subf %r15, %r8, %r15
	ld %r16, 1384(%r6)
	ld %r8, 1424(%r6)
	add %r16, %r16, %r5
	subf %r16, %r8, %r16
	ld %r17, 1392(%r6)
	ld %r8, 1432(%r6)
	add %r17, %r17, %r5
	subf %r17, %r8, %r17
	ld %r18, 1400(%r6)
	ld %r8, 1440(%r6)
	add %r18, %r18, %r5
	subf %r18, %r8, %r18
	rldicr %r19, %r14, 4, 59
	rldicr %r14, %r14, 9, 54
	rldicr %r20, %r15, 5, 58
	rldicr %r21, %r16, 5, 58
	rldicr %r22, %r17, 5, 58
	rldicr %r23, %r18, 5, 58
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	rldicr %r19, %r15, 4, 59
	rldicr %r15, %r15, 9, 54
	li %r24, 19
	mulld %r23, %r23, %r24
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r19
	add %r30, %r30, %r4
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r15, %r23
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r23
	add %r28, %r28, %r4
	rldicr %r19, %r16, 4, 59
	rldicr %r16, %r16, 9, 54
	mulld %r22, %r22, %r24
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r19
	add %r5, %r5, %r4
	mulld %r4, %r16, %r22
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r22
	add %r28, %r28, %r4
	mulld %r4, %r16, %r23
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r23
	add %r29, %r29, %r4
	rldicr %r17, %r17, 8, 55
	mulld %r4, %r17, %r22
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r22
	add %r29, %r29, %r4
	rldicr %r17, %r17, 1, 62
	mulld %r4, %r17, %r23
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r23
	add %r30, %r30, %r4
	rldicr %r18, %r18, 8, 55
	mulld %r4, %r18, %r23
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r23
	add %r31, %r31, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1448(%r6)
	std %r8, 1456(%r6)
	std %r9, 1464(%r6)
	std %r10, 1472(%r6)
	std %r11, 1480(%r6)
	ld %r14, 1368(%r6)
	ld %r8, 1408(%r6)
	add %r14, %r14, %r8
	ld %r15, 1376(%r6)
	ld %r8, 1416(%r6)
	add %r15, %r15, %r8
	ld %r16, 1384(%r6)
	ld %r8, 1424(%r6)
	add %r16, %r16, %r8
	ld %r17, 1392(%r6)
	ld %r8, 1432(%r6)
	add %r17, %r17, %r8
	ld %r18, 1400(%r6)
	ld %r8, 1440(%r6)
	add %r18, %r18, %r8
	rldicr %r19, %r14, 4, 59
	rldicr %r14, %r14, 9, 54
	rldicr %r20, %r15, 5, 58
	rldicr %r21, %r16, 5, 58
	rldicr %r22, %r17, 5, 58
	rldicr %r23, %r18, 5, 58
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	rldicr %r19, %r15, 4, 59
	rldicr %r15, %r15, 9, 54
	li %r24, 19
	mulld %r23, %r23, %r24
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r19
	add %r30, %r30, %r4
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r15, %r23
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r23
	add %r28, %r28, %r4
	rldicr %r19, %r16, 4, 59
	rldicr %r16, %r16, 9, 54
	mulld %r22, %r22, %r24
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r19
	add %r5, %r5, %r4
	mulld %r4, %r16, %r22
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r22
	add %r28, %r28, %r4
	mulld %r4, %r16, %r23
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r23
	add %r29, %r29, %r4
	rldicr %r17, %r17, 8, 55
	mulld %r4, %r17, %r22
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r22
	add %r29, %r29, %r4
	rldicr %r17, %r17, 1, 62
	mulld %r4, %r17, %r23
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r23
	add %r30, %r30, %r4
	rldicr %r18, %r18, 8, 55
	mulld %r4, %r18, %r23
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r23
	add %r31, %r31, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1208(%r6)
	std %r8, 1216(%r6)
	std %r9, 1224(%r6)
	std %r10, 1232(%r6)
	std %r11, 1240(%r6)
	li %r5, 1
	rldicr %r5, %r5, 52, 11
	addi %r9, %r5, -38
	addi %r5, %r5, -2
	ld %r14, 1288(%r6)
	ld %r8, 1328(%r6)
	add %r14, %r14, %r9
	subf %r14, %r8, %r14
	ld %r15, 1296(%r6)
	ld %r8, 1336(%r6)
	add %r15, %r15, %r5
	subf %r15, %r8, %r15
	ld %r16, 1304(%r6)
	ld %r8, 1344(%r6)
	add %r16, %r16, %r5
	subf %r16, %r8, %r16
	ld %r17, 1312(%r6)
	ld %r8, 1352(%r6)
	add %r17, %r17, %r5
	subf %r17, %r8, %r17
	ld %r18, 1320(%r6)
	ld %r8, 1360(%r6)
	add %r18, %r18, %r5
	subf %r18, %r8, %r18
	ld %r19, 1488(%r6)
	ld %r20, 1496(%r6)
	ld %r21, 1504(%r6)
	ld %r22, 1512(%r6)
	ld %r23, 1520(%r6)
	rldicr %r14, %r14, 8, 55
	rldicr %r15, %r15, 8, 55
	rldicr %r16, %r16, 8, 55
	rldicr %r17, %r17, 8, 55
	rldicr %r18, %r18, 8, 55
	rldicr %r19, %r19, 5, 58
	rldicr %r20, %r20, 5, 58
	rldicr %r21, %r21, 5, 58
	rldicr %r22, %r22, 5, 58
	rldicr %r23, %r23, 5, 58
	li %r5, 19
	mulld %r24, %r20, %r5
	mulld %r25, %r21, %r5
	mulld %r26, %r22, %r5
	mulld %r27, %r23, %r5
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r15, %r27
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r27
	add %r28, %r28, %r4
	mulld %r4, %r16, %r26
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r26
	add %r28, %r28, %r4
	mulld %r4, %r17, %r25
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r17, %r25
	add %r28, %r28, %r4
	mulld %r4, %r18, %r24
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r18, %r24
	add %r28, %r28, %r4
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r15, %r19
	add %r29, %r29, %r4
	mulld %r4, %r16, %r27
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r27
	add %r29, %r29, %r4
	mulld %r4, %r17, %r26
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r26
	add %r29, %r29, %r4
	mulld %r4, %r18, %r25
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r18, %r25
	add %r29, %r29, %r4
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r15, %r20
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r20
	add %r30, %r30, %r4
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r16, %r19
	add %r30, %r30, %r4
	mulld %r4, %r17, %r27
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r27
	add %r30, %r30, %r4
	mulld %r4, %r18, %r26
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r18, %r26
	add %r30, %r30, %r4
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r16, %r20
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r16, %r20
	add %r31, %r31, %r4
	mulld %r4, %r17, %r19
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r17, %r19
	add %r31, %r31, %r4
	mulld %r4, %r18, %r27
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r27
	add %r31, %r31, %r4
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r16, %r21
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r21
	add %r5, %r5, %r4
	mulld %r4, %r17, %r20
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r17, %r20
	add %r5, %r5, %r4
	mulld %r4, %r18, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r18, %r19
	add %r5, %r5, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1168(%r6)
	std %r8, 1176(%r6)
	std %r9, 1184(%r6)
	std %r10, 1192(%r6)
	std %r11, 1200(%r6)
	ld %r14, 1088(%r6)
	ld %r15, 1096(%r6)
	ld %r16, 1104(%r6)
	ld %r17, 1112(%r6)
	ld %r18, 1120(%r6)
	ld %r19, 1448(%r6)
	ld %r20, 1456(%r6)
	ld %r21, 1464(%r6)
	ld %r22, 1472(%r6)
	ld %r23, 1480(%r6)
	rldicr %r14, %r14, 8, 55
	rldicr %r15, %r15, 8, 55
	rldicr %r16, %r16, 8, 55
	rldicr %r17, %r17, 8, 55
	rldicr %r18, %r18, 8, 55
	rldicr %r19, %r19, 5, 58
	rldicr %r20, %r20, 5, 58
	rldicr %r21, %r21, 5, 58
	rldicr %r22, %r22, 5, 58
	rldicr %r23, %r23, 5, 58
	li %r5, 19
	mulld %r24, %r20, %r5
	mulld %r25, %r21, %r5
	mulld %r26, %r22, %r5
	mulld %r27, %r23, %r5
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r15, %r27
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r27
	add %r28, %r28, %r4
	mulld %r4, %r16, %r26
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r26
	add %r28, %r28, %r4
	mulld %r4, %r17, %r25
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r17, %r25
	add %r28, %r28, %r4
	mulld %r4, %r18, %r24
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r18, %r24
	add %r28, %r28, %r4
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r15, %r19
	add %r29, %r29, %r4
	mulld %r4, %r16, %r27
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r27
	add %r29, %r29, %r4
	mulld %r4, %r17, %r26
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r26
	add %r29, %r29, %r4
	mulld %r4, %r18, %r25
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r18, %r25
	add %r29, %r29, %r4
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r15, %r20
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r20
	add %r30, %r30, %r4
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r16, %r19
	add %r30, %r30, %r4
	mulld %r4, %r17, %r27
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r27
	add %r30, %r30, %r4
	mulld %r4, %r18, %r26
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r18, %r26
	add %r30, %r30, %r4
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r16, %r20
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r16, %r20
	add %r31, %r31, %r4
	mulld %r4, %r17, %r19
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r17, %r19
	add %r31, %r31, %r4
	mulld %r4, %r18, %r27
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r27
	add %r31, %r31, %r4
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r16, %r21
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r21
	add %r5, %r5, %r4
	mulld %r4, %r17, %r20
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r17, %r20
	add %r5, %r5, %r4
	mulld %r4, %r18, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r18, %r19
	add %r5, %r5, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1248(%r6)
	std %r8, 1256(%r6)
	std %r9, 1264(%r6)
	std %r10, 1272(%r6)
	std %r11, 1280(%r6)
	ld %r14, 1288(%r6)
	ld %r15, 1296(%r6)
	ld %r16, 1304(%r6)
	ld %r17, 1312(%r6)
	ld %r18, 1320(%r6)
	ld %r19, 1328(%r6)
	ld %r20, 1336(%r6)
	ld %r21, 1344(%r6)
	ld %r22, 1352(%r6)
	ld %r23, 1360(%r6)
	rldicr %r14, %r14, 8, 55
	rldicr %r15, %r15, 8, 55
	rldicr %r16, %r16, 8, 55
	rldicr %r17, %r17, 8, 55
	rldicr %r18, %r18, 8, 55
	rldicr %r19, %r19, 5, 58
	rldicr %r20, %r20, 5, 58
	rldicr %r21, %r21, 5, 58
	rldicr %r22, %r22, 5, 58
	rldicr %r23, %r23, 5, 58
	li %r5, 19
	mulld %r24, %r20, %r5
	mulld %r25, %r21, %r5
	mulld %r26, %r22, %r5
	mulld %r27, %r23, %r5
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r15, %r27
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r27
	add %r28, %r28, %r4
	mulld %r4, %r16, %r26
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r26
	add %r28, %r28, %r4
	mulld %r4, %r17, %r25
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r17, %r25
	add %r28, %r28, %r4
	mulld %r4, %r18, %r24
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r18, %r24
	add %r28, %r28, %r4
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r15, %r19
	add %r29, %r29, %r4
	mulld %r4, %r16, %r27
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r27
	add %r29, %r29, %r4
	mulld %r4, %r17, %r26
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r26
	add %r29, %r29, %r4
	mulld %r4, %r18, %r25
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r18, %r25
	add %r29, %r29, %r4
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r15, %r20
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r20
	add %r30, %r30, %r4
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r16, %r19
	add %r30, %r30, %r4
	mulld %r4, %r17, %r27
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r27
	add %r30, %r30, %r4
	mulld %r4, %r18, %r26
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r18, %r26
	add %r30, %r30, %r4
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r16, %r20
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r16, %r20
	add %r31, %r31, %r4
	mulld %r4, %r17, %r19
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r17, %r19
	add %r31, %r31, %r4
	mulld %r4, %r18, %r27
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r27
	add %r31, %r31, %r4
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r16, %r21
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r21
	add %r5, %r5, %r4
	mulld %r4, %r17, %r20
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r17, %r20
	add %r5, %r5, %r4
	mulld %r4, %r18, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r18, %r19
	add %r5, %r5, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1128(%r6)
	std %r8, 1136(%r6)
	std %r9, 1144(%r6)
	std %r10, 1152(%r6)
	std %r11, 1160(%r6)
	cmpldi %cr0, %r12, 0
	bne %cr0, 21b
	li %r11, 0
	subf %r11, %r0, %r11
	ld %r5, 1128(%r6)
	ld %r7, 1208(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	std %r5, 1128(%r6)
	std %r7, 1208(%r6)
	ld %r5, 1136(%r6)
	ld %r7, 1216(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	std %r5, 1136(%r6)
	std %r7, 1216(%r6)
	ld %r5, 1144(%r6)
	ld %r7, 1224(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	std %r5, 1144(%r6)
	std %r7, 1224(%r6)
	ld %r5, 1152(%r6)
	ld %r7, 1232(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	std %r5, 1152(%r6)
	std %r7, 1232(%r6)
	ld %r5, 1160(%r6)
	ld %r7, 1240(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	std %r5, 1160(%r6)
	std %r7, 1240(%r6)
	ld %r5, 1168(%r6)
	ld %r7, 1248(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	std %r5, 1168(%r6)
	std %r7, 1248(%r6)
	ld %r5, 1176(%r6)
	ld %r7, 1256(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	std %r5, 1176(%r6)
	std %r7, 1256(%r6)
	ld %r5, 1184(%r6)
	ld %r7, 1264(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	std %r5, 1184(%r6)
	std %r7, 1264(%r6)
	ld %r5, 1192(%r6)
	ld %r7, 1272(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	std %r5, 1192(%r6)
	std %r7, 1272(%r6)
	ld %r5, 1200(%r6)
	ld %r7, 1280(%r6)
	xor %r8, %r5, %r7
	and %r8, %r8, %r11
	xor %r5, %r5, %r8
	xor %r7, %r7, %r8
	std %r5, 1200(%r6)
	std %r7, 1280(%r6)
	ld %r14, 1168(%r6)
	ld %r15, 1176(%r6)
	ld %r16, 1184(%r6)
	ld %r17, 1192(%r6)
	ld %r18, 1200(%r6)
	rldicr %r19, %r14, 4, 59
	rldicr %r14, %r14, 9, 54
	rldicr %r20, %r15, 5, 58
	rldicr %r21, %r16, 5, 58
	rldicr %r22, %r17, 5, 58
	rldicr %r23, %r18, 5, 58
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	rldicr %r19, %r15, 4, 59
	rldicr %r15, %r15, 9, 54
	li %r24, 19
	mulld %r23, %r23, %r24
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r19
	add %r30, %r30, %r4
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r15, %r23
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r23
	add %r28, %r28, %r4
	rldicr %r19, %r16, 4, 59
	rldicr %r16, %r16, 9, 54
	mulld %r22, %r22, %r24
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r19
	add %r5, %r5, %r4
	mulld %r4, %r16, %r22
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r22
	add %r28, %r28, %r4
	mulld %r4, %r16, %r23
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r23
	add %r29, %r29, %r4
	rldicr %r17, %r17, 8, 55
	mulld %r4, %r17, %r22
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r22
	add %r29, %r29, %r4
	rldicr %r17, %r17, 1, 62
	mulld %r4, %r17, %r23
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r23
	add %r30, %r30, %r4
	rldicr %r18, %r18, 8, 55
	mulld %r4, %r18, %r23
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r23
	add %r31, %r31, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1528(%r6)
	std %r8, 1536(%r6)
	std %r9, 1544(%r6)
	std %r10, 1552(%r6)
	std %r11, 1560(%r6)
	ld %r14, 1528(%r6)
	ld %r15, 1536(%r6)
	ld %r16, 1544(%r6)
	ld %r17, 1552(%r6)
	ld %r18, 1560(%r6)
	rldicr %r19, %r14, 4, 59
	rldicr %r14, %r14, 9, 54
	rldicr %r20, %r15, 5, 58
	rldicr %r21, %r16, 5, 58
	rldicr %r22, %r17, 5, 58
	rldicr %r23, %r18, 5, 58
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	rldicr %r19, %r15, 4, 59
	rldicr %r15, %r15, 9, 54
	li %r24, 19
	mulld %r23, %r23, %r24
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r19
	add %r30, %r30, %r4
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r15, %r23
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r23
	add %r28, %r28, %r4
	rldicr %r19, %r16, 4, 59
	rldicr %r16, %r16, 9, 54
	mulld %r22, %r22, %r24
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r19
	add %r5, %r5, %r4
	mulld %r4, %r16, %r22
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r22
	add %r28, %r28, %r4
	mulld %r4, %r16, %r23
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r23
	add %r29, %r29, %r4
	rldicr %r17, %r17, 8, 55
	mulld %r4, %r17, %r22
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r22
	add %r29, %r29, %r4
	rldicr %r17, %r17, 1, 62
	mulld %r4, %r17, %r23
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r23
	add %r30, %r30, %r4
	rldicr %r18, %r18, 8, 55
	mulld %r4, %r18, %r23
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r23
	add %r31, %r31, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1568(%r6)
	std %r8, 1576(%r6)
	std %r9, 1584(%r6)
	std %r10, 1592(%r6)
	std %r11, 1600(%r6)
	ld %r14, 1568(%r6)
	ld %r15, 1576(%r6)
	ld %r16, 1584(%r6)
	ld %r17, 1592(%r6)
	ld %r18, 1600(%r6)
	rldicr %r19, %r14, 4, 59
	rldicr %r14, %r14, 9, 54
	rldicr %r20, %r15, 5, 58
	rldicr %r21, %r16, 5, 58
	rldicr %r22, %r17, 5, 58
	rldicr %r23, %r18, 5, 58
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	rldicr %r19, %r15, 4, 59
	rldicr %r15, %r15, 9, 54
	li %r24, 19
	mulld %r23, %r23, %r24
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r19
	add %r30, %r30, %r4
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r15, %r23
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r23
	add %r28, %r28, %r4
	rldicr %r19, %r16, 4, 59
	rldicr %r16, %r16, 9, 54
	mulld %r22, %r22, %r24
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r19
	add %r5, %r5, %r4
	mulld %r4, %r16, %r22
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r22
	add %r28, %r28, %r4
	mulld %r4, %r16, %r23
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r23
	add %r29, %r29, %r4
	rldicr %r17, %r17, 8, 55
	mulld %r4, %r17, %r22
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r22
	add %r29, %r29, %r4
	rldicr %r17, %r17, 1, 62
	mulld %r4, %r17, %r23
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r23
	add %r30, %r30, %r4
	rldicr %r18, %r18, 8, 55
	mulld %r4, %r18, %r23
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r23
	add %r31, %r31, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1568(%r6)
	std %r8, 1576(%r6)
	std %r9, 1584(%r6)
	std %r10, 1592(%r6)
	std %r11, 1600(%r6)
	ld %r14, 1168(%r6)
	ld %r15, 1176(%r6)
	ld %r16, 1184(%r6)
	ld %r17, 1192(%r6)
	ld %r18, 1200(%r6)
	ld %r19, 1568(%r6)
	ld %r20, 1576(%r6)
	ld %r21, 1584(%r6)
	ld %r22, 1592(%r6)
	ld %r23, 1600(%r6)
	rldicr %r14, %r14, 8, 55
	rldicr %r15, %r15, 8, 55
	rldicr %r16, %r16, 8, 55
	rldicr %r17, %r17, 8, 55
	rldicr %r18, %r18, 8, 55
	rldicr %r19, %r19, 5, 58
	rldicr %r20, %r20, 5, 58
	rldicr %r21, %r21, 5, 58
	rldicr %r22, %r22, 5, 58
	rldicr %r23, %r23, 5, 58
	li %r5, 19
	mulld %r24, %r20, %r5
	mulld %r25, %r21, %r5
	mulld %r26, %r22, %r5
	mulld %r27, %r23, %r5
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r15, %r27
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r27
	add %r28, %r28, %r4
	mulld %r4, %r16, %r26
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r26
	add %r28, %r28, %r4
	mulld %r4, %r17, %r25
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r17, %r25
	add %r28, %r28, %r4
	mulld %r4, %r18, %r24
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r18, %r24
	add %r28, %r28, %r4
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r15, %r19
	add %r29, %r29, %r4
	mulld %r4, %r16, %r27
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r27
	add %r29, %r29, %r4
	mulld %r4, %r17, %r26
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r26
	add %r29, %r29, %r4
	mulld %r4, %r18, %r25
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r18, %r25
	add %r29, %r29, %r4
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r15, %r20
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r20
	add %r30, %r30, %r4
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r16, %r19
	add %r30, %r30, %r4
	mulld %r4, %r17, %r27
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r27
	add %r30, %r30, %r4
	mulld %r4, %r18, %r26
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r18, %r26
	add %r30, %r30, %r4
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r16, %r20
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r16, %r20
	add %r31, %r31, %r4
	mulld %r4, %r17, %r19
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r17, %r19
	add %r31, %r31, %r4
	mulld %r4, %r18, %r27
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r27
	add %r31, %r31, %r4
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r16, %r21
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r21
	add %r5, %r5, %r4
	mulld %r4, %r17, %r20
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r17, %r20
	add %r5, %r5, %r4
	mulld %r4, %r18, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r18, %r19
	add %r5, %r5, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1568(%r6)
	std %r8, 1576(%r6)
	std %r9, 1584(%r6)
	std %r10, 1592(%r6)
	std %r11, 1600(%r6)
	ld %r14, 1528(%r6)
	ld %r15, 1536(%r6)
	ld %r16, 1544(%r6)
	ld %r17, 1552(%r6)
	ld %r18, 1560(%r6)
	ld %r19, 1568(%r6)
	ld %r20, 1576(%r6)
	ld %r21, 1584(%r6)
	ld %r22, 1592(%r6)
	ld %r23, 1600(%r6)
	rldicr %r14, %r14, 8, 55
	rldicr %r15, %r15, 8, 55
	rldicr %r16, %r16, 8, 55
	rldicr %r17, %r17, 8, 55
	rldicr %r18, %r18, 8, 55
	rldicr %r19, %r19, 5, 58
	rldicr %r20, %r20, 5, 58
	rldicr %r21, %r21, 5, 58
	rldicr %r22, %r22, 5, 58
	rldicr %r23, %r23, 5, 58
	li %r5, 19
	mulld %r24, %r20, %r5
	mulld %r25, %r21, %r5
	mulld %r26, %r22, %r5
	mulld %r27, %r23, %r5
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r15, %r27
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r27
	add %r28, %r28, %r4
	mulld %r4, %r16, %r26
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r26
	add %r28, %r28, %r4
	mulld %r4, %r17, %r25
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r17, %r25
	add %r28, %r28, %r4
	mulld %r4, %r18, %r24
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r18, %r24
	add %r28, %r28, %r4
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r15, %r19
	add %r29, %r29, %r4
	mulld %r4, %r16, %r27
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r27
	add %r29, %r29, %r4
	mulld %r4, %r17, %r26
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r26
	add %r29, %r29, %r4
	mulld %r4, %r18, %r25
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r18, %r25
	add %r29, %r29, %r4
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r15, %r20
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r20
	add %r30, %r30, %r4
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r16, %r19
	add %r30, %r30, %r4
	mulld %r4, %r17, %r27
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r27
	add %r30, %r30, %r4
	mulld %r4, %r18, %r26
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r18, %r26
	add %r30, %r30, %r4
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r16, %r20
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r16, %r20
	add %r31, %r31, %r4
	mulld %r4, %r17, %r19
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r17, %r19
	add %r31, %r31, %r4
	mulld %r4, %r18, %r27
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r27
	add %r31, %r31, %r4
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r16, %r21
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r21
	add %r5, %r5, %r4
	mulld %r4, %r17, %r20
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r17, %r20
	add %r5, %r5, %r4
	mulld %r4, %r18, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r18, %r19
	add %r5, %r5, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1528(%r6)
	std %r8, 1536(%r6)
	std %r9, 1544(%r6)
	std %r10, 1552(%r6)
	std %r11, 1560(%r6)
	ld %r14, 1528(%r6)
	ld %r15, 1536(%r6)
	ld %r16, 1544(%r6)
	ld %r17, 1552(%r6)
	ld %r18, 1560(%r6)
	rldicr %r19, %r14, 4, 59
	rldicr %r14, %r14, 9, 54
	rldicr %r20, %r15, 5, 58
	rldicr %r21, %r16, 5, 58
	rldicr %r22, %r17, 5, 58
	rldicr %r23, %r18, 5, 58
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	rldicr %r19, %r15, 4, 59
	rldicr %r15, %r15, 9, 54
	li %r24, 19
	mulld %r23, %r23, %r24
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r19
	add %r30, %r30, %r4
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r15, %r23
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r23
	add %r28, %r28, %r4
	rldicr %r19, %r16, 4, 59
	rldicr %r16, %r16, 9, 54
	mulld %r22, %r22, %r24
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r19
	add %r5, %r5, %r4
	mulld %r4, %r16, %r22
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r22
	add %r28, %r28, %r4
	mulld %r4, %r16, %r23
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r23
	add %r29, %r29, %r4
	rldicr %r17, %r17, 8, 55
	mulld %r4, %r17, %r22
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r22
	add %r29, %r29, %r4
	rldicr %r17, %r17, 1, 62
	mulld %r4, %r17, %r23
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r23
	add %r30, %r30, %r4
	rldicr %r18, %r18, 8, 55
	mulld %r4, %r18, %r23
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r23
	add %r31, %r31, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1608(%r6)
	std %r8, 1616(%r6)
	std %r9, 1624(%r6)
	std %r10, 1632(%r6)
	std %r11, 1640(%r6)
	ld %r14, 1568(%r6)
	ld %r15, 1576(%r6)
	ld %r16, 1584(%r6)
	ld %r17, 1592(%r6)
	ld %r18, 1600(%r6)
	ld %r19, 1608(%r6)
	ld %r20, 1616(%r6)
	ld %r21, 1624(%r6)
	ld %r22, 1632(%r6)
	ld %r23, 1640(%r6)
	rldicr %r14, %r14, 8, 55
	rldicr %r15, %r15, 8, 55
	rldicr %r16, %r16, 8, 55
	rldicr %r17, %r17, 8, 55
	rldicr %r18, %r18, 8, 55
	rldicr %r19, %r19, 5, 58
	rldicr %r20, %r20, 5, 58
	rldicr %r21, %r21, 5, 58
	rldicr %r22, %r22, 5, 58
	rldicr %r23, %r23, 5, 58
	li %r5, 19
	mulld %r24, %r20, %r5
	mulld %r25, %r21, %r5
	mulld %r26, %r22, %r5
	mulld %r27, %r23, %r5
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r15, %r27
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r27
	add %r28, %r28, %r4
	mulld %r4, %r16, %r26
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r26
	add %r28, %r28, %r4
	mulld %r4, %r17, %r25
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r17, %r25
	add %r28, %r28, %r4
	mulld %r4, %r18, %r24
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r18, %r24
	add %r28, %r28, %r4
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r15, %r19
	add %r29, %r29, %r4
	mulld %r4, %r16, %r27
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r27
	add %r29, %r29, %r4
	mulld %r4, %r17, %r26
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r26
	add %r29, %r29, %r4
	mulld %r4, %r18, %r25
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r18, %r25
	add %r29, %r29, %r4
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r15, %r20
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r20
	add %r30, %r30, %r4
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r16, %r19
	add %r30, %r30, %r4
	mulld %r4, %r17, %r27
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r27
	add %r30, %r30, %r4
	mulld %r4, %r18, %r26
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r18, %r26
	add %r30, %r30, %r4
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r16, %r20
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r16, %r20
	add %r31, %r31, %r4
	mulld %r4, %r17, %r19
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r17, %r19
	add %r31, %r31, %r4
	mulld %r4, %r18, %r27
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r27
	add %r31, %r31, %r4
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r16, %r21
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r21
	add %r5, %r5, %r4
	mulld %r4, %r17, %r20
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r17, %r20
	add %r5, %r5, %r4
	mulld %r4, %r18, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r18, %r19
	add %r5, %r5, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1568(%r6)
	std %r8, 1576(%r6)
	std %r9, 1584(%r6)
	std %r10, 1592(%r6)
	std %r11, 1600(%r6)
	ld %r14, 1568(%r6)
	ld %r15, 1576(%r6)
	ld %r16, 1584(%r6)
	ld %r17, 1592(%r6)
	ld %r18, 1600(%r6)
	rldicr %r19, %r14, 4, 59
	rldicr %r14, %r14, 9, 54
	rldicr %r20, %r15, 5, 58
	rldicr %r21, %r16, 5, 58
	rldicr %r22, %r17, 5, 58
	rldicr %r23, %r18, 5, 58
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	rldicr %r19, %r15, 4, 59
	rldicr %r15, %r15, 9, 54
	li %r24, 19
	mulld %r23, %r23, %r24
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r19
	add %r30, %r30, %r4
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r15, %r23
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r23
	add %r28, %r28, %r4
	rldicr %r19, %r16, 4, 59
	rldicr %r16, %r16, 9, 54
	mulld %r22, %r22, %r24
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r19
	add %r5, %r5, %r4
	mulld %r4, %r16, %r22
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r22
	add %r28, %r28, %r4
	mulld %r4, %r16, %r23
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r23
	add %r29, %r29, %r4
	rldicr %r17, %r17, 8, 55
	mulld %r4, %r17, %r22
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r22
	add %r29, %r29, %r4
	rldicr %r17, %r17, 1, 62
	mulld %r4, %r17, %r23
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r23
	add %r30, %r30, %r4
	rldicr %r18, %r18, 8, 55
	mulld %r4, %r18, %r23
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r23
	add %r31, %r31, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1608(%r6)
	std %r8, 1616(%r6)
	std %r9, 1624(%r6)
	std %r10, 1632(%r6)
	std %r11, 1640(%r6)
	li %r12, 4
22:
	or %r14, %r7, %r7
	or %r15, %r8, %r8
	or %r16, %r9, %r9
	or %r17, %r10, %r10
	or %r18, %r11, %r11
	rldicr %r19, %r14, 4, 59
	rldicr %r14, %r14, 9, 54
	rldicr %r20, %r15, 5, 58
	rldicr %r21, %r16, 5, 58
	rldicr %r22, %r17, 5, 58
	rldicr %r23, %r18, 5, 58
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	rldicr %r19, %r15, 4, 59
	rldicr %r15, %r15, 9, 54
	li %r24, 19
	mulld %r23, %r23, %r24
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r19
	add %r30, %r30, %r4
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r15, %r23
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r23
	add %r28, %r28, %r4
	rldicr %r19, %r16, 4, 59
	rldicr %r16, %r16, 9, 54
	mulld %r22, %r22, %r24
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r19
	add %r5, %r5, %r4
	mulld %r4, %r16, %r22
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r22
	add %r28, %r28, %r4
	mulld %r4, %r16, %r23
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r23
	add %r29, %r29, %r4
	rldicr %r17, %r17, 8, 55
	mulld %r4, %r17, %r22
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r22
	add %r29, %r29, %r4
	rldicr %r17, %r17, 1, 62
	mulld %r4, %r17, %r23
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r23
	add %r30, %r30, %r4
	rldicr %r18, %r18, 8, 55
	mulld %r4, %r18, %r23
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r23
	add %r31, %r31, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1608(%r6)
	std %r8, 1616(%r6)
	std %r9, 1624(%r6)
	std %r10, 1632(%r6)
	std %r11, 1640(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 22b
	ld %r14, 1608(%r6)
	ld %r15, 1616(%r6)
	ld %r16, 1624(%r6)
	ld %r17, 1632(%r6)
	ld %r18, 1640(%r6)
	ld %r19, 1568(%r6)
	ld %r20, 1576(%r6)
	ld %r21, 1584(%r6)
	ld %r22, 1592(%r6)
	ld %r23, 1600(%r6)
	rldicr %r14, %r14, 8, 55
	rldicr %r15, %r15, 8, 55
	rldicr %r16, %r16, 8, 55
	rldicr %r17, %r17, 8, 55
	rldicr %r18, %r18, 8, 55
	rldicr %r19, %r19, 5, 58
	rldicr %r20, %r20, 5, 58
	rldicr %r21, %r21, 5, 58
	rldicr %r22, %r22, 5, 58
	rldicr %r23, %r23, 5, 58
	li %r5, 19
	mulld %r24, %r20, %r5
	mulld %r25, %r21, %r5
	mulld %r26, %r22, %r5
	mulld %r27, %r23, %r5
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r15, %r27
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r27
	add %r28, %r28, %r4
	mulld %r4, %r16, %r26
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r26
	add %r28, %r28, %r4
	mulld %r4, %r17, %r25
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r17, %r25
	add %r28, %r28, %r4
	mulld %r4, %r18, %r24
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r18, %r24
	add %r28, %r28, %r4
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r15, %r19
	add %r29, %r29, %r4
	mulld %r4, %r16, %r27
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r27
	add %r29, %r29, %r4
	mulld %r4, %r17, %r26
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r26
	add %r29, %r29, %r4
	mulld %r4, %r18, %r25
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r18, %r25
	add %r29, %r29, %r4
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r15, %r20
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r20
	add %r30, %r30, %r4
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r16, %r19
	add %r30, %r30, %r4
	mulld %r4, %r17, %r27
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r27
	add %r30, %r30, %r4
	mulld %r4, %r18, %r26
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r18, %r26
	add %r30, %r30, %r4
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r16, %r20
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r16, %r20
	add %r31, %r31, %r4
	mulld %r4, %r17, %r19
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r17, %r19
	add %r31, %r31, %r4
	mulld %r4, %r18, %r27
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r27
	add %r31, %r31, %r4
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r16, %r21
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r21
	add %r5, %r5, %r4
	mulld %r4, %r17, %r20
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r17, %r20
	add %r5, %r5, %r4
	mulld %r4, %r18, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r18, %r19
	add %r5, %r5, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1568(%r6)
	std %r8, 1576(%r6)
	std %r9, 1584(%r6)
	std %r10, 1592(%r6)
	std %r11, 1600(%r6)
	ld %r14, 1568(%r6)
	ld %r15, 1576(%r6)
	ld %r16, 1584(%r6)
	ld %r17, 1592(%r6)
	ld %r18, 1600(%r6)
	rldicr %r19, %r14, 4, 59
	rldicr %r14, %r14, 9, 54
	rldicr %r20, %r15, 5, 58
	rldicr %r21, %r16, 5, 58
	rldicr %r22, %r17, 5, 58
	rldicr %r23, %r18, 5, 58
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	rldicr %r19, %r15, 4, 59
	rldicr %r15, %r15, 9, 54
	li %r24, 19
	mulld %r23, %r23, %r24
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r19
	add %r30, %r30, %r4
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r15, %r23
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r23
	add %r28, %r28, %r4
	rldicr %r19, %r16, 4, 59
	rldicr %r16, %r16, 9, 54
	mulld %r22, %r22, %r24
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r19
	add %r5, %r5, %r4
	mulld %r4, %r16, %r22
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r22
	add %r28, %r28, %r4
	mulld %r4, %r16, %r23
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r23
	add %r29, %r29, %r4
	rldicr %r17, %r17, 8, 55
	mulld %r4, %r17, %r22
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r22
	add %r29, %r29, %r4
	rldicr %r17, %r17, 1, 62
	mulld %r4, %r17, %r23
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r23
	add %r30, %r30, %r4
	rldicr %r18, %r18, 8, 55
	mulld %r4, %r18, %r23
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r23
	add %r31, %r31, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1608(%r6)
	std %r8, 1616(%r6)
	std %r9, 1624(%r6)
	std %r10, 1632(%r6)
	std %r11, 1640(%r6)
	li %r12, 9
23:
	or %r14, %r7, %r7
	or %r15, %r8, %r8
	or %r16, %r9, %r9
	or %r17, %r10, %r10
	or %r18, %r11, %r11
	rldicr %r19, %r14, 4, 59
	rldicr %r14, %r14, 9, 54
	rldicr %r20, %r15, 5, 58
	rldicr %r21, %r16, 5, 58
	rldicr %r22, %r17, 5, 58
	rldicr %r23, %r18, 5, 58
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	rldicr %r19, %r15, 4, 59
	rldicr %r15, %r15, 9, 54
	li %r24, 19
	mulld %r23, %r23, %r24
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r19
	add %r30, %r30, %r4
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r15, %r23
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r23
	add %r28, %r28, %r4
	rldicr %r19, %r16, 4, 59
	rldicr %r16, %r16, 9, 54
	mulld %r22, %r22, %r24
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r19
	add %r5, %r5, %r4
	mulld %r4, %r16, %r22
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r22
	add %r28, %r28, %r4
	mulld %r4, %r16, %r23
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r23
	add %r29, %r29, %r4
	rldicr %r17, %r17, 8, 55
	mulld %r4, %r17, %r22
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r22
	add %r29, %r29, %r4
	rldicr %r17, %r17, 1, 62
	mulld %r4, %r17, %r23
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r23
	add %r30, %r30, %r4
	rldicr %r18, %r18, 8, 55
	mulld %r4, %r18, %r23
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r23
	add %r31, %r31, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1608(%r6)
	std %r8, 1616(%r6)
	std %r9, 1624(%r6)
	std %r10, 1632(%r6)
	std %r11, 1640(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 23b
	ld %r14, 1608(%r6)
	ld %r15, 1616(%r6)
	ld %r16, 1624(%r6)
	ld %r17, 1632(%r6)
	ld %r18, 1640(%r6)
	ld %r19, 1568(%r6)
	ld %r20, 1576(%r6)
	ld %r21, 1584(%r6)
	ld %r22, 1592(%r6)
	ld %r23, 1600(%r6)
	rldicr %r14, %r14, 8, 55
	rldicr %r15, %r15, 8, 55
	rldicr %r16, %r16, 8, 55
	rldicr %r17, %r17, 8, 55
	rldicr %r18, %r18, 8, 55
	rldicr %r19, %r19, 5, 58
	rldicr %r20, %r20, 5, 58
	rldicr %r21, %r21, 5, 58
	rldicr %r22, %r22, 5, 58
	rldicr %r23, %r23, 5, 58
	li %r5, 19
	mulld %r24, %r20, %r5
	mulld %r25, %r21, %r5
	mulld %r26, %r22, %r5
	mulld %r27, %r23, %r5
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r15, %r27
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r27
	add %r28, %r28, %r4
	mulld %r4, %r16, %r26
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r26
	add %r28, %r28, %r4
	mulld %r4, %r17, %r25
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r17, %r25
	add %r28, %r28, %r4
	mulld %r4, %r18, %r24
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r18, %r24
	add %r28, %r28, %r4
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r15, %r19
	add %r29, %r29, %r4
	mulld %r4, %r16, %r27
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r27
	add %r29, %r29, %r4
	mulld %r4, %r17, %r26
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r26
	add %r29, %r29, %r4
	mulld %r4, %r18, %r25
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r18, %r25
	add %r29, %r29, %r4
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r15, %r20
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r20
	add %r30, %r30, %r4
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r16, %r19
	add %r30, %r30, %r4
	mulld %r4, %r17, %r27
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r27
	add %r30, %r30, %r4
	mulld %r4, %r18, %r26
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r18, %r26
	add %r30, %r30, %r4
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r16, %r20
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r16, %r20
	add %r31, %r31, %r4
	mulld %r4, %r17, %r19
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r17, %r19
	add %r31, %r31, %r4
	mulld %r4, %r18, %r27
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r27
	add %r31, %r31, %r4
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r16, %r21
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r21
	add %r5, %r5, %r4
	mulld %r4, %r17, %r20
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r17, %r20
	add %r5, %r5, %r4
	mulld %r4, %r18, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r18, %r19
	add %r5, %r5, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1608(%r6)
	std %r8, 1616(%r6)
	std %r9, 1624(%r6)
	std %r10, 1632(%r6)
	std %r11, 1640(%r6)
	ld %r14, 1608(%r6)
	ld %r15, 1616(%r6)
	ld %r16, 1624(%r6)
	ld %r17, 1632(%r6)
	ld %r18, 1640(%r6)
	rldicr %r19, %r14, 4, 59
	rldicr %r14, %r14, 9, 54
	rldicr %r20, %r15, 5, 58
	rldicr %r21, %r16, 5, 58
	rldicr %r22, %r17, 5, 58
	rldicr %r23, %r18, 5, 58
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	rldicr %r19, %r15, 4, 59
	rldicr %r15, %r15, 9, 54
	li %r24, 19
	mulld %r23, %r23, %r24
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r19
	add %r30, %r30, %r4
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r15, %r23
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r23
	add %r28, %r28, %r4
	rldicr %r19, %r16, 4, 59
	rldicr %r16, %r16, 9, 54
	mulld %r22, %r22, %r24
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r19
	add %r5, %r5, %r4
	mulld %r4, %r16, %r22
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r22
	add %r28, %r28, %r4
	mulld %r4, %r16, %r23
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r23
	add %r29, %r29, %r4
	rldicr %r17, %r17, 8, 55
	mulld %r4, %r17, %r22
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r22
	add %r29, %r29, %r4
	rldicr %r17, %r17, 1, 62
	mulld %r4, %r17, %r23
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r23
	add %r30, %r30, %r4
	rldicr %r18, %r18, 8, 55
	mulld %r4, %r18, %r23
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r23
	add %r31, %r31, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1648(%r6)
	std %r8, 1656(%r6)
	std %r9, 1664(%r6)
	std %r10, 1672(%r6)
	std %r11, 1680(%r6)
	li %r12, 19
24:
	or %r14, %r7, %r7
	or %r15, %r8, %r8
	or %r16, %r9, %r9
	or %r17, %r10, %r10
	or %r18, %r11, %r11
	rldicr %r19, %r14, 4, 59
	rldicr %r14, %r14, 9, 54
	rldicr %r20, %r15, 5, 58
	rldicr %r21, %r16, 5, 58
	rldicr %r22, %r17, 5, 58
	rldicr %r23, %r18, 5, 58
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	rldicr %r19, %r15, 4, 59
	rldicr %r15, %r15, 9, 54
	li %r24, 19
	mulld %r23, %r23, %r24
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r19
	add %r30, %r30, %r4
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r15, %r23
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r23
	add %r28, %r28, %r4
	rldicr %r19, %r16, 4, 59
	rldicr %r16, %r16, 9, 54
	mulld %r22, %r22, %r24
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r19
	add %r5, %r5, %r4
	mulld %r4, %r16, %r22
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r22
	add %r28, %r28, %r4
	mulld %r4, %r16, %r23
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r23
	add %r29, %r29, %r4
	rldicr %r17, %r17, 8, 55
	mulld %r4, %r17, %r22
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r22
	add %r29, %r29, %r4
	rldicr %r17, %r17, 1, 62
	mulld %r4, %r17, %r23
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r23
	add %r30, %r30, %r4
	rldicr %r18, %r18, 8, 55
	mulld %r4, %r18, %r23
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r23
	add %r31, %r31, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1648(%r6)
	std %r8, 1656(%r6)
	std %r9, 1664(%r6)
	std %r10, 1672(%r6)
	std %r11, 1680(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 24b
	ld %r14, 1648(%r6)
	ld %r15, 1656(%r6)
	ld %r16, 1664(%r6)
	ld %r17, 1672(%r6)
	ld %r18, 1680(%r6)
	ld %r19, 1608(%r6)
	ld %r20, 1616(%r6)
	ld %r21, 1624(%r6)
	ld %r22, 1632(%r6)
	ld %r23, 1640(%r6)
	rldicr %r14, %r14, 8, 55
	rldicr %r15, %r15, 8, 55
	rldicr %r16, %r16, 8, 55
	rldicr %r17, %r17, 8, 55
	rldicr %r18, %r18, 8, 55
	rldicr %r19, %r19, 5, 58
	rldicr %r20, %r20, 5, 58
	rldicr %r21, %r21, 5, 58
	rldicr %r22, %r22, 5, 58
	rldicr %r23, %r23, 5, 58
	li %r5, 19
	mulld %r24, %r20, %r5
	mulld %r25, %r21, %r5
	mulld %r26, %r22, %r5
	mulld %r27, %r23, %r5
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r15, %r27
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r27
	add %r28, %r28, %r4
	mulld %r4, %r16, %r26
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r26
	add %r28, %r28, %r4
	mulld %r4, %r17, %r25
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r17, %r25
	add %r28, %r28, %r4
	mulld %r4, %r18, %r24
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r18, %r24
	add %r28, %r28, %r4
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r15, %r19
	add %r29, %r29, %r4
	mulld %r4, %r16, %r27
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r27
	add %r29, %r29, %r4
	mulld %r4, %r17, %r26
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r26
	add %r29, %r29, %r4
	mulld %r4, %r18, %r25
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r18, %r25
	add %r29, %r29, %r4
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r15, %r20
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r20
	add %r30, %r30, %r4
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r16, %r19
	add %r30, %r30, %r4
	mulld %r4, %r17, %r27
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r27
	add %r30, %r30, %r4
	mulld %r4, %r18, %r26
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r18, %r26
	add %r30, %r30, %r4
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r16, %r20
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r16, %r20
	add %r31, %r31, %r4
	mulld %r4, %r17, %r19
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r17, %r19
	add %r31, %r31, %r4
	mulld %r4, %r18, %r27
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r27
	add %r31, %r31, %r4
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r16, %r21
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r21
	add %r5, %r5, %r4
	mulld %r4, %r17, %r20
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r17, %r20
	add %r5, %r5, %r4
	mulld %r4, %r18, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r18, %r19
	add %r5, %r5, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1608(%r6)
	std %r8, 1616(%r6)
	std %r9, 1624(%r6)
	std %r10, 1632(%r6)
	std %r11, 1640(%r6)
	ld %r14, 1608(%r6)
	ld %r15, 1616(%r6)
	ld %r16, 1624(%r6)
	ld %r17, 1632(%r6)
	ld %r18, 1640(%r6)
	rldicr %r19, %r14, 4, 59
	rldicr %r14, %r14, 9, 54
	rldicr %r20, %r15, 5, 58
	rldicr %r21, %r16, 5, 58
	rldicr %r22, %r17, 5, 58
	rldicr %r23, %r18, 5, 58
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	rldicr %r19, %r15, 4, 59
	rldicr %r15, %r15, 9, 54
	li %r24, 19
	mulld %r23, %r23, %r24
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r19
	add %r30, %r30, %r4
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r15, %r23
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r23
	add %r28, %r28, %r4
	rldicr %r19, %r16, 4, 59
	rldicr %r16, %r16, 9, 54
	mulld %r22, %r22, %r24
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r19
	add %r5, %r5, %r4
	mulld %r4, %r16, %r22
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r22
	add %r28, %r28, %r4
	mulld %r4, %r16, %r23
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r23
	add %r29, %r29, %r4
	rldicr %r17, %r17, 8, 55
	mulld %r4, %r17, %r22
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r22
	add %r29, %r29, %r4
	rldicr %r17, %r17, 1, 62
	mulld %r4, %r17, %r23
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r23
	add %r30, %r30, %r4
	rldicr %r18, %r18, 8, 55
	mulld %r4, %r18, %r23
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r23
	add %r31, %r31, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1608(%r6)
	std %r8, 1616(%r6)
	std %r9, 1624(%r6)
	std %r10, 1632(%r6)
	std %r11, 1640(%r6)
	li %r12, 9
25:
	or %r14, %r7, %r7
	or %r15, %r8, %r8
	or %r16, %r9, %r9
	or %r17, %r10, %r10
	or %r18, %r11, %r11
	rldicr %r19, %r14, 4, 59
	rldicr %r14, %r14, 9, 54
	rldicr %r20, %r15, 5, 58
	rldicr %r21, %r16, 5, 58
	rldicr %r22, %r17, 5, 58
	rldicr %r23, %r18, 5, 58
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	rldicr %r19, %r15, 4, 59
	rldicr %r15, %r15, 9, 54
	li %r24, 19
	mulld %r23, %r23, %r24
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r19
	add %r30, %r30, %r4
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r15, %r23
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r23
	add %r28, %r28, %r4
	rldicr %r19, %r16, 4, 59
	rldicr %r16, %r16, 9, 54
	mulld %r22, %r22, %r24
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r19
	add %r5, %r5, %r4
	mulld %r4, %r16, %r22
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r22
	add %r28, %r28, %r4
	mulld %r4, %r16, %r23
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r23
	add %r29, %r29, %r4
	rldicr %r17, %r17, 8, 55
	mulld %r4, %r17, %r22
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r22
	add %r29, %r29, %r4
	rldicr %r17, %r17, 1, 62
	mulld %r4, %r17, %r23
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r23
	add %r30, %r30, %r4
	rldicr %r18, %r18, 8, 55
	mulld %r4, %r18, %r23
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r23
	add %r31, %r31, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1608(%r6)
	std %r8, 1616(%r6)
	std %r9, 1624(%r6)
	std %r10, 1632(%r6)
	std %r11, 1640(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 25b
	ld %r14, 1608(%r6)
	ld %r15, 1616(%r6)
	ld %r16, 1624(%r6)
	ld %r17, 1632(%r6)
	ld %r18, 1640(%r6)
	ld %r19, 1568(%r6)
	ld %r20, 1576(%r6)
	ld %r21, 1584(%r6)
	ld %r22, 1592(%r6)
	ld %r23, 1600(%r6)
	rldicr %r14, %r14, 8, 55
	rldicr %r15, %r15, 8, 55
	rldicr %r16, %r16, 8, 55
	rldicr %r17, %r17, 8, 55
	rldicr %r18, %r18, 8, 55
	rldicr %r19, %r19, 5, 58
	rldicr %r20, %r20, 5, 58
	rldicr %r21, %r21, 5, 58
	rldicr %r22, %r22, 5, 58
	rldicr %r23, %r23, 5, 58
	li %r5, 19
	mulld %r24, %r20, %r5
	mulld %r25, %r21, %r5
	mulld %r26, %r22, %r5
	mulld %r27, %r23, %r5
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r15, %r27
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r27
	add %r28, %r28, %r4
	mulld %r4, %r16, %r26
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r26
	add %r28, %r28, %r4
	mulld %r4, %r17, %r25
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r17, %r25
	add %r28, %r28, %r4
	mulld %r4, %r18, %r24
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r18, %r24
	add %r28, %r28, %r4
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r15, %r19
	add %r29, %r29, %r4
	mulld %r4, %r16, %r27
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r27
	add %r29, %r29, %r4
	mulld %r4, %r17, %r26
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r26
	add %r29, %r29, %r4
	mulld %r4, %r18, %r25
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r18, %r25
	add %r29, %r29, %r4
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r15, %r20
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r20
	add %r30, %r30, %r4
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r16, %r19
	add %r30, %r30, %r4
	mulld %r4, %r17, %r27
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r27
	add %r30, %r30, %r4
	mulld %r4, %r18, %r26
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r18, %r26
	add %r30, %r30, %r4
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r16, %r20
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r16, %r20
	add %r31, %r31, %r4
	mulld %r4, %r17, %r19
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r17, %r19
	add %r31, %r31, %r4
	mulld %r4, %r18, %r27
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r27
	add %r31, %r31, %r4
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r16, %r21
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r21
	add %r5, %r5, %r4
	mulld %r4, %r17, %r20
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r17, %r20
	add %r5, %r5, %r4
	mulld %r4, %r18, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r18, %r19
	add %r5, %r5, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1568(%r6)
	std %r8, 1576(%r6)
	std %r9, 1584(%r6)
	std %r10, 1592(%r6)
	std %r11, 1600(%r6)
	ld %r14, 1568(%r6)
	ld %r15, 1576(%r6)
	ld %r16, 1584(%r6)
	ld %r17, 1592(%r6)
	ld %r18, 1600(%r6)
	rldicr %r19, %r14, 4, 59
	rldicr %r14, %r14, 9, 54
	rldicr %r20, %r15, 5, 58
	rldicr %r21, %r16, 5, 58
	rldicr %r22, %r17, 5, 58
	rldicr %r23, %r18, 5, 58
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	rldicr %r19, %r15, 4, 59
	rldicr %r15, %r15, 9, 54
	li %r24, 19
	mulld %r23, %r23, %r24
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r19
	add %r30, %r30, %r4
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r15, %r23
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r23
	add %r28, %r28, %r4
	rldicr %r19, %r16, 4, 59
	rldicr %r16, %r16, 9, 54
	mulld %r22, %r22, %r24
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r19
	add %r5, %r5, %r4
	mulld %r4, %r16, %r22
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r22
	add %r28, %r28, %r4
	mulld %r4, %r16, %r23
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r23
	add %r29, %r29, %r4
	rldicr %r17, %r17, 8, 55
	mulld %r4, %r17, %r22
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r22
	add %r29, %r29, %r4
	rldicr %r17, %r17, 1, 62
	mulld %r4, %r17, %r23
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r23
	add %r30, %r30, %r4
	rldicr %r18, %r18, 8, 55
	mulld %r4, %r18, %r23
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r23
	add %r31, %r31, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1608(%r6)
	std %r8, 1616(%r6)
	std %r9, 1624(%r6)
	std %r10, 1632(%r6)
	std %r11, 1640(%r6)
	li %r12, 49
26:
	or %r14, %r7, %r7
	or %r15, %r8, %r8
	or %r16, %r9, %r9
	or %r17, %r10, %r10
	or %r18, %r11, %r11
	rldicr %r19, %r14, 4, 59
	rldicr %r14, %r14, 9, 54
	rldicr %r20, %r15, 5, 58
	rldicr %r21, %r16, 5, 58
	rldicr %r22, %r17, 5, 58
	rldicr %r23, %r18, 5, 58
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	rldicr %r19, %r15, 4, 59
	rldicr %r15, %r15, 9, 54
	li %r24, 19
	mulld %r23, %r23, %r24
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r19
	add %r30, %r30, %r4
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r15, %r23
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r23
	add %r28, %r28, %r4
	rldicr %r19, %r16, 4, 59
	rldicr %r16, %r16, 9, 54
	mulld %r22, %r22, %r24
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r19
	add %r5, %r5, %r4
	mulld %r4, %r16, %r22
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r22
	add %r28, %r28, %r4
	mulld %r4, %r16, %r23
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r23
	add %r29, %r29, %r4
	rldicr %r17, %r17, 8, 55
	mulld %r4, %r17, %r22
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r22
	add %r29, %r29, %r4
	rldicr %r17, %r17, 1, 62
	mulld %r4, %r17, %r23
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r23
	add %r30, %r30, %r4
	rldicr %r18, %r18, 8, 55
	mulld %r4, %r18, %r23
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r23
	add %r31, %r31, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1608(%r6)
	std %r8, 1616(%r6)
	std %r9, 1624(%r6)
	std %r10, 1632(%r6)
	std %r11, 1640(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 26b
	ld %r14, 1608(%r6)
	ld %r15, 1616(%r6)
	ld %r16, 1624(%r6)
	ld %r17, 1632(%r6)
	ld %r18, 1640(%r6)
	ld %r19, 1568(%r6)
	ld %r20, 1576(%r6)
	ld %r21, 1584(%r6)
	ld %r22, 1592(%r6)
	ld %r23, 1600(%r6)
	rldicr %r14, %r14, 8, 55
	rldicr %r15, %r15, 8, 55
	rldicr %r16, %r16, 8, 55
	rldicr %r17, %r17, 8, 55
	rldicr %r18, %r18, 8, 55
	rldicr %r19, %r19, 5, 58
	rldicr %r20, %r20, 5, 58
	rldicr %r21, %r21, 5, 58
	rldicr %r22, %r22, 5, 58
	rldicr %r23, %r23, 5, 58
	li %r5, 19
	mulld %r24, %r20, %r5
	mulld %r25, %r21, %r5
	mulld %r26, %r22, %r5
	mulld %r27, %r23, %r5
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r15, %r27
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r27
	add %r28, %r28, %r4
	mulld %r4, %r16, %r26
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r26
	add %r28, %r28, %r4
	mulld %r4, %r17, %r25
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r17, %r25
	add %r28, %r28, %r4
	mulld %r4, %r18, %r24
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r18, %r24
	add %r28, %r28, %r4
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r15, %r19
	add %r29, %r29, %r4
	mulld %r4, %r16, %r27
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r27
	add %r29, %r29, %r4
	mulld %r4, %r17, %r26
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r26
	add %r29, %r29, %r4
	mulld %r4, %r18, %r25
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r18, %r25
	add %r29, %r29, %r4
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r15, %r20
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r20
	add %r30, %r30, %r4
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r16, %r19
	add %r30, %r30, %r4
	mulld %r4, %r17, %r27
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r27
	add %r30, %r30, %r4
	mulld %r4, %r18, %r26
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r18, %r26
	add %r30, %r30, %r4
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r16, %r20
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r16, %r20
	add %r31, %r31, %r4
	mulld %r4, %r17, %r19
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r17, %r19
	add %r31, %r31, %r4
	mulld %r4, %r18, %r27
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r27
	add %r31, %r31, %r4
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r16, %r21
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r21
	add %r5, %r5, %r4
	mulld %r4, %r17, %r20
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r17, %r20
	add %r5, %r5, %r4
	mulld %r4, %r18, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r18, %r19
	add %r5, %r5, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1608(%r6)
	std %r8, 1616(%r6)
	std %r9, 1624(%r6)
	std %r10, 1632(%r6)
	std %r11, 1640(%r6)
	ld %r14, 1608(%r6)
	ld %r15, 1616(%r6)
	ld %r16, 1624(%r6)
	ld %r17, 1632(%r6)
	ld %r18, 1640(%r6)
	rldicr %r19, %r14, 4, 59
	rldicr %r14, %r14, 9, 54
	rldicr %r20, %r15, 5, 58
	rldicr %r21, %r16, 5, 58
	rldicr %r22, %r17, 5, 58
	rldicr %r23, %r18, 5, 58
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	rldicr %r19, %r15, 4, 59
	rldicr %r15, %r15, 9, 54
	li %r24, 19
	mulld %r23, %r23, %r24
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r19
	add %r30, %r30, %r4
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r15, %r23
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r23
	add %r28, %r28, %r4
	rldicr %r19, %r16, 4, 59
	rldicr %r16, %r16, 9, 54
	mulld %r22, %r22, %r24
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r19
	add %r5, %r5, %r4
	mulld %r4, %r16, %r22
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r22
	add %r28, %r28, %r4
	mulld %r4, %r16, %r23
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r23
	add %r29, %r29, %r4
	rldicr %r17, %r17, 8, 55
	mulld %r4, %r17, %r22
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r22
	add %r29, %r29, %r4
	rldicr %r17, %r17, 1, 62
	mulld %r4, %r17, %r23
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r23
	add %r30, %r30, %r4
	rldicr %r18, %r18, 8, 55
	mulld %r4, %r18, %r23
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r23
	add %r31, %r31, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1648(%r6)
	std %r8, 1656(%r6)
	std %r9, 1664(%r6)
	std %r10, 1672(%r6)
	std %r11, 1680(%r6)
	li %r12, 99
27:
	or %r14, %r7, %r7
	or %r15, %r8, %r8
	or %r16, %r9, %r9
	or %r17, %r10, %r10
	or %r18, %r11, %r11
	rldicr %r19, %r14, 4, 59
	rldicr %r14, %r14, 9, 54
	rldicr %r20, %r15, 5, 58
	rldicr %r21, %r16, 5, 58
	rldicr %r22, %r17, 5, 58
	rldicr %r23, %r18, 5, 58
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	rldicr %r19, %r15, 4, 59
	rldicr %r15, %r15, 9, 54
	li %r24, 19
	mulld %r23, %r23, %r24
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r19
	add %r30, %r30, %r4
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r15, %r23
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r23
	add %r28, %r28, %r4
	rldicr %r19, %r16, 4, 59
	rldicr %r16, %r16, 9, 54
	mulld %r22, %r22, %r24
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r19
	add %r5, %r5, %r4
	mulld %r4, %r16, %r22
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r22
	add %r28, %r28, %r4
	mulld %r4, %r16, %r23
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r23
	add %r29, %r29, %r4
	rldicr %r17, %r17, 8, 55
	mulld %r4, %r17, %r22
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r22
	add %r29, %r29, %r4
	rldicr %r17, %r17, 1, 62
	mulld %r4, %r17, %r23
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r23
	add %r30, %r30, %r4
	rldicr %r18, %r18, 8, 55
	mulld %r4, %r18, %r23
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r23
	add %r31, %r31, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1648(%r6)
	std %r8, 1656(%r6)
	std %r9, 1664(%r6)
	std %r10, 1672(%r6)
	std %r11, 1680(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 27b
	ld %r14, 1648(%r6)
	ld %r15, 1656(%r6)
	ld %r16, 1664(%r6)
	ld %r17, 1672(%r6)
	ld %r18, 1680(%r6)
	ld %r19, 1608(%r6)
	ld %r20, 1616(%r6)
	ld %r21, 1624(%r6)
	ld %r22, 1632(%r6)
	ld %r23, 1640(%r6)
	rldicr %r14, %r14, 8, 55
	rldicr %r15, %r15, 8, 55
	rldicr %r16, %r16, 8, 55
	rldicr %r17, %r17, 8, 55
	rldicr %r18, %r18, 8, 55
	rldicr %r19, %r19, 5, 58
	rldicr %r20, %r20, 5, 58
	rldicr %r21, %r21, 5, 58
	rldicr %r22, %r22, 5, 58
	rldicr %r23, %r23, 5, 58
	li %r5, 19
	mulld %r24, %r20, %r5
	mulld %r25, %r21, %r5
	mulld %r26, %r22, %r5
	mulld %r27, %r23, %r5
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r15, %r27
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r27
	add %r28, %r28, %r4
	mulld %r4, %r16, %r26
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r26
	add %r28, %r28, %r4
	mulld %r4, %r17, %r25
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r17, %r25
	add %r28, %r28, %r4
	mulld %r4, %r18, %r24
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r18, %r24
	add %r28, %r28, %r4
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r15, %r19
	add %r29, %r29, %r4
	mulld %r4, %r16, %r27
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r27
	add %r29, %r29, %r4
	mulld %r4, %r17, %r26
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r26
	add %r29, %r29, %r4
	mulld %r4, %r18, %r25
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r18, %r25
	add %r29, %r29, %r4
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r15, %r20
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r20
	add %r30, %r30, %r4
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r16, %r19
	add %r30, %r30, %r4
	mulld %r4, %r17, %r27
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r27
	add %r30, %r30, %r4
	mulld %r4, %r18, %r26
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r18, %r26
	add %r30, %r30, %r4
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r16, %r20
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r16, %r20
	add %r31, %r31, %r4
	mulld %r4, %r17, %r19
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r17, %r19
	add %r31, %r31, %r4
	mulld %r4, %r18, %r27
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r27
	add %r31, %r31, %r4
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r16, %r21
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r21
	add %r5, %r5, %r4
	mulld %r4, %r17, %r20
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r17, %r20
	add %r5, %r5, %r4
	mulld %r4, %r18, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r18, %r19
	add %r5, %r5, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1608(%r6)
	std %r8, 1616(%r6)
	std %r9, 1624(%r6)
	std %r10, 1632(%r6)
	std %r11, 1640(%r6)
	ld %r14, 1608(%r6)
	ld %r15, 1616(%r6)
	ld %r16, 1624(%r6)
	ld %r17, 1632(%r6)
	ld %r18, 1640(%r6)
	rldicr %r19, %r14, 4, 59
	rldicr %r14, %r14, 9, 54
	rldicr %r20, %r15, 5, 58
	rldicr %r21, %r16, 5, 58
	rldicr %r22, %r17, 5, 58
	rldicr %r23, %r18, 5, 58
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	rldicr %r19, %r15, 4, 59
	rldicr %r15, %r15, 9, 54
	li %r24, 19
	mulld %r23, %r23, %r24
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r19
	add %r30, %r30, %r4
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r15, %r23
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r23
	add %r28, %r28, %r4
	rldicr %r19, %r16, 4, 59
	rldicr %r16, %r16, 9, 54
	mulld %r22, %r22, %r24
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r19
	add %r5, %r5, %r4
	mulld %r4, %r16, %r22
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r22
	add %r28, %r28, %r4
	mulld %r4, %r16, %r23
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r23
	add %r29, %r29, %r4
	rldicr %r17, %r17, 8, 55
	mulld %r4, %r17, %r22
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r22
	add %r29, %r29, %r4
	rldicr %r17, %r17, 1, 62
	mulld %r4, %r17, %r23
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r23
	add %r30, %r30, %r4
	rldicr %r18, %r18, 8, 55
	mulld %r4, %r18, %r23
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r23
	add %r31, %r31, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1608(%r6)
	std %r8, 1616(%r6)
	std %r9, 1624(%r6)
	std %r10, 1632(%r6)
	std %r11, 1640(%r6)
	li %r12, 49
28:
	or %r14, %r7, %r7
	or %r15, %r8, %r8
	or %r16, %r9, %r9
	or %r17, %r10, %r10
	or %r18, %r11, %r11
	rldicr %r19, %r14, 4, 59
	rldicr %r14, %r14, 9, 54
	rldicr %r20, %r15, 5, 58
	rldicr %r21, %r16, 5, 58
	rldicr %r22, %r17, 5, 58
	rldicr %r23, %r18, 5, 58
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	rldicr %r19, %r15, 4, 59
	rldicr %r15, %r15, 9, 54
	li %r24, 19
	mulld %r23, %r23, %r24
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r19
	add %r30, %r30, %r4
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r15, %r23
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r23
	add %r28, %r28, %r4
	rldicr %r19, %r16, 4, 59
	rldicr %r16, %r16, 9, 54
	mulld %r22, %r22, %r24
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r19
	add %r5, %r5, %r4
	mulld %r4, %r16, %r22
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r22
	add %r28, %r28, %r4
	mulld %r4, %r16, %r23
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r23
	add %r29, %r29, %r4
	rldicr %r17, %r17, 8, 55
	mulld %r4, %r17, %r22
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r22
	add %r29, %r29, %r4
	rldicr %r17, %r17, 1, 62
	mulld %r4, %r17, %r23
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r23
	add %r30, %r30, %r4
	rldicr %r18, %r18, 8, 55
	mulld %r4, %r18, %r23
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r23
	add %r31, %r31, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1608(%r6)
	std %r8, 1616(%r6)
	std %r9, 1624(%r6)
	std %r10, 1632(%r6)
	std %r11, 1640(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 28b
	ld %r14, 1608(%r6)
	ld %r15, 1616(%r6)
	ld %r16, 1624(%r6)
	ld %r17, 1632(%r6)
	ld %r18, 1640(%r6)
	ld %r19, 1568(%r6)
	ld %r20, 1576(%r6)
	ld %r21, 1584(%r6)
	ld %r22, 1592(%r6)
	ld %r23, 1600(%r6)
	rldicr %r14, %r14, 8, 55
	rldicr %r15, %r15, 8, 55
	rldicr %r16, %r16, 8, 55
	rldicr %r17, %r17, 8, 55
	rldicr %r18, %r18, 8, 55
	rldicr %r19, %r19, 5, 58
	rldicr %r20, %r20, 5, 58
	rldicr %r21, %r21, 5, 58
	rldicr %r22, %r22, 5, 58
	rldicr %r23, %r23, 5, 58
	li %r5, 19
	mulld %r24, %r20, %r5
	mulld %r25, %r21, %r5
	mulld %r26, %r22, %r5
	mulld %r27, %r23, %r5
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r15, %r27
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r27
	add %r28, %r28, %r4
	mulld %r4, %r16, %r26
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r26
	add %r28, %r28, %r4
	mulld %r4, %r17, %r25
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r17, %r25
	add %r28, %r28, %r4
	mulld %r4, %r18, %r24
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r18, %r24
	add %r28, %r28, %r4
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r15, %r19
	add %r29, %r29, %r4
	mulld %r4, %r16, %r27
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r27
	add %r29, %r29, %r4
	mulld %r4, %r17, %r26
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r26
	add %r29, %r29, %r4
	mulld %r4, %r18, %r25
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r18, %r25
	add %r29, %r29, %r4
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r15, %r20
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r20
	add %r30, %r30, %r4
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r16, %r19
	add %r30, %r30, %r4
	mulld %r4, %r17, %r27
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r27
	add %r30, %r30, %r4
	mulld %r4, %r18, %r26
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r18, %r26
	add %r30, %r30, %r4
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r16, %r20
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r16, %r20
	add %r31, %r31, %r4
	mulld %r4, %r17, %r19
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r17, %r19
	add %r31, %r31, %r4
	mulld %r4, %r18, %r27
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r27
	add %r31, %r31, %r4
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r16, %r21
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r21
	add %r5, %r5, %r4
	mulld %r4, %r17, %r20
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r17, %r20
	add %r5, %r5, %r4
	mulld %r4, %r18, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r18, %r19
	add %r5, %r5, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1568(%r6)
	std %r8, 1576(%r6)
	std %r9, 1584(%r6)
	std %r10, 1592(%r6)
	std %r11, 1600(%r6)
	ld %r14, 1568(%r6)
	ld %r15, 1576(%r6)
	ld %r16, 1584(%r6)
	ld %r17, 1592(%r6)
	ld %r18, 1600(%r6)
	rldicr %r19, %r14, 4, 59
	rldicr %r14, %r14, 9, 54
	rldicr %r20, %r15, 5, 58
	rldicr %r21, %r16, 5, 58
	rldicr %r22, %r17, 5, 58
	rldicr %r23, %r18, 5, 58
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	rldicr %r19, %r15, 4, 59
	rldicr %r15, %r15, 9, 54
	li %r24, 19
	mulld %r23, %r23, %r24
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r19
	add %r30, %r30, %r4
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r15, %r23
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r23
	add %r28, %r28, %r4
	rldicr %r19, %r16, 4, 59
	rldicr %r16, %r16, 9, 54
	mulld %r22, %r22, %r24
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r19
	add %r5, %r5, %r4
	mulld %r4, %r16, %r22
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r22
	add %r28, %r28, %r4
	mulld %r4, %r16, %r23
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r23
	add %r29, %r29, %r4
	rldicr %r17, %r17, 8, 55
	mulld %r4, %r17, %r22
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r22
	add %r29, %r29, %r4
	rldicr %r17, %r17, 1, 62
	mulld %r4, %r17, %r23
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r23
	add %r30, %r30, %r4
	rldicr %r18, %r18, 8, 55
	mulld %r4, %r18, %r23
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r23
	add %r31, %r31, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1568(%r6)
	std %r8, 1576(%r6)
	std %r9, 1584(%r6)
	std %r10, 1592(%r6)
	std %r11, 1600(%r6)
	li %r12, 4
29:
	or %r14, %r7, %r7
	or %r15, %r8, %r8
	or %r16, %r9, %r9
	or %r17, %r10, %r10
	or %r18, %r11, %r11
	rldicr %r19, %r14, 4, 59
	rldicr %r14, %r14, 9, 54
	rldicr %r20, %r15, 5, 58
	rldicr %r21, %r16, 5, 58
	rldicr %r22, %r17, 5, 58
	rldicr %r23, %r18, 5, 58
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	rldicr %r19, %r15, 4, 59
	rldicr %r15, %r15, 9, 54
	li %r24, 19
	mulld %r23, %r23, %r24
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r19
	add %r30, %r30, %r4
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r15, %r23
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r23
	add %r28, %r28, %r4
	rldicr %r19, %r16, 4, 59
	rldicr %r16, %r16, 9, 54
	mulld %r22, %r22, %r24
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r19
	add %r5, %r5, %r4
	mulld %r4, %r16, %r22
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r22
	add %r28, %r28, %r4
	mulld %r4, %r16, %r23
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r23
	add %r29, %r29, %r4
	rldicr %r17, %r17, 8, 55
	mulld %r4, %r17, %r22
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r22
	add %r29, %r29, %r4
	rldicr %r17, %r17, 1, 62
	mulld %r4, %r17, %r23
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r23
	add %r30, %r30, %r4
	rldicr %r18, %r18, 8, 55
	mulld %r4, %r18, %r23
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r23
	add %r31, %r31, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1568(%r6)
	std %r8, 1576(%r6)
	std %r9, 1584(%r6)
	std %r10, 1592(%r6)
	std %r11, 1600(%r6)
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 29b
	ld %r14, 1568(%r6)
	ld %r15, 1576(%r6)
	ld %r16, 1584(%r6)
	ld %r17, 1592(%r6)
	ld %r18, 1600(%r6)
	ld %r19, 1528(%r6)
	ld %r20, 1536(%r6)
	ld %r21, 1544(%r6)
	ld %r22, 1552(%r6)
	ld %r23, 1560(%r6)
	rldicr %r14, %r14, 8, 55
	rldicr %r15, %r15, 8, 55
	rldicr %r16, %r16, 8, 55
	rldicr %r17, %r17, 8, 55
	rldicr %r18, %r18, 8, 55
	rldicr %r19, %r19, 5, 58
	rldicr %r20, %r20, 5, 58
	rldicr %r21, %r21, 5, 58
	rldicr %r22, %r22, 5, 58
	rldicr %r23, %r23, 5, 58
	li %r5, 19
	mulld %r24, %r20, %r5
	mulld %r25, %r21, %r5
	mulld %r26, %r22, %r5
	mulld %r27, %r23, %r5
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r15, %r27
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r27
	add %r28, %r28, %r4
	mulld %r4, %r16, %r26
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r26
	add %r28, %r28, %r4
	mulld %r4, %r17, %r25
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r17, %r25
	add %r28, %r28, %r4
	mulld %r4, %r18, %r24
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r18, %r24
	add %r28, %r28, %r4
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r15, %r19
	add %r29, %r29, %r4
	mulld %r4, %r16, %r27
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r27
	add %r29, %r29, %r4
	mulld %r4, %r17, %r26
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r26
	add %r29, %r29, %r4
	mulld %r4, %r18, %r25
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r18, %r25
	add %r29, %r29, %r4
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r15, %r20
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r20
	add %r30, %r30, %r4
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r16, %r19
	add %r30, %r30, %r4
	mulld %r4, %r17, %r27
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r27
	add %r30, %r30, %r4
	mulld %r4, %r18, %r26
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r18, %r26
	add %r30, %r30, %r4
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r16, %r20
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r16, %r20
	add %r31, %r31, %r4
	mulld %r4, %r17, %r19
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r17, %r19
	add %r31, %r31, %r4
	mulld %r4, %r18, %r27
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r27
	add %r31, %r31, %r4
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r16, %r21
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r21
	add %r5, %r5, %r4
	mulld %r4, %r17, %r20
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r17, %r20
	add %r5, %r5, %r4
	mulld %r4, %r18, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r18, %r19
	add %r5, %r5, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1688(%r6)
	std %r8, 1696(%r6)
	std %r9, 1704(%r6)
	std %r10, 1712(%r6)
	std %r11, 1720(%r6)
	ld %r14, 1128(%r6)
	ld %r15, 1136(%r6)
	ld %r16, 1144(%r6)
	ld %r17, 1152(%r6)
	ld %r18, 1160(%r6)
	ld %r19, 1688(%r6)
	ld %r20, 1696(%r6)
	ld %r21, 1704(%r6)
	ld %r22, 1712(%r6)
	ld %r23, 1720(%r6)
	rldicr %r14, %r14, 8, 55
	rldicr %r15, %r15, 8, 55
	rldicr %r16, %r16, 8, 55
	rldicr %r17, %r17, 8, 55
	rldicr %r18, %r18, 8, 55
	rldicr %r19, %r19, 5, 58
	rldicr %r20, %r20, 5, 58
	rldicr %r21, %r21, 5, 58
	rldicr %r22, %r22, 5, 58
	rldicr %r23, %r23, 5, 58
	li %r5, 19
	mulld %r24, %r20, %r5
	mulld %r25, %r21, %r5
	mulld %r26, %r22, %r5
	mulld %r27, %r23, %r5
	mulld %r4, %r14, %r19
	rldicl %r7, %r4, 51, 13
	mulhdu %r28, %r14, %r19
	mulld %r4, %r15, %r27
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r15, %r27
	add %r28, %r28, %r4
	mulld %r4, %r16, %r26
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r16, %r26
	add %r28, %r28, %r4
	mulld %r4, %r17, %r25
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r17, %r25
	add %r28, %r28, %r4
	mulld %r4, %r18, %r24
	rldicl %r4, %r4, 51, 13
	add %r7, %r7, %r4
	mulhdu %r4, %r18, %r24
	add %r28, %r28, %r4
	mulld %r4, %r14, %r20
	rldicl %r8, %r4, 51, 13
	mulhdu %r29, %r14, %r20
	mulld %r4, %r15, %r19
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r15, %r19
	add %r29, %r29, %r4
	mulld %r4, %r16, %r27
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r16, %r27
	add %r29, %r29, %r4
	mulld %r4, %r17, %r26
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r17, %r26
	add %r29, %r29, %r4
	mulld %r4, %r18, %r25
	rldicl %r4, %r4, 51, 13
	add %r8, %r8, %r4
	mulhdu %r4, %r18, %r25
	add %r29, %r29, %r4
	mulld %r4, %r14, %r21
	rldicl %r9, %r4, 51, 13
	mulhdu %r30, %r14, %r21
	mulld %r4, %r15, %r20
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r15, %r20
	add %r30, %r30, %r4
	mulld %r4, %r16, %r19
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r16, %r19
	add %r30, %r30, %r4
	mulld %r4, %r17, %r27
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r17, %r27
	add %r30, %r30, %r4
	mulld %r4, %r18, %r26
	rldicl %r4, %r4, 51, 13
	add %r9, %r9, %r4
	mulhdu %r4, %r18, %r26
	add %r30, %r30, %r4
	mulld %r4, %r14, %r22
	rldicl %r10, %r4, 51, 13
	mulhdu %r31, %r14, %r22
	mulld %r4, %r15, %r21
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r15, %r21
	add %r31, %r31, %r4
	mulld %r4, %r16, %r20
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r16, %r20
	add %r31, %r31, %r4
	mulld %r4, %r17, %r19
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r17, %r19
	add %r31, %r31, %r4
	mulld %r4, %r18, %r27
	rldicl %r4, %r4, 51, 13
	add %r10, %r10, %r4
	mulhdu %r4, %r18, %r27
	add %r31, %r31, %r4
	mulld %r4, %r14, %r23
	rldicl %r11, %r4, 51, 13
	mulhdu %r5, %r14, %r23
	mulld %r4, %r15, %r22
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r15, %r22
	add %r5, %r5, %r4
	mulld %r4, %r16, %r21
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r16, %r21
	add %r5, %r5, %r4
	mulld %r4, %r17, %r20
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r17, %r20
	add %r5, %r5, %r4
	mulld %r4, %r18, %r19
	rldicl %r4, %r4, 51, 13
	add %r11, %r11, %r4
	mulhdu %r4, %r18, %r19
	add %r5, %r5, %r4
	add %r8, %r8, %r28
	add %r9, %r9, %r29
	add %r10, %r10, %r30
	add %r11, %r11, %r31
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r15, 19
	and %r14, %r5, %r4
	rldicl %r5, %r5, 13, 51
	mulld %r14, %r14, %r15
	mulld %r5, %r5, %r15
	add %r7, %r7, %r14
	add %r8, %r8, %r5
	rldicl %r16, %r7, 13, 51
	rldicl %r17, %r8, 13, 51
	rldicl %r18, %r9, 13, 51
	rldicl %r19, %r10, 13, 51
	rldicl %r20, %r11, 13, 51
	and %r7, %r7, %r4
	and %r8, %r8, %r4
	and %r9, %r9, %r4
	and %r10, %r10, %r4
	and %r11, %r11, %r4
	mulld %r20, %r20, %r15
	add %r7, %r7, %r20
	add %r8, %r8, %r16
	add %r9, %r9, %r17
	add %r10, %r10, %r18
	add %r11, %r11, %r19
	std %r7, 1128(%r6)
	std %r8, 1136(%r6)
	std %r9, 1144(%r6)
	std %r10, 1152(%r6)
	std %r11, 1160(%r6)
	ld %r14, 1128(%r6)
	ld %r15, 1136(%r6)
	ld %r16, 1144(%r6)
	ld %r17, 1152(%r6)
	ld %r18, 1160(%r6)
	li %r4, 1
	rldicr %r4, %r4, 51, 12
	addi %r4, %r4, -1
	li %r7, 19
	rldicl %r5, %r14, 13, 51
	and %r14, %r14, %r4
	add %r15, %r15, %r5
	rldicl %r5, %r15, 13, 51
	and %r15, %r15, %r4
	add %r16, %r16, %r5
	rldicl %r5, %r16, 13, 51
	and %r16, %r16, %r4
	add %r17, %r17, %r5
	rldicl %r5, %r17, 13, 51
	and %r17, %r17, %r4
	add %r18, %r18, %r5
	rldicl %r5, %r18, 13, 51
	and %r18, %r18, %r4
	mulld %r5, %r5, %r7
	add %r14, %r14, %r5
	rldicr %r5, %r15, 51, 12
	rldicl %r9, %r15, 51, 13
	rldicr %r12, %r16, 38, 25
	add %r9, %r9, %r12
	rldicl %r10, %r16, 38, 26
	rldicr %r12, %r17, 25, 38
	add %r10, %r10, %r12
	rldicl %r11, %r17, 25, 39
	rldicr %r12, %r18, 12, 51
	add %r11, %r11, %r12
	addc %r8, %r14, %r5
	addze %r9, %r9
	addze %r10, %r10
	addze %r11, %r11
	std %r8, 32(%r6)
	std %r9, 40(%r6)
	std %r10, 48(%r6)
	std %r11, 56(%r6)
	ld %r14, 896(%r6)
	ld %r15, 904(%r6)
	ld %r16, 912(%r6)
	ld %r17, 920(%r6)
	ld %r18, 928(%r6)
	ld %r19, 936(%r6)
	ld %r20, 944(%r6)
	ld %r21, 952(%r6)
	ld %r22, 960(%r6)
	ld %r23, 968(%r6)
	ld %r24, 976(%r6)
	ld %r25, 984(%r6)
	ld %r26, 992(%r6)
	ld %r27, 1000(%r6)
	ld %r28, 1008(%r6)
	ld %r29, 1016(%r6)
	ld %r30, 1024(%r6)
	ld %r31, 1032(%r6)
	lwz %r7, 60(%r6)
	rldicl %r8, %r7, 33, 31
	rldicr %r7, %r7, 33, 30
	rldicl %r7, %r7, 31, 33
	stw %r7, 60(%r6)
	li %r5, 19
	mulld %r8, %r8, %r5
	lwz %r7, 32(%r6)
	add %r7, %r7, %r8
	stw %r7, 32(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r8
	stw %r7, 36(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r8
	stw %r7, 40(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r8
	stw %r7, 44(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r8
	stw %r7, 48(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r8
	stw %r7, 52(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 56(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 60(%r6)
	rldicl %r8, %r7, 32, 32
	li %r8, 19
	lwz %r7, 32(%r6)
	add %r7, %r7, %r8
	stw %r7, 512(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 36(%r6)
	add %r7, %r7, %r8
	stw %r7, 516(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 40(%r6)
	add %r7, %r7, %r8
	stw %r7, 520(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 44(%r6)
	add %r7, %r7, %r8
	stw %r7, 524(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 48(%r6)
	add %r7, %r7, %r8
	stw %r7, 528(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 52(%r6)
	add %r7, %r7, %r8
	stw %r7, 532(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 56(%r6)
	add %r7, %r7, %r8
	stw %r7, 536(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 60(%r6)
	add %r7, %r7, %r8
	stw %r7, 540(%r6)
	rldicl %r8, %r7, 32, 32
	lwz %r7, 540(%r6)
	rldicl %r11, %r7, 33, 31
	li %r4, 0
	subf %r11, %r11, %r4
	rldicr %r7, %r7, 33, 30
	rldicl %r7, %r7, 31, 33
	stw %r7, 540(%r6)
	lwz %r5, 32(%r6)
	lwz %r7, 512(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 0(%r3)
	lwz %r5, 36(%r6)
	lwz %r7, 516(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 4(%r3)
	lwz %r5, 40(%r6)
	lwz %r7, 520(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 8(%r3)
	lwz %r5, 44(%r6)
	lwz %r7, 524(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 12(%r3)
	lwz %r5, 48(%r6)
	lwz %r7, 528(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 16(%r3)
	lwz %r5, 52(%r6)
	lwz %r7, 532(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 20(%r3)
	lwz %r5, 56(%r6)
	lwz %r7, 536(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 24(%r3)
	lwz %r5, 60(%r6)
	lwz %r7, 540(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 28(%r3)
	blr
