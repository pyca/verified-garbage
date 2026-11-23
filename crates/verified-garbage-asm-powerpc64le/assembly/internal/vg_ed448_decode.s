// The functions of `src/internal/vg_ed448_decode.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_decode:
	lwz %r7, 1064(%r6)
	stw %r7, 168(%r6)
	stw %r7, 56(%r6)
	lwz %r7, 1068(%r6)
	stw %r7, 172(%r6)
	stw %r7, 60(%r6)
	lwz %r7, 1072(%r6)
	stw %r7, 176(%r6)
	stw %r7, 64(%r6)
	lwz %r7, 1076(%r6)
	stw %r7, 180(%r6)
	stw %r7, 68(%r6)
	lwz %r7, 1080(%r6)
	stw %r7, 184(%r6)
	stw %r7, 72(%r6)
	lwz %r7, 1084(%r6)
	stw %r7, 188(%r6)
	stw %r7, 76(%r6)
	lwz %r7, 1088(%r6)
	stw %r7, 192(%r6)
	stw %r7, 80(%r6)
	lwz %r7, 1092(%r6)
	stw %r7, 196(%r6)
	stw %r7, 84(%r6)
	lwz %r7, 1096(%r6)
	stw %r7, 200(%r6)
	stw %r7, 88(%r6)
	lwz %r7, 1100(%r6)
	stw %r7, 204(%r6)
	stw %r7, 92(%r6)
	lwz %r7, 1104(%r6)
	stw %r7, 208(%r6)
	stw %r7, 96(%r6)
	lwz %r7, 1108(%r6)
	stw %r7, 212(%r6)
	stw %r7, 100(%r6)
	lwz %r7, 1112(%r6)
	stw %r7, 216(%r6)
	stw %r7, 104(%r6)
	lwz %r7, 1116(%r6)
	stw %r7, 220(%r6)
	stw %r7, 108(%r6)
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
	li %r10, 0
	lwz %r7, 0(%r3)
	lwz %r8, 1064(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 4(%r3)
	lwz %r8, 1068(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 8(%r3)
	lwz %r8, 1072(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 12(%r3)
	lwz %r8, 1076(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 16(%r3)
	lwz %r8, 1080(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 20(%r3)
	lwz %r8, 1084(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 24(%r3)
	lwz %r8, 1088(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 28(%r3)
	lwz %r8, 1092(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 32(%r3)
	lwz %r8, 1096(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 36(%r3)
	lwz %r8, 1100(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 40(%r3)
	lwz %r8, 1104(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 44(%r3)
	lwz %r8, 1108(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 48(%r3)
	lwz %r8, 1112(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	lwz %r7, 52(%r3)
	lwz %r8, 1116(%r6)
	xor %r7, %r7, %r8
	or %r10, %r10, %r7
	ld %r9, 3520(%r6)
	or %r9, %r9, %r10
	std %r9, 3520(%r6)
	lbz %r7, 1120(%r6)
	li %r8, 127
	and %r8, %r7, %r8
	ld %r9, 3520(%r6)
	or %r9, %r9, %r8
	std %r9, 3520(%r6)
	rldicl %r7, %r7, 57, 7
	stb %r7, 3528(%r6)
	lis %r7, 0
	ori %r7, %r7, 1
	stw %r7, 224(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 228(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 232(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 236(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 240(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 244(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 248(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 252(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 256(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 260(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 264(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 268(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 272(%r6)
	lis %r7, 0
	ori %r7, %r7, 0
	stw %r7, 276(%r6)
	ld %r15, 168(%r6)
	ld %r16, 176(%r6)
	ld %r17, 184(%r6)
	ld %r18, 192(%r6)
	ld %r19, 200(%r6)
	ld %r20, 208(%r6)
	ld %r21, 216(%r6)
	ld %r22, 168(%r6)
	ld %r23, 176(%r6)
	ld %r24, 184(%r6)
	ld %r25, 192(%r6)
	ld %r26, 200(%r6)
	ld %r27, 208(%r6)
	ld %r28, 216(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 280(%r6)
	std %r8, 288(%r6)
	std %r9, 296(%r6)
	std %r10, 304(%r6)
	std %r11, 312(%r6)
	std %r29, 320(%r6)
	std %r30, 328(%r6)
	ld %r7, 280(%r6)
	ld %r8, 224(%r6)
	subfc %r7, %r8, %r7
	std %r7, 392(%r6)
	ld %r7, 288(%r6)
	ld %r8, 232(%r6)
	subfe %r7, %r8, %r7
	std %r7, 400(%r6)
	ld %r7, 296(%r6)
	ld %r8, 240(%r6)
	subfe %r7, %r8, %r7
	std %r7, 408(%r6)
	ld %r7, 304(%r6)
	ld %r8, 248(%r6)
	subfe %r7, %r8, %r7
	std %r7, 416(%r6)
	ld %r7, 312(%r6)
	ld %r8, 256(%r6)
	subfe %r7, %r8, %r7
	std %r7, 424(%r6)
	ld %r7, 320(%r6)
	ld %r8, 264(%r6)
	subfe %r7, %r8, %r7
	std %r7, 432(%r6)
	ld %r7, 328(%r6)
	ld %r8, 272(%r6)
	subfe %r7, %r8, %r7
	std %r7, 440(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 392(%r6)
	subfc %r7, %r4, %r7
	std %r7, 392(%r6)
	ld %r7, 400(%r6)
	subfe %r7, %r8, %r7
	std %r7, 400(%r6)
	ld %r7, 408(%r6)
	subfe %r7, %r8, %r7
	std %r7, 408(%r6)
	ld %r7, 416(%r6)
	subfe %r7, %r5, %r7
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	subfe %r7, %r8, %r7
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	subfe %r7, %r8, %r7
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	subfe %r7, %r8, %r7
	std %r7, 440(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 392(%r6)
	subfc %r7, %r4, %r7
	std %r7, 392(%r6)
	ld %r7, 400(%r6)
	subfe %r7, %r8, %r7
	std %r7, 400(%r6)
	ld %r7, 408(%r6)
	subfe %r7, %r8, %r7
	std %r7, 408(%r6)
	ld %r7, 416(%r6)
	subfe %r7, %r5, %r7
	std %r7, 416(%r6)
	ld %r7, 424(%r6)
	subfe %r7, %r8, %r7
	std %r7, 424(%r6)
	ld %r7, 432(%r6)
	subfe %r7, %r8, %r7
	std %r7, 432(%r6)
	ld %r7, 440(%r6)
	subfe %r7, %r8, %r7
	std %r7, 440(%r6)
	ld %r15, 336(%r6)
	ld %r16, 344(%r6)
	ld %r17, 352(%r6)
	ld %r18, 360(%r6)
	ld %r19, 368(%r6)
	ld %r20, 376(%r6)
	ld %r21, 384(%r6)
	ld %r22, 280(%r6)
	ld %r23, 288(%r6)
	ld %r24, 296(%r6)
	ld %r25, 304(%r6)
	ld %r26, 312(%r6)
	ld %r27, 320(%r6)
	ld %r28, 328(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 448(%r6)
	std %r8, 456(%r6)
	std %r9, 464(%r6)
	std %r10, 472(%r6)
	std %r11, 480(%r6)
	std %r29, 488(%r6)
	std %r30, 496(%r6)
	ld %r7, 448(%r6)
	ld %r8, 224(%r6)
	subfc %r7, %r8, %r7
	std %r7, 448(%r6)
	ld %r7, 456(%r6)
	ld %r8, 232(%r6)
	subfe %r7, %r8, %r7
	std %r7, 456(%r6)
	ld %r7, 464(%r6)
	ld %r8, 240(%r6)
	subfe %r7, %r8, %r7
	std %r7, 464(%r6)
	ld %r7, 472(%r6)
	ld %r8, 248(%r6)
	subfe %r7, %r8, %r7
	std %r7, 472(%r6)
	ld %r7, 480(%r6)
	ld %r8, 256(%r6)
	subfe %r7, %r8, %r7
	std %r7, 480(%r6)
	ld %r7, 488(%r6)
	ld %r8, 264(%r6)
	subfe %r7, %r8, %r7
	std %r7, 488(%r6)
	ld %r7, 496(%r6)
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
	ld %r15, 392(%r6)
	ld %r16, 400(%r6)
	ld %r17, 408(%r6)
	ld %r18, 416(%r6)
	ld %r19, 424(%r6)
	ld %r20, 432(%r6)
	ld %r21, 440(%r6)
	ld %r22, 392(%r6)
	ld %r23, 400(%r6)
	ld %r24, 408(%r6)
	ld %r25, 416(%r6)
	ld %r26, 424(%r6)
	ld %r27, 432(%r6)
	ld %r28, 440(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 504(%r6)
	std %r8, 512(%r6)
	std %r9, 520(%r6)
	std %r10, 528(%r6)
	std %r11, 536(%r6)
	std %r29, 544(%r6)
	std %r30, 552(%r6)
	ld %r15, 504(%r6)
	ld %r16, 512(%r6)
	ld %r17, 520(%r6)
	ld %r18, 528(%r6)
	ld %r19, 536(%r6)
	ld %r20, 544(%r6)
	ld %r21, 552(%r6)
	ld %r22, 392(%r6)
	ld %r23, 400(%r6)
	ld %r24, 408(%r6)
	ld %r25, 416(%r6)
	ld %r26, 424(%r6)
	ld %r27, 432(%r6)
	ld %r28, 440(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 504(%r6)
	std %r8, 512(%r6)
	std %r9, 520(%r6)
	std %r10, 528(%r6)
	std %r11, 536(%r6)
	std %r29, 544(%r6)
	std %r30, 552(%r6)
	ld %r15, 504(%r6)
	ld %r16, 512(%r6)
	ld %r17, 520(%r6)
	ld %r18, 528(%r6)
	ld %r19, 536(%r6)
	ld %r20, 544(%r6)
	ld %r21, 552(%r6)
	ld %r22, 448(%r6)
	ld %r23, 456(%r6)
	ld %r24, 464(%r6)
	ld %r25, 472(%r6)
	ld %r26, 480(%r6)
	ld %r27, 488(%r6)
	ld %r28, 496(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 504(%r6)
	std %r8, 512(%r6)
	std %r9, 520(%r6)
	std %r10, 528(%r6)
	std %r11, 536(%r6)
	std %r29, 544(%r6)
	std %r30, 552(%r6)
	ld %r15, 392(%r6)
	ld %r16, 400(%r6)
	ld %r17, 408(%r6)
	ld %r18, 416(%r6)
	ld %r19, 424(%r6)
	ld %r20, 432(%r6)
	ld %r21, 440(%r6)
	ld %r22, 448(%r6)
	ld %r23, 456(%r6)
	ld %r24, 464(%r6)
	ld %r25, 472(%r6)
	ld %r26, 480(%r6)
	ld %r27, 488(%r6)
	ld %r28, 496(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 560(%r6)
	std %r8, 568(%r6)
	std %r9, 576(%r6)
	std %r10, 584(%r6)
	std %r11, 592(%r6)
	std %r29, 600(%r6)
	std %r30, 608(%r6)
	ld %r15, 560(%r6)
	ld %r16, 568(%r6)
	ld %r17, 576(%r6)
	ld %r18, 584(%r6)
	ld %r19, 592(%r6)
	ld %r20, 600(%r6)
	ld %r21, 608(%r6)
	ld %r22, 560(%r6)
	ld %r23, 568(%r6)
	ld %r24, 576(%r6)
	ld %r25, 584(%r6)
	ld %r26, 592(%r6)
	ld %r27, 600(%r6)
	ld %r28, 608(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 560(%r6)
	std %r8, 568(%r6)
	std %r9, 576(%r6)
	std %r10, 584(%r6)
	std %r11, 592(%r6)
	std %r29, 600(%r6)
	std %r30, 608(%r6)
	ld %r15, 504(%r6)
	ld %r16, 512(%r6)
	ld %r17, 520(%r6)
	ld %r18, 528(%r6)
	ld %r19, 536(%r6)
	ld %r20, 544(%r6)
	ld %r21, 552(%r6)
	ld %r22, 560(%r6)
	ld %r23, 568(%r6)
	ld %r24, 576(%r6)
	ld %r25, 584(%r6)
	ld %r26, 592(%r6)
	ld %r27, 600(%r6)
	ld %r28, 608(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 112(%r6)
	std %r8, 120(%r6)
	std %r9, 128(%r6)
	std %r10, 136(%r6)
	std %r11, 144(%r6)
	std %r29, 152(%r6)
	std %r30, 160(%r6)
	li %r4, 1
	li %r5, 0
	stw %r4, 840(%r6)
	stw %r5, 844(%r6)
	stw %r5, 848(%r6)
	stw %r5, 852(%r6)
	stw %r5, 856(%r6)
	stw %r5, 860(%r6)
	stw %r5, 864(%r6)
	stw %r5, 868(%r6)
	stw %r5, 872(%r6)
	stw %r5, 876(%r6)
	stw %r5, 880(%r6)
	stw %r5, 884(%r6)
	stw %r5, 888(%r6)
	stw %r5, 892(%r6)
	li %r12, 446
20:
	addi %r12, %r12, -1
	ld %r15, 840(%r6)
	ld %r16, 848(%r6)
	ld %r17, 856(%r6)
	ld %r18, 864(%r6)
	ld %r19, 872(%r6)
	ld %r20, 880(%r6)
	ld %r21, 888(%r6)
	ld %r22, 840(%r6)
	ld %r23, 848(%r6)
	ld %r24, 856(%r6)
	ld %r25, 864(%r6)
	ld %r26, 872(%r6)
	ld %r27, 880(%r6)
	ld %r28, 888(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 840(%r6)
	std %r8, 848(%r6)
	std %r9, 856(%r6)
	std %r10, 864(%r6)
	std %r11, 872(%r6)
	std %r29, 880(%r6)
	std %r30, 888(%r6)
	addi %r5, %r12, -222
	cmpldi %cr0, %r5, 0
	beq %cr0, 21f
	ld %r15, 840(%r6)
	ld %r16, 848(%r6)
	ld %r17, 856(%r6)
	ld %r18, 864(%r6)
	ld %r19, 872(%r6)
	ld %r20, 880(%r6)
	ld %r21, 888(%r6)
	ld %r22, 112(%r6)
	ld %r23, 120(%r6)
	ld %r24, 128(%r6)
	ld %r25, 136(%r6)
	ld %r26, 144(%r6)
	ld %r27, 152(%r6)
	ld %r28, 160(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 840(%r6)
	std %r8, 848(%r6)
	std %r9, 856(%r6)
	std %r10, 864(%r6)
	std %r11, 872(%r6)
	std %r29, 880(%r6)
	std %r30, 888(%r6)
	b 22f
21:
22:
	cmpldi %cr0, %r12, 0
	bne %cr0, 20b
	ld %r15, 504(%r6)
	ld %r16, 512(%r6)
	ld %r17, 520(%r6)
	ld %r18, 528(%r6)
	ld %r19, 536(%r6)
	ld %r20, 544(%r6)
	ld %r21, 552(%r6)
	ld %r22, 840(%r6)
	ld %r23, 848(%r6)
	ld %r24, 856(%r6)
	ld %r25, 864(%r6)
	ld %r26, 872(%r6)
	ld %r27, 880(%r6)
	ld %r28, 888(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 672(%r6)
	std %r8, 680(%r6)
	std %r9, 688(%r6)
	std %r10, 696(%r6)
	std %r11, 704(%r6)
	std %r29, 712(%r6)
	std %r30, 720(%r6)
	ld %r15, 672(%r6)
	ld %r16, 680(%r6)
	ld %r17, 688(%r6)
	ld %r18, 696(%r6)
	ld %r19, 704(%r6)
	ld %r20, 712(%r6)
	ld %r21, 720(%r6)
	ld %r22, 672(%r6)
	ld %r23, 680(%r6)
	ld %r24, 688(%r6)
	ld %r25, 696(%r6)
	ld %r26, 704(%r6)
	ld %r27, 712(%r6)
	ld %r28, 720(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	ld %r15, 448(%r6)
	ld %r16, 456(%r6)
	ld %r17, 464(%r6)
	ld %r18, 472(%r6)
	ld %r19, 480(%r6)
	ld %r20, 488(%r6)
	ld %r21, 496(%r6)
	ld %r22, 616(%r6)
	ld %r23, 624(%r6)
	ld %r24, 632(%r6)
	ld %r25, 640(%r6)
	ld %r26, 648(%r6)
	ld %r27, 656(%r6)
	ld %r28, 664(%r6)
	li %r7, 0
	li %r8, 0
	mulld %r4, %r15, %r22
	mulhdu %r5, %r15, %r22
	li %r9, 0
	addc %r7, %r7, %r4
	adde %r8, %r8, %r5
	addze %r9, %r9
	mulld %r4, %r15, %r23
	mulhdu %r5, %r15, %r23
	li %r10, 0
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r16, %r22
	mulhdu %r5, %r16, %r22
	addc %r8, %r8, %r4
	adde %r9, %r9, %r5
	addze %r10, %r10
	mulld %r4, %r15, %r24
	mulhdu %r5, %r15, %r24
	li %r11, 0
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r16, %r23
	mulhdu %r5, %r16, %r23
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r17, %r22
	mulhdu %r5, %r17, %r22
	addc %r9, %r9, %r4
	adde %r10, %r10, %r5
	addze %r11, %r11
	mulld %r4, %r15, %r25
	mulhdu %r5, %r15, %r25
	li %r29, 0
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r16, %r24
	mulhdu %r5, %r16, %r24
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r17, %r23
	mulhdu %r5, %r17, %r23
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r18, %r22
	mulhdu %r5, %r18, %r22
	addc %r10, %r10, %r4
	adde %r11, %r11, %r5
	addze %r29, %r29
	mulld %r4, %r15, %r26
	mulhdu %r5, %r15, %r26
	li %r30, 0
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r16, %r25
	mulhdu %r5, %r16, %r25
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r17, %r24
	mulhdu %r5, %r17, %r24
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r18, %r23
	mulhdu %r5, %r18, %r23
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r19, %r22
	mulhdu %r5, %r19, %r22
	addc %r11, %r11, %r4
	adde %r29, %r29, %r5
	addze %r30, %r30
	mulld %r4, %r15, %r27
	mulhdu %r5, %r15, %r27
	li %r31, 0
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r16, %r26
	mulhdu %r5, %r16, %r26
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r17, %r25
	mulhdu %r5, %r17, %r25
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r18, %r24
	mulhdu %r5, %r18, %r24
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r19, %r23
	mulhdu %r5, %r19, %r23
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r20, %r22
	mulhdu %r5, %r20, %r22
	addc %r29, %r29, %r4
	adde %r30, %r30, %r5
	addze %r31, %r31
	mulld %r4, %r15, %r28
	mulhdu %r5, %r15, %r28
	li %r15, 0
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r27
	mulhdu %r5, %r16, %r27
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r17, %r26
	mulhdu %r5, %r17, %r26
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r18, %r25
	mulhdu %r5, %r18, %r25
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r19, %r24
	mulhdu %r5, %r19, %r24
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r20, %r23
	mulhdu %r5, %r20, %r23
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r21, %r22
	mulhdu %r5, %r21, %r22
	addc %r30, %r30, %r4
	adde %r31, %r31, %r5
	addze %r15, %r15
	mulld %r4, %r16, %r28
	mulhdu %r5, %r16, %r28
	li %r22, 0
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r27
	mulhdu %r5, %r17, %r27
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r18, %r26
	mulhdu %r5, %r18, %r26
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r19, %r25
	mulhdu %r5, %r19, %r25
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r20, %r24
	mulhdu %r5, %r20, %r24
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r21, %r23
	mulhdu %r5, %r21, %r23
	addc %r31, %r31, %r4
	adde %r15, %r15, %r5
	addze %r22, %r22
	mulld %r4, %r17, %r28
	mulhdu %r5, %r17, %r28
	li %r16, 0
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r27
	mulhdu %r5, %r18, %r27
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r19, %r26
	mulhdu %r5, %r19, %r26
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r20, %r25
	mulhdu %r5, %r20, %r25
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r21, %r24
	mulhdu %r5, %r21, %r24
	addc %r15, %r15, %r4
	adde %r22, %r22, %r5
	addze %r16, %r16
	mulld %r4, %r18, %r28
	mulhdu %r5, %r18, %r28
	li %r23, 0
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r27
	mulhdu %r5, %r19, %r27
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r20, %r26
	mulhdu %r5, %r20, %r26
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r21, %r25
	mulhdu %r5, %r21, %r25
	addc %r22, %r22, %r4
	adde %r16, %r16, %r5
	addze %r23, %r23
	mulld %r4, %r19, %r28
	mulhdu %r5, %r19, %r28
	li %r17, 0
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r27
	mulhdu %r5, %r20, %r27
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r21, %r26
	mulhdu %r5, %r21, %r26
	addc %r16, %r16, %r4
	adde %r23, %r23, %r5
	addze %r17, %r17
	mulld %r4, %r20, %r28
	mulhdu %r5, %r20, %r28
	li %r24, 0
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r27
	mulhdu %r5, %r21, %r27
	addc %r23, %r23, %r4
	adde %r17, %r17, %r5
	addze %r24, %r24
	mulld %r4, %r21, %r28
	mulhdu %r5, %r21, %r28
	li %r18, 0
	addc %r17, %r17, %r4
	adde %r24, %r24, %r5
	addze %r18, %r18
	addc %r7, %r7, %r31
	adde %r8, %r8, %r15
	adde %r9, %r9, %r22
	adde %r10, %r10, %r16
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	li %r4, 0
	addze %r4, %r4
	rldicl %r19, %r16, 32, 32
	rldicr %r18, %r23, 32, 31
	add %r19, %r19, %r18
	rldicl %r20, %r23, 32, 32
	rldicr %r18, %r17, 32, 31
	add %r20, %r20, %r18
	rldicl %r21, %r17, 32, 32
	rldicr %r18, %r24, 32, 31
	add %r21, %r21, %r18
	rldicl %r25, %r24, 32, 32
	rldicr %r18, %r31, 32, 31
	add %r25, %r25, %r18
	rldicl %r26, %r31, 32, 32
	rldicr %r18, %r15, 32, 31
	add %r26, %r26, %r18
	rldicl %r27, %r15, 32, 32
	rldicr %r18, %r22, 32, 31
	add %r27, %r27, %r18
	rldicl %r28, %r22, 32, 32
	rldicr %r18, %r16, 32, 31
	add %r28, %r28, %r18
	addc %r7, %r7, %r19
	adde %r8, %r8, %r20
	adde %r9, %r9, %r21
	adde %r10, %r10, %r25
	adde %r11, %r11, %r26
	adde %r29, %r29, %r27
	adde %r30, %r30, %r28
	addze %r4, %r4
	li %r19, 0
	rldicl %r20, %r16, 32, 32
	rldicr %r20, %r20, 32, 31
	addc %r7, %r7, %r19
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r20
	adde %r11, %r11, %r23
	adde %r29, %r29, %r17
	adde %r30, %r30, %r24
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	li %r4, 0
	addze %r4, %r4
	rldicr %r5, %r4, 32, 31
	addc %r7, %r7, %r4
	adde %r8, %r8, %r19
	adde %r9, %r9, %r19
	adde %r10, %r10, %r5
	adde %r11, %r11, %r19
	adde %r29, %r29, %r19
	adde %r30, %r30, %r19
	std %r7, 616(%r6)
	std %r8, 624(%r6)
	std %r9, 632(%r6)
	std %r10, 640(%r6)
	std %r11, 648(%r6)
	std %r29, 656(%r6)
	std %r30, 664(%r6)
	ld %r7, 616(%r6)
	ld %r8, 392(%r6)
	subfc %r7, %r8, %r7
	std %r7, 56(%r6)
	ld %r7, 624(%r6)
	ld %r8, 400(%r6)
	subfe %r7, %r8, %r7
	std %r7, 64(%r6)
	ld %r7, 632(%r6)
	ld %r8, 408(%r6)
	subfe %r7, %r8, %r7
	std %r7, 72(%r6)
	ld %r7, 640(%r6)
	ld %r8, 416(%r6)
	subfe %r7, %r8, %r7
	std %r7, 80(%r6)
	ld %r7, 648(%r6)
	ld %r8, 424(%r6)
	subfe %r7, %r8, %r7
	std %r7, 88(%r6)
	ld %r7, 656(%r6)
	ld %r8, 432(%r6)
	subfe %r7, %r8, %r7
	std %r7, 96(%r6)
	ld %r7, 664(%r6)
	ld %r8, 440(%r6)
	subfe %r7, %r8, %r7
	std %r7, 104(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 56(%r6)
	subfc %r7, %r4, %r7
	std %r7, 56(%r6)
	ld %r7, 64(%r6)
	subfe %r7, %r8, %r7
	std %r7, 64(%r6)
	ld %r7, 72(%r6)
	subfe %r7, %r8, %r7
	std %r7, 72(%r6)
	ld %r7, 80(%r6)
	subfe %r7, %r5, %r7
	std %r7, 80(%r6)
	ld %r7, 88(%r6)
	subfe %r7, %r8, %r7
	std %r7, 88(%r6)
	ld %r7, 96(%r6)
	subfe %r7, %r8, %r7
	std %r7, 96(%r6)
	ld %r7, 104(%r6)
	subfe %r7, %r8, %r7
	std %r7, 104(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 56(%r6)
	subfc %r7, %r4, %r7
	std %r7, 56(%r6)
	ld %r7, 64(%r6)
	subfe %r7, %r8, %r7
	std %r7, 64(%r6)
	ld %r7, 72(%r6)
	subfe %r7, %r8, %r7
	std %r7, 72(%r6)
	ld %r7, 80(%r6)
	subfe %r7, %r5, %r7
	std %r7, 80(%r6)
	ld %r7, 88(%r6)
	subfe %r7, %r8, %r7
	std %r7, 88(%r6)
	ld %r7, 96(%r6)
	subfe %r7, %r8, %r7
	std %r7, 96(%r6)
	ld %r7, 104(%r6)
	subfe %r7, %r8, %r7
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
	li %r10, 0
	lwz %r7, 0(%r3)
	or %r10, %r10, %r7
	lwz %r7, 4(%r3)
	or %r10, %r10, %r7
	lwz %r7, 8(%r3)
	or %r10, %r10, %r7
	lwz %r7, 12(%r3)
	or %r10, %r10, %r7
	lwz %r7, 16(%r3)
	or %r10, %r10, %r7
	lwz %r7, 20(%r3)
	or %r10, %r10, %r7
	lwz %r7, 24(%r3)
	or %r10, %r10, %r7
	lwz %r7, 28(%r3)
	or %r10, %r10, %r7
	lwz %r7, 32(%r3)
	or %r10, %r10, %r7
	lwz %r7, 36(%r3)
	or %r10, %r10, %r7
	lwz %r7, 40(%r3)
	or %r10, %r10, %r7
	lwz %r7, 44(%r3)
	or %r10, %r10, %r7
	lwz %r7, 48(%r3)
	or %r10, %r10, %r7
	lwz %r7, 52(%r3)
	or %r10, %r10, %r7
	ld %r9, 3520(%r6)
	or %r9, %r9, %r10
	std %r9, 3520(%r6)
	li %r11, 0
	lwz %r5, 672(%r6)
	lwz %r7, 672(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 56(%r6)
	lwz %r5, 676(%r6)
	lwz %r7, 676(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 60(%r6)
	lwz %r5, 680(%r6)
	lwz %r7, 680(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 64(%r6)
	lwz %r5, 684(%r6)
	lwz %r7, 684(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 68(%r6)
	lwz %r5, 688(%r6)
	lwz %r7, 688(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 72(%r6)
	lwz %r5, 692(%r6)
	lwz %r7, 692(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 76(%r6)
	lwz %r5, 696(%r6)
	lwz %r7, 696(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 80(%r6)
	lwz %r5, 700(%r6)
	lwz %r7, 700(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 84(%r6)
	lwz %r5, 704(%r6)
	lwz %r7, 704(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 88(%r6)
	lwz %r5, 708(%r6)
	lwz %r7, 708(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 92(%r6)
	lwz %r5, 712(%r6)
	lwz %r7, 712(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 96(%r6)
	lwz %r5, 716(%r6)
	lwz %r7, 716(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 100(%r6)
	lwz %r5, 720(%r6)
	lwz %r7, 720(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 104(%r6)
	lwz %r5, 724(%r6)
	lwz %r7, 724(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 108(%r6)
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
	li %r10, 0
	lwz %r7, 0(%r3)
	or %r10, %r10, %r7
	lwz %r7, 4(%r3)
	or %r10, %r10, %r7
	lwz %r7, 8(%r3)
	or %r10, %r10, %r7
	lwz %r7, 12(%r3)
	or %r10, %r10, %r7
	lwz %r7, 16(%r3)
	or %r10, %r10, %r7
	lwz %r7, 20(%r3)
	or %r10, %r10, %r7
	lwz %r7, 24(%r3)
	or %r10, %r10, %r7
	lwz %r7, 28(%r3)
	or %r10, %r10, %r7
	lwz %r7, 32(%r3)
	or %r10, %r10, %r7
	lwz %r7, 36(%r3)
	or %r10, %r10, %r7
	lwz %r7, 40(%r3)
	or %r10, %r10, %r7
	lwz %r7, 44(%r3)
	or %r10, %r10, %r7
	lwz %r7, 48(%r3)
	or %r10, %r10, %r7
	lwz %r7, 52(%r3)
	or %r10, %r10, %r7
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	lbz %r7, 3528(%r6)
	and %r8, %r10, %r7
	ld %r9, 3520(%r6)
	or %r9, %r9, %r8
	std %r9, 3520(%r6)
	ld %r7, 672(%r6)
	ld %r8, 672(%r6)
	subfc %r7, %r8, %r7
	std %r7, 616(%r6)
	ld %r7, 680(%r6)
	ld %r8, 680(%r6)
	subfe %r7, %r8, %r7
	std %r7, 624(%r6)
	ld %r7, 688(%r6)
	ld %r8, 688(%r6)
	subfe %r7, %r8, %r7
	std %r7, 632(%r6)
	ld %r7, 696(%r6)
	ld %r8, 696(%r6)
	subfe %r7, %r8, %r7
	std %r7, 640(%r6)
	ld %r7, 704(%r6)
	ld %r8, 704(%r6)
	subfe %r7, %r8, %r7
	std %r7, 648(%r6)
	ld %r7, 712(%r6)
	ld %r8, 712(%r6)
	subfe %r7, %r8, %r7
	std %r7, 656(%r6)
	ld %r7, 720(%r6)
	ld %r8, 720(%r6)
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
	ld %r7, 616(%r6)
	ld %r8, 672(%r6)
	subfc %r7, %r8, %r7
	std %r7, 728(%r6)
	ld %r7, 624(%r6)
	ld %r8, 680(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 632(%r6)
	ld %r8, 688(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 640(%r6)
	ld %r8, 696(%r6)
	subfe %r7, %r8, %r7
	std %r7, 752(%r6)
	ld %r7, 648(%r6)
	ld %r8, 704(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 656(%r6)
	ld %r8, 712(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 664(%r6)
	ld %r8, 720(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 728(%r6)
	subfc %r7, %r4, %r7
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	subfe %r7, %r5, %r7
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
	li %r8, 0
	subfe %r4, %r8, %r8
	subf %r4, %r4, %r8
	rldicr %r5, %r4, 32, 31
	ld %r7, 728(%r6)
	subfc %r7, %r4, %r7
	std %r7, 728(%r6)
	ld %r7, 736(%r6)
	subfe %r7, %r8, %r7
	std %r7, 736(%r6)
	ld %r7, 744(%r6)
	subfe %r7, %r8, %r7
	std %r7, 744(%r6)
	ld %r7, 752(%r6)
	subfe %r7, %r5, %r7
	std %r7, 752(%r6)
	ld %r7, 760(%r6)
	subfe %r7, %r8, %r7
	std %r7, 760(%r6)
	ld %r7, 768(%r6)
	subfe %r7, %r8, %r7
	std %r7, 768(%r6)
	ld %r7, 776(%r6)
	subfe %r7, %r8, %r7
	std %r7, 776(%r6)
	lbz %r8, 0(%r3)
	li %r9, 1
	and %r8, %r8, %r9
	lbz %r7, 3528(%r6)
	xor %r8, %r8, %r7
	li %r11, 0
	subf %r11, %r8, %r11
	lwz %r5, 728(%r6)
	lwz %r7, 672(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1128(%r6)
	lwz %r5, 732(%r6)
	lwz %r7, 676(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1132(%r6)
	lwz %r5, 736(%r6)
	lwz %r7, 680(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1136(%r6)
	lwz %r5, 740(%r6)
	lwz %r7, 684(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1140(%r6)
	lwz %r5, 744(%r6)
	lwz %r7, 688(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1144(%r6)
	lwz %r5, 748(%r6)
	lwz %r7, 692(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1148(%r6)
	lwz %r5, 752(%r6)
	lwz %r7, 696(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1152(%r6)
	lwz %r5, 756(%r6)
	lwz %r7, 700(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1156(%r6)
	lwz %r5, 760(%r6)
	lwz %r7, 704(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1160(%r6)
	lwz %r5, 764(%r6)
	lwz %r7, 708(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1164(%r6)
	lwz %r5, 768(%r6)
	lwz %r7, 712(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1168(%r6)
	lwz %r5, 772(%r6)
	lwz %r7, 716(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1172(%r6)
	lwz %r5, 776(%r6)
	lwz %r7, 720(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1176(%r6)
	lwz %r5, 780(%r6)
	lwz %r7, 724(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1180(%r6)
	lwz %r5, 168(%r6)
	lwz %r7, 168(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1184(%r6)
	lwz %r5, 172(%r6)
	lwz %r7, 172(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1188(%r6)
	lwz %r5, 176(%r6)
	lwz %r7, 176(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1192(%r6)
	lwz %r5, 180(%r6)
	lwz %r7, 180(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1196(%r6)
	lwz %r5, 184(%r6)
	lwz %r7, 184(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1200(%r6)
	lwz %r5, 188(%r6)
	lwz %r7, 188(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1204(%r6)
	lwz %r5, 192(%r6)
	lwz %r7, 192(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1208(%r6)
	lwz %r5, 196(%r6)
	lwz %r7, 196(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1212(%r6)
	lwz %r5, 200(%r6)
	lwz %r7, 200(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1216(%r6)
	lwz %r5, 204(%r6)
	lwz %r7, 204(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1220(%r6)
	lwz %r5, 208(%r6)
	lwz %r7, 208(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1224(%r6)
	lwz %r5, 212(%r6)
	lwz %r7, 212(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1228(%r6)
	lwz %r5, 216(%r6)
	lwz %r7, 216(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1232(%r6)
	lwz %r5, 220(%r6)
	lwz %r7, 220(%r6)
	xor %r7, %r7, %r5
	and %r7, %r7, %r11
	xor %r5, %r5, %r7
	stw %r5, 1236(%r6)
	blr
