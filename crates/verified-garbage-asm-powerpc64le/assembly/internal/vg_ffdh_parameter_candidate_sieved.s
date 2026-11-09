// The functions of `src/internal/vg_ffdh_parameter_candidate_sieved.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ffdh_parameter_candidate_sieved:
	addi %r11, %r1, 96
	ld %r12, 0(%r11)
	rldicr %r11, %r12, 3, 60
	add %r11, %r10, %r11
	addi %r11, %r11, -160
	mflr %r0
	std %r0, 144(%r11)
	std %r14, 0(%r11)
	std %r15, 8(%r11)
	std %r16, 16(%r11)
	std %r17, 24(%r11)
	std %r18, 32(%r11)
	std %r19, 40(%r11)
	std %r20, 48(%r11)
	std %r21, 56(%r11)
	std %r22, 64(%r11)
	std %r23, 72(%r11)
	std %r24, 80(%r11)
	std %r25, 88(%r11)
	std %r26, 96(%r11)
	std %r27, 104(%r11)
	std %r28, 112(%r11)
	std %r29, 120(%r11)
	std %r30, 128(%r11)
	std %r31, 136(%r11)
	addi %r31, %r10, 0
	std %r12, 0(%r31)
	std %r3, 16(%r31)
	std %r4, 24(%r31)
	std %r4, 152(%r31)
	std %r5, 32(%r31)
	std %r6, 40(%r31)
	rlwinm %r7, %r7, 0, 0, 31
	std %r7, 128(%r31)
	std %r8, 136(%r31)
	std %r9, 144(%r31)
	ld %r4, 16(%r31)
	ld %r5, 24(%r31)
	li %r0, 0
20:
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	ld %r3, 144(%r31)
	ld %r4, 24(%r31)
	subf %r5, %r4, %r3
	rldicl %r5, %r5, 1, 63
	li %r0, 1
	xor %r5, %r5, %r0
	rldicl %r0, %r3, 1, 63
	or %r5, %r5, %r0
	cmpldi %cr0, %r5, 0
	beq %cr0, 21f
	ld %r3, 40(%r31)
	std %r3, 248(%r31)
	addi %r4, %r3, 7
	rldicl %r4, %r4, 61, 3
	std %r4, 216(%r31)
	addi %r4, %r3, 63
	rldicl %r4, %r4, 58, 6
	std %r4, 48(%r31)
	rldicr %r11, %r4, 1, 62
	rldicr %r29, %r4, 3, 60
	addi %r29, %r29, 16
	std %r29, 224(%r31)
	addi %r10, %r31, 256
	addi %r5, %r10, 0
	std %r5, 64(%r31)
	add %r5, %r5, %r29
	std %r5, 72(%r31)
	add %r5, %r5, %r29
	std %r5, 80(%r31)
	add %r5, %r5, %r29
	std %r5, 88(%r31)
	add %r5, %r5, %r29
	std %r5, 96(%r31)
	add %r5, %r5, %r29
	std %r5, 104(%r31)
	add %r5, %r5, %r29
	std %r5, 112(%r31)
	add %r5, %r5, %r29
	std %r5, 120(%r31)
	add %r5, %r5, %r29
	addi %r5, %r3, -2049
	rldicl %r5, %r5, 1, 63
	rldicr %r5, %r5, 6, 57
	li %r6, 128
	subf %r5, %r5, %r6
	std %r5, 168(%r31)
	ld %r3, 248(%r31)
	ld %r4, 48(%r31)
	rldicr %r4, %r4, 6, 57
	subf %r3, %r4, %r3
	addi %r3, %r3, 64
	li %r5, 0
23:
	add %r5, %r5, %r5
	addi %r5, %r5, 1
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 23b
	std %r5, 192(%r31)
	ld %r12, 136(%r31)
	ld %r6, 24(%r31)
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
24:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 24b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
25:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 25b
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	addi %r5, %r5, -8
	ld %r4, 192(%r31)
	ld %r6, 0(%r5)
	and %r6, %r6, %r4
	rldicl %r4, %r4, 63, 1
	addi %r4, %r4, 1
	or %r6, %r6, %r4
	std %r6, 0(%r5)
	ld %r6, 0(%r10)
	li %r4, 1
	or %r6, %r6, %r4
	std %r6, 0(%r10)
	ld %r3, 128(%r31)
	addi %r3, %r3, -2
	cmpldi %cr0, %r3, 0
	beq %cr0, 26f
	addi %r5, %r10, 0
	addi %r4, %r11, 0
	li %r3, 0
28:
	lwz %r0, 0(%r5)
	add %r3, %r3, %r0
	addi %r5, %r5, 4
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 28b
	lwz %r4, 0(%r10)
	lis %r6, -13108
	ori %r6, %r6, 52428
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 52428
	ori %r6, %r6, 52429
	mulhdu %r6, %r3, %r6
	rldicl %r6, %r6, 62, 2
	li %r7, 5
	mulld %r6, %r6, %r7
	subf %r3, %r6, %r3
	li %r6, 1
	and %r4, %r4, %r6
	xor %r4, %r4, %r6
	or %r3, %r3, %r6
	li %r6, 3
	xor %r3, %r3, %r6
	or %r3, %r3, %r4
	std %r3, 200(%r31)
	b 27f
26:
	addi %r5, %r10, 0
	addi %r4, %r11, 0
	li %r3, 0
29:
	lwz %r0, 0(%r5)
	add %r3, %r3, %r0
	addi %r5, %r5, 4
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 29b
	lwz %r4, 0(%r10)
	lis %r6, -21846
	ori %r6, %r6, 43690
	rldicr %r6, %r6, 32, 31
	oris %r6, %r6, 43690
	ori %r6, %r6, 43691
	mulhdu %r6, %r3, %r6
	rldicl %r6, %r6, 63, 1
	li %r7, 3
	mulld %r6, %r6, %r7
	subf %r3, %r6, %r3
	li %r6, 7
	and %r4, %r4, %r6
	li %r6, 3
	xor %r4, %r4, %r6
	li %r6, 2
	xor %r3, %r3, %r6
	or %r3, %r3, %r4
	std %r3, 200(%r31)
27:
	ld %r5, 200(%r31)
	cmpldi %cr0, %r5, 0
	beq %cr0, 210f
	ld %r4, 32(%r31)
	ld %r5, 152(%r31)
	std %r5, 0(%r4)
	li %r3, 2
	b 211f
210:
	bcl 20, 31, 2f
2:
	mflr %r23
	addis %r23, %r23, ({VG_RSA_KEYGEN_TRIAL32}
	addi %r23, %r23, ({VG_RSA_KEYGEN_TRIAL32}
	li %r24, 16
212:
	lwz %r0, 0(%r23)
	lwz %r9, 8(%r23)
	mulld %r0, %r0, %r9
	lwz %r9, 16(%r23)
	mulld %r0, %r0, %r9
	lwz %r9, 24(%r23)
	mulld %r0, %r0, %r9
	or %r12, %r0, %r0
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	li %r3, 0
	subf %r12, %r12, %r3
	or %r8, %r0, %r0
	addi %r5, %r10, 0
	rldicl %r6, %r11, 63, 1
	li %r7, 0
	li %r14, 0
213:
	ld %r0, 0(%r5)
	addc %r0, %r7, %r0
	addze %r9, %r14
	mulld %r3, %r0, %r12
	mulld %r4, %r3, %r8
	mulhdu %r7, %r3, %r8
	addc %r4, %r4, %r0
	adde %r7, %r7, %r9
	addi %r5, %r5, 8
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 213b
	std %r7, 208(%r31)
	li %r25, 0
	ld %r8, 0(%r23)
	rldicl %r9, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	rldicl %r8, %r8, 32, 32
	li %r3, 0
	addi %r5, %r31, 208
	li %r4, 2
214:
	lwz %r0, 0(%r5)
	add %r0, %r0, %r3
	mulld %r6, %r0, %r9
	rldicr %r6, %r6, 32, 31
	rldicl %r6, %r6, 32, 32
	mulld %r6, %r6, %r8
	add %r6, %r6, %r0
	rldicl %r3, %r6, 32, 32
	addi %r5, %r5, 4
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 214b
	addi %r6, %r3, -1
	rldicl %r6, %r6, 1, 63
	xor %r7, %r3, %r8
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	or %r6, %r6, %r7
	or %r25, %r25, %r6
	ld %r8, 8(%r23)
	rldicl %r9, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	rldicl %r8, %r8, 32, 32
	li %r3, 0
	addi %r5, %r31, 208
	li %r4, 2
215:
	lwz %r0, 0(%r5)
	add %r0, %r0, %r3
	mulld %r6, %r0, %r9
	rldicr %r6, %r6, 32, 31
	rldicl %r6, %r6, 32, 32
	mulld %r6, %r6, %r8
	add %r6, %r6, %r0
	rldicl %r3, %r6, 32, 32
	addi %r5, %r5, 4
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 215b
	addi %r6, %r3, -1
	rldicl %r6, %r6, 1, 63
	xor %r7, %r3, %r8
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	or %r6, %r6, %r7
	or %r25, %r25, %r6
	ld %r8, 16(%r23)
	rldicl %r9, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	rldicl %r8, %r8, 32, 32
	li %r3, 0
	addi %r5, %r31, 208
	li %r4, 2
216:
	lwz %r0, 0(%r5)
	add %r0, %r0, %r3
	mulld %r6, %r0, %r9
	rldicr %r6, %r6, 32, 31
	rldicl %r6, %r6, 32, 32
	mulld %r6, %r6, %r8
	add %r6, %r6, %r0
	rldicl %r3, %r6, 32, 32
	addi %r5, %r5, 4
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 216b
	addi %r6, %r3, -1
	rldicl %r6, %r6, 1, 63
	xor %r7, %r3, %r8
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	or %r6, %r6, %r7
	or %r25, %r25, %r6
	ld %r8, 24(%r23)
	rldicl %r9, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	rldicl %r8, %r8, 32, 32
	li %r3, 0
	addi %r5, %r31, 208
	li %r4, 2
217:
	lwz %r0, 0(%r5)
	add %r0, %r0, %r3
	mulld %r6, %r0, %r9
	rldicr %r6, %r6, 32, 31
	rldicl %r6, %r6, 32, 32
	mulld %r6, %r6, %r8
	add %r6, %r6, %r0
	rldicl %r3, %r6, 32, 32
	addi %r5, %r5, 4
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 217b
	addi %r6, %r3, -1
	rldicl %r6, %r6, 1, 63
	xor %r7, %r3, %r8
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	or %r6, %r6, %r7
	or %r25, %r25, %r6
	or %r22, %r25, %r25
	addi %r23, %r23, 32
	addi %r24, %r24, -4
	addi %r6, %r22, -1
	and %r24, %r24, %r6
	cmpldi %cr0, %r24, 0
	bne %cr0, 212b
	ld %r5, 200(%r31)
	or %r5, %r5, %r22
	std %r5, 200(%r31)
	ld %r5, 200(%r31)
	cmpldi %cr0, %r5, 0
	beq %cr0, 218f
	ld %r4, 32(%r31)
	ld %r5, 152(%r31)
	std %r5, 0(%r4)
	li %r3, 2
	b 219f
218:
	addi %r5, %r10, 0
	rldicl %r6, %r11, 63, 1
	addi %r6, %r6, -1
220:
	ld %r3, 0(%r5)
	ld %r4, 8(%r5)
	rldicl %r3, %r3, 63, 1
	rldicr %r4, %r4, 63, 0
	or %r3, %r3, %r4
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 220b
	ld %r3, 0(%r5)
	rldicl %r3, %r3, 63, 1
	std %r3, 0(%r5)
	ld %r5, 200(%r31)
	ld %r3, 0(%r10)
	li %r4, 1
	and %r3, %r3, %r4
	xor %r3, %r3, %r4
	or %r5, %r5, %r3
	std %r5, 200(%r31)
	bcl 20, 31, 2f
2:
	mflr %r23
	addis %r23, %r23, ({VG_RSA_KEYGEN_TRIAL32}
	addi %r23, %r23, ({VG_RSA_KEYGEN_TRIAL32}
	ld %r3, 40(%r31)
	addi %r3, %r3, -1025
	rldicl %r3, %r3, 1, 63
	rldicr %r3, %r3, 9, 54
	li %r4, 1024
	subf %r24, %r3, %r4
221:
	lwz %r0, 0(%r23)
	lwz %r9, 8(%r23)
	mulld %r0, %r0, %r9
	lwz %r9, 16(%r23)
	mulld %r0, %r0, %r9
	lwz %r9, 24(%r23)
	mulld %r0, %r0, %r9
	or %r12, %r0, %r0
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	li %r3, 0
	subf %r12, %r12, %r3
	or %r8, %r0, %r0
	addi %r5, %r10, 0
	rldicl %r6, %r11, 63, 1
	li %r7, 0
	li %r14, 0
222:
	ld %r0, 0(%r5)
	addc %r0, %r7, %r0
	addze %r9, %r14
	mulld %r3, %r0, %r12
	mulld %r4, %r3, %r8
	mulhdu %r7, %r3, %r8
	addc %r4, %r4, %r0
	adde %r7, %r7, %r9
	addi %r5, %r5, 8
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 222b
	std %r7, 208(%r31)
	li %r25, 0
	ld %r8, 0(%r23)
	rldicl %r9, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	rldicl %r8, %r8, 32, 32
	li %r3, 0
	addi %r5, %r31, 208
	li %r4, 2
223:
	lwz %r0, 0(%r5)
	add %r0, %r0, %r3
	mulld %r6, %r0, %r9
	rldicr %r6, %r6, 32, 31
	rldicl %r6, %r6, 32, 32
	mulld %r6, %r6, %r8
	add %r6, %r6, %r0
	rldicl %r3, %r6, 32, 32
	addi %r5, %r5, 4
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 223b
	addi %r6, %r3, -1
	rldicl %r6, %r6, 1, 63
	xor %r7, %r3, %r8
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	or %r6, %r6, %r7
	or %r25, %r25, %r6
	ld %r8, 8(%r23)
	rldicl %r9, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	rldicl %r8, %r8, 32, 32
	li %r3, 0
	addi %r5, %r31, 208
	li %r4, 2
224:
	lwz %r0, 0(%r5)
	add %r0, %r0, %r3
	mulld %r6, %r0, %r9
	rldicr %r6, %r6, 32, 31
	rldicl %r6, %r6, 32, 32
	mulld %r6, %r6, %r8
	add %r6, %r6, %r0
	rldicl %r3, %r6, 32, 32
	addi %r5, %r5, 4
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 224b
	addi %r6, %r3, -1
	rldicl %r6, %r6, 1, 63
	xor %r7, %r3, %r8
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	or %r6, %r6, %r7
	or %r25, %r25, %r6
	ld %r8, 16(%r23)
	rldicl %r9, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	rldicl %r8, %r8, 32, 32
	li %r3, 0
	addi %r5, %r31, 208
	li %r4, 2
225:
	lwz %r0, 0(%r5)
	add %r0, %r0, %r3
	mulld %r6, %r0, %r9
	rldicr %r6, %r6, 32, 31
	rldicl %r6, %r6, 32, 32
	mulld %r6, %r6, %r8
	add %r6, %r6, %r0
	rldicl %r3, %r6, 32, 32
	addi %r5, %r5, 4
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 225b
	addi %r6, %r3, -1
	rldicl %r6, %r6, 1, 63
	xor %r7, %r3, %r8
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	or %r6, %r6, %r7
	or %r25, %r25, %r6
	ld %r8, 24(%r23)
	rldicl %r9, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	rldicl %r8, %r8, 32, 32
	li %r3, 0
	addi %r5, %r31, 208
	li %r4, 2
226:
	lwz %r0, 0(%r5)
	add %r0, %r0, %r3
	mulld %r6, %r0, %r9
	rldicr %r6, %r6, 32, 31
	rldicl %r6, %r6, 32, 32
	mulld %r6, %r6, %r8
	add %r6, %r6, %r0
	rldicl %r3, %r6, 32, 32
	addi %r5, %r5, 4
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 226b
	addi %r6, %r3, -1
	rldicl %r6, %r6, 1, 63
	xor %r7, %r3, %r8
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	or %r6, %r6, %r7
	or %r25, %r25, %r6
	or %r22, %r25, %r25
	addi %r23, %r23, 32
	addi %r24, %r24, -4
	addi %r6, %r22, -1
	and %r24, %r24, %r6
	cmpldi %cr0, %r24, 0
	bne %cr0, 221b
	ld %r5, 200(%r31)
	or %r5, %r5, %r22
	std %r5, 200(%r31)
	ld %r5, 200(%r31)
	cmpldi %cr0, %r5, 0
	beq %cr0, 227f
	ld %r4, 32(%r31)
	ld %r5, 152(%r31)
	std %r5, 0(%r4)
	li %r3, 2
	b 228f
227:
	ld %r12, 136(%r31)
	ld %r6, 24(%r31)
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
229:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 229b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
230:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 230b
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	addi %r5, %r5, -8
	ld %r4, 192(%r31)
	ld %r6, 0(%r5)
	and %r6, %r6, %r4
	rldicl %r4, %r4, 63, 1
	addi %r4, %r4, 1
	or %r6, %r6, %r4
	std %r6, 0(%r5)
	ld %r6, 0(%r10)
	li %r4, 1
	or %r6, %r6, %r4
	std %r6, 0(%r10)
	bcl 20, 31, 2f
2:
	mflr %r23
	addis %r23, %r23, ({VG_RSA_KEYGEN_TRIAL32}
	addi %r23, %r23, ({VG_RSA_KEYGEN_TRIAL32}
	ld %r3, 40(%r31)
	addi %r3, %r3, -1025
	rldicl %r3, %r3, 1, 63
	rldicr %r3, %r3, 9, 54
	li %r4, 1024
	subf %r24, %r3, %r4
231:
	lwz %r0, 0(%r23)
	lwz %r9, 8(%r23)
	mulld %r0, %r0, %r9
	lwz %r9, 16(%r23)
	mulld %r0, %r0, %r9
	lwz %r9, 24(%r23)
	mulld %r0, %r0, %r9
	or %r12, %r0, %r0
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	li %r3, 0
	subf %r12, %r12, %r3
	or %r8, %r0, %r0
	addi %r5, %r10, 0
	rldicl %r6, %r11, 63, 1
	li %r7, 0
	li %r14, 0
232:
	ld %r0, 0(%r5)
	addc %r0, %r7, %r0
	addze %r9, %r14
	mulld %r3, %r0, %r12
	mulld %r4, %r3, %r8
	mulhdu %r7, %r3, %r8
	addc %r4, %r4, %r0
	adde %r7, %r7, %r9
	addi %r5, %r5, 8
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 232b
	std %r7, 208(%r31)
	li %r25, 0
	ld %r8, 0(%r23)
	rldicl %r9, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	rldicl %r8, %r8, 32, 32
	li %r3, 0
	addi %r5, %r31, 208
	li %r4, 2
233:
	lwz %r0, 0(%r5)
	add %r0, %r0, %r3
	mulld %r6, %r0, %r9
	rldicr %r6, %r6, 32, 31
	rldicl %r6, %r6, 32, 32
	mulld %r6, %r6, %r8
	add %r6, %r6, %r0
	rldicl %r3, %r6, 32, 32
	addi %r5, %r5, 4
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 233b
	addi %r6, %r3, -1
	rldicl %r6, %r6, 1, 63
	xor %r7, %r3, %r8
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	or %r6, %r6, %r7
	or %r25, %r25, %r6
	ld %r8, 8(%r23)
	rldicl %r9, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	rldicl %r8, %r8, 32, 32
	li %r3, 0
	addi %r5, %r31, 208
	li %r4, 2
234:
	lwz %r0, 0(%r5)
	add %r0, %r0, %r3
	mulld %r6, %r0, %r9
	rldicr %r6, %r6, 32, 31
	rldicl %r6, %r6, 32, 32
	mulld %r6, %r6, %r8
	add %r6, %r6, %r0
	rldicl %r3, %r6, 32, 32
	addi %r5, %r5, 4
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 234b
	addi %r6, %r3, -1
	rldicl %r6, %r6, 1, 63
	xor %r7, %r3, %r8
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	or %r6, %r6, %r7
	or %r25, %r25, %r6
	ld %r8, 16(%r23)
	rldicl %r9, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	rldicl %r8, %r8, 32, 32
	li %r3, 0
	addi %r5, %r31, 208
	li %r4, 2
235:
	lwz %r0, 0(%r5)
	add %r0, %r0, %r3
	mulld %r6, %r0, %r9
	rldicr %r6, %r6, 32, 31
	rldicl %r6, %r6, 32, 32
	mulld %r6, %r6, %r8
	add %r6, %r6, %r0
	rldicl %r3, %r6, 32, 32
	addi %r5, %r5, 4
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 235b
	addi %r6, %r3, -1
	rldicl %r6, %r6, 1, 63
	xor %r7, %r3, %r8
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	or %r6, %r6, %r7
	or %r25, %r25, %r6
	ld %r8, 24(%r23)
	rldicl %r9, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	rldicl %r8, %r8, 32, 32
	li %r3, 0
	addi %r5, %r31, 208
	li %r4, 2
236:
	lwz %r0, 0(%r5)
	add %r0, %r0, %r3
	mulld %r6, %r0, %r9
	rldicr %r6, %r6, 32, 31
	rldicl %r6, %r6, 32, 32
	mulld %r6, %r6, %r8
	add %r6, %r6, %r0
	rldicl %r3, %r6, 32, 32
	addi %r5, %r5, 4
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 236b
	addi %r6, %r3, -1
	rldicl %r6, %r6, 1, 63
	xor %r7, %r3, %r8
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	or %r6, %r6, %r7
	or %r25, %r25, %r6
	or %r22, %r25, %r25
	addi %r23, %r23, 32
	addi %r24, %r24, -4
	addi %r6, %r22, -1
	and %r24, %r24, %r6
	cmpldi %cr0, %r24, 0
	bne %cr0, 231b
	ld %r5, 200(%r31)
	or %r5, %r5, %r22
	std %r5, 200(%r31)
	ld %r5, 200(%r31)
	cmpldi %cr0, %r5, 0
	beq %cr0, 237f
	ld %r4, 32(%r31)
	ld %r5, 152(%r31)
	std %r5, 0(%r4)
	li %r3, 2
	b 238f
237:
	ld %r3, 40(%r31)
	std %r3, 248(%r31)
	addi %r4, %r3, 7
	rldicl %r4, %r4, 61, 3
	std %r4, 216(%r31)
	addi %r4, %r3, 63
	rldicl %r4, %r4, 58, 6
	std %r4, 48(%r31)
	rldicr %r11, %r4, 1, 62
	rldicr %r29, %r4, 3, 60
	addi %r29, %r29, 16
	std %r29, 224(%r31)
	addi %r10, %r31, 256
	addi %r5, %r10, 0
	std %r5, 64(%r31)
	add %r5, %r5, %r29
	std %r5, 72(%r31)
	add %r5, %r5, %r29
	std %r5, 80(%r31)
	add %r5, %r5, %r29
	std %r5, 88(%r31)
	add %r5, %r5, %r29
	std %r5, 96(%r31)
	add %r5, %r5, %r29
	std %r5, 104(%r31)
	add %r5, %r5, %r29
	std %r5, 112(%r31)
	add %r5, %r5, %r29
	std %r5, 120(%r31)
	add %r5, %r5, %r29
	addi %r5, %r3, -2049
	rldicl %r5, %r5, 1, 63
	rldicr %r5, %r5, 6, 57
	li %r6, 128
	subf %r5, %r5, %r6
	std %r5, 168(%r31)
	ld %r3, 248(%r31)
	ld %r4, 48(%r31)
	rldicr %r4, %r4, 6, 57
	subf %r3, %r4, %r3
	addi %r3, %r3, 64
	li %r5, 0
239:
	add %r5, %r5, %r5
	addi %r5, %r5, 1
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 239b
	std %r5, 192(%r31)
	ld %r12, 136(%r31)
	ld %r6, 24(%r31)
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
240:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 240b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
241:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 241b
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	addi %r5, %r5, -8
	ld %r4, 192(%r31)
	ld %r6, 0(%r5)
	and %r6, %r6, %r4
	rldicl %r4, %r4, 63, 1
	addi %r4, %r4, 1
	or %r6, %r6, %r4
	std %r6, 0(%r5)
	ld %r6, 0(%r10)
	li %r4, 1
	or %r6, %r6, %r4
	std %r6, 0(%r10)
	li %r3, 1
	std %r3, 168(%r31)
	ld %r0, 0(%r10)
	ld %r12, 0(%r10)
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	li %r3, 0
	subf %r3, %r12, %r3
	std %r3, 56(%r31)
	rldicr %r12, %r3, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r5, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
242:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 242b
	li %r0, 1
	stw %r0, 0(%r5)
	rldicr %r4, %r11, 6, 57
243:
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	addi %r17, %r11, 0
	li %r20, 0
244:
	lwz %r0, 0(%r15)
	add %r0, %r0, %r0
	add %r0, %r0, %r20
	stw %r0, 0(%r14)
	rldicl %r20, %r0, 32, 32
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 244b
	stw %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
245:
	lwz %r0, 0(%r14)
	lwz %r3, 0(%r16)
	subf %r0, %r3, %r0
	subf %r0, %r20, %r0
	stw %r0, 0(%r15)
	rldicl %r20, %r0, 1, 63
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 245b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	addi %r17, %r11, 0
246:
	lwz %r0, 0(%r15)
	lwz %r3, 0(%r14)
	xor %r3, %r3, %r0
	and %r3, %r3, %r20
	xor %r3, %r3, %r0
	stw %r3, 0(%r16)
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 246b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 243b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
247:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 247b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	li %r0, 1
	stw %r0, 0(%r14)
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r6, %r10, 0
	add %r6, %r6, %r29
	addi %r7, %r10, 0
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r4, %r11, 0
	ld %r3, 0(%r10)
	mulld %r22, %r3, %r12
	addi %r22, %r22, 2
	mulld %r22, %r22, %r12
	rldicr %r14, %r11, 2, 61
	add %r14, %r14, %r8
	std %r22, 8(%r14)
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r3, 0
248:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 248b
249:
	ld %r17, 0(%r6)
	addi %r6, %r6, 8
	ld %r19, 0(%r7)
	ld %r20, 0(%r8)
	mulld %r18, %r17, %r19
	mulhdu %r19, %r17, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r3, 0(%r10)
	mulld %r0, %r20, %r22
	mulld %r22, %r0, %r3
	mulhdu %r19, %r0, %r3
	addc %r22, %r22, %r20
	addze %r22, %r19
	addi %r14, %r8, 0
	addi %r15, %r7, 0
	addi %r3, %r10, 0
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicr %r16, %r16, 62, 1
	rldicl %r16, %r16, 2, 62
	cmpldi %cr0, %r16, 0
	beq %cr0, 250f
252:
	ld %r19, 8(%r14)
	ld %r20, 8(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 8(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r3, %r3, 8
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 252b
	b 251f
250:
251:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 253f
255:
	ld %r19, 8(%r14)
	ld %r20, 8(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 8(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 0(%r14)
	ld %r19, 16(%r14)
	ld %r20, 16(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 16(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 8(%r14)
	ld %r19, 24(%r14)
	ld %r20, 24(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 24(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 16(%r14)
	ld %r19, 32(%r14)
	ld %r20, 32(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 32(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r3, %r3, 32
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 255b
	b 254f
253:
254:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	li %r19, 0
	addze %r19, %r19
	addc %r18, %r18, %r22
	addze %r19, %r19
	std %r18, 0(%r14)
	std %r19, 8(%r14)
	ld %r22, 16(%r14)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 249b
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
256:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 256b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
257:
	ld %r0, 0(%r15)
	ld %r3, 0(%r14)
	xor %r3, %r3, %r0
	and %r3, %r3, %r20
	xor %r3, %r3, %r0
	std %r3, 0(%r16)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 257b
	addi %r8, %r10, 0
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
258:
	lwz %r0, 0(%r14)
	lwz %r3, 0(%r16)
	subf %r0, %r3, %r0
	subf %r0, %r20, %r0
	stw %r0, 0(%r15)
	rldicl %r20, %r0, 1, 63
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 258b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r31, 256
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
259:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 259b
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r6, 0
	li %r4, 1
260:
	ld %r7, 0(%r14)
	xor %r7, %r7, %r4
	li %r4, 0
	addi %r3, %r6, 0
	rldicl %r5, %r3, 63, 1
	li %r0, 1
	and %r0, %r3, %r0
	or %r5, %r5, %r0
	addi %r5, %r5, -1
	rldicl %r5, %r5, 1, 63
	li %r0, 0
	subf %r5, %r5, %r0
	and %r7, %r7, %r5
	or %r6, %r6, %r7
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 260b
	li %r7, 0
	subf %r7, %r6, %r7
	and %r6, %r6, %r7
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicr %r7, %r11, 2, 61
	add %r14, %r14, %r7
	std %r6, 0(%r14)
	li %r9, 0
	addi %r9, %r9, -1
	addi %r15, %r10, 0
	addi %r16, %r10, 0
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	ld %r5, 0(%r15)
	addi %r15, %r15, 8
	rldicl %r17, %r11, 63, 1
	addi %r17, %r17, -1
261:
	ld %r3, 0(%r15)
	rldicr %r4, %r3, 63, 0
	rldicl %r6, %r5, 63, 1
	or %r6, %r6, %r4
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r5, %r3, 0
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 261b
	rldicl %r6, %r5, 63, 1
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicr %r7, %r11, 2, 61
	add %r14, %r14, %r7
	ld %r3, 0(%r14)
	lis %r4, -8739
	ori %r4, %r4, 56797
	rldicr %r4, %r4, 32, 31
	oris %r4, %r4, 56797
	ori %r4, %r4, 56797
	and %r3, %r3, %r4
	rldicl %r5, %r3, 63, 1
	li %r0, 1
	and %r0, %r3, %r0
	or %r5, %r5, %r0
	addi %r5, %r5, -1
	rldicl %r5, %r5, 1, 63
	li %r0, 0
	subf %r5, %r5, %r0
	li %r9, 0
	addi %r9, %r9, -1
	xor %r9, %r9, %r5
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r16, %r10, 0
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	ld %r5, 0(%r15)
	addi %r15, %r15, 8
	rldicl %r17, %r11, 63, 1
	addi %r17, %r17, -1
262:
	ld %r3, 0(%r15)
	rldicr %r4, %r3, 63, 0
	rldicl %r6, %r5, 63, 1
	or %r6, %r6, %r4
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r5, %r3, 0
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 262b
	rldicl %r6, %r5, 63, 1
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicr %r7, %r11, 2, 61
	add %r14, %r14, %r7
	ld %r3, 0(%r14)
	lis %r4, -26215
	ori %r4, %r4, 39321
	rldicr %r4, %r4, 32, 31
	oris %r4, %r4, 39321
	ori %r4, %r4, 39321
	and %r3, %r3, %r4
	rldicl %r5, %r3, 63, 1
	li %r0, 1
	and %r0, %r3, %r0
	or %r5, %r5, %r0
	addi %r5, %r5, -1
	rldicl %r5, %r5, 1, 63
	li %r0, 0
	subf %r5, %r5, %r0
	li %r9, 0
	addi %r9, %r9, -1
	xor %r9, %r9, %r5
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r16, %r10, 0
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	ld %r5, 0(%r15)
	addi %r15, %r15, 8
	rldicl %r17, %r11, 63, 1
	addi %r17, %r17, -1
263:
	ld %r3, 0(%r15)
	rldicr %r4, %r3, 63, 0
	rldicl %r6, %r5, 63, 1
	or %r6, %r6, %r4
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r5, %r3, 0
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 263b
	rldicl %r6, %r5, 63, 1
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicr %r7, %r11, 2, 61
	add %r14, %r14, %r7
	ld %r3, 0(%r14)
	lis %r4, 4369
	ori %r4, %r4, 4369
	rldicr %r4, %r4, 32, 31
	oris %r4, %r4, 4369
	ori %r4, %r4, 4369
	and %r3, %r3, %r4
	rldicl %r5, %r3, 63, 1
	li %r0, 1
	and %r0, %r3, %r0
	or %r5, %r5, %r0
	addi %r5, %r5, -1
	rldicl %r5, %r5, 1, 63
	li %r0, 0
	subf %r5, %r5, %r0
	li %r9, 0
	addi %r9, %r9, -1
	xor %r9, %r9, %r5
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r16, %r10, 0
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	ld %r5, 0(%r15)
	addi %r15, %r15, 8
	rldicl %r17, %r11, 63, 1
	addi %r17, %r17, -1
264:
	ld %r3, 0(%r15)
	rldicr %r4, %r3, 63, 0
	rldicl %r6, %r5, 63, 1
	or %r6, %r6, %r4
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r5, %r3, 0
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 264b
	rldicl %r6, %r5, 63, 1
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	li %r3, 0
	std %r3, 176(%r31)
	li %r3, 4
	std %r3, 160(%r31)
265:
	ld %r3, 144(%r31)
	ld %r4, 152(%r31)
	subf %r3, %r4, %r3
	ld %r4, 216(%r31)
	subf %r5, %r4, %r3
	rldicl %r5, %r5, 1, 63
	li %r0, 1
	xor %r5, %r5, %r0
	rldicl %r0, %r3, 1, 63
	or %r5, %r5, %r0
	cmpldi %cr0, %r5, 0
	beq %cr0, 266f
	ld %r12, 136(%r31)
	ld %r3, 152(%r31)
	add %r12, %r12, %r3
	ld %r6, 216(%r31)
	add %r3, %r3, %r6
	std %r3, 152(%r31)
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
268:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 268b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
269:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 269b
	addi %r10, %r31, 256
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	rldicr %r6, %r11, 2, 61
	add %r5, %r5, %r6
	addi %r5, %r5, -8
	ld %r4, 192(%r31)
	ld %r6, 0(%r5)
	and %r6, %r6, %r4
	std %r6, 0(%r5)
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	ld %r24, 0(%r5)
	rldicl %r24, %r24, 63, 1
	addi %r5, %r5, 8
	rldicl %r6, %r11, 63, 1
	addi %r6, %r6, -1
270:
	ld %r3, 0(%r5)
	or %r24, %r24, %r3
	addi %r5, %r5, 8
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 270b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
271:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 271b
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	ld %r3, 0(%r5)
	li %r4, 1
	or %r3, %r3, %r4
	std %r3, 0(%r5)
	rldicr %r6, %r11, 2, 61
	add %r5, %r5, %r6
	li %r0, 0
	std %r0, 0(%r5)
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
272:
	lwz %r0, 0(%r14)
	lwz %r3, 0(%r16)
	subf %r0, %r3, %r0
	subf %r0, %r20, %r0
	stw %r0, 0(%r15)
	rldicl %r20, %r0, 1, 63
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 272b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	cmpldi %cr0, %r24, 0
	beq %cr0, 273f
	cmpldi %cr0, %r20, 0
	beq %cr0, 275f
	ld %r12, 56(%r31)
	rldicr %r12, %r12, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r6, %r10, 0
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	addi %r7, %r10, 0
	add %r7, %r7, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r4, %r11, 0
	ld %r3, 0(%r10)
	mulld %r22, %r3, %r12
	addi %r22, %r22, 2
	mulld %r22, %r22, %r12
	rldicr %r14, %r11, 2, 61
	add %r14, %r14, %r8
	std %r22, 8(%r14)
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r3, 0
277:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 277b
278:
	ld %r17, 0(%r6)
	addi %r6, %r6, 8
	ld %r19, 0(%r7)
	ld %r20, 0(%r8)
	mulld %r18, %r17, %r19
	mulhdu %r19, %r17, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r3, 0(%r10)
	mulld %r0, %r20, %r22
	mulld %r22, %r0, %r3
	mulhdu %r19, %r0, %r3
	addc %r22, %r22, %r20
	addze %r22, %r19
	addi %r14, %r8, 0
	addi %r15, %r7, 0
	addi %r3, %r10, 0
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicr %r16, %r16, 62, 1
	rldicl %r16, %r16, 2, 62
	cmpldi %cr0, %r16, 0
	beq %cr0, 279f
281:
	ld %r19, 8(%r14)
	ld %r20, 8(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 8(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r3, %r3, 8
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 281b
	b 280f
279:
280:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 282f
284:
	ld %r19, 8(%r14)
	ld %r20, 8(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 8(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 0(%r14)
	ld %r19, 16(%r14)
	ld %r20, 16(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 16(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 8(%r14)
	ld %r19, 24(%r14)
	ld %r20, 24(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 24(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 16(%r14)
	ld %r19, 32(%r14)
	ld %r20, 32(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 32(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r3, %r3, 32
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 284b
	b 283f
282:
283:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	li %r19, 0
	addze %r19, %r19
	addc %r18, %r18, %r22
	addze %r19, %r19
	std %r18, 0(%r14)
	std %r19, 8(%r14)
	ld %r22, 16(%r14)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 278b
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
285:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 285b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
286:
	ld %r0, 0(%r15)
	ld %r3, 0(%r14)
	xor %r3, %r3, %r0
	and %r3, %r3, %r20
	xor %r3, %r3, %r0
	std %r3, 0(%r16)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 286b
	addi %r3, %r31, 0
	ld %r4, 0(%r31)
	bl {vg_miller_rabin_round}
	rldicr %r3, %r3, 32, 31
	rldicl %r3, %r3, 32, 32
	addi %r10, %r31, 256
	ld %r11, 48(%r31)
	rldicr %r11, %r11, 1, 62
	ld %r29, 224(%r31)
	ld %r12, 56(%r31)
	rldicr %r12, %r12, 32, 31
	rldicl %r12, %r12, 32, 32
	cmpldi %cr0, %r3, 0
	beq %cr0, 287f
	ld %r3, 176(%r31)
	ld %r4, 168(%r31)
	addi %r3, %r3, 1
	std %r3, 176(%r31)
	subf %r4, %r3, %r4
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 3
	mulld %r4, %r4, %r5
	li %r5, 4
	subf %r4, %r4, %r5
	std %r4, 160(%r31)
	b 288f
287:
	li %r3, 2
	std %r3, 160(%r31)
288:
	b 276f
275:
276:
	b 274f
273:
274:
	b 267f
266:
	li %r3, 0
	std %r3, 160(%r31)
267:
	ld %r3, 160(%r31)
	addi %r3, %r3, -4
	cmpldi %cr0, %r3, 0
	beq %cr0, 265b
	ld %r3, 160(%r31)
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	beq %cr0, 289f
	ld %r3, 160(%r31)
	cmpldi %cr0, %r3, 0
	beq %cr0, 291f
	ld %r4, 32(%r31)
	ld %r5, 152(%r31)
	std %r5, 0(%r4)
	li %r3, 2
	b 292f
291:
	ld %r4, 32(%r31)
	li %r5, 0
	std %r5, 0(%r4)
	li %r3, 0
292:
	b 290f
289:
	addi %r5, %r10, 0
	rldicl %r6, %r11, 63, 1
	addi %r6, %r6, -1
293:
	ld %r3, 0(%r5)
	ld %r4, 8(%r5)
	rldicl %r3, %r3, 63, 1
	rldicr %r4, %r4, 63, 0
	or %r3, %r3, %r4
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 293b
	ld %r3, 0(%r5)
	rldicl %r3, %r3, 63, 1
	std %r3, 0(%r5)
	ld %r5, 200(%r31)
	ld %r3, 0(%r10)
	li %r4, 1
	and %r3, %r3, %r4
	xor %r3, %r3, %r4
	or %r5, %r5, %r3
	std %r5, 200(%r31)
	ld %r3, 40(%r31)
	addi %r3, %r3, -1
	std %r3, 248(%r31)
	addi %r4, %r3, 7
	rldicl %r4, %r4, 61, 3
	std %r4, 216(%r31)
	addi %r4, %r3, 63
	rldicl %r4, %r4, 58, 6
	std %r4, 48(%r31)
	rldicr %r11, %r4, 1, 62
	rldicr %r29, %r4, 3, 60
	addi %r29, %r29, 16
	std %r29, 224(%r31)
	addi %r10, %r31, 256
	addi %r5, %r10, 0
	std %r5, 64(%r31)
	add %r5, %r5, %r29
	std %r5, 72(%r31)
	add %r5, %r5, %r29
	std %r5, 80(%r31)
	add %r5, %r5, %r29
	std %r5, 88(%r31)
	add %r5, %r5, %r29
	std %r5, 96(%r31)
	add %r5, %r5, %r29
	std %r5, 104(%r31)
	add %r5, %r5, %r29
	std %r5, 112(%r31)
	add %r5, %r5, %r29
	std %r5, 120(%r31)
	add %r5, %r5, %r29
	addi %r5, %r3, -2049
	rldicl %r5, %r5, 1, 63
	rldicr %r5, %r5, 6, 57
	li %r6, 128
	subf %r5, %r5, %r6
	std %r5, 168(%r31)
	ld %r3, 248(%r31)
	ld %r4, 48(%r31)
	rldicr %r4, %r4, 6, 57
	subf %r3, %r4, %r3
	addi %r3, %r3, 64
	li %r5, 0
294:
	add %r5, %r5, %r5
	addi %r5, %r5, 1
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 294b
	std %r5, 192(%r31)
	ld %r0, 0(%r10)
	ld %r12, 0(%r10)
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	li %r3, 0
	subf %r3, %r12, %r3
	std %r3, 56(%r31)
	rldicr %r12, %r3, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r5, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
295:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 295b
	li %r0, 1
	stw %r0, 0(%r5)
	rldicr %r4, %r11, 6, 57
296:
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	addi %r17, %r11, 0
	li %r20, 0
297:
	lwz %r0, 0(%r15)
	add %r0, %r0, %r0
	add %r0, %r0, %r20
	stw %r0, 0(%r14)
	rldicl %r20, %r0, 32, 32
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 297b
	stw %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
298:
	lwz %r0, 0(%r14)
	lwz %r3, 0(%r16)
	subf %r0, %r3, %r0
	subf %r0, %r20, %r0
	stw %r0, 0(%r15)
	rldicl %r20, %r0, 1, 63
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 298b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	addi %r17, %r11, 0
299:
	lwz %r0, 0(%r15)
	lwz %r3, 0(%r14)
	xor %r3, %r3, %r0
	and %r3, %r3, %r20
	xor %r3, %r3, %r0
	stw %r3, 0(%r16)
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 299b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 296b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2100:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2100b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	li %r0, 1
	stw %r0, 0(%r14)
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r6, %r10, 0
	add %r6, %r6, %r29
	addi %r7, %r10, 0
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r4, %r11, 0
	ld %r3, 0(%r10)
	mulld %r22, %r3, %r12
	addi %r22, %r22, 2
	mulld %r22, %r22, %r12
	rldicr %r14, %r11, 2, 61
	add %r14, %r14, %r8
	std %r22, 8(%r14)
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r3, 0
2101:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2101b
2102:
	ld %r17, 0(%r6)
	addi %r6, %r6, 8
	ld %r19, 0(%r7)
	ld %r20, 0(%r8)
	mulld %r18, %r17, %r19
	mulhdu %r19, %r17, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r3, 0(%r10)
	mulld %r0, %r20, %r22
	mulld %r22, %r0, %r3
	mulhdu %r19, %r0, %r3
	addc %r22, %r22, %r20
	addze %r22, %r19
	addi %r14, %r8, 0
	addi %r15, %r7, 0
	addi %r3, %r10, 0
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicr %r16, %r16, 62, 1
	rldicl %r16, %r16, 2, 62
	cmpldi %cr0, %r16, 0
	beq %cr0, 2103f
2105:
	ld %r19, 8(%r14)
	ld %r20, 8(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 8(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r3, %r3, 8
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 2105b
	b 2104f
2103:
2104:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2106f
2108:
	ld %r19, 8(%r14)
	ld %r20, 8(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 8(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 0(%r14)
	ld %r19, 16(%r14)
	ld %r20, 16(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 16(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 8(%r14)
	ld %r19, 24(%r14)
	ld %r20, 24(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 24(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 16(%r14)
	ld %r19, 32(%r14)
	ld %r20, 32(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 32(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r3, %r3, 32
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 2108b
	b 2107f
2106:
2107:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	li %r19, 0
	addze %r19, %r19
	addc %r18, %r18, %r22
	addze %r19, %r19
	std %r18, 0(%r14)
	std %r19, 8(%r14)
	ld %r22, 16(%r14)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2102b
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2109:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2109b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2110:
	ld %r0, 0(%r15)
	ld %r3, 0(%r14)
	xor %r3, %r3, %r0
	and %r3, %r3, %r20
	xor %r3, %r3, %r0
	std %r3, 0(%r16)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2110b
	addi %r8, %r10, 0
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2111:
	lwz %r0, 0(%r14)
	lwz %r3, 0(%r16)
	subf %r0, %r3, %r0
	subf %r0, %r20, %r0
	stw %r0, 0(%r15)
	rldicl %r20, %r0, 1, 63
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2111b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r31, 256
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
2112:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2112b
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r6, 0
	li %r4, 1
2113:
	ld %r7, 0(%r14)
	xor %r7, %r7, %r4
	li %r4, 0
	addi %r3, %r6, 0
	rldicl %r5, %r3, 63, 1
	li %r0, 1
	and %r0, %r3, %r0
	or %r5, %r5, %r0
	addi %r5, %r5, -1
	rldicl %r5, %r5, 1, 63
	li %r0, 0
	subf %r5, %r5, %r0
	and %r7, %r7, %r5
	or %r6, %r6, %r7
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2113b
	li %r7, 0
	subf %r7, %r6, %r7
	and %r6, %r6, %r7
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicr %r7, %r11, 2, 61
	add %r14, %r14, %r7
	std %r6, 0(%r14)
	li %r9, 0
	addi %r9, %r9, -1
	addi %r15, %r10, 0
	addi %r16, %r10, 0
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	ld %r5, 0(%r15)
	addi %r15, %r15, 8
	rldicl %r17, %r11, 63, 1
	addi %r17, %r17, -1
2114:
	ld %r3, 0(%r15)
	rldicr %r4, %r3, 63, 0
	rldicl %r6, %r5, 63, 1
	or %r6, %r6, %r4
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r5, %r3, 0
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2114b
	rldicl %r6, %r5, 63, 1
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicr %r7, %r11, 2, 61
	add %r14, %r14, %r7
	ld %r3, 0(%r14)
	lis %r4, -8739
	ori %r4, %r4, 56797
	rldicr %r4, %r4, 32, 31
	oris %r4, %r4, 56797
	ori %r4, %r4, 56797
	and %r3, %r3, %r4
	rldicl %r5, %r3, 63, 1
	li %r0, 1
	and %r0, %r3, %r0
	or %r5, %r5, %r0
	addi %r5, %r5, -1
	rldicl %r5, %r5, 1, 63
	li %r0, 0
	subf %r5, %r5, %r0
	li %r9, 0
	addi %r9, %r9, -1
	xor %r9, %r9, %r5
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r16, %r10, 0
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	ld %r5, 0(%r15)
	addi %r15, %r15, 8
	rldicl %r17, %r11, 63, 1
	addi %r17, %r17, -1
2115:
	ld %r3, 0(%r15)
	rldicr %r4, %r3, 63, 0
	rldicl %r6, %r5, 63, 1
	or %r6, %r6, %r4
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r5, %r3, 0
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2115b
	rldicl %r6, %r5, 63, 1
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicr %r7, %r11, 2, 61
	add %r14, %r14, %r7
	ld %r3, 0(%r14)
	lis %r4, -26215
	ori %r4, %r4, 39321
	rldicr %r4, %r4, 32, 31
	oris %r4, %r4, 39321
	ori %r4, %r4, 39321
	and %r3, %r3, %r4
	rldicl %r5, %r3, 63, 1
	li %r0, 1
	and %r0, %r3, %r0
	or %r5, %r5, %r0
	addi %r5, %r5, -1
	rldicl %r5, %r5, 1, 63
	li %r0, 0
	subf %r5, %r5, %r0
	li %r9, 0
	addi %r9, %r9, -1
	xor %r9, %r9, %r5
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r16, %r10, 0
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	ld %r5, 0(%r15)
	addi %r15, %r15, 8
	rldicl %r17, %r11, 63, 1
	addi %r17, %r17, -1
2116:
	ld %r3, 0(%r15)
	rldicr %r4, %r3, 63, 0
	rldicl %r6, %r5, 63, 1
	or %r6, %r6, %r4
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r5, %r3, 0
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2116b
	rldicl %r6, %r5, 63, 1
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicr %r7, %r11, 2, 61
	add %r14, %r14, %r7
	ld %r3, 0(%r14)
	lis %r4, 4369
	ori %r4, %r4, 4369
	rldicr %r4, %r4, 32, 31
	oris %r4, %r4, 4369
	ori %r4, %r4, 4369
	and %r3, %r3, %r4
	rldicl %r5, %r3, 63, 1
	li %r0, 1
	and %r0, %r3, %r0
	or %r5, %r5, %r0
	addi %r5, %r5, -1
	rldicl %r5, %r5, 1, 63
	li %r0, 0
	subf %r5, %r5, %r0
	li %r9, 0
	addi %r9, %r9, -1
	xor %r9, %r9, %r5
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r16, %r10, 0
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	ld %r5, 0(%r15)
	addi %r15, %r15, 8
	rldicl %r17, %r11, 63, 1
	addi %r17, %r17, -1
2117:
	ld %r3, 0(%r15)
	rldicr %r4, %r3, 63, 0
	rldicl %r6, %r5, 63, 1
	or %r6, %r6, %r4
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r5, %r3, 0
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2117b
	rldicl %r6, %r5, 63, 1
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	li %r3, 0
	std %r3, 176(%r31)
	li %r3, 4
	std %r3, 160(%r31)
2118:
	ld %r3, 144(%r31)
	ld %r4, 152(%r31)
	subf %r3, %r4, %r3
	ld %r4, 216(%r31)
	subf %r5, %r4, %r3
	rldicl %r5, %r5, 1, 63
	li %r0, 1
	xor %r5, %r5, %r0
	rldicl %r0, %r3, 1, 63
	or %r5, %r5, %r0
	cmpldi %cr0, %r5, 0
	beq %cr0, 2119f
	ld %r12, 136(%r31)
	ld %r3, 152(%r31)
	add %r12, %r12, %r3
	ld %r6, 216(%r31)
	add %r3, %r3, %r6
	std %r3, 152(%r31)
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2121:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2121b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2122:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2122b
	addi %r10, %r31, 256
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	rldicr %r6, %r11, 2, 61
	add %r5, %r5, %r6
	addi %r5, %r5, -8
	ld %r4, 192(%r31)
	ld %r6, 0(%r5)
	and %r6, %r6, %r4
	std %r6, 0(%r5)
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	ld %r24, 0(%r5)
	rldicl %r24, %r24, 63, 1
	addi %r5, %r5, 8
	rldicl %r6, %r11, 63, 1
	addi %r6, %r6, -1
2123:
	ld %r3, 0(%r5)
	or %r24, %r24, %r3
	addi %r5, %r5, 8
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2123b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
2124:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2124b
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	ld %r3, 0(%r5)
	li %r4, 1
	or %r3, %r3, %r4
	std %r3, 0(%r5)
	rldicr %r6, %r11, 2, 61
	add %r5, %r5, %r6
	li %r0, 0
	std %r0, 0(%r5)
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2125:
	lwz %r0, 0(%r14)
	lwz %r3, 0(%r16)
	subf %r0, %r3, %r0
	subf %r0, %r20, %r0
	stw %r0, 0(%r15)
	rldicl %r20, %r0, 1, 63
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2125b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	cmpldi %cr0, %r24, 0
	beq %cr0, 2126f
	cmpldi %cr0, %r20, 0
	beq %cr0, 2128f
	ld %r12, 56(%r31)
	rldicr %r12, %r12, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r6, %r10, 0
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	addi %r7, %r10, 0
	add %r7, %r7, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r4, %r11, 0
	ld %r3, 0(%r10)
	mulld %r22, %r3, %r12
	addi %r22, %r22, 2
	mulld %r22, %r22, %r12
	rldicr %r14, %r11, 2, 61
	add %r14, %r14, %r8
	std %r22, 8(%r14)
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r3, 0
2130:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2130b
2131:
	ld %r17, 0(%r6)
	addi %r6, %r6, 8
	ld %r19, 0(%r7)
	ld %r20, 0(%r8)
	mulld %r18, %r17, %r19
	mulhdu %r19, %r17, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r3, 0(%r10)
	mulld %r0, %r20, %r22
	mulld %r22, %r0, %r3
	mulhdu %r19, %r0, %r3
	addc %r22, %r22, %r20
	addze %r22, %r19
	addi %r14, %r8, 0
	addi %r15, %r7, 0
	addi %r3, %r10, 0
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicr %r16, %r16, 62, 1
	rldicl %r16, %r16, 2, 62
	cmpldi %cr0, %r16, 0
	beq %cr0, 2132f
2134:
	ld %r19, 8(%r14)
	ld %r20, 8(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 8(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r3, %r3, 8
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 2134b
	b 2133f
2132:
2133:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2135f
2137:
	ld %r19, 8(%r14)
	ld %r20, 8(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 8(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 0(%r14)
	ld %r19, 16(%r14)
	ld %r20, 16(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 16(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 8(%r14)
	ld %r19, 24(%r14)
	ld %r20, 24(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 24(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 16(%r14)
	ld %r19, 32(%r14)
	ld %r20, 32(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 32(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r3, %r3, 32
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 2137b
	b 2136f
2135:
2136:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	li %r19, 0
	addze %r19, %r19
	addc %r18, %r18, %r22
	addze %r19, %r19
	std %r18, 0(%r14)
	std %r19, 8(%r14)
	ld %r22, 16(%r14)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2131b
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2138:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2138b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2139:
	ld %r0, 0(%r15)
	ld %r3, 0(%r14)
	xor %r3, %r3, %r0
	and %r3, %r3, %r20
	xor %r3, %r3, %r0
	std %r3, 0(%r16)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2139b
	addi %r3, %r31, 0
	ld %r4, 0(%r31)
	bl {vg_miller_rabin_round}
	rldicr %r3, %r3, 32, 31
	rldicl %r3, %r3, 32, 32
	addi %r10, %r31, 256
	ld %r11, 48(%r31)
	rldicr %r11, %r11, 1, 62
	ld %r29, 224(%r31)
	ld %r12, 56(%r31)
	rldicr %r12, %r12, 32, 31
	rldicl %r12, %r12, 32, 32
	cmpldi %cr0, %r3, 0
	beq %cr0, 2140f
	ld %r3, 176(%r31)
	ld %r4, 168(%r31)
	addi %r3, %r3, 1
	std %r3, 176(%r31)
	subf %r4, %r3, %r4
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 3
	mulld %r4, %r4, %r5
	li %r5, 4
	subf %r4, %r4, %r5
	std %r4, 160(%r31)
	b 2141f
2140:
	li %r3, 2
	std %r3, 160(%r31)
2141:
	b 2129f
2128:
2129:
	b 2127f
2126:
2127:
	b 2120f
2119:
	li %r3, 0
	std %r3, 160(%r31)
2120:
	ld %r3, 160(%r31)
	addi %r3, %r3, -4
	cmpldi %cr0, %r3, 0
	beq %cr0, 2118b
	ld %r3, 160(%r31)
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	beq %cr0, 2142f
	ld %r3, 160(%r31)
	cmpldi %cr0, %r3, 0
	beq %cr0, 2144f
	ld %r4, 32(%r31)
	ld %r5, 152(%r31)
	std %r5, 0(%r4)
	li %r3, 2
	b 2145f
2144:
	ld %r4, 32(%r31)
	li %r5, 0
	std %r5, 0(%r4)
	li %r3, 0
2145:
	b 2143f
2142:
	ld %r3, 40(%r31)
	std %r3, 248(%r31)
	addi %r4, %r3, 7
	rldicl %r4, %r4, 61, 3
	std %r4, 216(%r31)
	addi %r4, %r3, 63
	rldicl %r4, %r4, 58, 6
	std %r4, 48(%r31)
	rldicr %r11, %r4, 1, 62
	rldicr %r29, %r4, 3, 60
	addi %r29, %r29, 16
	std %r29, 224(%r31)
	addi %r10, %r31, 256
	addi %r5, %r10, 0
	std %r5, 64(%r31)
	add %r5, %r5, %r29
	std %r5, 72(%r31)
	add %r5, %r5, %r29
	std %r5, 80(%r31)
	add %r5, %r5, %r29
	std %r5, 88(%r31)
	add %r5, %r5, %r29
	std %r5, 96(%r31)
	add %r5, %r5, %r29
	std %r5, 104(%r31)
	add %r5, %r5, %r29
	std %r5, 112(%r31)
	add %r5, %r5, %r29
	std %r5, 120(%r31)
	add %r5, %r5, %r29
	addi %r5, %r3, -2049
	rldicl %r5, %r5, 1, 63
	rldicr %r5, %r5, 6, 57
	li %r6, 128
	subf %r5, %r5, %r6
	std %r5, 168(%r31)
	ld %r3, 248(%r31)
	ld %r4, 48(%r31)
	rldicr %r4, %r4, 6, 57
	subf %r3, %r4, %r3
	addi %r3, %r3, 64
	li %r5, 0
2146:
	add %r5, %r5, %r5
	addi %r5, %r5, 1
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 2146b
	std %r5, 192(%r31)
	ld %r12, 136(%r31)
	ld %r6, 24(%r31)
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2147:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2147b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2148:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2148b
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	addi %r5, %r5, -8
	ld %r4, 192(%r31)
	ld %r6, 0(%r5)
	and %r6, %r6, %r4
	rldicl %r4, %r4, 63, 1
	addi %r4, %r4, 1
	or %r6, %r6, %r4
	std %r6, 0(%r5)
	ld %r6, 0(%r10)
	li %r4, 1
	or %r6, %r6, %r4
	std %r6, 0(%r10)
	ld %r3, 168(%r31)
	addi %r3, %r3, -1
	std %r3, 168(%r31)
	ld %r0, 0(%r10)
	ld %r12, 0(%r10)
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	mulld %r3, %r0, %r12
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r12, %r12, %r3
	li %r3, 0
	subf %r3, %r12, %r3
	std %r3, 56(%r31)
	rldicr %r12, %r3, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r5, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2149:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2149b
	li %r0, 1
	stw %r0, 0(%r5)
	rldicr %r4, %r11, 6, 57
2150:
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	addi %r17, %r11, 0
	li %r20, 0
2151:
	lwz %r0, 0(%r15)
	add %r0, %r0, %r0
	add %r0, %r0, %r20
	stw %r0, 0(%r14)
	rldicl %r20, %r0, 32, 32
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2151b
	stw %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2152:
	lwz %r0, 0(%r14)
	lwz %r3, 0(%r16)
	subf %r0, %r3, %r0
	subf %r0, %r20, %r0
	stw %r0, 0(%r15)
	rldicl %r20, %r0, 1, 63
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2152b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	addi %r17, %r11, 0
2153:
	lwz %r0, 0(%r15)
	lwz %r3, 0(%r14)
	xor %r3, %r3, %r0
	and %r3, %r3, %r20
	xor %r3, %r3, %r0
	stw %r3, 0(%r16)
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2153b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2150b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2154:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2154b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	li %r0, 1
	stw %r0, 0(%r14)
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r6, %r10, 0
	add %r6, %r6, %r29
	addi %r7, %r10, 0
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	add %r7, %r7, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r4, %r11, 0
	ld %r3, 0(%r10)
	mulld %r22, %r3, %r12
	addi %r22, %r22, 2
	mulld %r22, %r22, %r12
	rldicr %r14, %r11, 2, 61
	add %r14, %r14, %r8
	std %r22, 8(%r14)
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r3, 0
2155:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2155b
2156:
	ld %r17, 0(%r6)
	addi %r6, %r6, 8
	ld %r19, 0(%r7)
	ld %r20, 0(%r8)
	mulld %r18, %r17, %r19
	mulhdu %r19, %r17, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r3, 0(%r10)
	mulld %r0, %r20, %r22
	mulld %r22, %r0, %r3
	mulhdu %r19, %r0, %r3
	addc %r22, %r22, %r20
	addze %r22, %r19
	addi %r14, %r8, 0
	addi %r15, %r7, 0
	addi %r3, %r10, 0
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicr %r16, %r16, 62, 1
	rldicl %r16, %r16, 2, 62
	cmpldi %cr0, %r16, 0
	beq %cr0, 2157f
2159:
	ld %r19, 8(%r14)
	ld %r20, 8(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 8(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r3, %r3, 8
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 2159b
	b 2158f
2157:
2158:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2160f
2162:
	ld %r19, 8(%r14)
	ld %r20, 8(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 8(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 0(%r14)
	ld %r19, 16(%r14)
	ld %r20, 16(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 16(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 8(%r14)
	ld %r19, 24(%r14)
	ld %r20, 24(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 24(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 16(%r14)
	ld %r19, 32(%r14)
	ld %r20, 32(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 32(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r3, %r3, 32
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 2162b
	b 2161f
2160:
2161:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	li %r19, 0
	addze %r19, %r19
	addc %r18, %r18, %r22
	addze %r19, %r19
	std %r18, 0(%r14)
	std %r19, 8(%r14)
	ld %r22, 16(%r14)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2156b
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2163:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2163b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2164:
	ld %r0, 0(%r15)
	ld %r3, 0(%r14)
	xor %r3, %r3, %r0
	and %r3, %r3, %r20
	xor %r3, %r3, %r0
	std %r3, 0(%r16)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2164b
	addi %r8, %r10, 0
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2165:
	lwz %r0, 0(%r14)
	lwz %r3, 0(%r16)
	subf %r0, %r3, %r0
	subf %r0, %r20, %r0
	stw %r0, 0(%r15)
	rldicl %r20, %r0, 1, 63
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2165b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r31, 256
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
2166:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2166b
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r6, 0
	li %r4, 1
2167:
	ld %r7, 0(%r14)
	xor %r7, %r7, %r4
	li %r4, 0
	addi %r3, %r6, 0
	rldicl %r5, %r3, 63, 1
	li %r0, 1
	and %r0, %r3, %r0
	or %r5, %r5, %r0
	addi %r5, %r5, -1
	rldicl %r5, %r5, 1, 63
	li %r0, 0
	subf %r5, %r5, %r0
	and %r7, %r7, %r5
	or %r6, %r6, %r7
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2167b
	li %r7, 0
	subf %r7, %r6, %r7
	and %r6, %r6, %r7
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicr %r7, %r11, 2, 61
	add %r14, %r14, %r7
	std %r6, 0(%r14)
	li %r9, 0
	addi %r9, %r9, -1
	addi %r15, %r10, 0
	addi %r16, %r10, 0
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	ld %r5, 0(%r15)
	addi %r15, %r15, 8
	rldicl %r17, %r11, 63, 1
	addi %r17, %r17, -1
2168:
	ld %r3, 0(%r15)
	rldicr %r4, %r3, 63, 0
	rldicl %r6, %r5, 63, 1
	or %r6, %r6, %r4
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r5, %r3, 0
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2168b
	rldicl %r6, %r5, 63, 1
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicr %r7, %r11, 2, 61
	add %r14, %r14, %r7
	ld %r3, 0(%r14)
	lis %r4, -8739
	ori %r4, %r4, 56797
	rldicr %r4, %r4, 32, 31
	oris %r4, %r4, 56797
	ori %r4, %r4, 56797
	and %r3, %r3, %r4
	rldicl %r5, %r3, 63, 1
	li %r0, 1
	and %r0, %r3, %r0
	or %r5, %r5, %r0
	addi %r5, %r5, -1
	rldicl %r5, %r5, 1, 63
	li %r0, 0
	subf %r5, %r5, %r0
	li %r9, 0
	addi %r9, %r9, -1
	xor %r9, %r9, %r5
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r16, %r10, 0
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	ld %r5, 0(%r15)
	addi %r15, %r15, 8
	rldicl %r17, %r11, 63, 1
	addi %r17, %r17, -1
2169:
	ld %r3, 0(%r15)
	rldicr %r4, %r3, 63, 0
	rldicl %r6, %r5, 63, 1
	or %r6, %r6, %r4
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r5, %r3, 0
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2169b
	rldicl %r6, %r5, 63, 1
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicr %r7, %r11, 2, 61
	add %r14, %r14, %r7
	ld %r3, 0(%r14)
	lis %r4, -26215
	ori %r4, %r4, 39321
	rldicr %r4, %r4, 32, 31
	oris %r4, %r4, 39321
	ori %r4, %r4, 39321
	and %r3, %r3, %r4
	rldicl %r5, %r3, 63, 1
	li %r0, 1
	and %r0, %r3, %r0
	or %r5, %r5, %r0
	addi %r5, %r5, -1
	rldicl %r5, %r5, 1, 63
	li %r0, 0
	subf %r5, %r5, %r0
	li %r9, 0
	addi %r9, %r9, -1
	xor %r9, %r9, %r5
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r16, %r10, 0
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	ld %r5, 0(%r15)
	addi %r15, %r15, 8
	rldicl %r17, %r11, 63, 1
	addi %r17, %r17, -1
2170:
	ld %r3, 0(%r15)
	rldicr %r4, %r3, 63, 0
	rldicl %r6, %r5, 63, 1
	or %r6, %r6, %r4
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r5, %r3, 0
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2170b
	rldicl %r6, %r5, 63, 1
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicr %r7, %r11, 2, 61
	add %r14, %r14, %r7
	ld %r3, 0(%r14)
	lis %r4, 4369
	ori %r4, %r4, 4369
	rldicr %r4, %r4, 32, 31
	oris %r4, %r4, 4369
	ori %r4, %r4, 4369
	and %r3, %r3, %r4
	rldicl %r5, %r3, 63, 1
	li %r0, 1
	and %r0, %r3, %r0
	or %r5, %r5, %r0
	addi %r5, %r5, -1
	rldicl %r5, %r5, 1, 63
	li %r0, 0
	subf %r5, %r5, %r0
	li %r9, 0
	addi %r9, %r9, -1
	xor %r9, %r9, %r5
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r16, %r10, 0
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	ld %r5, 0(%r15)
	addi %r15, %r15, 8
	rldicl %r17, %r11, 63, 1
	addi %r17, %r17, -1
2171:
	ld %r3, 0(%r15)
	rldicr %r4, %r3, 63, 0
	rldicl %r6, %r5, 63, 1
	or %r6, %r6, %r4
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r5, %r3, 0
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2171b
	rldicl %r6, %r5, 63, 1
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	li %r3, 0
	std %r3, 176(%r31)
	li %r3, 4
	std %r3, 160(%r31)
2172:
	ld %r3, 144(%r31)
	ld %r4, 152(%r31)
	subf %r3, %r4, %r3
	ld %r4, 216(%r31)
	subf %r5, %r4, %r3
	rldicl %r5, %r5, 1, 63
	li %r0, 1
	xor %r5, %r5, %r0
	rldicl %r0, %r3, 1, 63
	or %r5, %r5, %r0
	cmpldi %cr0, %r5, 0
	beq %cr0, 2173f
	ld %r12, 136(%r31)
	ld %r3, 152(%r31)
	add %r12, %r12, %r3
	ld %r6, 216(%r31)
	add %r3, %r3, %r6
	std %r3, 152(%r31)
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2175:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2175b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2176:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2176b
	addi %r10, %r31, 256
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	rldicr %r6, %r11, 2, 61
	add %r5, %r5, %r6
	addi %r5, %r5, -8
	ld %r4, 192(%r31)
	ld %r6, 0(%r5)
	and %r6, %r6, %r4
	std %r6, 0(%r5)
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	ld %r24, 0(%r5)
	rldicl %r24, %r24, 63, 1
	addi %r5, %r5, 8
	rldicl %r6, %r11, 63, 1
	addi %r6, %r6, -1
2177:
	ld %r3, 0(%r5)
	or %r24, %r24, %r3
	addi %r5, %r5, 8
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2177b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
2178:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2178b
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	ld %r3, 0(%r5)
	li %r4, 1
	or %r3, %r3, %r4
	std %r3, 0(%r5)
	rldicr %r6, %r11, 2, 61
	add %r5, %r5, %r6
	li %r0, 0
	std %r0, 0(%r5)
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2179:
	lwz %r0, 0(%r14)
	lwz %r3, 0(%r16)
	subf %r0, %r3, %r0
	subf %r0, %r20, %r0
	stw %r0, 0(%r15)
	rldicl %r20, %r0, 1, 63
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2179b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	cmpldi %cr0, %r24, 0
	beq %cr0, 2180f
	cmpldi %cr0, %r20, 0
	beq %cr0, 2182f
	ld %r12, 56(%r31)
	rldicr %r12, %r12, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r6, %r10, 0
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	addi %r7, %r10, 0
	add %r7, %r7, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r4, %r11, 0
	ld %r3, 0(%r10)
	mulld %r22, %r3, %r12
	addi %r22, %r22, 2
	mulld %r22, %r22, %r12
	rldicr %r14, %r11, 2, 61
	add %r14, %r14, %r8
	std %r22, 8(%r14)
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r3, 0
2184:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2184b
2185:
	ld %r17, 0(%r6)
	addi %r6, %r6, 8
	ld %r19, 0(%r7)
	ld %r20, 0(%r8)
	mulld %r18, %r17, %r19
	mulhdu %r19, %r17, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r3, 0(%r10)
	mulld %r0, %r20, %r22
	mulld %r22, %r0, %r3
	mulhdu %r19, %r0, %r3
	addc %r22, %r22, %r20
	addze %r22, %r19
	addi %r14, %r8, 0
	addi %r15, %r7, 0
	addi %r3, %r10, 0
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicr %r16, %r16, 62, 1
	rldicl %r16, %r16, 2, 62
	cmpldi %cr0, %r16, 0
	beq %cr0, 2186f
2188:
	ld %r19, 8(%r14)
	ld %r20, 8(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 8(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r3, %r3, 8
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 2188b
	b 2187f
2186:
2187:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2189f
2191:
	ld %r19, 8(%r14)
	ld %r20, 8(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 8(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 0(%r14)
	ld %r19, 16(%r14)
	ld %r20, 16(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 16(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 8(%r14)
	ld %r19, 24(%r14)
	ld %r20, 24(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 24(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 16(%r14)
	ld %r19, 32(%r14)
	ld %r20, 32(%r15)
	mulld %r12, %r17, %r20
	mulhdu %r20, %r17, %r20
	addc %r19, %r19, %r12
	addze %r20, %r20
	addc %r19, %r19, %r18
	addze %r18, %r20
	ld %r20, 32(%r3)
	mulld %r12, %r0, %r20
	mulhdu %r20, %r0, %r20
	addc %r12, %r12, %r19
	addze %r20, %r20
	addc %r12, %r12, %r22
	addze %r22, %r20
	std %r12, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r3, %r3, 32
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 2191b
	b 2190f
2189:
2190:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	li %r19, 0
	addze %r19, %r19
	addc %r18, %r18, %r22
	addze %r19, %r19
	std %r18, 0(%r14)
	std %r19, 8(%r14)
	ld %r22, 16(%r14)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2185b
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2192:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2192b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2193:
	ld %r0, 0(%r15)
	ld %r3, 0(%r14)
	xor %r3, %r3, %r0
	and %r3, %r3, %r20
	xor %r3, %r3, %r0
	std %r3, 0(%r16)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2193b
	addi %r3, %r31, 0
	ld %r4, 0(%r31)
	bl {vg_miller_rabin_round}
	rldicr %r3, %r3, 32, 31
	rldicl %r3, %r3, 32, 32
	addi %r10, %r31, 256
	ld %r11, 48(%r31)
	rldicr %r11, %r11, 1, 62
	ld %r29, 224(%r31)
	ld %r12, 56(%r31)
	rldicr %r12, %r12, 32, 31
	rldicl %r12, %r12, 32, 32
	cmpldi %cr0, %r3, 0
	beq %cr0, 2194f
	ld %r3, 176(%r31)
	ld %r4, 168(%r31)
	addi %r3, %r3, 1
	std %r3, 176(%r31)
	subf %r4, %r3, %r4
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 3
	mulld %r4, %r4, %r5
	li %r5, 4
	subf %r4, %r4, %r5
	std %r4, 160(%r31)
	b 2195f
2194:
	li %r3, 2
	std %r3, 160(%r31)
2195:
	b 2183f
2182:
2183:
	b 2181f
2180:
2181:
	b 2174f
2173:
	li %r3, 0
	std %r3, 160(%r31)
2174:
	ld %r3, 160(%r31)
	addi %r3, %r3, -4
	cmpldi %cr0, %r3, 0
	beq %cr0, 2172b
	ld %r3, 160(%r31)
	cmpldi %cr0, %r3, 0
	beq %cr0, 2196f
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	beq %cr0, 2198f
	ld %r4, 32(%r31)
	ld %r5, 152(%r31)
	std %r5, 0(%r4)
	li %r3, 2
	b 2199f
2198:
	ld %r4, 16(%r31)
	ld %r5, 24(%r31)
	add %r6, %r10, %r5
	addi %r6, %r6, -1
2200:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	addi %r6, %r6, -1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2200b
	ld %r4, 32(%r31)
	ld %r5, 152(%r31)
	std %r5, 0(%r4)
	li %r3, 1
2199:
	b 2197f
2196:
	ld %r4, 32(%r31)
	li %r5, 0
	std %r5, 0(%r4)
	li %r3, 0
2197:
2143:
290:
238:
228:
219:
211:
	b 22f
21:
	ld %r4, 32(%r31)
	li %r5, 0
	std %r5, 0(%r4)
	li %r3, 0
22:
	ld %r11, 0(%r31)
	rldicr %r11, %r11, 3, 60
	add %r11, %r31, %r11
	addi %r11, %r11, -160
	ld %r0, 144(%r11)
	mtlr %r0
	ld %r14, 0(%r11)
	ld %r15, 8(%r11)
	ld %r16, 16(%r11)
	ld %r17, 24(%r11)
	ld %r18, 32(%r11)
	ld %r19, 40(%r11)
	ld %r20, 48(%r11)
	ld %r21, 56(%r11)
	ld %r22, 64(%r11)
	ld %r23, 72(%r11)
	ld %r24, 80(%r11)
	ld %r25, 88(%r11)
	ld %r26, 96(%r11)
	ld %r27, 104(%r11)
	ld %r28, 112(%r11)
	ld %r29, 120(%r11)
	ld %r30, 128(%r11)
	ld %r31, 136(%r11)
	blr
