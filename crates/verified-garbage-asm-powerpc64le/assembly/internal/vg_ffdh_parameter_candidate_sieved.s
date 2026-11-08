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
	li %r3, 16
	std %r3, 208(%r31)
	bcl 20, 31, 2f
2:
	mflr %r23
	addis %r23, %r23, ({VG_RSA_KEYGEN_TRIAL32}
	addi %r23, %r23, ({VG_RSA_KEYGEN_TRIAL32}
	ld %r24, 208(%r31)
212:
	ld %r8, 0(%r23)
	rldicl %r9, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	rldicl %r8, %r8, 32, 32
	li %r3, 0
	addi %r5, %r10, 0
	addi %r4, %r11, 0
213:
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
	bne %cr0, 213b
	addi %r6, %r3, -1
	rldicl %r6, %r6, 1, 63
	xor %r7, %r3, %r8
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	or %r22, %r6, %r7
	addi %r23, %r23, 8
	addi %r24, %r24, -1
	addi %r6, %r22, -1
	and %r24, %r24, %r6
	cmpldi %cr0, %r24, 0
	bne %cr0, 212b
	ld %r5, 200(%r31)
	or %r5, %r5, %r22
	std %r5, 200(%r31)
	ld %r5, 200(%r31)
	cmpldi %cr0, %r5, 0
	beq %cr0, 214f
	ld %r4, 32(%r31)
	ld %r5, 152(%r31)
	std %r5, 0(%r4)
	li %r3, 2
	b 215f
214:
	addi %r5, %r10, 0
	rldicl %r6, %r11, 63, 1
	addi %r6, %r6, -1
216:
	ld %r3, 0(%r5)
	ld %r4, 8(%r5)
	rldicl %r3, %r3, 63, 1
	rldicr %r4, %r4, 63, 0
	or %r3, %r3, %r4
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 216b
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
	addi %r3, %r3, -1025
	rldicl %r3, %r3, 1, 63
	rldicr %r3, %r3, 9, 54
	li %r4, 1024
	subf %r3, %r3, %r4
	std %r3, 208(%r31)
	bcl 20, 31, 2f
2:
	mflr %r23
	addis %r23, %r23, ({VG_RSA_KEYGEN_TRIAL32}
	addi %r23, %r23, ({VG_RSA_KEYGEN_TRIAL32}
	ld %r24, 208(%r31)
217:
	ld %r8, 0(%r23)
	rldicl %r9, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	rldicl %r8, %r8, 32, 32
	li %r3, 0
	addi %r5, %r10, 0
	addi %r4, %r11, 0
218:
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
	bne %cr0, 218b
	addi %r6, %r3, -1
	rldicl %r6, %r6, 1, 63
	xor %r7, %r3, %r8
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	or %r22, %r6, %r7
	addi %r23, %r23, 8
	addi %r24, %r24, -1
	addi %r6, %r22, -1
	and %r24, %r24, %r6
	cmpldi %cr0, %r24, 0
	bne %cr0, 217b
	ld %r5, 200(%r31)
	or %r5, %r5, %r22
	std %r5, 200(%r31)
	ld %r5, 200(%r31)
	cmpldi %cr0, %r5, 0
	beq %cr0, 219f
	ld %r4, 32(%r31)
	ld %r5, 152(%r31)
	std %r5, 0(%r4)
	li %r3, 2
	b 220f
219:
	ld %r12, 136(%r31)
	ld %r6, 24(%r31)
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
221:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 221b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
222:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 222b
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
	ld %r3, 40(%r31)
	addi %r3, %r3, -1025
	rldicl %r3, %r3, 1, 63
	rldicr %r3, %r3, 9, 54
	li %r4, 1024
	subf %r3, %r3, %r4
	std %r3, 208(%r31)
	bcl 20, 31, 2f
2:
	mflr %r23
	addis %r23, %r23, ({VG_RSA_KEYGEN_TRIAL32}
	addi %r23, %r23, ({VG_RSA_KEYGEN_TRIAL32}
	ld %r24, 208(%r31)
223:
	ld %r8, 0(%r23)
	rldicl %r9, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	rldicl %r8, %r8, 32, 32
	li %r3, 0
	addi %r5, %r10, 0
	addi %r4, %r11, 0
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
	or %r22, %r6, %r7
	addi %r23, %r23, 8
	addi %r24, %r24, -1
	addi %r6, %r22, -1
	and %r24, %r24, %r6
	cmpldi %cr0, %r24, 0
	bne %cr0, 223b
	ld %r5, 200(%r31)
	or %r5, %r5, %r22
	std %r5, 200(%r31)
	ld %r5, 200(%r31)
	cmpldi %cr0, %r5, 0
	beq %cr0, 225f
	ld %r4, 32(%r31)
	ld %r5, 152(%r31)
	std %r5, 0(%r4)
	li %r3, 2
	b 226f
225:
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
227:
	add %r5, %r5, %r5
	addi %r5, %r5, 1
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 227b
	std %r5, 192(%r31)
	ld %r12, 136(%r31)
	ld %r6, 24(%r31)
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
228:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 228b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
229:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 229b
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
230:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 230b
	li %r0, 1
	stw %r0, 0(%r5)
	rldicr %r4, %r11, 6, 57
231:
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	addi %r17, %r11, 0
	li %r20, 0
232:
	lwz %r0, 0(%r15)
	add %r0, %r0, %r0
	add %r0, %r0, %r20
	stw %r0, 0(%r14)
	rldicl %r20, %r0, 32, 32
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 232b
	stw %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
233:
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
	bne %cr0, 233b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	addi %r17, %r11, 0
234:
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
	bne %cr0, 234b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 231b
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
235:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 235b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
236:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 236b
237:
	ld %r17, 0(%r6)
	addi %r6, %r6, 8
	ld %r19, 0(%r7)
	ld %r20, 0(%r8)
	mulld %r18, %r17, %r19
	mulhdu %r19, %r17, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r3, 0(%r10)
	mulld %r22, %r3, %r12
	addi %r22, %r22, 2
	mulld %r22, %r22, %r12
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
	beq %cr0, 238f
240:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r3, %r3, 8
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 240b
	b 239f
238:
239:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 241f
243:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	ld %r19, 16(%r14)
	addc %r18, %r18, %r19
	ld %r19, 16(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 16(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 8(%r14)
	ld %r19, 24(%r14)
	addc %r18, %r18, %r19
	ld %r19, 24(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 24(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 16(%r14)
	ld %r19, 32(%r14)
	addc %r18, %r18, %r19
	ld %r19, 32(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 32(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r3, %r3, 32
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 243b
	b 242f
241:
242:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	li %r19, 0
	addze %r19, %r19
	addc %r18, %r18, %r22
	addze %r19, %r19
	std %r18, 0(%r14)
	std %r19, 8(%r14)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 237b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
244:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 244b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
245:
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
	bne %cr0, 245b
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
246:
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
	bne %cr0, 246b
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
247:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 247b
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r6, 0
	li %r4, 1
248:
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
	bne %cr0, 248b
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
249:
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
	bne %cr0, 249b
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
250:
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
	bne %cr0, 250b
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
251:
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
	bne %cr0, 251b
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
252:
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
	bne %cr0, 252b
	rldicl %r6, %r5, 63, 1
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	li %r3, 0
	std %r3, 176(%r31)
	li %r3, 4
	std %r3, 160(%r31)
253:
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
	beq %cr0, 254f
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
256:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 256b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
257:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 257b
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
258:
	ld %r3, 0(%r5)
	or %r24, %r24, %r3
	addi %r5, %r5, 8
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 258b
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
259:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 259b
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
260:
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
	bne %cr0, 260b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	cmpldi %cr0, %r24, 0
	beq %cr0, 261f
	cmpldi %cr0, %r20, 0
	beq %cr0, 263f
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
265:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 265b
266:
	ld %r17, 0(%r6)
	addi %r6, %r6, 8
	ld %r19, 0(%r7)
	ld %r20, 0(%r8)
	mulld %r18, %r17, %r19
	mulhdu %r19, %r17, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r3, 0(%r10)
	mulld %r22, %r3, %r12
	addi %r22, %r22, 2
	mulld %r22, %r22, %r12
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
	beq %cr0, 267f
269:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r3, %r3, 8
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 269b
	b 268f
267:
268:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 270f
272:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	ld %r19, 16(%r14)
	addc %r18, %r18, %r19
	ld %r19, 16(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 16(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 8(%r14)
	ld %r19, 24(%r14)
	addc %r18, %r18, %r19
	ld %r19, 24(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 24(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 16(%r14)
	ld %r19, 32(%r14)
	addc %r18, %r18, %r19
	ld %r19, 32(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 32(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r3, %r3, 32
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 272b
	b 271f
270:
271:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	li %r19, 0
	addze %r19, %r19
	addc %r18, %r18, %r22
	addze %r19, %r19
	std %r18, 0(%r14)
	std %r19, 8(%r14)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 266b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
273:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 273b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
274:
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
	bne %cr0, 274b
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
	beq %cr0, 275f
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
	b 276f
275:
	li %r3, 2
	std %r3, 160(%r31)
276:
	b 264f
263:
264:
	b 262f
261:
262:
	b 255f
254:
	li %r3, 0
	std %r3, 160(%r31)
255:
	ld %r3, 160(%r31)
	addi %r3, %r3, -4
	cmpldi %cr0, %r3, 0
	beq %cr0, 253b
	ld %r3, 160(%r31)
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	beq %cr0, 277f
	ld %r3, 160(%r31)
	cmpldi %cr0, %r3, 0
	beq %cr0, 279f
	ld %r4, 32(%r31)
	ld %r5, 152(%r31)
	std %r5, 0(%r4)
	li %r3, 2
	b 280f
279:
	ld %r4, 32(%r31)
	li %r5, 0
	std %r5, 0(%r4)
	li %r3, 0
280:
	b 278f
277:
	addi %r5, %r10, 0
	rldicl %r6, %r11, 63, 1
	addi %r6, %r6, -1
281:
	ld %r3, 0(%r5)
	ld %r4, 8(%r5)
	rldicl %r3, %r3, 63, 1
	rldicr %r4, %r4, 63, 0
	or %r3, %r3, %r4
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 281b
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
282:
	add %r5, %r5, %r5
	addi %r5, %r5, 1
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 282b
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
283:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 283b
	li %r0, 1
	stw %r0, 0(%r5)
	rldicr %r4, %r11, 6, 57
284:
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	addi %r17, %r11, 0
	li %r20, 0
285:
	lwz %r0, 0(%r15)
	add %r0, %r0, %r0
	add %r0, %r0, %r20
	stw %r0, 0(%r14)
	rldicl %r20, %r0, 32, 32
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 285b
	stw %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
286:
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
	bne %cr0, 286b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	addi %r17, %r11, 0
287:
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
	bne %cr0, 287b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 284b
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
288:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 288b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
289:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 289b
290:
	ld %r17, 0(%r6)
	addi %r6, %r6, 8
	ld %r19, 0(%r7)
	ld %r20, 0(%r8)
	mulld %r18, %r17, %r19
	mulhdu %r19, %r17, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r3, 0(%r10)
	mulld %r22, %r3, %r12
	addi %r22, %r22, 2
	mulld %r22, %r22, %r12
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
	beq %cr0, 291f
293:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r3, %r3, 8
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 293b
	b 292f
291:
292:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 294f
296:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	ld %r19, 16(%r14)
	addc %r18, %r18, %r19
	ld %r19, 16(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 16(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 8(%r14)
	ld %r19, 24(%r14)
	addc %r18, %r18, %r19
	ld %r19, 24(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 24(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 16(%r14)
	ld %r19, 32(%r14)
	addc %r18, %r18, %r19
	ld %r19, 32(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 32(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r3, %r3, 32
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 296b
	b 295f
294:
295:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	li %r19, 0
	addze %r19, %r19
	addc %r18, %r18, %r22
	addze %r19, %r19
	std %r18, 0(%r14)
	std %r19, 8(%r14)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 290b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
297:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 297b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
298:
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
	bne %cr0, 298b
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
299:
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
	bne %cr0, 299b
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
2100:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2100b
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r6, 0
	li %r4, 1
2101:
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
	bne %cr0, 2101b
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
2102:
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
	bne %cr0, 2102b
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
2103:
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
	bne %cr0, 2103b
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
2104:
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
	bne %cr0, 2104b
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
2105:
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
	bne %cr0, 2105b
	rldicl %r6, %r5, 63, 1
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	li %r3, 0
	std %r3, 176(%r31)
	li %r3, 4
	std %r3, 160(%r31)
2106:
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
	beq %cr0, 2107f
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
2109:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2109b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2110:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2110b
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
2111:
	ld %r3, 0(%r5)
	or %r24, %r24, %r3
	addi %r5, %r5, 8
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2111b
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
2112:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2112b
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
2113:
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
	bne %cr0, 2113b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	cmpldi %cr0, %r24, 0
	beq %cr0, 2114f
	cmpldi %cr0, %r20, 0
	beq %cr0, 2116f
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2118:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2118b
2119:
	ld %r17, 0(%r6)
	addi %r6, %r6, 8
	ld %r19, 0(%r7)
	ld %r20, 0(%r8)
	mulld %r18, %r17, %r19
	mulhdu %r19, %r17, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r3, 0(%r10)
	mulld %r22, %r3, %r12
	addi %r22, %r22, 2
	mulld %r22, %r22, %r12
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
	beq %cr0, 2120f
2122:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r3, %r3, 8
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 2122b
	b 2121f
2120:
2121:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2123f
2125:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	ld %r19, 16(%r14)
	addc %r18, %r18, %r19
	ld %r19, 16(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 16(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 8(%r14)
	ld %r19, 24(%r14)
	addc %r18, %r18, %r19
	ld %r19, 24(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 24(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 16(%r14)
	ld %r19, 32(%r14)
	addc %r18, %r18, %r19
	ld %r19, 32(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 32(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r3, %r3, 32
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 2125b
	b 2124f
2123:
2124:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	li %r19, 0
	addze %r19, %r19
	addc %r18, %r18, %r22
	addze %r19, %r19
	std %r18, 0(%r14)
	std %r19, 8(%r14)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2119b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2126:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2126b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2127:
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
	bne %cr0, 2127b
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
	beq %cr0, 2128f
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
	b 2129f
2128:
	li %r3, 2
	std %r3, 160(%r31)
2129:
	b 2117f
2116:
2117:
	b 2115f
2114:
2115:
	b 2108f
2107:
	li %r3, 0
	std %r3, 160(%r31)
2108:
	ld %r3, 160(%r31)
	addi %r3, %r3, -4
	cmpldi %cr0, %r3, 0
	beq %cr0, 2106b
	ld %r3, 160(%r31)
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	beq %cr0, 2130f
	ld %r3, 160(%r31)
	cmpldi %cr0, %r3, 0
	beq %cr0, 2132f
	ld %r4, 32(%r31)
	ld %r5, 152(%r31)
	std %r5, 0(%r4)
	li %r3, 2
	b 2133f
2132:
	ld %r4, 32(%r31)
	li %r5, 0
	std %r5, 0(%r4)
	li %r3, 0
2133:
	b 2131f
2130:
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
2134:
	add %r5, %r5, %r5
	addi %r5, %r5, 1
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 2134b
	std %r5, 192(%r31)
	ld %r12, 136(%r31)
	ld %r6, 24(%r31)
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2135:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2135b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2136:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2136b
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
2137:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2137b
	li %r0, 1
	stw %r0, 0(%r5)
	rldicr %r4, %r11, 6, 57
2138:
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	addi %r17, %r11, 0
	li %r20, 0
2139:
	lwz %r0, 0(%r15)
	add %r0, %r0, %r0
	add %r0, %r0, %r20
	stw %r0, 0(%r14)
	rldicl %r20, %r0, 32, 32
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2139b
	stw %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2140:
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
	bne %cr0, 2140b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	addi %r17, %r11, 0
2141:
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
	bne %cr0, 2141b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2138b
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
2142:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2142b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2143:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2143b
2144:
	ld %r17, 0(%r6)
	addi %r6, %r6, 8
	ld %r19, 0(%r7)
	ld %r20, 0(%r8)
	mulld %r18, %r17, %r19
	mulhdu %r19, %r17, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r3, 0(%r10)
	mulld %r22, %r3, %r12
	addi %r22, %r22, 2
	mulld %r22, %r22, %r12
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
	beq %cr0, 2145f
2147:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r3, %r3, 8
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 2147b
	b 2146f
2145:
2146:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2148f
2150:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	ld %r19, 16(%r14)
	addc %r18, %r18, %r19
	ld %r19, 16(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 16(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 8(%r14)
	ld %r19, 24(%r14)
	addc %r18, %r18, %r19
	ld %r19, 24(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 24(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 16(%r14)
	ld %r19, 32(%r14)
	addc %r18, %r18, %r19
	ld %r19, 32(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 32(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r3, %r3, 32
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 2150b
	b 2149f
2148:
2149:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	li %r19, 0
	addze %r19, %r19
	addc %r18, %r18, %r22
	addze %r19, %r19
	std %r18, 0(%r14)
	std %r19, 8(%r14)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2144b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2151:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2151b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2152:
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
	bne %cr0, 2152b
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
2153:
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
	bne %cr0, 2153b
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
2154:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2154b
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r6, 0
	li %r4, 1
2155:
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
	bne %cr0, 2155b
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
2156:
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
	bne %cr0, 2156b
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
2157:
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
	bne %cr0, 2157b
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
2158:
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
	bne %cr0, 2158b
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
2159:
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
	bne %cr0, 2159b
	rldicl %r6, %r5, 63, 1
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	li %r3, 0
	std %r3, 176(%r31)
	li %r3, 4
	std %r3, 160(%r31)
2160:
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
	beq %cr0, 2161f
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
2163:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2163b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2164:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2164b
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
2165:
	ld %r3, 0(%r5)
	or %r24, %r24, %r3
	addi %r5, %r5, 8
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2165b
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
2166:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2166b
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
2167:
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
	bne %cr0, 2167b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	cmpldi %cr0, %r24, 0
	beq %cr0, 2168f
	cmpldi %cr0, %r20, 0
	beq %cr0, 2170f
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2172:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2172b
2173:
	ld %r17, 0(%r6)
	addi %r6, %r6, 8
	ld %r19, 0(%r7)
	ld %r20, 0(%r8)
	mulld %r18, %r17, %r19
	mulhdu %r19, %r17, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r3, 0(%r10)
	mulld %r22, %r3, %r12
	addi %r22, %r22, 2
	mulld %r22, %r22, %r12
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
	beq %cr0, 2174f
2176:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r3, %r3, 8
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 2176b
	b 2175f
2174:
2175:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2177f
2179:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	ld %r19, 8(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 8(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 0(%r14)
	ld %r19, 16(%r14)
	addc %r18, %r18, %r19
	ld %r19, 16(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 16(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 8(%r14)
	ld %r19, 24(%r14)
	addc %r18, %r18, %r19
	ld %r19, 24(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 24(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 16(%r14)
	ld %r19, 32(%r14)
	addc %r18, %r18, %r19
	ld %r19, 32(%r15)
	mulld %r20, %r17, %r19
	mulhdu %r19, %r17, %r19
	addze %r19, %r19
	addc %r20, %r20, %r18
	addze %r18, %r19
	ld %r19, 32(%r3)
	addc %r22, %r22, %r20
	mulld %r20, %r0, %r19
	mulhdu %r19, %r0, %r19
	addze %r19, %r19
	addc %r20, %r20, %r22
	addze %r22, %r19
	std %r20, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r3, %r3, 32
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 2179b
	b 2178f
2177:
2178:
	ld %r19, 8(%r14)
	addc %r18, %r18, %r19
	li %r19, 0
	addze %r19, %r19
	addc %r18, %r18, %r22
	addze %r19, %r19
	std %r18, 0(%r14)
	std %r19, 8(%r14)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2173b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2180:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2180b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2181:
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
	bne %cr0, 2181b
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
	beq %cr0, 2182f
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
	b 2183f
2182:
	li %r3, 2
	std %r3, 160(%r31)
2183:
	b 2171f
2170:
2171:
	b 2169f
2168:
2169:
	b 2162f
2161:
	li %r3, 0
	std %r3, 160(%r31)
2162:
	ld %r3, 160(%r31)
	addi %r3, %r3, -4
	cmpldi %cr0, %r3, 0
	beq %cr0, 2160b
	ld %r3, 160(%r31)
	cmpldi %cr0, %r3, 0
	beq %cr0, 2184f
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	beq %cr0, 2186f
	ld %r4, 32(%r31)
	ld %r5, 152(%r31)
	std %r5, 0(%r4)
	li %r3, 2
	b 2187f
2186:
	ld %r4, 16(%r31)
	ld %r5, 24(%r31)
	add %r6, %r10, %r5
	addi %r6, %r6, -1
2188:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	addi %r6, %r6, -1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2188b
	ld %r4, 32(%r31)
	ld %r5, 152(%r31)
	std %r5, 0(%r4)
	li %r3, 1
2187:
	b 2185f
2184:
	ld %r4, 32(%r31)
	li %r5, 0
	std %r5, 0(%r4)
	li %r3, 0
2185:
2131:
278:
226:
220:
215:
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
