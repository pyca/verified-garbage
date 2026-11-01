// The functions of `src/cast5_cfb.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cast5_cfb64_encrypt:
	stdu %r1, -208(%r1)
	addi %r8, %r1, 32
	or %r10, %r4, %r4
	or %r4, %r5, %r5
	or %r5, %r6, %r6
	or %r6, %r7, %r7
	or %r7, %r8, %r8
	addi %r10, %r10, -12
	cmpldi %cr0, %r10, 0
	beq %cr0, 20f
	mflr %r0
	std %r0, 152(%r7)
	std %r29, 128(%r7)
	std %r30, 136(%r7)
	std %r31, 144(%r7)
	or %r29, %r4, %r4
	or %r30, %r6, %r6
	or %r31, %r4, %r4
	or %r6, %r5, %r5
	or %r5, %r7, %r7
	lwz %r8, 0(%r31)
	stw %r8, 160(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 164(%r5)
	or %r31, %r6, %r6
	cmpldi %cr0, %r30, 0
	beq %cr0, 22f
24:
	lwz %r8, 160(%r5)
	stw %r8, 0(%r5)
	lwz %r8, 164(%r5)
	stw %r8, 4(%r5)
	or %r6, %r29, %r29
	or %r7, %r30, %r30
	std %r14, 8(%r5)
	std %r15, 16(%r5)
	std %r16, 24(%r5)
	std %r17, 32(%r5)
	std %r18, 40(%r5)
	std %r19, 48(%r5)
	std %r20, 56(%r5)
	std %r21, 64(%r5)
	std %r22, 72(%r5)
	std %r23, 80(%r5)
	std %r24, 88(%r5)
	std %r25, 96(%r5)
	std %r26, 104(%r5)
	std %r27, 112(%r5)
	std %r28, 120(%r5)
	bcl 20, 31, 2f
2:
	mflr %r27
	addis %r27, %r27, ({VG_CAST5_S1234}
	addi %r27, %r27, ({VG_CAST5_S1234}
	li %r26, 255
	li %r0, 0
	li %r4, 16
	lwbrx %r8, %r5, %r0
	addi %r24, %r5, 4
	lwbrx %r9, %r24, %r0
	or %r10, %r3, %r3
	or %r11, %r4, %r4
	li %r12, 1
25:
	cmpldi %cr0, %r12, 0
	beq %cr0, 26f
	addi %r24, %r12, -1
	cmpldi %cr0, %r24, 0
	beq %cr0, 28f
	lwz %r28, 0(%r10)
	xor %r28, %r28, %r9
	b 29f
28:
	lwz %r28, 0(%r10)
	add %r28, %r28, %r9
29:
	b 27f
26:
	lwz %r28, 0(%r10)
	subf %r28, %r9, %r28
27:
	lwz %r29, 64(%r10)
	rldicr %r30, %r29, 63, 0
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 1, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	rldicr %r30, %r29, 62, 1
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 2, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	rldicr %r30, %r29, 61, 2
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 4, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	rldicr %r30, %r29, 60, 3
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 8, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	rldicr %r30, %r29, 59, 4
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 16, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	and %r14, %r28, %r26
	rlwinm %r15, %r28, 24, 8, 31
	and %r15, %r15, %r26
	rlwinm %r16, %r28, 16, 16, 31
	and %r16, %r16, %r26
	rlwinm %r17, %r28, 8, 24, 31
	or %r23, %r27, %r27
	li %r22, 0
	li %r18, 0
	li %r19, 0
	li %r20, 0
	li %r21, 0
210:
	lwz %r25, 0(%r23)
	xor %r24, %r14, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r18, %r18, %r25
	lwz %r25, 4(%r23)
	xor %r24, %r15, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r19, %r19, %r25
	lwz %r25, 8(%r23)
	xor %r24, %r16, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r20, %r20, %r25
	lwz %r25, 12(%r23)
	xor %r24, %r17, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r21, %r21, %r25
	addi %r23, %r23, 16
	addi %r22, %r22, 1
	addi %r24, %r22, -256
	cmpldi %cr0, %r24, 0
	bne %cr0, 210b
	cmpldi %cr0, %r12, 0
	beq %cr0, 211f
	addi %r24, %r12, -1
	cmpldi %cr0, %r24, 0
	beq %cr0, 213f
	subf %r28, %r20, %r21
	add %r28, %r28, %r19
	xor %r28, %r28, %r18
	b 214f
213:
	xor %r28, %r21, %r20
	subf %r28, %r19, %r28
	add %r28, %r28, %r18
214:
	b 212f
211:
	add %r28, %r21, %r20
	xor %r28, %r28, %r19
	subf %r28, %r18, %r28
212:
	xor %r28, %r28, %r8
	or %r8, %r9, %r9
	or %r9, %r28, %r28
	addi %r10, %r10, 4
	addi %r24, %r12, -2
	cmpldi %cr0, %r24, 0
	beq %cr0, 215f
	addi %r12, %r12, 1
	b 216f
215:
	li %r12, 0
216:
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 25b
	stwbrx %r9, %r5, %r0
	addi %r24, %r5, 4
	stwbrx %r8, %r24, %r0
	ld %r14, 8(%r5)
	ld %r15, 16(%r5)
	ld %r16, 24(%r5)
	ld %r17, 32(%r5)
	ld %r18, 40(%r5)
	ld %r19, 48(%r5)
	ld %r20, 56(%r5)
	ld %r21, 64(%r5)
	ld %r22, 72(%r5)
	ld %r23, 80(%r5)
	ld %r24, 88(%r5)
	ld %r25, 96(%r5)
	ld %r26, 104(%r5)
	ld %r27, 112(%r5)
	ld %r28, 120(%r5)
	or %r29, %r6, %r6
	or %r30, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 0(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 4(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 0(%r31)
	stw %r8, 160(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 164(%r5)
	addi %r31, %r31, 8
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 24b
	b 23f
22:
23:
	or %r31, %r29, %r29
	lwz %r8, 160(%r5)
	stw %r8, 0(%r31)
	lwz %r8, 164(%r5)
	stw %r8, 4(%r31)
	ld %r29, 128(%r5)
	ld %r30, 136(%r5)
	ld %r31, 144(%r5)
	ld %r0, 152(%r5)
	mtlr %r0
	b 21f
20:
	mflr %r0
	std %r0, 152(%r7)
	std %r29, 128(%r7)
	std %r30, 136(%r7)
	std %r31, 144(%r7)
	or %r29, %r4, %r4
	or %r30, %r6, %r6
	or %r31, %r4, %r4
	or %r6, %r5, %r5
	or %r5, %r7, %r7
	lwz %r8, 0(%r31)
	stw %r8, 160(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 164(%r5)
	or %r31, %r6, %r6
	cmpldi %cr0, %r30, 0
	beq %cr0, 217f
219:
	lwz %r8, 160(%r5)
	stw %r8, 0(%r5)
	lwz %r8, 164(%r5)
	stw %r8, 4(%r5)
	or %r6, %r29, %r29
	or %r7, %r30, %r30
	std %r14, 8(%r5)
	std %r15, 16(%r5)
	std %r16, 24(%r5)
	std %r17, 32(%r5)
	std %r18, 40(%r5)
	std %r19, 48(%r5)
	std %r20, 56(%r5)
	std %r21, 64(%r5)
	std %r22, 72(%r5)
	std %r23, 80(%r5)
	std %r24, 88(%r5)
	std %r25, 96(%r5)
	std %r26, 104(%r5)
	std %r27, 112(%r5)
	std %r28, 120(%r5)
	bcl 20, 31, 2f
2:
	mflr %r27
	addis %r27, %r27, ({VG_CAST5_S1234}
	addi %r27, %r27, ({VG_CAST5_S1234}
	li %r26, 255
	li %r0, 0
	li %r4, 12
	lwbrx %r8, %r5, %r0
	addi %r24, %r5, 4
	lwbrx %r9, %r24, %r0
	or %r10, %r3, %r3
	or %r11, %r4, %r4
	li %r12, 1
220:
	cmpldi %cr0, %r12, 0
	beq %cr0, 221f
	addi %r24, %r12, -1
	cmpldi %cr0, %r24, 0
	beq %cr0, 223f
	lwz %r28, 0(%r10)
	xor %r28, %r28, %r9
	b 224f
223:
	lwz %r28, 0(%r10)
	add %r28, %r28, %r9
224:
	b 222f
221:
	lwz %r28, 0(%r10)
	subf %r28, %r9, %r28
222:
	lwz %r29, 64(%r10)
	rldicr %r30, %r29, 63, 0
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 1, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	rldicr %r30, %r29, 62, 1
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 2, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	rldicr %r30, %r29, 61, 2
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 4, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	rldicr %r30, %r29, 60, 3
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 8, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	rldicr %r30, %r29, 59, 4
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 16, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	and %r14, %r28, %r26
	rlwinm %r15, %r28, 24, 8, 31
	and %r15, %r15, %r26
	rlwinm %r16, %r28, 16, 16, 31
	and %r16, %r16, %r26
	rlwinm %r17, %r28, 8, 24, 31
	or %r23, %r27, %r27
	li %r22, 0
	li %r18, 0
	li %r19, 0
	li %r20, 0
	li %r21, 0
225:
	lwz %r25, 0(%r23)
	xor %r24, %r14, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r18, %r18, %r25
	lwz %r25, 4(%r23)
	xor %r24, %r15, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r19, %r19, %r25
	lwz %r25, 8(%r23)
	xor %r24, %r16, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r20, %r20, %r25
	lwz %r25, 12(%r23)
	xor %r24, %r17, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r21, %r21, %r25
	addi %r23, %r23, 16
	addi %r22, %r22, 1
	addi %r24, %r22, -256
	cmpldi %cr0, %r24, 0
	bne %cr0, 225b
	cmpldi %cr0, %r12, 0
	beq %cr0, 226f
	addi %r24, %r12, -1
	cmpldi %cr0, %r24, 0
	beq %cr0, 228f
	subf %r28, %r20, %r21
	add %r28, %r28, %r19
	xor %r28, %r28, %r18
	b 229f
228:
	xor %r28, %r21, %r20
	subf %r28, %r19, %r28
	add %r28, %r28, %r18
229:
	b 227f
226:
	add %r28, %r21, %r20
	xor %r28, %r28, %r19
	subf %r28, %r18, %r28
227:
	xor %r28, %r28, %r8
	or %r8, %r9, %r9
	or %r9, %r28, %r28
	addi %r10, %r10, 4
	addi %r24, %r12, -2
	cmpldi %cr0, %r24, 0
	beq %cr0, 230f
	addi %r12, %r12, 1
	b 231f
230:
	li %r12, 0
231:
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 220b
	stwbrx %r9, %r5, %r0
	addi %r24, %r5, 4
	stwbrx %r8, %r24, %r0
	ld %r14, 8(%r5)
	ld %r15, 16(%r5)
	ld %r16, 24(%r5)
	ld %r17, 32(%r5)
	ld %r18, 40(%r5)
	ld %r19, 48(%r5)
	ld %r20, 56(%r5)
	ld %r21, 64(%r5)
	ld %r22, 72(%r5)
	ld %r23, 80(%r5)
	ld %r24, 88(%r5)
	ld %r25, 96(%r5)
	ld %r26, 104(%r5)
	ld %r27, 112(%r5)
	ld %r28, 120(%r5)
	or %r29, %r6, %r6
	or %r30, %r7, %r7
	lwz %r8, 0(%r31)
	lwz %r9, 0(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 4(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	lwz %r8, 0(%r31)
	stw %r8, 160(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 164(%r5)
	addi %r31, %r31, 8
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 219b
	b 218f
217:
218:
	or %r31, %r29, %r29
	lwz %r8, 160(%r5)
	stw %r8, 0(%r31)
	lwz %r8, 164(%r5)
	stw %r8, 4(%r31)
	ld %r29, 128(%r5)
	ld %r30, 136(%r5)
	ld %r31, 144(%r5)
	ld %r0, 152(%r5)
	mtlr %r0
21:
	addi %r12, %r1, 32
	li %r11, 0
	std %r11, 0(%r12)
	std %r11, 8(%r12)
	std %r11, 16(%r12)
	std %r11, 24(%r12)
	std %r11, 32(%r12)
	std %r11, 40(%r12)
	std %r11, 48(%r12)
	std %r11, 56(%r12)
	std %r11, 64(%r12)
	std %r11, 72(%r12)
	std %r11, 80(%r12)
	std %r11, 88(%r12)
	std %r11, 96(%r12)
	std %r11, 104(%r12)
	std %r11, 112(%r12)
	std %r11, 120(%r12)
	std %r11, 128(%r12)
	std %r11, 136(%r12)
	std %r11, 144(%r12)
	std %r11, 152(%r12)
	std %r11, 160(%r12)
	std %r11, 168(%r12)
	addi %r1, %r1, 208
	blr

vg_cast5_cfb64_decrypt:
	stdu %r1, -208(%r1)
	addi %r8, %r1, 32
	or %r10, %r4, %r4
	or %r4, %r5, %r5
	or %r5, %r6, %r6
	or %r6, %r7, %r7
	or %r7, %r8, %r8
	addi %r10, %r10, -12
	cmpldi %cr0, %r10, 0
	beq %cr0, 20f
	mflr %r0
	std %r0, 152(%r7)
	std %r29, 128(%r7)
	std %r30, 136(%r7)
	std %r31, 144(%r7)
	or %r29, %r4, %r4
	or %r30, %r6, %r6
	or %r31, %r4, %r4
	or %r6, %r5, %r5
	or %r5, %r7, %r7
	lwz %r8, 0(%r31)
	stw %r8, 160(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 164(%r5)
	or %r31, %r6, %r6
	cmpldi %cr0, %r30, 0
	beq %cr0, 22f
24:
	lwz %r8, 160(%r5)
	stw %r8, 0(%r5)
	lwz %r8, 164(%r5)
	stw %r8, 4(%r5)
	or %r6, %r29, %r29
	or %r7, %r30, %r30
	std %r14, 8(%r5)
	std %r15, 16(%r5)
	std %r16, 24(%r5)
	std %r17, 32(%r5)
	std %r18, 40(%r5)
	std %r19, 48(%r5)
	std %r20, 56(%r5)
	std %r21, 64(%r5)
	std %r22, 72(%r5)
	std %r23, 80(%r5)
	std %r24, 88(%r5)
	std %r25, 96(%r5)
	std %r26, 104(%r5)
	std %r27, 112(%r5)
	std %r28, 120(%r5)
	bcl 20, 31, 2f
2:
	mflr %r27
	addis %r27, %r27, ({VG_CAST5_S1234}
	addi %r27, %r27, ({VG_CAST5_S1234}
	li %r26, 255
	li %r0, 0
	li %r4, 16
	lwbrx %r8, %r5, %r0
	addi %r24, %r5, 4
	lwbrx %r9, %r24, %r0
	or %r10, %r3, %r3
	or %r11, %r4, %r4
	li %r12, 1
25:
	cmpldi %cr0, %r12, 0
	beq %cr0, 26f
	addi %r24, %r12, -1
	cmpldi %cr0, %r24, 0
	beq %cr0, 28f
	lwz %r28, 0(%r10)
	xor %r28, %r28, %r9
	b 29f
28:
	lwz %r28, 0(%r10)
	add %r28, %r28, %r9
29:
	b 27f
26:
	lwz %r28, 0(%r10)
	subf %r28, %r9, %r28
27:
	lwz %r29, 64(%r10)
	rldicr %r30, %r29, 63, 0
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 1, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	rldicr %r30, %r29, 62, 1
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 2, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	rldicr %r30, %r29, 61, 2
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 4, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	rldicr %r30, %r29, 60, 3
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 8, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	rldicr %r30, %r29, 59, 4
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 16, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	and %r14, %r28, %r26
	rlwinm %r15, %r28, 24, 8, 31
	and %r15, %r15, %r26
	rlwinm %r16, %r28, 16, 16, 31
	and %r16, %r16, %r26
	rlwinm %r17, %r28, 8, 24, 31
	or %r23, %r27, %r27
	li %r22, 0
	li %r18, 0
	li %r19, 0
	li %r20, 0
	li %r21, 0
210:
	lwz %r25, 0(%r23)
	xor %r24, %r14, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r18, %r18, %r25
	lwz %r25, 4(%r23)
	xor %r24, %r15, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r19, %r19, %r25
	lwz %r25, 8(%r23)
	xor %r24, %r16, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r20, %r20, %r25
	lwz %r25, 12(%r23)
	xor %r24, %r17, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r21, %r21, %r25
	addi %r23, %r23, 16
	addi %r22, %r22, 1
	addi %r24, %r22, -256
	cmpldi %cr0, %r24, 0
	bne %cr0, 210b
	cmpldi %cr0, %r12, 0
	beq %cr0, 211f
	addi %r24, %r12, -1
	cmpldi %cr0, %r24, 0
	beq %cr0, 213f
	subf %r28, %r20, %r21
	add %r28, %r28, %r19
	xor %r28, %r28, %r18
	b 214f
213:
	xor %r28, %r21, %r20
	subf %r28, %r19, %r28
	add %r28, %r28, %r18
214:
	b 212f
211:
	add %r28, %r21, %r20
	xor %r28, %r28, %r19
	subf %r28, %r18, %r28
212:
	xor %r28, %r28, %r8
	or %r8, %r9, %r9
	or %r9, %r28, %r28
	addi %r10, %r10, 4
	addi %r24, %r12, -2
	cmpldi %cr0, %r24, 0
	beq %cr0, 215f
	addi %r12, %r12, 1
	b 216f
215:
	li %r12, 0
216:
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 25b
	stwbrx %r9, %r5, %r0
	addi %r24, %r5, 4
	stwbrx %r8, %r24, %r0
	ld %r14, 8(%r5)
	ld %r15, 16(%r5)
	ld %r16, 24(%r5)
	ld %r17, 32(%r5)
	ld %r18, 40(%r5)
	ld %r19, 48(%r5)
	ld %r20, 56(%r5)
	ld %r21, 64(%r5)
	ld %r22, 72(%r5)
	ld %r23, 80(%r5)
	ld %r24, 88(%r5)
	ld %r25, 96(%r5)
	ld %r26, 104(%r5)
	ld %r27, 112(%r5)
	ld %r28, 120(%r5)
	or %r29, %r6, %r6
	or %r30, %r7, %r7
	lwz %r8, 0(%r31)
	stw %r8, 160(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 164(%r5)
	lwz %r8, 0(%r31)
	lwz %r9, 0(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 4(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	addi %r31, %r31, 8
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 24b
	b 23f
22:
23:
	or %r31, %r29, %r29
	lwz %r8, 160(%r5)
	stw %r8, 0(%r31)
	lwz %r8, 164(%r5)
	stw %r8, 4(%r31)
	ld %r29, 128(%r5)
	ld %r30, 136(%r5)
	ld %r31, 144(%r5)
	ld %r0, 152(%r5)
	mtlr %r0
	b 21f
20:
	mflr %r0
	std %r0, 152(%r7)
	std %r29, 128(%r7)
	std %r30, 136(%r7)
	std %r31, 144(%r7)
	or %r29, %r4, %r4
	or %r30, %r6, %r6
	or %r31, %r4, %r4
	or %r6, %r5, %r5
	or %r5, %r7, %r7
	lwz %r8, 0(%r31)
	stw %r8, 160(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 164(%r5)
	or %r31, %r6, %r6
	cmpldi %cr0, %r30, 0
	beq %cr0, 217f
219:
	lwz %r8, 160(%r5)
	stw %r8, 0(%r5)
	lwz %r8, 164(%r5)
	stw %r8, 4(%r5)
	or %r6, %r29, %r29
	or %r7, %r30, %r30
	std %r14, 8(%r5)
	std %r15, 16(%r5)
	std %r16, 24(%r5)
	std %r17, 32(%r5)
	std %r18, 40(%r5)
	std %r19, 48(%r5)
	std %r20, 56(%r5)
	std %r21, 64(%r5)
	std %r22, 72(%r5)
	std %r23, 80(%r5)
	std %r24, 88(%r5)
	std %r25, 96(%r5)
	std %r26, 104(%r5)
	std %r27, 112(%r5)
	std %r28, 120(%r5)
	bcl 20, 31, 2f
2:
	mflr %r27
	addis %r27, %r27, ({VG_CAST5_S1234}
	addi %r27, %r27, ({VG_CAST5_S1234}
	li %r26, 255
	li %r0, 0
	li %r4, 12
	lwbrx %r8, %r5, %r0
	addi %r24, %r5, 4
	lwbrx %r9, %r24, %r0
	or %r10, %r3, %r3
	or %r11, %r4, %r4
	li %r12, 1
220:
	cmpldi %cr0, %r12, 0
	beq %cr0, 221f
	addi %r24, %r12, -1
	cmpldi %cr0, %r24, 0
	beq %cr0, 223f
	lwz %r28, 0(%r10)
	xor %r28, %r28, %r9
	b 224f
223:
	lwz %r28, 0(%r10)
	add %r28, %r28, %r9
224:
	b 222f
221:
	lwz %r28, 0(%r10)
	subf %r28, %r9, %r28
222:
	lwz %r29, 64(%r10)
	rldicr %r30, %r29, 63, 0
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 1, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	rldicr %r30, %r29, 62, 1
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 2, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	rldicr %r30, %r29, 61, 2
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 4, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	rldicr %r30, %r29, 60, 3
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 8, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	rldicr %r30, %r29, 59, 4
	rldicl %r30, %r30, 1, 63
	addi %r30, %r30, -1
	rlwinm %r24, %r28, 16, 0, 31
	xor %r25, %r28, %r24
	and %r25, %r25, %r30
	xor %r28, %r24, %r25
	and %r14, %r28, %r26
	rlwinm %r15, %r28, 24, 8, 31
	and %r15, %r15, %r26
	rlwinm %r16, %r28, 16, 16, 31
	and %r16, %r16, %r26
	rlwinm %r17, %r28, 8, 24, 31
	or %r23, %r27, %r27
	li %r22, 0
	li %r18, 0
	li %r19, 0
	li %r20, 0
	li %r21, 0
225:
	lwz %r25, 0(%r23)
	xor %r24, %r14, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r18, %r18, %r25
	lwz %r25, 4(%r23)
	xor %r24, %r15, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r19, %r19, %r25
	lwz %r25, 8(%r23)
	xor %r24, %r16, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r20, %r20, %r25
	lwz %r25, 12(%r23)
	xor %r24, %r17, %r22
	addi %r24, %r24, -1
	rldicl %r24, %r24, 1, 63
	subf %r24, %r24, %r0
	and %r25, %r25, %r24
	or %r21, %r21, %r25
	addi %r23, %r23, 16
	addi %r22, %r22, 1
	addi %r24, %r22, -256
	cmpldi %cr0, %r24, 0
	bne %cr0, 225b
	cmpldi %cr0, %r12, 0
	beq %cr0, 226f
	addi %r24, %r12, -1
	cmpldi %cr0, %r24, 0
	beq %cr0, 228f
	subf %r28, %r20, %r21
	add %r28, %r28, %r19
	xor %r28, %r28, %r18
	b 229f
228:
	xor %r28, %r21, %r20
	subf %r28, %r19, %r28
	add %r28, %r28, %r18
229:
	b 227f
226:
	add %r28, %r21, %r20
	xor %r28, %r28, %r19
	subf %r28, %r18, %r28
227:
	xor %r28, %r28, %r8
	or %r8, %r9, %r9
	or %r9, %r28, %r28
	addi %r10, %r10, 4
	addi %r24, %r12, -2
	cmpldi %cr0, %r24, 0
	beq %cr0, 230f
	addi %r12, %r12, 1
	b 231f
230:
	li %r12, 0
231:
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 220b
	stwbrx %r9, %r5, %r0
	addi %r24, %r5, 4
	stwbrx %r8, %r24, %r0
	ld %r14, 8(%r5)
	ld %r15, 16(%r5)
	ld %r16, 24(%r5)
	ld %r17, 32(%r5)
	ld %r18, 40(%r5)
	ld %r19, 48(%r5)
	ld %r20, 56(%r5)
	ld %r21, 64(%r5)
	ld %r22, 72(%r5)
	ld %r23, 80(%r5)
	ld %r24, 88(%r5)
	ld %r25, 96(%r5)
	ld %r26, 104(%r5)
	ld %r27, 112(%r5)
	ld %r28, 120(%r5)
	or %r29, %r6, %r6
	or %r30, %r7, %r7
	lwz %r8, 0(%r31)
	stw %r8, 160(%r5)
	lwz %r8, 4(%r31)
	stw %r8, 164(%r5)
	lwz %r8, 0(%r31)
	lwz %r9, 0(%r5)
	xor %r8, %r8, %r9
	stw %r8, 0(%r31)
	lwz %r8, 4(%r31)
	lwz %r9, 4(%r5)
	xor %r8, %r8, %r9
	stw %r8, 4(%r31)
	addi %r31, %r31, 8
	addi %r30, %r30, -1
	cmpldi %cr0, %r30, 0
	bne %cr0, 219b
	b 218f
217:
218:
	or %r31, %r29, %r29
	lwz %r8, 160(%r5)
	stw %r8, 0(%r31)
	lwz %r8, 164(%r5)
	stw %r8, 4(%r31)
	ld %r29, 128(%r5)
	ld %r30, 136(%r5)
	ld %r31, 144(%r5)
	ld %r0, 152(%r5)
	mtlr %r0
21:
	addi %r12, %r1, 32
	li %r11, 0
	std %r11, 0(%r12)
	std %r11, 8(%r12)
	std %r11, 16(%r12)
	std %r11, 24(%r12)
	std %r11, 32(%r12)
	std %r11, 40(%r12)
	std %r11, 48(%r12)
	std %r11, 56(%r12)
	std %r11, 64(%r12)
	std %r11, 72(%r12)
	std %r11, 80(%r12)
	std %r11, 88(%r12)
	std %r11, 96(%r12)
	std %r11, 104(%r12)
	std %r11, 112(%r12)
	std %r11, 120(%r12)
	std %r11, 128(%r12)
	std %r11, 136(%r12)
	std %r11, 144(%r12)
	std %r11, 152(%r12)
	std %r11, 160(%r12)
	std %r11, 168(%r12)
	addi %r1, %r1, 208
	blr
