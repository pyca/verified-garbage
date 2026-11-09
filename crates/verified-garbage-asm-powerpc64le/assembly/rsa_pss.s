// The functions of `src/rsa_pss.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pss_verify_precomputed:
	stdu %r1, -256(%r1)
	addi %r11, %r1, 0
	ld %r11, 400(%r11)
	ld %r11, 40(%r11)
	addi %r12, %r11, -0
	cmpldi %cr0, %r12, 0
	beq %cr0, 20f
	addi %r12, %r11, -1
	cmpldi %cr0, %r12, 0
	beq %cr0, 22f
	addi %r12, %r11, -2
	cmpldi %cr0, %r12, 0
	beq %cr0, 24f
	addi %r12, %r11, -3
	cmpldi %cr0, %r12, 0
	beq %cr0, 26f
	addi %r12, %r11, -4
	cmpldi %cr0, %r12, 0
	beq %cr0, 28f
	addi %r12, %r11, -5
	cmpldi %cr0, %r12, 0
	beq %cr0, 210f
	addi %r12, %r11, -6
	cmpldi %cr0, %r12, 0
	beq %cr0, 212f
	addi %r12, %r1, 0
	std %r14, 112(%r12)
	std %r15, 120(%r12)
	std %r16, 128(%r12)
	std %r17, 136(%r12)
	std %r18, 144(%r12)
	std %r19, 152(%r12)
	std %r20, 160(%r12)
	std %r21, 168(%r12)
	std %r22, 176(%r12)
	std %r23, 184(%r12)
	std %r24, 192(%r12)
	std %r25, 200(%r12)
	std %r26, 208(%r12)
	std %r27, 216(%r12)
	std %r28, 224(%r12)
	std %r29, 232(%r12)
	mflr %r0
	std %r0, 240(%r12)
	ld %r20, 360(%r12)
	rlwinm %r20, %r20, 0, 0, 31
	ld %r14, 368(%r12)
	ld %r27, 376(%r12)
	ld %r22, 384(%r12)
	ld %r23, 392(%r12)
	or %r15, %r4, %r4
	or %r16, %r7, %r7
	ld %r19, 352(%r12)
	or %r24, %r5, %r5
	or %r25, %r6, %r6
	or %r26, %r9, %r9
	lbz %r9, 0(%r3)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r17, %r11, 1, 63
	li %r11, 0
	subf %r11, %r17, %r11
	li %r8, 255
	and %r11, %r11, %r8
	or %r18, %r10, %r11
	subf %r21, %r17, %r15
	addi %r21, %r21, -33
	cmpldi %cr0, %r9, 0
	beq %cr0, 214f
	subf %r3, %r17, %r15
	addi %r3, %r3, -34
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 216f
	cmpldi %cr0, %r20, 0
	beq %cr0, 218f
	li %r4, 0
	b 219f
218:
	or %r4, %r19, %r19
219:
	subf %r3, %r17, %r15
	addi %r3, %r3, -34
	subf %r3, %r4, %r3
	rldicl %r3, %r3, 1, 63
	rldicl %r5, %r4, 1, 63
	or %r3, %r3, %r5
	cmpldi %cr0, %r3, 0
	bne %cr0, 220f
	addi %r12, %r1, 0
	li %r4, 8192
	add %r4, %r14, %r4
	std %r4, 96(%r12)
	addi %r5, %r27, -1024
	std %r5, 104(%r12)
	addi %r3, %r14, 0
	or %r4, %r15, %r15
	or %r5, %r22, %r22
	or %r6, %r23, %r23
	or %r7, %r24, %r24
	or %r8, %r25, %r25
	or %r9, %r26, %r26
	or %r10, %r15, %r15
	bl {vg_rsa_public_precomputed_checked}
	add %r4, %r14, %r15
	addi %r4, %r4, -1
	lbz %r5, 0(%r4)
	li %r6, 188
	xor %r5, %r5, %r6
	add %r7, %r14, %r17
	lbz %r6, 0(%r7)
	li %r8, 255
	xor %r8, %r8, %r18
	and %r6, %r6, %r8
	or %r5, %r5, %r6
	lbz %r6, 0(%r14)
	li %r8, 0
	subf %r8, %r17, %r8
	and %r6, %r6, %r8
	or %r5, %r5, %r6
	stb %r5, 0(%r4)
	add %r26, %r14, %r17
	or %r27, %r21, %r21
	add %r24, %r26, %r21
	li %r25, 32
	li %r28, 0
	li %r29, 0
222:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r5, %r14, 1344
	or %r8, %r28, %r28
	stb %r8, 3(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 2(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 1(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 0(%r5)
	addi %r3, %r14, 1024
	or %r4, %r25, %r25
	li %r6, 4
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 408(%r9)
	ld %r9, 32(%r9)
	addi %r11, %r14, 1280
	add %r12, %r26, %r29
	subf %r8, %r29, %r27
	subf %r10, %r9, %r8
	rldicl %r6, %r10, 1, 63
	li %r7, 0
	subf %r6, %r6, %r7
	and %r10, %r10, %r6
	add %r9, %r9, %r10
223:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 223b
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 222b
	add %r4, %r14, %r17
	lbz %r5, 0(%r4)
	and %r5, %r5, %r18
	stb %r5, 0(%r4)
	add %r4, %r14, %r17
	or %r5, %r21, %r21
	li %r6, 0
	li %r7, 0
	addi %r7, %r7, -1
	li %r8, 0
	li %r9, 0
224:
	lbz %r10, 0(%r4)
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	addi %r12, %r11, -1
	and %r12, %r12, %r7
	and %r3, %r6, %r12
	or %r8, %r8, %r3
	and %r3, %r10, %r12
	or %r9, %r9, %r3
	li %r3, 0
	subf %r3, %r11, %r3
	and %r7, %r7, %r3
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 224b
	add %r4, %r14, %r15
	addi %r4, %r4, -1
	lbz %r24, 0(%r4)
	li %r3, 1
	xor %r9, %r9, %r3
	or %r24, %r24, %r9
	subf %r25, %r8, %r21
	addi %r25, %r25, -1
	cmpldi %cr0, %r20, 0
	beq %cr0, 225f
	b 226f
225:
	xor %r3, %r25, %r19
	or %r24, %r24, %r3
226:
	cmpldi %cr0, %r20, 0
	beq %cr0, 227f
	addi %r4, %r14, 2560
	li %r5, 2048
	li %r6, 0
229:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 229b
	or %r4, %r16, %r16
	addi %r5, %r14, 2568
	li %r6, 32
230:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 230b
	add %r4, %r14, %r17
	addi %r5, %r14, 2600
	or %r6, %r21, %r21
231:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 231b
	addi %r8, %r8, 1
	li %r9, 1
	li %r10, 10
232:
	addi %r4, %r14, 2600
	add %r5, %r4, %r9
	li %r6, 1
	and %r6, %r8, %r6
	li %r7, 0
	subf %r6, %r6, %r7
	or %r7, %r21, %r21
233:
	lbz %r11, 0(%r4)
	lbz %r3, 0(%r5)
	xor %r3, %r3, %r11
	and %r3, %r3, %r6
	xor %r11, %r11, %r3
	stb %r11, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 233b
	rldicl %r8, %r8, 63, 1
	add %r9, %r9, %r9
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 232b
	addi %r29, %r25, 40
	addi %r28, %r21, 55
	rldicl %r28, %r28, 57, 7
	addi %r28, %r28, 1
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 2560
	rldicr %r5, %r28, 7, 56
	li %r6, 0
234:
	xor %r7, %r6, %r29
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	li %r12, 0
	subf %r7, %r7, %r12
	li %r8, 128
	and %r7, %r7, %r8
	lbz %r8, 0(%r4)
	or %r8, %r8, %r7
	stb %r8, 0(%r4)
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 234b
	addi %r26, %r14, 4432
	rldicl %r8, %r29, 3, 61
	li %r11, 176
	stdbrx %r8, %r26, %r11
	add %r8, %r29, %r29
	add %r8, %r8, %r8
	add %r8, %r8, %r8
	li %r11, 184
	stdbrx %r8, %r26, %r11
	addi %r27, %r29, 16
	rldicl %r27, %r27, 57, 7
	addi %r4, %r14, 2672
	li %r6, 0
	or %r9, %r28, %r28
235:
	xor %r7, %r6, %r27
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	li %r12, 0
	subf %r7, %r7, %r12
	addi %r5, %r14, 4608
	li %r10, 16
236:
	lbz %r8, 0(%r5)
	and %r8, %r8, %r7
	lbz %r11, 0(%r4)
	or %r11, %r11, %r8
	stb %r11, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 236b
	addi %r4, %r4, 112
	addi %r6, %r6, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 235b
	li %r26, 0
237:
	addi %r3, %r14, 1024
	rldicr %r4, %r26, 7, 56
	add %r4, %r4, %r14
	addi %r4, %r4, 2560
	li %r5, 1
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 24(%r12)
	mtctr %r12
	bctrl
	xor %r3, %r26, %r27
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	li %r12, 0
	subf %r3, %r3, %r12
	addi %r4, %r14, 1024
	addi %r5, %r14, 4800
	li %r6, 64
238:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	and %r7, %r7, %r3
	xor %r8, %r8, %r7
	stb %r8, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 238b
	addi %r26, %r26, 1
	addi %r28, %r28, -1
	cmpldi %cr0, %r28, 0
	bne %cr0, 237b
	addi %r3, %r14, 4800
	addi %r4, %r14, 1280
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 32(%r12)
	mtctr %r12
	bctrl
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	addi %r5, %r14, 1280
	li %r6, 32
239:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 239b
	addi %r3, %r24, -1
	rldicl %r3, %r3, 1, 63
	b 228f
227:
	addi %r4, %r14, 2560
	li %r5, 8
	li %r6, 0
240:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 240b
	or %r4, %r16, %r16
	addi %r5, %r14, 2568
	li %r6, 32
241:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 241b
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	subf %r4, %r19, %r4
	addi %r5, %r14, 2600
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 242f
	b 243f
242:
244:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 244b
243:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	li %r4, 0
	addi %r5, %r14, 2560
	addi %r6, %r19, 40
	addi %r3, %r14, 1024
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r19, 40
	addi %r3, %r14, 1024
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	addi %r5, %r14, 1280
	li %r6, 32
245:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 245b
	addi %r3, %r24, -1
	rldicl %r3, %r3, 1, 63
228:
	b 221f
220:
	li %r3, 0
221:
	b 217f
216:
	li %r3, 0
217:
	b 215f
214:
	li %r3, 0
215:
	addi %r12, %r1, 0
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r14, 112(%r12)
	ld %r15, 120(%r12)
	ld %r16, 128(%r12)
	ld %r17, 136(%r12)
	ld %r18, 144(%r12)
	ld %r19, 152(%r12)
	ld %r20, 160(%r12)
	ld %r21, 168(%r12)
	ld %r22, 176(%r12)
	ld %r23, 184(%r12)
	ld %r24, 192(%r12)
	ld %r25, 200(%r12)
	ld %r26, 208(%r12)
	ld %r27, 216(%r12)
	ld %r28, 224(%r12)
	ld %r29, 232(%r12)
	b 213f
212:
	addi %r12, %r1, 0
	std %r14, 112(%r12)
	std %r15, 120(%r12)
	std %r16, 128(%r12)
	std %r17, 136(%r12)
	std %r18, 144(%r12)
	std %r19, 152(%r12)
	std %r20, 160(%r12)
	std %r21, 168(%r12)
	std %r22, 176(%r12)
	std %r23, 184(%r12)
	std %r24, 192(%r12)
	std %r25, 200(%r12)
	std %r26, 208(%r12)
	std %r27, 216(%r12)
	std %r28, 224(%r12)
	std %r29, 232(%r12)
	mflr %r0
	std %r0, 240(%r12)
	ld %r20, 360(%r12)
	rlwinm %r20, %r20, 0, 0, 31
	ld %r14, 368(%r12)
	ld %r27, 376(%r12)
	ld %r22, 384(%r12)
	ld %r23, 392(%r12)
	or %r15, %r4, %r4
	or %r16, %r7, %r7
	ld %r19, 352(%r12)
	or %r24, %r5, %r5
	or %r25, %r6, %r6
	or %r26, %r9, %r9
	lbz %r9, 0(%r3)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r17, %r11, 1, 63
	li %r11, 0
	subf %r11, %r17, %r11
	li %r8, 255
	and %r11, %r11, %r8
	or %r18, %r10, %r11
	subf %r21, %r17, %r15
	addi %r21, %r21, -29
	cmpldi %cr0, %r9, 0
	beq %cr0, 246f
	subf %r3, %r17, %r15
	addi %r3, %r3, -30
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 248f
	cmpldi %cr0, %r20, 0
	beq %cr0, 250f
	li %r4, 0
	b 251f
250:
	or %r4, %r19, %r19
251:
	subf %r3, %r17, %r15
	addi %r3, %r3, -30
	subf %r3, %r4, %r3
	rldicl %r3, %r3, 1, 63
	rldicl %r5, %r4, 1, 63
	or %r3, %r3, %r5
	cmpldi %cr0, %r3, 0
	bne %cr0, 252f
	addi %r12, %r1, 0
	li %r4, 8192
	add %r4, %r14, %r4
	std %r4, 96(%r12)
	addi %r5, %r27, -1024
	std %r5, 104(%r12)
	addi %r3, %r14, 0
	or %r4, %r15, %r15
	or %r5, %r22, %r22
	or %r6, %r23, %r23
	or %r7, %r24, %r24
	or %r8, %r25, %r25
	or %r9, %r26, %r26
	or %r10, %r15, %r15
	bl {vg_rsa_public_precomputed_checked}
	add %r4, %r14, %r15
	addi %r4, %r4, -1
	lbz %r5, 0(%r4)
	li %r6, 188
	xor %r5, %r5, %r6
	add %r7, %r14, %r17
	lbz %r6, 0(%r7)
	li %r8, 255
	xor %r8, %r8, %r18
	and %r6, %r6, %r8
	or %r5, %r5, %r6
	lbz %r6, 0(%r14)
	li %r8, 0
	subf %r8, %r17, %r8
	and %r6, %r6, %r8
	or %r5, %r5, %r6
	stb %r5, 0(%r4)
	add %r26, %r14, %r17
	or %r27, %r21, %r21
	add %r24, %r26, %r21
	li %r25, 28
	li %r28, 0
	li %r29, 0
254:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r5, %r14, 1344
	or %r8, %r28, %r28
	stb %r8, 3(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 2(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 1(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 0(%r5)
	addi %r3, %r14, 1024
	or %r4, %r25, %r25
	li %r6, 4
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 408(%r9)
	ld %r9, 32(%r9)
	addi %r11, %r14, 1280
	add %r12, %r26, %r29
	subf %r8, %r29, %r27
	subf %r10, %r9, %r8
	rldicl %r6, %r10, 1, 63
	li %r7, 0
	subf %r6, %r6, %r7
	and %r10, %r10, %r6
	add %r9, %r9, %r10
255:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 255b
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 254b
	add %r4, %r14, %r17
	lbz %r5, 0(%r4)
	and %r5, %r5, %r18
	stb %r5, 0(%r4)
	add %r4, %r14, %r17
	or %r5, %r21, %r21
	li %r6, 0
	li %r7, 0
	addi %r7, %r7, -1
	li %r8, 0
	li %r9, 0
256:
	lbz %r10, 0(%r4)
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	addi %r12, %r11, -1
	and %r12, %r12, %r7
	and %r3, %r6, %r12
	or %r8, %r8, %r3
	and %r3, %r10, %r12
	or %r9, %r9, %r3
	li %r3, 0
	subf %r3, %r11, %r3
	and %r7, %r7, %r3
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 256b
	add %r4, %r14, %r15
	addi %r4, %r4, -1
	lbz %r24, 0(%r4)
	li %r3, 1
	xor %r9, %r9, %r3
	or %r24, %r24, %r9
	subf %r25, %r8, %r21
	addi %r25, %r25, -1
	cmpldi %cr0, %r20, 0
	beq %cr0, 257f
	b 258f
257:
	xor %r3, %r25, %r19
	or %r24, %r24, %r3
258:
	cmpldi %cr0, %r20, 0
	beq %cr0, 259f
	addi %r4, %r14, 2560
	li %r5, 2048
	li %r6, 0
261:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 261b
	or %r4, %r16, %r16
	addi %r5, %r14, 2568
	li %r6, 28
262:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 262b
	add %r4, %r14, %r17
	addi %r5, %r14, 2596
	or %r6, %r21, %r21
263:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 263b
	addi %r8, %r8, 1
	li %r9, 1
	li %r10, 10
264:
	addi %r4, %r14, 2596
	add %r5, %r4, %r9
	li %r6, 1
	and %r6, %r8, %r6
	li %r7, 0
	subf %r6, %r6, %r7
	or %r7, %r21, %r21
265:
	lbz %r11, 0(%r4)
	lbz %r3, 0(%r5)
	xor %r3, %r3, %r11
	and %r3, %r3, %r6
	xor %r11, %r11, %r3
	stb %r11, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 265b
	rldicl %r8, %r8, 63, 1
	add %r9, %r9, %r9
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 264b
	addi %r29, %r25, 36
	addi %r28, %r21, 51
	rldicl %r28, %r28, 57, 7
	addi %r28, %r28, 1
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 2560
	rldicr %r5, %r28, 7, 56
	li %r6, 0
266:
	xor %r7, %r6, %r29
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	li %r12, 0
	subf %r7, %r7, %r12
	li %r8, 128
	and %r7, %r7, %r8
	lbz %r8, 0(%r4)
	or %r8, %r8, %r7
	stb %r8, 0(%r4)
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 266b
	addi %r26, %r14, 4432
	rldicl %r8, %r29, 3, 61
	li %r11, 176
	stdbrx %r8, %r26, %r11
	add %r8, %r29, %r29
	add %r8, %r8, %r8
	add %r8, %r8, %r8
	li %r11, 184
	stdbrx %r8, %r26, %r11
	addi %r27, %r29, 16
	rldicl %r27, %r27, 57, 7
	addi %r4, %r14, 2672
	li %r6, 0
	or %r9, %r28, %r28
267:
	xor %r7, %r6, %r27
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	li %r12, 0
	subf %r7, %r7, %r12
	addi %r5, %r14, 4608
	li %r10, 16
268:
	lbz %r8, 0(%r5)
	and %r8, %r8, %r7
	lbz %r11, 0(%r4)
	or %r11, %r11, %r8
	stb %r11, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 268b
	addi %r4, %r4, 112
	addi %r6, %r6, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 267b
	li %r26, 0
269:
	addi %r3, %r14, 1024
	rldicr %r4, %r26, 7, 56
	add %r4, %r4, %r14
	addi %r4, %r4, 2560
	li %r5, 1
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 24(%r12)
	mtctr %r12
	bctrl
	xor %r3, %r26, %r27
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	li %r12, 0
	subf %r3, %r3, %r12
	addi %r4, %r14, 1024
	addi %r5, %r14, 4800
	li %r6, 64
270:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	and %r7, %r7, %r3
	xor %r8, %r8, %r7
	stb %r8, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 270b
	addi %r26, %r26, 1
	addi %r28, %r28, -1
	cmpldi %cr0, %r28, 0
	bne %cr0, 269b
	addi %r3, %r14, 4800
	addi %r4, %r14, 1280
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 32(%r12)
	mtctr %r12
	bctrl
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	addi %r5, %r14, 1280
	li %r6, 28
271:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 271b
	addi %r3, %r24, -1
	rldicl %r3, %r3, 1, 63
	b 260f
259:
	addi %r4, %r14, 2560
	li %r5, 8
	li %r6, 0
272:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 272b
	or %r4, %r16, %r16
	addi %r5, %r14, 2568
	li %r6, 28
273:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 273b
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	subf %r4, %r19, %r4
	addi %r5, %r14, 2596
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 274f
	b 275f
274:
276:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 276b
275:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	li %r4, 0
	addi %r5, %r14, 2560
	addi %r6, %r19, 36
	addi %r3, %r14, 1024
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r19, 36
	addi %r3, %r14, 1024
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	addi %r5, %r14, 1280
	li %r6, 28
277:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 277b
	addi %r3, %r24, -1
	rldicl %r3, %r3, 1, 63
260:
	b 253f
252:
	li %r3, 0
253:
	b 249f
248:
	li %r3, 0
249:
	b 247f
246:
	li %r3, 0
247:
	addi %r12, %r1, 0
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r14, 112(%r12)
	ld %r15, 120(%r12)
	ld %r16, 128(%r12)
	ld %r17, 136(%r12)
	ld %r18, 144(%r12)
	ld %r19, 152(%r12)
	ld %r20, 160(%r12)
	ld %r21, 168(%r12)
	ld %r22, 176(%r12)
	ld %r23, 184(%r12)
	ld %r24, 192(%r12)
	ld %r25, 200(%r12)
	ld %r26, 208(%r12)
	ld %r27, 216(%r12)
	ld %r28, 224(%r12)
	ld %r29, 232(%r12)
213:
	b 211f
210:
	addi %r12, %r1, 0
	std %r14, 112(%r12)
	std %r15, 120(%r12)
	std %r16, 128(%r12)
	std %r17, 136(%r12)
	std %r18, 144(%r12)
	std %r19, 152(%r12)
	std %r20, 160(%r12)
	std %r21, 168(%r12)
	std %r22, 176(%r12)
	std %r23, 184(%r12)
	std %r24, 192(%r12)
	std %r25, 200(%r12)
	std %r26, 208(%r12)
	std %r27, 216(%r12)
	std %r28, 224(%r12)
	std %r29, 232(%r12)
	mflr %r0
	std %r0, 240(%r12)
	ld %r20, 360(%r12)
	rlwinm %r20, %r20, 0, 0, 31
	ld %r14, 368(%r12)
	ld %r27, 376(%r12)
	ld %r22, 384(%r12)
	ld %r23, 392(%r12)
	or %r15, %r4, %r4
	or %r16, %r7, %r7
	ld %r19, 352(%r12)
	or %r24, %r5, %r5
	or %r25, %r6, %r6
	or %r26, %r9, %r9
	lbz %r9, 0(%r3)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r17, %r11, 1, 63
	li %r11, 0
	subf %r11, %r17, %r11
	li %r8, 255
	and %r11, %r11, %r8
	or %r18, %r10, %r11
	subf %r21, %r17, %r15
	addi %r21, %r21, -65
	cmpldi %cr0, %r9, 0
	beq %cr0, 278f
	subf %r3, %r17, %r15
	addi %r3, %r3, -66
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 280f
	cmpldi %cr0, %r20, 0
	beq %cr0, 282f
	li %r4, 0
	b 283f
282:
	or %r4, %r19, %r19
283:
	subf %r3, %r17, %r15
	addi %r3, %r3, -66
	subf %r3, %r4, %r3
	rldicl %r3, %r3, 1, 63
	rldicl %r5, %r4, 1, 63
	or %r3, %r3, %r5
	cmpldi %cr0, %r3, 0
	bne %cr0, 284f
	addi %r12, %r1, 0
	li %r4, 8192
	add %r4, %r14, %r4
	std %r4, 96(%r12)
	addi %r5, %r27, -1024
	std %r5, 104(%r12)
	addi %r3, %r14, 0
	or %r4, %r15, %r15
	or %r5, %r22, %r22
	or %r6, %r23, %r23
	or %r7, %r24, %r24
	or %r8, %r25, %r25
	or %r9, %r26, %r26
	or %r10, %r15, %r15
	bl {vg_rsa_public_precomputed_checked}
	add %r4, %r14, %r15
	addi %r4, %r4, -1
	lbz %r5, 0(%r4)
	li %r6, 188
	xor %r5, %r5, %r6
	add %r7, %r14, %r17
	lbz %r6, 0(%r7)
	li %r8, 255
	xor %r8, %r8, %r18
	and %r6, %r6, %r8
	or %r5, %r5, %r6
	lbz %r6, 0(%r14)
	li %r8, 0
	subf %r8, %r17, %r8
	and %r6, %r6, %r8
	or %r5, %r5, %r6
	stb %r5, 0(%r4)
	add %r26, %r14, %r17
	or %r27, %r21, %r21
	add %r24, %r26, %r21
	li %r25, 64
	li %r28, 0
	li %r29, 0
286:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r5, %r14, 1344
	or %r8, %r28, %r28
	stb %r8, 3(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 2(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 1(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 0(%r5)
	addi %r3, %r14, 1024
	or %r4, %r25, %r25
	li %r6, 4
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 408(%r9)
	ld %r9, 32(%r9)
	addi %r11, %r14, 1280
	add %r12, %r26, %r29
	subf %r8, %r29, %r27
	subf %r10, %r9, %r8
	rldicl %r6, %r10, 1, 63
	li %r7, 0
	subf %r6, %r6, %r7
	and %r10, %r10, %r6
	add %r9, %r9, %r10
287:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 287b
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 286b
	add %r4, %r14, %r17
	lbz %r5, 0(%r4)
	and %r5, %r5, %r18
	stb %r5, 0(%r4)
	add %r4, %r14, %r17
	or %r5, %r21, %r21
	li %r6, 0
	li %r7, 0
	addi %r7, %r7, -1
	li %r8, 0
	li %r9, 0
288:
	lbz %r10, 0(%r4)
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	addi %r12, %r11, -1
	and %r12, %r12, %r7
	and %r3, %r6, %r12
	or %r8, %r8, %r3
	and %r3, %r10, %r12
	or %r9, %r9, %r3
	li %r3, 0
	subf %r3, %r11, %r3
	and %r7, %r7, %r3
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 288b
	add %r4, %r14, %r15
	addi %r4, %r4, -1
	lbz %r24, 0(%r4)
	li %r3, 1
	xor %r9, %r9, %r3
	or %r24, %r24, %r9
	subf %r25, %r8, %r21
	addi %r25, %r25, -1
	cmpldi %cr0, %r20, 0
	beq %cr0, 289f
	b 290f
289:
	xor %r3, %r25, %r19
	or %r24, %r24, %r3
290:
	cmpldi %cr0, %r20, 0
	beq %cr0, 291f
	addi %r4, %r14, 2560
	li %r5, 2048
	li %r6, 0
293:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 293b
	or %r4, %r16, %r16
	addi %r5, %r14, 2568
	li %r6, 64
294:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 294b
	add %r4, %r14, %r17
	addi %r5, %r14, 2632
	or %r6, %r21, %r21
295:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 295b
	addi %r8, %r8, 1
	li %r9, 1
	li %r10, 10
296:
	addi %r4, %r14, 2632
	add %r5, %r4, %r9
	li %r6, 1
	and %r6, %r8, %r6
	li %r7, 0
	subf %r6, %r6, %r7
	or %r7, %r21, %r21
297:
	lbz %r11, 0(%r4)
	lbz %r3, 0(%r5)
	xor %r3, %r3, %r11
	and %r3, %r3, %r6
	xor %r11, %r11, %r3
	stb %r11, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 297b
	rldicl %r8, %r8, 63, 1
	add %r9, %r9, %r9
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 296b
	addi %r29, %r25, 72
	addi %r28, %r21, 87
	rldicl %r28, %r28, 57, 7
	addi %r28, %r28, 1
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 2560
	rldicr %r5, %r28, 7, 56
	li %r6, 0
298:
	xor %r7, %r6, %r29
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	li %r12, 0
	subf %r7, %r7, %r12
	li %r8, 128
	and %r7, %r7, %r8
	lbz %r8, 0(%r4)
	or %r8, %r8, %r7
	stb %r8, 0(%r4)
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 298b
	addi %r26, %r14, 4432
	rldicl %r8, %r29, 3, 61
	li %r11, 176
	stdbrx %r8, %r26, %r11
	add %r8, %r29, %r29
	add %r8, %r8, %r8
	add %r8, %r8, %r8
	li %r11, 184
	stdbrx %r8, %r26, %r11
	addi %r27, %r29, 16
	rldicl %r27, %r27, 57, 7
	addi %r4, %r14, 2672
	li %r6, 0
	or %r9, %r28, %r28
299:
	xor %r7, %r6, %r27
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	li %r12, 0
	subf %r7, %r7, %r12
	addi %r5, %r14, 4608
	li %r10, 16
2100:
	lbz %r8, 0(%r5)
	and %r8, %r8, %r7
	lbz %r11, 0(%r4)
	or %r11, %r11, %r8
	stb %r11, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 2100b
	addi %r4, %r4, 112
	addi %r6, %r6, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 299b
	li %r26, 0
2101:
	addi %r3, %r14, 1024
	rldicr %r4, %r26, 7, 56
	add %r4, %r4, %r14
	addi %r4, %r4, 2560
	li %r5, 1
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 24(%r12)
	mtctr %r12
	bctrl
	xor %r3, %r26, %r27
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	li %r12, 0
	subf %r3, %r3, %r12
	addi %r4, %r14, 1024
	addi %r5, %r14, 4800
	li %r6, 64
2102:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	and %r7, %r7, %r3
	xor %r8, %r8, %r7
	stb %r8, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2102b
	addi %r26, %r26, 1
	addi %r28, %r28, -1
	cmpldi %cr0, %r28, 0
	bne %cr0, 2101b
	addi %r3, %r14, 4800
	addi %r4, %r14, 1280
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 32(%r12)
	mtctr %r12
	bctrl
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	addi %r5, %r14, 1280
	li %r6, 64
2103:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2103b
	addi %r3, %r24, -1
	rldicl %r3, %r3, 1, 63
	b 292f
291:
	addi %r4, %r14, 2560
	li %r5, 8
	li %r6, 0
2104:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2104b
	or %r4, %r16, %r16
	addi %r5, %r14, 2568
	li %r6, 64
2105:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2105b
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	subf %r4, %r19, %r4
	addi %r5, %r14, 2632
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 2106f
	b 2107f
2106:
2108:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2108b
2107:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	li %r4, 0
	addi %r5, %r14, 2560
	addi %r6, %r19, 72
	addi %r3, %r14, 1024
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r19, 72
	addi %r3, %r14, 1024
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	addi %r5, %r14, 1280
	li %r6, 64
2109:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2109b
	addi %r3, %r24, -1
	rldicl %r3, %r3, 1, 63
292:
	b 285f
284:
	li %r3, 0
285:
	b 281f
280:
	li %r3, 0
281:
	b 279f
278:
	li %r3, 0
279:
	addi %r12, %r1, 0
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r14, 112(%r12)
	ld %r15, 120(%r12)
	ld %r16, 128(%r12)
	ld %r17, 136(%r12)
	ld %r18, 144(%r12)
	ld %r19, 152(%r12)
	ld %r20, 160(%r12)
	ld %r21, 168(%r12)
	ld %r22, 176(%r12)
	ld %r23, 184(%r12)
	ld %r24, 192(%r12)
	ld %r25, 200(%r12)
	ld %r26, 208(%r12)
	ld %r27, 216(%r12)
	ld %r28, 224(%r12)
	ld %r29, 232(%r12)
211:
	b 29f
28:
	addi %r12, %r1, 0
	std %r14, 112(%r12)
	std %r15, 120(%r12)
	std %r16, 128(%r12)
	std %r17, 136(%r12)
	std %r18, 144(%r12)
	std %r19, 152(%r12)
	std %r20, 160(%r12)
	std %r21, 168(%r12)
	std %r22, 176(%r12)
	std %r23, 184(%r12)
	std %r24, 192(%r12)
	std %r25, 200(%r12)
	std %r26, 208(%r12)
	std %r27, 216(%r12)
	std %r28, 224(%r12)
	std %r29, 232(%r12)
	mflr %r0
	std %r0, 240(%r12)
	ld %r20, 360(%r12)
	rlwinm %r20, %r20, 0, 0, 31
	ld %r14, 368(%r12)
	ld %r27, 376(%r12)
	ld %r22, 384(%r12)
	ld %r23, 392(%r12)
	or %r15, %r4, %r4
	or %r16, %r7, %r7
	ld %r19, 352(%r12)
	or %r24, %r5, %r5
	or %r25, %r6, %r6
	or %r26, %r9, %r9
	lbz %r9, 0(%r3)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r17, %r11, 1, 63
	li %r11, 0
	subf %r11, %r17, %r11
	li %r8, 255
	and %r11, %r11, %r8
	or %r18, %r10, %r11
	subf %r21, %r17, %r15
	addi %r21, %r21, -49
	cmpldi %cr0, %r9, 0
	beq %cr0, 2110f
	subf %r3, %r17, %r15
	addi %r3, %r3, -50
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 2112f
	cmpldi %cr0, %r20, 0
	beq %cr0, 2114f
	li %r4, 0
	b 2115f
2114:
	or %r4, %r19, %r19
2115:
	subf %r3, %r17, %r15
	addi %r3, %r3, -50
	subf %r3, %r4, %r3
	rldicl %r3, %r3, 1, 63
	rldicl %r5, %r4, 1, 63
	or %r3, %r3, %r5
	cmpldi %cr0, %r3, 0
	bne %cr0, 2116f
	addi %r12, %r1, 0
	li %r4, 8192
	add %r4, %r14, %r4
	std %r4, 96(%r12)
	addi %r5, %r27, -1024
	std %r5, 104(%r12)
	addi %r3, %r14, 0
	or %r4, %r15, %r15
	or %r5, %r22, %r22
	or %r6, %r23, %r23
	or %r7, %r24, %r24
	or %r8, %r25, %r25
	or %r9, %r26, %r26
	or %r10, %r15, %r15
	bl {vg_rsa_public_precomputed_checked}
	add %r4, %r14, %r15
	addi %r4, %r4, -1
	lbz %r5, 0(%r4)
	li %r6, 188
	xor %r5, %r5, %r6
	add %r7, %r14, %r17
	lbz %r6, 0(%r7)
	li %r8, 255
	xor %r8, %r8, %r18
	and %r6, %r6, %r8
	or %r5, %r5, %r6
	lbz %r6, 0(%r14)
	li %r8, 0
	subf %r8, %r17, %r8
	and %r6, %r6, %r8
	or %r5, %r5, %r6
	stb %r5, 0(%r4)
	add %r26, %r14, %r17
	or %r27, %r21, %r21
	add %r24, %r26, %r21
	li %r25, 48
	li %r28, 0
	li %r29, 0
2118:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r5, %r14, 1344
	or %r8, %r28, %r28
	stb %r8, 3(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 2(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 1(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 0(%r5)
	addi %r3, %r14, 1024
	or %r4, %r25, %r25
	li %r6, 4
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 408(%r9)
	ld %r9, 32(%r9)
	addi %r11, %r14, 1280
	add %r12, %r26, %r29
	subf %r8, %r29, %r27
	subf %r10, %r9, %r8
	rldicl %r6, %r10, 1, 63
	li %r7, 0
	subf %r6, %r6, %r7
	and %r10, %r10, %r6
	add %r9, %r9, %r10
2119:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2119b
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 2118b
	add %r4, %r14, %r17
	lbz %r5, 0(%r4)
	and %r5, %r5, %r18
	stb %r5, 0(%r4)
	add %r4, %r14, %r17
	or %r5, %r21, %r21
	li %r6, 0
	li %r7, 0
	addi %r7, %r7, -1
	li %r8, 0
	li %r9, 0
2120:
	lbz %r10, 0(%r4)
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	addi %r12, %r11, -1
	and %r12, %r12, %r7
	and %r3, %r6, %r12
	or %r8, %r8, %r3
	and %r3, %r10, %r12
	or %r9, %r9, %r3
	li %r3, 0
	subf %r3, %r11, %r3
	and %r7, %r7, %r3
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2120b
	add %r4, %r14, %r15
	addi %r4, %r4, -1
	lbz %r24, 0(%r4)
	li %r3, 1
	xor %r9, %r9, %r3
	or %r24, %r24, %r9
	subf %r25, %r8, %r21
	addi %r25, %r25, -1
	cmpldi %cr0, %r20, 0
	beq %cr0, 2121f
	b 2122f
2121:
	xor %r3, %r25, %r19
	or %r24, %r24, %r3
2122:
	cmpldi %cr0, %r20, 0
	beq %cr0, 2123f
	addi %r4, %r14, 2560
	li %r5, 2048
	li %r6, 0
2125:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2125b
	or %r4, %r16, %r16
	addi %r5, %r14, 2568
	li %r6, 48
2126:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2126b
	add %r4, %r14, %r17
	addi %r5, %r14, 2616
	or %r6, %r21, %r21
2127:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2127b
	addi %r8, %r8, 1
	li %r9, 1
	li %r10, 10
2128:
	addi %r4, %r14, 2616
	add %r5, %r4, %r9
	li %r6, 1
	and %r6, %r8, %r6
	li %r7, 0
	subf %r6, %r6, %r7
	or %r7, %r21, %r21
2129:
	lbz %r11, 0(%r4)
	lbz %r3, 0(%r5)
	xor %r3, %r3, %r11
	and %r3, %r3, %r6
	xor %r11, %r11, %r3
	stb %r11, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 2129b
	rldicl %r8, %r8, 63, 1
	add %r9, %r9, %r9
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 2128b
	addi %r29, %r25, 56
	addi %r28, %r21, 71
	rldicl %r28, %r28, 57, 7
	addi %r28, %r28, 1
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 2560
	rldicr %r5, %r28, 7, 56
	li %r6, 0
2130:
	xor %r7, %r6, %r29
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	li %r12, 0
	subf %r7, %r7, %r12
	li %r8, 128
	and %r7, %r7, %r8
	lbz %r8, 0(%r4)
	or %r8, %r8, %r7
	stb %r8, 0(%r4)
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2130b
	addi %r26, %r14, 4432
	rldicl %r8, %r29, 3, 61
	li %r11, 176
	stdbrx %r8, %r26, %r11
	add %r8, %r29, %r29
	add %r8, %r8, %r8
	add %r8, %r8, %r8
	li %r11, 184
	stdbrx %r8, %r26, %r11
	addi %r27, %r29, 16
	rldicl %r27, %r27, 57, 7
	addi %r4, %r14, 2672
	li %r6, 0
	or %r9, %r28, %r28
2131:
	xor %r7, %r6, %r27
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	li %r12, 0
	subf %r7, %r7, %r12
	addi %r5, %r14, 4608
	li %r10, 16
2132:
	lbz %r8, 0(%r5)
	and %r8, %r8, %r7
	lbz %r11, 0(%r4)
	or %r11, %r11, %r8
	stb %r11, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 2132b
	addi %r4, %r4, 112
	addi %r6, %r6, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2131b
	li %r26, 0
2133:
	addi %r3, %r14, 1024
	rldicr %r4, %r26, 7, 56
	add %r4, %r4, %r14
	addi %r4, %r4, 2560
	li %r5, 1
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 24(%r12)
	mtctr %r12
	bctrl
	xor %r3, %r26, %r27
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	li %r12, 0
	subf %r3, %r3, %r12
	addi %r4, %r14, 1024
	addi %r5, %r14, 4800
	li %r6, 64
2134:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	and %r7, %r7, %r3
	xor %r8, %r8, %r7
	stb %r8, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2134b
	addi %r26, %r26, 1
	addi %r28, %r28, -1
	cmpldi %cr0, %r28, 0
	bne %cr0, 2133b
	addi %r3, %r14, 4800
	addi %r4, %r14, 1280
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 32(%r12)
	mtctr %r12
	bctrl
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	addi %r5, %r14, 1280
	li %r6, 48
2135:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2135b
	addi %r3, %r24, -1
	rldicl %r3, %r3, 1, 63
	b 2124f
2123:
	addi %r4, %r14, 2560
	li %r5, 8
	li %r6, 0
2136:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2136b
	or %r4, %r16, %r16
	addi %r5, %r14, 2568
	li %r6, 48
2137:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2137b
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	subf %r4, %r19, %r4
	addi %r5, %r14, 2616
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 2138f
	b 2139f
2138:
2140:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2140b
2139:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	li %r4, 0
	addi %r5, %r14, 2560
	addi %r6, %r19, 56
	addi %r3, %r14, 1024
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r19, 56
	addi %r3, %r14, 1024
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	addi %r5, %r14, 1280
	li %r6, 48
2141:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2141b
	addi %r3, %r24, -1
	rldicl %r3, %r3, 1, 63
2124:
	b 2117f
2116:
	li %r3, 0
2117:
	b 2113f
2112:
	li %r3, 0
2113:
	b 2111f
2110:
	li %r3, 0
2111:
	addi %r12, %r1, 0
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r14, 112(%r12)
	ld %r15, 120(%r12)
	ld %r16, 128(%r12)
	ld %r17, 136(%r12)
	ld %r18, 144(%r12)
	ld %r19, 152(%r12)
	ld %r20, 160(%r12)
	ld %r21, 168(%r12)
	ld %r22, 176(%r12)
	ld %r23, 184(%r12)
	ld %r24, 192(%r12)
	ld %r25, 200(%r12)
	ld %r26, 208(%r12)
	ld %r27, 216(%r12)
	ld %r28, 224(%r12)
	ld %r29, 232(%r12)
29:
	b 27f
26:
	addi %r12, %r1, 0
	std %r14, 112(%r12)
	std %r15, 120(%r12)
	std %r16, 128(%r12)
	std %r17, 136(%r12)
	std %r18, 144(%r12)
	std %r19, 152(%r12)
	std %r20, 160(%r12)
	std %r21, 168(%r12)
	std %r22, 176(%r12)
	std %r23, 184(%r12)
	std %r24, 192(%r12)
	std %r25, 200(%r12)
	std %r26, 208(%r12)
	std %r27, 216(%r12)
	std %r28, 224(%r12)
	std %r29, 232(%r12)
	mflr %r0
	std %r0, 240(%r12)
	ld %r20, 360(%r12)
	rlwinm %r20, %r20, 0, 0, 31
	ld %r14, 368(%r12)
	ld %r27, 376(%r12)
	ld %r22, 384(%r12)
	ld %r23, 392(%r12)
	or %r15, %r4, %r4
	or %r16, %r7, %r7
	ld %r19, 352(%r12)
	or %r24, %r5, %r5
	or %r25, %r6, %r6
	or %r26, %r9, %r9
	lbz %r9, 0(%r3)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r17, %r11, 1, 63
	li %r11, 0
	subf %r11, %r17, %r11
	li %r8, 255
	and %r11, %r11, %r8
	or %r18, %r10, %r11
	subf %r21, %r17, %r15
	addi %r21, %r21, -33
	cmpldi %cr0, %r9, 0
	beq %cr0, 2142f
	subf %r3, %r17, %r15
	addi %r3, %r3, -34
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 2144f
	cmpldi %cr0, %r20, 0
	beq %cr0, 2146f
	li %r4, 0
	b 2147f
2146:
	or %r4, %r19, %r19
2147:
	subf %r3, %r17, %r15
	addi %r3, %r3, -34
	subf %r3, %r4, %r3
	rldicl %r3, %r3, 1, 63
	rldicl %r5, %r4, 1, 63
	or %r3, %r3, %r5
	cmpldi %cr0, %r3, 0
	bne %cr0, 2148f
	addi %r12, %r1, 0
	li %r4, 8192
	add %r4, %r14, %r4
	std %r4, 96(%r12)
	addi %r5, %r27, -1024
	std %r5, 104(%r12)
	addi %r3, %r14, 0
	or %r4, %r15, %r15
	or %r5, %r22, %r22
	or %r6, %r23, %r23
	or %r7, %r24, %r24
	or %r8, %r25, %r25
	or %r9, %r26, %r26
	or %r10, %r15, %r15
	bl {vg_rsa_public_precomputed_checked}
	add %r4, %r14, %r15
	addi %r4, %r4, -1
	lbz %r5, 0(%r4)
	li %r6, 188
	xor %r5, %r5, %r6
	add %r7, %r14, %r17
	lbz %r6, 0(%r7)
	li %r8, 255
	xor %r8, %r8, %r18
	and %r6, %r6, %r8
	or %r5, %r5, %r6
	lbz %r6, 0(%r14)
	li %r8, 0
	subf %r8, %r17, %r8
	and %r6, %r6, %r8
	or %r5, %r5, %r6
	stb %r5, 0(%r4)
	add %r26, %r14, %r17
	or %r27, %r21, %r21
	add %r24, %r26, %r21
	li %r25, 32
	li %r28, 0
	li %r29, 0
2150:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r5, %r14, 1344
	or %r8, %r28, %r28
	stb %r8, 3(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 2(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 1(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 0(%r5)
	addi %r3, %r14, 1024
	or %r4, %r25, %r25
	li %r6, 4
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 408(%r9)
	ld %r9, 32(%r9)
	addi %r11, %r14, 1280
	add %r12, %r26, %r29
	subf %r8, %r29, %r27
	subf %r10, %r9, %r8
	rldicl %r6, %r10, 1, 63
	li %r7, 0
	subf %r6, %r6, %r7
	and %r10, %r10, %r6
	add %r9, %r9, %r10
2151:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2151b
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 2150b
	add %r4, %r14, %r17
	lbz %r5, 0(%r4)
	and %r5, %r5, %r18
	stb %r5, 0(%r4)
	add %r4, %r14, %r17
	or %r5, %r21, %r21
	li %r6, 0
	li %r7, 0
	addi %r7, %r7, -1
	li %r8, 0
	li %r9, 0
2152:
	lbz %r10, 0(%r4)
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	addi %r12, %r11, -1
	and %r12, %r12, %r7
	and %r3, %r6, %r12
	or %r8, %r8, %r3
	and %r3, %r10, %r12
	or %r9, %r9, %r3
	li %r3, 0
	subf %r3, %r11, %r3
	and %r7, %r7, %r3
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2152b
	add %r4, %r14, %r15
	addi %r4, %r4, -1
	lbz %r24, 0(%r4)
	li %r3, 1
	xor %r9, %r9, %r3
	or %r24, %r24, %r9
	subf %r25, %r8, %r21
	addi %r25, %r25, -1
	cmpldi %cr0, %r20, 0
	beq %cr0, 2153f
	b 2154f
2153:
	xor %r3, %r25, %r19
	or %r24, %r24, %r3
2154:
	cmpldi %cr0, %r20, 0
	beq %cr0, 2155f
	addi %r4, %r14, 2560
	li %r5, 2048
	li %r6, 0
2157:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2157b
	or %r4, %r16, %r16
	addi %r5, %r14, 2568
	li %r6, 32
2158:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2158b
	add %r4, %r14, %r17
	addi %r5, %r14, 2600
	or %r6, %r21, %r21
2159:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2159b
	addi %r8, %r8, 1
	li %r9, 1
	li %r10, 10
2160:
	addi %r4, %r14, 2600
	add %r5, %r4, %r9
	li %r6, 1
	and %r6, %r8, %r6
	li %r7, 0
	subf %r6, %r6, %r7
	or %r7, %r21, %r21
2161:
	lbz %r11, 0(%r4)
	lbz %r3, 0(%r5)
	xor %r3, %r3, %r11
	and %r3, %r3, %r6
	xor %r11, %r11, %r3
	stb %r11, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 2161b
	rldicl %r8, %r8, 63, 1
	add %r9, %r9, %r9
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 2160b
	addi %r29, %r25, 40
	addi %r28, %r21, 47
	rldicl %r28, %r28, 58, 6
	addi %r28, %r28, 1
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 2560
	rldicr %r5, %r28, 6, 57
	li %r6, 0
2162:
	xor %r7, %r6, %r29
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	li %r12, 0
	subf %r7, %r7, %r12
	li %r8, 128
	and %r7, %r7, %r8
	lbz %r8, 0(%r4)
	or %r8, %r8, %r7
	stb %r8, 0(%r4)
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2162b
	addi %r26, %r14, 4520
	add %r8, %r29, %r29
	add %r8, %r8, %r8
	add %r8, %r8, %r8
	li %r11, 88
	stdbrx %r8, %r26, %r11
	addi %r27, %r29, 8
	rldicl %r27, %r27, 58, 6
	addi %r4, %r14, 2616
	li %r6, 0
	or %r9, %r28, %r28
2163:
	xor %r7, %r6, %r27
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	li %r12, 0
	subf %r7, %r7, %r12
	addi %r5, %r14, 4608
	li %r10, 8
2164:
	lbz %r8, 0(%r5)
	and %r8, %r8, %r7
	lbz %r11, 0(%r4)
	or %r11, %r11, %r8
	stb %r11, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 2164b
	addi %r4, %r4, 56
	addi %r6, %r6, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2163b
	li %r26, 0
2165:
	addi %r3, %r14, 1024
	rldicr %r4, %r26, 6, 57
	add %r4, %r4, %r14
	addi %r4, %r4, 2560
	li %r5, 1
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 24(%r12)
	mtctr %r12
	bctrl
	xor %r3, %r26, %r27
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	li %r12, 0
	subf %r3, %r3, %r12
	addi %r4, %r14, 1024
	addi %r5, %r14, 4800
	li %r6, 32
2166:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	and %r7, %r7, %r3
	xor %r8, %r8, %r7
	stb %r8, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2166b
	addi %r26, %r26, 1
	addi %r28, %r28, -1
	cmpldi %cr0, %r28, 0
	bne %cr0, 2165b
	addi %r3, %r14, 4800
	addi %r4, %r14, 1280
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 32(%r12)
	mtctr %r12
	bctrl
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	addi %r5, %r14, 1280
	li %r6, 32
2167:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2167b
	addi %r3, %r24, -1
	rldicl %r3, %r3, 1, 63
	b 2156f
2155:
	addi %r4, %r14, 2560
	li %r5, 8
	li %r6, 0
2168:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2168b
	or %r4, %r16, %r16
	addi %r5, %r14, 2568
	li %r6, 32
2169:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2169b
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	subf %r4, %r19, %r4
	addi %r5, %r14, 2600
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 2170f
	b 2171f
2170:
2172:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2172b
2171:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	li %r4, 0
	addi %r5, %r14, 2560
	addi %r6, %r19, 40
	addi %r3, %r14, 1024
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r19, 40
	addi %r3, %r14, 1024
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	addi %r5, %r14, 1280
	li %r6, 32
2173:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2173b
	addi %r3, %r24, -1
	rldicl %r3, %r3, 1, 63
2156:
	b 2149f
2148:
	li %r3, 0
2149:
	b 2145f
2144:
	li %r3, 0
2145:
	b 2143f
2142:
	li %r3, 0
2143:
	addi %r12, %r1, 0
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r14, 112(%r12)
	ld %r15, 120(%r12)
	ld %r16, 128(%r12)
	ld %r17, 136(%r12)
	ld %r18, 144(%r12)
	ld %r19, 152(%r12)
	ld %r20, 160(%r12)
	ld %r21, 168(%r12)
	ld %r22, 176(%r12)
	ld %r23, 184(%r12)
	ld %r24, 192(%r12)
	ld %r25, 200(%r12)
	ld %r26, 208(%r12)
	ld %r27, 216(%r12)
	ld %r28, 224(%r12)
	ld %r29, 232(%r12)
27:
	b 25f
24:
	addi %r12, %r1, 0
	std %r14, 112(%r12)
	std %r15, 120(%r12)
	std %r16, 128(%r12)
	std %r17, 136(%r12)
	std %r18, 144(%r12)
	std %r19, 152(%r12)
	std %r20, 160(%r12)
	std %r21, 168(%r12)
	std %r22, 176(%r12)
	std %r23, 184(%r12)
	std %r24, 192(%r12)
	std %r25, 200(%r12)
	std %r26, 208(%r12)
	std %r27, 216(%r12)
	std %r28, 224(%r12)
	std %r29, 232(%r12)
	mflr %r0
	std %r0, 240(%r12)
	ld %r20, 360(%r12)
	rlwinm %r20, %r20, 0, 0, 31
	ld %r14, 368(%r12)
	ld %r27, 376(%r12)
	ld %r22, 384(%r12)
	ld %r23, 392(%r12)
	or %r15, %r4, %r4
	or %r16, %r7, %r7
	ld %r19, 352(%r12)
	or %r24, %r5, %r5
	or %r25, %r6, %r6
	or %r26, %r9, %r9
	lbz %r9, 0(%r3)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r17, %r11, 1, 63
	li %r11, 0
	subf %r11, %r17, %r11
	li %r8, 255
	and %r11, %r11, %r8
	or %r18, %r10, %r11
	subf %r21, %r17, %r15
	addi %r21, %r21, -29
	cmpldi %cr0, %r9, 0
	beq %cr0, 2174f
	subf %r3, %r17, %r15
	addi %r3, %r3, -30
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 2176f
	cmpldi %cr0, %r20, 0
	beq %cr0, 2178f
	li %r4, 0
	b 2179f
2178:
	or %r4, %r19, %r19
2179:
	subf %r3, %r17, %r15
	addi %r3, %r3, -30
	subf %r3, %r4, %r3
	rldicl %r3, %r3, 1, 63
	rldicl %r5, %r4, 1, 63
	or %r3, %r3, %r5
	cmpldi %cr0, %r3, 0
	bne %cr0, 2180f
	addi %r12, %r1, 0
	li %r4, 8192
	add %r4, %r14, %r4
	std %r4, 96(%r12)
	addi %r5, %r27, -1024
	std %r5, 104(%r12)
	addi %r3, %r14, 0
	or %r4, %r15, %r15
	or %r5, %r22, %r22
	or %r6, %r23, %r23
	or %r7, %r24, %r24
	or %r8, %r25, %r25
	or %r9, %r26, %r26
	or %r10, %r15, %r15
	bl {vg_rsa_public_precomputed_checked}
	add %r4, %r14, %r15
	addi %r4, %r4, -1
	lbz %r5, 0(%r4)
	li %r6, 188
	xor %r5, %r5, %r6
	add %r7, %r14, %r17
	lbz %r6, 0(%r7)
	li %r8, 255
	xor %r8, %r8, %r18
	and %r6, %r6, %r8
	or %r5, %r5, %r6
	lbz %r6, 0(%r14)
	li %r8, 0
	subf %r8, %r17, %r8
	and %r6, %r6, %r8
	or %r5, %r5, %r6
	stb %r5, 0(%r4)
	add %r26, %r14, %r17
	or %r27, %r21, %r21
	add %r24, %r26, %r21
	li %r25, 28
	li %r28, 0
	li %r29, 0
2182:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r5, %r14, 1344
	or %r8, %r28, %r28
	stb %r8, 3(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 2(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 1(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 0(%r5)
	addi %r3, %r14, 1024
	or %r4, %r25, %r25
	li %r6, 4
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 408(%r9)
	ld %r9, 32(%r9)
	addi %r11, %r14, 1280
	add %r12, %r26, %r29
	subf %r8, %r29, %r27
	subf %r10, %r9, %r8
	rldicl %r6, %r10, 1, 63
	li %r7, 0
	subf %r6, %r6, %r7
	and %r10, %r10, %r6
	add %r9, %r9, %r10
2183:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2183b
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 2182b
	add %r4, %r14, %r17
	lbz %r5, 0(%r4)
	and %r5, %r5, %r18
	stb %r5, 0(%r4)
	add %r4, %r14, %r17
	or %r5, %r21, %r21
	li %r6, 0
	li %r7, 0
	addi %r7, %r7, -1
	li %r8, 0
	li %r9, 0
2184:
	lbz %r10, 0(%r4)
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	addi %r12, %r11, -1
	and %r12, %r12, %r7
	and %r3, %r6, %r12
	or %r8, %r8, %r3
	and %r3, %r10, %r12
	or %r9, %r9, %r3
	li %r3, 0
	subf %r3, %r11, %r3
	and %r7, %r7, %r3
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2184b
	add %r4, %r14, %r15
	addi %r4, %r4, -1
	lbz %r24, 0(%r4)
	li %r3, 1
	xor %r9, %r9, %r3
	or %r24, %r24, %r9
	subf %r25, %r8, %r21
	addi %r25, %r25, -1
	cmpldi %cr0, %r20, 0
	beq %cr0, 2185f
	b 2186f
2185:
	xor %r3, %r25, %r19
	or %r24, %r24, %r3
2186:
	cmpldi %cr0, %r20, 0
	beq %cr0, 2187f
	addi %r4, %r14, 2560
	li %r5, 2048
	li %r6, 0
2189:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2189b
	or %r4, %r16, %r16
	addi %r5, %r14, 2568
	li %r6, 28
2190:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2190b
	add %r4, %r14, %r17
	addi %r5, %r14, 2596
	or %r6, %r21, %r21
2191:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2191b
	addi %r8, %r8, 1
	li %r9, 1
	li %r10, 10
2192:
	addi %r4, %r14, 2596
	add %r5, %r4, %r9
	li %r6, 1
	and %r6, %r8, %r6
	li %r7, 0
	subf %r6, %r6, %r7
	or %r7, %r21, %r21
2193:
	lbz %r11, 0(%r4)
	lbz %r3, 0(%r5)
	xor %r3, %r3, %r11
	and %r3, %r3, %r6
	xor %r11, %r11, %r3
	stb %r11, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 2193b
	rldicl %r8, %r8, 63, 1
	add %r9, %r9, %r9
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 2192b
	addi %r29, %r25, 36
	addi %r28, %r21, 43
	rldicl %r28, %r28, 58, 6
	addi %r28, %r28, 1
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 2560
	rldicr %r5, %r28, 6, 57
	li %r6, 0
2194:
	xor %r7, %r6, %r29
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	li %r12, 0
	subf %r7, %r7, %r12
	li %r8, 128
	and %r7, %r7, %r8
	lbz %r8, 0(%r4)
	or %r8, %r8, %r7
	stb %r8, 0(%r4)
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2194b
	addi %r26, %r14, 4520
	add %r8, %r29, %r29
	add %r8, %r8, %r8
	add %r8, %r8, %r8
	li %r11, 88
	stdbrx %r8, %r26, %r11
	addi %r27, %r29, 8
	rldicl %r27, %r27, 58, 6
	addi %r4, %r14, 2616
	li %r6, 0
	or %r9, %r28, %r28
2195:
	xor %r7, %r6, %r27
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	li %r12, 0
	subf %r7, %r7, %r12
	addi %r5, %r14, 4608
	li %r10, 8
2196:
	lbz %r8, 0(%r5)
	and %r8, %r8, %r7
	lbz %r11, 0(%r4)
	or %r11, %r11, %r8
	stb %r11, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 2196b
	addi %r4, %r4, 56
	addi %r6, %r6, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2195b
	li %r26, 0
2197:
	addi %r3, %r14, 1024
	rldicr %r4, %r26, 6, 57
	add %r4, %r4, %r14
	addi %r4, %r4, 2560
	li %r5, 1
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 24(%r12)
	mtctr %r12
	bctrl
	xor %r3, %r26, %r27
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	li %r12, 0
	subf %r3, %r3, %r12
	addi %r4, %r14, 1024
	addi %r5, %r14, 4800
	li %r6, 32
2198:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	and %r7, %r7, %r3
	xor %r8, %r8, %r7
	stb %r8, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2198b
	addi %r26, %r26, 1
	addi %r28, %r28, -1
	cmpldi %cr0, %r28, 0
	bne %cr0, 2197b
	addi %r3, %r14, 4800
	addi %r4, %r14, 1280
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 32(%r12)
	mtctr %r12
	bctrl
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	addi %r5, %r14, 1280
	li %r6, 28
2199:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2199b
	addi %r3, %r24, -1
	rldicl %r3, %r3, 1, 63
	b 2188f
2187:
	addi %r4, %r14, 2560
	li %r5, 8
	li %r6, 0
2200:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2200b
	or %r4, %r16, %r16
	addi %r5, %r14, 2568
	li %r6, 28
2201:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2201b
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	subf %r4, %r19, %r4
	addi %r5, %r14, 2596
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 2202f
	b 2203f
2202:
2204:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2204b
2203:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	li %r4, 0
	addi %r5, %r14, 2560
	addi %r6, %r19, 36
	addi %r3, %r14, 1024
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r19, 36
	addi %r3, %r14, 1024
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	addi %r5, %r14, 1280
	li %r6, 28
2205:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2205b
	addi %r3, %r24, -1
	rldicl %r3, %r3, 1, 63
2188:
	b 2181f
2180:
	li %r3, 0
2181:
	b 2177f
2176:
	li %r3, 0
2177:
	b 2175f
2174:
	li %r3, 0
2175:
	addi %r12, %r1, 0
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r14, 112(%r12)
	ld %r15, 120(%r12)
	ld %r16, 128(%r12)
	ld %r17, 136(%r12)
	ld %r18, 144(%r12)
	ld %r19, 152(%r12)
	ld %r20, 160(%r12)
	ld %r21, 168(%r12)
	ld %r22, 176(%r12)
	ld %r23, 184(%r12)
	ld %r24, 192(%r12)
	ld %r25, 200(%r12)
	ld %r26, 208(%r12)
	ld %r27, 216(%r12)
	ld %r28, 224(%r12)
	ld %r29, 232(%r12)
25:
	b 23f
22:
	addi %r12, %r1, 0
	std %r14, 112(%r12)
	std %r15, 120(%r12)
	std %r16, 128(%r12)
	std %r17, 136(%r12)
	std %r18, 144(%r12)
	std %r19, 152(%r12)
	std %r20, 160(%r12)
	std %r21, 168(%r12)
	std %r22, 176(%r12)
	std %r23, 184(%r12)
	std %r24, 192(%r12)
	std %r25, 200(%r12)
	std %r26, 208(%r12)
	std %r27, 216(%r12)
	std %r28, 224(%r12)
	std %r29, 232(%r12)
	mflr %r0
	std %r0, 240(%r12)
	ld %r20, 360(%r12)
	rlwinm %r20, %r20, 0, 0, 31
	ld %r14, 368(%r12)
	ld %r27, 376(%r12)
	ld %r22, 384(%r12)
	ld %r23, 392(%r12)
	or %r15, %r4, %r4
	or %r16, %r7, %r7
	ld %r19, 352(%r12)
	or %r24, %r5, %r5
	or %r25, %r6, %r6
	or %r26, %r9, %r9
	lbz %r9, 0(%r3)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r17, %r11, 1, 63
	li %r11, 0
	subf %r11, %r17, %r11
	li %r8, 255
	and %r11, %r11, %r8
	or %r18, %r10, %r11
	subf %r21, %r17, %r15
	addi %r21, %r21, -21
	cmpldi %cr0, %r9, 0
	beq %cr0, 2206f
	subf %r3, %r17, %r15
	addi %r3, %r3, -22
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 2208f
	cmpldi %cr0, %r20, 0
	beq %cr0, 2210f
	li %r4, 0
	b 2211f
2210:
	or %r4, %r19, %r19
2211:
	subf %r3, %r17, %r15
	addi %r3, %r3, -22
	subf %r3, %r4, %r3
	rldicl %r3, %r3, 1, 63
	rldicl %r5, %r4, 1, 63
	or %r3, %r3, %r5
	cmpldi %cr0, %r3, 0
	bne %cr0, 2212f
	addi %r12, %r1, 0
	li %r4, 8192
	add %r4, %r14, %r4
	std %r4, 96(%r12)
	addi %r5, %r27, -1024
	std %r5, 104(%r12)
	addi %r3, %r14, 0
	or %r4, %r15, %r15
	or %r5, %r22, %r22
	or %r6, %r23, %r23
	or %r7, %r24, %r24
	or %r8, %r25, %r25
	or %r9, %r26, %r26
	or %r10, %r15, %r15
	bl {vg_rsa_public_precomputed_checked}
	add %r4, %r14, %r15
	addi %r4, %r4, -1
	lbz %r5, 0(%r4)
	li %r6, 188
	xor %r5, %r5, %r6
	add %r7, %r14, %r17
	lbz %r6, 0(%r7)
	li %r8, 255
	xor %r8, %r8, %r18
	and %r6, %r6, %r8
	or %r5, %r5, %r6
	lbz %r6, 0(%r14)
	li %r8, 0
	subf %r8, %r17, %r8
	and %r6, %r6, %r8
	or %r5, %r5, %r6
	stb %r5, 0(%r4)
	add %r26, %r14, %r17
	or %r27, %r21, %r21
	add %r24, %r26, %r21
	li %r25, 20
	li %r28, 0
	li %r29, 0
2214:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r5, %r14, 1344
	or %r8, %r28, %r28
	stb %r8, 3(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 2(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 1(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 0(%r5)
	addi %r3, %r14, 1024
	or %r4, %r25, %r25
	li %r6, 4
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 408(%r9)
	ld %r9, 32(%r9)
	addi %r11, %r14, 1280
	add %r12, %r26, %r29
	subf %r8, %r29, %r27
	subf %r10, %r9, %r8
	rldicl %r6, %r10, 1, 63
	li %r7, 0
	subf %r6, %r6, %r7
	and %r10, %r10, %r6
	add %r9, %r9, %r10
2215:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2215b
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 2214b
	add %r4, %r14, %r17
	lbz %r5, 0(%r4)
	and %r5, %r5, %r18
	stb %r5, 0(%r4)
	add %r4, %r14, %r17
	or %r5, %r21, %r21
	li %r6, 0
	li %r7, 0
	addi %r7, %r7, -1
	li %r8, 0
	li %r9, 0
2216:
	lbz %r10, 0(%r4)
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	addi %r12, %r11, -1
	and %r12, %r12, %r7
	and %r3, %r6, %r12
	or %r8, %r8, %r3
	and %r3, %r10, %r12
	or %r9, %r9, %r3
	li %r3, 0
	subf %r3, %r11, %r3
	and %r7, %r7, %r3
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2216b
	add %r4, %r14, %r15
	addi %r4, %r4, -1
	lbz %r24, 0(%r4)
	li %r3, 1
	xor %r9, %r9, %r3
	or %r24, %r24, %r9
	subf %r25, %r8, %r21
	addi %r25, %r25, -1
	cmpldi %cr0, %r20, 0
	beq %cr0, 2217f
	b 2218f
2217:
	xor %r3, %r25, %r19
	or %r24, %r24, %r3
2218:
	cmpldi %cr0, %r20, 0
	beq %cr0, 2219f
	addi %r4, %r14, 2560
	li %r5, 2048
	li %r6, 0
2221:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2221b
	or %r4, %r16, %r16
	addi %r5, %r14, 2568
	li %r6, 20
2222:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2222b
	add %r4, %r14, %r17
	addi %r5, %r14, 2588
	or %r6, %r21, %r21
2223:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2223b
	addi %r8, %r8, 1
	li %r9, 1
	li %r10, 10
2224:
	addi %r4, %r14, 2588
	add %r5, %r4, %r9
	li %r6, 1
	and %r6, %r8, %r6
	li %r7, 0
	subf %r6, %r6, %r7
	or %r7, %r21, %r21
2225:
	lbz %r11, 0(%r4)
	lbz %r3, 0(%r5)
	xor %r3, %r3, %r11
	and %r3, %r3, %r6
	xor %r11, %r11, %r3
	stb %r11, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 2225b
	rldicl %r8, %r8, 63, 1
	add %r9, %r9, %r9
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 2224b
	addi %r29, %r25, 28
	addi %r28, %r21, 35
	rldicl %r28, %r28, 58, 6
	addi %r28, %r28, 1
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 2560
	rldicr %r5, %r28, 6, 57
	li %r6, 0
2226:
	xor %r7, %r6, %r29
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	li %r12, 0
	subf %r7, %r7, %r12
	li %r8, 128
	and %r7, %r7, %r8
	lbz %r8, 0(%r4)
	or %r8, %r8, %r7
	stb %r8, 0(%r4)
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2226b
	addi %r26, %r14, 4532
	add %r8, %r29, %r29
	add %r8, %r8, %r8
	add %r8, %r8, %r8
	li %r11, 76
	stdbrx %r8, %r26, %r11
	addi %r27, %r29, 8
	rldicl %r27, %r27, 58, 6
	addi %r4, %r14, 2616
	li %r6, 0
	or %r9, %r28, %r28
2227:
	xor %r7, %r6, %r27
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	li %r12, 0
	subf %r7, %r7, %r12
	addi %r5, %r14, 4608
	li %r10, 8
2228:
	lbz %r8, 0(%r5)
	and %r8, %r8, %r7
	lbz %r11, 0(%r4)
	or %r11, %r11, %r8
	stb %r11, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 2228b
	addi %r4, %r4, 56
	addi %r6, %r6, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2227b
	li %r26, 0
2229:
	addi %r3, %r14, 1024
	rldicr %r4, %r26, 6, 57
	add %r4, %r4, %r14
	addi %r4, %r4, 2560
	li %r5, 1
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 24(%r12)
	mtctr %r12
	bctrl
	xor %r3, %r26, %r27
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	li %r12, 0
	subf %r3, %r3, %r12
	addi %r4, %r14, 1024
	addi %r5, %r14, 4800
	li %r6, 20
2230:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	and %r7, %r7, %r3
	xor %r8, %r8, %r7
	stb %r8, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2230b
	addi %r26, %r26, 1
	addi %r28, %r28, -1
	cmpldi %cr0, %r28, 0
	bne %cr0, 2229b
	addi %r3, %r14, 4800
	addi %r4, %r14, 1280
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 32(%r12)
	mtctr %r12
	bctrl
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	addi %r5, %r14, 1280
	li %r6, 20
2231:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2231b
	addi %r3, %r24, -1
	rldicl %r3, %r3, 1, 63
	b 2220f
2219:
	addi %r4, %r14, 2560
	li %r5, 8
	li %r6, 0
2232:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2232b
	or %r4, %r16, %r16
	addi %r5, %r14, 2568
	li %r6, 20
2233:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2233b
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	subf %r4, %r19, %r4
	addi %r5, %r14, 2588
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 2234f
	b 2235f
2234:
2236:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2236b
2235:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	li %r4, 0
	addi %r5, %r14, 2560
	addi %r6, %r19, 28
	addi %r3, %r14, 1024
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r19, 28
	addi %r3, %r14, 1024
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	addi %r5, %r14, 1280
	li %r6, 20
2237:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2237b
	addi %r3, %r24, -1
	rldicl %r3, %r3, 1, 63
2220:
	b 2213f
2212:
	li %r3, 0
2213:
	b 2209f
2208:
	li %r3, 0
2209:
	b 2207f
2206:
	li %r3, 0
2207:
	addi %r12, %r1, 0
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r14, 112(%r12)
	ld %r15, 120(%r12)
	ld %r16, 128(%r12)
	ld %r17, 136(%r12)
	ld %r18, 144(%r12)
	ld %r19, 152(%r12)
	ld %r20, 160(%r12)
	ld %r21, 168(%r12)
	ld %r22, 176(%r12)
	ld %r23, 184(%r12)
	ld %r24, 192(%r12)
	ld %r25, 200(%r12)
	ld %r26, 208(%r12)
	ld %r27, 216(%r12)
	ld %r28, 224(%r12)
	ld %r29, 232(%r12)
23:
	b 21f
20:
	addi %r12, %r1, 0
	std %r14, 112(%r12)
	std %r15, 120(%r12)
	std %r16, 128(%r12)
	std %r17, 136(%r12)
	std %r18, 144(%r12)
	std %r19, 152(%r12)
	std %r20, 160(%r12)
	std %r21, 168(%r12)
	std %r22, 176(%r12)
	std %r23, 184(%r12)
	std %r24, 192(%r12)
	std %r25, 200(%r12)
	std %r26, 208(%r12)
	std %r27, 216(%r12)
	std %r28, 224(%r12)
	std %r29, 232(%r12)
	mflr %r0
	std %r0, 240(%r12)
	ld %r20, 360(%r12)
	rlwinm %r20, %r20, 0, 0, 31
	ld %r14, 368(%r12)
	ld %r27, 376(%r12)
	ld %r22, 384(%r12)
	ld %r23, 392(%r12)
	or %r15, %r4, %r4
	or %r16, %r7, %r7
	ld %r19, 352(%r12)
	or %r24, %r5, %r5
	or %r25, %r6, %r6
	or %r26, %r9, %r9
	lbz %r9, 0(%r3)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r17, %r11, 1, 63
	li %r11, 0
	subf %r11, %r17, %r11
	li %r8, 255
	and %r11, %r11, %r8
	or %r18, %r10, %r11
	subf %r21, %r17, %r15
	addi %r21, %r21, -17
	cmpldi %cr0, %r9, 0
	beq %cr0, 2238f
	subf %r3, %r17, %r15
	addi %r3, %r3, -18
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 2240f
	cmpldi %cr0, %r20, 0
	beq %cr0, 2242f
	li %r4, 0
	b 2243f
2242:
	or %r4, %r19, %r19
2243:
	subf %r3, %r17, %r15
	addi %r3, %r3, -18
	subf %r3, %r4, %r3
	rldicl %r3, %r3, 1, 63
	rldicl %r5, %r4, 1, 63
	or %r3, %r3, %r5
	cmpldi %cr0, %r3, 0
	bne %cr0, 2244f
	addi %r12, %r1, 0
	li %r4, 8192
	add %r4, %r14, %r4
	std %r4, 96(%r12)
	addi %r5, %r27, -1024
	std %r5, 104(%r12)
	addi %r3, %r14, 0
	or %r4, %r15, %r15
	or %r5, %r22, %r22
	or %r6, %r23, %r23
	or %r7, %r24, %r24
	or %r8, %r25, %r25
	or %r9, %r26, %r26
	or %r10, %r15, %r15
	bl {vg_rsa_public_precomputed_checked}
	add %r4, %r14, %r15
	addi %r4, %r4, -1
	lbz %r5, 0(%r4)
	li %r6, 188
	xor %r5, %r5, %r6
	add %r7, %r14, %r17
	lbz %r6, 0(%r7)
	li %r8, 255
	xor %r8, %r8, %r18
	and %r6, %r6, %r8
	or %r5, %r5, %r6
	lbz %r6, 0(%r14)
	li %r8, 0
	subf %r8, %r17, %r8
	and %r6, %r6, %r8
	or %r5, %r5, %r6
	stb %r5, 0(%r4)
	add %r26, %r14, %r17
	or %r27, %r21, %r21
	add %r24, %r26, %r21
	li %r25, 16
	li %r28, 0
	li %r29, 0
2246:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r5, %r14, 1344
	or %r8, %r28, %r28
	stb %r8, 3(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 2(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 1(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 0(%r5)
	addi %r3, %r14, 1024
	or %r4, %r25, %r25
	li %r6, 4
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 408(%r9)
	ld %r9, 32(%r9)
	addi %r11, %r14, 1280
	add %r12, %r26, %r29
	subf %r8, %r29, %r27
	subf %r10, %r9, %r8
	rldicl %r6, %r10, 1, 63
	li %r7, 0
	subf %r6, %r6, %r7
	and %r10, %r10, %r6
	add %r9, %r9, %r10
2247:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2247b
	addi %r12, %r1, 0
	ld %r12, 408(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 2246b
	add %r4, %r14, %r17
	lbz %r5, 0(%r4)
	and %r5, %r5, %r18
	stb %r5, 0(%r4)
	add %r4, %r14, %r17
	or %r5, %r21, %r21
	li %r6, 0
	li %r7, 0
	addi %r7, %r7, -1
	li %r8, 0
	li %r9, 0
2248:
	lbz %r10, 0(%r4)
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	addi %r12, %r11, -1
	and %r12, %r12, %r7
	and %r3, %r6, %r12
	or %r8, %r8, %r3
	and %r3, %r10, %r12
	or %r9, %r9, %r3
	li %r3, 0
	subf %r3, %r11, %r3
	and %r7, %r7, %r3
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2248b
	add %r4, %r14, %r15
	addi %r4, %r4, -1
	lbz %r24, 0(%r4)
	li %r3, 1
	xor %r9, %r9, %r3
	or %r24, %r24, %r9
	subf %r25, %r8, %r21
	addi %r25, %r25, -1
	cmpldi %cr0, %r20, 0
	beq %cr0, 2249f
	b 2250f
2249:
	xor %r3, %r25, %r19
	or %r24, %r24, %r3
2250:
	cmpldi %cr0, %r20, 0
	beq %cr0, 2251f
	addi %r4, %r14, 2560
	li %r5, 2048
	li %r6, 0
2253:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2253b
	or %r4, %r16, %r16
	addi %r5, %r14, 2568
	li %r6, 16
2254:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2254b
	add %r4, %r14, %r17
	addi %r5, %r14, 2584
	or %r6, %r21, %r21
2255:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2255b
	addi %r8, %r8, 1
	li %r9, 1
	li %r10, 10
2256:
	addi %r4, %r14, 2584
	add %r5, %r4, %r9
	li %r6, 1
	and %r6, %r8, %r6
	li %r7, 0
	subf %r6, %r6, %r7
	or %r7, %r21, %r21
2257:
	lbz %r11, 0(%r4)
	lbz %r3, 0(%r5)
	xor %r3, %r3, %r11
	and %r3, %r3, %r6
	xor %r11, %r11, %r3
	stb %r11, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 2257b
	rldicl %r8, %r8, 63, 1
	add %r9, %r9, %r9
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 2256b
	addi %r29, %r25, 24
	addi %r28, %r21, 31
	rldicl %r28, %r28, 58, 6
	addi %r28, %r28, 1
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 2560
	rldicr %r5, %r28, 6, 57
	li %r6, 0
2258:
	xor %r7, %r6, %r29
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	li %r12, 0
	subf %r7, %r7, %r12
	li %r8, 128
	and %r7, %r7, %r8
	lbz %r8, 0(%r4)
	or %r8, %r8, %r7
	stb %r8, 0(%r4)
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2258b
	addi %r26, %r14, 4536
	add %r8, %r29, %r29
	add %r8, %r8, %r8
	add %r8, %r8, %r8
	std %r8, 72(%r26)
	addi %r27, %r29, 8
	rldicl %r27, %r27, 58, 6
	addi %r4, %r14, 2616
	li %r6, 0
	or %r9, %r28, %r28
2259:
	xor %r7, %r6, %r27
	addi %r7, %r7, -1
	rldicl %r7, %r7, 1, 63
	li %r12, 0
	subf %r7, %r7, %r12
	addi %r5, %r14, 4608
	li %r10, 8
2260:
	lbz %r8, 0(%r5)
	and %r8, %r8, %r7
	lbz %r11, 0(%r4)
	or %r11, %r11, %r8
	stb %r11, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 2260b
	addi %r4, %r4, 56
	addi %r6, %r6, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2259b
	li %r26, 0
2261:
	addi %r3, %r14, 1024
	rldicr %r4, %r26, 6, 57
	add %r4, %r4, %r14
	addi %r4, %r4, 2560
	li %r5, 1
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 24(%r12)
	mtctr %r12
	bctrl
	xor %r3, %r26, %r27
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	li %r12, 0
	subf %r3, %r3, %r12
	addi %r4, %r14, 1024
	addi %r5, %r14, 4800
	li %r6, 16
2262:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	and %r7, %r7, %r3
	xor %r8, %r8, %r7
	stb %r8, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2262b
	addi %r26, %r26, 1
	addi %r28, %r28, -1
	cmpldi %cr0, %r28, 0
	bne %cr0, 2261b
	addi %r3, %r14, 4800
	addi %r4, %r14, 1280
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 32(%r12)
	mtctr %r12
	bctrl
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	addi %r5, %r14, 1280
	li %r6, 16
2263:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2263b
	addi %r3, %r24, -1
	rldicl %r3, %r3, 1, 63
	b 2252f
2251:
	addi %r4, %r14, 2560
	li %r5, 8
	li %r6, 0
2264:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2264b
	or %r4, %r16, %r16
	addi %r5, %r14, 2568
	li %r6, 16
2265:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2265b
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	subf %r4, %r19, %r4
	addi %r5, %r14, 2584
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 2266f
	b 2267f
2266:
2268:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2268b
2267:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	li %r4, 0
	addi %r5, %r14, 2560
	addi %r6, %r19, 24
	addi %r3, %r14, 1024
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r19, 24
	addi %r3, %r14, 1024
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 400(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	addi %r5, %r14, 1280
	li %r6, 16
2269:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2269b
	addi %r3, %r24, -1
	rldicl %r3, %r3, 1, 63
2252:
	b 2245f
2244:
	li %r3, 0
2245:
	b 2241f
2240:
	li %r3, 0
2241:
	b 2239f
2238:
	li %r3, 0
2239:
	addi %r12, %r1, 0
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r14, 112(%r12)
	ld %r15, 120(%r12)
	ld %r16, 128(%r12)
	ld %r17, 136(%r12)
	ld %r18, 144(%r12)
	ld %r19, 152(%r12)
	ld %r20, 160(%r12)
	ld %r21, 168(%r12)
	ld %r22, 176(%r12)
	ld %r23, 184(%r12)
	ld %r24, 192(%r12)
	ld %r25, 200(%r12)
	ld %r26, 208(%r12)
	ld %r27, 216(%r12)
	ld %r28, 224(%r12)
	ld %r29, 232(%r12)
21:
	addi %r1, %r1, 256
	blr

vg_rsa_pss_sign:
	stdu %r1, -256(%r1)
	addi %r11, %r1, 0
	ld %r11, 464(%r11)
	ld %r11, 40(%r11)
	addi %r12, %r11, -0
	cmpldi %cr0, %r12, 0
	beq %cr0, 20f
	addi %r12, %r11, -1
	cmpldi %cr0, %r12, 0
	beq %cr0, 22f
	addi %r12, %r11, -2
	cmpldi %cr0, %r12, 0
	beq %cr0, 24f
	addi %r12, %r11, -3
	cmpldi %cr0, %r12, 0
	beq %cr0, 26f
	addi %r12, %r11, -4
	cmpldi %cr0, %r12, 0
	beq %cr0, 28f
	addi %r12, %r11, -5
	cmpldi %cr0, %r12, 0
	beq %cr0, 210f
	addi %r12, %r11, -6
	cmpldi %cr0, %r12, 0
	beq %cr0, 212f
	addi %r12, %r1, 0
	std %r14, 112(%r12)
	std %r15, 120(%r12)
	std %r16, 128(%r12)
	std %r17, 136(%r12)
	std %r18, 144(%r12)
	std %r19, 152(%r12)
	std %r20, 160(%r12)
	std %r21, 168(%r12)
	std %r22, 176(%r12)
	std %r23, 184(%r12)
	std %r24, 192(%r12)
	std %r25, 200(%r12)
	std %r26, 208(%r12)
	std %r27, 216(%r12)
	std %r28, 224(%r12)
	std %r29, 232(%r12)
	mflr %r0
	std %r0, 240(%r12)
	ld %r14, 448(%r12)
	or %r15, %r6, %r6
	or %r16, %r3, %r3
	or %r17, %r9, %r9
	or %r18, %r10, %r10
	ld %r19, 440(%r12)
	or %r20, %r5, %r5
	or %r21, %r7, %r7
	or %r22, %r8, %r8
	lbz %r9, 0(%r5)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	or %r23, %r11, %r11
	cmpldi %cr0, %r9, 0
	beq %cr0, 214f
	subf %r3, %r23, %r15
	addi %r3, %r3, -34
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 216f
	subf %r3, %r23, %r15
	addi %r3, %r3, -34
	subf %r3, %r19, %r3
	rldicl %r3, %r3, 1, 63
	rldicl %r5, %r19, 1, 63
	or %r3, %r3, %r5
	cmpldi %cr0, %r3, 0
	bne %cr0, 218f
	addi %r4, %r14, 2560
	li %r5, 8
	li %r6, 0
220:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 220b
	addi %r12, %r1, 0
	ld %r4, 416(%r12)
	addi %r5, %r14, 2568
	li %r6, 32
221:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 221b
	addi %r5, %r14, 2600
	addi %r12, %r1, 0
	ld %r4, 432(%r12)
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 222f
	b 223f
222:
224:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 224b
223:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 464(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	li %r4, 0
	addi %r5, %r14, 2560
	addi %r6, %r19, 40
	addi %r3, %r14, 1024
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 464(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r19, 40
	addi %r3, %r14, 1024
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 464(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 0
	or %r5, %r15, %r15
	li %r6, 0
225:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 225b
	addi %r4, %r14, 0
	add %r4, %r4, %r15
	subf %r4, %r19, %r4
	addi %r4, %r4, -34
	li %r5, 1
	stb %r5, 0(%r4)
	addi %r5, %r4, 1
	addi %r12, %r1, 0
	ld %r4, 432(%r12)
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 226f
	b 227f
226:
228:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 228b
227:
	addi %r4, %r14, 1280
	addi %r5, %r14, 0
	add %r5, %r5, %r15
	addi %r5, %r5, -33
	li %r6, 32
229:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 229b
	addi %r4, %r14, 0
	add %r4, %r4, %r15
	addi %r4, %r4, -1
	li %r5, 188
	stb %r5, 0(%r4)
	addi %r24, %r14, 0
	add %r24, %r24, %r15
	addi %r24, %r24, -33
	li %r25, 32
	addi %r26, %r14, 0
	add %r26, %r26, %r23
	subf %r27, %r23, %r15
	addi %r27, %r27, -33
	li %r28, 0
	li %r29, 0
230:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r5, %r14, 1344
	or %r8, %r28, %r28
	stb %r8, 3(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 2(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 1(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 0(%r5)
	addi %r3, %r14, 1024
	or %r4, %r25, %r25
	li %r6, 4
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 472(%r9)
	ld %r9, 32(%r9)
	addi %r11, %r14, 1280
	add %r12, %r26, %r29
	subf %r8, %r29, %r27
	subf %r10, %r9, %r8
	rldicl %r6, %r10, 1, 63
	li %r7, 0
	subf %r6, %r6, %r7
	and %r10, %r10, %r6
	add %r9, %r9, %r10
231:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 231b
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 230b
	lbz %r9, 0(%r20)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	li %r8, 0
	subf %r8, %r11, %r8
	li %r7, 255
	and %r8, %r8, %r7
	or %r10, %r10, %r8
	addi %r4, %r14, 0
	add %r4, %r4, %r23
	lbz %r5, 0(%r4)
	and %r5, %r5, %r10
	stb %r5, 0(%r4)
	stdu %r1, -192(%r1)
	addi %r12, %r1, 0
	std %r17, 96(%r12)
	std %r18, 104(%r12)
	ld %r0, 544(%r12)
	std %r0, 112(%r12)
	ld %r0, 552(%r12)
	std %r0, 120(%r12)
	ld %r0, 560(%r12)
	std %r0, 128(%r12)
	ld %r0, 568(%r12)
	std %r0, 136(%r12)
	ld %r0, 576(%r12)
	std %r0, 144(%r12)
	ld %r0, 584(%r12)
	std %r0, 152(%r12)
	ld %r0, 592(%r12)
	std %r0, 160(%r12)
	ld %r0, 600(%r12)
	std %r0, 168(%r12)
	li %r0, 8192
	add %r0, %r14, %r0
	std %r0, 176(%r12)
	ld %r11, 648(%r12)
	addi %r11, %r11, -1024
	std %r11, 184(%r12)
	or %r3, %r16, %r16
	or %r4, %r15, %r15
	or %r5, %r20, %r20
	or %r6, %r15, %r15
	or %r7, %r21, %r21
	or %r8, %r22, %r22
	addi %r9, %r14, 0
	or %r10, %r15, %r15
	bl {vg_rsa_private_checked}
	addi %r1, %r1, 192
	b 219f
218:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
232:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 232b
	li %r3, 0
219:
	b 217f
216:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
233:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 233b
	li %r3, 0
217:
	b 215f
214:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
234:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 234b
	li %r3, 0
215:
	addi %r12, %r1, 0
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r14, 112(%r12)
	ld %r15, 120(%r12)
	ld %r16, 128(%r12)
	ld %r17, 136(%r12)
	ld %r18, 144(%r12)
	ld %r19, 152(%r12)
	ld %r20, 160(%r12)
	ld %r21, 168(%r12)
	ld %r22, 176(%r12)
	ld %r23, 184(%r12)
	ld %r24, 192(%r12)
	ld %r25, 200(%r12)
	ld %r26, 208(%r12)
	ld %r27, 216(%r12)
	ld %r28, 224(%r12)
	ld %r29, 232(%r12)
	b 213f
212:
	addi %r12, %r1, 0
	std %r14, 112(%r12)
	std %r15, 120(%r12)
	std %r16, 128(%r12)
	std %r17, 136(%r12)
	std %r18, 144(%r12)
	std %r19, 152(%r12)
	std %r20, 160(%r12)
	std %r21, 168(%r12)
	std %r22, 176(%r12)
	std %r23, 184(%r12)
	std %r24, 192(%r12)
	std %r25, 200(%r12)
	std %r26, 208(%r12)
	std %r27, 216(%r12)
	std %r28, 224(%r12)
	std %r29, 232(%r12)
	mflr %r0
	std %r0, 240(%r12)
	ld %r14, 448(%r12)
	or %r15, %r6, %r6
	or %r16, %r3, %r3
	or %r17, %r9, %r9
	or %r18, %r10, %r10
	ld %r19, 440(%r12)
	or %r20, %r5, %r5
	or %r21, %r7, %r7
	or %r22, %r8, %r8
	lbz %r9, 0(%r5)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	or %r23, %r11, %r11
	cmpldi %cr0, %r9, 0
	beq %cr0, 235f
	subf %r3, %r23, %r15
	addi %r3, %r3, -30
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 237f
	subf %r3, %r23, %r15
	addi %r3, %r3, -30
	subf %r3, %r19, %r3
	rldicl %r3, %r3, 1, 63
	rldicl %r5, %r19, 1, 63
	or %r3, %r3, %r5
	cmpldi %cr0, %r3, 0
	bne %cr0, 239f
	addi %r4, %r14, 2560
	li %r5, 8
	li %r6, 0
241:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 241b
	addi %r12, %r1, 0
	ld %r4, 416(%r12)
	addi %r5, %r14, 2568
	li %r6, 28
242:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 242b
	addi %r5, %r14, 2596
	addi %r12, %r1, 0
	ld %r4, 432(%r12)
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 243f
	b 244f
243:
245:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 245b
244:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 464(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	li %r4, 0
	addi %r5, %r14, 2560
	addi %r6, %r19, 36
	addi %r3, %r14, 1024
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 464(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r19, 36
	addi %r3, %r14, 1024
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 464(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 0
	or %r5, %r15, %r15
	li %r6, 0
246:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 246b
	addi %r4, %r14, 0
	add %r4, %r4, %r15
	subf %r4, %r19, %r4
	addi %r4, %r4, -30
	li %r5, 1
	stb %r5, 0(%r4)
	addi %r5, %r4, 1
	addi %r12, %r1, 0
	ld %r4, 432(%r12)
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 247f
	b 248f
247:
249:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 249b
248:
	addi %r4, %r14, 1280
	addi %r5, %r14, 0
	add %r5, %r5, %r15
	addi %r5, %r5, -29
	li %r6, 28
250:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 250b
	addi %r4, %r14, 0
	add %r4, %r4, %r15
	addi %r4, %r4, -1
	li %r5, 188
	stb %r5, 0(%r4)
	addi %r24, %r14, 0
	add %r24, %r24, %r15
	addi %r24, %r24, -29
	li %r25, 28
	addi %r26, %r14, 0
	add %r26, %r26, %r23
	subf %r27, %r23, %r15
	addi %r27, %r27, -29
	li %r28, 0
	li %r29, 0
251:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r5, %r14, 1344
	or %r8, %r28, %r28
	stb %r8, 3(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 2(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 1(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 0(%r5)
	addi %r3, %r14, 1024
	or %r4, %r25, %r25
	li %r6, 4
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 472(%r9)
	ld %r9, 32(%r9)
	addi %r11, %r14, 1280
	add %r12, %r26, %r29
	subf %r8, %r29, %r27
	subf %r10, %r9, %r8
	rldicl %r6, %r10, 1, 63
	li %r7, 0
	subf %r6, %r6, %r7
	and %r10, %r10, %r6
	add %r9, %r9, %r10
252:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 252b
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 251b
	lbz %r9, 0(%r20)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	li %r8, 0
	subf %r8, %r11, %r8
	li %r7, 255
	and %r8, %r8, %r7
	or %r10, %r10, %r8
	addi %r4, %r14, 0
	add %r4, %r4, %r23
	lbz %r5, 0(%r4)
	and %r5, %r5, %r10
	stb %r5, 0(%r4)
	stdu %r1, -192(%r1)
	addi %r12, %r1, 0
	std %r17, 96(%r12)
	std %r18, 104(%r12)
	ld %r0, 544(%r12)
	std %r0, 112(%r12)
	ld %r0, 552(%r12)
	std %r0, 120(%r12)
	ld %r0, 560(%r12)
	std %r0, 128(%r12)
	ld %r0, 568(%r12)
	std %r0, 136(%r12)
	ld %r0, 576(%r12)
	std %r0, 144(%r12)
	ld %r0, 584(%r12)
	std %r0, 152(%r12)
	ld %r0, 592(%r12)
	std %r0, 160(%r12)
	ld %r0, 600(%r12)
	std %r0, 168(%r12)
	li %r0, 8192
	add %r0, %r14, %r0
	std %r0, 176(%r12)
	ld %r11, 648(%r12)
	addi %r11, %r11, -1024
	std %r11, 184(%r12)
	or %r3, %r16, %r16
	or %r4, %r15, %r15
	or %r5, %r20, %r20
	or %r6, %r15, %r15
	or %r7, %r21, %r21
	or %r8, %r22, %r22
	addi %r9, %r14, 0
	or %r10, %r15, %r15
	bl {vg_rsa_private_checked}
	addi %r1, %r1, 192
	b 240f
239:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
253:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 253b
	li %r3, 0
240:
	b 238f
237:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
254:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 254b
	li %r3, 0
238:
	b 236f
235:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
255:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 255b
	li %r3, 0
236:
	addi %r12, %r1, 0
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r14, 112(%r12)
	ld %r15, 120(%r12)
	ld %r16, 128(%r12)
	ld %r17, 136(%r12)
	ld %r18, 144(%r12)
	ld %r19, 152(%r12)
	ld %r20, 160(%r12)
	ld %r21, 168(%r12)
	ld %r22, 176(%r12)
	ld %r23, 184(%r12)
	ld %r24, 192(%r12)
	ld %r25, 200(%r12)
	ld %r26, 208(%r12)
	ld %r27, 216(%r12)
	ld %r28, 224(%r12)
	ld %r29, 232(%r12)
213:
	b 211f
210:
	addi %r12, %r1, 0
	std %r14, 112(%r12)
	std %r15, 120(%r12)
	std %r16, 128(%r12)
	std %r17, 136(%r12)
	std %r18, 144(%r12)
	std %r19, 152(%r12)
	std %r20, 160(%r12)
	std %r21, 168(%r12)
	std %r22, 176(%r12)
	std %r23, 184(%r12)
	std %r24, 192(%r12)
	std %r25, 200(%r12)
	std %r26, 208(%r12)
	std %r27, 216(%r12)
	std %r28, 224(%r12)
	std %r29, 232(%r12)
	mflr %r0
	std %r0, 240(%r12)
	ld %r14, 448(%r12)
	or %r15, %r6, %r6
	or %r16, %r3, %r3
	or %r17, %r9, %r9
	or %r18, %r10, %r10
	ld %r19, 440(%r12)
	or %r20, %r5, %r5
	or %r21, %r7, %r7
	or %r22, %r8, %r8
	lbz %r9, 0(%r5)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	or %r23, %r11, %r11
	cmpldi %cr0, %r9, 0
	beq %cr0, 256f
	subf %r3, %r23, %r15
	addi %r3, %r3, -66
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 258f
	subf %r3, %r23, %r15
	addi %r3, %r3, -66
	subf %r3, %r19, %r3
	rldicl %r3, %r3, 1, 63
	rldicl %r5, %r19, 1, 63
	or %r3, %r3, %r5
	cmpldi %cr0, %r3, 0
	bne %cr0, 260f
	addi %r4, %r14, 2560
	li %r5, 8
	li %r6, 0
262:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 262b
	addi %r12, %r1, 0
	ld %r4, 416(%r12)
	addi %r5, %r14, 2568
	li %r6, 64
263:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 263b
	addi %r5, %r14, 2632
	addi %r12, %r1, 0
	ld %r4, 432(%r12)
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 264f
	b 265f
264:
266:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 266b
265:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 464(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	li %r4, 0
	addi %r5, %r14, 2560
	addi %r6, %r19, 72
	addi %r3, %r14, 1024
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 464(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r19, 72
	addi %r3, %r14, 1024
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 464(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 0
	or %r5, %r15, %r15
	li %r6, 0
267:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 267b
	addi %r4, %r14, 0
	add %r4, %r4, %r15
	subf %r4, %r19, %r4
	addi %r4, %r4, -66
	li %r5, 1
	stb %r5, 0(%r4)
	addi %r5, %r4, 1
	addi %r12, %r1, 0
	ld %r4, 432(%r12)
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 268f
	b 269f
268:
270:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 270b
269:
	addi %r4, %r14, 1280
	addi %r5, %r14, 0
	add %r5, %r5, %r15
	addi %r5, %r5, -65
	li %r6, 64
271:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 271b
	addi %r4, %r14, 0
	add %r4, %r4, %r15
	addi %r4, %r4, -1
	li %r5, 188
	stb %r5, 0(%r4)
	addi %r24, %r14, 0
	add %r24, %r24, %r15
	addi %r24, %r24, -65
	li %r25, 64
	addi %r26, %r14, 0
	add %r26, %r26, %r23
	subf %r27, %r23, %r15
	addi %r27, %r27, -65
	li %r28, 0
	li %r29, 0
272:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r5, %r14, 1344
	or %r8, %r28, %r28
	stb %r8, 3(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 2(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 1(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 0(%r5)
	addi %r3, %r14, 1024
	or %r4, %r25, %r25
	li %r6, 4
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 472(%r9)
	ld %r9, 32(%r9)
	addi %r11, %r14, 1280
	add %r12, %r26, %r29
	subf %r8, %r29, %r27
	subf %r10, %r9, %r8
	rldicl %r6, %r10, 1, 63
	li %r7, 0
	subf %r6, %r6, %r7
	and %r10, %r10, %r6
	add %r9, %r9, %r10
273:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 273b
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 272b
	lbz %r9, 0(%r20)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	li %r8, 0
	subf %r8, %r11, %r8
	li %r7, 255
	and %r8, %r8, %r7
	or %r10, %r10, %r8
	addi %r4, %r14, 0
	add %r4, %r4, %r23
	lbz %r5, 0(%r4)
	and %r5, %r5, %r10
	stb %r5, 0(%r4)
	stdu %r1, -192(%r1)
	addi %r12, %r1, 0
	std %r17, 96(%r12)
	std %r18, 104(%r12)
	ld %r0, 544(%r12)
	std %r0, 112(%r12)
	ld %r0, 552(%r12)
	std %r0, 120(%r12)
	ld %r0, 560(%r12)
	std %r0, 128(%r12)
	ld %r0, 568(%r12)
	std %r0, 136(%r12)
	ld %r0, 576(%r12)
	std %r0, 144(%r12)
	ld %r0, 584(%r12)
	std %r0, 152(%r12)
	ld %r0, 592(%r12)
	std %r0, 160(%r12)
	ld %r0, 600(%r12)
	std %r0, 168(%r12)
	li %r0, 8192
	add %r0, %r14, %r0
	std %r0, 176(%r12)
	ld %r11, 648(%r12)
	addi %r11, %r11, -1024
	std %r11, 184(%r12)
	or %r3, %r16, %r16
	or %r4, %r15, %r15
	or %r5, %r20, %r20
	or %r6, %r15, %r15
	or %r7, %r21, %r21
	or %r8, %r22, %r22
	addi %r9, %r14, 0
	or %r10, %r15, %r15
	bl {vg_rsa_private_checked}
	addi %r1, %r1, 192
	b 261f
260:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
274:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 274b
	li %r3, 0
261:
	b 259f
258:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
275:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 275b
	li %r3, 0
259:
	b 257f
256:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
276:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 276b
	li %r3, 0
257:
	addi %r12, %r1, 0
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r14, 112(%r12)
	ld %r15, 120(%r12)
	ld %r16, 128(%r12)
	ld %r17, 136(%r12)
	ld %r18, 144(%r12)
	ld %r19, 152(%r12)
	ld %r20, 160(%r12)
	ld %r21, 168(%r12)
	ld %r22, 176(%r12)
	ld %r23, 184(%r12)
	ld %r24, 192(%r12)
	ld %r25, 200(%r12)
	ld %r26, 208(%r12)
	ld %r27, 216(%r12)
	ld %r28, 224(%r12)
	ld %r29, 232(%r12)
211:
	b 29f
28:
	addi %r12, %r1, 0
	std %r14, 112(%r12)
	std %r15, 120(%r12)
	std %r16, 128(%r12)
	std %r17, 136(%r12)
	std %r18, 144(%r12)
	std %r19, 152(%r12)
	std %r20, 160(%r12)
	std %r21, 168(%r12)
	std %r22, 176(%r12)
	std %r23, 184(%r12)
	std %r24, 192(%r12)
	std %r25, 200(%r12)
	std %r26, 208(%r12)
	std %r27, 216(%r12)
	std %r28, 224(%r12)
	std %r29, 232(%r12)
	mflr %r0
	std %r0, 240(%r12)
	ld %r14, 448(%r12)
	or %r15, %r6, %r6
	or %r16, %r3, %r3
	or %r17, %r9, %r9
	or %r18, %r10, %r10
	ld %r19, 440(%r12)
	or %r20, %r5, %r5
	or %r21, %r7, %r7
	or %r22, %r8, %r8
	lbz %r9, 0(%r5)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	or %r23, %r11, %r11
	cmpldi %cr0, %r9, 0
	beq %cr0, 277f
	subf %r3, %r23, %r15
	addi %r3, %r3, -50
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 279f
	subf %r3, %r23, %r15
	addi %r3, %r3, -50
	subf %r3, %r19, %r3
	rldicl %r3, %r3, 1, 63
	rldicl %r5, %r19, 1, 63
	or %r3, %r3, %r5
	cmpldi %cr0, %r3, 0
	bne %cr0, 281f
	addi %r4, %r14, 2560
	li %r5, 8
	li %r6, 0
283:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 283b
	addi %r12, %r1, 0
	ld %r4, 416(%r12)
	addi %r5, %r14, 2568
	li %r6, 48
284:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 284b
	addi %r5, %r14, 2616
	addi %r12, %r1, 0
	ld %r4, 432(%r12)
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 285f
	b 286f
285:
287:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 287b
286:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 464(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	li %r4, 0
	addi %r5, %r14, 2560
	addi %r6, %r19, 56
	addi %r3, %r14, 1024
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 464(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r19, 56
	addi %r3, %r14, 1024
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 464(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 0
	or %r5, %r15, %r15
	li %r6, 0
288:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 288b
	addi %r4, %r14, 0
	add %r4, %r4, %r15
	subf %r4, %r19, %r4
	addi %r4, %r4, -50
	li %r5, 1
	stb %r5, 0(%r4)
	addi %r5, %r4, 1
	addi %r12, %r1, 0
	ld %r4, 432(%r12)
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 289f
	b 290f
289:
291:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 291b
290:
	addi %r4, %r14, 1280
	addi %r5, %r14, 0
	add %r5, %r5, %r15
	addi %r5, %r5, -49
	li %r6, 48
292:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 292b
	addi %r4, %r14, 0
	add %r4, %r4, %r15
	addi %r4, %r4, -1
	li %r5, 188
	stb %r5, 0(%r4)
	addi %r24, %r14, 0
	add %r24, %r24, %r15
	addi %r24, %r24, -49
	li %r25, 48
	addi %r26, %r14, 0
	add %r26, %r26, %r23
	subf %r27, %r23, %r15
	addi %r27, %r27, -49
	li %r28, 0
	li %r29, 0
293:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r5, %r14, 1344
	or %r8, %r28, %r28
	stb %r8, 3(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 2(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 1(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 0(%r5)
	addi %r3, %r14, 1024
	or %r4, %r25, %r25
	li %r6, 4
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 472(%r9)
	ld %r9, 32(%r9)
	addi %r11, %r14, 1280
	add %r12, %r26, %r29
	subf %r8, %r29, %r27
	subf %r10, %r9, %r8
	rldicl %r6, %r10, 1, 63
	li %r7, 0
	subf %r6, %r6, %r7
	and %r10, %r10, %r6
	add %r9, %r9, %r10
294:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 294b
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 293b
	lbz %r9, 0(%r20)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	li %r8, 0
	subf %r8, %r11, %r8
	li %r7, 255
	and %r8, %r8, %r7
	or %r10, %r10, %r8
	addi %r4, %r14, 0
	add %r4, %r4, %r23
	lbz %r5, 0(%r4)
	and %r5, %r5, %r10
	stb %r5, 0(%r4)
	stdu %r1, -192(%r1)
	addi %r12, %r1, 0
	std %r17, 96(%r12)
	std %r18, 104(%r12)
	ld %r0, 544(%r12)
	std %r0, 112(%r12)
	ld %r0, 552(%r12)
	std %r0, 120(%r12)
	ld %r0, 560(%r12)
	std %r0, 128(%r12)
	ld %r0, 568(%r12)
	std %r0, 136(%r12)
	ld %r0, 576(%r12)
	std %r0, 144(%r12)
	ld %r0, 584(%r12)
	std %r0, 152(%r12)
	ld %r0, 592(%r12)
	std %r0, 160(%r12)
	ld %r0, 600(%r12)
	std %r0, 168(%r12)
	li %r0, 8192
	add %r0, %r14, %r0
	std %r0, 176(%r12)
	ld %r11, 648(%r12)
	addi %r11, %r11, -1024
	std %r11, 184(%r12)
	or %r3, %r16, %r16
	or %r4, %r15, %r15
	or %r5, %r20, %r20
	or %r6, %r15, %r15
	or %r7, %r21, %r21
	or %r8, %r22, %r22
	addi %r9, %r14, 0
	or %r10, %r15, %r15
	bl {vg_rsa_private_checked}
	addi %r1, %r1, 192
	b 282f
281:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
295:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 295b
	li %r3, 0
282:
	b 280f
279:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
296:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 296b
	li %r3, 0
280:
	b 278f
277:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
297:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 297b
	li %r3, 0
278:
	addi %r12, %r1, 0
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r14, 112(%r12)
	ld %r15, 120(%r12)
	ld %r16, 128(%r12)
	ld %r17, 136(%r12)
	ld %r18, 144(%r12)
	ld %r19, 152(%r12)
	ld %r20, 160(%r12)
	ld %r21, 168(%r12)
	ld %r22, 176(%r12)
	ld %r23, 184(%r12)
	ld %r24, 192(%r12)
	ld %r25, 200(%r12)
	ld %r26, 208(%r12)
	ld %r27, 216(%r12)
	ld %r28, 224(%r12)
	ld %r29, 232(%r12)
29:
	b 27f
26:
	addi %r12, %r1, 0
	std %r14, 112(%r12)
	std %r15, 120(%r12)
	std %r16, 128(%r12)
	std %r17, 136(%r12)
	std %r18, 144(%r12)
	std %r19, 152(%r12)
	std %r20, 160(%r12)
	std %r21, 168(%r12)
	std %r22, 176(%r12)
	std %r23, 184(%r12)
	std %r24, 192(%r12)
	std %r25, 200(%r12)
	std %r26, 208(%r12)
	std %r27, 216(%r12)
	std %r28, 224(%r12)
	std %r29, 232(%r12)
	mflr %r0
	std %r0, 240(%r12)
	ld %r14, 448(%r12)
	or %r15, %r6, %r6
	or %r16, %r3, %r3
	or %r17, %r9, %r9
	or %r18, %r10, %r10
	ld %r19, 440(%r12)
	or %r20, %r5, %r5
	or %r21, %r7, %r7
	or %r22, %r8, %r8
	lbz %r9, 0(%r5)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	or %r23, %r11, %r11
	cmpldi %cr0, %r9, 0
	beq %cr0, 298f
	subf %r3, %r23, %r15
	addi %r3, %r3, -34
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 2100f
	subf %r3, %r23, %r15
	addi %r3, %r3, -34
	subf %r3, %r19, %r3
	rldicl %r3, %r3, 1, 63
	rldicl %r5, %r19, 1, 63
	or %r3, %r3, %r5
	cmpldi %cr0, %r3, 0
	bne %cr0, 2102f
	addi %r4, %r14, 2560
	li %r5, 8
	li %r6, 0
2104:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2104b
	addi %r12, %r1, 0
	ld %r4, 416(%r12)
	addi %r5, %r14, 2568
	li %r6, 32
2105:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2105b
	addi %r5, %r14, 2600
	addi %r12, %r1, 0
	ld %r4, 432(%r12)
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 2106f
	b 2107f
2106:
2108:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2108b
2107:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 464(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	li %r4, 0
	addi %r5, %r14, 2560
	addi %r6, %r19, 40
	addi %r3, %r14, 1024
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 464(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r19, 40
	addi %r3, %r14, 1024
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 464(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 0
	or %r5, %r15, %r15
	li %r6, 0
2109:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2109b
	addi %r4, %r14, 0
	add %r4, %r4, %r15
	subf %r4, %r19, %r4
	addi %r4, %r4, -34
	li %r5, 1
	stb %r5, 0(%r4)
	addi %r5, %r4, 1
	addi %r12, %r1, 0
	ld %r4, 432(%r12)
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 2110f
	b 2111f
2110:
2112:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2112b
2111:
	addi %r4, %r14, 1280
	addi %r5, %r14, 0
	add %r5, %r5, %r15
	addi %r5, %r5, -33
	li %r6, 32
2113:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2113b
	addi %r4, %r14, 0
	add %r4, %r4, %r15
	addi %r4, %r4, -1
	li %r5, 188
	stb %r5, 0(%r4)
	addi %r24, %r14, 0
	add %r24, %r24, %r15
	addi %r24, %r24, -33
	li %r25, 32
	addi %r26, %r14, 0
	add %r26, %r26, %r23
	subf %r27, %r23, %r15
	addi %r27, %r27, -33
	li %r28, 0
	li %r29, 0
2114:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r5, %r14, 1344
	or %r8, %r28, %r28
	stb %r8, 3(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 2(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 1(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 0(%r5)
	addi %r3, %r14, 1024
	or %r4, %r25, %r25
	li %r6, 4
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 472(%r9)
	ld %r9, 32(%r9)
	addi %r11, %r14, 1280
	add %r12, %r26, %r29
	subf %r8, %r29, %r27
	subf %r10, %r9, %r8
	rldicl %r6, %r10, 1, 63
	li %r7, 0
	subf %r6, %r6, %r7
	and %r10, %r10, %r6
	add %r9, %r9, %r10
2115:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2115b
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 2114b
	lbz %r9, 0(%r20)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	li %r8, 0
	subf %r8, %r11, %r8
	li %r7, 255
	and %r8, %r8, %r7
	or %r10, %r10, %r8
	addi %r4, %r14, 0
	add %r4, %r4, %r23
	lbz %r5, 0(%r4)
	and %r5, %r5, %r10
	stb %r5, 0(%r4)
	stdu %r1, -192(%r1)
	addi %r12, %r1, 0
	std %r17, 96(%r12)
	std %r18, 104(%r12)
	ld %r0, 544(%r12)
	std %r0, 112(%r12)
	ld %r0, 552(%r12)
	std %r0, 120(%r12)
	ld %r0, 560(%r12)
	std %r0, 128(%r12)
	ld %r0, 568(%r12)
	std %r0, 136(%r12)
	ld %r0, 576(%r12)
	std %r0, 144(%r12)
	ld %r0, 584(%r12)
	std %r0, 152(%r12)
	ld %r0, 592(%r12)
	std %r0, 160(%r12)
	ld %r0, 600(%r12)
	std %r0, 168(%r12)
	li %r0, 8192
	add %r0, %r14, %r0
	std %r0, 176(%r12)
	ld %r11, 648(%r12)
	addi %r11, %r11, -1024
	std %r11, 184(%r12)
	or %r3, %r16, %r16
	or %r4, %r15, %r15
	or %r5, %r20, %r20
	or %r6, %r15, %r15
	or %r7, %r21, %r21
	or %r8, %r22, %r22
	addi %r9, %r14, 0
	or %r10, %r15, %r15
	bl {vg_rsa_private_checked}
	addi %r1, %r1, 192
	b 2103f
2102:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
2116:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2116b
	li %r3, 0
2103:
	b 2101f
2100:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
2117:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2117b
	li %r3, 0
2101:
	b 299f
298:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
2118:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2118b
	li %r3, 0
299:
	addi %r12, %r1, 0
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r14, 112(%r12)
	ld %r15, 120(%r12)
	ld %r16, 128(%r12)
	ld %r17, 136(%r12)
	ld %r18, 144(%r12)
	ld %r19, 152(%r12)
	ld %r20, 160(%r12)
	ld %r21, 168(%r12)
	ld %r22, 176(%r12)
	ld %r23, 184(%r12)
	ld %r24, 192(%r12)
	ld %r25, 200(%r12)
	ld %r26, 208(%r12)
	ld %r27, 216(%r12)
	ld %r28, 224(%r12)
	ld %r29, 232(%r12)
27:
	b 25f
24:
	addi %r12, %r1, 0
	std %r14, 112(%r12)
	std %r15, 120(%r12)
	std %r16, 128(%r12)
	std %r17, 136(%r12)
	std %r18, 144(%r12)
	std %r19, 152(%r12)
	std %r20, 160(%r12)
	std %r21, 168(%r12)
	std %r22, 176(%r12)
	std %r23, 184(%r12)
	std %r24, 192(%r12)
	std %r25, 200(%r12)
	std %r26, 208(%r12)
	std %r27, 216(%r12)
	std %r28, 224(%r12)
	std %r29, 232(%r12)
	mflr %r0
	std %r0, 240(%r12)
	ld %r14, 448(%r12)
	or %r15, %r6, %r6
	or %r16, %r3, %r3
	or %r17, %r9, %r9
	or %r18, %r10, %r10
	ld %r19, 440(%r12)
	or %r20, %r5, %r5
	or %r21, %r7, %r7
	or %r22, %r8, %r8
	lbz %r9, 0(%r5)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	or %r23, %r11, %r11
	cmpldi %cr0, %r9, 0
	beq %cr0, 2119f
	subf %r3, %r23, %r15
	addi %r3, %r3, -30
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 2121f
	subf %r3, %r23, %r15
	addi %r3, %r3, -30
	subf %r3, %r19, %r3
	rldicl %r3, %r3, 1, 63
	rldicl %r5, %r19, 1, 63
	or %r3, %r3, %r5
	cmpldi %cr0, %r3, 0
	bne %cr0, 2123f
	addi %r4, %r14, 2560
	li %r5, 8
	li %r6, 0
2125:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2125b
	addi %r12, %r1, 0
	ld %r4, 416(%r12)
	addi %r5, %r14, 2568
	li %r6, 28
2126:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2126b
	addi %r5, %r14, 2596
	addi %r12, %r1, 0
	ld %r4, 432(%r12)
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 2127f
	b 2128f
2127:
2129:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2129b
2128:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 464(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	li %r4, 0
	addi %r5, %r14, 2560
	addi %r6, %r19, 36
	addi %r3, %r14, 1024
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 464(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r19, 36
	addi %r3, %r14, 1024
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 464(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 0
	or %r5, %r15, %r15
	li %r6, 0
2130:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2130b
	addi %r4, %r14, 0
	add %r4, %r4, %r15
	subf %r4, %r19, %r4
	addi %r4, %r4, -30
	li %r5, 1
	stb %r5, 0(%r4)
	addi %r5, %r4, 1
	addi %r12, %r1, 0
	ld %r4, 432(%r12)
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 2131f
	b 2132f
2131:
2133:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2133b
2132:
	addi %r4, %r14, 1280
	addi %r5, %r14, 0
	add %r5, %r5, %r15
	addi %r5, %r5, -29
	li %r6, 28
2134:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2134b
	addi %r4, %r14, 0
	add %r4, %r4, %r15
	addi %r4, %r4, -1
	li %r5, 188
	stb %r5, 0(%r4)
	addi %r24, %r14, 0
	add %r24, %r24, %r15
	addi %r24, %r24, -29
	li %r25, 28
	addi %r26, %r14, 0
	add %r26, %r26, %r23
	subf %r27, %r23, %r15
	addi %r27, %r27, -29
	li %r28, 0
	li %r29, 0
2135:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r5, %r14, 1344
	or %r8, %r28, %r28
	stb %r8, 3(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 2(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 1(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 0(%r5)
	addi %r3, %r14, 1024
	or %r4, %r25, %r25
	li %r6, 4
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 472(%r9)
	ld %r9, 32(%r9)
	addi %r11, %r14, 1280
	add %r12, %r26, %r29
	subf %r8, %r29, %r27
	subf %r10, %r9, %r8
	rldicl %r6, %r10, 1, 63
	li %r7, 0
	subf %r6, %r6, %r7
	and %r10, %r10, %r6
	add %r9, %r9, %r10
2136:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2136b
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 2135b
	lbz %r9, 0(%r20)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	li %r8, 0
	subf %r8, %r11, %r8
	li %r7, 255
	and %r8, %r8, %r7
	or %r10, %r10, %r8
	addi %r4, %r14, 0
	add %r4, %r4, %r23
	lbz %r5, 0(%r4)
	and %r5, %r5, %r10
	stb %r5, 0(%r4)
	stdu %r1, -192(%r1)
	addi %r12, %r1, 0
	std %r17, 96(%r12)
	std %r18, 104(%r12)
	ld %r0, 544(%r12)
	std %r0, 112(%r12)
	ld %r0, 552(%r12)
	std %r0, 120(%r12)
	ld %r0, 560(%r12)
	std %r0, 128(%r12)
	ld %r0, 568(%r12)
	std %r0, 136(%r12)
	ld %r0, 576(%r12)
	std %r0, 144(%r12)
	ld %r0, 584(%r12)
	std %r0, 152(%r12)
	ld %r0, 592(%r12)
	std %r0, 160(%r12)
	ld %r0, 600(%r12)
	std %r0, 168(%r12)
	li %r0, 8192
	add %r0, %r14, %r0
	std %r0, 176(%r12)
	ld %r11, 648(%r12)
	addi %r11, %r11, -1024
	std %r11, 184(%r12)
	or %r3, %r16, %r16
	or %r4, %r15, %r15
	or %r5, %r20, %r20
	or %r6, %r15, %r15
	or %r7, %r21, %r21
	or %r8, %r22, %r22
	addi %r9, %r14, 0
	or %r10, %r15, %r15
	bl {vg_rsa_private_checked}
	addi %r1, %r1, 192
	b 2124f
2123:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
2137:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2137b
	li %r3, 0
2124:
	b 2122f
2121:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
2138:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2138b
	li %r3, 0
2122:
	b 2120f
2119:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
2139:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2139b
	li %r3, 0
2120:
	addi %r12, %r1, 0
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r14, 112(%r12)
	ld %r15, 120(%r12)
	ld %r16, 128(%r12)
	ld %r17, 136(%r12)
	ld %r18, 144(%r12)
	ld %r19, 152(%r12)
	ld %r20, 160(%r12)
	ld %r21, 168(%r12)
	ld %r22, 176(%r12)
	ld %r23, 184(%r12)
	ld %r24, 192(%r12)
	ld %r25, 200(%r12)
	ld %r26, 208(%r12)
	ld %r27, 216(%r12)
	ld %r28, 224(%r12)
	ld %r29, 232(%r12)
25:
	b 23f
22:
	addi %r12, %r1, 0
	std %r14, 112(%r12)
	std %r15, 120(%r12)
	std %r16, 128(%r12)
	std %r17, 136(%r12)
	std %r18, 144(%r12)
	std %r19, 152(%r12)
	std %r20, 160(%r12)
	std %r21, 168(%r12)
	std %r22, 176(%r12)
	std %r23, 184(%r12)
	std %r24, 192(%r12)
	std %r25, 200(%r12)
	std %r26, 208(%r12)
	std %r27, 216(%r12)
	std %r28, 224(%r12)
	std %r29, 232(%r12)
	mflr %r0
	std %r0, 240(%r12)
	ld %r14, 448(%r12)
	or %r15, %r6, %r6
	or %r16, %r3, %r3
	or %r17, %r9, %r9
	or %r18, %r10, %r10
	ld %r19, 440(%r12)
	or %r20, %r5, %r5
	or %r21, %r7, %r7
	or %r22, %r8, %r8
	lbz %r9, 0(%r5)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	or %r23, %r11, %r11
	cmpldi %cr0, %r9, 0
	beq %cr0, 2140f
	subf %r3, %r23, %r15
	addi %r3, %r3, -22
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 2142f
	subf %r3, %r23, %r15
	addi %r3, %r3, -22
	subf %r3, %r19, %r3
	rldicl %r3, %r3, 1, 63
	rldicl %r5, %r19, 1, 63
	or %r3, %r3, %r5
	cmpldi %cr0, %r3, 0
	bne %cr0, 2144f
	addi %r4, %r14, 2560
	li %r5, 8
	li %r6, 0
2146:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2146b
	addi %r12, %r1, 0
	ld %r4, 416(%r12)
	addi %r5, %r14, 2568
	li %r6, 20
2147:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2147b
	addi %r5, %r14, 2588
	addi %r12, %r1, 0
	ld %r4, 432(%r12)
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 2148f
	b 2149f
2148:
2150:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2150b
2149:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 464(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	li %r4, 0
	addi %r5, %r14, 2560
	addi %r6, %r19, 28
	addi %r3, %r14, 1024
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 464(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r19, 28
	addi %r3, %r14, 1024
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 464(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 0
	or %r5, %r15, %r15
	li %r6, 0
2151:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2151b
	addi %r4, %r14, 0
	add %r4, %r4, %r15
	subf %r4, %r19, %r4
	addi %r4, %r4, -22
	li %r5, 1
	stb %r5, 0(%r4)
	addi %r5, %r4, 1
	addi %r12, %r1, 0
	ld %r4, 432(%r12)
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 2152f
	b 2153f
2152:
2154:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2154b
2153:
	addi %r4, %r14, 1280
	addi %r5, %r14, 0
	add %r5, %r5, %r15
	addi %r5, %r5, -21
	li %r6, 20
2155:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2155b
	addi %r4, %r14, 0
	add %r4, %r4, %r15
	addi %r4, %r4, -1
	li %r5, 188
	stb %r5, 0(%r4)
	addi %r24, %r14, 0
	add %r24, %r24, %r15
	addi %r24, %r24, -21
	li %r25, 20
	addi %r26, %r14, 0
	add %r26, %r26, %r23
	subf %r27, %r23, %r15
	addi %r27, %r27, -21
	li %r28, 0
	li %r29, 0
2156:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r5, %r14, 1344
	or %r8, %r28, %r28
	stb %r8, 3(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 2(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 1(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 0(%r5)
	addi %r3, %r14, 1024
	or %r4, %r25, %r25
	li %r6, 4
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 472(%r9)
	ld %r9, 32(%r9)
	addi %r11, %r14, 1280
	add %r12, %r26, %r29
	subf %r8, %r29, %r27
	subf %r10, %r9, %r8
	rldicl %r6, %r10, 1, 63
	li %r7, 0
	subf %r6, %r6, %r7
	and %r10, %r10, %r6
	add %r9, %r9, %r10
2157:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2157b
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 2156b
	lbz %r9, 0(%r20)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	li %r8, 0
	subf %r8, %r11, %r8
	li %r7, 255
	and %r8, %r8, %r7
	or %r10, %r10, %r8
	addi %r4, %r14, 0
	add %r4, %r4, %r23
	lbz %r5, 0(%r4)
	and %r5, %r5, %r10
	stb %r5, 0(%r4)
	stdu %r1, -192(%r1)
	addi %r12, %r1, 0
	std %r17, 96(%r12)
	std %r18, 104(%r12)
	ld %r0, 544(%r12)
	std %r0, 112(%r12)
	ld %r0, 552(%r12)
	std %r0, 120(%r12)
	ld %r0, 560(%r12)
	std %r0, 128(%r12)
	ld %r0, 568(%r12)
	std %r0, 136(%r12)
	ld %r0, 576(%r12)
	std %r0, 144(%r12)
	ld %r0, 584(%r12)
	std %r0, 152(%r12)
	ld %r0, 592(%r12)
	std %r0, 160(%r12)
	ld %r0, 600(%r12)
	std %r0, 168(%r12)
	li %r0, 8192
	add %r0, %r14, %r0
	std %r0, 176(%r12)
	ld %r11, 648(%r12)
	addi %r11, %r11, -1024
	std %r11, 184(%r12)
	or %r3, %r16, %r16
	or %r4, %r15, %r15
	or %r5, %r20, %r20
	or %r6, %r15, %r15
	or %r7, %r21, %r21
	or %r8, %r22, %r22
	addi %r9, %r14, 0
	or %r10, %r15, %r15
	bl {vg_rsa_private_checked}
	addi %r1, %r1, 192
	b 2145f
2144:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
2158:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2158b
	li %r3, 0
2145:
	b 2143f
2142:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
2159:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2159b
	li %r3, 0
2143:
	b 2141f
2140:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
2160:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2160b
	li %r3, 0
2141:
	addi %r12, %r1, 0
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r14, 112(%r12)
	ld %r15, 120(%r12)
	ld %r16, 128(%r12)
	ld %r17, 136(%r12)
	ld %r18, 144(%r12)
	ld %r19, 152(%r12)
	ld %r20, 160(%r12)
	ld %r21, 168(%r12)
	ld %r22, 176(%r12)
	ld %r23, 184(%r12)
	ld %r24, 192(%r12)
	ld %r25, 200(%r12)
	ld %r26, 208(%r12)
	ld %r27, 216(%r12)
	ld %r28, 224(%r12)
	ld %r29, 232(%r12)
23:
	b 21f
20:
	addi %r12, %r1, 0
	std %r14, 112(%r12)
	std %r15, 120(%r12)
	std %r16, 128(%r12)
	std %r17, 136(%r12)
	std %r18, 144(%r12)
	std %r19, 152(%r12)
	std %r20, 160(%r12)
	std %r21, 168(%r12)
	std %r22, 176(%r12)
	std %r23, 184(%r12)
	std %r24, 192(%r12)
	std %r25, 200(%r12)
	std %r26, 208(%r12)
	std %r27, 216(%r12)
	std %r28, 224(%r12)
	std %r29, 232(%r12)
	mflr %r0
	std %r0, 240(%r12)
	ld %r14, 448(%r12)
	or %r15, %r6, %r6
	or %r16, %r3, %r3
	or %r17, %r9, %r9
	or %r18, %r10, %r10
	ld %r19, 440(%r12)
	or %r20, %r5, %r5
	or %r21, %r7, %r7
	or %r22, %r8, %r8
	lbz %r9, 0(%r5)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	or %r23, %r11, %r11
	cmpldi %cr0, %r9, 0
	beq %cr0, 2161f
	subf %r3, %r23, %r15
	addi %r3, %r3, -18
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 2163f
	subf %r3, %r23, %r15
	addi %r3, %r3, -18
	subf %r3, %r19, %r3
	rldicl %r3, %r3, 1, 63
	rldicl %r5, %r19, 1, 63
	or %r3, %r3, %r5
	cmpldi %cr0, %r3, 0
	bne %cr0, 2165f
	addi %r4, %r14, 2560
	li %r5, 8
	li %r6, 0
2167:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2167b
	addi %r12, %r1, 0
	ld %r4, 416(%r12)
	addi %r5, %r14, 2568
	li %r6, 16
2168:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2168b
	addi %r5, %r14, 2584
	addi %r12, %r1, 0
	ld %r4, 432(%r12)
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 2169f
	b 2170f
2169:
2171:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2171b
2170:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 464(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	li %r4, 0
	addi %r5, %r14, 2560
	addi %r6, %r19, 24
	addi %r3, %r14, 1024
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 464(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r19, 24
	addi %r3, %r14, 1024
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 464(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 0
	or %r5, %r15, %r15
	li %r6, 0
2172:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2172b
	addi %r4, %r14, 0
	add %r4, %r4, %r15
	subf %r4, %r19, %r4
	addi %r4, %r4, -18
	li %r5, 1
	stb %r5, 0(%r4)
	addi %r5, %r4, 1
	addi %r12, %r1, 0
	ld %r4, 432(%r12)
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 2173f
	b 2174f
2173:
2175:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2175b
2174:
	addi %r4, %r14, 1280
	addi %r5, %r14, 0
	add %r5, %r5, %r15
	addi %r5, %r5, -17
	li %r6, 16
2176:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2176b
	addi %r4, %r14, 0
	add %r4, %r4, %r15
	addi %r4, %r4, -1
	li %r5, 188
	stb %r5, 0(%r4)
	addi %r24, %r14, 0
	add %r24, %r24, %r15
	addi %r24, %r24, -17
	li %r25, 16
	addi %r26, %r14, 0
	add %r26, %r26, %r23
	subf %r27, %r23, %r15
	addi %r27, %r27, -17
	li %r28, 0
	li %r29, 0
2177:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r5, %r14, 1344
	or %r8, %r28, %r28
	stb %r8, 3(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 2(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 1(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 0(%r5)
	addi %r3, %r14, 1024
	or %r4, %r25, %r25
	li %r6, 4
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 472(%r9)
	ld %r9, 32(%r9)
	addi %r11, %r14, 1280
	add %r12, %r26, %r29
	subf %r8, %r29, %r27
	subf %r10, %r9, %r8
	rldicl %r6, %r10, 1, 63
	li %r7, 0
	subf %r6, %r6, %r7
	and %r10, %r10, %r6
	add %r9, %r9, %r10
2178:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2178b
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 2177b
	lbz %r9, 0(%r20)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	li %r8, 0
	subf %r8, %r11, %r8
	li %r7, 255
	and %r8, %r8, %r7
	or %r10, %r10, %r8
	addi %r4, %r14, 0
	add %r4, %r4, %r23
	lbz %r5, 0(%r4)
	and %r5, %r5, %r10
	stb %r5, 0(%r4)
	stdu %r1, -192(%r1)
	addi %r12, %r1, 0
	std %r17, 96(%r12)
	std %r18, 104(%r12)
	ld %r0, 544(%r12)
	std %r0, 112(%r12)
	ld %r0, 552(%r12)
	std %r0, 120(%r12)
	ld %r0, 560(%r12)
	std %r0, 128(%r12)
	ld %r0, 568(%r12)
	std %r0, 136(%r12)
	ld %r0, 576(%r12)
	std %r0, 144(%r12)
	ld %r0, 584(%r12)
	std %r0, 152(%r12)
	ld %r0, 592(%r12)
	std %r0, 160(%r12)
	ld %r0, 600(%r12)
	std %r0, 168(%r12)
	li %r0, 8192
	add %r0, %r14, %r0
	std %r0, 176(%r12)
	ld %r11, 648(%r12)
	addi %r11, %r11, -1024
	std %r11, 184(%r12)
	or %r3, %r16, %r16
	or %r4, %r15, %r15
	or %r5, %r20, %r20
	or %r6, %r15, %r15
	or %r7, %r21, %r21
	or %r8, %r22, %r22
	addi %r9, %r14, 0
	or %r10, %r15, %r15
	bl {vg_rsa_private_checked}
	addi %r1, %r1, 192
	b 2166f
2165:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
2179:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2179b
	li %r3, 0
2166:
	b 2164f
2163:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
2180:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2180b
	li %r3, 0
2164:
	b 2162f
2161:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
2181:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2181b
	li %r3, 0
2162:
	addi %r12, %r1, 0
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r14, 112(%r12)
	ld %r15, 120(%r12)
	ld %r16, 128(%r12)
	ld %r17, 136(%r12)
	ld %r18, 144(%r12)
	ld %r19, 152(%r12)
	ld %r20, 160(%r12)
	ld %r21, 168(%r12)
	ld %r22, 176(%r12)
	ld %r23, 184(%r12)
	ld %r24, 192(%r12)
	ld %r25, 200(%r12)
	ld %r26, 208(%r12)
	ld %r27, 216(%r12)
	ld %r28, 224(%r12)
	ld %r29, 232(%r12)
21:
	addi %r1, %r1, 256
	blr
